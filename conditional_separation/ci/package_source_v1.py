"""Package-only Git blob export: no checkout/index, filters or archive extraction."""
import hashlib,json,platform,re,subprocess,sys
from pathlib import Path,PurePosixPath,PureWindowsPath

MAX_FILES=10000
MAX_FILE=32*1024**2
MAX_TOTAL=256*1024**2

def require(ok,message):
    if not ok:raise ValueError(message)

def plan_tree(raw):
    require(raw and raw.endswith(b'\0'),'complete nonempty NUL tree listing')
    result=[];seen=set();directories={}
    reserved={'CON','PRN','AUX','NUL'}|{f'{p}{i}' for p in ('COM','LPT') for i in range(1,10)}
    for record in raw[:-1].split(b'\0'):
        meta,name=record.split(b'\t',1);mode,kind,oid=meta.decode('ascii').split(' ')
        name=name.decode('utf-8')
        require(mode in {'100644','100755'} and kind=='blob','regular Git blobs only')
        require(re.fullmatch('[0-9a-f]{40}',oid) is not None,'literal SHA1 blob identity')
        require(name.startswith('conditional_separation/'),'package prefix only')
        rel=name[len('conditional_separation/'):];parts=rel.split('/')
        for part in parts:
            require(re.fullmatch('[A-Za-z0-9_.+-]+',part) is not None and part not in {'.','..'},'portable path component')
            require(not part.endswith(('.', ' ')) and part.split('.')[0].upper() not in reserved,'Windows reserved path')
            require(part.lower() not in {'.git','.lake','__pycache__'} and not part.lower().endswith(('.olean','.olean.private','.olean.server','.ilean','.o','.obj','.pyc')),'source files only')
        for i in range(1,len(parts)):
            prefix='/'.join(parts[:i]);folded=prefix.casefold()
            require(directories.get(folded,prefix)==prefix,'inconsistent directory-prefix spelling')
            directories[folded]=prefix
        key=rel.casefold();require(key not in seen,'duplicate/case-colliding path');seen.add(key)
        result.append({'path':rel,'mode':mode,'git_blob':oid})
    require(len(result)<=MAX_FILES,'source file limit')
    for key in seen:
        parts=key.split('/')
        require(not any('/'.join(parts[:i]) in seen for i in range(1,len(parts))),'file/directory collision')
    return result

# These limits are conservative engineering policy, not a Windows API theorem.
WINDOWS_PATH_LIMIT = 248
TEMP_NAME_MARGIN = 16  # Unproven allowance; actual compiler temp suffix is unknown.
ARTIFACT_SUFFIXES = {
    'olean': ('.lake/build/lib/lean', '.olean'),
    'server': ('.lake/build/lib/lean', '.olean.server'),
    'private': ('.lake/build/lib/lean', '.olean.private'),
    'ilean': ('.lake/build/lib/lean', '.ilean'),
    'trace': ('.lake/build/lib/lean', '.olean.trace'),
    'setup': ('.lake/build/ir', '.setup.json'),
    'c': ('.lake/build/ir', '.c'),
    'object': ('.lake/build/ir', '.c.o'),
}

def owned_paths(rows):
    result={};seen=set()
    for row in rows:
        name=row['path']
        require(isinstance(name,str) and name and '\\' not in name and ':' not in name,'relative source path')
        p=PurePosixPath(name)
        require(not p.is_absolute() and p.as_posix()==name and '..' not in p.parts,'canonical source path')
        require(name.casefold() not in seen,'duplicate source path');seen.add(name.casefold())
        if not name.endswith('.lean'):continue
        if name in {'lakefile.lean','template/Attempt.lean','tools/SourceImports.lean'}:continue
        require(name.startswith('core/') or name=='ConditionalSeparation.lean' or name.startswith('ConditionalSeparation/'),'foreign Lean source')
        module=name[5:-5] if name.startswith('core/') else name[:-5]
        require(all(re.fullmatch('[A-Za-z_][A-Za-z0-9_]*',p) for p in module.split('/')),'module components')
        require(module.casefold() not in {x.casefold() for x in result},'duplicate module identity')
        result[module]=name
    require(result,'no owned modules')
    return result

def price_paths(package,rows,system):
    require(system in {'Windows','Linux','Darwin'},'supported native system')
    cls=PureWindowsPath if system=='Windows' else PurePosixPath
    package=cls(package)
    require(package.is_absolute() and '..' not in package.parts,'absolute physical package root')
    require(system!='Windows' or (len(package.drive)==2 and package.drive[1]==':'),'local Windows drive required')
    paths=owned_paths(rows);details=[];maxima={}
    for module,source in paths.items():
        candidates={'source':package/source}
        candidates.update({k:package/base/(module+suffix) for k,(base,suffix) in ARTIFACT_SUFFIXES.items()})
        lengths={k:len(str(p).encode('utf-16-le'))//2 for k,p in candidates.items()}
        component=max(len(part.encode('utf-16-le'))//2 for p in candidates.values() for part in p.parts)
        details.append({'module':module,'lengths_utf16':lengths,'max_component_utf16':component})
        for k,n in lengths.items():maxima[k]=max(maxima.get(k,0),n)
    return {'system':system,'package_root':str(package),'owned_modules':len(paths),'maxima_utf16':maxima,
            'max_component_utf16':max(r['max_component_utf16'] for r in details),
            'engineering_margin':TEMP_NAME_MARGIN,'engineering_limit':WINDOWS_PATH_LIMIT,'details':details}

def admit_paths(package,rows,system):
    report=price_paths(package,rows,system)
    if system=='Windows':
        require(max(report['maxima_utf16'].values())+TEMP_NAME_MARGIN<=WINDOWS_PATH_LIMIT,'Windows engineering path budget exceeded')
        require(report['max_component_utf16']+TEMP_NAME_MARGIN<=240,'Windows engineering component budget exceeded')
    return {k:v for k,v in report.items() if k!='details'}

def unaliased(path):
    path=Path(path)
    require(path.is_absolute() and path.resolve(strict=True)==path,'physical absolute root required')
    require(not any(p.is_symlink() or getattr(p,'is_junction',lambda:False)() for p in (path,*path.parents)),'no alias/symlink/junction roots')
    return path

def checked_layout(package,raw_temp,expected_head):
    require(isinstance(expected_head,str) and re.fullmatch('[0-9a-f]{40}',expected_head) and expected_head!='0'*40,'nonzero exact head')
    temp=unaliased(Path(raw_temp));require(temp.is_dir(),'runner-private temp directory')
    work=temp/'w'
    if work.exists() or work.is_symlink():require(unaliased(work).is_dir(),'real runner-private work root')
    package=unaliased(Path(package));require(package==temp/'s'/'p','exact runner-private short package')
    bare=unaliased(temp/'g');require(bare.is_dir() and not (bare/'index').exists(),'private no-index Git store')
    for name in [package/'PACKAGE_FILES.json',package.parent/'SOURCE_MATERIALIZATION.json',package.parent/'.git']:
        require(name.is_file() and not name.is_symlink() and name.stat().st_nlink==1,'regular layout binding')
    require((package.parent/'.git').read_text().strip()=='gitdir: '+bare.as_posix(),'Git pointer/layout binding')
    inventory=json.loads((package/'PACKAGE_FILES.json').read_bytes())
    record=json.loads((package.parent/'SOURCE_MATERIALIZATION.json').read_bytes())
    require(inventory.get('schema')=='conditional-separation-source-files-v1','inventory schema')
    require(record.get('schema')=='package-source-blobs-v1' and record.get('head')==expected_head,'source/head binding')
    require(record.get('layout')=='runner-private-short-v1' and record.get('package_directory')=='p','materializer layout binding')
    rows=inventory['files'];actual=record['files']
    report=admit_paths(str(package),rows,platform.system())
    require(len({r['path'] for r in actual})==len(actual),'duplicate materialization path')
    pins={r['path']:(r['bytes'],r['sha256']) for r in actual}
    require(set(pins)=={r['path'] for r in rows}|{'PACKAGE_FILES.json'},'complete materialization/inventory names')
    require(all(pins[r['path']]==(r['bytes'],r['sha256']) for r in rows),'materialization/inventory pins')
    for r in actual:
        require(type(r['bytes']) is int and r['bytes']>=0 and re.fullmatch('[0-9a-f]{64}',r['sha256']),'source pin schema')
        path=package/Path(*PurePosixPath(r['path']).parts)
        require(path.is_file() and not path.is_symlink() and path.stat().st_nlink==1,'regular physical source')
        require(not any(p.is_symlink() or getattr(p,'is_junction',lambda:False)() for p in path.parents),'physical source ancestors')
        data=path.read_bytes()
        require((len(data),hashlib.sha256(data).hexdigest())==pins[r['path']],'physical source bytes changed')
    report['archive_source_budget']=admit_paths(str(temp/'w'/'u'),rows,platform.system())
    report.update(source_materialization_sha256=hashlib.sha256((package.parent/'SOURCE_MATERIALIZATION.json').read_bytes()).hexdigest(),
                  inventory_sha256=hashlib.sha256((package/'PACKAGE_FILES.json').read_bytes()).hexdigest(),
                  source_parent=str(package.parent),bare_store=str(bare),work_root=str(temp/'w'),tested_head=expected_head)
    return report


def materialize(gitdir,head,destination,short_layout=False):
    require(type(short_layout) is bool,'literal layout flag')
    gitdir=Path(gitdir).absolute();destination=Path(destination).absolute()
    require(re.fullmatch('[0-9a-f]{40}',head) is not None and head!='0'*40,'nonzero exact commit')
    require(gitdir.is_dir() and not gitdir.is_symlink(),'real private bare Git directory')
    require(not (gitdir/'index').exists(),'no repository index admitted')
    require(not destination.exists() and not destination.is_symlink(),'fresh source destination')
    require(not any(p.is_symlink() for p in (destination.parent,*destination.parents)),'no symlink destination ancestors')
    def git(*args):return subprocess.run(['git','--git-dir',str(gitdir),*args],check=True,stdout=subprocess.PIPE).stdout
    require(git('rev-parse','--is-bare-repository').strip()==b'true','bare source store required')
    require(git('rev-parse','HEAD^{commit}').decode().strip()==head,'exact fetched HEAD required')
    rows=plan_tree(git('ls-tree','-rz','--full-tree',head,'--','conditional_separation'))
    total=0
    for row in rows:
        size=int(git('cat-file','-s',row['git_blob']));require(0<=size<=MAX_FILE,'source blob size limit')
        row['bytes']=size;total+=size
    require(total<=MAX_TOTAL,'total source size limit')
    if short_layout:
        parent=unaliased(destination.parent)
        unaliased(gitdir)
        require(destination==parent/'s' and gitdir==parent/'g','runner-private short source roots')
        admit_paths(str(destination/'p'),rows,platform.system())
    destination.mkdir()
    for row in rows:
        b=git('cat-file','blob',row['git_blob'])
        require(len(b)==row['bytes'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob'],'exact raw Git blob bytes')
        p=destination/('p' if short_layout else 'conditional_separation')/row['path'];p.parent.mkdir(parents=True,exist_ok=True)
        with p.open('xb') as f:f.write(b)
        row['sha256']=hashlib.sha256(b).hexdigest()
    (destination/'.git').write_text('gitdir: '+gitdir.as_posix()+'\n',encoding='utf-8')
    receipt={'schema':'package-source-blobs-v1','head':head,'files':rows,'index_created':False,'source_role':'raw Git blobs; no checkout/filter/line-ending conversion'}
    if short_layout:receipt.update(layout='runner-private-short-v1',package_directory='p')
    with (destination/'SOURCE_MATERIALIZATION.json').open('x',encoding='utf-8') as f:json.dump(receipt,f,indent=2);f.write('\n')
    return receipt

if __name__=='__main__':
    if sys.flags.optimize:raise SystemExit('optimized package materialization rejected')
    args=sys.argv[1:]
    require(len(args) in {3,4} and (len(args)==3 or args[3]=='--short-layout-v1'),'private bare store, exact head, fresh destination and optional short layout')
    r=materialize(*args[:3],short_layout=len(args)==4);print(json.dumps({'head':r['head'],'files':len(r['files']),'index_created':False}))
