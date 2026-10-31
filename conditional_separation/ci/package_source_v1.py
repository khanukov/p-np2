"""Package-only Git blob export: no checkout/index, filters or archive extraction."""
import hashlib,json,re,subprocess,sys
from pathlib import Path

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

def materialize(gitdir,head,destination):
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
    destination.mkdir()
    for row in rows:
        b=git('cat-file','blob',row['git_blob'])
        require(len(b)==row['bytes'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob'],'exact raw Git blob bytes')
        p=destination/'conditional_separation'/row['path'];p.parent.mkdir(parents=True,exist_ok=True)
        with p.open('xb') as f:f.write(b)
        row['sha256']=hashlib.sha256(b).hexdigest()
    (destination/'.git').write_text('gitdir: '+gitdir.as_posix()+'\n',encoding='utf-8')
    receipt={'schema':'package-source-blobs-v1','head':head,'files':rows,'index_created':False,'source_role':'raw Git blobs; no checkout/filter/line-ending conversion'}
    with (destination/'SOURCE_MATERIALIZATION.json').open('x',encoding='utf-8') as f:json.dump(receipt,f,indent=2);f.write('\n')
    return receipt

if __name__=='__main__':
    if sys.flags.optimize:raise SystemExit('optimized package materialization rejected')
    require(len(sys.argv)==4,'private bare store, exact head and fresh destination required')
    r=materialize(*sys.argv[1:]);print(json.dumps({'head':r['head'],'files':len(r['files']),'index_created':False}))
