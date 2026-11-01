"""Private/native-CI DATA for physical paths, not a Windows compiler result."""
import hashlib,importlib.util,json,os,subprocess,tempfile,unittest
from pathlib import Path,PureWindowsPath
from unittest.mock import patch

ROOT=Path(os.environ.get('WINDOWS_CONTROL_CORE',Path(__file__).resolve().parents[1])).resolve()
def helper():
    spec=importlib.util.spec_from_file_location('layout_materializer_DATA',ROOT/'ci/package_source_v1.py')
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def private():
    p=Path(os.environ['CI_DATA_ROOT']);
    if not p.is_dir():raise ValueError('existing private DATA root required')
    return Path(tempfile.mkdtemp(prefix='layout-',dir=p))

class Budgets(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.m=helper();cls.rows=json.loads((ROOT/'PACKAGE_FILES.json').read_bytes())['files']
    def test_all_1146_and_literal_old_new(self):
        old=self.m.price_paths(r'D:\a\p-np2\p-np2\source\conditional_separation',self.rows,'Windows')
        new=self.m.price_paths(r'D:\a\_temp\s\p',self.rows,'Windows')
        self.assertEqual(new['owned_modules'],1146)
        self.assertIn('ConditionalSeparation',self.m.owned_paths(self.rows))
        self.assertEqual(old['maxima_utf16']['olean'],253)
        self.assertEqual(new['maxima_utf16']['olean'],221)
        self.assertEqual(max(old['maxima_utf16'].values())+16,277)
        self.assertEqual(max(new['maxima_utf16'].values())+16,245)
        mapping=self.m.owned_paths(self.rows)
        expected={r['path'][5:-5] if r['path'].startswith('core/') else r['path'][:-5]:r['path'] for r in self.rows if r['path'].endswith('.lean') and (r['path'].startswith(('core/','ConditionalSeparation/')) or r['path']=='ConditionalSeparation.lean')}
        self.assertEqual(mapping,expected)
        self.assertIn('Pnp4/Tests/AxiomsAudit',mapping)
        for record in new['details']:
            module=record['module'];root=PureWindowsPath(r'D:\a\_temp\s\p')
            self.assertEqual(record['lengths_utf16']['source'],len(str(root/mapping[module]).encode('utf-16-le'))//2)
            for kind,(base,suffix) in self.m.ARTIFACT_SUFFIXES.items():
                self.assertEqual(record['lengths_utf16'][kind],len(str(root/base/(module+suffix)).encode('utf-16-le'))//2)
        out=private()/'all-owned-path-prices.json';out.write_text(json.dumps({'old':old,'new':new},indent=2))
        with self.assertRaisesRegex(ValueError,'engineering path budget'):
            self.m.admit_paths(old['package_root'],self.rows,'Windows')
        self.assertEqual(self.m.admit_paths(new['package_root'],self.rows,'Windows')['owned_modules'],1146)
    def test_invalid_roots_and_long_prefix(self):
        for root in ['relative',r'C:relative',r'\\server\share\p',r'D:\a\..\p','D:\\'+'long'*30]:
            with self.subTest(root=root),self.assertRaises(ValueError):self.m.admit_paths(root,self.rows,'Windows')
        with self.assertRaisesRegex(ValueError,'supported native system'):self.m.price_paths('/data',self.rows,'Unknown')
    def test_invalid_foreign_and_duplicate_paths(self):
        for rows in [[{'path':'../bad.lean'}],[{'path':'C:/bad.lean'}],[{'path':'foreign/Bad.lean'}],
                     [{'path':'core/A.lean'},{'path':'core/a.lean'}],
                     [{'path':'core/ConditionalSeparation.lean'},{'path':'ConditionalSeparation.lean'}],
                     [{'path':'core/A//B.lean'}],[]]:
            with self.subTest(rows=rows),self.assertRaises(ValueError):self.m.owned_paths(rows)
    def test_oversized_component_rejected(self):
        with self.assertRaises(ValueError):self.m.admit_paths(r'D:\t\s\p',[{'path':'core/'+'A'*240+'.lean'}],'Windows')
    def test_auxiliary_sources_are_not_owned_libraries(self):
        mapping=self.m.owned_paths(self.rows)
        self.assertNotIn('tools/SourceImports',mapping);self.assertNotIn('template/Attempt',mapping)

class Materialization(unittest.TestCase):
    def setUp(self):
        self.m=helper();self.temp=private();self.bare=self.temp/'g';self.log=[]
        self.git('init','--bare',str(self.bare))
        bodies={'core/Tiny.lean':b'-- INERT DATA ONLY\n','ConditionalSeparation.lean':b'-- NO PROOF\n'}
        rows=[{'path':p,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()} for p,b in bodies.items()]
        bodies['PACKAGE_FILES.json']=(json.dumps({'schema':'conditional-separation-source-files-v1','files':rows})+'\n').encode()
        tree={}
        for name,b in bodies.items():
            oid=self.git('hash-object','-w','--stdin',data=b).strip().decode();node=tree;parts=('conditional_separation/'+name).split('/')
            for part in parts[:-1]:node=node.setdefault(part,{})
            node[parts[-1]]=oid
        def emit(node):
            lines=[]
            for name,value in sorted(node.items()):
                mode,kind,oid=('040000','tree',emit(value)) if isinstance(value,dict) else ('100644','blob',value)
                lines.append(f'{mode} {kind} {oid}\t{name}\n')
            return self.git('mktree',data=''.join(lines).encode()).strip().decode()
        self.head=self.git('commit-tree',emit(tree),data=b'Synthetic private DATA\n').strip().decode()
        self.git('update-ref','--no-deref','HEAD',self.head)
    def git(self,*args,data=None):
        argv=['git',*args] if args[0]=='init' else ['git','--git-dir',str(self.bare),*args]
        env=os.environ.copy();env.update(GIT_AUTHOR_NAME='Synthetic DATA',GIT_AUTHOR_EMAIL='data@example.invalid',GIT_COMMITTER_NAME='Synthetic DATA',GIT_COMMITTER_EMAIL='data@example.invalid')
        r=subprocess.run(argv,input=data,capture_output=True,env=env)
        self.log.append({'argv':argv,'OS_exit':r.returncode,'stdout':r.stdout.decode(errors='replace'),'stderr':r.stderr.decode(errors='replace')})
        self.assertEqual(r.returncode,0,self.log[-1]);return r.stdout
    def tearDown(self):
        (self.temp/'git-DATA-commands.json').write_text(json.dumps(self.log,indent=2))
    def short(self):return self.m.materialize(self.bare,self.head,self.temp/'s',short_layout=True)
    def test_default_api_is_unchanged(self):
        out=self.temp/'legacy';receipt=self.m.materialize(self.bare,self.head,out)
        self.assertNotIn('layout',receipt);self.assertNotIn('package_directory',receipt)
        self.assertEqual((out/'conditional_separation/core/Tiny.lean').read_bytes(),b'-- INERT DATA ONLY\n')
        self.assertFalse((out/'p').exists());self.assertFalse((self.bare/'index').exists())
    def test_short_head_source_and_custody(self):
        lines=(ROOT/'ci/conditional-separation-native-v2.yml').read_text(encoding='utf-8').splitlines()
        defaults=lines.index('    defaults:');steps=lines.index('    steps:')
        self.assertEqual(lines[defaults:steps],['    defaults:','      run:','        shell: python'])
        starts=[i for i,line in enumerate(lines) if line.startswith('      - name: ')]
        blocks=[lines[start:stop] for start,stop in zip(starts,starts[1:]+[len(lines)])]
        runs=[block for block in blocks if '        run: |' in block]
        self.assertEqual([block[0].removeprefix('      - name: ') for block in runs],[
            'Package-only raw Git blobs at the exact public feature head',
            'Verified Elan asset and exact Lean toolchain',
            'Exact external foundations only (no project cache)',
            'Fresh project source build, root audit and real unit tests',
            'External attempts, exact R rejections and conditional consumer',
            'Stage bounded owned evidence even on failure'])
        for index,block in enumerate(runs):
            with self.subTest(run_step=index):
                expected='${{ github.workspace }}' if index==0 else '${{ runner.temp }}/s/p'
                self.assertEqual([line for line in block if line.startswith('        working-directory:')],
                                 ['        working-directory: '+expected])
        receipt=self.short();package=self.temp/'s/p'
        report=self.m.checked_layout(package,self.temp,self.head)
        self.assertEqual(receipt['layout'],'runner-private-short-v1')
        self.assertEqual(report['package_root'],str(package))
        self.assertEqual(report['work_root'],str(self.temp/'w'))
        self.assertEqual(report['tested_head'],self.head);self.assertEqual(report['owned_modules'],2)
        self.assertEqual(report['archive_source_budget']['package_root'],str(self.temp/'w/u'))
        self.assertEqual(self.git('rev-parse','HEAD').decode().strip(),self.head)
        self.assertFalse((self.bare/'index').exists())
    def test_existing_source_and_invalid_flag_rejected(self):
        self.short()
        with self.assertRaisesRegex(ValueError,'fresh source destination'):self.short()
        with self.assertRaisesRegex(ValueError,'literal layout flag'):self.m.materialize(self.bare,self.head,self.temp/'new',short_layout=1)
        self.assertFalse((self.temp/'new').exists())
    def test_short_roots_and_wrong_head_rejected(self):
        for dest in [self.temp/'foreign',self.temp/'p']:
            with self.assertRaisesRegex(ValueError,'short source roots'):self.m.materialize(self.bare,self.head,dest,short_layout=True)
            self.assertFalse(dest.exists())
        with self.assertRaisesRegex(ValueError,'exact fetched HEAD'):self.m.materialize(self.bare,'b'*40,self.temp/'s',short_layout=True)
        self.assertFalse((self.temp/'s').exists())
    def test_existing_index_rejected(self):
        (self.bare/'index').write_bytes(b'INERT index DATA')
        with self.assertRaisesRegex(ValueError,'no repository index'):self.short()
        self.assertFalse((self.temp/'s').exists())
    def test_symlink_and_junction_property_rejected(self):
        self.short();package=self.temp/'s/p';original=Path.is_symlink
        with patch.object(Path,'is_symlink',new=lambda p:p==package or original(p)):
            with self.assertRaisesRegex(ValueError,'alias/symlink'):self.m.checked_layout(package,self.temp,self.head)
        with patch.object(Path,'is_junction',new=lambda p:p==package,create=True):
            with self.assertRaisesRegex(ValueError,'alias/symlink'):self.m.checked_layout(package,self.temp,self.head)
    def test_head_pointer_and_receipt_rejected(self):
        self.short();package=self.temp/'s/p'
        with self.assertRaisesRegex(ValueError,'source/head binding'):self.m.checked_layout(package,self.temp,'b'*40)
        pointer=self.temp/'s/.git';pointer.write_text('gitdir: WRONG\n')
        with self.assertRaisesRegex(ValueError,'Git pointer'):self.m.checked_layout(package,self.temp,self.head)
    def test_source_change_rejected(self):
        self.short();package=self.temp/'s/p';(package/'core/Tiny.lean').write_bytes(b'TAMPERED DATA')
        with self.assertRaisesRegex(ValueError,'physical source bytes'):self.m.checked_layout(package,self.temp,self.head)
    def test_metadata_missing_and_duplicate_rejected(self):
        self.short();package=self.temp/'s/p';path=self.temp/'s/SOURCE_MATERIALIZATION.json'
        old=json.loads(path.read_bytes());old['files'].append(old['files'][0]);path.write_text(json.dumps(old))
        with self.assertRaisesRegex(ValueError,'duplicate materialization'):self.m.checked_layout(package,self.temp,self.head)
        path.rename(self.temp/'retained-record.json')
        with self.assertRaisesRegex(ValueError,'regular layout binding'):self.m.checked_layout(package,self.temp,self.head)

if __name__=='__main__':unittest.main(verbosity=2)
