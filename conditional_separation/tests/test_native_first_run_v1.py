"""Finite DATA for registration and package-only Git materialization, not native CI."""
import hashlib,importlib.util,json,os,re,subprocess,tempfile,unittest
from pathlib import Path
ROOT=Path(os.environ.get('FIRST_RUN_CORE',Path(__file__).resolve().parents[1])).resolve()

def load_materializer():
    p=ROOT/'ci/package_source_v1.py'
    spec=importlib.util.spec_from_file_location('package_source_test',p)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module


def symlink_capability(link,target):
    import errno
    try:link.symlink_to(target,target_is_directory=True)
    except OSError as e:
        allowed={errno.EPERM,errno.EACCES,errno.ENOSYS,errno.ENOTSUP,getattr(errno,'EOPNOTSUPP',errno.ENOTSUP)}
        if e.errno not in allowed and getattr(e,'winerror',None) not in {50,1314}:raise
        return {'available':False,'errno':e.errno,'winerror':getattr(e,'winerror',None)}
    return {'available':True,'errno':None,'winerror':None}

class Registration(unittest.TestCase):
    def core_and_globs(self):
        rows=json.loads((ROOT/'PACKAGE_FILES.json').read_bytes())['files']
        modules={r['path'][5:-5].replace('/','.') for r in rows if r['path'].startswith('core/') and r['path'].endswith('.lean')}
        text=(ROOT/'lakefile.lean').read_text().split('@[default_target]')[0]
        globs=re.findall(r'\.(andSubmodules|submodules|one) `([A-Za-z0-9_.]+)',text)
        self.assertTrue(globs);return modules,globs
    def test_no_nonexistent_root(self):
        modules,globs=self.core_and_globs()
        for kind,root in globs:
            if kind!='submodules':self.assertIn(root,modules)
    def test_complete_exact_registration(self):
        modules,globs=self.core_and_globs(); selected=[]
        for kind,root in globs:
            if kind!='submodules':selected.append(root)
            if kind!='one':selected.extend(m for m in modules if m.startswith(root+'.'))
        self.assertEqual(set(selected),modules)
        self.assertEqual(len(selected),len(modules))
    def test_no_monorepo_checkout(self):
        workflow=(ROOT/'ci/conditional-separation-native-v2.yml').read_text()
        self.assertNotIn('uses: actions/checkout@',workflow)
        self.assertIn('git',workflow)
        self.assertNotIn('core.protectNTFS=false',workflow)

class Paths(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.m=load_materializer()
    def row(self,path='conditional_separation/core/Good.lean',mode='100644',kind='blob',oid=None):
        return f'{mode} {kind} {oid or "a"*40}\t{path}\0'.encode()
    def test_valid_regular_and_executable(self):
        rows=self.m.plan_tree(self.row()+self.row('conditional_separation/ci/script.py','100755'))
        self.assertEqual([r['path'] for r in rows],['core/Good.lean','ci/script.py'])
    def test_rejected_names(self):
        for name in ['../escape','/absolute','a/../b','a//b','a\\b','a:b','AUX.lean','sub/CoM1.txt','NUL','trailing.','trailing ','a\nname','.git/config','.lake/owned.olean','__pycache__/x','x.olean','x.olean.private','x.ilean','x.o']:
            with self.subTest(name=name),self.assertRaises(ValueError):self.m.plan_tree(self.row('conditional_separation/'+name))
    def test_foreign_path(self):
        with self.assertRaises(ValueError):self.m.plan_tree(self.row('Facts/Sunflower/Aux.lean'))
    def test_symlink_submodule_and_malformed(self):
        for raw in [self.row(mode='120000'),self.row(mode='160000',kind='commit'),self.row(oid='z'*40),b'bad',b'']:
            with self.subTest(raw=raw),self.assertRaises(ValueError):self.m.plan_tree(raw)
    def test_duplicates_case_and_file_parent(self):
        for raw in [self.row()+self.row(),self.row()+self.row('conditional_separation/core/good.lean'),self.row('conditional_separation/a')+self.row('conditional_separation/a/b')]:
            with self.subTest(raw=raw),self.assertRaises(ValueError):self.m.plan_tree(raw)

    def test_directory_prefix_spelling(self):
        for a,b in [('Foo/a','foo/b'),('Top/Inner/a','Top/inner/b'),('Foo','foo/a')]:
            with self.subTest(paths=[a,b]),self.assertRaises(ValueError):self.m.plan_tree(self.row('conditional_separation/'+a)+self.row('conditional_separation/'+b))
        self.assertEqual(len(self.m.plan_tree(self.row('conditional_separation/Foo/a')+self.row('conditional_separation/Foo/b'))),2)

class GitExport(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.m=load_materializer()
        data=os.environ.get('CI_DATA_ROOT')
        if not data or not Path(data).is_dir():raise RuntimeError('explicit existing private CI_DATA_ROOT required')
        cls.data=Path(data).resolve()
    def setUp(self):
        self.base=Path(tempfile.mkdtemp(prefix='git-source-data-',dir=self.data));self.bare=self.base/'objects.git';self.commands=[]
        self.git('init','--bare',str(self.bare))
        self.payloads={'conditional_separation/lakefile.lean':b'import Lake\n','conditional_separation/raw.txt':b'CRLF\r\nLF\n','Facts/Sunflower/FactSunflower/Proof/Sunflower/Aux.lean':b'unrelated DATA\n'}
        tree={}
        for path,b in self.payloads.items():
            oid=self.git('--git-dir',str(self.bare),'hash-object','-w','--stdin',data=b).strip().decode();node=tree;parts=path.split('/')
            for part in parts[:-1]:node=node.setdefault(part,{})
            node[parts[-1]]=oid
        def emit(node):
            lines=[]
            for name,value in sorted(node.items()):
                mode,kind,oid=('040000','tree',emit(value)) if isinstance(value,dict) else ('100644','blob',value)
                lines.append(f'{mode} {kind} {oid}\t{name}\n')
            return self.git('--git-dir',str(self.bare),'mktree',data=''.join(lines).encode()).strip().decode()
        self.head=self.git('--git-dir',str(self.bare),'commit-tree',emit(tree),data=b'Synthetic DATA only\n').strip().decode()
        self.git('--git-dir',str(self.bare),'update-ref','--no-deref','HEAD',self.head)
    def git(self,*args,data=None,cwd=None):
        env=os.environ.copy();env.update(GIT_AUTHOR_NAME='Synthetic DATA',GIT_AUTHOR_EMAIL='data@example.invalid',GIT_COMMITTER_NAME='Synthetic DATA',GIT_COMMITTER_EMAIL='data@example.invalid')
        p=subprocess.run(['git',*args],input=data,capture_output=True,cwd=cwd,env=env)
        self.commands.append({'argv':['git',*args],'OS_exit':p.returncode,'stdout':p.stdout.decode(errors='replace'),'stderr':p.stderr.decode(errors='replace')})
        self.assertEqual(p.returncode,0,self.commands[-1]);return p.stdout
    def tearDown(self):
        (self.base/'fixture-commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
    def test_export_exact_bytes_head_and_exclusion(self):
        dest=self.base/'source';receipt=self.m.materialize(self.bare,self.head,dest)
        self.assertEqual(receipt['head'],self.head);self.assertFalse((self.bare/'index').exists());self.assertFalse((dest/'Facts').exists())
        self.assertEqual(self.git('rev-parse','HEAD',cwd=dest).decode().strip(),self.head)
        self.assertEqual({r['path'] for r in receipt['files']},{'lakefile.lean','raw.txt'})
        for path,b in self.payloads.items():
            if path.startswith('conditional_separation/'):
                self.assertEqual((dest/path).read_bytes(),b)
        with self.assertRaises(ValueError):self.m.materialize(self.bare,self.head,dest)
    def test_wrong_head_and_existing_index(self):
        dest=self.base/'source'
        with self.assertRaises(ValueError):self.m.materialize(self.bare,'a'*40,dest)
        self.assertFalse(dest.exists());(self.bare/'index').write_bytes(b'DATA')
        with self.assertRaises(ValueError):self.m.materialize(self.bare,self.head,dest)
        self.assertFalse(dest.exists())
    def test_symlink_destination(self):
        from unittest.mock import patch
        link=self.base/'source';original=Path.is_symlink
        def relevant_property(path):return path==link or original(path)
        with patch.object(Path,'is_symlink',new=relevant_property):
            with self.assertRaisesRegex(ValueError,'fresh source destination'):
                self.m.materialize(self.bare,self.head,link)
        self.assertFalse(link.exists())
    def test_real_symlink_capability(self):
        link=self.base/'source';cap=symlink_capability(link,self.data)
        (self.base/'symlink-capability.json').write_text(json.dumps(dict(cap,scope='REAL_CURRENT_HOST_CAPABILITY',os_name=os.name)))
        if not cap['available']:self.skipTest('real symlink unavailable: '+repr(cap))
        with self.assertRaisesRegex(ValueError,'fresh source destination'):
            self.m.materialize(self.bare,self.head,link)
    def test_forced_symlink_capability_denial(self):
        import errno
        from unittest.mock import patch
        link=self.base/'source'
        with patch.object(Path,'symlink_to',side_effect=PermissionError(errno.EPERM,'forced DATA denial')):
            cap=symlink_capability(link,self.data)
        self.assertFalse(cap['available']);self.assertEqual(cap['errno'],errno.EPERM);self.assertFalse(link.exists())
        (self.base/'forced-capability.json').write_text(json.dumps(dict(cap,scope='DATA_FORCED_DENIAL_NOT_HOST_OBSERVATION')))
    def test_unexpected_symlink_error_propagates(self):
        import errno
        from unittest.mock import patch
        with patch.object(Path,'symlink_to',side_effect=OSError(errno.EIO,'forced DATA IO failure')):
            with self.assertRaises(OSError):symlink_capability(self.base/'source',self.data)
    def test_case_conflict_rejected_before_destination(self):
        blob=self.git('--git-dir',str(self.bare),'hash-object','-w','--stdin',data=b'DATA').strip().decode()
        sub=self.git('--git-dir',str(self.bare),'mktree',data=f'100644 blob {blob}\ta\n'.encode()).strip().decode()
        sub_b=self.git('--git-dir',str(self.bare),'mktree',data=f'100644 blob {blob}\tb\n'.encode()).strip().decode()
        inner=self.git('--git-dir',str(self.bare),'mktree',data=f'040000 tree {sub}\tFoo\n040000 tree {sub_b}\tfoo\n'.encode()).strip().decode()
        tree=self.git('--git-dir',str(self.bare),'mktree',data=f'040000 tree {inner}\tconditional_separation\n'.encode()).strip().decode()
        head=self.git('--git-dir',str(self.bare),'commit-tree',tree,data=b'Case DATA only\n').strip().decode()
        self.git('--git-dir',str(self.bare),'update-ref','--no-deref','HEAD',head)
        dest=self.base/'source'
        with self.assertRaisesRegex(ValueError,'inconsistent directory-prefix spelling'):self.m.materialize(self.bare,head,dest)
        self.assertFalse(dest.exists())

class AdmissionPrefix(unittest.TestCase):
    """Execute only the literal metadata prefix, before any Git/process root."""
    def prefix(self):
        import ast
        text=(ROOT/'ci/conditional-separation-native-v2.yml').read_text()
        block=re.findall(r'        run: \|\n((?:          [^\n]*\n)+)',text)[0]
        tree=ast.parse('\n'.join(line[10:] for line in block.splitlines()))
        body=[]
        for node in tree.body:
            if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='work' for t in node.targets):break
            body.append(node)
        self.assertTrue(body)
        for node in ast.walk(ast.Module(body=body,type_ignores=[])):
            if isinstance(node,ast.Call):self.assertNotEqual(ast.unparse(node.func),'subprocess.run')
        return compile(ast.Module(body=body,type_ignores=[]),'literal-admission-prefix-DATA','exec')
    def run_prefix(self,kind='pull_request',private=False,head=None,expected=None,ref='refs/heads/feature',repo='fixture/public'):
        from unittest.mock import patch
        data=Path(os.environ['CI_DATA_ROOT']);p=Path(tempfile.mkdtemp(prefix='admission-',dir=data))/'event.json'
        head=head or 'a'*40;expected=expected or head
        row={'full_name':repo,'private':private}
        event={'pull_request':{'head':{'sha':head,'repo':row}},'repository':row}
        p.write_text(json.dumps(event))
        env={'GITHUB_EVENT_PATH':str(p),'GITHUB_EVENT_NAME':kind,'GITHUB_SHA':head,'GITHUB_REF':ref,'CI_EXPECTED_HEAD':expected}
        with patch.dict(os.environ,env):exec(self.prefix(),{})
    def test_public_exact_head_prefix(self):
        for kind in ['pull_request','push','workflow_dispatch']:
            with self.subTest(kind=kind):self.run_prefix(kind=kind)
    def test_invalid_admission_prefix(self):
        for args in [{'private':True},{'private':None},{'expected':'b'*40},{'head':'0'*40},{'head':'not-sha'},{'repo':'../fixture'},{'repo':'fixture/x:y'},{'kind':'pull_request_target'},{'kind':'push','ref':'refs/heads/main'},{'kind':'workflow_dispatch','ref':'refs/tags/v1'}]:
            with self.subTest(args=args),self.assertRaises(ValueError):self.run_prefix(**args)

if __name__=='__main__':unittest.main()
