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
    """Literal metadata DATA; external reviewed-C/current-PR-H/owner joins remain external."""
    def prefix(self,text=None):
        import ast
        if text is None:text=(ROOT/'ci/conditional-separation-native-v2.yml').read_text(encoding='utf-8')
        blocks=re.findall(r'        run: \|\n((?:          [^\n]*\n)+)',text)
        self.assertEqual(len(blocks),6)
        tree=ast.parse('\n'.join(line[10:] for line in blocks[0].splitlines()))
        boundaries=[i for i,n in enumerate(tree.body) if isinstance(n,ast.Assign)
                    and any(isinstance(t,ast.Name) and t.id=='temp' for t in n.targets)]
        self.assertEqual(len(boundaries),1,'one literal pre-acquisition boundary required')
        boundary=tree.body[boundaries[0]]
        self.assertEqual(ast.unparse(boundary.value),"Path(os.environ['RUNNER_TEMP']).resolve(strict=True)")
        body=tree.body[:boundaries[0]]
        self.assertEqual([type(n) for n in body],
                         [ast.Import,ast.ImportFrom,ast.If,ast.Assign,ast.Assign,ast.Assign,
                          ast.If,ast.If,ast.Assign,ast.If,ast.If,ast.If])
        self.assertEqual(ast.unparse(body[0]),'import hashlib, json, os, re, subprocess, sys')
        self.assertEqual(ast.unparse(body[1]),'from pathlib import Path')
        self.assertEqual(ast.unparse(body[-1].test),"kind == 'push'")
        allowed={'Path','json.loads',"Path(os.environ['GITHUB_EVENT_PATH']).read_bytes",
                 'repo.get','event.get','ref.startswith','any','re.fullmatch','ValueError','SystemExit'}
        for node in ast.walk(ast.Module(body=body,type_ignores=[])):
            if isinstance(node,ast.Call):self.assertIn(ast.unparse(node.func),allowed)
        return compile(ast.Module(body=body,type_ignores=[]),'literal-metadata-prefix-DATA','exec')

    def run_prefix(self,kind='push',private=False,head=None,controller=None,
                   ref='refs/heads/infrastructure/conditional-separation-package-docfix-20261031',
                   repo='khanukov/p-np2',event_sha=None,workflow_sha=None,inputs=...,
                   missing_env=None,text=None):
        import socket,urllib.request
        from unittest.mock import patch
        data=Path(os.environ['CI_DATA_ROOT']);p=Path(tempfile.mkdtemp(prefix='admission-',dir=data))/'event.json'
        controller='a'*40 if controller is None else controller
        head=controller if head is None else head
        event={'repository':{'full_name':repo,'private':private}}
        if kind=='workflow_dispatch':
            event['inputs']={'controller_sha':controller,'source_sha':head} if inputs is ... else inputs
        p.write_text(json.dumps(event),encoding='utf-8')
        env={'GITHUB_EVENT_PATH':str(p),'GITHUB_EVENT_NAME':kind,'GITHUB_REF':ref,
             'GITHUB_SHA':controller if event_sha is None else event_sha,
             'GITHUB_WORKFLOW_SHA':controller if workflow_sha is None else workflow_sha,
             'CI_CONTROLLER_SHA':controller,'CI_EXPECTED_HEAD':head}
        if missing_env:env.pop(missing_env)
        code=self.prefix(text);scope={}
        denied=AssertionError('metadata prefix attempted a process/network/acquisition effect')
        with patch.dict(os.environ,env,clear=True),patch.object(subprocess,'run',side_effect=denied), \
             patch.object(subprocess,'Popen',side_effect=denied),patch.object(os,'system',side_effect=denied), \
             patch.object(socket,'create_connection',side_effect=denied), \
             patch.object(urllib.request,'urlopen',side_effect=denied),patch.object(Path,'resolve',side_effect=denied):
            exec(code,scope)
        self.assertEqual((scope['controller'],scope['head']),(controller,head))
        self.assertNotIn('temp',scope);self.assertNotIn('git',scope)

    def test_public_exact_head_prefix(self):
        for args in ({},{'kind':'workflow_dispatch'},
                     {'kind':'workflow_dispatch','head':'b'*40,'ref':'refs/heads/reviewed-controller'}):
            with self.subTest(args=args):self.run_prefix(**args)

    def test_invalid_admission_prefix(self):
        cases=[{'private':True},{'private':None},{'repo':'fixture/public'},{'repo':'../fixture'},
               {'repo':'fixture/x:y'},{'head':'0'*40},{'head':'not-sha'},{'controller':'0'*40},
               {'controller':'A'*40},{'head':'b'*40},{'event_sha':'b'*40},{'workflow_sha':'b'*40},
               {'kind':'pull_request'},{'kind':'pull_request_target'},
               {'ref':'refs/heads/main'},{'ref':'refs/heads/master'},{'ref':'refs/tags/v1'},
               {'ref':'refs/heads/infrastructure/conditional-separation-package-parallel-20261101'},
               {'ref':'refs/heads/foreign'}, {'kind':'workflow_dispatch','ref':'refs/tags/v1'},
               {'kind':'workflow_dispatch','inputs':None},{'kind':'workflow_dispatch','inputs':{}},
               {'kind':'workflow_dispatch','inputs':{'controller_sha':'b'*40,'source_sha':'a'*40}},
               {'kind':'workflow_dispatch','inputs':{'controller_sha':'a'*40,'source_sha':'b'*40}},
               {'kind':'workflow_dispatch','inputs':{'controller_sha':'a'*40,'source_sha':'a'*40,'extra':'DATA'}}]
        for args in cases:
            with self.subTest(args=args),self.assertRaises(ValueError):self.run_prefix(**args)

    def test_required_environment_is_not_inherited_from_host(self):
        for key in ('GITHUB_EVENT_PATH','GITHUB_EVENT_NAME','GITHUB_REF','GITHUB_SHA',
                    'GITHUB_WORKFLOW_SHA','CI_CONTROLLER_SHA','CI_EXPECTED_HEAD'):
            with self.subTest(key=key),self.assertRaises(KeyError):self.run_prefix(missing_env=key)

    def test_prefix_extraction_rejects_effects_and_boundary_drift(self):
        text=(ROOT/'ci/conditional-separation-native-v2.yml').read_text(encoding='utf-8')
        boundary="          temp = Path(os.environ['RUNNER_TEMP']).resolve(strict=True)\n"
        drift=(text.replace(boundary,boundary.replace('temp =','work ='),1),
               text.replace(boundary,boundary+boundary,1),
               text.replace(boundary,"          subprocess.run(['INERT_DATA_NEVER_EXECUTE'])\n"+boundary,1),
               text.replace("          if sys.flags.optimize:\n              raise SystemExit('optimized source admission rejected')\n",'',1))
        for changed in drift:
            with self.subTest(change=hashlib.sha256(changed.encode()).hexdigest()),self.assertRaises(AssertionError):
                self.prefix(changed)


class UTF8OperationalIO(unittest.TestCase):
    """Finite exact-expression DATA; never executes the native rejection driver."""
    def prepared(self,write_newline=None):
        import ast,re,types
        from unittest.mock import patch
        source=(ROOT/'tests/lean_rejections.py').read_text(encoding='utf-8')
        tree=ast.parse(source)
        calls=sorted((n for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr in {'read_text','write_text'}),key=lambda n:n.lineno)
        self.assertEqual(len(calls),12)
        work=(ROOT/'tools/workbench.py').read_text(encoding='utf-8')
        functions=[n for n in ast.parse(work).body if isinstance(n,ast.FunctionDef) and n.name in {'name','guard_source'}]
        self.assertEqual([n.name for n in functions],['name','guard_source'])
        allowed={'isinstance','re.fullmatch','ValueError','name'}
        for n in ast.walk(ast.Module(body=functions,type_ignores=[])):
            if isinstance(n,ast.Call):self.assertIn(ast.unparse(n.func),allowed)
        pure={'__builtins__':{'isinstance':isinstance,'str':str,'ValueError':ValueError},'re':re}
        exec(compile(ast.Module(body=functions,type_ignores=[]),'literal-pure-guard-DATA','exec'),pure)
        data=Path(os.environ['CI_DATA_ROOT']).resolve()
        base=Path(tempfile.mkdtemp(prefix='utf8-boundary-data-',dir=data))
        for part in ['attempt','package/template','receipts/axiom-guard-compile','receipts/type-guard-compile','suite']:(base/part).mkdir(parents=True,exist_ok=True)
        wrong=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='wrong' for t in n.targets))
        sample=pure['guard_source']('Attempt.unit','True')+wrong
        self.assertIn('\u2190',sample);self.assertIn('\u2200',sample);self.assertIn('\u2203',sample);self.assertIn('\u00ac',sample)
        scope={'__builtins__':{},'A':base/'attempt','P':base/'package','C':base/'suite','root':base/'receipts','p':base/'source.lean','shadow':base/'shadow.lean','helper':base/'helper.lean','consumer':base/'Consumer.lean','m':types.SimpleNamespace(guard_source=pure['guard_source']),'text':sample,'result':{'qualification':sample},'json':json}
        original=Path.open
        def cp1252(path,mode='r',buffering=-1,encoding=None,errors=None,newline=None):
            if 'b' not in mode and encoding in (None,'locale'):encoding='cp1252'
            if 'b' not in mode and any(c in mode for c in 'wax') and newline is None:newline=write_newline
            return original(path,mode,buffering,encoding,errors,newline)
        return ast,calls,scope,sample,patch.object(Path,'open',new=cp1252)
    def evaluate(self,ast,node,scope):
        return eval(compile(ast.Expression(body=node),'literal-rejection-expression-DATA','eval'),scope)
    def assert_utf8_text_write(self,path,text,write_newline=None):
        import io
        # None preserves the ordinary platform default, including Windows CRLF.
        translation=os.linesep if write_newline is None else write_newline
        with io.TextIOWrapper(io.BytesIO(),encoding='utf-8',newline=translation) as model:
            model.write(text);model.flush();physical=model.buffer.getvalue()
        raw=path.read_bytes()
        self.assertEqual(raw,physical)
        with io.TextIOWrapper(io.BytesIO(raw),encoding='utf-8',newline=None) as reader:
            self.assertEqual(reader.read(),text.replace('\r\n','\n').replace('\r','\n'))
    def test_actual_write_expressions_both_newline_modes(self):
        for mode in ('\n','\r\n'):
            ast,calls,scope,sample,locale=self.prepared(write_newline=mode)
            selected=[n for n in calls if n.func.attr=='write_text']
            self.assertEqual(len(selected),7)
            for node in selected:
                with self.subTest(newline=repr(mode),line=node.lineno):
                    expected=self.evaluate(ast,node.args[0],scope)
                    path=self.evaluate(ast,node.func.value,scope)
                    with locale:self.evaluate(ast,node,scope)
                    self.assert_utf8_text_write(path,expected,write_newline=mode)
                    self.assertIn('\n',expected)
                    wrong=expected.replace('\n','\r\n' if mode=='\n' else '\n').encode('utf-8')
                    with self.assertRaises(AssertionError):self.assertEqual(path.read_bytes(),wrong)
    def test_actual_guard_writes_with_cp1252_default(self):
        ast,calls,scope,sample,locale=self.prepared()
        selected=[n for n in calls if n.func.attr=='write_text' and isinstance(n.func.value,ast.Name) and n.func.value.id=='consumer']
        self.assertEqual(len(selected),2)
        for node in selected:
            with self.subTest(line=node.lineno):
                expected=self.evaluate(ast,node.args[0],scope)
                with locale:self.evaluate(ast,node,scope)
                self.assert_utf8_text_write(scope['consumer'],expected)
    def test_metadata_template_and_log_reads_with_cp1252_default(self):
        ast,calls,scope,sample,locale=self.prepared()
        selected=[n for n in calls if n.func.attr=='read_text']
        self.assertEqual(len(selected),5)
        for node in selected:
            with self.subTest(line=node.lineno):
                path=self.evaluate(ast,node.func.value,scope);path.write_bytes(sample.encode('utf-8'))
                with locale:self.assertEqual(self.evaluate(ast,node,scope),sample)
                path.write_bytes(b'\xff')
                with locale,self.assertRaises(UnicodeDecodeError):self.evaluate(ast,node,scope)
    def test_all_text_boundaries_explicit_strict_utf8(self):
        ast,calls,scope,sample,locale=self.prepared()
        for node in calls:
            with self.subTest(line=node.lineno):
                keywords={k.arg:k.value for k in node.keywords}
                self.assertIn('encoding',keywords)
                self.assertEqual(ast.literal_eval(keywords['encoding']),'utf-8')
                self.assertNotIn('errors',keywords)
    def test_source_and_receipt_writes_with_cp1252_default(self):
        ast,calls,scope,sample,locale=self.prepared()
        selected=[n for n in calls if n.func.attr=='write_text']
        self.assertEqual(len(selected),7)
        for node in selected:
            with self.subTest(line=node.lineno):
                expected=self.evaluate(ast,node.args[0],scope)
                path=self.evaluate(ast,node.func.value,scope)
                with locale:self.evaluate(ast,node,scope)
                self.assert_utf8_text_write(path,expected)

class AssemblyNegativeDATA(unittest.TestCase):
    """Inert receipt-protocol DATA; fake compiler callbacks NEVER execute Lean."""
    def fixture(self, mutation=None):
        import ast,datetime,types
        from unittest.mock import patch
        tree=ast.parse((ROOT/'tests/lean_rejections.py').read_bytes())
        fixture=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='assembly_negative')
        work=ast.parse((ROOT/'tools/workbench.py').read_bytes())
        names={'name','guard_source','guard_body','check','command'}
        functions=[n for n in work.body if isinstance(n,ast.FunctionDef) and n.name in names]
        self.assertEqual({n.name for n in functions},names)
        compiler=next(n for n in work.body if isinstance(n,ast.FunctionDef) and n.name=='compile_source')
        command_call=next(n.value for n in compiler.body if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and ast.unparse(n.value.func)=='command')
        command_expression=compile(ast.Expression(body=command_call),'OWN_PRODUCTION_COMPILE_COMMAND_DATA','eval')
        with tempfile.TemporaryDirectory(prefix='FAKE_DATA_NOT_LEAN-',dir=os.environ['CI_DATA_ROOT']) as temporary:
            base=Path(temporary);attempt=base/'attempt';core=base/'core';suite=base/'suite'
            for p in (attempt,core,suite):p.mkdir()
            runs=attempt/'.lake/conditional-check/runs';calls=[];records=[]
            def save(path,value):path.write_bytes((json.dumps(value)+'\n').encode('utf-8'))
            def fresh(a):
                run=runs/'FAKE_DATA_NOT_AN_OS_RECEIPT';run.mkdir(parents=True);return run
            def output(path,text):path.write_bytes(text.encode('utf-8'))
            def compile_data(a,run,label,source,module,overrides):
                self.assertEqual(a,attempt);calls.append(label)
                self.assertIn(label,{'own-0','exact-closed-guard','final-assembly'})
                directory=run/(label+'-compile')
                setup=dict(name=module,isModule=False,options={},plugins=[],dynlibs=[],importArts=overrides)
                save(run/(label+'.setup.json'),setup)
                (run/(label+'.source.lean.txt')).write_bytes(source.read_bytes())
                argv=['lake','env','lean','-DwarningAsError=true','--root='+str(attempt),
                      '--setup='+str(run/(label+'.setup.json')),'-o',str(run/(module+'.olean')),str(source)]
                code=1 if label=='final-assembly' else 0
                if label=='exact-closed-guard' and mutation=='guard_failure':code=1
                if label=='final-assembly' and mutation=='accepted':code=0
                log='[CS_ROOT] Attempt.unit\n'
                if label=='final-assembly':log=f'{source}:9:1: error: Application type mismatch: Attempt.unit has type\n  True\nbut is expected to have type\n  ConditionalSeparation.OpenProblem.R\n'
                class InertProcess:
                    pid=1  # DATA only, never an OS observation.
                    def __init__(self,actual,*,cwd,stdout,stderr,**options):
                        self.rc=code
                        self_waits.append(False)
                        self.index=len(self_waits)-1
                        self_outer.assertEqual(actual,argv);self_outer.assertEqual(cwd,core)
                        stdout.write(log.encode('utf-8'))
                    def wait(self):self_waits[self.index]=True;return self.rc
                self_outer=self;self_waits=[]
                scope['subprocess']=types.SimpleNamespace(Popen=InertProcess)
                failure=None
                try:
                    eval(command_expression,{'__builtins__':{},'command':scope['command'],'root':run,'label':label,'attempt':a,
                         'setup_path':run/(label+'.setup.json'),'output':run/(module+'.olean'),'source':source,'core':core,'str':str})
                except RuntimeError as error:failure=error
                self.assertEqual(self_waits,[True])
                if label=='final-assembly':
                    if mutation=='missing_terminal':(directory/'terminal.json').unlink()
                    if mutation=='unknown_terminal':save(directory/'terminal.json',dict(OS_exit=None,end='2020-01-01T00:00:00+00:00'))
                    if mutation=='wrong_label':failure=RuntimeError(f'final-assembly rejected or failed (exit 1); see {directory}')
                    if mutation=='bool_terminal':save(directory/'terminal.json',dict(OS_exit=True,end='2020-01-01T00:00:00+00:00'))
                    if mutation=='wrong_exit':save(directory/'terminal.json',dict(OS_exit=2,end='2020-01-01T00:00:00+00:00'))
                    if mutation=='unexpected_error':(directory/'stdout.txt').write_bytes(b'error: unknown module')
                    if mutation=='wrong_R':(directory/'stdout.txt').write_bytes(log.replace('ConditionalSeparation.OpenProblem.R','Decoy.R').encode('utf-8'))
                    if mutation=='expected_recovery':(directory/'stdout.txt').write_bytes((log+f'{source}:20:1: error: nonallowed axiom sorryAx\n{source}:30:1: error: nonallowed axiom sorryAx\n').encode('utf-8'))
                    if mutation=='extra_error':(directory/'stdout.txt').write_bytes((log+f'{source}:10:1: error: unrelated error\n').encode('utf-8'))
                    if mutation=='stderr':(directory/'stderr.txt').write_bytes(b'FAKE unexpected stderr')
                    if mutation=='wrong_guard_root':(run/'exact-closed-guard-compile/stdout.txt').write_bytes(b'[CS_ROOT] Other.unit\n')
                    if mutation=='extra_axiom':(run/'exact-closed-guard-compile/stdout.txt').write_bytes(b'[CS_ROOT] Attempt.unit\n[CS_AXIOM] Fake.bad\n')
                    if mutation=='wrong_context':setup['importArts']={};save(run/(label+'.setup.json'),setup)
                    if mutation=='wrong_argv':argv.append('--unexpected');save(directory/'launch.json',dict(argv=argv,cwd=str(core),start='2020-01-01T00:00:00+00:00'))
                    if mutation=='wrong_cwd':save(directory/'launch.json',dict(argv=argv,cwd=str(base),start='2020-01-01T00:00:00+00:00'))
                    if mutation=='wrong_source':(run/(label+'.source.lean.txt')).write_bytes(b'FAKE altered source')
                    if mutation=='wrong_guard_source':(run/'exact-closed-guard.source.lean.txt').write_bytes(b'FAKE altered guard')
                    if mutation=='wrong_attempt_source':(run/'own-0.source.lean.txt').write_bytes(b'FAKE altered attempt')
                    if mutation=='unknown_exception':raise RuntimeError('FAKE unrelated runtime error')
                    if mutation=='extra_run':(runs/'EXTRA_FAKE_RUN').mkdir()
                if failure is not None:raise failure
                return [str(run/(module+'.olean'))]  # No object is created or represented as genuine.
            scope=dict(Path=Path,json=json,re=re,datetime=datetime,os=types.SimpleNamespace(name='posix',getpgid=lambda pid:1),ALLOWED={'propext','Classical.choice','Quot.sound'},
                       read_json=lambda path:{'core':str(core)},verify_core=lambda p:'a'*64,
                       fresh_check_run=fresh,write_new_output=output,module_sources=lambda a,r:[('Attempt',attempt/'Attempt.lean')],compile_source=compile_data)
            exec(compile(ast.Module(body=functions,type_ignores=[]),'OWN_CHECK_BODY_FAKE_COMPILER_DATA','exec'),scope)
            def check(a,proof,**kwargs):
                self.assertEqual((a,proof),(attempt,'Attempt.unit'));self.assertEqual(kwargs,{'expected':'True','assemble':True})
                return scope['check'](a,proof,**kwargs)
            native=dict(A=attempt,P=core,C=suite,records=records,header='import ConditionalSeparation.OpenProblem\nnamespace Attempt\n',
                        body=lambda text:(attempt/'Attempt.lean').write_bytes(text.encode('utf-8')),hashlib=hashlib,json=json,
                        m=types.SimpleNamespace(check=check,guard_source=scope['guard_source'],ALLOWED=scope['ALLOWED']))
            exec(compile(ast.Module(body=[fixture],type_ignores=[]),'OWN_G10_RECEIPT_PROTOCOL_DATA','exec'),native)
            with patch.object(subprocess,'Popen',side_effect=AssertionError('NO compiler/process DATA effect')),patch.object(subprocess,'run',side_effect=AssertionError('NO operational DATA effect')):
                native['assembly_negative']()
            self.assertEqual(calls,['own-0','exact-closed-guard','final-assembly'])
            self.assertEqual(len(records),1);self.assertIs(records[0]['PASS'],True)
            self.assertEqual((records[0]['guard_OS_exit'],records[0]['assembly_OS_exit']),(0,1))
            return records
    def test_native_entry_registers_exact_assembly_fixture(self):
        import ast
        tree=ast.parse((ROOT/'tests/lean_rejections.py').read_bytes())
        fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='assembly_negative')
        calls=[n for n in ast.walk(fn) if isinstance(n,ast.Call) and ast.unparse(n.func)=='m.check']
        self.assertEqual(len(calls),1)
        self.assertEqual({k.arg:ast.literal_eval(k.value) for k in calls[0].keywords},{'expected':'True','assemble':True})
        self.assertTrue(any(isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and ast.unparse(n.value.func)=='assembly_negative' for n in tree.body))
    def test_closed_true_then_specific_assembly_failure_data(self):self.fixture()
    def test_actual_compile_command_suffix_is_the_rejection_boundary(self):
        self.assertIn('final-assembly-compile rejected or failed (exit 1);',self.fixture()[0]['error'])
    def test_unsuffixed_fake_exception_is_not_the_production_boundary(self):
        with self.assertRaises(RuntimeError):self.fixture('wrong_label')
    def test_expected_assembly_guard_recovery_is_still_rejected(self):self.fixture('expected_recovery')
    def test_guard_failure_or_assembly_acceptance_rejects(self):
        for change in ('guard_failure','accepted','missing_terminal','unknown_terminal','bool_terminal','wrong_exit','unknown_exception','extra_run'):
            with self.subTest(change=change),self.assertRaises((RuntimeError,OSError)):self.fixture(change)
    def test_unrelated_diagnostics_never_count_as_assembly_negative(self):
        for change in ('unexpected_error','wrong_R','extra_error','stderr','wrong_guard_root','extra_axiom'):
            with self.subTest(change=change),self.assertRaises(RuntimeError):self.fixture(change)
    def test_source_setup_command_context_mismatch_rejects(self):
        for change in ('wrong_context','wrong_argv','wrong_cwd','wrong_source','wrong_guard_source','wrong_attempt_source'):
            with self.subTest(change=change),self.assertRaises(RuntimeError):self.fixture(change)


if __name__=='__main__':unittest.main()
