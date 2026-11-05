"""Finite path/archive DATA. Compiler boundaries are explicitly simulated, never Lean evidence."""
import errno,hashlib,importlib.util,io,json,os,tempfile,unittest,warnings,zipfile
from pathlib import Path
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1]
def load(label,relative):
 spec=importlib.util.spec_from_file_location(label,ROOT/relative)
 module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
archive=load('archive_hardening_DATA','ci/portable_ci_data_v1.py')
def private():
 root=Path(os.environ['CI_DATA_ROOT'])
 if not root.is_dir():raise ValueError('explicit existing private DATA required')
 return Path(tempfile.mkdtemp(prefix='path-archive-',dir=root))
def source_zip(names,*,reverse_members=False,reverse_rows=False,rows=None):
 bodies=[(name,b'INERT SOURCE DATA\r\n'+str(i).encode()) for i,name in enumerate(names)]
 if rows is None:
  rows=[{'path':name,'bytes':len(body),'sha256':hashlib.sha256(body).hexdigest()} for name,body in bodies]
 if reverse_rows:rows=list(reversed(rows))
 inventory=json.dumps({'schema':'conditional-separation-source-files-v1','files':rows}).encode()
 members=bodies+[('PACKAGE_FILES.json',inventory)]
 if reverse_members:members.reverse()
 output=io.BytesIO()
 with warnings.catch_warnings():
  warnings.simplefilter('ignore',UserWarning)
  with zipfile.ZipFile(output,'w') as z:
   for name,body in members:z.writestr(name,body)
 return output.getvalue()
class ArchivePaths(unittest.TestCase):
 def setUp(self):self.temp=private()
 def test_self_pinned_multipart_artifacts_rejected(self):
  for index,suffix in enumerate(['.olean.private','.olean.server','.olean.trace','.setup.json','.c.o','.obj','.olean','.ilean']):
   with self.subTest(suffix=suffix):
    dest=self.temp/str(index)
    with self.assertRaises(ValueError):archive.unpack_source(source_zip(['Example'+suffix]),dest)
    self.assertFalse(dest.exists())
 def test_casefold_prefix_and_file_directory_rejected(self):
  pairs=[['Example.lean','example.lean'],['Dir/A.lean','dir/B.lean'],
         ['File','file/Child.lean'],['a/B/x.lean','a/b/y.lean'],['File','File/Child.lean']]
  for i,names in enumerate(pairs):
   for members in (False,True):
    for rows in (False,True):
     with self.subTest(names=names,members=members,rows=rows):
      data=source_zip(names,reverse_members=members,reverse_rows=rows)
      with self.assertRaises(ValueError):archive.source_payloads(data)
      dest=self.temp/(str(i)+str(members)+str(rows))
      with self.assertRaises(ValueError):archive.unpack_source(data,dest)
      self.assertFalse(dest.exists())
 def test_inventory_collision_precedes_missing_pin(self):
  rows=[{'path':n,'bytes':0,'sha256':hashlib.sha256(b'').hexdigest()} for n in ['File','file/Child.lean']]
  for reverse in (False,True):
   with self.subTest(reverse=reverse),self.assertRaisesRegex(ValueError,'collision'):
    archive.source_payloads(source_zip(['README.md'],rows=rows,reverse_rows=reverse))
 def test_valid_source_bytes_and_order(self):
  names=['Dir/A.lean','Dir/B.lean','README.md','LICENSE','lakefile.lean','lake-manifest.json','Src/code.c']
  for reverse in (False,True):
   data=source_zip(names,reverse_members=reverse,reverse_rows=not reverse)
   payloads=archive.source_payloads(data);dest=self.temp/str(reverse)
   archive.unpack_source(data,dest)
   self.assertEqual(set(payloads),set(names)|{'PACKAGE_FILES.json'})
   for name,body in payloads.items():self.assertEqual((dest/name).read_bytes(),body)
 def test_exact_duplicates_and_reserved_paths(self):
  for name in ['../bad','a\\bad','C:/bad','.git/config','.LAKE/x','reports/x','__pycache__/x','AUX.lean','x.','./x','', '.', '.aws/credentials','cache/Fake.olean','A.olean.private/child']:
   with self.subTest(name=name),self.assertRaises(ValueError):archive.source_payloads(source_zip([name]))
  with self.assertRaises(ValueError):archive.source_payloads(source_zip(['Same.lean','Same.lean']))

def make_link(target,link,*,directory=False):
 """Only recognized platform capability denials are skips; EIO propagates."""
 try:link.symlink_to(target,target_is_directory=directory)
 except OSError as error:
  if error.errno in {errno.EACCES,errno.EPERM,errno.ENOSYS,errno.ENOTSUP,errno.EOPNOTSUPP} or getattr(error,'winerror',None) in {50,1314}:
   raise unittest.SkipTest('real link capability unavailable: '+str(error)) from error
  raise
class WorkbenchPaths(unittest.TestCase):
 def setUp(self):
  self.w=load('workbench_path_hardening_DATA','tools/workbench.py')
  self.temp=private();self.attempt=self.temp/'attempt';self.attempt.mkdir()
  (self.attempt/'attempt.json').write_text(json.dumps({'core':str(ROOT)}))
  self.calls=[]
  def simulated_compile(attempt,root,label,source,module,overrides):
   self.calls.append({'label':label,'source':str(source),'module':module})
   if label not in {'exact-closed-guard','final-assembly'}:raise AssertionError('unexpected DATA compile boundary')
   directory=root/(label+'-compile');directory.mkdir()
   (directory/'stdout.txt').write_text('DATA ONLY: NO COMPILER EXECUTED\n[CS_ROOT] Attempt.placeholder\n')
   return []
  self.patches=[patch.object(self.w,'verify_core',return_value='DATA_ONLY_NO_CORE_VALIDATION'),
    patch.object(self.w,'module_sources',return_value=[]),
    patch.object(self.w,'compile_source',side_effect=simulated_compile),
    patch.object(self.w,'command',side_effect=AssertionError('no actual command permitted in path DATA'))]
  for item in self.patches:item.start();self.addCleanup(item.stop)
 def tearDown(self):
  (self.temp/'DATA_BOUNDARIES.json').write_text(json.dumps({'compile_boundaries_simulated':self.calls,
    'source_enumeration':'synthetic empty roster','actual_compiler_invocations':0,
    'R_validation':False,'meaning':'filesystem behavior only; synthetic root log is NOT a kernel receipt'},indent=2))
 def check_data(self):return self.w.check(self.attempt,'Attempt.placeholder')
 def test_mocked_output_components_refused(self):
  original=Path.is_symlink
  for parts in ['.lake','.lake/conditional-check','.lake/conditional-check/runs']:
   with self.subTest(parts=parts):
    target=self.attempt/parts
    with patch.object(Path,'is_symlink',new=lambda p:p==target or original(p)):
     with self.assertRaises(ValueError):self.check_data()
 def test_mocked_junction_components_refused(self):
  for parts in ['.lake','.lake/conditional-check','.lake/conditional-check/runs']:
   with self.subTest(parts=parts):
    target=self.attempt/parts
    with patch.object(Path,'is_junction',new=lambda p:p==target,create=True):
     with self.assertRaises(ValueError):self.check_data()
 def test_real_lake_symlink_refused_without_outside_writes(self):
  outside=self.temp/'outside';outside.mkdir();sentinel=outside/'sentinel';sentinel.write_bytes(b'UNCHANGED')
  make_link(outside,self.attempt/'.lake',directory=True)
  try:
   with self.assertRaises(ValueError):self.check_data()
  finally:
   self.assertEqual(sentinel.read_bytes(),b'UNCHANGED')
   self.assertEqual(sorted(p.name for p in outside.iterdir()),['sentinel'])
 def test_old_shared_final_links_are_never_overwritten(self):
  shared=self.attempt/'.lake/conditional-check';shared.mkdir(parents=True)
  for name in ['Consumer.lean','Assembly.lean']:
   target=self.temp/(name+'.outside');target.write_bytes(b'UNCHANGED')
   make_link(target,shared/name)
  self.check_data()
  for name in ['Consumer.lean','Assembly.lean']:
   self.assertEqual((self.temp/(name+'.outside')).read_bytes(),b'UNCHANGED')
 def test_repeat_runs_generate_sources_in_distinct_owned_runs(self):
  one=self.check_data();two=self.check_data()
  self.assertNotEqual(one['receipts'],two['receipts'])
  for result in [one,two]:
   run=Path(result['receipts'])
   for name in ['STATUS.json','Consumer.lean','Assembly.lean','RESULT.json']:
    self.assertTrue((run/name).is_file(),name)
   for call in self.calls:
    self.assertTrue(Path(call['source']).is_relative_to(self.attempt/'.lake/conditional-check/runs'))
  self.assertFalse((self.attempt/'.lake/conditional-check/Consumer.lean').exists())
 def test_exclusive_final_writer_refuses_existing_and_mocked_aliases(self):
  target=self.temp/'new.lean';original=Path.is_symlink
  with patch.object(Path,'is_symlink',new=lambda p:p==target or original(p)):
   with self.assertRaises(ValueError):self.w.write_new_output(target,'INERT')
  with patch.object(Path,'is_junction',new=lambda p:p==target,create=True):
   with self.assertRaises(ValueError):self.w.write_new_output(target,'INERT')
  self.w.write_new_output(target,'INERT')
  with self.assertRaises(FileExistsError):self.w.write_new_output(target,'REPLACE')
  self.assertEqual(target.read_text(),'INERT')
 def test_real_final_writer_link_refusal(self):
  outside=self.temp/'outside';outside.write_bytes(b'UNCHANGED');link=self.temp/'link.lean'
  make_link(outside,link)
  with self.assertRaises(ValueError):self.w.write_new_output(link,'REPLACE')
  self.assertEqual(outside.read_bytes(),b'UNCHANGED')
 def test_fresh_run_refuses_preexisting_uuid(self):
  existing=self.attempt/'.lake/conditional-check/runs/fixed';existing.mkdir(parents=True)
  sentinel=existing/'STATUS.json';sentinel.write_bytes(b'UNCHANGED')
  with patch.object(self.w.uuid,'uuid4',return_value='fixed'):
   with self.assertRaises(FileExistsError):self.check_data()
  self.assertEqual(sentinel.read_bytes(),b'UNCHANGED')
 def test_link_capability_denial_is_explicit(self):
  with patch.object(Path,'symlink_to',side_effect=OSError(errno.EPERM,'forced DATA capability denial')):
   with self.assertRaises(unittest.SkipTest):make_link(self.temp/'target',self.temp/'link')
 def test_unexpected_link_eio_propagates(self):
  with patch.object(Path,'symlink_to',side_effect=OSError(errno.EIO,'forced DATA unexpected I/O')):
   with self.assertRaises(OSError) as observed:make_link(self.temp/'target',self.temp/'link')
  self.assertEqual(observed.exception.errno,errno.EIO)
if __name__=='__main__':unittest.main(verbosity=2)
