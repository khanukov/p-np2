"""Finite synthetic acquisition-evidence DATA, never dependency execution."""
import importlib.util,json,os,sys,unittest
from pathlib import Path
HELPER=Path(__file__).resolve().parents[1]/'ci/ci_evidence_data_v2.py'
DATA=Path(os.environ['CI_DATA_ROOT']) if 'CI_DATA_ROOT' in os.environ else None
if __name__=='__main__':
 for flag in ['--helper','--data-root']:
  if flag in sys.argv:
   i=sys.argv.index(flag);value=Path(sys.argv[i+1]);del sys.argv[i:i+2]
   if flag=='--helper':HELPER=value
   else:DATA=value;DATA.mkdir(parents=True,exist_ok=False)
LABEL='locked-dependency-materialization'
class AcquisitionEvidence(unittest.TestCase):
 def setUp(self):
  if DATA is None or not DATA.is_dir():raise ValueError('explicit private CI_DATA_ROOT')
  self.root=DATA/self._testMethodName;self.root.mkdir()
  spec=importlib.util.spec_from_file_location('pure_evidence_DATA',HELPER)
  self.m=importlib.util.module_from_spec(spec);spec.loader.exec_module(self.m)
 def fixture(self,name,rc):
  base=self.root/name;base.mkdir();work=base/'work';package=base/'package';work.mkdir();package.mkdir()
  (package/'PACKAGE_FILES.json').write_text('{"schema":"SYNTHETIC_DATA_ONLY","files":[]}')
  command=work/LABEL;command.mkdir()
  payload={'launch.json':{'argv':['SYNTHETIC_DATA_NOT_EXECUTED']},'process.json':{'pid':'SYNTHETIC_NOT_OS_PID'},
           'stdout.txt':'DATA stdout','stderr.txt':'DATA stderr'}
  if rc is not None:payload['terminal.json']={'OS_exit':rc,'scope':'SYNTHETIC_INPUT_NOT_ACTUAL_TERMINAL'}
  for path,value in payload.items():(command/path).write_text(value if isinstance(value,str) else json.dumps(value))
  result=self.m.stage_evidence(work,package,base/'evidence',{'event':'SYNTHETIC_DATA'})
  return base,result,payload
 def test_success_and_failure_receipts_selected(self):
  for rc in [0,1]:
   with self.subTest(input_exit=rc):
    base,result,payload=self.fixture('exit-'+str(rc),rc)
    names={r['path'] for r in result['files']}
    self.assertTrue({'commands/'+LABEL+'/'+p for p in payload}<=names)
    for p in payload:self.assertEqual((base/'work'/LABEL/p).read_bytes(),(base/'evidence/commands'/LABEL/p).read_bytes())
    self.assertEqual(result['command_states'][LABEL],'TERMINAL_PRESENT_UNINTERPRETED')
    self.assertTrue(result['export_complete']);self.assertFalse(result['native_validation_pass'])
 def test_started_without_terminal_is_UNKNOWN_and_incomplete(self):
  base,result,payload=self.fixture('started',None)
  self.assertEqual(result['command_states'].get(LABEL),'STARTED_NO_TERMINAL_UNKNOWN')
  self.assertFalse(result['export_complete']);self.assertFalse(result['native_validation_pass'])
  self.assertFalse((base/'evidence/commands'/LABEL/'terminal.json').exists())
  self.assertTrue(any(o['path']=='commands/'+LABEL+'/terminal.json' for o in result['omissions']))
 def test_unstarted_command_is_not_fabricated(self):
  work=self.root/'work';package=self.root/'package';work.mkdir();package.mkdir()
  (package/'PACKAGE_FILES.json').write_text('{"schema":"SYNTHETIC_DATA_ONLY","files":[]}')
  result=self.m.stage_evidence(work,package,self.root/'evidence',{'event':'SYNTHETIC_DATA'})
  self.assertNotIn(LABEL,result['command_states']);self.assertFalse(result['native_validation_pass'])
if __name__=='__main__':unittest.main(verbosity=2)
