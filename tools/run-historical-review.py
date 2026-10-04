"""Run reviewed GP historical regressions without companion access or live CAS."""
import ast,json,os,sys,re,xml.etree.ElementTree as ET
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
H=ROOT/'oracle/history/checkout'
sys.dont_write_bytecode=True
sys.path[:0]=[str(ROOT/'oracle/checkout'),str(H),str(ROOT/'oracle/checkout/tests')]
os.environ['PYTHONDONTWRITEBYTECODE']='1'
os.environ['TEMP']=os.environ['TMP']=str(ROOT/'tmp')
os.environ['GP_RUN_SLOW_CHAIN_REPLAY']='1'
# Explicitly reviewed exclusions. Mixed digest/native tests are excluded as a
# whole; separate corpus probes cover their offline hash boundary where needed.
EXCLUDE={
 'test_fixture_is_a_deterministic_copy_and_projection_of_native_inputs',
 'test_live_native_bindings_when_sibling_checkout_is_available',
 'test_current_native_receipt_reproduces_checked_in_projection',
 'test_current_native_source_files_match_frozen_bindings',
 'test_checked_in_copy_is_byte_identical_to_landed_native_certificate',
 'test_native_receipt_bindings_match_without_running_release_suite',
 'test_current_native_seam_files_and_all_transitive_bindings_match',
 'test_frozen_projection_rebuilds_from_the_landed_native_manifest',
 'test_live_jc_commit_sources_and_declarations_are_bound',
 'test_declaration_and_digest_drift_are_refused_before_use',
 'test_frozen_digest_and_native_bindings_are_checked',
 'test_checked_in_native_bindings_are_current',
}
def reason(path,name):
 if path.endswith('test_jc_h3_pin_ablation_frontier.py'):
  return 'Default build consumes unfrozen companion campaign receipts; completed sweep manifest required.'
 if name.startswith('test_real_singular'):
  return 'Requires real Singular execution; offline historical review does not configure that backend.'
 if name in EXCLUDE or name.startswith('test_native_bindings_'):
  return 'Reads or regenerates companion campaign bindings; completed sweep manifest required.'
 return None

def guard(event,args):
 if event=='open' and isinstance(args[0],(str,bytes)):
  path=os.fsdecode(args[0]).replace('\\','/').lower()
  if '/math-stuff/' in path or '/grandportage-jc-campaign/' in path:
   raise RuntimeError('Offline historical review attempted companion access: '+path)
 if event=='subprocess.Popen':
  command=args[0]
  if command is None:
   match=re.match(r'^(?:"([^"]+)"|(\S+))',args[1]);command=next(x for x in match.groups() if x is not None)
  executable=os.fsdecode(command).replace('\\','/').split('/')[-1].lower()
  if executable not in ('git','git.exe'):
   raise RuntimeError('Offline historical review attempted external execution: '+executable)
sys.addaudithook(guard)
coverage=json.loads((ROOT/'corpus/REVIEW-COVERAGE.json').read_text(encoding='utf-8'))
selected=[];records=[]
for entry in coverage['historical_deleted_tests']:
 path=entry['path'];source=(H/path).read_text(encoding='utf-8')
 for node in ast.parse(source).body:
  if isinstance(node,ast.FunctionDef) and node.name.startswith('test_'):
   why=reason(path,node.name);key=path+'::'+node.name
   records.append(dict(path=path,test=node.name,line=node.lineno,selection='excluded' if why else 'selected',reason=why))
   if not why:selected.append(str(H/path)+'::'+node.name)
(ROOT/'reports/historical-review-selection.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8')
suffix='tests'
if '--failed-only' in sys.argv:
 previous=ET.parse(ROOT/'reports/oracle-batch7-tests.xml')
 failed={t.attrib['name'].split('[')[0] for t in previous.findall('.//testcase') if t.find('failure') is not None}
 selected=[p for p in selected if p.split('::')[-1] in failed]
 suffix='retry-tests'
import pytest
raise SystemExit(pytest.main(['-q','-p','no:cacheprovider','--confcutdir='+str(H),'--basetemp='+str(ROOT/('tmp/pytest-history7-'+suffix)),'--junitxml='+str(ROOT/('reports/oracle-batch7-'+suffix+'.xml')),*selected]))
