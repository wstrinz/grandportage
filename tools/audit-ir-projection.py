import hashlib,importlib.util,json,tempfile
from pathlib import Path
from grandportage import project_v2 as I
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('explain_tests',ROOT/'oracle/checkout/tests/test_explain.py');T=importlib.util.module_from_spec(spec);spec.loader.exec_module(T)
root=Path(tempfile.mkdtemp(prefix='projection-binding-',dir=ROOT/'tmp'))
g=T.receipt_graph(root);before=I.project(g);rid=next(iter(g.verdicts));g.authority_receipts.clear();after=I.project(g)
assert before['state_fingerprint']==after['state_fingerprint']
b=before['categories']['bindings'][rid];a=after['categories']['bindings'][rid]
assert b['candidate']['current_under_loaded_state'] and not a['candidate']['current_under_loaded_state']
rows=[{'name':'loaded authority map omitted from state fingerprint','same_state_fingerprint':True,'before_current':True,'after_current':False,'scope':'Direct loaded-state map mutation, not a persisted event or hash collision'}]
try:I.expression('1/2',['x'],0)
except ValueError as e:
 assert str(e)=='rational_expression_adapter';rows.append({'name':'rational characteristic zero','result':'GAP','reason':str(e)})
else:raise AssertionError('expected rational gap')
encoded=I.expression('1/2',['x'],3)
assert encoded==I.expression('2',['x'],3)
rows.append({'name':'rational syntax in characteristic three','equals_integer_two':True,'scope':'Existing parser reduces coefficients modulo three; target context must retain characteristic'})
assert I.expression('x^3',['x'],3)!=I.expression('x',['x'],3)
rows.append({'name':'polynomial versus point-function equality','distinct_encodings':True,'scope':'No reduction by finite-field point identities'})
report={'oracle_commit':'ac4155787207e2847d248cffed7be871d5dcd577','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Four offline projection controls; actual SOS recording for state control, no live CAS or Lean.','controls':rows}
(ROOT/'reports/IR-PROJECTION-BOUNDARIES.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print('4 IR projection controls verified')
