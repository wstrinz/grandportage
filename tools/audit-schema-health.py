"""Audit authoring schema approximation and health result classification."""
from pathlib import Path
import argparse,contextlib,hashlib,importlib.util,io,json,tempfile
from unittest.mock import patch
import jsonschema
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import cli,mcp as M,cas,format as F,store as S
rows=[]
event=dict(ev='claim',id='C',model='M',kind='PREDICATE',statement='p',integral='false')
jsonschema.validate(event,M._event_schema('claim'))
try:F.validate_native_event(event,'control',S.GraphError)
except S.GraphError as exc:rows.append(dict(id='schema_truthy_flag',json_schema_accepts=True,native_refusal=str(exc)))
else:raise AssertionError('native accepted string boolean')
tomb=dict(ev='inference',id='R',supersedes='I',discharge_kind='RETRACT',why='withdraw')
F.validate_native_event(tomb,'control',S.GraphError)
try:jsonschema.validate(tomb,M._event_schema('inference'))
except jsonschema.ValidationError as exc:rows.append(dict(id='schema_tombstone',native_shape_accepts=True,json_schema_refusal=exc.message))
else:raise AssertionError('schema unexpectedly permits sparse tombstone')
with tempfile.TemporaryDirectory(dir=ROOT/'tmp',prefix='doctor-audit-') as tmp:
 for name,basis in [('correct',['y-2','x-1']),('unexpected',['1'])]:
  raw=dict(aborted=False,stdout='',stderr='',argv=['synthetic-cas'])
  with patch.object(cas,'_execute',return_value=raw),patch.object(cas,'_parse_result',return_value={'GPH_G':basis}),patch.object(cas,'_singular_binary_version',return_value='synthetic-version'):
   health=M.h_cas_health({},tmp)
   out=io.StringIO()
   with contextlib.redirect_stdout(out):code=cli.cmd_doctor(argparse.Namespace(root=tmp,graph=None,json=True))
   report=json.loads(out.getvalue());assert code==0 and report['cas']['healthy'] is True
   assert ('UNEXPECTED' in health['content'][0]['text'])==(name=='unexpected')
   rows.append(dict(id='health_'+name,health_response=health,doctor_exit=code,doctor_healthy=report['cas']['healthy'],graph_exists=report['graph']['exists']))
report={'controls':rows,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':{p:r.sha(ROOT/'oracle/checkout'/p) for p in ['grandportage/cli.py','grandportage/mcp.py','grandportage/format.py']},'findings':['Published event schema is an authoring approximation: string licensing flag passes schema but native shape refuses; sparse lifecycle tombstone passes native shape but schema requires asserted.','Unexpected parsed health basis returns normal text without isError. Doctor derives healthy solely from isError and exits zero even though text warns not to trust verdicts.'],'proposed_fix':'Encode licensing booleans and sparse tombstone alternatives consistently in exported schema, or state its narrower advisory contract. Return structured failed health on unexpected arithmetic output and propagate it to doctor status. Health never substitutes for certificate replay.','scope':'Mocked CAS execution and parser outputs isolate classification; no real backend behavior or false proof authority claimed. Missing graph is reported explicitly and is not treated as a doctor error by current policy.'}
(ROOT/'reports/SCHEMA-HEALTH-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Four schema/health boundary controls verified.')
