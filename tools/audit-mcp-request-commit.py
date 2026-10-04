"""Bound MCP transport errors and post-commit reporting failures."""
from pathlib import Path
import hashlib,importlib.util,io,json,tempfile
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import mcp as M,store as S
rows=[]
ping=json.dumps(dict(jsonrpc='2.0',id=2,method='ping'))+'\n'
for name,prefix in [('invalid_json','{\n'),('json_array','[]\n')]:
 out=io.StringIO();error=None
 try:M.serve(io.StringIO(prefix+ping),out,root=str(ROOT/'tmp'))
 except AttributeError as exc:error=str(exc)
 responses=[json.loads(x) for x in out.getvalue().splitlines()]
 assert (error is not None)==(name=='json_array')
 if name=='invalid_json':assert responses[0]['error']['code']==-32700 and responses[1]['id']==2
 else:assert responses==[]
 rows.append(dict(id=name,exception=error,responses=responses))
with tempfile.TemporaryDirectory(dir=ROOT/'tmp',prefix='mcp-boundary-') as tmp:
 for name,event in [('valid',dict(ev='model',id='M',what='valid')),('invalid',dict(ev='model',id='BAD',unknown=True)),('post_commit_failure',dict(ev='model',id='LATE',what='commits before reporting'))]:
  path=Path(S.graph_path(tmp));before=path.read_bytes() if path.exists() else None
  request=dict(jsonrpc='2.0',id=1,method='tools/call',params=dict(name='portage_declare',arguments=dict(events=[event])))
  if name=='post_commit_failure':
   with patch.object(M.C,'run',side_effect=RuntimeError('synthetic report failure')):response=M.dispatch(request,root=tmp)
  else:response=M.dispatch(request,root=tmp)
  after=path.read_bytes() if path.exists() else None;changed=before!=after
  assert changed==(name!='invalid')
  assert bool(response['result'].get('isError'))==(name!='valid')
  if name=='post_commit_failure':assert 'LATE' in S.load(str(path)).models
  rows.append(dict(id=name,response=response,graph_changed=changed,model_present=event['id'] in S.load(str(path)).models))
report={'controls':rows,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':r.sha(ROOT/'oracle/checkout/grandportage/mcp.py'),'findings':['Invalid JSON syntax yields an error then the next ping is served; valid JSON array reaches dispatch.get and raises AttributeError before subsequent lines are handled.','Malformed event refuses without graph changes; a simulated reporting failure after successful append returns isError despite durable model addition. Tool error alone does not imply no mutation.'],'proposed_fix':'Validate request/params/arguments shapes before dispatch and contain per-message errors so later input can continue. Return explicit commit status and graph receipt when post-append reporting fails; preserve pre-commit refusal semantics.','scope':'Two in-memory stream controls and three temporary graph declarations. Reporting failure is injected, not an observed production incident. No campaign graph, CAS or oracle modification.'}
(ROOT/'reports/MCP-REQUEST-COMMIT-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print('Five MCP request/commit controls verified.')
