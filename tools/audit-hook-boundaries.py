"""Synthetic hook shape and repeated-diagnostic controls."""
import contextlib,hashlib,io,json,tempfile
from pathlib import Path
from unittest.mock import patch
from grandportage import hook as H,store as S
r=Path(__file__).resolve().parents[1];root=Path(tempfile.mkdtemp(prefix='hook-boundary-',dir=r/'tmp'))
S.append([{'ev':'model','id':'M','what':'synthetic'}],str(root))
baseline=Path(H.baseline_path(str(root)));baseline.write_text('[]',encoding='utf-8')
try:H.evaluate(str(root));baseline_error=None
except Exception as e:baseline_error=type(e).__name__
assert baseline_error=='AttributeError'
with patch('sys.stdin',io.StringIO('[]')):
 try:H.main(['--root',str(root)]);payload_error=None
 except Exception as e:payload_error=type(e).__name__
assert payload_error=='AttributeError'
baseline.write_text('{}',encoding='utf-8')
outputs=[]
for bad in ['{first malformed','[']:
 Path(S.graph_path(str(root))).write_text(bad+'\n',encoding='utf-8')
 block,detail=H.evaluate(str(root));assert block
 err=io.StringIO()
 with patch('sys.stdin',io.StringIO(json.dumps({'cwd':str(root),'tool_name':'Write'}))),contextlib.redirect_stderr(err):
  code=H.main([])
 assert code==2
 outputs.append({'evaluate_message':detail,'hook_message':err.getvalue()})
assert outputs[0]['evaluate_message']!=outputs[1]['evaluate_message']
assert 'still refused, unchanged' in outputs[1]['hook_message']
report={'source_commit':'ac4155787207e2847d248cffed7be871d5dcd577','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'observations':[{'control':'nonobject_baseline','exception':baseline_error},{'control':'nonobject_hook_input','exception':payload_error},{'control':'changed_malformed_graph','outputs':outputs,'blocking_exit_preserved':True}],'scope':'Synthetic local hook calls only. No installed host hook behavior or proof admission tested.'}
(r/'reports/HOOK-BOUNDARY-AUDIT.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print('Verified three hook controls; malformed graph remains blocking.')
