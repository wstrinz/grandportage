"""Check whether compact MCP handoff distinguishes point universes."""
from pathlib import Path
import hashlib,importlib.util,json,tempfile
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import mcp as M,store as S
rows=[]
with tempfile.TemporaryDirectory(dir=ROOT/'tmp',prefix='mcp-show-') as tmp:
 for universe in ['BASE','ALGEBRAIC_CLOSURE']:
  root=Path(tmp)/universe;event=dict(ev='model',id='M',desc='zeros of x^2+1',about='Q',compute_in='Q',coefficient_domain='Q',characteristic=0,point_universe=universe,ring_vars=['x'],generators=['x^2+1'])
  S.append([event],str(root));graph=S.load(S.graph_path(str(root)));output=M.h_portage_show({},str(root))['content'][0]['text']
  rows.append(dict(point_universe=universe,point_scope=list(S.point_scope(graph.models['M'])),rendered=output))
assert rows[0]['rendered']==rows[1]['rendered'] and rows[0]['point_scope']!=rows[1]['point_scope']
report={'controls':rows,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':r.sha(ROOT/'oracle/checkout/grandportage/mcp.py'),'finding':'The handoff text is identical for a Q BASE model and its algebraic-closure point interpretation. V(x^2+1) has no rational point but has algebraic-closure points. Stored context stays distinct; only the compact rendering omits it.','proposed_fix':'Include point universe and selected embedding/context in model handoff rows, or explicitly label the view incomplete and provide a structured full context. Do not infer semantic equality from matching rendered text.','scope':'Two synthetic graph roots, no backend or authority mutation beyond ordinary model declarations.'}
(ROOT/'reports/MCP-HANDOFF-CONTEXT-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print('Two distinct point contexts render identically; stored contexts remain distinct.')
