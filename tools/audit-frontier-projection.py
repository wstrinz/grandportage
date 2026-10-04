import copy,hashlib,importlib.util,json
from pathlib import Path
from grandportage import frontier as F
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('frontier_tests',ROOT/'oracle/checkout/tests/test_frontier.py');T=importlib.util.module_from_spec(spec);spec.loader.exec_module(T)
rows=[]
a=T._item('A',status='FAILED',target=None);a.pop('status_when_premises_discharged')
r=F.build([a]);obs=F.item_observations(r)
assert obs[0]['state']=='CLOSED'
rows.append({'name':'unrecognized non-open status defaults closed','observation':obs[0]})
a['frontier_state']='OPEN';r=F.build([a]);assert F.item_observations(r)[0]['state']=='OPEN'
rows.append({'name':'explicit open state preserves failed obligation','observation':F.item_observations(r)[0]})
a=T._item('A',premise='P');base=F.build([a]);updated=F.build([a],[T._discharge()])
assert base['history']['input_fingerprint']==updated['history']['input_fingerprint'] and base['open_items']!=updated['open_items']
rows.append({'name':'historical fingerprint excludes overlays','same_history_fingerprint':True,'before_open':base['open_items'],'after_open':updated['open_items'],'scope':'historical identity by design, not full observation identity'})
a=T._item('A',status='VERIFIED',exports=['scope.consumer']);b=T._item('B',scope='scope.consumer',premise='A')
r=F.build([a,b]);assert r['items'][1]['remaining_open_premises']==['A']
a['status']='DISCHARGED';r2=F.build([a,b]);assert r2['items'][1]['remaining_open_premises']==[]
rows.append({'name':'only literal DISCHARGED propagates','verified_source_remaining':r['items'][1]['remaining_open_premises'],'discharged_source_remaining':r2['items'][1]['remaining_open_premises'],'scope':'explicit status vocabulary, neither status checked by a mathematical verifier'})
report={'oracle_commit':'ac4155787207e2847d248cffed7be871d5dcd577','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Four direct synthetic derived-view controls; no graph input, campaign harvest or proof admission.','controls':rows}
(ROOT/'reports/FRONTIER-PROJECTION-BOUNDARIES.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print('4 frontier projection controls verified')
