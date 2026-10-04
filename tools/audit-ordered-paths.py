"""Separate empty-route audit, typed reach and legacy transport behavior."""
from pathlib import Path
import hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import format as F,store as S,verify as V,provenance as P,check as C
rows=[]
for typed in [False,True]:
 for target in (['R','C'] if typed else ['unspecified_about']):
  for recorded in [False,True]:
   graph=S.Graph();graph.apply(F.meta_event())
   for mid,field in [('M','R'),('N',target)]:
    model=dict(ev='model',id=mid,coefficient_domain='Q',characteristic=0,point_universe='BASE',ring_vars=['x'],generators=['x^2+1'])
    if typed:model.update(about=field,compute_in='Q')
    graph.apply(model)
   graph.apply(dict(ev='claim',id='E',model='M',kind='EMPTY',statement='no ordered-field zero',certificate='ORDERED_SOS_CERT',scope='R'))
   graph.apply(dict(ev='edge',id='EDGE',src='M',dst='N',type='BASE_EXTENSION',map_kind='IDENTITY_MAP',why='test field interpretation'))
   for iid,path in [('ZERO',[]),('STEP',[['EDGE','ALONG']])]:
    graph.apply(dict(ev='inference',id=iid,claim='E',path=path,asserted='carry the emptiness premise'))
   if recorded:
    cert=dict(method='rational_sos_cofactor_v1',ring_vars=['x'],generators=['x^2+1'],squares=['x'],cofactors=['-1'])
    verdict,why,rep=V.ordered_sos(graph,'E',cert);assert verdict==V.CERT_VERIFIED
    graph.apply(V._verdict_event(graph,'certificate','E',verdict,why,rep,execution=P.native_execution_provenance()))
   graph.validate()
   zero=C.audit_inference(graph,'ZERO');step=C.audit_inference(graph,'STEP')
   assert zero==(True,[])
   if typed:assert step[0]==(recorded and target=='R')
   rows.append(dict(typed=typed,target=target,recorded=recorded,reach=graph.claims['E'].get('certificate_reach'),zero_path={'licensed':zero[0],'trace':zero[1]},one_step={'licensed':step[0],'trace':step[1]},findings=[{'id':x.fid,'detail':x.detail} for x in C.run(graph)]))
report={'controls':rows,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':{p:r.sha(ROOT/'oracle/checkout'/p) for p in ['grandportage/check.py','grandportage/kernel.py','grandportage/store.py']},'scope':'Six graphs, each audited with zero and one transport step; actual native receipt when recorded. No CAS, campaign data or implementation changes. A route audit is not a held-claim verdict.'}
(ROOT/'reports/ORDERED-PATH-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
for row in rows:print(row['typed'],row['target'],row['recorded'],'zero',row['zero_path']['licensed'],'step',row['one_step']['licensed'])
