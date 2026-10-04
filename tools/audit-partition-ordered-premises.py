"""Isolate ordered premise interpretation at the partition audit consumer."""
from pathlib import Path
import hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import format as F,store as S,verify as V,provenance as P,check as C
native=S.Graph();native.apply(F.meta_event())
try:native.apply(dict(ev='inference',id='NATIVE',via_partition='P',premises=[{'claim':'E'}],concludes_kind='EMPTY',asserted='native boundary control'))
except S.GraphError as exc:
 native_refusal=str(exc);assert 'unknown field' in native_refusal and 'via_partition' in native_refusal
else:raise AssertionError('native partition field unexpectedly admitted')
rows=[]
for field,recorded,cover in [('R',True,True),('C',True,True),('R',False,True),('C',True,False)]:
 g=S.Graph() # Legacy graph API, matching retained partition tests.
 for mid in ['M','B1','B2']:
  g.apply(dict(ev='model',id=mid,about=field,compute_in='Q',coefficient_domain='Q',characteristic=0,point_universe='BASE',ring_vars=['x'],generators=['x^2+1']))
 g.apply(dict(ev='claim',id='COVER',model='M',kind='PREDICATE',statement='two identical copies cover the parent'))
 g.apply(dict(ev='partition',id='P',parent='M',branches=['B1','B2'],exhaustive='COVER',why='identical-locus cover isolates premise interpretation'))
 for bid in ['B1','B2']:
  cid='E'+bid;g.apply(dict(ev='claim',id=cid,model=bid,kind='EMPTY',statement='no ordered-field zero',certificate='ORDERED_SOS_CERT',scope='ANY_ORDERED'))
  if recorded:
   cert=dict(method='rational_sos_cofactor_v1',ring_vars=['x'],generators=['x^2+1'],squares=['x'],cofactors=['-1'])
   verdict,why,rep=V.ordered_sos(g,cid,cert);assert verdict==V.CERT_VERIFIED
   g.apply(V._verdict_event(g,'certificate',cid,verdict,why,rep,execution=P.native_execution_provenance()))
 g.apply(dict(ev='inference',id='JOIN',via_partition='P',premises=[{'claim':x} for x in ['EB1','EB2','COVER']],concludes_kind='EMPTY',asserted='the parent has no points'));g.validate()
 # Isolated consumer premise, as in source test _split: no cover receipt minted.
 if cover:g.partitions['P']['exhaustive_verdict']='VERIFIED'
 allowed,trace=C.audit_inference(g,'JOIN');assert allowed==cover
 rows.append(dict(field=field,branch_receipts_recorded=recorded,cover_projection_supplied=cover,branch_reaches=[g.claims[x].get('certificate_reach') for x in ['EB1','EB2']],audit_allowed=allowed,trace=trace,findings=[dict(id=x.fid,detail=x.detail) for x in C.run(g)]))
report={'native_schema_refusal':native_refusal,'controls':rows,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':{p:r.sha(ROOT/'oracle/checkout'/p) for p in ['grandportage/check.py','grandportage/kernel.py','grandportage/store.py']},'finding':'Given a correct cover projection, partition audit counts ORDERED_SOS branch premises without checking current reach or applicability to C. Valid ordered identities cannot prove complex emptiness of x^2+1: i is a root. Missing branch receipts also do not prevent this consumer from counting the certificate kind.','proposed_fix':'Require every branch premise to have replay-earned authority applicable to the exact branch/parent context before composition. Keep cover correctness as a separate required premise.','limitation':'Legacy graph API consumer isolation: current epoch-1 schema rejects via_partition before this path. Cover projection explicitly assigned, not persisted or produced by a backend. Identical loci make the supplied cover mathematically true. Branch SOS receipts, when present, use actual native replay. No end-to-end admission or clean-global-check claim; all findings retained.'}
(ROOT/'reports/PARTITION-ORDERED-PREMISE-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Four partition consumer controls verified.')
