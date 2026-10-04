"""Compare native mapped-ring producer verification with fold admission."""
from pathlib import Path
import hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import store as S,format as F,verify as V,provenance as P
records=[]
for mode in ['valid','false_cofactor','false_inverse']:
 g=S.Graph();g.apply(F.meta_event())
 gens=[] if mode=='false_inverse' else ['x']
 for mid in ['A','B']:g.apply(dict(ev='model',id=mid,what=mid,characteristic=0,ring_vars=['x'],generators=gens))
 g.apply(dict(ev='edge',id='E',src='A',dst='B',type='EQUIVALENCE',map_kind='POLYNOMIAL',why='offline test map',ring_iso=True,forward={'x':'0' if mode=='false_inverse' else 'x'},inverse={'x':'x'},ring_iso_certificate=dict(schema='mapped_ring_iso_v1',forward_cofactors=[] if not gens else [['0' if mode=='false_cofactor' else '1']],inverse_cofactors=[] if not gens else [['1']])))
 g.validate();verdict,why=V.ring_iso(g,'E')
 assert (verdict==V.ISO_VERIFIED)==(mode=='valid')
 # Deliberately simulate an incorrect native producer assertion, not the real verifier's output.
 e=V._verdict_event(g,'ring_iso','E',V.ISO_VERIFIED,'simulated native producer assertion',execution=P.native_execution_provenance())
 current,reason=P.current_verdict(g,e);g.apply(e);g.validate()
 assert current and g.edges['E']['ring_iso_verdict']==V.ISO_VERIFIED
 records.append(dict(control=mode,actual_verifier=verdict,verifier_reason=why,asserted_verdict=V.ISO_VERIFIED,fold_current=current,fold_reason=reason,active=g.edges['E']['ring_iso_verdict']))
report=dict(oracle_commit=r.PIN,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sources={n:r.sha(ROOT/'oracle/checkout'/n) for n in ['grandportage/verify.py','grandportage/store.py','grandportage/provenance.py']},controls=records,scope='Actual verifier and native graph fold, no CAS and no patched freshness. Invalid positive verdicts intentionally fabricated after the actual verifier refused; not a claim that verify_all emits them.',finding='The native producer performs exact certificate and composition checks; fold-time eligibility tests schema/maps but does not repeat them. A matching synthetic positive event activates invalid mapped evidence.',proposal='Replay mapped certificate and inverse laws at admission, binding exact endpoint conventions; retain invalid-proof refusal distinct from map refutation.')
(ROOT/'reports/MAPPED-RING-REPLAY-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print('Three verifier-versus-fold controls passed; real verifier rejects both invalid controls.')
