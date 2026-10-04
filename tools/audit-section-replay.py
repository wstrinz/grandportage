"""Characterize section proof custody with real freshness and fabricated producer metadata."""
from pathlib import Path
from copy import deepcopy
import hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import verify as V, provenance as P, store as S, format as F
from tests.test_contracts import _SectionBackend
from grandportage import groebner as G
from tests.test_artifacts import _artifact,_manifest
def native_graph():
 g=S.Graph();g.apply(F.meta_event(),source='diagnostic',lineno=1)
 events=[dict(ev='model',id='SOURCE',what='source',characteristic=0,ring_vars=['y','x'],generators=['y*x-1','y^2-x']),dict(ev='model',id='TARGET',what='target',characteristic=0,ring_vars=['x'],generators=['x^3-1'],eliminated=['y']),dict(ev='edge',id='E',src='SOURCE',dst='TARGET',type='IMAGE_CLOSURE',map_kind='POLYNOMIAL',why='eliminate y',built_by_operation='Eliminate')]
 for i,event in enumerate(events):g.apply(event,source='diagnostic',lineno=i+2)
 return g.validate()
base=native_graph(); verdict,why,proof=V.elimination_section(base,'E',{'y':'x^2'},_backend=_SectionBackend())
assert verdict==V.SECTION_VERIFIED
execution=_manifest(_artifact())
valid=V._verdict_event(base,'elimination','E',verdict,why,proof,execution=execution)
records=[]
for mode in ['valid','tampered_old_fingerprint','invalid_reissued_by_producer']:
 g=native_graph();event=deepcopy(valid)
 if mode!='valid':event['representation']['rows'][0]['cofactors']=['0']
 if mode=='invalid_reissued_by_producer':event=V._verdict_event(g,'elimination','E',verdict,why,event['representation'],execution=execution)
 row=event['representation']['rows'][0]
 try:G.check_membership_identity(row['substituted'],proof['target_generators'],row['cofactors'],proof['target_ring_vars'],0);arithmetic=True
 except G.CertificateError:arithmetic=False
 assert arithmetic==(mode=='valid')
 current,reason=P.current_verdict(g,event)
 g.apply(event,source='offline fabricated producer diagnostic',lineno=1)
 active=g.edges['E'].get('contraction_verdict')
 print(mode,current,reason,active)
 if mode=='tampered_old_fingerprint':assert not current and active is None
 else:assert current and active==V.SECTION_VERIFIED
 records.append(dict(control=mode,current=current,reason=reason,active=active,cofactor_identity_valid=arithmetic,first_row=event['representation']['rows'][0]))
report=dict(oracle_commit=r.PIN,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sources={n:r.sha(ROOT/'oracle/checkout'/n) for n in ['grandportage/store.py','grandportage/provenance.py','tests/test_contracts.py','tests/test_artifacts.py']},controls=records,execution='Fabricated test execution descriptor; no Singular run, no binary probe, no persisted graph. Actual current_verdict and Graph.apply used without patching freshness.',conclusion='Existing fingerprint rejects ordinary proof tampering. Reissuing an invalid cofactor row with freshly computed producer metadata remains current because section fold checks binding/shape, not cofactor arithmetic. This demonstrates the retained trusted-producer boundary, not unauthenticated control of a genuine producer. Replay-only 0.50 must independently check section substitution and ideal identities.')
(ROOT/'reports/SECTION-REPLAY-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Valid section current; stale tampering inactive; reissued invalid cofactor current under fabricated producer provenance.')
