"""Reproduce the unresolved retry/merge semantics without proposing kernel rules."""
import copy,hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'oracle/checkout'),str(ROOT/'oracle/checkout/tests')]
from grandportage import store as S,format as F,verify as V
from test_verdict_provenance import _identity_graph,_verdict,_elimination_graph,_section_representation,_execution

def view(g):
    return dict(projected=g.claims['C'].get('identity_verdict'),
                retained_receipts={k:r.evidence.verdict for k,r in g.authority_receipts.items()},
                freshness={k:v['current'] for k,v in g.verdicts.items()})

def main():
    prefix=[F.meta_event(),dict(ev='model',id='M',what='a line',characteristic=0,ring_vars=['x'],generators=['x']),dict(ev='claim',id='C',model='M',kind='IDENTITY',statement='x vanishes',lhs='x',rhs='0',ring_vars=['x'],identity_origin='DERIVED',established_by='RAN',ladder='exact-checked')]
    g=_identity_graph();positive=_verdict(g);positive['id']='v.positive'
    failed=_verdict(g,'UNVERIFIED');failed['id']='v.unfinished';failed['why']='Producer did not finish; no mathematical refutation.'
    branches={'positive':prefix+[positive],'unfinished':prefix+[failed]}
    observations=[]
    for order in [('positive','unfinished'),('unfinished','positive')]:
        g,conflicts=S.merge_report_events([(name,copy.deepcopy(branches[name])) for name in order])
        assert not conflicts
        observations.append(dict(branch_order=list(order),**view(g)))
    assert [o['projected'] for o in observations]==['UNVERIFIED','VERIFIED_DERIVED']
    assert all(o['freshness']=={'v.positive':True,'v.unfinished':True} for o in observations)
    section=[]
    for order in [('positive','rejected'),('rejected','positive')]:
        g=_elimination_graph()
        events={'positive':V._verdict_event(g,'elimination','E',V.SECTION_VERIFIED,'section checked',_section_representation(),execution=_execution()),'rejected':V._verdict_event(g,'elimination','E',V.SECTION_REJECTED,'different proposal failed',execution=_execution(with_trace=False))}
        for name in order:g.apply(copy.deepcopy(events[name]))
        assert g.edges['E']['contraction_verdict']==V.SECTION_VERIFIED
        section.append(dict(order=list(order),projected=g.edges['E']['contraction_verdict'],retained_receipts=len(g.authority_receipts),history_count=len(g.verdicts)))
    report=dict(oracle_commit=json.loads((ROOT/'oracle/PIN.json').read_text(encoding='utf-8-sig'))['commit'],script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),authority='DIAGNOSTIC_ONLY',external_execution=False,identity_merge=observations,section_orders=section,verdict_is_supersedable='verdict' in S.Graph._SUPERSEDABLE,
        finding='The two valid identity-receipt branches merge without conflict but their active projected field depends on concatenation order. Both receipts remain fresh and retained. Rejected elimination proposals have a subject-specific non-overwrite rule.',
        limitation='Backend execution manifests are fabricated test fixtures. Section arithmetic is replayed by the pinned fold. This assay does not establish GP 0.50 independent-warrant semantics or generic selective warrant retraction.',
        unresolved=['Does a failed attempt leave an earlier independently valid warrant active?','How are individual warrants retracted separately from the claim they support?','How should merge handle multiple current positive and negative receipts without arrival-order priority?'])
    (ROOT/'reports/RETRY-MERGE-AUDIT.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print('Reproduced both identity merge orders and both section orders; unresolved policy retained.')
if __name__=='__main__':main()
