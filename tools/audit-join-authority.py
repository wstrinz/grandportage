"""Diagnostic of legacy joins versus entailment and transitive proof closure."""
import copy,hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'oracle/checkout'),str(ROOT/'oracle/checkout/tests')]
from grandportage import store as S,check as C

def fold(events):return S.Graph().apply_all([(copy.deepcopy(e),'join-audit',i) for i,e in enumerate(events)]).validate()
def main():
    prefix=[dict(ev='model',id='M',desc='one context'),dict(ev='claim',id='P',model='M',kind='PREDICATE',statement='0=0'),dict(ev='claim',id='Q',model='M',kind='PREDICATE',statement='1=1')]
    join=dict(ev='inference',id='JOIN',premises=[dict(claim='P',path=[]),dict(claim='Q',path=[])],concludes_kind='PREDICATE',asserted='0=0 and 1=1')
    rows=[]
    for conclusion in ['0=0 and 1=1','0=1']:
        g=fold(prefix+[dict(join,asserted=conclusion)]);ok,trace=C.audit_inference(g,'JOIN')
        assert ok
        rows.append(dict(conclusion_text=conclusion,transport_audit=ok,trace=trace,clean_inferences=C.clean_inferences(g,C.run(g))))
    missing=copy.deepcopy(join);missing['premises'][1]=dict(required_kind='PREDICATE',at='M',missing_why='second premise unavailable')
    g=fold(prefix+[missing]);ok,trace=C.audit_inference(g,'JOIN');assert not ok
    rows.append(dict(scenario='explicit_missing_premise',transport_audit=ok,trace=trace))
    derived=dict(ev='inference',id='NEXT',claim='JOIN',path=[],concludes_kind='PREDICATE',asserted='reuse prior inference')
    try:fold(prefix+[join,derived])
    except S.GraphError as exc:transitive=dict(supported=False,reason=str(exc))
    else:raise AssertionError('Legacy inference unexpectedly became a claim premise')
    report=dict(oracle_commit=json.loads((ROOT/'oracle/PIN.json').read_text(encoding='utf-8-sig'))['commit'],script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),authority='DIAGNOSTIC_ONLY',external_execution=False,observations=rows,transitive_inference_reference=transitive,
        interpretation='Legacy join acceptance checks route compatibility, not logical entailment. Accepting both conclusion strings is documented scope, not a demonstrated false checked theorem. An inference is not itself a claim premise in this vocabulary.',
        source='grandportage/store.py::_apply_inference',remaining='Extract neutral premise/transport cases separately; total closure, alternative warrant support and admitted derivation semantics cannot be inferred from this oracle.')
    (ROOT/'reports/JOIN-AUTHORITY-AUDIT.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print('Two conclusion-text controls, one missing-premise control and transitive-reference boundary reproduced.')
if __name__=='__main__':main()
