"""Audit neutral lifecycle migration against frozen inputs and semantic mutations."""
import copy,hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'oracle/checkout'),str(ROOT/'oracle/checkout/tests')]
from lifecycle_inputs import decode
from lifecycle_probes import probe

def read(path):return json.loads((ROOT/path).read_text(encoding='utf-8'))
def sha(path):return hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
def main():
    baseline=read('oracle/LIFECYCLE-INPUT-BASELINE.json');routes=read('oracle/ROUTES.json')['routes'];results=[]
    for cid,old in baseline['cases'].items():
        case=read('corpus/must/'+cid+'.json')
        assert case['expected']==old['expected'],cid
        assert decode(case['inputs'])==old['inputs'],cid
        results.append(dict(id=cid,exact_oracle_input_preserved=True,expected_preserved=True,case_sha256=sha('corpus/must/'+cid+'.json'),original_case_sha256=old['original_case_sha256']))
    changed=read('corpus/must/GP-X143.json');changed['inputs']['objects']['object-2']['properties']['description']='model'
    observation=probe(changed,routes['GP-X143']);assert observation['observed_verdict']=='ACCEPT'
    controls=[dict(name='matching description removes redeclaration conflict',observed=observation['observed_verdict'])]
    changed=read('corpus/must/GP-X156.json');changed['inputs']['history'][-1]['replacement']['prior']='missing'
    observation=probe(changed,routes['GP-X156']);assert observation['observed_verdict']=='REFUSE' and 'not a edge' in observation['reason']
    controls.append(dict(name='missing replacement target reaches fold reference guard',observed=observation['observed_verdict'],reason=observation['reason']))
    for name,changed in [('unknown_property',read('corpus/must/GP-X143.json')),('unknown_object_reference',read('corpus/must/GP-X143.json'))]:
        if name=='unknown_property':changed['inputs']['objects']['object-1']['properties']['ignored_licence']=True
        else:changed['inputs']['history'][0]['object']='absent'
        try:decode(changed['inputs'])
        except ValueError as exc:controls.append(dict(name=name,observed='adapter_rejection',reason=str(exc)))
        else:raise AssertionError('Malformed scenario was accepted')
    def graph_records(x):
        if isinstance(x,dict):return ('ev' in x) or any(graph_records(v) for v in x.values())
        if isinstance(x,list):return any(graph_records(v) for v in x)
        return False
    cases=list((ROOT/'corpus/must').glob('*.json'))
    assert not any(graph_records(json.loads(p.read_text(encoding='utf-8'))['inputs']) for p in cases)
    report=dict(authority='ADAPTER_MIGRATION_AUDIT',cases=results,controls=controls,case_count_scanned=len(cases),embedded_gp_event_objects=0,script_sha256=sha('tools/audit-neutral-lifecycle.py'),adapter_sha256=sha('tools/lifecycle_inputs.py'),baseline_sha256=sha('oracle/LIFECYCLE-INPUT-BASELINE.json'),limitation='Exact translation and structural scan do not prove complete semantic neutrality of every corpus family. Mutation controls are temporary and never rewrite case expectations.')
    (ROOT/'reports/NEUTRAL-LIFECYCLE-AUDIT.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(f'{len(results)} exact translations; {len(controls)} mutation controls; {len(cases)} inputs scanned with no embedded GP event objects.')
if __name__=='__main__':main()
