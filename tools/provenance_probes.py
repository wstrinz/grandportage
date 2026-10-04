"""Provenance and review-policy adapters for the frozen oracle, not proof authority."""
import json
from pathlib import Path
from tempfile import TemporaryDirectory
from grandportage import store as S, check as C, hook as H
ROOT=Path(__file__).resolve().parents[1]

def fold(events):
    return S.Graph().apply_all([(e,'provenance-corpus',i) for i,e in enumerate(events)]).validate()

def probe(case,route):
    d=case['inputs']
    if d['scenario']=='construction_dependency':
        events=[dict(ev='model',id=x,desc=x) for x in ['source','first','second']]
        events += [dict(ev='edge',id='relax',src='source',dst='first',type='NECESSARY_CONDITION',why='drops equations'),
                   dict(ev='claim',id='point',model='first',kind='NONEMPTY',witness_kind='EXHIBITED',statement='point of the relaxation',scope='Q'),
                   dict(ev='inference',id='bad',claim='point',path=[['relax','AGAINST']],asserted='source has a point'),
                   dict(ev='edge',id='next',src='first',dst='second',type='NECESSARY_CONDITION',why='drops more equations'),
                   dict(ev='inference',id='clean',claim='point',path=[['next','ALONG']],asserted='second has a point'),
                   dict(ev='built_by',model='second',inference='clean')]
        if d['first_context_depends_on_refused_lift']:
            events.append(dict(ev='built_by',model='first',inference='bad'))
        g=fold(events); findings=C.run(g)
        tainted=sorted(f.subject for f in findings if f.rule==C.R_TAINT)
        clean=C.audit_inference(g,'clean')[0];bad=C.audit_inference(g,'bad')[0]
        assert clean and not bad
        return dict(observed_verdict='REFUSE' if 'second' in tainted else 'ACCEPT',reason='Legacy construction-provenance diagnostic only; no checked point or new warrant semantics.',final_step_licensed=clean,initial_lift_licensed=bad,tainted_contexts=tainted,findings=[f.as_dict() for f in findings if f.rule==C.R_TAINT])
    if d['scenario']!='reviewed_warning':raise ValueError('Unknown scenario')
    types={'unspecified':'UNTYPED','equations_forgotten':'NECESSARY_CONDITION'}
    def events(relation):
        return [dict(ev='model',id='tight',desc='tight'),dict(ev='model',id='loose',desc='loose'),
                dict(ev='edge',id='relation',src='tight',dst='loose',type=types[relation],why='some step',map_kind='POLYNOMIAL',debt_why='not yet worked out'),
                dict(ev='claim',id='point',model='loose',kind='NONEMPTY',witness_kind='EXHIBITED',statement='a witness',scope='Q'),
                dict(ev='inference',id='lift',claim='point',path=[['relation','AGAINST']],asserted='tight has a point')]
    with TemporaryDirectory(prefix='baseline-probe-',dir=ROOT/'tmp') as root:
        path=Path(S.graph_path(root));path.parent.mkdir(parents=True,exist_ok=True)
        def write(relation):
            path.write_text(''.join(json.dumps(e,sort_keys=True)+'\n' for e in events(relation)),encoding='utf-8')
            return C.run(S.load(str(path)))
        before=write(d['reviewed_relation'])
        if d['review_record']!='absent':
            H.save_baseline(root,before,note=d['review_reason'])
            assert not H.evaluate(root)[0]
            if d['review_record']=='without_meaning_digest':
                baseline=H.read_baseline(root)
                for entry in baseline['accepted'].values():entry.pop('fingerprint',None)
                Path(H.baseline_path(root)).write_text(json.dumps(baseline),encoding='utf-8')
            elif d['review_record']!='meaning_bound':raise ValueError('Unknown review record')
        after=write(d['current_relation']);blocked,message=H.evaluate(root)
        shared=sorted({f.fid for f in before}&{f.fid for f in after})
        assert shared
        return dict(observed_verdict='REFUSE' if blocked else 'ACCEPT',reason='Operational hook permission only: carrying a warning never validates the refused mathematical inference.',hook_blocked=blocked,stable_finding_ids=shared,stale_warning='STALE' in message,original_reason_visible=d['review_reason'] in message,diagnostic=message)
