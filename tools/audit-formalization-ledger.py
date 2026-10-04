"""Calibrate historical regression-label checks without changing corpus expectations."""
import copy, hashlib, importlib.util, json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('corpus_replay', ROOT/'tools/check-corpus.py')
replay = importlib.util.module_from_spec(spec)
spec.loader.exec_module(replay)
replay.validate()
from grandportage import kernel as K
path = ROOT/'oracle/history/checkout/experiments/jc_formalization_transport/adapter.py'
spec = importlib.util.spec_from_file_location('historical_ledger_audit', path)
adapter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(adapter)
original = json.loads(adapter.DEFAULT_FIXTURE.read_text(encoding='utf-8'))

def raw_ruling(assay, edges):
    edge = edges[assay['edge_id']]
    if assay['claim_kind'] in adapter._CUSTOM_CLAIMS:
        return adapter.INEXPRESSIBLE
    if edge['relation'] in (adapter.OUT_OF_KERNEL,K.UNTYPED):
        return adapter.REFUSED
    if edge['relation'] == adapter.DEFINITIONAL:
        return adapter.LICENSED
    arguments = dict(assay['transport_attributes'])
    if assay['scope'] is not None:
        arguments['scope'] = assay['scope']
    result = K.transport(edge['relation'],assay['direction'],assay['claim_kind'],**arguments)
    return adapter.LICENSED if result.licensed else adapter.REFUSED

records = []
for mode, watched in [('retype_forgetting','JC.ASSAY.A.REVERSE_REALIZATION'),
                      ('relabel_scope','JC.ASSAY.E.FIELD_WIDENING')]:
    value = copy.deepcopy(original)
    if mode == 'retype_forgetting':
        next(e for e in value['edges'] if e['id']=='JC.EDGE.FORGET_ACTUAL_SUMMIT')['relation']='EQUIVALENCE'
    else:
        next(a for a in value['assays'] if a['id']==watched)['scope']='SCHEME'
    edges = {e['id']:e for e in value['edges']}
    actual = {a['id']:raw_ruling(a,edges) for a in value['assays']}
    assert actual[watched] == adapter.LICENSED
    try:
        adapter.compile_ledger(value)
        raise AssertionError('Expected the historical stored-answer check to detect the mutation')
    except adapter.FormalizationLedgerError as exc:
        assert str(exc).startswith('ASY8:')
        mismatch = str(exc)
    # Only an in-memory historical regression fixture is changed here.
    # No neutral corpus case, saved fixture or expected verdict is edited.
    revised = copy.deepcopy(value)
    edits = []
    for assay in revised['assays']:
        if assay['expected_verdict'] != actual[assay['id']]:
            edits.append({'assay':assay['id'],'before':assay['expected_verdict'],'after':actual[assay['id']]})
        assay['expected_verdict'] = actual[assay['id']]
    compiled = adapter.compile_ledger(revised)
    assert compiled['graph_effect'] == 'NONE'
    records.append({'mutation':mode,'watched_assay':watched,'direct_conditional_result':actual[watched],
                    'historical_regression_failure':mismatch,'in_memory_test_label_edits':edits,
                    'after_matching_labels':{'compiled':True,'authority':compiled['authority'],
                                             'graph_effect':compiled['graph_effect']}})
report = {'schema_version':1,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'oracle_commit':replay.PIN,'historical_manifest_sha256':replay.sha(ROOT/'oracle/history/PIN.json'),
          'scope':'Diagnostic calibration, not a false held-claim reproduction and not a change to any corpus expectation.',
          'records':records}
(ROOT/'reports/FORMALIZATION-LABEL-AUDIT.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Two label-audit controls reproduced: the conditional rule licenses the relabeled input, ASY8 detects expected-answer drift, and matching that test label still yields graph_effect NONE.')
