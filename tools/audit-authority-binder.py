"""Measure the internal binder contract without asserting a persisted bypass."""
from pathlib import Path
from unittest.mock import patch
import hashlib, importlib.util, json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');replay=importlib.util.module_from_spec(spec);spec.loader.exec_module(replay);replay.validate()
from grandportage import authority as A, provenance as P, store as S
from tests.test_authority_binding import _event, _graph_with_target
records=[]
# Precisely the frozen characterization setup: no real provenance is claimed.
with patch.object(P,'current_verdict',return_value=(True,'diagnostic assumption only')):
 evidence=A.check(_graph_with_target('claims'),_event('claim','VERIFIED_AMBIENT'))
 receipt=A.bind(evidence,'identity_verdict','identity_why')
 intended={}; unrelated={'id':'OTHER'}
 A.project(receipt,intended);A.project(receipt,unrelated)
 assert intended['identity_verdict']==unrelated['identity_verdict']=='VERIFIED_AMBIENT'
 records.append(dict(control='target_identity_is_callers_obligation',evidence_object=evidence.context.object_id,projected_target=unrelated,scope='Direct internal API under explicitly patched freshness. No persisted event or graph validation bypass established.'))
 try:A.bind(evidence,'identity_verdict','identity_verdict')
 except ValueError:records.append(dict(control='duplicate_projection_refused',passed=True))
 else:raise AssertionError('duplicate accepted')
 payload={'cofactors':['1']};r=A.bind(evidence,'identity_verdict','identity_why',[('representation',payload)])
 payload['cofactors'][0]='0';target={};A.project(r,target)
 assert target['representation']['cofactors']==['0']
 records.append(dict(control='receipt_is_shallow_frozen',projected_payload=target['representation'],scope='Synthetic extra projection passed directly by trusted caller; not a malformed proof admitted by store.'))
with patch.object(P,'current_verdict',return_value=(False,'stale control')):
 refused=A.check(_graph_with_target('claims'),_event('claim','VERIFIED_AMBIENT'))
 assert isinstance(refused,A.AuthorityRefusal)
 try:A.bind(refused,'identity_verdict','identity_why')
 except TypeError:records.append(dict(control='refused_evidence_cannot_bind',passed=True))
 else:raise AssertionError('refusal bound')
report=dict(oracle_commit=replay.PIN,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sources={n:replay.sha(ROOT/'oracle/checkout'/n) for n in ['grandportage/authority.py','grandportage/authority_registry.py','tests/test_authority_binding.py','tests/test_authority_registry.py','grandportage/store.py']},controls=records,conclusion='Internal API preconditions measured, not an end-to-end authority flaw. Store chooses target[of] and runs subject replay before bind; full subject coverage remains partial. Proposed successor design: explicit target/context validation at projection and immutable proof payloads, evaluated against corpus before adoption.')
(ROOT/'reports/AUTHORITY-BINDER-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Four binder boundary controls passed; no persisted bypass claimed.')
