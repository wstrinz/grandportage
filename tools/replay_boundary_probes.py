"""Separate replay authority, historical readability and raw evidence availability."""
from dataclasses import replace
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch
from grandportage import store as S,verify as V,cas,artifacts as A,backend as B,provenance as P
from tests.test_artifacts import _artifact,_manifest
ROOT=Path(__file__).resolve().parents[1]
def probe(case,route):
 d=case['inputs']
 if d['local_backend'] not in ('matching','unavailable','different') or d['question'] not in ('exact_identity_current','raw_artifact_audit','historical_authority'):raise ValueError('Unsupported replay question')
 if d['model']!=dict(field='Q',variables=['x'],equations=['x']):raise ValueError('Unsupported model')
 if d['identity']!=dict(left='x^2',right='0'):raise ValueError('Unsupported identity')
 artifact=_artifact()
 if d['historical_identity']=='unavailable':artifact=replace(artifact,backend=replace(artifact.backend,binary_version='unavailable: TimeoutExpired'))
 elif d['historical_identity']!='identified':raise ValueError('Unsupported historical identity')
 version={'matching':artifact.backend.binary_version,'unavailable':'unavailable: exit 1','different':'Singular for test-fixture version 99.0'}[d['local_backend']]
 with TemporaryDirectory(prefix='replay-boundary-',dir=ROOT/'tmp') as root,patch.object(cas,'_singular_binary_version',return_value=version):
  S.append([dict(ev='model',id='M',desc='origin',characteristic=0,ring_vars=['x'],generators=['x']),dict(ev='claim',id='C',model='M',kind='IDENTITY',statement='x squared vanishes',lhs=d['identity']['left'],rhs=d['identity']['right'],ring_vars=['x'],identity_origin='DERIVED')],root)
  g=S.load(S.graph_path(root));ref=A.persist(root,artifact)
  representation=None if d['cofactors'] is None else dict(cofactors=d['cofactors'],generators=['x'],ring_vars=['x'],target='(x^2) - (0)')
  verdict=V._verdict_event(g,'claim','C','VERIFIED_DERIVED','offline boundary control',representation,execution=_manifest(artifact))
  try:S.append([verdict],root)
  except S.GraphError as exc:return dict(observed_verdict='REFUSE',reason=str(exc),refused_at='fold',execution_descriptor='fabricated_historical_metadata',external_execution=False)
  if d['raw_artifact']=='absent':Path(A.artifact_path(root,ref)).unlink()
  elif d['raw_artifact']!='present':raise ValueError('Unsupported availability')
  g=S.load(S.graph_path(root));audit=A.audit_graph_report(root,g);active=g.claims['C'].get('identity_verdict');current=g.verdicts[verdict['id']]['current']
  readable=P.decode_backend_provenance(verdict['backend'],current_only=False) is not None
  identified=P.backend_provenance(verdict['backend'],current_only=False) is not None
  if d['question']=='raw_artifact_audit':accepted=not audit['problems']
  elif d['question']=='historical_authority':accepted=identified and current and active=='VERIFIED_DERIVED'
  else:accepted=current and active=='VERIFIED_DERIVED'
  return dict(observed_verdict='ACCEPT' if accepted else 'REFUSE',reason='Observe the specified boundary only; raw storage, exact proof replay, and historical metadata eligibility are distinct.',active_identity_verdict=active,receipt_current=current,artifact_audit=audit,historical_readable=readable,historical_identified=identified,execution_descriptor='fabricated_historical_metadata_with_explicit_exact_proof_when_present',external_execution=False)
