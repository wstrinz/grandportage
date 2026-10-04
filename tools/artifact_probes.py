"""Isolated storage-integrity probes. Fabricated execution records carry no proof authority."""
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch
import json
from grandportage import artifacts as A, backend as B
from tests.test_artifacts import _artifact, _manifest
ROOT=Path(__file__).resolve().parents[1]
def probe(case,route):
 d=case['inputs'];mode=d['storage_action']
 allowed={'roundtrip_deduplicate','corrupt_then_persist','change_output_keep_hash','change_output_rehash','noncanonical_encoding','missing_object','swapped_reference','wrong_protocol','path_reference','atomic_link_failure','ordered_batch'}
 if mode not in allowed or d['evidence_origin']!='fabricated_offline_record':raise ValueError('Unsupported artifact scenario')
 if not isinstance(d['output'],str):raise ValueError('Output must be text')
 artifact=_artifact(d['output']);details={};problems=[]
 with TemporaryDirectory(prefix='artifact-probe-',dir=ROOT/'tmp') as root:
  ref=B.execution_artifact_fingerprint(artifact);path=Path(A.artifact_path(root,ref))
  try:
   if mode=='path_reference':A.artifact_path(root,d['reference'])
   elif mode=='atomic_link_failure':
    with patch.object(A.os,'link',side_effect=OSError('simulated immutable link failure')):A.persist(root,artifact)
   elif mode=='missing_object':problems=A.audit_manifest(root,_manifest(artifact))
   elif mode=='ordered_batch':
    other=_artifact(d['second_output']);refs=A.persist_all(root,[artifact,other]);details['order_preserved']=refs==[ref,B.execution_artifact_fingerprint(other)];assert details['order_preserved']
    for r in refs:A.load(root,r)
   elif mode=='swapped_reference':
    other=_artifact(d['second_output']);otherref=A.persist(root,other);manifest=_manifest(artifact);manifest['executions'][0]['artifact_fingerprint']=otherref;problems=A.audit_manifest(root,manifest)
   else:
    A.persist(root,artifact)
    if mode=='roundtrip_deduplicate':
     second=A.persist(root,artifact);value=A.load(root,ref);details['deduplicated']=second==ref;details['exact_payload_roundtrip']=value==artifact.payload();assert all(details.values());problems=A.audit_manifest(root,_manifest(artifact))
    elif mode=='corrupt_then_persist':
     corrupt=b'{"corrupt":true}';path.write_bytes(corrupt)
     try:A.persist(root,artifact)
     finally:details['corrupt_bytes_preserved']=path.read_bytes()==corrupt
    elif mode=='wrong_protocol':
     manifest=_manifest(artifact);manifest['protocol_version']-=1;problems=A.audit_manifest(root,manifest)
    else:
     value=artifact.payload()
     if mode in ('change_output_keep_hash','change_output_rehash'):
      value['stdout']=d['replacement_output']
      if mode=='change_output_rehash':value['stdout_fingerprint']=B.text_fingerprint(value['stdout'])
     path.write_text(json.dumps(value,sort_keys=True,separators=(',',':')) if mode!='noncanonical_encoding' else json.dumps(value,indent=2),encoding='utf-8')
     A.load(root,ref)
  except A.ArtifactError as exc:problems=[str(exc)]
  if mode=='atomic_link_failure':details['target_absent']=not path.exists();assert details['target_absent']
 return dict(observed_verdict='REFUSE' if problems else 'ACCEPT',reason='; '.join(problems) or 'Storage roundtrip/integrity checks succeeded for fabricated records only.',problems=problems,**details,external_execution=False,graph_effect='NONE')
