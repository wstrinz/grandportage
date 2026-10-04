"""Separate artifact projection checks from whole-manifest admission."""
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import copy,hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');replay=importlib.util.module_from_spec(spec);spec.loader.exec_module(replay);replay.validate()
from grandportage import artifacts as A,provenance as P
from tests.test_artifacts import _artifact,_manifest
records=[]
with TemporaryDirectory(prefix='manifest-audit-',dir=ROOT/'tmp') as root:
 artifact=_artifact();A.persist(root,artifact);base=_manifest(artifact)
 for mode in ['matching','wrong_trace_digest','unknown_field']:
  manifest=copy.deepcopy(base)
  if mode=='wrong_trace_digest':manifest['trace_fingerprint']='sha256:'+'0'*64
  if mode=='unknown_field':manifest['extra']='not admitted'
  encoded=P.BACKEND_PROVENANCE_PREFIX+json.dumps(manifest)
  low=A.audit_manifest(root,manifest);decoded=P.decode_backend_provenance(encoded,current_only=False)
  graph=SimpleNamespace(verdicts={'receipt':{'backend':encoded}},notes=[])
  full=A.audit_graph_report(root,graph)
  assert low==[]
  assert (decoded is not None)==(mode=='matching')
  assert bool(full['problems'])==(mode!='matching')
  records.append(dict(mode=mode,artifact_projection_problems=low,manifest_decoded=decoded is not None,graph_audit=full))
report=dict(oracle_commit=replay.PIN,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Diagnostic composition boundary using fabricated records; no mathematical graph authority.',records=records,finding='An empty low-level artifact projection audit is not full manifest admission. The graph audit independently rejects malformed whole manifests.')
(ROOT/'reports/ARTIFACT-MANIFEST-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Three manifest-composition controls pass: low-level storage integrity is separate from closed-schema and trace-digest admission.')
