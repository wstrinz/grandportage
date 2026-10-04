"""Bounded offline transcript and artifact boundary diagnostics; no CAS."""
import hashlib,json,sys
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
from grandportage import backend as B, cas
r=Path(__file__).resolve().parents[1]
observations=[]
for label,code,expected in [('plain',"import os; os.write(1,b'OK\\n')",'OK\n'),('invalid_utf8',"import os; os.write(1,b'O\\xffK\\n')",'OK\n')]:
 with patch.object(cas,'_argv',return_value=[sys.executable,'-B','-c',code]):
  result=cas._run_subprocess(SimpleNamespace(text=''),3)
 assert result['returncode']==0 and result['stdout']==expected
 observations.append({'control':label,'stdout':result['stdout'],'retained_text_fingerprint':B.text_fingerprint(result['stdout']),'returncode':result['returncode']})
assert observations[0]['retained_text_fingerprint']==observations[1]['retained_text_fingerprint']
valid='sha256:'+'0'*64
observations.append({'control':'fingerprint_final_newline','ordinary':B.valid_fingerprint(valid),'newline':B.valid_fingerprint(valid+'\n')})
assert observations[-1]['ordinary'] and observations[-1]['newline']
program=cas.CASProgram(cas.SINGULAR,ring='GP_R',ring_vars=['x'],decls=[('GP_I','ideal','x')],body=[],outputs=['GP_I'])
reason={'detail':'before'}
backend=cas.SingularBackend(runner=lambda p,t:{'stdout':'','stderr':'','returncode':124,'aborted':True,'abort_reason':reason,'argv':['test']},binary_version='test')
result=backend.execute(program)
before=B.execution_artifact_fingerprint(result.artifact)
reason['detail']='after'
after=B.execution_artifact_fingerprint(result.artifact)
assert before!=after
B.validate_execution_artifact(result,program)
observations.append({'control':'mutable_abort_reason_direct_test_adapter','artifact_fingerprint_changed':before!=after,'validator_accepts':True,'scope':'Injected runner only. Native subprocess abort_reason is a string or null; no persisted bypass claimed.'})
report={'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_commit':'ac4155787207e2847d248cffed7be871d5dcd577','observations':observations,'interpretation':'Decoded transcript hashing is not raw-byte custody. Final-newline fingerprint acceptance is lexical validation drift, not a demonstrated accepted stored object. Frozen dataclass is shallow for untyped abort_reason; native producer does not emit mutable reasons.'}
(r/'reports/BACKEND-TRANSCRIPT-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(observations,indent=2))
