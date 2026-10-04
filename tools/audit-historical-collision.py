import json,hashlib,importlib.util,sys
from pathlib import Path
R=Path(__file__).resolve().parents[1];sys.path[:0]=[str(R/'oracle/checkout'),str(R/'tools')]
from historical_probes import load
m=load('ladder');s=json.loads((R/'oracle/history/checkout/fixtures/jc_source_ladder/localized_triangular_solve_chain_v1.json').read_text(encoding='utf-8'));s['ring_vars'].append('GP_INV_t')
for step in s['steps']:step['input_state_fingerprint']='sha256:'+'0'*64
try:m.compile_events(s)
except ValueError as exc:
 assert 'input_state_fingerprint' in str(exc),str(exc)
 result=dict(observed_exception=type(exc).__name__,reason=str(exc),compiler_collision_guard_reached=False,meaning='The historical compound mutation demonstrates stale-state refusal, not isolated collision-guard coverage.')
else:raise AssertionError('Historical compound mutation unexpectedly accepted')
result['audit_script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
result.update(historical_manifest_sha256=hashlib.sha256((R/'oracle/history/PIN.json').read_bytes()).hexdigest())
(R/'reports/HISTORICAL-COLLISION-AUDIT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(result['reason'])
