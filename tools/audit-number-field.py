import hashlib,json
from pathlib import Path
from grandportage import number_field as N
ROOT=Path(__file__).resolve().parents[1]
field={'kind':N.SCHEMA,'base':'Q','symbol':'a','minimal_polynomial':'a^3-2'}
model={'characteristic':0,'coefficient_domain':'Q','point_universe':'ALGEBRAIC_CLOSURE','ring_vars':['x'],'generators':['x^3-2'],'open_conditions':['x']}
rows=[]
ok,why,receipt=N.check_extension_witness(model,field,{'x':'a'});assert ok
rows.append({'name':'irreducible cubic point','is_point':ok,'receipt':receipt})
m={**model,'generators':['2*x^3-1']}
ok,why,receipt=N.check_extension_witness(m,field,{'x':{'numerator':'1','denominator':'a'}});assert ok
rows.append({'name':'invertible algebraic denominator','is_point':ok,'receipt':receipt})
ok,why,receipt=N.check_extension_witness({**model,'open_conditions':['x^3-2']},field,{'x':'a'});assert not ok
rows.append({'name':'vanishing guard','is_point':ok,'reason':why})
try:N.check_extension_witness(model,{**field,'minimal_polynomial':'a^3-a'}, {'x':'a'})
except N.NumberFieldError as e:
 assert 'reducible' in str(e);rows.append({'name':'reducible cubic','result':'UNVERIFIABLE_FIELD','reason':str(e)})
else:raise AssertionError('expected refusal')
report={'oracle_commit':'ac4155787207e2847d248cffed7be871d5dcd577','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Four exact native arithmetic controls, no CAS or campaign data.','controls':rows}
(ROOT/'reports/NUMBER-FIELD-BOUNDARIES.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print('4 number-field controls verified')
