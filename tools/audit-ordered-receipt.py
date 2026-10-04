import hashlib,importlib.util,json
from pathlib import Path
from grandportage import ordered as O,ordered_receipt as R,store as S
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('ordered_tests',ROOT/'oracle/checkout/tests/test_ordered_real_semantics.py');T=importlib.util.module_from_spec(spec);spec.loader.exec_module(T)
rows=[]
for name,poly,interval,expr,expected in [('repeated interior root','(w^2-2)^2',('1','2'),'w',1),('zero at repeated root','(w^2-2)^2',('1','2'),'w^2-2',0),('repeated endpoint root','(w-2)^2',('2','3'),'w',1),('reversed endpoint interval','w-2',('2','1'),'w',1)]:
 model=T._model(generator=poly,interval=interval);sign,receipt=O.selected_real_sign(model,expr);assert sign==expected and R.verify(model,expr,receipt)==expected
 rows.append({'name':name,'sign':sign,'producer_and_checker_agree':True})
try:T._graph([T._model(generator='w-2',interval=('2','1')),T._claim()])
except S.GraphError as e:
 assert 'lo < hi' in str(e);rows.append({'name':'native reversed interval control','result':'REFUSED','reason':str(e)})
else:raise AssertionError('native schema must refuse')
report={'oracle_commit':'ac4155787207e2847d248cffed7be871d5dcd577','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Five exact offline controls. Reversed interval acceptance is direct API only and is blocked by native model validation.','controls':rows}
(ROOT/'reports/ORDERED-RECEIPT-BOUNDARIES.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print('5 ordered receipt controls verified')
