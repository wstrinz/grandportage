"""Neutral product-identity and branch-construction premise controls."""
from pathlib import Path
import hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import product_split as P,operations as O

def receipt(equation='x*y',scalar='1'):
 return {'schema':'product_split_v1','characteristic':0,'ring_vars':['x','y','z'],'unit_generators':['z'],'receipts':[{'id':'split','equation':equation,'scalar':scalar,'left':'x','right':'y'}]}
def construct(value,generators):
 return O.product_split('parent',['x','y','z'],generators,value,'split',coefficient_domain='Q',point_universe='ALGEBRAIC_CLOSURE',open_conditions=['z'])
rows=[]
for name,value,generators,expected in [('constant',receipt(),['x*y'],True),('normalized_parent',receipt(),['y*x'],True),('equivalent_ideal_nonliteral',receipt(),['2*x*y'],False),('variable_unit',receipt('z*x*y','z'),['z*x*y'],False),('false_identity',receipt('x*y+1'),['x*y+1'],False)]:
 try:
  op=construct(value,generators)
  models=[e for e in op.events if e['ev']=='model']
  assert len(models)==2 and all(e['open_conditions']==['z'] for e in models)
  assert not any(e['ev']=='verdict' for e in op.events)
  result={'accepted':True,'event_kinds':[e['ev'] for e in op.events],'open_conditions_preserved':True,'no_verdict_event':True}
 except (P.ProductSplitError,ValueError) as exc:
  result={'accepted':False,'exception':type(exc).__name__,'message':str(exc)}
 assert result['accepted']==expected,(name,result)
 rows.append({'id':name,'spec':value,'parent_generators':generators,'observation':result})
unit_report=P.verify(receipt('z*x*y','z'));assert unit_report['verdict']==P.VERIFIED
# Each omission keeps the formal polynomial identity true but removes one interpretation premise.
countermodels=[{'omitted':'no_zero_divisors','ring':'Z/6Z','scalar':1,'left':2,'right':3,'equation_value':0}, {'omitted':'scalar_remains_unit','ring':'Q','scalar':0,'left':1,'right':1,'equation_value':0}, {'omitted':'equation_vanishes','ring':'Q','scalar':1,'left':1,'right':1,'equation_value':1}]
for c in countermodels:
 product=c['scalar']*c['left']*c['right']
 if c['ring']=='Z/6Z':product%=6
 assert product==c['equation_value'] and c['left']!=0 and c['right']!=0
positive=[]
for p in [2,3,5,7]:
 tuples=[(s,x,y) for s in range(1,p) for x in range(p) for y in range(p) if s*x*y%p==0]
 assert all(x==0 or y==0 for s,x,y in tuples)
 positive.append({'prime':p,'vanishing_unit_product_assignments':len(tuples),'all_have_zero_factor':True})
report={'constructor_controls':rows,'variable_unit_standalone_verdict':unit_report['verdict'],'countermodels':countermodels,'positive_finite_field_controls':positive,'scope':'Exact synthetic arithmetic and pinned direct constructor/checker only. Z/6Z is a premise-deletion semantic countermodel, not an admitted characteristic-six GP model. Finite enumeration is not a general soundness proof. No graph append, CAS or campaign source.','source_hashes':{p:r.sha(ROOT/p) for p in ['oracle/checkout/grandportage/product_split.py','oracle/checkout/grandportage/operations.py']},'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'reports/PRODUCT-SPLIT-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Five constructor controls, three premise countermodels and four finite-field positive enumerations verified.')
