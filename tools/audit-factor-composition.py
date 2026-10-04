"""Neutral exact factor and affine-composition controls; no graph authority."""
from pathlib import Path
import copy,hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import factor_power as F,factor_power_contradiction as C
factor={'schema':F.SCHEMA,'characteristic':0,'ring_vars':['x','u'],'unit_generators':['u'],'receipts':[{'id':'power','equation':'x^2','scalar':'1','base':'x','exponent':2}]}
composition={'schema':C.SCHEMA,'factor_power':factor,'factor_receipt':'power','pivot':{'variable':'x','solution':'0'},'consequence':{'id':'second','equation':'x+1','residual':'1'}}
controls=[('factor_valid',F.verify,factor,True)]
for name,changes,expected in [('max_exponent',{'equation':'x^64','exponent':64},True),('over_exponent',{'equation':'x^65','exponent':65},False),('bool_exponent',{'equation':'x','exponent':True},False),('unit_scalar',{'equation':'u*x^2','scalar':'u'},True),('undeclared_scalar',{'equation':'x^3','scalar':'x'},False)]:
 s=copy.deepcopy(factor);s['receipts'][0].update(changes);controls.append((name,F.verify,s,expected))
controls.append(('composition_valid',C.verify,composition,True))
for name,key,change in [('self_referential_pivot','pivot',{'variable':'x','solution':'x'}),('wrong_residual','consequence',{'id':'second','equation':'x+1','residual':'2'}),('nonunit_residual','consequence',{'id':'second','equation':'x','residual':'0'})]:
 s=copy.deepcopy(composition);s[key]=change;controls.append((name,C.verify,s,False))
rows=[]
for name,checker,value,expected in controls:
 try:
  result=checker(value);observed=True;detail={'verdict':result['verdict'],'licenses':result['licenses'],'open_obligations':result['open_obligations'],'authority_boundary':result['authority_boundary']}
 except (F.FactorPowerError,C.FactorPowerContradictionError) as exc:
  observed=False;detail={'exception':type(exc).__name__,'message':str(exc)}
 assert observed==expected,(name,detail)
 rows.append({'id':name,'input':value,'accepted':observed,'observation':detail})
assert 2**2%4==0 and 2%4!=0
report={'controls':rows,'semantic_countermodel':{'ring':'Z/4Z','base':2,'exponent':2,'power':0,'base_nonzero':True,'scope':'Without excluding nonzero nilpotents, vanishing powers do not force base vanishing. Not a GP characteristic-four model.'},'scope':'Pinned direct checkers, synthetic exact inputs. No model/graph events, CAS or campaign. Max-exponent refusal is resource policy, not a false mathematical identity.','source_hashes':{p:r.sha(ROOT/p) for p in ['oracle/checkout/grandportage/factor_power.py','oracle/checkout/grandportage/factor_power_contradiction.py']},'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'reports/FACTOR-COMPOSITION-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Ten direct checker controls and one nilpotent premise countermodel verified.')
