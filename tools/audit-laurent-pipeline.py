"""Neutral Laurent/coefficient composition boundary controls."""
from pathlib import Path
import copy,hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import laurent_lowering as L,coefficient_expansion as C,laurent_coefficient_pipeline as P
laurent={'schema':L.SCHEMA,'characteristic':0,'series_variable':'y','coefficient_variables':['a'],'inputs':{'F':{'-1':'a'}},'program':[],'equalities':[{'id':'self','left':'F','right':'F'}],'exports':[{'id':'cleared','node':'F','shift':1}]}
image={'schema':'sparse_polynomial_v1','terms':[{'coefficient':'1','powers':[['a',1]]}]}
coefficient={'schema':C.SCHEMA,'characteristic':0,'parameter':'y','coefficient_variables':['a'],'source_variables':['s'],'images':{'s':image},'bounded_variables':{},'equations':[{'id':'eq','expression':'s','degree':0,'coverage':C.COMPLETE,'coefficients':{'0':'a'}}]}
base={'schema':P.SCHEMA,'laurent':laurent,'coefficient_expansion':coefficient,'bindings':[{'export':'cleared','image':'s'}]}
controls=[('bound',copy.deepcopy(base),True)]
s=copy.deepcopy(base);s['coefficient_expansion']['images']['s']['terms'][0]['coefficient']='2';s['coefficient_expansion']['equations'][0]['coefficients']['0']='2*a';controls.append(('self_consistent_changed_intermediate',s,False))
s=copy.deepcopy(base);s['coefficient_expansion']['images']['s']='a';controls.append(('equivalent_infix_intermediate',s,False))
s=copy.deepcopy(base);s['bindings']=[];controls.append(('missing_bindings',s,False))
s=copy.deepcopy(base);s['bindings']*=2;controls.append(('duplicate_binding',s,False))
s=copy.deepcopy(base);s['laurent']['exports'].append({'id':'extra','node':'F','shift':1});controls.append(('unused_verified_export',s,True))
rows=[]
for name,s,expected in controls:
 left=L.verify(s['laurent']);right=C.verify(s['coefficient_expansion'])
 try:
  result=P.verify(s);accepted=True;detail={'verdict':result['verdict'],'licenses':result['licenses'],'authority_boundary':result['authority_boundary']}
 except P.LaurentCoefficientPipelineError as exc:accepted=False;detail={'exception':type(exc).__name__,'message':str(exc)}
 assert accepted==expected,(name,detail)
 rows.append({'id':name,'input':s,'individual_passes_verified':True,'pipeline_accepted':accepted,'observation':detail})
report={'controls':rows,'scope':'Pinned exact compiler validators; finite Laurent input a/y shifted to a. Reflexive equality checks no source derivation; no chart validity or model authority claimed. No CAS, campaign or graph mutation.','finding':'Both passes can verify independently while composition refuses an edited or merely differently represented intermediate. Total bindings concern downstream images; unused verified exports are allowed.','source_hashes':{p:r.sha(ROOT/p) for p in ['oracle/checkout/grandportage/laurent_lowering.py','oracle/checkout/grandportage/laurent_coefficient_pipeline.py','oracle/checkout/grandportage/coefficient_expansion.py']},'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'reports/LAURENT-PIPELINE-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Six pipeline controls verified; both individual passes valid in all six.')
