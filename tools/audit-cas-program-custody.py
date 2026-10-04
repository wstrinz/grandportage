"""Program mutability and declaration metadata controls, no live CAS."""
import hashlib,json,tempfile
from pathlib import Path
from grandportage import cas,store as S
r=Path(__file__).resolve().parents[1]
def program(body=None,generators=None):
 return cas.CASProgram(cas.SINGULAR,ring='GP_R',ring_vars=['x'],decls=[('GP_I','ideal','x')],body=body or [],outputs=['GP_I'],generators=generators)
try:program(body=['poly x = 1;']); refused=False
except cas.IdentifierCollision:refused=True
assert refused
seen=[]
def runner(p,t):
 seen.append(p.text)
 return {'returncode':0,'aborted':False,'stdout':'@@GP_I:\nGP_I[1]=x\n'+p.completion_marker+'\n','stderr':'','argv':['injected']}
p=program();p.body.append('poly x = 1;')
result=cas.SingularBackend(runner=runner,binary_version='test-double').execute(p)
assert 'poly x = 1;' in seen[-1]
assert cas._parse_result(result,p.outputs)=={'GP_I':'GP_I[1]=x'}
rows=[{'control':'constructor_shadowing','refused':refused},{'control':'post_constructor_mutation','runner_received_shadowing_statement':True,'complete_mock_transcript_parsed':True,'scope':'Direct Python object mutation; no live CAS or graph admission.'}]
root=Path(tempfile.mkdtemp(prefix='program-metadata-',dir=r/'tmp'))
S.append([{'ev':'model','id':'SRC','what':'source','field':'Q','characteristic':0,'ring_vars':['x'],'generators':['x']}],str(root))
p=program(generators=['1'])
answer=cas.run_cas(p,edge={'src':'SRC','type':'IMAGE_CLOSURE','map_kind':'POLYNOMIAL','why':'synthetic declaration control'},produces='DST',describes='caller metadata',root=str(root),_runner=runner)
g=S.load(S.graph_path(str(root)))
assert g.models['DST']['generators']==['1'] and answer['values']=={'GP_I':'GP_I[1]=x'}
rows.append({'control':'generator_metadata_not_output','stored_generators':g.models['DST']['generators'],'parsed_output':answer['values'],'scope':'Model declaration copies caller-supplied program.generators, not output. No verified operation/contraction verdict was created.'})
report={'source_commit':'ac4155787207e2847d248cffed7be871d5dcd577','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'observations':rows}
(r/'reports/CAS-PROGRAM-CUSTODY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(rows,indent=2))
