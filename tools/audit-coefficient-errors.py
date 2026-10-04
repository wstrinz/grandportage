"""Check coefficient validator error boundaries using bounded JSON inputs."""
from pathlib import Path
import contextlib,copy,hashlib,importlib.util,io,json,tempfile
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import coefficient_expansion as C,cli
base={'schema':C.SCHEMA,'characteristic':0,'parameter':'y','coefficient_variables':['a'],'source_variables':['p'],'images':{'p':'a'},'bounded_variables':{},'equations':[{'id':'eq','expression':'p','degree':0,'coverage':C.COMPLETE,'coefficients':{'0':'a'}}]}
controls=[('valid',copy.deepcopy(base),'accepted',0)]
s=copy.deepcopy(base);s['equations'][0]['coverage']='unknown';controls.append(('invalid_string',s,'CoefficientExpansionError',2))
s=copy.deepcopy(base);s['equations'][0]['coverage']=[];controls.append(('list_coverage',s,'TypeError','TypeError'))
s=copy.deepcopy(base);s['equations'][0]['coefficients']={'\u00b2':'a'};controls.append(('unicode_digit_key',s,'ValueError',2))
rows=[]
with tempfile.TemporaryDirectory(prefix='coefficient-boundary-',dir=ROOT/'tmp') as tmp:
 for name,s,expected_direct,expected_cli in controls:
  try:result=C.verify(s);direct={'outcome':'accepted','verdict':result['verdict']}
  except Exception as exc:direct={'outcome':type(exc).__name__,'message':str(exc)}
  assert direct['outcome']==expected_direct,(name,direct)
  path=Path(tmp)/(name+'.json');path.write_text(json.dumps(s),encoding='utf-8');out=io.StringIO();err=io.StringIO()
  with contextlib.redirect_stdout(out),contextlib.redirect_stderr(err):
   try:code=cli.main(['verify-coefficient-expansion','--spec',str(path)]);observation={'outcome':code}
   except Exception as exc:observation={'outcome':type(exc).__name__,'message':str(exc)}
  observation.update(stdout=out.getvalue(),stderr=err.getvalue());assert observation['outcome']==expected_cli,(name,observation)
  rows.append({'id':name,'input':s,'direct':direct,'cli':observation})
report={'controls':rows,'finding':'A list-valued coverage raises uncaught TypeError through CLI. Superscript digit passes str.isdigit but int conversion raises ValueError; CLI catches it, direct domain exception contract differs. Invalid string yields normal refusal and valid control accepts. No malformed input produced authority.','proposed_fix':'Validate coverage as a string before membership. Validate ASCII canonical row keys before conversion and normalize validation errors to CoefficientExpansionError; retain CLI and direct boundary controls.','scope':'Bounded local JSON files under disposable F scratch; no graph write, CAS or campaign.','source_hashes':{p:r.sha(ROOT/p) for p in ['oracle/checkout/grandportage/coefficient_expansion.py','oracle/checkout/grandportage/cli.py']},'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'reports/COEFFICIENT-ERROR-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print('Four direct and CLI controls verified; malformed coverage list escapes as TypeError.')
