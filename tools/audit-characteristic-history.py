"""Audit the historical characteristic predicate without executing the old application."""
from pathlib import Path
import ast,hashlib,importlib.util,json,subprocess
ROOT=Path(__file__).resolve().parents[1];COMMIT='f2b7c49e59d382ba182e90aee057c3441911d183';SOURCE=str((Path(__import__('os').environ.get('GP_DEV_ROOT') or Path.home()/'dev'))/'grand-portage')
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import store as S
raw=subprocess.check_output(['git','-C',SOURCE,'show',COMMIT+':grandportage/store.py']);tree=ast.parse(raw)
method=next(n for n in ast.walk(tree) if isinstance(n,ast.FunctionDef) and n.name=='_apply_model')
first=method.body[0];assert isinstance(first,ast.If)
check=next(n for n in ast.walk(first) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='_require');predicate=check.args[0]
assert ast.unparse(predicate)=='isinstance(ch, int) and (not isinstance(ch, bool)) and (ch >= 0)'
compiled=compile(ast.Expression(predicate),'<historical-characteristic-predicate>','eval')
rows=[]
for value in [-1,False,0,1,2,4,23,'23']:
 old=eval(compiled,{'__builtins__':{},'isinstance':isinstance,'int':int,'bool':bool},{'ch':value});new=S.valid_characteristic(value)
 rows.append(dict(value=value,type=type(value).__name__,historical_predicate=old,current_predicate=new))
assert [x['value'] for x in rows if x['historical_predicate']!=x['current_predicate']]==[1,4]
report=dict(commit=COMMIT,historical_source_sha256=hashlib.sha256(raw).hexdigest(),current_source_sha256=r.sha(ROOT/'oracle/checkout/grandportage/store.py'),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),predicate=ast.unparse(predicate),controls=rows,scope='Only the exact extracted historical Boolean predicate is evaluated; no old module, verifier, CAS or campaign executes.',finding='Historical diagnostic claimed prime characteristic but admitted 1 and composite 4; pinned validator refuses both. Historical None bypass and default-to-zero sites are read-only observations, not executed here.')
(ROOT/'reports/CHARACTERISTIC-PREDICATE-HISTORY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print('Eight predicate controls verified; historical 1 and 4 admission differs from pinned validator.')
