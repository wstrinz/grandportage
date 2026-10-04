"""Audit localization sparse/text boundary without changing the oracle."""
from pathlib import Path
import contextlib, copy, hashlib, importlib.util, io, json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import cli, groebner as G, localization as L
base={'schema':L.SCHEMA,'characteristic':0,'ring_vars':['x'],'generators':['x'],'guards':['x'],'expression':{'numerator':'1','denominator_powers':[0]},'certificate':{'localization_powers':[1],'membership_target':'x','cofactors':['1']}}
sparse=G.encode_sparse_polynomial(G.parse_polynomial('x',['x']))
rows=[]
for name,guard in [('infix','x'),('sparse',sparse)]:
 value=copy.deepcopy(base);value['guards']=[guard]
 report=L.verify(value);assert report['verdict']==L.VERIFIED
 path=ROOT/'tmp'/('localization-boundary-'+name+'.json');path.write_text(json.dumps(value),encoding='utf-8')
 for as_json in [False,True]:
  out=io.StringIO();err=io.StringIO();args=['verify-localization-membership','--spec',str(path)]+(['--json'] if as_json else [])
  with contextlib.redirect_stdout(out),contextlib.redirect_stderr(err):
   try:code=cli.main(args);failure=None
   except TypeError as exc:code=None;failure=str(exc)
  assert (failure is not None)==(name=='sparse' and not as_json)
  if failure is None:assert code==0
  rows.append({'id':name+('_json' if as_json else '_text'),'direct_verdict':report['verdict'],'exit_code':code,'type_error':failure,'stdout':out.getvalue(),'stderr':err.getvalue()})
for name,guards in [('duplicate_infix',['x','x+0']),('duplicate_mixed',['x',sparse])]:
 value=copy.deepcopy(base);value['guards']=guards;value['expression']['denominator_powers']=[0,0];value['certificate']['localization_powers']=[1,0]
 try:report=L.verify(value);accepted=True;message=None
 except L.LocalizationError as exc:accepted=False;message=str(exc)
 assert accepted==(name=='duplicate_mixed')
 rows.append({'id':name,'accepted':accepted,'message':message})
report={'controls':rows,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':{p:r.sha(ROOT/'oracle/checkout'/p) for p in ['grandportage/localization.py','grandportage/cli.py']},'findings':['A valid sparse guard passes direct verification and JSON CLI output; default text output prints a verified header then raises uncaught TypeError in string join.','Equivalent infix guards are rejected as duplicates; an infix/sparse pair representing the same polynomial is accepted because uniqueness keys retain representation kind. Repeated inversion does not invalidate this identity.'],'proposed_fixes':['Render guard values using the polynomial formatter (or a format-aware serializer) before joining; ensure successful verification has a complete output path.','Use representation-independent canonical polynomial keys for guard uniqueness, or explicitly revise the uniqueness contract; do not silently change expectations.'],'scope':'Six tiny controls, no CAS or campaign data. Rendering crash and uniqueness-contract gap, not false mathematical acceptance or a normal REFUSE result.'}
(ROOT/'reports/LOCALIZATION-REPRESENTATION-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Six localization representation controls verified.')
