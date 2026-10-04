"""Bounded exact-polynomial representation and internal API boundary audit."""
from pathlib import Path
import hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);r.validate()
from grandportage import groebner as G
rows=[]
for name,text in [('ordinary','x^2'),('derived_above_sparse_limit','x^100000*x')]:
 p=G.parse_polynomial(text,['x']);encoded=G.encode_sparse_polynomial(p)
 try:q=G.parse_polynomial(encoded,['x']);outcome={'accepted':True,'equal':q==p}
 except G.CertificateError as exc:outcome={'accepted':False,'message':str(exc)}
 assert outcome['accepted']==(name=='ordinary')
 rows.append({'id':name,'input':text,'rendered':G.render_polynomial(p),'sparse':encoded,'reparse':outcome})
negative=G.Polynomial(['x'],0,{(-1,):1});copied=G.parse_polynomial(negative,['x']);assert copied==negative
try:G.parse_polynomial(G.encode_sparse_polynomial(negative),['x'])
except G.CertificateError as exc:negative_refusal=str(exc)
else:raise AssertionError('negative sparse power accepted')
rows.append({'id':'internal_negative_power','internal_constructor_accepted':True,'native_object_parse_accepted':True,'sparse_parse_refusal':negative_refusal,'scope':'Direct trusted-process Python object construction, not JSON/infix admission.'})
left=G.parse_polynomial('x',['x'],0);right=G.parse_polynomial('1',['y'],2)
quotient=left.divide_by_scalar(right);assert quotient==left
try:left+right
except G.CertificateError as exc:add_refusal=str(exc)
else:raise AssertionError('cross-ring addition accepted')
rows.append({'id':'cross_ring_scalar_method','division_rendered':G.render_polynomial(quotient),'addition_refusal':add_refusal,'scope':'Direct method call; infix parser creates both operands in the same validated ring and budget.'})
a=G.parse_polynomial('x',['x']);b=G.parse_polynomial('x',['x']);assert a==b
try:a+b
except G.CertificateError as exc:budget_refusal=str(exc)
else:raise AssertionError('separate-budget addition accepted')
rows.append({'id':'distinct_budget_operands','equality':True,'addition_refusal':budget_refusal})
report={'controls':rows,'source_sha256':r.sha(ROOT/'oracle/checkout/grandportage/groebner.py'),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'findings':['Valid infix arithmetic can generate exponent 100001; sparse encoding emits it but sparse parsing refuses it. Bounded encoding/roundtrip claims need this qualification.','Internal Polynomial objects do not independently enforce nonnegative exponents; passing a native object through parse preserves that assumption.','divide_by_scalar does not use _same_ring on its argument; no external parser bypass reproduced.','Equality intentionally ignores invocation budget while arithmetic requires a shared budget.'],'proposed_fix':'Define limits on intermediate/result exponents versus syntax explicitly and validate output encoding against its advertised input contract. Either validate internal constructor and scalar-operation invariants or mark/enforce their trusted-caller preconditions. No silent expansion of limits.','scope':'Tiny exact synthetic controls; no high-memory expansion, CAS, graph mutation, campaign source or frozen source edits. No false JSON/text proof admission demonstrated.'}
(ROOT/'reports/POLYNOMIAL-REPRESENTATION-BOUNDARY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print('Five representation/API controls verified; exponent roundtrip mismatch reproduced.')
