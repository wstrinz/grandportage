"""Reproducible hostile controls and corpus-sized toy-load test. No corpus semantic replay."""
import copy, hashlib, json, pathlib, subprocess, sys, time
ROOT=pathlib.Path(__file__).resolve().parents[1]
PKG=ROOT/'spikes/lean-core'
SCRATCH=ROOT/'tmp/phase0c'
SCRATCH.mkdir(parents=True,exist_ok=True)
EXE=PKG/'.lake/build/bin/gp_spike.exe'
CHECK=PKG/'.lake/build/bin/gp_check_spike.exe'
PYTHON=ROOT/'.venv/Scripts/python.exe'
SHA=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
results=[]
def run(name,exe,args,expected,validate=lambda j:True):
    start=time.perf_counter()
    p=subprocess.run([str(exe),*map(str,args)],capture_output=True,text=True,timeout=60,cwd=ROOT)
    elapsed=time.perf_counter()-start
    try:j=json.loads(p.stdout)
    except Exception:j={'raw':p.stdout}
    ok=p.returncode==expected and validate(j)
    results.append({'name':name,'seconds':elapsed,'exit':p.returncode,'output':j,'stderr':p.stderr,'passed':ok})
    assert ok,(name,p.returncode,j,p.stderr)
    return j
def log(name,events,expected=0,wanted=None):
    p=SCRATCH/(name+'.jsonl')
    p.write_text('\n'.join(json.dumps(x,separators=(',',':')) for x in events)+'\n',encoding='utf-8')
    def validate(j):
        return wanted is None or {x['id']:x['held'] for x in j['claims']}==wanted
    return run(name,EXE,[p],expected,validate)
mh=hashlib.sha256(b'toy-model-v1').hexdigest()
ch=SHA(PKG/'Spike.lean')
sources=[{'event':'source','key':'model','hash':mh},{'event':'source','key':'checker','hash':ch}]
claim={'event':'declare','id':'base','lhs':7,'rhs':7,'scope':['Q','R'],'model':'model','model_hash':mh,'checker_hash':ch}
receipt={**claim,'event':'receipt','reach':['Q','R']}
base=sources+[claim,receipt]
narrow={'event':'narrow','id':'narrow','parent':'base','scope':['Q']}
log('positive-narrow',base+[narrow],wanted={'base':True,'narrow':True})
log('assertion-alone',sources+[claim],wanted={'base':False})
false=copy.deepcopy(base); false[2]['rhs']=8;false[3]['rhs']=8
log('false-equality',false,wanted={'base':False})
for field,value in [('lhs',8),('scope',['Q']),('model_hash','tampered'),('checker_hash','tampered'),('id','other')]:
    bad=copy.deepcopy(base);bad[3][field]=value
    log('receipt-mismatch-'+field,bad,wanted={'base':False})
log('insufficient-reach',sources+[claim,{**receipt,'reach':['Q']}],wanted={'base':False})
log('widening-refused',base+[{**narrow,'scope':['Q','R','C']}],wanted={'base':True,'narrow':False})
log('stale-model',base+[narrow,{'event':'source','key':'model','hash':'new'}],wanted={'base':False,'narrow':False})
log('stale-checker',base+[{'event':'source','key':'checker','hash':'new'}],wanted={'base':False})
log('duplicate-id',base+[claim],expected=2)
log('unknown-event',[{'event':'invent-authority'}],expected=2)
log('bad-field-type',sources+[{**claim,'lhs':'7'}],expected=2)
log('missing-field',sources+[{k:v for k,v in claim.items() if k!='scope'}],expected=2)
log('cyclic-narrow',[{'event':'narrow','id':'a','parent':'b','scope':['Q']},{'event':'narrow','id':'b','parent':'a','scope':['Q']}],wanted={'a':False,'b':False})
p=SCRATCH/'malformed.jsonl';p.write_text('{bad json}\n')
run('malformed-json',EXE,[p],2)
# Same exact byte concatenation and repeat fold; no commutative merge claim.
left=SCRATCH/'left.jsonl';right=SCRATCH/'right.jsonl';joined=SCRATCH/'joined.jsonl'
left.write_text('\n'.join(map(json.dumps,base))+'\n');right.write_text(json.dumps(narrow)+'\n')
joined.write_bytes(left.read_bytes()+right.read_bytes())
a=run('concatenated-fold',EXE,[joined],0);b=run('deterministic-refold',EXE,[joined],0)
assert a==b
# Case IDs and case-byte digests populate opaque toy model fields; this is a load exercise ONLY.
cases=sorted((ROOT/'corpus/must').glob('*.json'))
assert len(cases)==459
events=[];wanted={}
for ix,p in enumerate(cases):
    j=json.loads(p.read_text(encoding='utf-8')); cid=j['id']; digest=SHA(p)
    events.append({'event':'source','key':cid,'hash':digest})
    c={**claim,'id':cid,'lhs':ix,'rhs':ix,'model':cid,'model_hash':digest,'scope':['toy']}
    events.extend([c,{**c,'event':'receipt','reach':['toy']}]);wanted[cid]=True
events.insert(0,sources[1])
log('459-case-sized-load',events,wanted=wanted)
def term(exp,num,den=1):return dict(exp=exp,num=num,den=den)
unit=dict(generators=[[term(1,2)],[term(0,1),term(1,-2)]],cofactors=[[term(0,1)],[term(0,1)]],target=[term(0,1)])
fraction=dict(generators=[[term(1,2)],[term(0,1),term(1,-2)]],cofactors=[[term(0,1,2)],[term(0,1,2)]],target=[term(0,1,2)])
candidates={'unit':(unit,0),'fraction':(fraction,0)}
bad=copy.deepcopy(unit);bad['cofactors'][1][0]['num']=2;candidates['tampered-cofactor']=(bad,1)
bad=copy.deepcopy(unit);bad['cofactors']=bad['cofactors'][:1];candidates['truncated-cofactor']=(bad,1)
bad=copy.deepcopy(unit);bad['target']=[term(0,1),term(5,1)];candidates['high-degree-target']=(bad,1)
bad=copy.deepcopy(unit);bad['cofactors'][0][0]['den']=0;candidates['zero-denominator']=(bad,2)
bad=copy.deepcopy(unit);bad['target']=[term(0,3),term(0,-2)];candidates['duplicate-terms']=(bad,0)
for name,(candidate,code) in candidates.items():
    p=SCRATCH/(name+'.json');p.write_text(json.dumps(candidate),encoding='utf-8')
    run('lean-poly-'+name,CHECK,['poly',p],code)
    # External invalid candidate reports a valid response with valid=false => exit1; parse failure child exit2 also refused by wrapper exit1.
    run('process-poly-'+name,CHECK,['external',PYTHON,PKG/'fraction_checker.py',p],0 if code==0 else 1)
# Positive child exit alone cannot pass binding/version checks.
for kind,response in [('wrong-input',{'request':'other','checker':'fraction-cofactor-v1','valid':True}),('wrong-version',{'checker':'other','valid':True})]:
    p=SCRATCH/(kind+'.py')
    if kind=='wrong-input':s='import json;print('+repr(json.dumps(response))+')'
    else:s='import json,sys;request=sys.stdin.read();print(json.dumps(dict(request=request,checker="other",valid=True)))'
    p.write_text(s,encoding='utf-8')
    run('process-'+kind,CHECK,['external',PYTHON,p,SCRATCH/'unit.json'],1)
for name,proof,kind,code in [('valid','3 0 1 2 0\n','unsat',0),('sat-counterexample','3 0 1 2 0\n','sat',1),('bad-hints','3 0 9 0\n','unsat',1),('malformed','nonsense\n','unsat',2)]:
    p=SCRATCH/(name+'.lrat');p.write_text(proof,encoding='utf-8')
    run('lrat-'+name,CHECK,['lrat',p,kind],code)
out={'status':'passed','case_count':459,'semantic_corpus_execution':False,'results':results,'source_hashes':{str(p.relative_to(ROOT)).replace('\\','/'):SHA(p) for p in PKG.rglob('*') if p.is_file() and '.lake' not in p.parts},'executable_hashes':{str(p.relative_to(ROOT)).replace('\\','/'):SHA(p) for p in (EXE,CHECK)}}
(ROOT/'reports/PHASE-0C-CORE-VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':out['status'],'checks':len(results),'toy_load_seconds':next(r['seconds'] for r in results if r['name']=='459-case-sized-load')}))


