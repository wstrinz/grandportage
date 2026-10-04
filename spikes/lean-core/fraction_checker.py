"""External Fraction checker for the spike, not an admitted GP checker."""
import json, sys
from fractions import Fraction
def poly(terms):
    out = {}
    for t in terms:
        if type(t['exp']) is not int or t['exp'] < 0: raise ValueError('bad exponent')
        if type(t['num']) is not int or type(t['den']) is not int or t['den'] <= 0: raise ValueError('bad rational')
        e = t['exp']
        out[e] = out.get(e, Fraction()) + Fraction(t['num'], t['den'])
    return out
def check(j):
    gs, qs, target = j['generators'], j['cofactors'], poly(j['target'])
    if len(gs) != len(qs): return False
    total = {}
    for g,q in zip(gs,qs):
        for a,x in poly(g).items():
            for b,y in poly(q).items():
                total[a+b] = total.get(a+b, Fraction()) + x*y
    return {e:c for e,c in total.items() if c} == {e:c for e,c in target.items() if c}
request = sys.stdin.read()
try:
    valid = check(json.loads(request))
    print(json.dumps({'request':request,'checker':'fraction-cofactor-v1','valid':valid}))
except Exception as exc:
    print(json.dumps({'request':request,'checker':'fraction-cofactor-v1','valid':False,'error':str(exc)}))
    sys.exit(2)
