"""Untrusted realization search for the 3P campaign (campaign-op; GP replays everything).

Fields: F(p, m) = F_p[a]/(m) (p = 0 means Q; m = [1] means the prime field).
A realization is found by placing points one at a time: a point on two lines
through placed points is their intersection, on one line a random point of it,
otherwise random.  It is then moved to the encoder's frame and checked against
the encoded equations and guards.
"""
import json, random, itertools, math
from fractions import Fraction
import sympy as sp


class F:
    def __init__(self, p, m=(1,)):  # m: monic coefficients, low degree first, e.g. a^2+a+1 -> (1,1,1)
        self.p, self.m, self.k = p, tuple(m), len(m) - 1

    def c(self, x):
        return Fraction(x) if self.p == 0 else x % self.p

    def el(self, coeffs):
        v = [self.c(x) for x in coeffs] + [self.c(0)] * self.k
        return tuple(v[: max(self.k, 1)])

    def zero(self): return self.el([0])
    def one(self): return self.el([1])

    def add(self, x, y): return tuple(self.c(a + b) for a, b in zip(x, y))
    def neg(self, x): return tuple(self.c(-a) for a in x)
    def sub(self, x, y): return self.add(x, self.neg(y))

    def mul(self, x, y):
        k = max(self.k, 1)
        prod = [self.c(0)] * (2 * k)
        for i, a in enumerate(x):
            for j, b in enumerate(y):
                prod[i + j] = self.c(prod[i + j] + a * b)
        for d in range(2 * k - 1, self.k - 1 if self.k else 0, -1):  # reduce by monic m
            if self.k == 0 or d < self.k: break
            t = prod[d]
            if t:
                for i, mc in enumerate(self.m):
                    prod[d - self.k + i] = self.c(prod[d - self.k + i] - t * mc)
        return tuple(prod[:k])

    def iszero(self, x): return all(a == 0 for a in x)

    def inv(self, x):
        # solve x*y = 1 as a linear system over the base field
        k = max(self.k, 1)
        cols = [self.mul(x, self.el([0] * i + [1])) for i in range(k)]
        A = sp.Matrix(k, k, lambda r, c: cols[c][r])
        b = sp.Matrix([1] + [0] * (k - 1))
        if self.p == 0:
            y = A.LUsolve(b)
            return tuple(Fraction(int(sp.fraction(v)[0]), int(sp.fraction(v)[1])) for v in y)
        y = A.inv_mod(self.p) * b
        return tuple(int(v) % self.p for v in y)

    def rand(self, R=3):
        k = max(self.k, 1)
        if self.p == 0:
            return tuple(Fraction(random.randint(-R, R)) for _ in range(k))
        return tuple(random.randrange(self.p) for _ in range(k))

    def tostr(self, x, var="a"):
        terms = []
        for i, a in enumerate(x):
            if a == 0: continue
            s = str(a)
            terms.append(f"({s})" + (f"*{var}^{i}" if i else ""))
        return " + ".join(terms) if terms else "0"


def cross(K, u, v):
    return [K.sub(K.mul(u[1], v[2]), K.mul(u[2], v[1])),
            K.sub(K.mul(u[2], v[0]), K.mul(u[0], v[2])),
            K.sub(K.mul(u[0], v[1]), K.mul(u[1], v[0]))]


def dot(K, u, v):
    s = K.zero()
    for a, b in zip(u, v): s = K.add(s, K.mul(a, b))
    return s


def det3(K, u, v, w): return dot(K, u, cross(K, v, w))


def construct(K, mat, order=None, R=3):
    els = mat["elements"]
    lines = [set(l) for l in mat["lines"]]
    order = order or els
    pos = {}
    for e in order:
        cons = [l for l in lines if e in l and len([x for x in l if x in pos]) >= 2]
        if not cons:
            v = [K.rand(R) for _ in range(3)]
        elif len(cons) == 1:
            a, b = [x for x in cons[0] if x in pos][:2]
            s, t = K.rand(R), K.rand(R)
            v = [K.add(K.mul(s, pa), K.mul(t, pb)) for pa, pb in zip(pos[a], pos[b])]
        else:
            ls = []
            for l in cons[:2]:
                a, b = [x for x in l if x in pos][:2]
                ls.append(cross(K, pos[a], pos[b]))
            v = cross(K, ls[0], ls[1])
        pos[e] = v
    return pos


def to_frame(K, pos, frame):
    """Projective map sending the frame to e1, e2, e3 (and 1,1,1 when there are four)."""
    A = [pos[f] for f in frame[:3]]  # columns
    # invert the 3x3 matrix with columns A via adjugate
    d = det3(K, A[0], A[1], A[2])
    if K.iszero(d): return None
    di = K.inv(d)
    rows = [cross(K, A[1], A[2]), cross(K, A[2], A[0]), cross(K, A[0], A[1])]  # rows of adj
    T = [[K.mul(di, x) for x in r] for r in rows]
    if len(frame) == 4:
        c = [dot(K, r, pos[frame[3]]) for r in T]
        if any(K.iszero(x) for x in c): return None
        T = [[K.mul(K.inv(c[i]), x) for x in T[i]] for i in range(3)]
    return {e: [dot(K, r, v) for r in T] for e, v in pos.items()}


_PARSED = {}


def _parse(enc):
    key = enc["digest"]
    if key not in _PARSED:
        names = enc["variables"]
        syms = sp.symbols(names)
        _PARSED[key] = [[sp.Poly(sp.sympify(s, locals=dict(zip(names, syms))), *syms).terms() for s in enc[kind]]
                        for kind in ("equations", "nonzero")]
    return _PARSED[key]


def check(K, enc, coords):
    """Evaluate encoded equations and guards at the point (dict var -> field element)."""
    names = enc["variables"]
    vals = []
    for polys in _parse(enc):
        out = []
        for terms in polys:
            acc = K.zero()
            for mon, co in terms:
                t = K.el([int(co) if K.p else Fraction(int(sp.fraction(co)[0]), int(sp.fraction(co)[1]))])
                for v, d in zip(names, mon):
                    for _ in range(d): t = K.mul(t, coords[v])
                acc = K.add(acc, t)
            out.append(acc)
        vals.append(out)
    return vals


def coords_of(enc, framed):
    out = {}
    for v in enc["variables"]:
        comp, e = "xyz".index(v[0]), v[1:]
        out[v] = framed[e][comp]
    return out


def search(K, mat, enc, tries=2000, R=3, orders=None, score=None):
    best = None
    els = mat["elements"]
    for t in range(tries):
        order = random.choice(orders) if orders else (els if t % 3 == 0 else random.sample(els, len(els)))
        pos = construct(K, mat, order, R)
        fr = to_frame(K, pos, enc["frame"])
        if fr is None: continue
        co = coords_of(enc, fr)
        eqs, gs = check(K, enc, co)
        if all(K.iszero(x) for x in eqs) and not any(K.iszero(x) for x in gs):
            sc = score(K, co, gs) if score else 0
            if best is None or sc < best[0]:
                best = (sc, co, gs)
                if not score: break
    return best


def clear_denoms_Q(enc, co):
    """Scale each non-frame point's homogeneous coordinates to coprime integers (Q only)."""
    pts = {}
    for v in enc["variables"]:
        pts.setdefault(v[1:], {})[v[0]] = co[v][0]
    out = {}
    for e, d in pts.items():
        L = math.lcm(*[x.denominator for x in d.values()])
        ints = [int(x * L) for x in d.values()]
        g = math.gcd(*ints) or 1
        for c, x in zip(d.keys(), ints): out[c + e] = (Fraction(x // g),)
    return out


def bad_primes(gs):
    ps = set()
    for g in gs:
        x = g[0]
        for n in (x.numerator, x.denominator):
            ps |= set(sp.factorint(abs(int(n))).keys())
    return ps


def q_score(K, co, gs):
    return sum(math.log(p) * 10 + 1 for p in bad_primes(gs)) + sum(abs(x[0].numerator) for x in co.values()) * 0.01
