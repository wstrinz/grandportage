#!/usr/bin/env python3
"""Emit stock-Comparator challenge/solution shards for the held 3P ledger claims (Track E, route B).

usage: python tools/comparator-emit.py --campaign <campaign dir> --out <output dir>
           [--shard-size 64] [--encoder <encode-matroid.py>] [--prelude <comparator-prelude.lean>]
           [--root GPComparator] [--manifest <path>] [--clean]

Classes (statement in Mathlib vocabulary; `RealizesRank3` and each matroid's lines are spelled out
in the challenge and compared by value, never as `definition_names` holes):
  map-p    map rule at characteristic p: every algebraically closed K with CharP K p realizes M
  map-s    map rule outside S: every algebraically closed K with ringChar K ∉ S realizes M
  point-p  NONEMPTY by a point at p: every field K with CharP K p realizes M
  point-s  NONEMPTY by a point outside S (or at characteristic 0): every field K in scope realizes M
  bridge   NOT_IN_IDEAL(1) by the bridge rule from a NONEMPTY point: every algebraically closed K
           in scope realizes M (solved from the premise's point)
  source   NOT_IN_IDEAL(1) of a monic one-variable source system: f has a root in every
           algebraically closed K in scope
EMPTY claims (ideal certificates) need frame normalization; that class is listed as deferred
(reprioritised 2026-10-09), not refused.

Solutions: the route B prelude (`GPCert`), per claim the checker data and
`GPCert.realizes…_of_certOk … (by decide +kernel)`; sources use `GPCert.exists_rootZ`.

Fidelity checks (a claim failing any of them is refused and listed with its reason, never guessed):
kind, target, scope, rule and premises match the class; characteristics are prime and every receipt
certificate is at the claim's characteristic; the encoder's output reproduces the claim's encoding
digest and system; the matroid is simple rank 3; an independent frame reconstruction equals the
encoder's; the map or point covers exactly the system's variables, every equation vanishes and every
guard is a unit in scope; every triple has the certificate the Lean checker re-checks.
Soundness does not depend on these checks (the kernel checks the certificates); fidelity does.

Writes <out>/<root>/<Shard>/{Challenge,Solution}.lean, <out>/comparator/<shard>.json and the
manifest (default <out>/MANIFEST.json). Same inputs give byte-identical outputs. Reads the campaign;
writes nothing to it unless --manifest points there. A support filed by reference (`receipt_ref`) is
read from its campaign file and checked against its SHA-256; a malformed, missing or mismatched
reference refuses the whole run (exit 2), as it refuses every `gp` command.
"""
import argparse
import hashlib
import importlib.util
import itertools
import json
import re
import shutil
import sys
from fractions import Fraction
from math import gcd

# Certificates carry integers far beyond CPython's default 4,300-digit str() limit (3.11+).
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
from pathlib import Path

EMITTER = "gp-comparator-emit/v1"
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
PART2 = "/-! ## GPCert part 2"
# class id -> shard name prefix (map-p keeps the first run's shard names)
CLASSES = {"map-p": "Shard", "map-s": "MapOut", "point-p": "PointChar", "point-s": "PointOut",
           "bridge": "Bridge", "source": "Source"}
LEDGER_TOTAL_KEY = "claims_in_ledger"


class Refuse(Exception):
    pass


class Deferred(Refuse):
    """A class not emitted yet: listed separately, not as a refusal."""


def sha(data):
    return hashlib.sha256(data).hexdigest()


# ---- univariate polynomials over F_p, coefficient lists low degree first ----
def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def md(a, p):
    return trim([c % p for c in a])


def padd(a, b, p):
    n = max(len(a), len(b))
    return md([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)], p)


def psub(a, b, p):
    return padd(a, [-c for c in b], p)


def pmul(a, b, p):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return md(r, p)


def pdivmod(a, b, p):
    a = md(a, p)
    b = md(b, p)
    inv = pow(b[-1], -1, p)
    q = [0] * max(len(a) - len(b) + 1, 0)
    while len(a) >= len(b) and a:
        c = a[-1] * inv % p
        k = len(a) - len(b)
        q[k] = c
        for i, y in enumerate(b):
            a[k + i] = (a[k + i] - c * y) % p
        a = trim(a)
    return trim(q), a


def pinv(d, f, p):
    """Inverse of d modulo (f, p), or None."""
    r0, r1, s0, s1 = md(f, p), md(d, p), [], [1]
    while r1:
        q, r = pdivmod(r0, r1, p)
        r0, r1, s0, s1 = r1, r, s1, psub(s0, pmul(q, s1, p), p)
    if len(r0) != 1:
        return None
    return pdivmod(pmul(s0, [pow(r0[0], -1, p)], p), f, p)[1]


# ---- univariate polynomials over Q (Fractions) and Z ----
def qadd(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def qneg(a):
    return [-c for c in a]


def qmul(a, b):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return trim(r)


def qdivmod(a, f):
    """Division by a monic f; exact over Z when a is integral."""
    a = trim(a)
    q = [0] * max(len(a) - len(f) + 1, 0)
    while len(a) >= len(f) and a:
        c = a[-1]
        k = len(a) - len(f)
        q[k] = c
        a = trim([a[i] - (c * f[i - k] if k <= i < k + len(f) else 0) for i in range(len(a))])
    return trim(q), a


def qinv(d, f):
    """Inverse of d modulo f over Q, or None."""
    r0, r1, s0, s1 = [Fraction(c) for c in f], [Fraction(c) for c in qdivmod(d, f)[1]], [], [Fraction(1)]
    while r1:
        lc = r1[-1]
        q, r = [], list(r0)
        q = [Fraction(0)] * max(len(r) - len(r1) + 1, 0)
        while len(r) >= len(r1) and r:
            c = r[-1] / lc
            k = len(r) - len(r1)
            q[k] = c
            r = trim([r[i] - (c * r1[i - k] if k <= i < k + len(r1) else 0) for i in range(len(r))])
        r0, r1, s0, s1 = r1, r, s1, qadd(s0, qneg(qmul(trim(q), s1)))
    if len(r0) != 1:
        return None
    return qdivmod([c / r0[0] for c in s0], f)[1]


def lcm(a, b):
    return a * b // gcd(a, b)


def den_lcm(poly):
    out = 1
    for c in poly:
        out = lcm(out, Fraction(c).denominator)
    return out


def factor_over(c, primes):
    """Exponents of c over `primes`, or None when c has another prime factor."""
    es = []
    for s in primes:
        e = 0
        while c % s == 0:
            c //= s
            e += 1
        es.append(e)
    return es if c == 1 else None


def prime_factors(c):
    out, d = [], 2
    while d * d <= c:
        if c % d == 0:
            out.append(d)
            while c % d == 0:
                c //= d
        d += 1
    if c > 1:
        out.append(c)
    return out


def parse_uni(s, var="a"):
    """Parse a polynomial in one variable ('a**2 + 3', '-a - 1', '2*a^3', 'a/3') into Fractions."""
    s = s.replace(" ", "").replace("**", "^")
    if s in ("", "0"):
        return []
    if not re.fullmatch(r"[0-9a-z^*/+-]+", s):
        raise Refuse(f"unparsed polynomial {s!r}")
    out = []
    for t in re.findall(r"[+-]?[^+-]+", s):
        sign = -1 if t.startswith("-") else 1
        coef, deg = Fraction(1), 0
        body, _, den = t.lstrip("+-").partition("/")
        if den:
            if not den.isdigit() or int(den) == 0:
                raise Refuse(f"unparsed denominator in {s!r}")
            coef /= int(den)
        for f in body.split("*"):
            if f == var:
                deg += 1
            elif f.startswith(var + "^"):
                deg += int(f[len(var) + 1:])
            elif f.isdigit():
                coef *= int(f)
            else:
                raise Refuse(f"unparsed factor {f!r} in {s!r}")
        n = max(len(out), deg + 1)
        out = [(out[i] if i < len(out) else 0) for i in range(n)]
        out[deg] += sign * coef
    return trim(out)


def int_poly(a, what):
    if any(Fraction(c).denominator != 1 for c in a):
        raise Refuse(f"{what} has non-integer coefficients")
    return [int(c) for c in a]


def eval_terms(s):
    """Encoder polynomial string ('x5*y6 - 2*y5^2', ...) as (sign*coef, [(var, exp)]) terms."""
    s = s.replace(" ", "")
    if not re.fullmatch(r"[0-9a-z^*+-]+", s):
        raise Refuse(f"unparsed system polynomial {s!r}")
    out = []
    for t in re.findall(r"[+-]?[^+-]+", s):
        sign = -1 if t.startswith("-") else 1
        coef, facs = sign, []
        for fac in t.lstrip("+-").split("*"):
            name, _, e = fac.partition("^")
            e = int(e) if e else 1
            if name.isdigit():
                coef *= int(name) ** e
            else:
                facs.append((name, e))
        out.append((coef, facs))
    return out


def eval_multi(s, image, f, p):
    """Evaluate at image[var] in F_p[a]/(f)."""
    total = []
    for coef, facs in eval_terms(s):
        val = [coef % p]
        for name, e in facs:
            if name not in image:
                raise Refuse(f"system variable {name!r} not in the map")
            for _ in range(e):
                val = pdivmod(pmul(val, image[name], p), f, p)[1]
        total = padd(total, val, p)
    return pdivmod(total, f, p)[1]


def eval_multi_q(s, image, f):
    """Evaluate at image[var] in Q[a]/(f)."""
    total = []
    for coef, facs in eval_terms(s):
        val = [Fraction(coef)]
        for name, e in facs:
            if name not in image:
                raise Refuse(f"system variable {name!r} not in the map")
            for _ in range(e):
                val = qdivmod(qmul(val, image[name]), f)[1]
        total = qadd(total, val)
    return qdivmod(total, f)[1]


def is_prime(p):
    return isinstance(p, int) and not isinstance(p, bool) and p >= 2 and \
        all(p % d for d in range(2, int(p ** 0.5) + 1))


def san(s):
    return re.sub(r"[^A-Za-z0-9]", "_", s)


def lst(a):
    return "[" + ", ".join(map(str, a)) + "]"


def zig(z):
    return 2 * z if z >= 0 else -2 * z - 1


def base_enc(digits, b):
    return sum(d * b ** k for k, d in enumerate(digits))


# ---- campaign ----
class Custody(Exception):
    """A support's receipt reference is malformed, or its file is missing or does not match its SHA-256."""


def load_receipt_ref(camp, support):
    """The receipt of a support filed by reference (`gp submit` since 2026-10-10: `receipt_ref`
    {"path": "receipts/<sha256>.json", "sha256": ...}), read from the campaign and checked against the
    recorded SHA-256, as `gp` checks it on every command. Anything else raises Custody."""
    ref = support.get("receipt_ref")
    rel = ref.get("path") if isinstance(ref, dict) else None
    digest = ref.get("sha256") if isinstance(ref, dict) else None
    label = support.get("label")
    if not (isinstance(rel, str) and isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest)) or \
            "\\" in rel or ":" in rel or rel.startswith("/") or ".." in rel.split("/"):
        raise Custody(f"support {label} has a malformed receipt reference")
    path = Path(camp) / rel
    if not path.is_file():
        raise Custody(f"receipt file {rel} of support {label} is missing")
    data = path.read_bytes()
    if sha(data) != digest:
        raise Custody(f"receipt file {rel} of support {label} does not match its recorded SHA-256 {digest[:12]}")
    return json.loads(data.decode("utf-8"))


def load_ledger(camp):
    """The ledger's claims and accepted supports by key (a later support supersedes an earlier one).
    A support filed by reference gets its checked receipt as `receipt`; inline supports are unchanged."""
    raw = (camp / "ledger.jsonl").read_bytes()
    claims, sup = {}, {}
    for line in raw.decode("utf-8").splitlines():
        if not line.strip():
            continue
        d = json.loads(line)
        if d["op"] == "claim":
            claims[d["key"]] = d
        elif d["op"] == "support":
            sup[d["key"]] = d
    for k, d in sup.items():
        if "receipt_ref" in d:
            sup[k] = dict(d, receipt=load_receipt_ref(camp, d))
    return raw, claims, sup


def load_encoder(path):
    spec = importlib.util.spec_from_file_location("gp_encode_matroid", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def classify(key, claims, sup):
    """The emitter class of a supported claim, or raise Refuse."""
    c, r = claims[key], sup[key]["receipt"]
    rule, cert = r.get("rule", {}).get("type"), r.get("certificate", {}).get("type")
    sc = set(c["scope"])
    if c.get("kind") == "EMPTY":
        raise Deferred("deferred (reprioritised 2026-10-09): EMPTY by ideal certificate needs frame "
                       "normalization (GPBinding.Matroid.frame_iff bridged to RealizesRank3)")
    if rule == "map":
        return "map-p" if sc == {"characteristic"} else "map-s"
    if cert == "point":
        return "point-p" if sc == {"characteristic"} else "point-s"
    if rule == "bridge":
        return "bridge"
    if cert == "proper_coefficient":
        return "source"
    raise Refuse(f"no emitter class for kind {c.get('kind')} with rule {rule} / certificate {cert}")


def check_scope(c):
    """Return ('p', p), ('s', S) or ('0', None) for the claim's scope."""
    sc = c["scope"]
    if set(sc) == {"characteristic"}:
        p = sc["characteristic"]
        if not is_prime(p):
            raise Refuse(f"characteristic {p!r} is not prime (the statement would be vacuous)")
        return "p", p
    if set(sc) == {"outside"}:
        S = sc["outside"]
        if not isinstance(S, list) or not all(is_prime(s) for s in S) or len(set(S)) != len(S):
            raise Refuse(f"excluded set {S!r} is not a list of distinct primes")
        return "s", S
    if sc == {"char0": True}:
        return "0", None
    raise Refuse(f"scope {sc} is not one characteristic, outside S, or characteristic 0")


_ENC = {}  # (encoder, matroid path) -> (json, encoding, error); the encoder is deterministic


def frame_of(c, camp, encoder):
    """Encoder checks shared by the matroid classes; returns the matroid data and frame columns."""
    mpath = camp / "matroids" / f"{c['matroid']}.json"
    if not c.get("matroid") or not mpath.is_file():
        raise Refuse(f"matroid file for {c.get('matroid')!r} not found")
    ck = (id(encoder), str(mpath))
    if ck not in _ENC:
        mjson = json.loads(mpath.read_bytes().decode("utf-8"))
        try:
            _ENC[ck] = (mjson, encoder.encode(mjson), None)
        except ValueError as e:
            _ENC[ck] = (mjson, None, str(e))
    mjson, enc, err = _ENC[ck]
    if err is not None:
        raise Refuse(f"encoder rejects the matroid: {err}")
    if mjson["name"] != c["matroid"]:
        raise Refuse(f"matroid file names {mjson['name']!r}, claim names {c['matroid']!r}")
    if c["inputs"] != [f"encoding:{enc['digest']}"]:
        raise Refuse("encoder output does not reproduce the claim's encoding digest")
    sysc = c["system"]
    if (sysc["variables"] != enc["variables"] or sysc["equations"] != enc["equations"]
            or sysc["nonzero"] != enc["nonzero"]):
        raise Refuse("claim system differs from the encoder's output")
    els = enc["matroid"]["elements"]
    n = len(els)
    idx = {e: i for i, e in enumerate(els)}
    lines = [sorted(idx[e] for e in l) for l in enc["matroid"]["lines"]]
    on = lambda t: any(all(x in l for x in t) for l in lines)
    triples = list(itertools.combinations(range(n), 3))
    for i, j in itertools.combinations(range(n), 2):
        if all(on(tuple(sorted((i, j, k)))) for k in range(n) if k not in (i, j)):
            raise Refuse(f"pair {els[i]},{els[j]} lies in no independent triple: not simple rank 3")
    if any(len(l) < 3 for l in lines) or any(len(set(a) & set(b)) > 1 for a, b in itertools.combinations(lines, 2)):
        raise Refuse("lines are not those of a simple rank-3 matroid")
    base = next((t for t in triples if not on(t)), None)
    if base is None:
        raise Refuse("no basis: rank below 3")
    fourth = next((j for j in range(n) if j not in base and
                   not any(on(tuple(sorted(pr + (j,)))) for pr in itertools.combinations(base, 2))), None)
    frame = {base[0]: [[1], [], []], base[1]: [[], [1], []], base[2]: [[], [], [1]]}
    if fourth is not None:
        frame[fourth] = [[1], [1], [1]]
    if [els[j] for j in list(base) + ([fourth] if fourth is not None else [])] != enc["frame"]:
        raise Refuse(f"reconstructed frame differs from the encoder's {enc['frame']}")
    free = [j for j in range(n) if j not in frame]
    want = [f"{ch}{j + 1}" for j in free for ch in "xyz"]
    if enc["variables"] != want:
        raise Refuse("encoder variables are not the free columns in order")
    return dict(matroid=c["matroid"], n=n, els=els, lines=lines, on=on, triples=triples, frame=frame,
                free=free, vars=want, system=sysc, encoding=enc["digest"])


def columns(m, image):
    return [m["frame"][j] if j in m["frame"] else [image[f"{ch}{j + 1}"] for ch in "xyz"] for j in range(m["n"])]


def det_parts(col, t, mul, add):
    a, b, c = t
    P = add(add(mul(col[a][0], mul(col[b][1], col[c][2])), mul(col[a][1], mul(col[b][2], col[c][0]))),
            mul(col[a][2], mul(col[b][0], col[c][1])))
    N = add(add(mul(col[a][0], mul(col[b][2], col[c][1])), mul(col[a][1], mul(col[b][0], col[c][2]))),
            mul(col[a][2], mul(col[b][1], col[c][0])))
    return P, N


def modp_data(m, vecs, f, p):
    """Certificates for GPCert.certOk (part 1): per triple (g, q) over F_p."""
    vecs = [[md(e, p) for e in col] for col in vecs]
    fm = md(f, p)
    certs = []
    for t in m["triples"]:
        P, N = det_parts(vecs, t, lambda x, y: pmul(x, y, p), lambda x, y: padd(x, y, p))
        D = psub(P, N, p)
        if m["on"](t):
            q, rem = pdivmod(D, fm, p)
            if rem:
                raise Refuse(f"on-line triple {[m['els'][i] for i in t]} has nonzero determinant")
            certs.append(([], q))
        else:
            g = pinv(D, fm, p)
            if g is None:
                raise Refuse(f"off-line triple {[m['els'][i] for i in t]} has a non-unit determinant")
            q, rem = pdivmod(psub(pmul(g, D, p), [1], p), fm, p)
            assert rem == []
            certs.append((g, q))
    return vecs, certs


def z_data(m, vecs_q, f, S):
    """Certificates for GPCert.certOkZ: integer columns, per triple (g, q) with g det = U + q f.
    S is the excluded prime list, or None for characteristic 0 (then S = primes of U)."""
    vecs = []
    for col in vecs_q:
        d = 1
        for e in col:
            d = lcm(d, den_lcm(e))
        vecs.append([[int(c * d) for c in e] for e in col])
    raw = []
    for t in m["triples"]:
        P, N = det_parts(vecs, t, qmul, qadd)
        D = qadd(P, qneg(N))
        if m["on"](t):
            q, rem = qdivmod(D, f)
            if rem:
                raise Refuse(f"on-line triple {[m['els'][i] for i in t]} has nonzero determinant")
            raw.append((None, [], q))
        else:
            g0 = qinv(D, f)
            if g0 is None:
                raise Refuse(f"off-line triple {[m['els'][i] for i in t]} has a non-invertible determinant")
            c0 = den_lcm(g0)
            g1 = [int(x * c0) for x in g0]
            q1, rem = qdivmod(qadd(qmul(g1, D), [-c0]), f)
            assert rem == []
            if S is not None and factor_over(c0, S) is None:
                raise Refuse(f"off-line triple {[m['els'][i] for i in t]} is not a unit outside {S}")
            raw.append((c0, g1, q1))
    U = 1
    for c0, _, _ in raw:
        if c0 is not None:
            U = lcm(U, c0)
    Sl = sorted(prime_factors(U)) if S is None else list(S)
    es = factor_over(U, Sl)
    assert es is not None
    certs = []
    for c0, g1, q1 in raw:
        k = 1 if c0 is None else U // c0
        certs.append(([k * x for x in g1], [int(k * x) for x in q1]))
    return vecs, certs, Sl, es, U


def source_poly(c, p_or_none):
    ss = c["system"]
    if ss["variables"] != ["a"] or len(ss["equations"]) != 1 or ss.get("nonzero"):
        raise Refuse("source system is not one equation in `a`")
    f = parse_uni(ss["equations"][0])
    f = int_poly(f, "source polynomial")
    if len(f) < 2 or f[-1] != 1:
        raise Refuse(f"source polynomial {ss['equations'][0]!r} is not monic of degree >= 1")
    return f


def check_cert_chars(certs, kind, val):
    for cert in certs:
        ch = cert.get("characteristic")
        if kind == "p" and ch != val:
            raise Refuse(f"receipt certificate at characteristic {ch}, claim at {val}")
        if kind != "p" and ch is not None:
            raise Refuse(f"receipt certificate at characteristic {ch}, claim scope is not one characteristic")


def point_record(key, claims, sup, camp, encoder):
    """Fidelity and data for a NONEMPTY point claim (used by point and bridge classes)."""
    c, r = claims[key], sup[key]["receipt"]
    if c.get("kind") != "NONEMPTY" or c.get("target") is not None:
        raise Refuse(f"kind/target {c.get('kind')}/{c.get('target')} is not NONEMPTY")
    kind, val = check_scope(c)
    cert = r.get("certificate", {})
    if cert.get("type") != "point":
        raise Refuse("receipt certificate is not a point")
    check_cert_chars([cert], kind, val)
    m = frame_of(c, camp, encoder)
    pt = cert.get("point", {})
    if set(pt) != set(m["vars"]):
        raise Refuse("point variables differ from the system's")
    image = {}
    for v, s in sorted(pt.items()):
        image[v] = int_poly(parse_uni(s, var="#"), f"point coordinate {v}")
    if kind == "p":
        p = val
        imp = {v: md(e, p) for v, e in image.items()}
        for e in m["system"]["equations"]:
            if eval_multi(e, imp, [0, 1], p):
                raise Refuse(f"equation {e!r} does not vanish at the point")
        for g in m["system"]["nonzero"]:
            if not eval_multi(g, imp, [0, 1], p):
                raise Refuse(f"guard {g!r} vanishes at the point")
        vecs, certs = modp_data(m, columns(m, imp), [0, 1], p)
        data = dict(route="modp", p=p, f=[0, 1], vecs=vecs, certs=certs)
    else:
        imq = {v: [Fraction(x) for x in e] for v, e in image.items()}
        for e in m["system"]["equations"]:
            if eval_multi_q(e, imq, [0, 1]):
                raise Refuse(f"equation {e!r} does not vanish at the point")
        for g in m["system"]["nonzero"]:
            gv = eval_multi_q(g, imq, [0, 1])
            if not gv or (kind == "s" and factor_over(abs(int(gv[0])), val) is None):
                raise Refuse(f"guard {g!r} is not a unit at the point in scope")
        vecs, certs, Sl, es, U = z_data(m, columns(m, imq), [0, 1], val if kind == "s" else None)
        data = dict(route="z", f=[0, 1], vecs=vecs, certs=certs, Sl=Sl, es=es)
    return c, kind, val, m, data


def build(key, cls, claims, sup, camp, encoder):
    """Return the claim's emission record, or raise Refuse with the reason."""
    c, s = claims[key], sup[key]
    r = s["receipt"]
    digest = s.get("receipt_sha256", s["receipt_ref"]["sha256"]) if "receipt_ref" in s else s.get("receipt_sha256")
    x = dict(key=key, label=c["label"], cls=cls, receipt_sha256=digest, source_key=None)
    if cls in ("map-p", "map-s"):
        if c.get("kind") != "NOT_IN_IDEAL" or c.get("target") != "1":
            raise Refuse(f"kind/target {c.get('kind')}/{c.get('target')} is not NOT_IN_IDEAL(1)")
        kind, val = check_scope(c)
        if (cls == "map-p") != (kind == "p") or kind == "0":
            raise Refuse(f"scope {c['scope']} does not match class {cls}")
        rule = r["rule"]
        if rule.get("type") != "map":
            raise Refuse("receipt rule is not map")
        check_cert_chars(rule.get("guard_certificates", []) + rule.get("eq_certificates", []), kind, val)
        prem = r.get("premises", [])
        if len(prem) != 1 or prem[0] not in claims:
            raise Refuse(f"map receipt premises {prem} are not one ledger claim")
        src = claims[prem[0]]
        if src.get("kind") != "NOT_IN_IDEAL" or src.get("target") != "1" or src.get("matroid") is not None:
            raise Refuse("source premise is not a NOT_IN_IDEAL(1) source system")
        if kind == "p" and src["scope"] != {"characteristic": val}:
            raise Refuse(f"source scope {src['scope']} differs from the claim's")
        if kind == "s" and not (set(src["scope"]) == {"outside"} and set(src["scope"]["outside"]) <= set(val)):
            raise Refuse(f"source scope {src['scope']} does not cover the claim's")
        f = source_poly(src, val)
        m = frame_of(c, camp, encoder)
        mp = rule.get("map", {})
        if set(mp) != set(m["vars"]):
            raise Refuse("map variables differ from the system's")
        x["source_key"] = prem[0]
        if kind == "p":
            p = val
            image = {v: pdivmod(md(int_poly(parse_uni(t), f"map image {v}"), p), f, p)[1]
                     for v, t in sorted(mp.items())}
            for e in m["system"]["equations"]:
                if eval_multi(e, image, f, p):
                    raise Refuse(f"equation {e!r} does not vanish at the map image")
            for g in m["system"]["nonzero"]:
                if pinv(eval_multi(g, image, f, p), f, p) is None:
                    raise Refuse(f"guard {g!r} is not a unit at the map image")
            vecs, certs = modp_data(m, columns(m, image), f, p)
            data = dict(route="modp", p=p, f=f, vecs=vecs, certs=certs)
        else:
            image = {v: qdivmod(parse_uni(t), f)[1] for v, t in sorted(mp.items())}
            for e in m["system"]["equations"]:
                if eval_multi_q(e, image, f):
                    raise Refuse(f"equation {e!r} does not vanish at the map image")
            for g in m["system"]["nonzero"]:
                if qinv(eval_multi_q(g, image, f), f) is None:
                    raise Refuse(f"guard {g!r} is not invertible at the map image")
            vecs, certs, Sl, es, U = z_data(m, columns(m, image), f, val)
            data = dict(route="z", f=f, vecs=vecs, certs=certs, Sl=Sl, es=es)
        x.update(m=m, kind=kind, val=val, data=data, algclosed=True, point=False)
    elif cls in ("point-p", "point-s"):
        c2, kind, val, m, data = point_record(key, claims, sup, camp, encoder)
        if (cls == "point-p") != (kind == "p"):
            raise Refuse(f"scope {c['scope']} does not match class {cls}")
        x.update(m=m, kind=kind, val=val, data=data, algclosed=False, point=True)
    elif cls == "bridge":
        if c.get("kind") != "NOT_IN_IDEAL" or c.get("target") != "1" or c.get("matroid") is None:
            raise Refuse("bridge claim is not a matroid NOT_IN_IDEAL(1)")
        if r.get("rule") != {"type": "bridge"}:
            raise Refuse("bridge receipt carries unexpected fields")
        prem = r.get("premises", [])
        if len(prem) != 1 or prem[0] not in claims or prem[0] not in sup:
            raise Refuse(f"bridge premises {prem} are not one supported ledger claim")
        pc = claims[prem[0]]
        for fld in ("matroid", "inputs", "system", "scope"):
            if pc.get(fld) != c.get(fld):
                raise Refuse(f"bridge premise differs from the claim in {fld}")
        _, kind, val, m, data = point_record(prem[0], claims, sup, camp, encoder)
        x["source_key"] = prem[0]
        x.update(m=m, kind=kind, val=val, data=data, algclosed=True, point=True)
    elif cls == "source":
        if c.get("kind") != "NOT_IN_IDEAL" or c.get("target") != "1" or c.get("matroid") is not None:
            raise Refuse("source claim is not a NOT_IN_IDEAL(1) source system")
        kind, val = check_scope(c)
        cert = r.get("certificate", {})
        if cert.get("type") != "proper_coefficient":
            raise Refuse("receipt certificate is not proper_coefficient")
        check_cert_chars([cert], kind, val)
        x.update(m=None, kind=kind, val=val, f=source_poly(c, val), algclosed=True, point=False)
    else:
        raise Refuse(f"unknown class {cls}")
    if x.get("m"):
        x.update(matroid=x["m"]["matroid"], encoding=x["m"]["encoding"])
    else:
        x.update(matroid=None, encoding=None)
    return x


# ---- Lean text ----
HEADER = '''import Mathlib

/-!
GP 3P map-rule claims, shard {shard} (ledger keys {keys}). Each is NOT_IN_IDEAL(1) of the framed
realization system over a characteristic p, stated in Mathlib vocabulary: the matroid is realizable
over every algebraically closed field of characteristic p. Generated by {emitter}.
-/

/-- `v` realizes the simple rank-3 matroid with these lines over `K`: three elements `a < b < c`
have linearly independent vectors exactly when no line contains all three. -/
def RealizesRank3 {{K : Type*}} [Field K] {{n : ℕ}} (lines : List (Finset (Fin n)))
    (v : Fin n → Fin 3 → K) : Prop :=
  ∀ a b c : Fin n, a < b → b < c →
    (LinearIndependent K ![v a, v b, v c] ↔ ¬ ∃ l ∈ lines, a ∈ l ∧ b ∈ l ∧ c ∈ l)
'''
REALIZES = HEADER[HEADER.index("/-- `v` realizes"):].replace("{{", "{").replace("}}", "}")
MEANING = {
    "map-s": "Each is NOT_IN_IDEAL(1) of the framed\nrealization system at every characteristic "
             "outside a finite set S of primes (0 included), stated in\nMathlib vocabulary: the matroid "
             "is realizable over every algebraically closed field K with\n`ringChar K ∉ S`.",
    "point-p": "Each is NONEMPTY of the framed realization\nsystem over a characteristic p, by a point in "
               "the prime field, stated in Mathlib vocabulary: the\nmatroid is realizable over every "
               "field of characteristic p.",
    "point-s": "Each is NONEMPTY of the framed realization\nsystem outside a finite set S of primes (or "
               "at characteristic 0), by an integer point, stated in\nMathlib vocabulary: the matroid is "
               "realizable over every field K with `ringChar K ∉ S` (or `CharZero K`).",
    "bridge": "Each is NOT_IN_IDEAL(1) of the framed realization\nsystem in its scope, by the bridge rule "
              "from a NONEMPTY point claim, stated in Mathlib vocabulary:\nthe matroid is realizable over "
              "every algebraically closed field in scope.",
    "source": "Each is NOT_IN_IDEAL(1) of a one-variable source\nsystem `f(a) = 0`, stated in Mathlib "
              "vocabulary: `f` has a root in every algebraically closed field\nin scope.",
}
TITLE = {"map-s": "map-rule claims outside S", "point-p": "point claims at p",
         "point-s": "point claims outside S", "bridge": "bridge claims", "source": "source claims"}


def header(cls, sid, keys):
    h = HEADER.format(shard=sid, keys=keys, emitter=EMITTER)
    if cls == "map-p":
        return h
    old = ("GP 3P map-rule claims, shard {shard} (ledger keys {keys}). Each is NOT_IN_IDEAL(1) of the framed\n"
           "realization system over a characteristic p, stated in Mathlib vocabulary: the matroid is realizable\n"
           "over every algebraically closed field of characteristic p.").format(shard=sid, keys=keys)
    new = f"GP 3P {TITLE[cls]}, shard {sid} (ledger keys {keys}). {MEANING[cls]}"
    assert old in h
    return h.replace(old, new)


def lines_def(m):
    ls = ", ".join("{" + ", ".join(map(str, l)) + "}" for l in m["lines"])
    return (f"/-- The lines of matroid `{m['matroid']}` on `0, …, {m['n'] - 1}` "
            f"(campaign elements {', '.join(m['els'])}). -/\n"
            f"def lines_{san(m['matroid'])} : List (Finset (Fin {m['n']})) :=\n  [{ls}]")


def binders(x):
    kind, val = x["kind"], x["val"]
    ac = "[IsAlgClosed K] " if x["algclosed"] else ""
    if kind == "p":
        return f"{ac}[CharP K {val}]"
    if kind == "s":
        return f"{ac}(hK : ringChar K ∉ ({lst(val)} : List ℕ))"
    return f"{ac}[CharZero K]"


def poly_text(f, v="a"):
    parts = []
    for d, c in reversed(list(enumerate(f))):
        if c == 0:
            continue
        mono = "" if d == 0 else (v if d == 1 else f"{v} ^ {d}")
        body = str(abs(c)) if d == 0 else (mono if abs(c) == 1 else f"{abs(c)} * {mono}")
        parts.append((c < 0, body))
    s = ("-" if parts[0][0] else "") + parts[0][1]
    for neg, body in parts[1:]:
        s += (" - " if neg else " + ") + body
    return s


def statement(x):
    if x["cls"] == "source":
        return (f"theorem {x['thm']} (K : Type*) [Field K] {binders(x)} :\n"
                f"    ∃ a : K, {poly_text(x['f'])} = 0")
    m = x["m"]
    return (f"theorem {x['thm']} (K : Type*) [Field K] {binders(x)} :\n"
            f"    ∃ v : Fin {m['n']} → Fin 3 → K, RealizesRank3 lines_{san(m['matroid'])} v")


def doc(x):
    kind, val = x["kind"], x["val"]
    sc = f"characteristic {val}" if kind == "p" else (f"outside {lst(val)}" if kind == "s" else "characteristic 0")
    return f"/-- Ledger key {x['key']} (`{x['label']}`), {sc}. -/\n"


def hk(x):
    return {"s": " hK", "0": " (by simp [ringChar.eq_zero])", "p": ""}[x["kind"]]


def solution_block(x):
    if x["cls"] == "source":
        return (f"{doc(x)}{statement(x)} := by\n"
                f"  obtain ⟨r, hr⟩ := GPCert.exists_rootZ (K := K) {lst(x['f'][:-1])} (by simp)\n"
                f"  refine ⟨r, ?_⟩\n"
                f"  simp only [List.cons_append, List.nil_append, GPCert.evZ] at hr\n"
                f"  push_cast at hr\n"
                f"  linear_combination hr\n")
    d, m = x["data"], x["m"]
    ns = f"W{x['key']}"
    lname = f"lines_{san(m['matroid'])}"
    ln = ", ".join(lst(l) for l in m["lines"])
    vecs, certs = d["vecs"], d["certs"]
    if d["route"] == "modp":
        p = d["p"]
        fl = [c % p for c in d["f"]][:-1]
        enc = lambda poly: sum(c * p ** k for k, c in enumerate(poly))
        vecsN = [enc(e) for cv in vecs for e in cv]
        dg = max([len(g) for g, _ in certs] + [1])
        dq = max([len(q) for _, q in certs] + [1])
        D = max([len(e) for cv in vecs for e in cv] + [dg, dq]) + 1
        B = p ** dg
        M = B * p ** dq
        S = sum((enc(g) + B * enc(q)) * M ** k for k, (g, q) in enumerate(certs))
        col, dc = f"(GPCert.colOf {p} {D} {{v}})", f"(GPCert.certOf {p} {D} {B})"
        flt = "[0]" if x["point"] else "fl"
        defs = "" if x["point"] else f"noncomputable def fl : List ℕ := {lst(fl)}\n"
        ok = f"GPCert.certOk {lname} linesN {p} {flt} {col.format(v='vecsN')} {dc} {M} L S = true"
        if x["point"]:
            proof = (f"GPCert.realizes_of_certOk_X {lname} {ns}.linesN {p} {col.format(v=ns + '.vecsN')} "
                     f"{dc} {M} {ns}.L {ns}.S {ns}.ok K")
        else:
            proof = (f"GPCert.realizes_of_certOk {lname} {ns}.linesN {p} {ns}.fl {col.format(v=ns + '.vecsN')} "
                     f"{dc} {M} {ns}.L {ns}.S {ns}.ok K")
        if x["cls"] == "map-p":  # the first run's exact text
            return f'''namespace {ns}
noncomputable def linesN : List (List ℕ) := [{ln}]
noncomputable def fl : List ℕ := {lst(fl)}
noncomputable def vecsN : List ℕ := {lst(vecsN)}
noncomputable def L : List ℕ := {lst(range(m['n']))}
noncomputable def S : ℕ := {S}
theorem ok : GPCert.certOk {lname} linesN {p} fl (GPCert.colOf {p} {D} vecsN) (GPCert.certOf {p} {D} {B}) {M} L S = true := by decide +kernel
end {ns}

{doc(x)}{statement(x)} :=
  GPCert.realizes_of_certOk {lname} {ns}.linesN {p} {ns}.fl (GPCert.colOf {p} {D} {ns}.vecsN) (GPCert.certOf {p} {D} {B}) {M} {ns}.L {ns}.S {ns}.ok K
'''
    else:
        B1 = max([zig(c) for cv in vecs for e in cv for c in e] + [1]) + 1
        D1 = max([len(e) for cv in vecs for e in cv] + [1]) + 1
        vecsN = [base_enc([zig(c) for c in e], B1) for cv in vecs for e in cv]
        B2 = max([zig(c) for g, q in certs for c in g + q] + [1]) + 1
        dg = max([len(g) for g, _ in certs] + [1])
        dq = max([len(q) for _, q in certs] + [1])
        G = B2 ** dg
        M = G * B2 ** dq
        D2 = max(dg, dq) + 1
        S = sum((base_enc([zig(c) for c in g], B2) + G * base_enc([zig(c) for c in q], B2)) * M ** k
                for k, (g, q) in enumerate(certs))
        Sl, es = lst(d["Sl"]), lst(d["es"])
        col, dc = f"(GPCert.colOfZ {B1} {D1} {{v}})", f"(GPCert.certOfZ {B2} {D2} {G})"
        flt = "[0]" if x["point"] else "fl"
        defs = "" if x["point"] else f"noncomputable def fl : List ℤ := {lst(d['f'][:-1])}\n"
        ok = f"GPCert.certOkZ {lname} linesN {Sl} {es} {flt} {col.format(v='vecsN')} {dc} {M} L S = true"
        if x["point"]:
            proof = (f"GPCert.realizesZ_of_certOk_X {lname} {ns}.linesN {Sl} {es} {col.format(v=ns + '.vecsN')} "
                     f"{dc} {M} {ns}.L {ns}.S {ns}.ok K{hk(x)}")
        else:
            proof = (f"GPCert.realizesZ_of_certOk {lname} {ns}.linesN {Sl} {es} {ns}.fl "
                     f"{col.format(v=ns + '.vecsN')} {dc} {M} {ns}.L {ns}.S {ns}.ok K{hk(x)}")
    return f'''namespace {ns}
noncomputable def linesN : List (List ℕ) := [{ln}]
{defs}noncomputable def vecsN : List ℕ := {lst(vecsN)}
noncomputable def L : List ℕ := {lst(range(m['n']))}
noncomputable def S : ℕ := {S}
theorem ok : {ok} := by decide +kernel
end {ns}

{doc(x)}{statement(x)} :=
  {proof}
'''


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    data = text.encode("utf-8")
    path.write_bytes(data)
    return sha(data)


def main(argv=None):
    here = Path(__file__).resolve().parent
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--campaign", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--shard-size", type=int, default=64)
    ap.add_argument("--encoder", type=Path, default=here / "encode-matroid.py")
    ap.add_argument("--prelude", type=Path, default=here / "comparator-prelude.lean")
    ap.add_argument("--root", default="GPComparator")
    ap.add_argument("--manifest", type=Path, help="manifest path (default <out>/MANIFEST.json)")
    ap.add_argument("--clean", action="store_true", help="remove earlier <root>/ and comparator/ outputs")
    args = ap.parse_args(argv)
    if not re.fullmatch(r"[A-Z][A-Za-z0-9]*", args.root) or args.shard_size < 1:
        ap.error("bad --root or --shard-size")
    for d in (args.out / args.root, args.out / "comparator"):
        if d.exists():
            if not args.clean:
                ap.error(f"{d} exists (use --clean)")
            shutil.rmtree(d)

    try:
        raw, claims, sup = load_ledger(args.campaign)
    except Custody as e:
        print(f"refused (receipt custody): {e}", file=sys.stderr)
        return 2
    encoder = load_encoder(args.encoder)
    prelude = args.prelude.read_bytes().decode("utf-8")
    if PART2 not in prelude:
        ap.error("prelude has no part 2 marker")
    prelude1 = prelude[:prelude.index(PART2)]

    emitted, refused, deferred = [], [], []
    for k in sorted(sup):
        try:
            cls = classify(k, claims, sup)
            emitted.append(build(k, cls, claims, sup, args.campaign, encoder))
        except Deferred as e:
            deferred.append({"key": k, "label": claims[k]["label"], "class": "empty", "reason": str(e)})
        except Refuse as e:
            refused.append({"key": k, "label": claims[k]["label"], "class": None, "reason": str(e)})
            try:
                refused[-1]["class"] = classify(k, claims, sup)
            except Refuse:
                refused[-1]["class"] = "empty" if claims[k].get("kind") == "EMPTY" else "none"
    for x in emitted:
        x["thm"] = ("root_" if x["cls"] == "source" else "realizable_") + san(x["label"])
    for field, what in (("thm", "theorem name"), ("matroid", "matroid identifier")):
        seen = {}
        for x in emitted:
            if x[field] is not None:
                seen.setdefault(san(x[field]), set()).add(x[field])
        bad = {s for s, v in seen.items() if len(v) > 1}
        for x in [x for x in emitted if x[field] is not None and san(x[field]) in bad]:
            refused.append({"key": x["key"], "label": x["label"], "class": x["cls"],
                            "reason": f"{what} collides after sanitizing"})
        emitted = [x for x in emitted if x[field] is None or san(x[field]) not in bad]
    refused.sort(key=lambda r: r["key"])

    shards, manifest_claims = [], []
    for cls, prefix in CLASSES.items():
        xs_all = [x for x in emitted if x["cls"] == cls]
        for si in range(0, len(xs_all), args.shard_size):
            xs = xs_all[si:si + args.shard_size]
            sid = f"{prefix}{si // args.shard_size:03d}"
            head = header(cls, sid, ", ".join(str(x["key"]) for x in xs))
            defs, seen = [], set()
            for x in xs:
                if x["matroid"] is not None and x["matroid"] not in seen:
                    seen.add(x["matroid"])
                    defs.append(lines_def(x["m"]))
            prefix_text = head + "\n" + "".join(d + "\n\n" for d in defs) + ("" if defs else "")
            if not defs:
                prefix_text = head + "\n"
            chal = prefix_text + "\n".join(doc(x) + statement(x) + " := by\n  sorry\n" for x in xs)
            pre = prelude1 if cls == "map-p" else prelude
            sol = prefix_text + pre.rstrip("\n") + "\n\n" + "\n".join(solution_block(x) for x in xs)
            mod = f"{args.root}.{sid}"
            cfg = {"challenge_module": f"{mod}.Challenge", "solution_module": f"{mod}.Solution",
                   "theorem_names": [x["thm"] for x in xs], "permitted_axioms": AXIOMS}
            base = args.out / args.root / sid
            h_c = write(base / "Challenge.lean", chal)
            h_s = write(base / "Solution.lean", sol)
            h_j = write(args.out / "comparator" / f"{sid.lower()}.json", json.dumps(cfg, indent=1) + "\n")
            shards.append({"shard": sid, "class": cls, "claims": len(xs),
                           "challenge": f"{args.root}/{sid}/Challenge.lean", "challenge_sha256": h_c,
                           "solution": f"{args.root}/{sid}/Solution.lean", "solution_sha256": h_s,
                           "config": f"comparator/{sid.lower()}.json", "config_sha256": h_j})
            for x in xs:
                stmt_text = (lines_def(x["m"]) + "\n\n" if x["m"] else "") + statement(x) + "\n"
                scope = {"p": {"characteristic": x["val"]}, "s": {"outside": x["val"]},
                         "0": {"char0": True}}[x["kind"]]
                manifest_claims.append({"key": x["key"], "label": x["label"], "class": cls,
                                        "matroid": x["matroid"], "scope": scope, "shard": sid,
                                        "theorem": x["thm"], "statement_sha256": sha(stmt_text.encode("utf-8")),
                                        "encoding": x["encoding"], "premise_key": x["source_key"],
                                        "receipt_sha256": x["receipt_sha256"]})
    realizes = REALIZES
    per_class = {}
    for cls in list(CLASSES) + ["empty", "none"]:
        e = sum(1 for x in manifest_claims if x["class"] == cls)
        rf = sum(1 for r in refused if r["class"] == cls)
        df = sum(1 for r in deferred if r["class"] == cls)
        if e or rf or df:
            per_class[cls] = {"emitted": e, "refused": rf, "deferred": df}
    total = len(claims)
    manifest = {
        "schema": EMITTER, "shard_size": args.shard_size, "root": args.root, "permitted_axioms": AXIOMS,
        "inputs": {"ledger_sha256": sha(raw), "encoder_sha256": sha(args.encoder.read_bytes()),
                   "prelude_sha256": sha(args.prelude.read_bytes()),
                   "realizes_def_sha256": sha(realizes.encode("utf-8"))},
        "counts": {LEDGER_TOTAL_KEY: total, "supported": len(sup), "unsupported": total - len(sup),
                   "emitted": len(manifest_claims), "refused": len(refused), "deferred": len(deferred),
                   "shards": len(shards),
                   "coverage_percent": round(100 * len(manifest_claims) / total, 2)},
        "classes": per_class,
        "unsupported": [{"key": k, "label": claims[k]["label"]} for k in sorted(claims) if k not in sup],
        "refused": refused, "deferred": deferred, "shards": shards, "claims": manifest_claims}
    mpath = args.manifest or (args.out / "MANIFEST.json")
    write(mpath, json.dumps(manifest, indent=1, ensure_ascii=False, sort_keys=True) + "\n")
    print(f"{len(manifest_claims)} of {total} claims emitted ({manifest['counts']['coverage_percent']}%) "
          f"in {len(shards)} shards; {len(refused)} refused; {len(deferred)} deferred; {total - len(sup)} unsupported")
    for cls, v in per_class.items():
        print(f"  {cls}: {v['emitted']} emitted, {v['refused']} refused, {v['deferred']} deferred")
    reasons = {}
    for r in refused:
        reasons.setdefault((r["class"], r["reason"]), []).append(r["key"])
    for (cls, why), ks in sorted(reasons.items(), key=lambda kv: str(kv[0])):
        print(f"  refused [{cls}] x{len(ks)}: {why} (keys {', '.join(map(str, ks[:8]))}{'…' if len(ks) > 8 else ''})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
