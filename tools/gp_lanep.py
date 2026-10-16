"""Lane P (GP 0.52, P1): Lean-proposition claims with premises as scope. Loaded by tools/gp.py.

A P campaign's campaign.json says {"profile": "P", "package": "lean", "roots": ["<lib root>", ...]}; its Lake
package (at the binding's pin) holds the statements, each a `def X : Prop`. Ledger ops (gp-ledger/v1; readers older
than 0.52 skip them, so P claims are invisible to them):

  register   code k -> declaration, closure hash and environment stamp (or a prose text hash, never holdable)
  pclaim     a claim (statement code, premise codes) with an optional lean_theorem or weakening support
  discharge  a claim derived by the discharge rule from (s, S u {h}) and (h, T), T a subset of S
  pwarrant   a recorded-only warrant: exact_script (4), hand_proof (5; complete|sketch), numerical (6), external
  fidelity   unaudited < LLM-audited < human-audited < anchored, attached to a code
  present    a presentation of a claim in a venue with a tag; views mark it OVERSTATED
  bind       the binder report for the package's source tree, stored content-addressed under binds/
  pwithdraw  a permanent withdrawal of a P claim (all sixteen warrant slots are retracted)

Every held verdict comes from the Kernel fold in `gp_ledgerp` (`GPProfile.LaneP.fold_held_meaningP`); the binder
`gp_bindp` elaborates nothing (docs/private/LANEP-DESIGN.md).
"""
import json
import os
from pathlib import Path
import subprocess
import time

G = None  # the gp module's globals, injected by tools/gp.py

CLAIM_OPS = ("pclaim", "discharge")
TIER_NAMES = {1: "comparator receipt", 2: "lean theorem", 3: "profile replay", 4: "exact script", 5: "hand proof",
              6: "numerical", 7: "conjecture"}
TAGS = {"COMPARATOR": 1, "LEAN": 2, "REPLAY": 3, "CERT": 4, "SCRIPT": 4, "HAND": 5, "NUMERICAL": 6, "PROBE": 6,
        "CONJECTURE": 7, "OPEN": 7}
FIDELITY = ["unaudited", "LLM-audited", "human-audited", "anchored"]
RECORDED = {"hand_proof": 5, "exact_script": 4, "numerical": 6, "external": None}
PACKAGE_FILES = ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain")
BUILD_TIMEOUT = int(os.environ.get("GP_LANEP_BUILD_TIMEOUT", "3600"))  # wall-clock cap on `lake build`, seconds
BELOW_NORMAL = getattr(subprocess, "BELOW_NORMAL_PRIORITY_CLASS", 0)


def exe(name):
    return G.PROFILE / (f".lake/build/bin/{name}" + (".exe" if os.name == "nt" else ""))


def refusal(what, fix, rule="lane P", scope="-"):
    return G.Refusal(what, rule, scope, fix)


# --- the ledger's P records -------------------------------------------------------------------

def is_p(ledger):
    return isinstance(ledger.statement, dict) and ledger.statement.get("profile") == "P"


def registers(ledger):
    return [r for r in ledger.records if r["op"] == "register"]


def code_by_name(ledger):
    return {r["name"]: r for r in registers(ledger)}


def code_by_id(ledger):
    return {r["code"]: r for r in registers(ledger)}


def code_ref(ledger, name, what="statement"):
    r = code_by_name(ledger).get(name)
    if r is None:
        raise refusal(f"no registered {what} {name!r}", f"register it first with `gp register` (or --prose TEXT --as {name})")
    return r


def name_of(ledger, code):
    r = code_by_id(ledger).get(code)
    return r["name"] if r else f"code {code}"


def pclaims(ledger):
    return [r for r in ledger.records if r["op"] in CLAIM_OPS]


def pclaim(ledger, label):
    for r in pclaims(ledger):
        if r["label"] == label:
            return r
    raise refusal(f"no P claim labelled {label!r}", "file it first with `gp claim --lean` or `gp claim --prose`", "ledger")


def by_key(ledger):
    return {c["key"]: c for c in pclaims(ledger)}


def pwarrants(ledger, key):
    return [r for r in ledger.records if r["op"] == "pwarrant" and r.get("key") == key]


def presentations(ledger, key):
    return sorted((r for r in ledger.records if r["op"] == "present" and r.get("key") == key), key=G.content)


def pwithdrawals(ledger):
    out = {}
    for r in ledger.records:
        if r["op"] == "pwithdraw" and type(r.get("key")) is int:
            out.setdefault(r["key"], r)
    return out


def fidelity_of(ledger):
    """The effective fidelity record per code: the latest (by time, then content), so both merge orders agree."""
    out = {}
    for r in ledger.records:
        if r["op"] == "fidelity":
            k = r["code"]
            if k not in out or (r.get("at", ""), G.content(r)) > (out[k].get("at", ""), G.content(out[k])):
                out[k] = r
    return out


def fidelity_text(r):
    if r is None:
        return "unaudited"
    return "anchored (asserted)" if r["level"] == "anchored" else r["level"]


def conditions(ledger, key):
    return sorted({h for w in pwarrants(ledger, key) for h in w.get("conditions", [])})


def new_code(ledger, body):
    used = {r["code"] for r in registers(ledger)}
    text = json.dumps(body, ensure_ascii=False, sort_keys=True)
    salt = 0
    while True:
        k = G.KEY_BASE + int(G.sha(f"code|{text}#{salt}".encode("utf-8")), 16) % G.KEY_SPACE
        if k not in used:
            return k
        salt += 1


def new_pkey(ledger, body):
    used = {c["key"] for c in pclaims(ledger)}
    text = json.dumps(body, ensure_ascii=False, sort_keys=True)
    salt = 0
    while True:
        k = G.KEY_BASE + int(G.sha(f"{text}#{salt}".encode("utf-8")), 16) % G.KEY_SPACE
        if k not in used:
            return k
        salt += 1


# --- the campaign package -----------------------------------------------------------------------

def package(ledger):
    return ledger.dir / ledger.statement.get("package", "lean")


def roots(ledger):
    rs = ledger.statement.get("roots")
    if not rs:
        raise refusal("campaign.json names no library roots", 'add "roots": ["<Lib>"] to campaign.json and restate')
    return rs


def package_sources(pkg, rs):
    files = [pkg / f for f in PACKAGE_FILES if (pkg / f).exists()]
    for r in rs:
        if (pkg / f"{r}.lean").exists():
            files.append(pkg / f"{r}.lean")
        files += sorted((pkg / r).rglob("*.lean")) if (pkg / r).is_dir() else []
    return files


def modules(pkg, rs):
    out = []
    for f in package_sources(pkg, rs):
        if f.suffix == ".lean":
            out.append(".".join(f.relative_to(pkg).with_suffix("").parts))
    return sorted(set(out))


def tree_sha(ledger):
    pkg = package(ledger)
    if not pkg.is_dir():
        raise refusal(f"the campaign package {pkg} is missing", "restore it, or set \"package\" in campaign.json")
    return G.tree_identity(package_sources(pkg, roots(ledger)), base=pkg)


def theorem_id(decl, stmt, premises):
    return f"{decl}|{stmt}|{','.join(str(p) for p in premises)}"


def bind_input(ledger, extra_codes=(), extra_theorems=()):
    regs = registers(ledger) + list(extra_codes)
    cs = {}
    for r in regs:
        if r["kind"] == "lean":
            cs[r["code"]] = {"code": r["code"], "kind": "lean", "decl": r["decl"]}
        elif r["kind"] == "not":
            cs[r["code"]] = {"code": r["code"], "kind": "not", "of": r["of"]}
    ths = {}
    for c in pclaims(ledger):
        s = c.get("support") or {}
        if s.get("kind") == "theorem":
            t = {"decl": s["decl"], "stmt": c["stmt"], "premises": c["premises"]}
            ths[theorem_id(**t)] = t
    for t in extra_theorems:
        ths[theorem_id(**t)] = t
    if not cs and not ths:
        return None  # prose only: nothing to bind, and no package is needed
    return {"roots": roots(ledger), "imports": modules(package(ledger), roots(ledger)),
            "codes": [cs[k] for k in sorted(cs)], "theorems": [dict(ths[i], id=i) for i in sorted(ths)]}


def stamp_of(pkg, lean, githash):
    """The environment stamp: toolchain and every manifest revision (pinned dependencies, design §1)."""
    manifest = json.loads((pkg / "lake-manifest.json").read_text(encoding="utf-8"))
    pk = sorted((p["name"], p.get("rev") or p.get("type", "")) for p in manifest.get("packages", []))
    toolchain = (pkg / "lean-toolchain").read_text(encoding="utf-8").strip()
    return G.sha(json.dumps({"lean": lean, "githash": githash, "toolchain": toolchain, "packages": pk},
                            sort_keys=True).encode("utf-8"))


def closure_hash(closure):
    return G.sha("".join(f"{h}  {n}\n" for n, h in sorted(closure.items())).encode("utf-8"))


def bind_records(ledger):
    return [r for r in ledger.records if r["op"] == "bind"]


def load_report(ledger, rec):
    data = ledger.receipt_file({"label": "bind", "receipt_ref": rec["report"]})
    return json.loads(data.decode("utf-8"))


def toolchain_env(pkg):
    pin = (G.PROFILE / "lean-toolchain").read_text(encoding="utf-8").strip()
    mine = (pkg / "lean-toolchain").read_text(encoding="utf-8").strip() if (pkg / "lean-toolchain").exists() else None
    if mine != pin:
        raise refusal(f"the campaign package is pinned to {mine}, not the binding's {pin}",
                      f"pin {pkg / 'lean-toolchain'} to {pin} (design review note 1: campaigns stay on the binding pin)")
    toolchain, lake = G.toolchain_lake()
    return dict(os.environ, PATH=str(toolchain / "bin") + os.pathsep + os.environ["PATH"]), lake


def run_capped(cmd, cwd, env, timeout):
    p = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         creationflags=BELOW_NORMAL)
    try:
        out, err = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        p.kill()
        p.communicate()
        return None, b"", b""
    return p.returncode, out, err


def ensure_exe(name):
    path = exe(name)
    if G.stale(path):
        G.lake_build(name, path)
    return path


def run_binder(ledger, inp, tree, key, persist=True):
    """`lake build` the package (BelowNormal, wall-clock capped), then `lake env gp_bindp` over it. The report is
    stored as receipts/<sha256>.json and recorded by a `bind` op; a timeout is recorded as an attempt."""
    pkg = package(ledger).resolve()
    binder = ensure_exe("gp_bindp").resolve()
    env, lake = toolchain_env(pkg)
    t0 = time.time()
    rc, out, err = run_capped([str(lake), "build"], pkg, env, BUILD_TIMEOUT)
    if rc is None:
        if persist:
            ledger.append({"op": "pattempt", "status": "timeout", "tree_sha256": tree, "cap_seconds": BUILD_TIMEOUT})
        raise refusal(f"lake build of the campaign package exceeded {BUILD_TIMEOUT} s (recorded as attempt timeout)",
                      "make the slow proof cheaper; nothing elaborated under the cap is trusted", "lake build")
    if rc != 0:
        text = (out + b"\n" + err).decode("utf-8", "replace").replace("\r\n", "\n")
        tail = [line for line in text.splitlines() if line.strip()][-G.BUILD_TAIL:]
        raise G.Refusal(f"the campaign package does not build (lake build exited {rc})", "lake build", "-",
                        f"fix the package; run `lake build` in {pkg} for the full message",
                        detail=["lake's last lines:"] + ["  " + line for line in tail])
    t1 = time.time()
    tmp = (ledger.dir / ".gp-bind-input.json").resolve()  # lake env runs in the package directory
    tmp.write_bytes(json.dumps(inp, sort_keys=True).encode("utf-8"))
    try:
        rc, out, err = run_capped([str(lake), "env", str(binder), str(tmp)], pkg, env, BUILD_TIMEOUT)
    finally:
        tmp.unlink(missing_ok=True)
    if rc != 0:
        raise refusal(f"the P binder failed: {(err or b'').decode('utf-8', 'replace').strip()[-400:]}",
                      "report this to the builder", "gp_bindp")
    raw = json.loads(out.decode("utf-8"))
    t2 = time.time()
    stamp = stamp_of(pkg, raw["lean"], raw["githash"])
    codes = {}
    for row in raw["codes"]:
        entry = {k: row[k] for k in ("found", "prop") if k in row}
        if "closure" in row:
            entry["closure"] = {n: G.sha(t.encode("utf-8")) for n, t in row["closure"]}
            entry["hash"] = closure_hash(entry["closure"])
        codes[str(row["code"])] = entry
    report = {"schema": "gp-bindp-report/v1", "key": key, "tree_sha256": tree, "stamp": stamp, "lean": raw["lean"],
              "githash": raw["githash"], "codes": codes, "theorems": {r["id"]: r for r in raw["theorems"]}}
    if persist:
        ref = ledger.store_receipt(report)  # receipts/<sha256>.json: content-addressed, checked on every read
        ledger.append({"op": "bind", "key": key, "tree_sha256": tree, "stamp": stamp, "report": ref,
                       "seconds": {"build": round(t1 - t0, 1), "bind": round(t2 - t1, 1)}})
    report["_seconds"] = {"build": round(t1 - t0, 1), "bind": round(t2 - t1, 1)}
    return report


def current_report(ledger, extra_codes=(), extra_theorems=(), persist=True):
    """The binder report for the package as it is now and these inputs: a recorded bind whose key matches (its
    stored report checked against its SHA-256), else a fresh bind. Every view binds, so drift is always seen."""
    inp = bind_input(ledger, extra_codes, extra_theorems)
    if inp is None:
        return {"schema": "gp-bindp-report/v1", "key": "none", "tree_sha256": None, "stamp": "none", "codes": {},
                "theorems": {}}
    tree = tree_sha(ledger)
    key = G.sha((tree + json.dumps(inp, sort_keys=True)).encode("utf-8"))
    for r in bind_records(ledger):
        if r.get("key") == key:
            return load_report(ledger, r)
    return run_binder(ledger, inp, tree, key, persist)


def current_of(report, regs, code):
    """A code's current (hash, stamp) in this bind, or None: missing, not a Prop, or prose."""
    r = regs.get(code)
    if r is None:
        return None
    if r["kind"] == "lean":
        e = report["codes"].get(str(code)) or {}
        return (e["hash"], report["stamp"]) if e.get("found") and e.get("prop") and "hash" in e else None
    if r["kind"] == "not":
        inner = current_of(report, regs, r["of"])
        return ("not:" + inner[0], inner[1]) if inner else None
    return None


def drift(ledger, report, code):
    """Why a Lean code is not fresh, naming the changed constants; None when fresh (prose: None)."""
    regs = code_by_id(ledger)
    r = regs.get(code)
    if r is None or r["kind"] == "prose":
        return None
    if r["kind"] == "not":
        return drift(ledger, report, r["of"])
    e = report["codes"].get(str(code)) or {}
    if not e.get("found"):
        return f"{r['decl']} is missing from the package (renamed or deleted)"
    if not e.get("prop"):
        return f"{r['decl']} is no longer a campaign-local Prop"
    if report["stamp"] != r["stamp"]:
        return f"the environment stamp changed since {r['name']} was registered (toolchain or a pinned dependency)"
    if e["hash"] != r["hash"]:
        old, new = r.get("closure", {}), e.get("closure", {})
        changed = sorted(n for n in set(old) | set(new) if old.get(n) != new.get(n))
        return f"{r['name']} was redefined: changed {', '.join(changed) or 'its closure'}"
    return None


def theorem_verdict(row):
    if row is None:
        return "not bound yet"
    if not row.get("found"):
        return "the theorem is missing from the package"
    if not row.get("axiomsOk"):
        bad = [a for a in row.get("axioms", []) if a not in ("propext", "Quot.sound", "Classical.choice")]
        return f"axiom audit: uses {', '.join(bad)}"
    if row.get("kernel") != "ok":
        return f"the kernel refused its type: {row.get('kernel', '').splitlines()[0]}"
    return "ok"


# --- the fold -------------------------------------------------------------------------------------

def recorded_tier(w):
    """The tier a recorded-only warrant shows (0: none). Never a hold: the Kernel gets it as a citation."""
    kind = w.get("kind")
    if kind == "hand_proof":
        return 5 if w.get("state") == "complete" else 0
    if kind == "external":
        return w["tier"] if w.get("tier") in (1, 2, 3) else 0
    return RECORDED.get(kind) or 0


def plan(ledger, report):
    regs = code_by_id(ledger)
    fid = fidelity_of(ledger)
    codes = [{"code": k, "hash": r["hash"], "stamp": r["stamp"],
              "current": (lambda cur: {"hash": cur[0], "stamp": cur[1]} if cur else None)(current_of(report, regs, k)),
              "fidelity": FIDELITY.index(fid[k]["level"]) if k in fid else 0} for k, r in sorted(regs.items())]
    records, claims = {}, []
    for c in pclaims(ledger):
        s = c.get("support") or None
        sup = None
        if s and s["kind"] == "theorem":
            sup = {"kind": "theorem", "decl": s["decl"]}
            tid = theorem_id(s["decl"], c["stmt"], c["premises"])
            row = report["theorems"].get(tid)
            records[tid] = {"declaration": s["decl"], "stmt": c["stmt"], "premises": c["premises"],
                            "ok": theorem_verdict(row) == "ok"}
        elif s and s["kind"] == "discharge":
            sup = {"kind": "discharge", "from": s["from"], "by": s["by"]}
        elif s and s["kind"] == "weaken":
            sup = {"kind": "weaken", "from": s["from"]}
        claims.append({"key": c["key"], "stmt": c["stmt"], "scope": sorted(set(c["premises"])),
                       "conditions": conditions(ledger, c["key"]), "support": sup,
                       "recorded": [{"tier": recorded_tier(w), "digest": w.get("sha256") or G.sha(G.content(w).encode())}
                                    for w in pwarrants(ledger, c["key"])],
                       "presentations": [{"tier": TAGS[p["tag"]], "premises": p.get("premises", [])}
                                         for p in presentations(ledger, c["key"])]})
    return {"codes": codes, "records": [records[k] for k in sorted(records)], "claims": claims,
            "withdrawn": sorted(pwithdrawals(ledger))}


def run_runner(p):
    path = ensure_exe("gp_ledgerp")
    tmp = Path(os.environ.get("TEMP") or os.environ.get("TMPDIR") or "/tmp") / f"gp-ledgerp-{os.getpid()}.json"
    tmp.write_bytes(json.dumps(p, sort_keys=True).encode("utf-8"))
    try:
        out = subprocess.run([str(path), "run", str(tmp)], capture_output=True, text=True, encoding="utf-8")
    finally:
        tmp.unlink(missing_ok=True)
    if out.returncode != 0:
        raise RuntimeError(out.stderr.strip() or "gp_ledgerp failed")
    return json.loads(out.stdout)


class State:
    """One P fold: the binder report, the runner's items by key and the frontier."""

    def __init__(self, ledger, report=None):
        self.ledger = ledger
        self.report = report if report is not None else current_report(ledger)
        out = run_runner(plan(ledger, self.report))
        if out.get("error") or out.get("elaboration"):
            raise refusal(f"the P ledger does not fold: {out.get('error') or out.get('elaboration')}",
                          "find the record it names; restore the ledger from its branch", "ledger fold")
        self.items = {i["key"]: i for i in out["items"]}
        self.frontier = out["frontier"]
        self.claims = by_key(ledger)
        self.withdrawn = pwithdrawals(ledger)

    def held(self, key):
        return self.items[key]["held"]


def state(ledger, report=None):
    return State(ledger, report)


# --- views ---------------------------------------------------------------------------------------

def names(ledger, codes):
    return ", ".join(sorted(name_of(ledger, k) for k in codes))


def stmt_text(ledger, c):
    s = name_of(ledger, c["stmt"])
    return s + (f" under {names(ledger, c['premises'])}" if c["premises"] else "")


def unbound_why(st, c):
    reasons = [d for d in (drift(st.ledger, st.report, k) for k in [c["stmt"]] + c["premises"]) if d]
    return "; ".join(dict.fromkeys(reasons))


def recorded_text(w):
    if w["kind"] == "hand_proof":
        return f"hand proof ({w.get('state', 'sketch')})"
    if w["kind"] == "external":
        return f"external tier {w.get('tier')} ({w.get('what', 'recorded')})"
    return TIER_NAMES[RECORDED[w["kind"]]] if RECORDED.get(w["kind"]) else f"unknown kind {w['kind']!r} (earns nothing)"


def best_step(st, key, seen=()):
    """The weakest step on the best path to `key`, as (tier, text), or None."""
    item, c = st.items[key], st.claims[key]
    if item["best"] is None:
        return None
    t = item["best"]
    s = c.get("support") or {}
    rec = [w for w in pwarrants(st.ledger, key) if recorded_tier(w) == t]
    if rec:
        return t, f"{c['label']}: {recorded_text(rec[0])}"
    if s.get("kind") == "theorem" and t == 2:
        return t, f"{c['label']}: lean theorem {s['decl']}"
    if s.get("kind") in ("discharge", "weaken") and key not in seen:
        subs = [best_step(st, k, seen + (key,)) for k in ([s["from"], s["by"]] if s["kind"] == "discharge" else [s["from"]])]
        subs = [x for x in subs if x]
        if subs:
            return max(subs)
    return t, c["label"]


def tier_text(st, key):
    item, c = st.items[key], st.claims[key]
    if item["held"]:
        return f"tier {item['tier']}" + (" (unreplayed)" if item["tier"] == 2 else "")
    parts = []
    if item["best"] is not None:
        step = best_step(st, key)
        via = f"; weakest step: {step[1]}" if step and (c.get("support") or {}).get("kind") in ("discharge", "weaken") else ""
        rec = [w for w in pwarrants(st.ledger, key) if recorded_tier(w) == item["best"]]
        what = (recorded_text(rec[0]) + ", recorded only") if rec else "not held"
        parts.append(f"best: tier {item['best']} ({what}{via})")
    else:
        sketches = [w for w in pwarrants(st.ledger, key) if recorded_tier(w) == 0]
        if sketches:
            parts.append(f"best: {recorded_text(sketches[0])}")
    s = c.get("support") or {}
    if s.get("kind") == "theorem" and not item["proofAccepted"]:
        row = st.report["theorems"].get(theorem_id(s["decl"], c["stmt"], c["premises"]))
        verdict = theorem_verdict(row)
        parts.append(f"theorem {s['decl']} refused: {verdict}" if verdict != "ok" else
                     f"theorem {s['decl']}: bound, statement not fresh")
    if s.get("kind") == "discharge":
        for k in (s["from"], s["by"]):
            if k in st.items and not st.items[k]["held"]:
                parts.append(f"rests on unheld {st.claims[k]['label']}")
    if s.get("kind") == "weaken" and s["from"] in st.items and not st.items[s["from"]]["held"]:
        parts.append(f"rests on unheld {st.claims[s['from']]['label']}")
    return "; ".join(parts) if parts else "no warrant"


def presented_text(st, key):
    item, ps = st.items[key], presentations(st.ledger, key)
    groups = {}
    for p, over in zip(ps, item["overstated"]):
        groups.setdefault(p["tag"], []).append(over)
    out = []
    for tag in sorted(groups, key=lambda t: (TAGS[t], t)):
        n, m = len(groups[tag]), sum(groups[tag])
        venues = f"{n} venue{'s' if n != 1 else ''}"
        out.append(f"presented [{tag}] in {venues}" + (": OVERSTATED" if m == n else f" ({m} OVERSTATED)" if m else ""))
    return out


def summary(st, key):
    """One claim's status line: state; tier or best; open premises; presentations; fidelity."""
    c, item = st.claims[key], st.items[key]
    if key in st.withdrawn:
        head = f"withdrawn {st.withdrawn[key].get('at', '-')}: {st.withdrawn[key].get('reason', '')}"
    elif item["held"]:
        head = "held"
    else:
        why = unbound_why(st, c)
        head = f"unbound ({why}; register a new code and refile the claim)" if why else "open"
    parts = [head] if key in st.withdrawn else [head, tier_text(st, key)]
    opened = sorted(set(c["premises"]) | set(conditions(st.ledger, key)))
    if opened:
        settled = {h: k for h, k in item["settled"]}
        parts.append("open: " + ", ".join(sorted(
            name_of(st.ledger, h) + (f" (dischargeable by {st.claims[settled[h]]['label']})" if h in settled else "")
            for h in opened)))
    parts += presented_text(st, key)
    fid = fidelity_of(st.ledger)
    lowest = min([c["stmt"]] + opened, key=lambda k: FIDELITY.index(fid[k]["level"]) if k in fid else 0)
    parts.append("fidelity: " + fidelity_text(fid.get(lowest)) + (f" ({name_of(st.ledger, lowest)})" if lowest != c["stmt"] else ""))
    return "; ".join(p for p in parts if p)


def cmd_status(ledger, args):
    st = state(ledger)
    cs = sorted(st.claims.values(), key=lambda c: c["label"])
    if not cs:
        print("no P claims")
    for c in cs:
        print(f"{c['label']}: {summary(st, c['key'])}")
    if cs:
        print("\nheld verdicts come from the Kernel fold; tier 2 shows as unreplayed until the lean4checker replay (P2)")


def cmd_explain(ledger, args):
    st = state(ledger)
    c = pclaim(ledger, args.label)
    print(f"{c['label']}: {summary(st, c['key'])}")
    print(f"  statement: {stmt_text(ledger, c)}")
    regs = code_by_id(ledger)
    for k in [c["stmt"]] + c["premises"]:
        r = regs[k]
        where = r.get("decl") or ("¬" + name_of(ledger, r["of"]) if r["kind"] == "not" else "prose")
        d = drift(ledger, st.report, k)
        print(f"    {r['name']}: {r['kind']} {where}, closure {r['hash'][:12]}" + (f"; NOT FRESH: {d}" if d else ""))
    weakest = best_step(st, c["key"])

    def walk(key, pad, seen):
        cc, item = st.claims[key], st.items[key]
        s = cc.get("support") or {}
        mark = "  <- weakest step" if weakest and weakest[1].startswith(cc["label"] + ":") else ""
        state_ = "held" if item["held"] else "not held"
        if s.get("kind") == "theorem":
            row = st.report["theorems"].get(theorem_id(s["decl"], cc["stmt"], cc["premises"]))
            axs = ", ".join((row or {}).get("axioms", [])) or "-"
            print(f"{pad}{cc['label']}: lean_theorem {s['decl']} [tier 2, {state_}]: {theorem_verdict(row)}; "
                  f"axioms {axs}{mark}")
        elif s.get("kind") == "discharge":
            print(f"{pad}{cc['label']}: discharge of {name_of(ledger, s['premise'])} [{state_}]")
            for k in (s["from"], s["by"]):
                if k not in seen:
                    walk(k, pad + "  ", seen | {k})
        elif s.get("kind") == "weaken":
            print(f"{pad}{cc['label']}: weakening [{state_}]")
            if s["from"] not in seen:
                walk(s["from"], pad + "  ", seen | {s["from"]})
        else:
            print(f"{pad}{cc['label']}: no holding warrant [{state_}]")
        for w in pwarrants(ledger, key):
            m = "  <- weakest step" if weakest and weakest[1] == f"{cc['label']}: {recorded_text(w)}" else ""
            cond = f"; conditions (OPEN): {names(ledger, w['conditions'])}" if w.get("conditions") else ""
            print(f"{pad}  recorded only: {recorded_text(w)} {w.get('locator', '')} sha256 {w.get('sha256', '-')[:12]}"
                  f"{cond}{m}")

    print("  warrant path:")
    walk(c["key"], "    ", {c["key"]})
    for p, over in zip(presentations(ledger, c["key"]), st.items[c["key"]]["overstated"]):
        stated = names(ledger, p.get("premises", [])) or "no premises"
        print(f"  presented in {p['venue']} as [{p['tag']}] stating {stated}" + (": OVERSTATED" if over else ""))


def cmd_frontier(ledger, args):
    st = state(ledger)
    print("open premises, by the claims they would unlock:")
    if not st.frontier:
        print("  none")
    for f in st.frontier:
        users = sorted(c["label"] for c in st.claims.values() if f["code"] in c["premises"] and c["key"] not in st.withdrawn)
        cands = sorted(c["label"] for c in st.claims.values() if c["stmt"] == f["code"] and c["key"] not in st.withdrawn)
        print(f"  {name_of(ledger, f['code'])}: {f['unlocks']} claim{'s' if f['unlocks'] != 1 else ''} "
              f"({', '.join(users)})" + (f"; claims of it: {', '.join(cands)}" if cands else "; no claim of it yet"))
    rows = []
    for c in sorted(st.claims.values(), key=lambda c: c["label"]):
        if st.items[c["key"]]["held"] or c["key"] in st.withdrawn:
            continue
        why = unbound_why(st, c)
        if why:
            rows.append(f"  {c['label']}: unbound: {why}; smallest fix: register a new code and refile the claim")
            continue
        s = c.get("support") or {}
        if s.get("kind") == "theorem" and not st.items[c["key"]]["proofAccepted"]:
            row = st.report["theorems"].get(theorem_id(s["decl"], c["stmt"], c["premises"]))
            rows.append(f"  {c['label']}: theorem {s['decl']}: {theorem_verdict(row)}; smallest fix: prove "
                        f"{stmt_text(ledger, c)} with the standard axioms only")
    if rows:
        print("open claims with a refused or unbound warrant:")
        print("\n".join(rows))


# --- filing ---------------------------------------------------------------------------------------

def parse_stmt(ledger, text):
    """A statement handle, or its negation written `¬X` or `not:X` (a derived code, registered on first use)."""
    neg = text.startswith("¬") or text.startswith("not:")
    base = text[1:] if text.startswith("¬") else text[4:] if neg else text
    r = code_ref(ledger, base)
    if not neg:
        return r, None
    name = "¬" + r["name"]
    have = code_by_name(ledger).get(name)
    if have:
        return have, None
    if r["kind"] == "prose":
        raise refusal(f"{base} is prose; only Lean statements have negation codes", "register the negation as prose")
    body = {"name": name, "kind": "not", "of": r["code"], "hash": "not:" + r["hash"], "stamp": r["stamp"]}
    return dict(body, code=new_code(ledger, {"name": name, "kind": "not", "of": r["code"]}), op="register"), body


def cmd_register(ledger, args):
    if args.prose is not None:
        name = args.as_ or args.decl
        if not name:
            raise refusal("a prose statement needs a name", "give --as NAME")
        if name in code_by_name(ledger):
            raise refusal(f"{name!r} is already registered", "choose a new name with --as")
        text = args.prose.strip()
        if not text:
            raise refusal("the prose text is empty", "give the statement's text")
        body = {"name": name, "kind": "prose", "text": text, "hash": G.sha(text.encode("utf-8")), "stamp": "prose"}
        code = new_code(ledger, {"name": name, "kind": "prose", "text": text})
        ledger.append(dict({"op": "register", "code": code}, **body))
        print(f"registered {name} (code {code}): prose, text {body['hash'][:12]}; never holdable")
        return
    if not args.decl:
        raise refusal("register needs a declaration", "gp register <Decl> [--as NAME], or --prose TEXT --as NAME")
    decl = args.decl
    name = args.as_ or decl.split(".")[-1]
    if name in code_by_name(ledger):
        raise refusal(f"{name!r} is already registered", "register under a new name with --as NAME")
    code = new_code(ledger, {"name": name, "kind": "lean", "decl": decl})
    report = current_report(ledger, extra_codes=[{"code": code, "kind": "lean", "decl": decl}])
    e = report["codes"].get(str(code)) or {}
    if not e.get("found"):
        raise refusal(f"{decl} is not a declaration of the campaign package", "check the name (fully qualified), then build")
    if not e.get("prop"):
        raise refusal(f"{decl} is not a campaign-local `def {decl.split('.')[-1]} : Prop` without universe parameters",
                      "state it as `def X : Prop := ...` in the package")
    for r in registers(ledger):
        if r.get("decl") == decl and r["hash"] == e["hash"] and r["stamp"] == report["stamp"]:
            raise refusal(f"{decl} is already registered as {r['name']} with this closure", f"use {r['name']}")
    body = {"name": name, "kind": "lean", "decl": decl, "hash": e["hash"], "closure": e["closure"],
            "stamp": report["stamp"]}
    ledger.append(dict({"op": "register", "code": code}, **body))
    print(f"registered {name} (code {code}): {decl}, closure {e['hash'][:12]} over {len(e['closure'])} local "
          f"constant{'s' if len(e['closure']) != 1 else ''}, stamp {report['stamp'][:12]}")


def premise_codes(ledger, premises):
    out = []
    for h in premises or []:
        r, body = parse_stmt(ledger, h)
        if body:
            ledger.append(r)
        if r["code"] in out:
            raise refusal(f"premise {h} is given twice", "give each premise once")
        out.append(r["code"])
    return out


def label_free(ledger, label):
    if any(c["label"] == label for c in pclaims(ledger)) or any(c["label"] == label for c in ledger.claims()):
        raise refusal(f"label {label!r} is taken", "choose a new label", "ledger")


def cmd_claim(ledger, args):
    label_free(ledger, args.label)
    if args.prose and args.lean:
        raise refusal("a claim has one statement", "give --lean X or --prose X")
    stmt_name = args.lean or args.prose
    r, body = parse_stmt(ledger, stmt_name)
    if args.lean and r["kind"] == "prose":
        raise refusal(f"{stmt_name} is a prose statement", f"file it with --prose {stmt_name}")
    if args.prose and r["kind"] != "prose":
        raise refusal(f"{stmt_name} is a Lean statement", f"file it with --lean {stmt_name}")
    if r["kind"] == "prose" and args.theorem:
        raise refusal(f"{stmt_name} is prose: prose statements are never holdable", "register a Lean statement")
    if body:
        ledger.append(r)
    premises = premise_codes(ledger, args.premise)
    regs = code_by_id(ledger)
    if args.theorem and any(regs[p]["kind"] == "prose" for p in premises):
        raise refusal("a lean_theorem cannot take a prose premise: the binder has no Lean type for it",
                      "register the premise as a Lean statement, or drop --theorem")
    support = None
    if args.theorem and args.from_:
        raise refusal("a claim has one holding warrant", "give --theorem T or --from L")
    if args.theorem:
        support = {"kind": "theorem", "decl": args.theorem}
    if args.from_:
        src = pclaim(ledger, args.from_)
        if src["stmt"] != r["code"] or not set(src["premises"]) <= set(premises):
            raise refusal(f"weakening needs the same statement and a larger scope than {args.from_}",
                          f"file --lean {name_of(ledger, src['stmt'])} with every premise of {args.from_}")
        support = {"kind": "weaken", "from": src["key"]}
    rec = {"label": args.label, "stmt": r["code"], "premises": premises, "support": support}
    key = new_pkey(ledger, rec)
    if support and support["kind"] == "theorem":
        current_report(ledger, extra_theorems=[{"decl": args.theorem, "stmt": r["code"], "premises": premises}])
    ledger.append(dict({"op": "pclaim", "key": key}, **rec))
    st = state(ledger)
    print(f"claim {args.label} (key {key}) filed: {stmt_text(ledger, rec)}; {summary(st, key)}")


def cmd_discharge(ledger, args):
    c = pclaim(ledger, args.label)
    by = pclaim(ledger, args.by)
    h = code_ref(ledger, args.premise, "premise")["code"] if not args.premise.startswith(("¬", "not:")) else \
        parse_stmt(ledger, args.premise)[0]["code"]
    if h not in c["premises"]:
        raise refusal(f"{args.premise} is not a premise of {args.label} ({stmt_text(ledger, c)})",
                      f"discharge one of: {names(ledger, c['premises']) or 'none (it has no premises)'}", "discharge")
    if by["stmt"] != h:
        raise refusal(f"statement mismatch: {args.by} is a claim of {name_of(ledger, by['stmt'])}, the premise is "
                      f"{args.premise} (code mismatch)", f"discharge with a claim whose statement is {args.premise}",
                      "discharge")
    rest = [p for p in c["premises"] if p != h]
    extra = [p for p in by["premises"] if p not in rest]
    if extra:
        raise refusal(f"{args.by} has premises the result would drop: {names(ledger, extra)}",
                      f"discharge those first, or keep them: weaken {args.label} to include them", "discharge")
    label = args.as_ or f"{args.label}~{name_of(ledger, h)}"
    label_free(ledger, label)
    rec = {"label": label, "stmt": c["stmt"], "premises": rest,
           "support": {"kind": "discharge", "from": c["key"], "by": by["key"], "premise": h}}
    key = new_pkey(ledger, rec)
    ledger.append(dict({"op": "discharge", "key": key}, **rec))
    st = state(ledger)
    print(f"claim {label} (key {key}) filed by discharging {args.premise} in {args.label} with {args.by}: "
          f"{stmt_text(ledger, rec)}; {summary(st, key)}")


def cmd_submit(ledger, args):
    c = pclaim(ledger, args.label)
    kinds = [(k, v) for k, v in (("hand_proof", args.hand_proof), ("exact_script", args.script),
                                  ("numerical", args.numerical), ("external", args.external)) if v]
    if len(kinds) != 1:
        raise refusal("a P submission is one of --hand-proof, --script, --numerical or --external", "give exactly one")
    kind, path = kinds[0]
    p = Path(path)
    if not p.is_file():
        raise refusal(f"cannot read {path}", "give the file the warrant records")
    try:
        rel = p.resolve().relative_to(ledger.dir.resolve()).as_posix()
    except ValueError:
        raise refusal(f"{path} is outside the campaign", "copy it into the campaign directory and submit that copy")
    rec = {"op": "pwarrant", "key": c["key"], "label": c["label"], "kind": kind, "locator": rel,
           "sha256": G.sha(p.read_bytes())}
    if kind == "hand_proof":
        if args.state not in ("complete", "sketch"):
            raise refusal("a hand proof declares its state", "give --state complete or --state sketch")
        rec["state"] = args.state
        rec["conditions"] = premise_codes(ledger, args.condition)
    elif kind == "external":
        if args.tier not in (1, 2, 3):
            raise refusal("an external warrant names the tier its own checker earned (1, 2 or 3)", "give --tier N")
        rec["tier"] = args.tier
        rec["what"] = args.what or "checked elsewhere"
    if args.state and kind != "hand_proof":
        raise refusal("--state is for hand proofs", "drop --state")
    ledger.append(rec)
    st = state(ledger)
    print(f"recorded only: {recorded_text(rec)} for {c['label']} ({rel}, sha256 {rec['sha256'][:12]}); it never "
          f"holds a claim; {summary(st, c['key'])}")


def cmd_fidelity(ledger, args):
    r, body = parse_stmt(ledger, args.name)
    if body:
        ledger.append(r)
    if args.level not in FIDELITY:
        raise refusal(f"unknown fidelity level {args.level}", f"one of {', '.join(FIDELITY)}")
    ledger.append({"op": "fidelity", "code": r["code"], "name": r["name"], "level": args.level, "by": args.by,
                   "ref": args.ref})
    note = " (asserted: P1 checks no anchor)" if args.level == "anchored" else ""
    print(f"fidelity of {r['name']}: {args.level}{note}, by {args.by}")


def cmd_present(ledger, args):
    c = pclaim(ledger, args.label)
    tag = args.tag.strip("[]").upper()
    if tag not in TAGS:
        raise refusal(f"unknown tag [{tag}]", f"one of {', '.join('[' + t + ']' for t in TAGS)}")
    rec = {"op": "present", "key": c["key"], "label": c["label"], "venue": args.venue, "tag": tag,
           "premises": premise_codes(ledger, args.premise), "locator": args.locator}
    ledger.append(rec)
    st = state(ledger)
    i = presentations(ledger, c["key"]).index(next(p for p in presentations(ledger, c["key"]) if G.content(p) == G.content(rec)))
    over = st.items[c["key"]]["overstated"][i]
    print(f"presentation of {c['label']} in {args.venue} as [{tag}] recorded" + (": OVERSTATED" if over else ""))


def cmd_bind(ledger, args):
    if args.replay:
        raise refusal("the lean4checker replay is Lane P phase 2", "use `gp bind`; tier 2 shows as unreplayed")
    before = {r.get("key") for r in bind_records(ledger)}
    report = current_report(ledger)
    if report["key"] == "none":
        print("nothing to bind: no Lean statement is registered")
        return
    fresh = report["key"] not in before
    sec = report.get("_seconds")
    print(f"bind {report['key'][:12]}: tree {report['tree_sha256'][:12]}, stamp {report['stamp'][:12]}" +
          (f", {sec['build']} s build + {sec['bind']} s binder" if fresh and sec else " (recorded bind reused)"))
    for r in registers(ledger):
        if r["kind"] == "prose":
            continue
        d = drift(ledger, report, r["code"])
        print(f"  {r['name']}: " + (f"NOT FRESH: {d}" if d else "fresh"))
    for tid, row in sorted(report["theorems"].items()):
        print(f"  theorem {tid.split('|')[0]}: {theorem_verdict(row)}")


def cmd_withdraw(ledger, args):
    c = pclaim(ledger, args.label)
    key = c["key"]
    if key in pwithdrawals(ledger):
        raise refusal(f"{args.label} is already withdrawn", "nothing to do: a withdrawal is permanent", "withdrawal")
    reason = (args.reason or "").strip()
    if not reason:
        raise refusal("a withdrawal needs a reason", 'give --reason "why the claim is withdrawn"', "withdrawal")
    record = {"op": "pwithdraw", "label": args.label, "key": key, "reason": reason}
    before = state(ledger)
    after = state(G.ledger_with(ledger, [record]), before.report)
    lost = [k for k in before.items if k != key and before.held(k) and not after.held(k)]
    if lost and not args.cascade:
        raise refusal(f"withdrawing {args.label} would un-hold {len(lost)} other held claim{'s' if len(lost) > 1 else ''}: "
                      + ", ".join(sorted(before.claims[k]["label"] for k in lost)),
                      "rerun with --cascade to withdraw it anyway", "withdrawal")
    ledger.append(record)
    print(f"withdrawn: {args.label} (key {key}): {reason}; " + ("was held" if before.held(key) else "was not held"))
    for k in sorted(lost, key=lambda k: before.claims[k]["label"]):
        s = before.claims[k].get("support") or {}
        print(f"  no longer held: {before.claims[k]['label']} ({s.get('kind', 'support')})")


def cmd_merge(ledger, args):
    """Land another branch's P records here if the merged ledger folds; the result depends only on the record set."""
    other = G.Ledger(args.other)
    if not other.records:
        raise G.merge_refusal(f"no ledger at {args.other}", "merge from a campaign directory with a ledger")
    other.check_schema()
    if other.bound_statement_sha() != ledger.bound_statement_sha():
        raise G.merge_refusal("the branches bind different versions of the campaign statement",
                              "restate on one branch so both bind the same statement, then merge again")
    have = {G.content(r) for r in ledger.records}
    new = [r for r in other.records if G.content(r) not in have and r["op"] not in ("init", "merge")]
    if not new:
        print("nothing to merge: every record of the other branch is already here")
        return
    merged = G.ledger_with(ledger, new)
    merged.receipt_dirs = [ledger.dir, other.dir]
    seen_code, seen_name, seen_key, seen_label = {}, {}, {}, {}
    for r in registers(merged):
        if seen_code.setdefault(r["code"], G.content(r)) != G.content(r) or \
                seen_name.setdefault(r["name"], r["code"]) != r["code"]:
            raise G.merge_refusal(f"the branches register {r['name']!r} (code {r['code']}) differently",
                                  "register under a new name on one branch")
    for c in pclaims(merged):
        if seen_key.setdefault(c["key"], G.content(c)) != G.content(c) or \
                seen_label.setdefault(c["label"], c["key"]) != c["key"]:
            raise G.merge_refusal(f"conflicting P claims under {c['label']!r} / key {c['key']}",
                                  "relabel one of them on its branch")
    if any(r["op"] in G.LIFECYCLE for r in merged.records):
        raise G.merge_refusal("the merged log carries raw retraction or supersession records",
                              "withdraw a claim with `gp withdraw`")
    for r in new:  # their receipt files (bind reports) land here, each checked against its SHA-256 first
        if r["op"] == "bind":
            ledger.copy_receipt({"label": "bind", "receipt_ref": r["report"]}, merged.receipt_file(
                {"label": "bind", "receipt_ref": r["report"]}))
    merged.receipt_dirs = [ledger.dir]
    state(merged, current_report(merged, persist=False))  # the merged ledger must fold; nothing is written
    with ledger.path.open("ab") as f:
        for r in new:
            f.write((json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n").encode("utf-8"))
    ledger.records += new
    ledger.append({"op": "merge", "records": len(new), "from_sha256": G.sha(other.path.read_bytes())})
    print(f"merged {len(new)} P records; the merged log folds")


COMMANDS = {"register": cmd_register, "claim": cmd_claim, "discharge": cmd_discharge, "submit": cmd_submit,
            "fidelity": cmd_fidelity, "present": cmd_present, "bind": cmd_bind, "status": cmd_status,
            "explain": cmd_explain, "frontier": cmd_frontier, "withdraw": cmd_withdraw, "merge": cmd_merge}
P_ONLY = ("register", "discharge", "fidelity", "present", "bind")
