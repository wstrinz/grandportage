"""Lane P (GP 0.52, P1 and P2): Lean-proposition claims with premises as scope. Loaded by tools/gp.py.

A P campaign's campaign.json says {"profile": "P", "package": "lean", "roots": ["<lib root>", ...]}; its Lake
package (at the binding's pin) holds the statements, each a `def X : Prop`. Ledger ops (gp-ledger/v1; readers older
than 0.52 skip them, so P claims are invisible to them):

  register   code k -> declaration, closure hash and environment stamp (or a prose text hash, never holdable; a
             prose code may be a process condition: review, merge, wording, fidelity-review); a bridge code (P2)
             is generated as the literal 3a/3b meaning of a claim of another campaign
  pclaim     a claim (statement code, premise codes, open process conditions) with an optional lean_theorem,
             weakening, Comparator (P2, tier 1) or bridge (P2, tier 3) support
  discharge  a claim derived by the discharge rule from (s, S u {h}) and (h, T), T a subset of S
  pwarrant   a recorded-only warrant: exact_script (4), hand_proof (5; complete|sketch), numerical (6), external;
             or a Comparator receipt (P2): held at the pinned revisions, recorded only at any other
  fidelity   unaudited < LLM-audited < human-audited < anchored, attached to a code
  present    a presentation of a claim in a venue with a tag; views mark it OVERSTATED
  bind       the binder report for the package's source tree, stored content-addressed under receipts/
  replay     a lean4checker replay of the package's modules (P2): tier 2 is final only after a passing replay
  pwithdraw  a permanent withdrawal of a P claim (all sixteen warrant slots are retracted)

Every held verdict comes from the Kernel fold in `gp_ledgerp` (`GPProfile.LaneP.fold_held_meaningP`); the binder
`gp_bindp` elaborates nothing (docs/private/LANEP-DESIGN.md).
"""
import json
import os
from pathlib import Path
import re
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
PROCESS = ("review", "merge", "wording", "fidelity-review")  # process conditions (P2): never OVERSTATED
CMP_DIR, BRIDGE_DIR = "GPComparator", "GPBridge"  # generated modules under the first library root (P2)
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
OKAY = b"Your solution is okay"


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


def is_process(ledger, code):
    r = code_by_id(ledger).get(code)
    return bool(r and r.get("process"))


def conditions(ledger, key):
    """A claim's open mathematical conditions: its hand proofs' reviewer conditions that are not process conditions."""
    return sorted({h for w in pwarrants(ledger, key) for h in w.get("conditions", []) if not is_process(ledger, h)})


def process_open(ledger, c, seen=()):
    """A claim's open process conditions (P2): its own, its hand proofs' reviewer conditions that are process
    conditions, and those of the claims a discharge or weakening rests on. They are shown; a presentation that leaves
    them out reads "conditions open", not OVERSTATED."""
    hand = {h for w in pwarrants(ledger, c["key"]) for h in w.get("conditions", []) if is_process(ledger, h)}
    out = hand | set(c.get("conditions", []))
    s = c.get("support") or {}
    keys = by_key(ledger) if s.get("kind") in ("discharge", "weaken") else {}
    for k in (s.get("from"), s.get("by")):
        if k in keys and k not in seen:
            out |= set(process_open(ledger, keys[k], seen + (c["key"],)))
    return sorted(out)


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


def is_generated(module, kind=CMP_DIR):
    return f".{kind}." in f".{module}."


def modules(pkg, rs):
    """The package's modules as the binder imports them: every module except emitted Comparator solutions, which
    declare their challenge's theorem name again."""
    out = []
    for f in package_sources(pkg, rs):
        if f.suffix == ".lean":
            m = ".".join(f.relative_to(pkg).with_suffix("").parts)
            if not (is_generated(m) and m.endswith(".Solution")):
                out.append(m)
    return sorted(set(out))


def tree_sha(ledger):
    pkg = package(ledger)
    if not pkg.is_dir():
        raise refusal(f"the campaign package {pkg} is missing", "restore it, or set \"package\" in campaign.json")
    return G.tree_identity(package_sources(pkg, roots(ledger)), base=pkg)


def theorem_id(decl, stmt, premises):
    return f"{decl}|{stmt}|{','.join(str(p) for p in premises)}"


def bind_input(ledger, extra_codes=(), extra_theorems=(), extra_challenges=()):
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
    chals = {}
    for c in pclaims(ledger):
        s = c.get("support") or {}
        if s.get("kind") == "comparator" and s.get("theorem"):
            chals[f"cmp|{c['key']}"] = {"decl": s["theorem"], "module": s["challenge"], "stmt": c["stmt"],
                                         "premises": c["premises"]}
    for ch in extra_challenges:
        chals[ch["id"]] = {k: v for k, v in ch.items() if k != "id"}
    bridges = {r["code"]: {"code": r["code"], "decl": r["decl"], "lit": r["bridge"]["lit"]} for r in regs
               if r["kind"] == "lean" and r.get("bridge")}
    if not cs and not ths:
        return None  # prose only: nothing to bind, and no package is needed
    out = {"roots": roots(ledger), "imports": modules(package(ledger), roots(ledger)),
           "codes": [cs[k] for k in sorted(cs)], "theorems": [dict(ths[i], id=i) for i in sorted(ths)]}
    if chals:  # P2 inputs only when used, so a P1 ledger's bind key (and its recorded bind) is unchanged
        out["challenges"] = [dict(chals[i], id=i) for i in sorted(chals)]
    if bridges:
        out["bridges"] = [bridges[k] for k in sorted(bridges)]
    return out


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
        entry = {k: row[k] for k in ("found", "prop", "module") if k in row}
        if "closure" in row:
            entry["closure"] = {n: G.sha(t.encode("utf-8")) for n, t in row["closure"]}
            entry["hash"] = closure_hash(entry["closure"])
        codes[str(row["code"])] = entry
    report = {"schema": "gp-bindp-report/v1", "key": key, "tree_sha256": tree, "stamp": stamp, "lean": raw["lean"],
              "githash": raw["githash"], "codes": codes, "theorems": {r["id"]: r for r in raw["theorems"]}}
    if raw.get("challenges"):
        report["challenges"] = {r["id"]: r for r in raw["challenges"]}
    if raw.get("bridges"):
        report["bridges"] = {str(r["code"]): r for r in raw["bridges"]}
    if persist:
        ref = ledger.store_receipt(report)  # receipts/<sha256>.json: content-addressed, checked on every read
        ledger.append({"op": "bind", "key": key, "tree_sha256": tree, "stamp": stamp, "report": ref,
                       "seconds": {"build": round(t1 - t0, 1), "bind": round(t2 - t1, 1)}})
    report["_seconds"] = {"build": round(t1 - t0, 1), "bind": round(t2 - t1, 1)}
    return report


def current_report(ledger, extra_codes=(), extra_theorems=(), persist=True, extra_challenges=()):
    """The binder report for the package as it is now and these inputs: a recorded bind whose key matches (its
    stored report checked against its SHA-256), else a fresh bind. Every view binds, so drift is always seen."""
    inp = bind_input(ledger, extra_codes, extra_theorems, extra_challenges)
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


def replay_of(ledger, report):
    """The lean4checker replay of exactly this bind's tree and stamp, or None (P2): a failed one if any failed (the
    kernel found a declaration it rejects), else a passing one. Independent of record order, so of merge order."""
    rs = [r for r in ledger.records if r["op"] == "replay" and r.get("tree_sha256") == report.get("tree_sha256")
          and r.get("stamp") == report.get("stamp")]
    return min(rs, key=lambda r: (r.get("ok") is True, G.content(r))) if rs else None


def theorem_verdict(row, replay=None):
    if replay is not None and replay.get("ok") is False:
        return "the lean4checker replay of this package failed (" + "; ".join(replay.get("detail") or ["-"])[:300] + ")"
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
    """The tier a recorded-only warrant shows (0: none). Never a hold: the Kernel gets it as a citation. A pinned
    Comparator receipt holds through its claim's support instead, so as a citation it shows nothing."""
    kind = w.get("kind")
    if kind == "hand_proof":
        return 5 if w.get("state") == "complete" else 0
    if kind == "comparator":
        return 0 if pinned(w) else 1
    if kind == "external":
        return w["tier"] if w.get("tier") in (1, 2, 3) else 0
    return RECORDED.get(kind) or 0


def comparator_pins():
    """The revisions a Comparator receipt must name to hold (decision 3): .github/workflows/comparator.yml's Comparator
    and lean4export pins, at the binding's toolchain. Receipts from any other pin are recorded only."""
    path = G.ROOT / ".github/workflows/comparator.yml"
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    pins = {}
    for k in ("COMPARATOR_REV", "LEAN4EXPORT_REV"):
        m = re.search(rf"^\s*{k}:\s*([0-9a-f]{{40}})", text, re.M)
        pins[k.lower()] = m.group(1) if m else None
    pins["toolchain"] = (G.PROFILE / "lean-toolchain").read_text(encoding="utf-8").strip()
    return pins


def pinned(w):
    """A Comparator receipt holds only at today's pins (decision 3): its recorded revisions against comparator.yml's,
    so moving the pins turns older receipts into recorded-only ones."""
    pins = comparator_pins()
    rv = w.get("revisions") or {}
    return all(pins.values()) and all(rv.get(k) == pins[k] for k in ("comparator_rev", "lean4export_rev", "toolchain"))


def module_file(ledger, module):
    return package(ledger) / (module.replace(".", "/") + ".lean")


def file_sha(path):
    return G.sha(path.read_bytes()) if path.is_file() else None


def comparator_status(ledger, report, c):
    """(ok, why) for a claim supported by a Comparator receipt: a pinned receipt whose stored receipt and log check
    against their SHA-256 (else the command refuses), whose log says okay, whose theorem is the claim's and whose
    challenge SHA-256 is the challenge file's now; and the binder's check that the challenge's type is the claim's."""
    s = c["support"]
    ws = [w for w in pwarrants(ledger, c["key"]) if w.get("kind") == "comparator"]
    held_ws = [w for w in ws if pinned(w)]
    if not held_ws:
        return False, ("only receipts from other pins, recorded only" if ws else "no Comparator receipt yet")
    row = (report.get("challenges") or {}).get(f"cmp|{c['key']}")
    if not row or not row.get("found") or not row.get("module"):
        return False, f"the challenge {s['challenge']} is missing from the package"
    if not row.get("typeOk"):
        return False, "the challenge's type is not the claim's (the emitter is not trusted)"
    now = file_sha(module_file(ledger, s["challenge"]))
    why = "no receipt matches"
    for w in reversed(held_ws):
        r = json.loads(ledger.receipt_file({"label": c["label"], "receipt_ref": w["receipt"]}).decode("utf-8"))
        log = ledger.receipt_file({"label": c["label"], "receipt_ref": w["log"]})
        if r.get("theorem") != s["theorem"] or OKAY not in log or G.sha(log) != r.get("log_sha256"):
            why = "the receipt is not for this challenge, or its log does not say okay"
        elif r.get("challenge_sha256") != now:
            why = "the challenge file changed since Comparator ran"
        else:
            return True, "ok"
    return False, why


def bridged_ledger(ledger, r):
    b = r["bridge"]
    d = Path(b["campaign"])
    other = G.Ledger(d if d.is_absolute() else ledger.dir / d)
    if not other.records:
        raise refusal(f"the bridged campaign {b['campaign']} has no ledger", "restore it, or refile without the bridge")
    other.check_schema()
    other.verify_statement()
    return other


def bridged_plan(ledger, r):
    """The 3a/3b part a bridge is re-folded from: the bridged claim and every claim it rests on, in the 3b surface, with
    that campaign's withdrawals (`gp`'s own `surface3`). The P runner folds it under `admission3`."""
    other = bridged_ledger(ledger, r)
    key = r["bridge"]["key"]
    if other.claim_by_key(key) is None:
        return None
    s3 = G.surface3(other, {key})
    s3.pop("udgFrames", None)
    withdrawn = sorted(other.withdrawals())
    if withdrawn:
        s3["withdrawn"] = withdrawn
    return s3


def plan(ledger, report):
    regs = code_by_id(ledger)
    fid = fidelity_of(ledger)
    codes = [{"code": k, "hash": r["hash"], "stamp": r["stamp"],
              "current": (lambda cur: {"hash": cur[0], "stamp": cur[1]} if cur else None)(current_of(report, regs, k)),
              "fidelity": FIDELITY.index(fid[k]["level"]) if k in fid else 0} for k, r in sorted(regs.items())]
    records, claims, bridged = {}, [], set()
    replay = replay_of(ledger, report)
    for c in pclaims(ledger):
        s = c.get("support") or None
        sup = None
        if s and s["kind"] == "theorem":
            sup = {"kind": "theorem", "decl": s["decl"]}
            tid = theorem_id(s["decl"], c["stmt"], c["premises"])
            row = report["theorems"].get(tid)
            records[tid] = {"declaration": s["decl"], "stmt": c["stmt"], "premises": c["premises"],
                            "ok": theorem_verdict(row, replay) == "ok"}
        elif s and s["kind"] == "comparator" and s.get("theorem"):
            decl = "comparator:" + s["theorem"]
            sup = {"kind": "comparator", "decl": decl}
            records[decl] = {"declaration": decl, "stmt": c["stmt"], "premises": c["premises"],
                             "ok": comparator_status(ledger, report, c)[0]}
        elif s and s["kind"] == "bridge":
            sup = {"kind": "bridge"}
            bridged.add(c["stmt"])
        elif s and s["kind"] == "discharge":
            sup = {"kind": "discharge", "from": s["from"], "by": s["by"]}
        elif s and s["kind"] == "weaken":
            sup = {"kind": "weaken", "from": s["from"]}
        proc = process_open(ledger, c)
        claims.append(dict({"key": c["key"], "stmt": c["stmt"], "scope": sorted(set(c["premises"])),
                       "conditions": conditions(ledger, c["key"]), "support": sup,
                       "recorded": [{"tier": recorded_tier(w), "digest": w.get("sha256") or G.sha(G.content(w).encode())}
                                    for w in pwarrants(ledger, c["key"])],
                       "presentations": [{"tier": TAGS[p["tag"]], "premises": p.get("premises", [])}
                                         for p in presentations(ledger, c["key"])]}, **({"process": proc} if proc else {})))
    out = {"codes": codes, "records": [records[k] for k in sorted(records)], "claims": claims,
           "withdrawn": sorted(pwithdrawals(ledger))}
    bridges = []
    for k in sorted(bridged):
        r = regs.get(k)
        if r and r.get("bridge") and ((report.get("bridges") or {}).get(str(k)) or {}).get("kernel") == "ok":
            p3 = bridged_plan(ledger, r)
            if p3 is not None:
                bridges.append({"code": k, "lit": r["bridge"]["lit"], "plan": p3})
    if bridges:  # only when used, so a P1 ledger gives the runner exactly the P1 input
        out["bridges"] = bridges
    return out


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
    if w["kind"] == "comparator":
        return "Comparator receipt" + ("" if pinned(w) else " at another pin")
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
    if s.get("kind") == "comparator" and t == 1:
        return t, f"{c['label']}: Comparator receipt"
    if s.get("kind") == "bridge" and t == 3:
        return t, f"{c['label']}: bridge"
    if s.get("kind") in ("discharge", "weaken") and key not in seen:
        subs = [best_step(st, k, seen + (key,)) for k in ([s["from"], s["by"]] if s["kind"] == "discharge" else [s["from"]])]
        subs = [x for x in subs if x]
        if subs:
            return max(subs)
    return t, c["label"]


def replayed(st):
    r = replay_of(st.ledger, st.report)
    return bool(r and r.get("ok"))


def bridge_why(st, c):
    """Why a bridge does not hold: the binder's check of the generated definition, or the bridged claim's state."""
    r = code_by_id(st.ledger).get(c["stmt"]) or {}
    b = r.get("bridge")
    if not b:
        return f"{name_of(st.ledger, c['stmt'])} is not a bridge code"
    row = (st.report.get("bridges") or {}).get(str(c["stmt"])) or {}
    if row.get("kernel") != "ok":
        return f"the binder did not confirm {r['decl']} is the literal meaning: {row.get('kernel', 'not bound yet')}"
    other = bridged_ledger(st.ledger, r)
    if b["key"] in other.withdrawals():
        return f"the bridged claim {b['label']} is withdrawn in {b['campaign']}"
    return f"the bridged claim {b['label']} of {b['campaign']} is not held there (re-folded) with this statement"


def tier_text(st, key):
    item, c = st.items[key], st.claims[key]
    if item["held"]:
        return f"tier {item['tier']}" + (" (unreplayed)" if item["tier"] == 2 and not replayed(st) else "")
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
        verdict = theorem_verdict(row, replay_of(st.ledger, st.report))
        parts.append(f"theorem {s['decl']} refused: {verdict}" if verdict != "ok" else
                     f"theorem {s['decl']}: bound, statement not fresh")
    if s.get("kind") == "comparator" and not item["proofAccepted"]:
        ok, why = comparator_status(st.ledger, st.report, c)
        parts.append(f"Comparator: {why}" if not ok else "Comparator receipt checked, statement not fresh")
    if s.get("kind") == "bridge" and not item["proofAccepted"]:
        parts.append(f"bridge: {bridge_why(st, c)}")
    if s.get("kind") == "discharge":
        for k in (s["from"], s["by"]):
            if k in st.items and not st.items[k]["held"]:
                parts.append(f"rests on unheld {st.claims[k]['label']}")
    if s.get("kind") == "weaken" and s["from"] in st.items and not st.items[s["from"]]["held"]:
        parts.append(f"rests on unheld {st.claims[s['from']]['label']}")
    return "; ".join(parts) if parts else "no warrant"


def presented_text(st, key):
    """Per tag: OVERSTATED (above the earned tier, or a mathematical premise left out), else "conditions open" when a
    presentation leaves out an open process condition (P2)."""
    item, ps = st.items[key], presentations(st.ledger, key)
    groups = {}
    for p, over, cond in zip(ps, item["overstated"], item.get("conditionsOpen") or [False] * len(ps)):
        groups.setdefault(p["tag"], []).append((over, cond and not over))
    out = []
    for tag in sorted(groups, key=lambda t: (TAGS[t], t)):
        n, m, q = len(groups[tag]), sum(o for o, _ in groups[tag]), sum(c for _, c in groups[tag])
        venues = f"{n} venue{'s' if n != 1 else ''}"
        notes = ([f"{m} OVERSTATED"] if m else []) + (["conditions open" if q == n else f"{q} conditions open"] if q else [])
        out.append(f"presented [{tag}] in {venues}" + (": OVERSTATED" if m == n else f" ({', '.join(notes)})" if notes
                                                       else ""))
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
    proc = process_open(st.ledger, c)
    if proc:
        parts.append("conditions open: " + names(st.ledger, proc))
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
        print("\nheld verdicts come from the Kernel fold; " + (
            "tier 2 is final: lean4checker replayed the package as it is now" if replayed(st) else
            "tier 2 shows as unreplayed until `gp bind --replay` passes on the package as it is now"))


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
    replay = replay_of(ledger, st.report)

    def walk(key, pad, seen):
        cc, item = st.claims[key], st.items[key]
        s = cc.get("support") or {}
        mark = "  <- weakest step" if weakest and weakest[1].startswith(cc["label"] + ":") else ""
        state_ = "held" if item["held"] else "not held"
        if s.get("kind") == "theorem":
            row = st.report["theorems"].get(theorem_id(s["decl"], cc["stmt"], cc["premises"]))
            axs = ", ".join((row or {}).get("axioms", [])) or "-"
            print(f"{pad}{cc['label']}: lean_theorem {s['decl']} [tier 2, {state_}]: {theorem_verdict(row, replay)}; "
                  f"axioms {axs}; " + ("replayed by lean4checker" if replay and replay.get("ok") else "unreplayed")
                  + mark)
        elif s.get("kind") == "comparator":
            ok, why = comparator_status(ledger, st.report, cc)
            print(f"{pad}{cc['label']}: comparator_receipt {s.get('theorem')} (solution: {s['decl']}) [tier 1, {state_}]: "
                  f"{why}; challenge {s.get('challenge')}{mark}")
        elif s.get("kind") == "bridge":
            b = code_by_id(ledger)[cc["stmt"]].get("bridge") or {}
            why = "ok" if item["held"] else bridge_why(st, cc)
            print(f"{pad}{cc['label']}: profile_replay of {b.get('campaign')}:{b.get('label')} [tier 3, {state_}]: "
                  f"{why}{mark}")
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
            if w.get("kind") == "comparator":
                rv = w.get("revisions") or {}
                print(f"{pad}  {'receipt' if pinned(w) else 'recorded only'}: {recorded_text(w)}, Comparator "
                      f"{(rv.get('comparator_rev') or '-')[:12]}, lean4export {(rv.get('lean4export_rev') or '-')[:12]}, "
                      f"{rv.get('toolchain')}; log sha256 {w['log']['sha256'][:12]}")
                continue
            m = "  <- weakest step" if weakest and weakest[1] == f"{cc['label']}: {recorded_text(w)}" else ""
            cond = f"; conditions (OPEN): {names(ledger, w['conditions'])}" if w.get("conditions") else ""
            print(f"{pad}  recorded only: {recorded_text(w)} {w.get('locator', '')} sha256 {w.get('sha256', '-')[:12]}"
                  f"{cond}{m}")

    print("  warrant path:")
    walk(c["key"], "    ", {c["key"]})
    item = st.items[c["key"]]
    proc = process_open(ledger, c)
    for p, over, cond in zip(presentations(ledger, c["key"]), item["overstated"],
                             item.get("conditionsOpen") or [False] * len(item["overstated"])):
        stated = names(ledger, p.get("premises", [])) or "no premises"
        left = [h for h in proc if h not in p.get("premises", [])]
        print(f"  presented in {p['venue']} as [{p['tag']}] stating {stated}" + (": OVERSTATED" if over else
              f": conditions open ({names(ledger, left)})" if cond else ""))


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
    procs = {}
    for c in st.claims.values():
        if c["key"] not in st.withdrawn:
            for h in process_open(ledger, c):
                procs.setdefault(h, []).append(c["label"])
    if procs:
        print("open process conditions (shown, never OVERSTATED):")
        for h in sorted(procs, key=lambda h: (-len(procs[h]), name_of(ledger, h))):
            kind = code_by_id(ledger)[h].get("process")
            print(f"  {name_of(ledger, h)} ({kind}): {len(procs[h])} claim{'s' if len(procs[h]) != 1 else ''} "
                  f"({', '.join(sorted(procs[h]))})")
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
            rows.append(f"  {c['label']}: theorem {s['decl']}: {theorem_verdict(row, replay_of(ledger, st.report))}; "
                        f"smallest fix: prove {stmt_text(ledger, c)} with the standard axioms only")
        if s.get("kind") == "comparator":
            rows.append(f"  {c['label']}: Comparator: {comparator_status(ledger, st.report, c)[1]}; smallest fix: run "
                        f"bash tools/lanep-comparator.sh in WSL and `gp submit {c['label']} --comparator <receipt>`")
        if s.get("kind") == "bridge":
            rows.append(f"  {c['label']}: bridge: {bridge_why(st, c)}")
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


BRIDGE_FILE = """import GPBinding.LaneP.Bridge

/-!
Generated by `gp register --bridge` (Lane P, profile_replay; GP 0.52 P2). Do not edit: any change unbinds the code.
`{ident}` is the literal 3a/3b meaning of claim {label} (key {key}) of the campaign {campaign}. The P runner re-folds
that campaign's claim and accepts a claim of `{ident}` when the bridged claim is held with exactly this statement.
-/

namespace {ns}

def {ident} : Prop := GPBinding.LaneP.meaning3 {lit}

theorem {ident}_bridgeSound : GPBinding.LaneP.BridgeSound {ident} {lit} := Iff.rfl

end {ns}
"""


def lean_string(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def manifest_revs(pkg):
    path = pkg / "lake-manifest.json"
    if not path.exists():
        return {}
    return {q["name"]: q.get("rev") for q in json.loads(path.read_text(encoding="utf-8")).get("packages", [])}


def binding_pin_check(ledger):
    """A bridge needs the campaign pin to be the binding pin: the package requires the binding (`gp_binding`, for
    `GPBinding.LaneP.meaning3`) and every package both pin is at the binding's revision (the toolchain is checked on
    every bind)."""
    pkg = package(ledger)
    text = "".join((pkg / f).read_text(encoding="utf-8") for f in ("lakefile.toml", "lakefile.lean") if (pkg / f).exists())
    if not re.search(r'name\s*=\s*"gp_binding"', text) and not re.search(r"require\s+gp_binding\b", text):
        raise refusal("the campaign package does not require the binding (gp_binding), so a bridge has no meaning to "
                      "state", f'add [[require]] name = "gp_binding" path = "{(G.ROOT / "binding").as_posix()}" to '
                      f"{pkg / 'lakefile.toml'} and pin Mathlib to the binding's revision", "bridge")
    mine, theirs = manifest_revs(pkg), manifest_revs(G.ROOT / "binding")
    bad = sorted(k for k in mine if theirs.get(k) and mine[k] and mine[k] != theirs[k])
    if bad:
        raise refusal(f"the campaign package pins {', '.join(bad)} differently from the binding",
                      "pin them to binding/lake-manifest.json's revisions (campaign pin = binding pin)", "bridge")


def register_lean(ledger, decl, name, extra=None):
    """Bind a Lean statement code: the declaration exists, is a campaign-local Prop, and has this closure."""
    code = new_code(ledger, {"name": name, "kind": "lean", "decl": decl})
    entry = dict({"code": code, "kind": "lean", "decl": decl}, **(extra or {}))
    report = current_report(ledger, extra_codes=[entry])
    e = report["codes"].get(str(code)) or {}
    if not e.get("found"):
        raise refusal(f"{decl} is not a declaration of the campaign package", "check the name (fully qualified), then build")
    if not e.get("prop"):
        raise refusal(f"{decl} is not a campaign-local `def {decl.split('.')[-1]} : Prop` without universe parameters",
                      "state it as `def X : Prop := ...` in the package")
    if (extra or {}).get("bridge"):
        row = (report.get("bridges") or {}).get(str(code)) or {}
        if row.get("kernel") != "ok":
            raise refusal(f"the kernel did not accept {decl} as the literal meaning: {row.get('kernel', 'no report')}",
                          "regenerate the bridge file; do not edit it", "bridge")
    for r in registers(ledger):
        if r.get("decl") == decl and r["hash"] == e["hash"] and r["stamp"] == report["stamp"]:
            raise refusal(f"{decl} is already registered as {r['name']} with this closure", f"use {r['name']}")
    body = dict({"name": name, "kind": "lean", "decl": decl, "hash": e["hash"], "closure": e["closure"],
                 "stamp": report["stamp"]}, **(extra or {}))
    ledger.append(dict({"op": "register", "code": code}, **body))
    return code, e, report


def cmd_register_bridge(ledger, args):
    name = args.as_
    if not name:
        raise refusal("a bridge code needs a name", "give --as NAME", "bridge")
    if name in code_by_name(ledger):
        raise refusal(f"{name!r} is already registered", "register under a new name with --as NAME", "bridge")
    camp, sep, label = args.bridge.rpartition(":")
    if not sep or not camp or not label:
        raise refusal(f"cannot read the bridge {args.bridge!r}", "give --bridge <campaign-dir>:<label>", "bridge")
    other = G.Ledger(camp)
    if not other.records:
        raise refusal(f"no ledger at {camp}", "give the directory of a 3a/3b campaign", "bridge")
    other.check_schema()
    if is_p(other) or (isinstance(other.verify_statement(), dict) and other.statement.get("profile") == "P"):
        raise refusal(f"{camp} is a Lane P campaign; a bridge reaches a 3a/3b claim", "bridge to a 3a/3b campaign", "bridge")
    c = other.claim(label)
    binding_pin_check(ledger)
    lit = json.dumps(G.claim_surface3(c), sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    try:
        where = Path(os.path.relpath(Path(camp).resolve(), ledger.dir.resolve())).as_posix()
    except ValueError:  # another drive
        where = Path(camp).resolve().as_posix()
    root = roots(ledger)[0]
    ident = re.sub(r"[^A-Za-z0-9_]", "_", name)
    ident = ident if ident[:1].isalpha() else "B_" + ident
    path = package(ledger) / root / BRIDGE_DIR / f"{ident}.lean"
    if path.exists():
        raise refusal(f"{path} exists", "register the bridge under a new name with --as NAME", "bridge")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(BRIDGE_FILE.format(ident=ident, label=label, key=c["key"], campaign=where, ns=f"{root}.{BRIDGE_DIR}",
                                        lit=lean_string(lit)).encode("utf-8"))
    bridge = {"campaign": where, "label": label, "key": c["key"], "lit": lit}
    try:
        code, e, report = register_lean(ledger, f"{root}.{BRIDGE_DIR}.{ident}", name, {"bridge": bridge})
    except G.Refusal:
        path.unlink(missing_ok=True)
        raise
    print(f"registered {name} (code {code}): the literal 3a/3b meaning of {label} (key {c['key']}) of {where}, "
          f"generated as {root}.{BRIDGE_DIR}.{ident}; the kernel confirmed it (BridgeSound by Iff.rfl); closure "
          f"{e['hash'][:12]}, stamp {report['stamp'][:12]}")


def cmd_register(ledger, args):
    if getattr(args, "bridge", None):
        return cmd_register_bridge(ledger, args)
    if getattr(args, "process", None) and args.prose is None:
        raise refusal("a process condition is a prose statement", "give --prose TEXT --as NAME --process KIND")
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
        process = getattr(args, "process", None)
        if process:
            if process not in PROCESS:
                raise refusal(f"unknown process condition kind {process}", f"one of {', '.join(PROCESS)}")
            body["process"] = process
        code = new_code(ledger, {"name": name, "kind": "prose", "text": text, **({"process": process} if process else {})})
        ledger.append(dict({"op": "register", "code": code}, **body))
        print(f"registered {name} (code {code}): prose, text {body['hash'][:12]}; never holdable" +
              (f"; a process condition ({process}): shown as open, never OVERSTATED" if process else ""))
        return
    if not args.decl:
        raise refusal("register needs a declaration", "gp register <Decl> [--as NAME], or --prose TEXT --as NAME")
    decl = args.decl
    name = args.as_ or decl.split(".")[-1]
    if name in code_by_name(ledger):
        raise refusal(f"{name!r} is already registered", "register under a new name with --as NAME")
    code, e, report = register_lean(ledger, decl, name)
    print(f"registered {name} (code {code}): {decl}, closure {e['hash'][:12]} over {len(e['closure'])} local "
          f"constant{'s' if len(e['closure']) != 1 else ''}, stamp {report['stamp'][:12]}")


def premise_codes(ledger, premises, process_ok=False):
    """Codes of premises (`process_ok`: reviewer conditions, which may be process conditions)."""
    out = []
    for h in premises or []:
        r, body = parse_stmt(ledger, h)
        if body:
            ledger.append(r)
        if r["code"] in out:
            raise refusal(f"premise {h} is given twice", "give each premise once")
        if r.get("process") and not process_ok:
            raise refusal(f"{h} is a process condition ({r['process']}), not a mathematical premise",
                          f"give it with --condition {h}")
        out.append(r["code"])
    return out


def condition_codes(ledger, conds):
    """A claim's open process conditions (P2): registered prose with --process."""
    out = []
    for h in conds or []:
        r = code_ref(ledger, h, "process condition")
        if not r.get("process"):
            raise refusal(f"{h} is not a process condition", f"register it with --process KIND, or give it as --premise {h}")
        if r["code"] not in out:
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
    comparator, bridge = getattr(args, "comparator", None), getattr(args, "bridge", None)
    if r["kind"] == "prose" and (args.theorem or comparator or bridge):
        raise refusal(f"{stmt_name} is prose: prose statements are never holdable", "register a Lean statement")
    if sum(bool(x) for x in (args.theorem, args.from_, comparator, bridge)) > 1:
        raise refusal("a claim has one holding warrant", "give one of --theorem T, --from L, --comparator T, --bridge B")
    if body:
        ledger.append(r)
    premises = premise_codes(ledger, args.premise)
    conds = condition_codes(ledger, getattr(args, "condition", None))
    regs = code_by_id(ledger)
    if (args.theorem or comparator) and any(regs[p]["kind"] == "prose" for p in premises):
        raise refusal("a lean_theorem cannot take a prose premise: the binder has no Lean type for it",
                      "register the premise as a Lean statement, or drop --theorem")
    support = None
    if args.theorem:
        support = {"kind": "theorem", "decl": args.theorem}
    if comparator:
        support = {"kind": "comparator", "decl": comparator}
    if bridge:
        b = r.get("bridge")
        if not b:
            raise refusal(f"{stmt_name} is not a bridge code", "register one with gp register --bridge DIR:LABEL --as NAME",
                          "bridge")
        camp, _, lab = bridge.rpartition(":")
        same = not camp or Path(camp).resolve() == bridged_ledger(ledger, r).dir.resolve()
        if lab != b["label"] or not same:
            raise refusal(f"{stmt_name} bridges {b['campaign']}:{b['label']}, not {bridge}",
                          f"give --bridge {b['label']}, or register a bridge code for {bridge}", "bridge")
        support = {"kind": "bridge"}
    if args.from_:
        src = pclaim(ledger, args.from_)
        if src["stmt"] != r["code"] or not set(src["premises"]) <= set(premises):
            raise refusal(f"weakening needs the same statement and a larger scope than {args.from_}",
                          f"file --lean {name_of(ledger, src['stmt'])} with every premise of {args.from_}")
        support = {"kind": "weaken", "from": src["key"]}
    rec = dict({"label": args.label, "stmt": r["code"], "premises": premises, "support": support},
               **({"conditions": conds} if conds else {}))
    key = new_pkey(ledger, rec)
    if support and support["kind"] == "theorem":
        current_report(ledger, extra_theorems=[{"decl": args.theorem, "stmt": r["code"], "premises": premises}])
    if support and support["kind"] == "comparator":
        support.update(emit_comparator(ledger, key, args.label, r["code"], premises, comparator))
    ledger.append(dict({"op": "pclaim", "key": key}, **rec))
    st = state(ledger)
    print(f"claim {args.label} (key {key}) filed: {stmt_text(ledger, rec)}; {summary(st, key)}")
    if support and support["kind"] == "comparator":
        cfg = (ledger.dir / "comparator" / f"K{key}.json").as_posix()
        print(f"Comparator challenge emitted: {support['challenge']} (theorem {support['theorem']}); run in WSL:\n"
              f"  bash tools/lanep-comparator.sh {ledger.dir.as_posix()} {cfg}\n"
              f"then: gp submit {args.label} --comparator {cfg[:-5]}.receipt.json")


def lean_term(ledger, code):
    r = code_by_id(ledger)[code]
    return r["decl"] if r["kind"] == "lean" else f"¬({lean_term(ledger, r['of'])})"


def base_codes(ledger, codes):
    regs = code_by_id(ledger)
    return [k if regs[k]["kind"] == "lean" else base_codes(ledger, [regs[k]["of"]])[0] for k in codes]


def code_modules(ledger, codes):
    """The modules declaring these codes, from the latest bind that reports them; None if none does."""
    for rec in reversed(bind_records(ledger)):
        rep_ = load_report(ledger, rec)
        mods = [(rep_["codes"].get(str(k)) or {}).get("module") for k in codes]
        if all(mods):
            return sorted(set(mods))
    return None


def emit_comparator(ledger, key, label, stmt, premises, solution):
    """Emit a Comparator challenge for the claim from the registry, and a solution applying `solution`, into the
    campaign package (<root>/GPComparator/K<key>/), and the Comparator config into <campaign>/comparator/K<key>.json.
    The emitter is not trusted: the binder checks the challenge's type is the claim's before the claim is filed."""
    pkg, rs = package(ledger), roots(ledger)
    base = f"{rs[0]}.{CMP_DIR}.K{key}"
    theorem = f"GPLaneP.K{key}"
    ty = " → ".join([f"({lean_term(ledger, h)})" for h in premises] + [f"({lean_term(ledger, stmt)})"])
    mods = [m for m in modules(pkg, rs) if not is_generated(m)]
    chal_mods = code_modules(ledger, base_codes(ledger, [stmt] + premises)) or mods
    doc = (f"/-! Comparator challenge for claim {label} (Lane P, GP 0.52 P2), emitted by gp from the statement registry. "
           f"The P binder checks that `{theorem}`'s type is the claim's; the emitter is not trusted. -/")
    chal = "".join(f"import {m}\n" for m in chal_mods) + f"\n{doc}\n\ntheorem {theorem} : {ty} := by sorry\n"
    sol = "".join(f"import {m}\n" for m in mods) + (f"\n/-! Comparator solution for claim {label}: `{solution}` at the "
                                                   f"claim's type. Comparator checks it. -/\n\n"
                                                   f"theorem {theorem} : {ty} := {solution}\n")
    d = pkg / rs[0] / CMP_DIR / f"K{key}"
    paths = [d / "Challenge.lean", d / "Solution.lean", ledger.dir / "comparator" / f"K{key}.json"]
    for q in paths:
        if q.exists():
            raise refusal(f"{q} exists", "move it aside: gp emits each challenge once", "comparator")
    for q in paths:
        q.parent.mkdir(parents=True, exist_ok=True)
    paths[0].write_bytes(chal.encode("utf-8"))
    paths[1].write_bytes(sol.encode("utf-8"))
    paths[2].write_bytes((json.dumps({"challenge_module": f"{base}.Challenge", "solution_module": f"{base}.Solution",
                                      "theorem_names": [theorem], "permitted_axioms": AXIOMS}, indent=1) + "\n").encode("utf-8"))
    try:
        report = current_report(ledger, extra_challenges=[{"id": f"cmp|{key}", "decl": theorem, "module": f"{base}.Challenge",
                                                           "stmt": stmt, "premises": premises}])
        row = (report.get("challenges") or {}).get(f"cmp|{key}") or {}
        if not (row.get("found") and row.get("module") and row.get("typeOk")):
            raise refusal("the emitted challenge's type is not the claim's", "report this to the builder", "comparator")
    except G.Refusal:
        for q in paths:
            q.unlink(missing_ok=True)
        raise
    return {"theorem": theorem, "challenge": f"{base}.Challenge", "solution": f"{base}.Solution"}


def store_raw(ledger, data, suffix):
    """File raw bytes (a Comparator log) as receipts/<sha256><suffix>; checked against the SHA-256 on every read."""
    digest = G.sha(data)
    rel = f"{G.RECEIPTS}/{digest}{suffix}"
    path = ledger.dir / rel
    if path.exists():
        if G.sha(path.read_bytes()) != digest:
            raise refusal(f"{rel} exists and does not hold the bytes its name hashes", f"move the damaged {rel} aside")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    return {"path": rel, "sha256": digest}


def submit_comparator(ledger, c, args):
    s = c.get("support") or {}
    if s.get("kind") != "comparator" or not s.get("theorem"):
        raise refusal(f"{c['label']} is not a Comparator claim", f"file a claim with --comparator T", "comparator")
    p = Path(args.comparator)
    try:
        receipt = json.loads(p.read_bytes().decode("utf-8"))
    except (OSError, ValueError):
        raise refusal(f"cannot read the receipt {args.comparator}", "give the receipt lanep-comparator.sh wrote", "comparator")
    if not isinstance(receipt, dict) or receipt.get("schema") != "gp-comparator-receipt/v1":
        raise refusal("not a gp-comparator-receipt/v1 receipt", "give the receipt lanep-comparator.sh wrote", "comparator")
    if receipt.get("theorem") != s["theorem"] or receipt.get("challenge_module") != s["challenge"]:
        raise refusal(f"the receipt is for {receipt.get('theorem')}, not this claim's challenge {s['theorem']}",
                      "submit the receipt of this claim's challenge", "comparator")
    logp = Path(args.log) if getattr(args, "log", None) else p.parent / str(receipt.get("log") or "")
    try:
        log = logp.read_bytes()
    except OSError:
        raise refusal(f"cannot read the Comparator log {logp}", "give it with --log", "comparator")
    if G.sha(log) != receipt.get("log_sha256"):
        raise refusal("the log does not match the receipt's SHA-256", "submit the log Comparator wrote", "comparator")
    if OKAY not in log or receipt.get("okay") is not True or receipt.get("exit") != 0:
        raise refusal('Comparator did not accept the solution (its log does not say "Your solution is okay")',
                      "fix the solution and rerun Comparator", "comparator")
    pins = comparator_pins()
    at_pin = pinned({"revisions": receipt})
    if at_pin:
        if receipt.get("challenge_sha256") != file_sha(module_file(ledger, s["challenge"])):
            raise refusal("the challenge changed since Comparator ran", "rerun Comparator on the emitted challenge", "comparator")
        if receipt.get("tree_sha256") != tree_sha(ledger):
            raise refusal("the campaign package changed since Comparator ran (its tree SHA-256 differs)",
                          "rerun bash tools/lanep-comparator.sh on the package as it is now", "comparator")
    rec = {"op": "pwarrant", "key": c["key"], "label": c["label"], "kind": "comparator", "theorem": s["theorem"],
           "challenge_sha256": receipt.get("challenge_sha256"), "pinned": at_pin,
           "revisions": {k: receipt.get(k) for k in ("comparator_rev", "lean4export_rev", "toolchain")},
           "receipt": ledger.store_receipt(receipt), "log": store_raw(ledger, log, ".log")}
    ledger.append(rec)
    st = state(ledger)
    print(f"Comparator receipt for {c['label']} recorded" + (" at the pinned revisions" if at_pin else
          " from another pin: recorded only (decision 3)") + f"; {summary(st, c['key'])}")


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
    if getattr(args, "comparator", None):
        if any((args.hand_proof, args.script, args.numerical, args.external)):
            raise refusal("a P submission is one warrant", "give --comparator alone")
        return submit_comparator(ledger, c, args)
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
        rec["conditions"] = premise_codes(ledger, args.condition, process_ok=True)
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
           "premises": premise_codes(ledger, args.premise, process_ok=True), "locator": args.locator}
    ledger.append(rec)
    st = state(ledger)
    i = presentations(ledger, c["key"]).index(next(p for p in presentations(ledger, c["key"]) if G.content(p) == G.content(rec)))
    over = st.items[c["key"]]["overstated"][i]
    print(f"presentation of {c['label']} in {args.venue} as [{tag}] recorded" + (": OVERSTATED" if over else ""))


def replay(ledger, report):
    """`gp bind --replay` (P2, decision 7): replay the package's modules (the binder's import set) with lean4checker at
    the pinned toolchain. A module that skipped the kernel (`debug.skipKernelTC`) fails here; then no theorem warrant
    of this package holds until a replay passes. A passing replay makes tier 2 final for this tree and stamp."""
    toolchain, _ = G.toolchain_lake()
    chk = toolchain / ("bin/leanchecker" + (".exe" if os.name == "nt" else ""))
    if not chk.is_file():
        raise refusal("lean4checker (`leanchecker`) is not in the pinned toolchain", "tier 2 stays unreplayed", "replay")
    pkg = package(ledger).resolve()
    env, lake = toolchain_env(pkg)
    mods = modules(pkg, roots(ledger))
    t0 = time.time()
    rc, out, err = run_capped([str(lake), "env", str(chk), *mods], pkg, env, BUILD_TIMEOUT)
    if rc is None:
        raise refusal(f"the lean4checker replay exceeded {BUILD_TIMEOUT} s", "nothing is recorded; tier 2 stays unreplayed",
                      "replay")
    lines = [l for l in (out + b"\n" + err).decode("utf-8", "replace").replace("\r\n", "\n").splitlines() if l.strip()]
    rec = {"op": "replay", "checker": "leanchecker", "tree_sha256": report["tree_sha256"], "stamp": report["stamp"],
           "modules": mods, "ok": rc == 0, "seconds": round(time.time() - t0, 1)}
    if rc != 0:
        rec["detail"] = lines[:G.BUILD_TAIL]
    ledger.append(rec)
    if rc != 0:
        raise G.Refusal("the lean4checker replay failed: a declaration of the package does not replay in the kernel",
                        "replay", "-", "find the module that skipped the kernel (`set_option debug.skipKernelTC`); no "
                        "theorem warrant of this package holds until a replay passes",
                        detail=["leanchecker:"] + ["  " + l for l in lines[:G.BUILD_TAIL]])
    print(f"replayed {len(mods)} module{'s' if len(mods) != 1 else ''} with lean4checker in {rec['seconds']} s: "
          "tier 2 is final for this package")


def cmd_bind(ledger, args):
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
    for cid, row in sorted((report.get("challenges") or {}).items()):
        ok = row.get("found") and row.get("module") and row.get("typeOk")
        print(f"  Comparator challenge K{cid.split('|')[1]}: " + ("its type is the claim's" if ok else "NOT the claim's type"))
    for code, row in sorted((report.get("bridges") or {}).items()):
        print(f"  bridge {name_of(ledger, int(code))}: " + ("the kernel confirms the literal meaning" if row.get("kernel") == "ok"
                                                           else row.get("kernel", "-")))
    if args.replay:
        replay(ledger, report)


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
        if r["op"] == "pwarrant" and r.get("kind") == "comparator":
            for ref in (r["receipt"], r["log"]):
                ledger.copy_receipt({"label": r["label"], "receipt_ref": ref},
                                    merged.receipt_file({"label": r["label"], "receipt_ref": ref}))
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
