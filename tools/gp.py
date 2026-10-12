"""gp: the 3P campaign CLI (post-G3a handoff §4.6). Lean-first: every verdict comes from the profile.

usage: python tools/gp.py --campaign <dir> <command> ...

  init                                  start a ledger for the campaign statement in <dir>/campaign.json
  claim <label> (--matroid M | --system FILE | --nf FILE | --udg GRAPH [--gauge]) --kind KIND [--target POLY]
        (--char P | --char0 | --outside P,Q | --real | --semireal | --rat-field) [--premise NAME]
                                        file a claim; it is open until a receipt supports it
  cover <label> --candidates FILE --n N --m M [--premise NAME[=data] ...] [--supports L1,L2]
                                        a candidate cover for the goal's spine rule (a ledger record, no claim)
  submit <label> <receipt.json>         offer a certificate or a rule instance; GP replays it
  status                                held, open, refused and earned, per claim and per matroid
  explain <label>                       the licence tree of one claim, or a cover's join
  frontier                              open claims, each with its last refusal and smallest fix
  tailings --export [FILE]              by-products: refused attempts, earned widenings, open items
  emit-lean (<label> | --all)           Lean theorem warrants for held claims the generator covers
  merge <other-campaign-dir>            land another branch's records here, only if the merged log folds

The ledger (<dir>/ledger.jsonl, gp-ledger/v1) is append-only and written only by this CLI. Each claim
binds its encoding digest; each support records the receipt it was replayed from, inline (as older
supports are) or by reference: receipts/<sha256>.json, whose SHA-256 is checked on every command
before anything folds. The Kernel fold over the whole ledger decides every status, on every command.
A refused submission is logged with the refusal and never becomes support.
"""
import argparse
import datetime
import hashlib
import importlib.util
import itertools
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PROFILE = ROOT / "profile"
EXE = PROFILE / (".lake/build/bin/gp_ledger" + (".exe" if os.name == "nt" else ""))
ELAN_HOME = Path(os.environ.get("ELAN_HOME") or Path.home() / ".elan")
SCHEMA = "gp-ledger/v1"
KINDS = ["EMPTY", "NONEMPTY", "IN_IDEAL", "VANISHES_ON", "NOT_IN_IDEAL"]
# What a held kind says about a matroid's realization system.
MEANING = {"EMPTY": "not realizable", "NONEMPTY": "realizable, with a point over the prime field",
           "NOT_IN_IDEAL": "realizable (geometrically nonempty)"}

_spec = importlib.util.spec_from_file_location("encode_matroid", ROOT / "tools/encode-matroid.py")
encoder = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(encoder)
_spec_udg = importlib.util.spec_from_file_location("encode_udg", ROOT / "tools/encode-udg.py")
udg_encoder = importlib.util.module_from_spec(_spec_udg)
_spec_udg.loader.exec_module(udg_encoder)


class Refusal(Exception):
    """A CLI-level refusal: what was refused, under which rule and scope, and the smallest fix."""

    def __init__(self, what, rule, scope, fix):
        super().__init__(what)
        self.body = {"message": what, "rule": rule, "scope": scope, "smallest_fix": fix}


def now():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def sha(data):
    return hashlib.sha256(data).hexdigest()


# --- the ledger -----------------------------------------------------------------------------

RECEIPTS = "receipts"
SHA256_HEX = re.compile(r"[0-9a-f]{64}")


def receipt_bytes(receipt):
    """The stored bytes of a receipt filed by reference: its canonical JSON."""
    return json.dumps(receipt, ensure_ascii=False, sort_keys=True).encode("utf-8")


def receipt_digest(support):
    """A support's receipt identity: the SHA-256 of its stored file, or of an inline receipt's canonical
    bytes (the bytes it would be stored as). Equal digests are equal receipts."""
    ref = support.get("receipt_ref")
    return ref["sha256"] if ref else sha(receipt_bytes(support["receipt"]))


def receipt_ref_path(record):
    """The checked relative path and SHA-256 of a support's receipt reference, else a refusal."""
    ref = record.get("receipt_ref")
    rel = ref.get("path") if isinstance(ref, dict) else None
    digest = ref.get("sha256") if isinstance(ref, dict) else None
    ok = isinstance(rel, str) and isinstance(digest, str) and SHA256_HEX.fullmatch(digest) is not None
    if not ok or "\\" in rel or ":" in rel or rel.startswith("/") or ".." in rel.split("/"):
        raise Refusal(f"support {record.get('label')} has a malformed receipt reference", "receipt custody", "-",
                      'a reference is {"path": "receipts/<sha256>.json", "sha256": "<sha256>"}, inside the campaign')
    return rel, digest


class Ledger:
    def __init__(self, campaign):
        self.dir = Path(campaign)
        self.path = self.dir / "ledger.jsonl"
        self.records = []
        self._refused = None
        self._claims = None
        self._supports = None
        # Where receipt files are looked up, in order (a merge adds the other branch's directory).
        # Files are content-addressed and checked on every read, so no directory is trusted.
        self.receipt_dirs = [self.dir]
        if self.path.exists():
            self.records = [json.loads(l) for l in self.path.read_text(encoding="utf-8").splitlines() if l.strip()]

    def append(self, record):
        record = dict(record, at=now())
        with self.path.open("ab") as f:
            f.write((json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n").encode("utf-8"))
        self.records.append(record)
        self._refused = None
        self._claims = None
        self._supports = None
        return record

    def store_receipt(self, receipt):
        """File a receipt as receipts/<sha256>.json and return its reference. A file is written once;
        an existing one must already hold exactly these bytes."""
        data = receipt_bytes(receipt)
        digest = sha(data)
        rel = f"{RECEIPTS}/{digest}.json"
        path = self.dir / rel
        if path.exists():
            if sha(path.read_bytes()) != digest:
                raise Refusal(f"{rel} exists and does not hold the receipt its name hashes", "receipt custody",
                              "-", f"move the damaged {rel} aside; receipt files are never overwritten")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            tmp = path.with_name(path.name + ".tmp")
            tmp.write_bytes(data)
            tmp.replace(path)
        return {"path": rel, "sha256": digest}

    def receipt_file(self, record):
        """The bytes of a support's referenced receipt file, checked against the recorded SHA-256. A
        malformed reference, a missing file or a mismatch refuses: nothing is folded."""
        rel, digest = receipt_ref_path(record)
        label = record.get("label")
        for d in self.receipt_dirs:
            path = Path(d) / rel
            if path.is_file():
                data = path.read_bytes()
                if sha(data) != digest:
                    raise Refusal(f"receipt file {rel} of support {label} does not match its recorded SHA-256 "
                                  f"{digest[:12]}", "receipt custody", "-",
                                  f"restore {rel} from the branch that filed it; the ledger is never rewritten")
                return data
        raise Refusal(f"receipt file {rel} of support {label} is missing", "receipt custody", "-",
                      f"restore {rel} (SHA-256 {digest[:12]}) from the branch that filed it")

    def load_receipt(self, record):
        return json.loads(self.receipt_file(record).decode("utf-8"))

    def copy_receipt(self, record, data):
        """Land another branch's checked receipt file (`receipt_file`) under the same path here."""
        rel, digest = receipt_ref_path(record)
        path = self.dir / rel
        if path.exists():
            if sha(path.read_bytes()) != digest:
                raise Refusal(f"{rel} exists here and does not match its recorded SHA-256 {digest[:12]}",
                              "receipt custody", "-", f"restore {rel} on this branch, then merge again")
            return
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_name(path.name + ".tmp")
        tmp.write_bytes(data)
        tmp.replace(path)

    def claims(self):
        if self._claims is None:  # indexed once; `append` drops the index
            cs = [r for r in self.records if r["op"] == "claim"]
            pos = {}
            for i, c in enumerate(cs):
                pos.setdefault(c["key"], []).append(i)
            self._claims = (cs, pos)
        return list(self._claims[0])

    def claim_by_key(self, key):
        """The first claim with this key, as `next(c for c in claims() if c["key"] == key)` finds it."""
        self.claims()
        cs, pos = self._claims
        return cs[pos[key][0]] if key in pos else None

    def claims_with_keys(self, keys):
        """The claims whose key is in `keys`, in ledger order, as a scan of `claims()` lists them."""
        self.claims()
        cs, pos = self._claims
        return [cs[i] for i in sorted(i for k in set(keys) for i in pos.get(k, []))]

    def covers(self):
        """Candidate covers (`gp cover`): ledger records the spine view reads, never Kernel claims."""
        return [r for r in self.records if r["op"] == "cover"]

    def claim(self, label):
        for r in self.claims():
            if r["label"] == label:
                return r
        raise Refusal(f"no claim labelled {label!r}", "ledger", "-", "file it first with `gp claim`")

    def supports(self):
        """The accepted support of each claim key (one per claim; later supports supersede). A support
        filed by reference carries its receipt, read back from its checked file (`receipt_file`)."""
        stamp = (id(self.records), len(self.records))
        if self._supports is None or self._supports[0] != stamp:  # read once per command
            out = {}
            for r in self.records:
                if r["op"] == "support":
                    out[r["key"]] = r
            self._supports = (stamp, {k: dict(r, receipt=self.load_receipt(r)) if "receipt_ref" in r else r
                                      for k, r in out.items()})
        return dict(self._supports[1])

    def attempts(self, label=None):
        if self._refused is None:  # indexed once; `append` drops the index
            self._refused = {None: [r for r in self.records if r["op"] == "refused"]}
            for r in self._refused[None]:
                if r.get("label") is not None:
                    self._refused.setdefault(r["label"], []).append(r)
        return list(self._refused.get(label, []))


def matroid_file(campaign, name):
    """A matroid the statement lists, or one the campaign agent added under matroids/ with a source."""
    statement = json.loads((Path(campaign) / "campaign.json").read_text(encoding="utf-8"))
    for stage in statement["family"]:
        for m in stage.get("matroids", []):
            if m["name"] == name:
                return m
    added = Path(campaign) / "matroids" / f"{name}.json"
    if added.exists():
        m = json.loads(added.read_text(encoding="utf-8"))
        if m.get("name") != name or not m.get("source"):
            raise Refusal(f"{added.name} needs its own name and a cited source", "campaign statement: F1",
                          "-", "add \"name\" and \"source\" (tagged [VERIFY] until checked)")
        return m
    raise Refusal(f"matroid {name!r} is not in the campaign family", "campaign statement", "-",
                  f"use a listed matroid, or add matroids/{name}.json with a cited source")


def scope_of(args):
    if args.char is not None:
        return {"characteristic": args.char}
    if args.outside is not None:
        return {"outside": sorted({int(p) for p in args.outside.split(",") if p.strip()})}
    return {"char0": True}


def show_scope(scope):
    """A requested scope, as filed."""
    if "context" in scope:
        return CONTEXTS[scope["context"]]
    if "characteristic" in scope:
        return f"characteristic {scope['characteristic']}"
    if "outside" in scope:
        return "characteristic 0 and every prime" + (f" except {scope['outside']}" if scope["outside"] else "")
    return "characteristic 0"


def show_reach(r):
    """A computed reach from the profile (char0 flag plus a finite or cofinite prime set)."""
    if r is None:
        return "none"
    parts = ["0"] if r["char0"] else []
    if "finite" in r["primes"]:
        parts += [str(p) for p in r["primes"]["finite"]]
        return "{" + ", ".join(parts) + "}" if parts else "{}"
    ex = r["primes"]["cofinite"]
    return ("0 and " if r["char0"] else "") + "every prime" + (f" except {{{', '.join(map(str, ex))}}}" if ex else "")


# --- the profile ------------------------------------------------------------------------------

def surface(ledger, extra=None):
    """The ledger as the explicit statement surface, with one trial support optionally swapped in."""
    supports = ledger.supports()
    routed = routed_3b(ledger, extra)  # decided by gp_ledger3 (`surface3`), not by gp_ledger
    claims = []
    for c in ledger.claims():
        if c["key"] in routed:
            continue
        s = {"key": c["key"], "variables": c["system"]["variables"], "equations": c["system"]["equations"],
             "nonzero": c["system"]["nonzero"], "kind": c["kind"], "inputs": c["inputs"]}
        if c.get("target") is not None:
            s["target"] = c["target"]
        s.update({k: v for k, v in c["scope"].items() if k in ("characteristic", "outside")})
        receipt = (extra or {}).get(c["key"]) or (supports.get(c["key"]) or {}).get("receipt")
        if receipt:
            s.update(receipt)
        claims.append(s)
    plan = {"claims": claims, "requested": [c["key"] for c in ledger.claims() if c["key"] not in routed],
            "frames": frames(ledger)}
    if routed:
        plan["_3b"] = surface3(ledger, routed, extra)
    return plan


def frames(ledger):
    """Each matroid claim's matroid as index lines, for the Lean encoder to re-derive its system."""
    out = []
    for c in ledger.claims():
        if c["matroid"]:
            m, _ = encoder.canonical(matroid_file(ledger.dir, c["matroid"]))
            index = {e: i for i, e in enumerate(m["elements"])}
            out.append({"key": c["key"], "n": len(m["elements"]),
                        "lines": [[index[e] for e in line] for line in m["lines"]]})
    return out


FRAME_THEOREM = "GPBinding.Matroid.frame_iff"
UDG_FRAME_THEOREM = "GPBinding.UDG.udg_frame_iff"


def premise_state(out, claim):
    """ENCODING-FRAME is discharged for a claim whose system the Lean encoder re-derives exactly: matroid
    claims through gp_ledger's `frames`, graph-bound (--udg) claims through gp_ledger3's `udgFrames`."""
    equal = out.get("_frame_equal")
    if equal is None:  # built once per runner output; views call this once per claim
        equal = out["_frame_equal"] = {f["key"]: f["equal"] for f in out.get("frames", []) + out.get("udgFrames", [])}
    return "discharged" if equal.get(claim["key"]) else "OPEN"


def framed(c):
    """A claim whose ENCODING-FRAME a Lean encoder checks: a matroid claim or a graph-bound claim."""
    return bool(c.get("matroid") or c.get("udg"))


_built = False


def stale(exe=EXE):
    """The runner is older than some profile source (or missing): never run a stale checker."""
    if not exe.exists():
        return True
    built = exe.stat().st_mtime
    sources = [PROFILE / "lakefile.toml", PROFILE / "lake-manifest.json", ROOT / "phase2/lean/lakefile.toml"]
    sources += list((PROFILE / "GPProfile").rglob("*.lean")) + list((ROOT / "phase2/lean/GP50").rglob("*.lean"))
    return any(f.exists() and f.stat().st_mtime > built for f in sources)


def run_profile(plan, candidates=False, guard=False):
    global _built
    if "_3b" in plan:
        return run_mixed(plan, candidates)
    if not _built and stale():
        toolchain = ELAN_HOME / "toolchains" / (PROFILE / "lean-toolchain").read_text(
            encoding="utf-8").strip().replace("/", "--").replace(":", "---")
        env = dict(os.environ, PATH=str(toolchain / "bin") + os.pathsep + os.environ["PATH"])
        subprocess.run([str(toolchain / ("bin/lake" + (".exe" if os.name == "nt" else ""))), "build", "gp_ledger"],
                       cwd=PROFILE, env=env, check=True, capture_output=True)
        _built = True
    _built = True
    out = subprocess.run([str(EXE)] + (["--candidates"] if candidates else []) + (["--guard"] if guard else []),
                         input=json.dumps(plan),
                         capture_output=True, text=True, encoding="utf-8")
    if out.returncode != 0:
        raise RuntimeError(out.stderr.strip() or "gp_ledger failed")
    return json.loads(out.stdout)


# --- 3b claims (gp_ledger3) -------------------------------------------------------------------
#
# 3b claims (over ℝ, ℚ, semireal fields and number fields) are decided by `gp_ledger3`, which runs
# `Plan3.run` over the summed 3a + 3b profile. A claim goes there when its statement is 3b (it has a
# `family`), when its support is a 3b certificate or rule, or when its rule rests on such a claim.
# The 3a premises those claims use are copied in as `alg` claims. Every other claim stays with
# `gp_ledger`, exactly as before; a ledger with no 3b claim never runs `gp_ledger3`.

EXE3 = PROFILE / (".lake/build/bin/gp_ledger3" + (".exe" if os.name == "nt" else ""))
KUMMER = "KUMMER-INDEPENDENCE"
FRAME = "ENCODING-FRAME"
# Named premises a claim may carry (--premise), with what each asserts; all are OPEN until a checker is
# admitted. ENCODING-FRAME on a --system claim is the u(22) point-set / graph-embedding frame.
OPEN_PREMISES = {
    KUMMER: "the square classes{of} are independent in ℚ*/ℚ*²",
    # HW61 G-3: u(22) premises named for what they assert, each dischargeable on its own.
    "AMP-THM1": "u(n) for n <= 21 and the lists of extremal graphs are as Alexeev-Mixon-Parshall's Theorem 1 states",
    "GP74-NON-UD": "the graphs{of} among Globus-Parshall's 74 are not unit-distance graphs",
    "ENUM-COMPLETE": "the enumeration{of} lists every candidate graph",
    FRAME: "a point set is a unit-distance embedding of the claim's graph, and back",
}
FAMILIES3 = ("orderFree", "real", "realCover", "nf")
CERTS3 = ("alg_point", "sos", "ordered", "real_point", "nf", "rational_root", "root_cover", "case_tree")
RULES3 = ("k1a", "k1b", "narrow")
CONTEXTS = {"real": "the field ℝ", "semireal": "every semireal field", "rat_field": "the field ℚ"}
WHERE = {"real": "over ℝ", "semireal": "in any semireal field", "rat_field": "over ℚ"}
SIGNS = {1: 1, -1: -1, 0: 0, "1": 1, "-1": -1, "0": 0, ">0": 1, "<0": -1, "=0": 0, "+": 1, "-": -1}
SIGN_TEXT = {1: "> 0", -1: "< 0", 0: "= 0"}
_built3 = False

def receipt_of(supports, c, extra=None):
    """The receipt a fold offers a claim: the trial one, else its accepted support's."""
    return (extra or {}).get(c["key"]) or (supports.get(c["key"]) or {}).get("receipt")


def is_3b_receipt(r):
    return bool(r) and ((r.get("certificate") or {}).get("type") in CERTS3 or
                        (r.get("rule") or {}).get("type") in RULES3)


def routed_3b(ledger, extra=None):
    """The keys gp_ledger3 decides: 3b statements, 3b supports, and rules resting on either."""
    supports = ledger.supports()
    claims = ledger.claims()
    routed = {c["key"] for c in claims if c.get("family") in FAMILIES3 or is_3b_receipt(receipt_of(supports, c, extra))}
    if not routed:
        return routed
    deps = {c["key"]: (receipt_of(supports, c, extra) or {}).get("premises", []) for c in claims}
    grow = True
    while grow:
        new = {k for k, ps in deps.items() if k not in routed and any(p in routed for p in ps)}
        routed |= new
        grow = bool(new)
    return routed


def claim_surface3(c, receipt=None):
    """One claim in the 3b statement surface (`GPProfile.Real.LedgerRun3`)."""
    fam = c.get("family") or "alg"
    s = {"key": c["key"], "family": fam, "inputs": c["inputs"]}
    s.update(c["system"])
    if fam == "alg":
        s["kind"] = c["kind"]
        if c.get("target") is not None:
            s["target"] = c["target"]
        s.update({k: v for k, v in c["scope"].items() if k in ("characteristic", "outside")})
    elif fam != "nf":
        s["context"] = c["scope"]["context"]
        if fam != "realCover":
            s["kind"] = c["kind"]
    if receipt:
        s.update(receipt)
    return s


def surface3(ledger, routed, extra=None):
    """The routed claims and every premise they rest on, in ledger order."""
    supports = ledger.supports()
    claims = ledger.claims()
    by = {}
    for c in claims:
        by.setdefault(c["key"], c)
    need, stack = set(routed), list(routed)
    while stack:
        for p in (receipt_of(supports, by[stack.pop()], extra) or {}).get("premises", []):
            if p in by and p not in need:
                need.add(p)
                stack.append(p)
    return {"claims": [claim_surface3(c, receipt_of(supports, c, extra)) for k, c in by.items() if k in need],
            "requested": [k for k in by if k in routed], "udgFrames": udg_frames(c for k, c in by.items() if k in need)}


def udg_frames(claims):
    """Each graph-bound claim's graph, for gp_ledger3 to re-derive its system with the Lean encoder."""
    return [{"key": c["key"], "n": c["udg"].get("n"), "edges": c["udg"].get("edges"),
             "gauge": c["udg"].get("gauge") is True} for c in claims if isinstance(c.get("udg"), dict)]


def lake_build(target):
    toolchain = ELAN_HOME / "toolchains" / (PROFILE / "lean-toolchain").read_text(
        encoding="utf-8").strip().replace("/", "--").replace(":", "---")
    env = dict(os.environ, PATH=str(toolchain / "bin") + os.pathsep + os.environ["PATH"])
    subprocess.run([str(toolchain / ("bin/lake" + (".exe" if os.name == "nt" else ""))), "build", target],
                   cwd=PROFILE, env=env, check=True, capture_output=True)


def run_ledger3(plan):
    global _built3
    if not _built3 and stale(EXE3):
        lake_build("gp_ledger3")
    _built3 = True
    out = subprocess.run([str(EXE3)], input=json.dumps(plan), capture_output=True, text=True, encoding="utf-8")
    if out.returncode != 0:
        raise RuntimeError(out.stderr.strip() or "gp_ledger3 failed")
    return json.loads(out.stdout)


def run_mixed(plan, candidates=False):
    """gp_ledger on the 3a part, gp_ledger3 on the 3b part; one result, items keyed by claim."""
    plan = dict(plan)
    part3 = plan.pop("_3b")
    out = run_profile(plan, candidates) if plan["claims"] else \
        dict({"items": [], "widened": [], "earned": [], "frames": []}, **({"candidates": []} if candidates else {}))
    if out.get("error") or out.get("elaboration"):
        return out
    out3 = run_ledger3(part3)
    if out3.get("error"):
        return dict(out, error=humane(out3["error"]))
    keep = set(part3["requested"])
    return dict(out, items=out["items"] + [i for i in out3["items"] if i["key"] in keep],
                udgFrames=out3.get("udgFrames", []))


def context_of(args):
    return next((k for k in CONTEXTS if getattr(args, k, False)), None)


def claim_is_3b(args):
    return bool(context_of(args) or getattr(args, "nf", None) or getattr(args, "premise", None) or
                getattr(args, "goal", None) or getattr(args, "udg", None) or args.kind == "COVER")


def named_premises3(args):
    """`--premise NAME[=data]`: the names, and each one's data (Kummer: the rationals whose square classes it
    is about)."""
    names, notes = [], {}
    for p in args.premise or []:
        name, _, data = p.partition("=")
        if name not in OPEN_PREMISES:
            raise Refusal(f"unknown named premise {name}", "named premises", "-",
                          f"name one of {', '.join(OPEN_PREMISES)}")
        if name == FRAME and (args.matroid or getattr(args, "udg", None)):
            raise Refusal(f"{FRAME} comes with --{'matroid' if args.matroid else 'udg'}", "named premises", "-",
                          f"drop --premise {FRAME}")
        if name not in names:
            names.append(name)
        if data:
            notes[name] = [q.strip() for q in data.split(",") if q.strip()]
            if name == KUMMER and not all(re.fullmatch(r"-?\d+(/\d+)?", q) for q in notes[name]):
                raise Refusal(f"the square classes must be exact rationals: {data}", "named premises", "-",
                              f"write --premise {KUMMER}=2,3,5/7")
    return names, notes


def goal_of(ledger):
    """The campaign statement's DECIDE goal, if it has one (a dict with "kind": "DECIDE")."""
    statement = json.loads((ledger.dir / "campaign.json").read_text(encoding="utf-8"))
    goal = statement.get("goal")
    return goal if isinstance(goal, dict) and goal.get("kind") == "DECIDE" else None


def check_goal_side(ledger, args, family, scope, kind, udg=None):
    """`--goal yes` files a claim as the goal statement Q; `--goal no` as its negation. Shape alone is not
    meaning: a claim stands for its side only through an admitted bridge (`goal_bridge`), so an unbridged
    goal claim is refused at filing (HW61 G-1). The frame is checked by the filing's own elaboration run."""
    goal = goal_of(ledger)
    if goal is None:
        raise Refusal("the campaign statement has no DECIDE goal", "campaign statement", "-",
                      'the statement needs "goal": {"kind": "DECIDE", "name": ..., "statement": ..., ...}')
    name = goal.get("name", "the goal")
    over_r = scope.get("context") == "real"
    reaches_r = scope.get("context") in ("real", "semireal") or (family is None and "characteristic" not in scope)
    if args.goal == "yes" and not (kind == "NONEMPTY" and over_r):
        raise Refusal(f"{name} is shown by a point over ℝ", "DECIDE goal", show_scope(scope),
                      "file it as --kind NONEMPTY --real")
    if args.goal == "no" and not (kind == "EMPTY" and reaches_r):
        raise Refusal(f"not {name} is shown by an exclusion that reaches ℝ", "DECIDE goal", show_scope(scope),
                      "file it as --kind EMPTY with --real, --semireal or --char0")
    gap = goal_bridge({"goal": args.goal, "udg": udg, "kind": kind, "scope": scope}, goal)
    if gap:
        raise Refusal(gap, "DECIDE goal", show_scope(scope), GOAL_FIX[args.goal])


# HW61 G-1, G-2. A goal side is decided only through an admitted bridge from held claims to the goal's
# meaning Q(n, m) := ∃ P : Finset ℝ², P.card = n ∧ m ≤ unitDistNum P, with (n, m) the goal's "udg" parameters.
# - Q: a held graph-bound (--udg) NONEMPTY claim over ℝ whose system the Lean encoder re-derives
#   (`udg_frame_iff`), on n vertices with at least m edges (`realize_sound`; together `udg_realize`).
# - not Q: the spine view (`spine_verdict`): a cover (`gp cover`, CoverComplete n m L) whose every candidate
#   has a held, frame-equal --udg EMPTY claim over ℝ (`candidate_isEmpty`), then `spine_sound`. A claim
#   filed --goal no never decides.
# The Python join (graph matching, the n and m comparisons, the exhaustive-cover check) is trusted (TCB.md).
GOAL_FIX = {"yes": "file the realization with --udg GRAPH --kind NONEMPTY --real, for a graph on the goal's n "
                   "vertices with at least its m edges",
            "no": "file each exclusion without --goal (--udg GRAPH --kind EMPTY --real); not Q is held only "
                  "through a candidate cover (`gp cover`)"}
SPINE = "GPBinding.UDG.spine_sound"
YES_BRIDGE = "GPBinding.UDG.udg_frame_iff, GPBinding.UDG.realize_sound"


def goal_udg(goal):
    """The goal's structured parameters (n points, at least m unit distances), or None."""
    u = (goal or {}).get("udg")
    if isinstance(u, dict) and all(type(u.get(k)) is int and u[k] >= 0 for k in ("n", "m")):
        return u["n"], u["m"]
    return None


def canon(g):
    """A graph record as (n, edges) when it is canonical: edges i < j < n, sorted, no repeats; else None."""
    if not isinstance(g, dict) or type(g.get("n")) is not int or g["n"] < 0 or not isinstance(g.get("edges"), list):
        return None
    edges = []
    for e in g["edges"]:
        if not (isinstance(e, list) and len(e) == 2 and all(type(v) is int for v in e) and 0 <= e[0] < e[1] < g["n"]):
            return None
        edges.append((e[0], e[1]))
    return (g["n"], tuple(edges)) if edges == sorted(set(edges)) else None


def graph_sha(n, edges):
    """A graph's identity: SHA-256 of its canonical JSON {"edges": [[i, j], ...], "n": n}."""
    return sha(json.dumps({"edges": [list(e) for e in edges], "n": n}, sort_keys=True,
                          separators=(",", ":")).encode("utf-8"))


def graph_text(g):
    c = canon(g)
    if c is None:
        return "a malformed graph record"
    name = f"{g['name']} " if g.get("name") else ""
    return f"{name}({c[0]} vertices, {len(c[1])} edges, sha256 {graph_sha(*c)[:12]})"


def goal_bridge(claim, goal=None, out=None):
    """None when a goal claim stands for its side; otherwise why it does not. Only Q has a claim-level bridge;
    `out` (the runner's output) supplies the frame check, which filing does in its own elaboration run."""
    if claim.get("goal") == "no":
        return ("one exclusion cannot show not Q: not Q is held only by the spine rule, a candidate cover "
                "(`gp cover`) with a held exclusion over ℝ for every candidate")
    if not claim.get("udg"):
        return ("a --system claim carries no bridge to Q: Q needs a graph-bound claim (--udg) whose "
                "unit-distance frame the Lean encoder re-derives")
    params = goal_udg(goal)
    if params is None:
        return 'the goal states no graph parameters ("udg": {"n": ..., "m": ...}), so no claim bridges to it'
    if claim.get("kind") != "NONEMPTY" or (claim.get("scope") or {}).get("context") != "real":
        return "Q is shown by a NONEMPTY claim over ℝ"
    g = canon(claim["udg"])
    if g is None:
        return "the claim's graph record is not canonical"
    n, m = params
    if g[0] != n:
        return f"the graph has {g[0]} vertices; Q is about {n} points"
    if len(g[1]) < m:
        return f"the graph has {len(g[1])} edges; Q needs at least {m} unit distances"
    if out is not None and premise_state(out, claim) != "discharged":
        return "the claim's system is not the Lean encoder's for its graph (ENCODING-FRAME unequal)"
    return None


def read_graph(spec, what="graph"):
    """A graph: a graph6 string, a file holding one graph6 line or JSON {n, edges}, or such JSON itself."""
    text = spec if isinstance(spec, str) else None
    if isinstance(spec, str):
        try:
            if Path(spec).is_file():
                text = Path(spec).read_text(encoding="utf-8")
        except (OSError, ValueError):
            pass
    try:
        g = spec if isinstance(spec, dict) else (json.loads(text) if text.strip().startswith("{") else None)
        if g is None:
            lines = [l.strip() for l in text.splitlines() if l.strip()]
            if len(lines) != 1:
                raise ValueError("a graph is one graph6 line")
            n, edges = udg_encoder.graph6_decode(lines[0])
            g = {"name": lines[0], "n": n, "edges": edges}
        n, edges = udg_encoder.canonical(g)
    except (ValueError, KeyError, TypeError) as e:
        raise Refusal(f"cannot read the {what}: {e}", "graph surface", "-",
                      'give a graph6 string, or JSON {"n": 4, "edges": [[0, 1], ...]}')
    return {"name": g.get("name"), "n": n, "edges": [list(e) for e in edges]}


def read_json(path, what):
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, ValueError) as e:
        raise Refusal(f"cannot read the {what} file: {e}", "statement surface", "-", f"write {path} as JSON")


def signs3(atoms):
    out = []
    for a in atoms:
        if not (isinstance(a, list) and len(a) == 2 and isinstance(a[1], (int, str)) and a[1] in SIGNS):
            raise Refusal(f"a sign condition is [polynomial, sign], not {a!r}", "3b statement surface", "-",
                          'write ["x - 1", 1] (or ">0"), ["y", -1] (or "<0"), ["z", 0] (or "=0")')
        out.append([a[0], SIGNS[a[1]]])
    return out


def system3(raw, cover=False):
    """A real system: variables, equations, nonzero guards, sign conditions (and a cover's branches)."""
    if not isinstance(raw, dict) or "variables" not in raw:
        raise Refusal("the system file needs variables", "3b statement surface", "-",
                      'write {"variables": [...], "equations": [...], "nonzero": [...], "signs": [...]}')
    system = {"variables": raw["variables"], "equations": raw.get("equations", []), "nonzero": raw.get("nonzero", [])}
    if raw.get("signs"):
        system["signs"] = signs3(raw["signs"])
    if cover:
        system["branches"] = [{"equations": b.get("equations", []), "nonzero": b.get("nonzero", []),
                               "signs": signs3(b.get("signs", []))} for b in raw.get("branches", [])]
    return system


def cmd_claim3(ledger, args):
    """File a 3b claim, or a 3a claim carrying a named premise."""
    if any(c["label"] == args.label for c in ledger.claims() + ledger.covers()):
        raise Refusal(f"label {args.label!r} is taken", "ledger", "-", "choose a new label")
    premises, notes = named_premises3(args)
    ctx = context_of(args)
    family, udg = None, None
    if args.matroid and (ctx or args.kind == "COVER"):
        raise Refusal("a matroid's real claims are filed as systems", "3b statement surface", CONTEXTS.get(ctx, "-"),
                      "encode it with tools/encode-matroid.py and file it with --system")
    if args.udg:
        if not ctx:
            raise Refusal("a graph-bound claim is a 3b claim over a field", "3b statement surface",
                          show_scope(scope_of(args)), "claim it with --real (or --semireal, --rat-field)")
        if args.kind not in ("EMPTY", "NONEMPTY") or args.target:
            raise Refusal(f"over {CONTEXTS[ctx]} a claim is EMPTY or NONEMPTY", "3b statement kinds", CONTEXTS[ctx],
                          "use --kind EMPTY or --kind NONEMPTY, without --target")
        if args.kind == "NONEMPTY" and ctx != "real":
            raise Refusal(f"no admitted evidence gives a point in {CONTEXTS[ctx]}", "3b evidence", CONTEXTS[ctx],
                          "claim the embedding over ℝ (--real)")
        g = read_graph(args.udg)
        enc = udg_encoder.encode(g, args.gauge)
        system = {k: enc[k] for k in ("variables", "equations", "nonzero")}
        udg = {"n": g["n"], "edges": g["edges"], "gauge": bool(args.gauge), "sha256": graph_sha(g["n"], g["edges"])}
        if g.get("name"):
            udg["name"] = g["name"]
        family, scope, kind = "orderFree", {"context": ctx}, args.kind
        premises = [FRAME] + premises
    elif args.nf:
        if args.kind != "NONEMPTY" or not args.char0:
            raise Refusal("a number-field point is a NONEMPTY claim at characteristic 0", "3b statement surface",
                          "-", "use --kind NONEMPTY --char0")
        raw = read_json(args.nf, "number-field point")
        missing = [k for k in ("symbol", "minimal_polynomial", "variables", "point") if k not in raw]
        if missing:
            raise Refusal(f"the number-field point needs {', '.join(missing)}", "3b statement surface", "-",
                          'write {"symbol": "t", "minimal_polynomial": "t^2 - 2", "variables": [...], '
                          '"equations": [...], "nonzero": [...], "point": {"x": "t", ...}}')
        system = {k: raw[k] for k in ("symbol", "minimal_polynomial", "variables", "point")}
        system.update(equations=raw.get("equations", []), nonzero=raw.get("nonzero", []))
        family, scope, kind = "nf", {"char0": True}, "NONEMPTY"
    elif args.kind == "COVER":
        if ctx != "real":
            raise Refusal("a selected-root cover is a claim over ℝ", "3b statement surface", "-", "add --real")
        system = system3(read_json(args.system, "system"), cover=True)
        if not system["branches"]:
            raise Refusal("a cover needs branches", "3b statement surface", CONTEXTS[ctx],
                          'add "branches": [{"equations": [...], "signs": [...]}, ...]')
        family, scope, kind = "realCover", {"context": ctx}, "COVER"
    elif ctx:
        if args.kind not in ("EMPTY", "NONEMPTY") or args.target:
            raise Refusal(f"over {CONTEXTS[ctx]} a claim is EMPTY or NONEMPTY", "3b statement kinds", CONTEXTS[ctx],
                          "use --kind EMPTY or --kind NONEMPTY, without --target")
        system = system3(read_json(args.system, "system"))
        family = "real" if system.get("signs") else "orderFree"
        if family == "real" and ctx != "real":
            raise Refusal("sign conditions are read only over ℝ", "3b scopes", CONTEXTS[ctx],
                          "claim it with --real, or drop the sign conditions")
        if args.kind == "NONEMPTY" and ctx != "real":
            raise Refusal(f"no admitted evidence gives a point in {CONTEXTS[ctx]}", "3b evidence", CONTEXTS[ctx],
                          "claim the point over ℝ (--real); a rational point is the 3a claim NONEMPTY --char0")
        scope, kind = {"context": ctx}, args.kind
    else:  # a 3a claim with a named premise, filed as `claim` files it
        if args.kind not in KINDS:
            raise Refusal(f"unknown kind {args.kind}", "statement kinds", "-", f"one of {', '.join(KINDS)}")
        scope, kind = scope_of(args), args.kind
        if args.matroid:
            enc = encoder.encode(matroid_file(ledger.dir, args.matroid))
            system = {k: enc[k] for k in ("variables", "equations", "nonzero")}
            inputs = [f"encoding:{enc['digest']}"]
            premises = [enc["premise"]["name"]] + premises
        else:
            raw = read_json(args.system, "system")
            system = {k: raw[k] for k in ("variables", "equations", "nonzero")}
    if udg:
        inputs = [f"udg:{udg['sha256']}"]
    elif not args.matroid:
        inputs = [f"system:{sha(json.dumps(system, sort_keys=True).encode())}"]
    bad = decimals(system)
    if bad:
        raise Refusal(f"decimals are not exact numbers: {', '.join(bad[:3])}", "exact statements", show_scope(scope),
                      "write each value as an integer or a fraction p/q")
    if args.goal:
        check_goal_side(ledger, args, family, scope, kind, udg)
    body = {"label": args.label, "matroid": args.matroid, "system": system, "kind": kind, "target": args.target,
            "scope": scope, "inputs": inputs, "named_premises": premises}
    body.update({k: v for k, v in (("family", family), ("goal", args.goal), ("premise_notes", notes), ("udg", udg))
                 if v})
    key = new_key(ledger, body)  # the merge guard's content-hashed, branch-safe key
    record = dict({"op": "claim", "key": key}, **body)
    if family:
        out = run_ledger3({"claims": [claim_surface3(record)], "requested": [key], "udgFrames": udg_frames([record])})
        if out.get("error"):
            raise Refusal(f"the claim does not elaborate: {humane(out['error'])}", "3b statement surface",
                          show_scope(scope), "fix the file: declared variables, exact polynomials, signs -1, 0 or 1")
        if udg and not all(f["equal"] for f in out.get("udgFrames", [])) or udg and not out.get("udgFrames"):
            raise Refusal("the encoded system is not the Lean encoder's for this graph", "ENCODING-FRAME",
                          show_scope(scope), "report to the builder: tools/encode-udg.py and GPProfile.UDG disagree")
    ledger.append(record)
    note = "".join(f" [premise {p}: OPEN]" for p in premises if p != FRAME or not (args.matroid or udg))
    if udg:
        note += f" [graph {graph_text(udg)}; {FRAME}: equal to the Lean encoder's]"
    print(f"claim {args.label} (key {key}) filed: {kind} at {show_scope(scope)}{note}; open")


# --- 3b views ---

def conditions(c):
    """A claim's conditions in words, or their counts when that would be long."""
    s = c["system"]
    eqs, gs, sg = s.get("equations", []), s.get("nonzero", []), s.get("signs", [])
    text = ", ".join([f"{e} = 0" for e in eqs] + [f"{g} ≠ 0" for g in gs] + [f"{p} {SIGN_TEXT[v]}" for p, v in sg])
    if len(text) <= 100:
        return text or "no conditions"
    parts = [f"{n} {w}" for n, w in ((len(eqs), "equations"), (len(gs), "nonzero conditions"),
                                     (len(sg), "sign conditions")) if n]
    return ", ".join(parts) + f" in {len(s['variables'])} variables"


def meaning3(c):
    """What a held claim says, in the claim's own terms."""
    fam, k, conds = c.get("family"), c["kind"], conditions(c)
    if fam in ("orderFree", "real"):
        where = WHERE[c["scope"]["context"]]
        return f"no point {where} with {conds}" if k == "EMPTY" else f"has a point {where} with {conds}"
    if fam == "realCover":
        return f"every point over ℝ with {conds} satisfies one of its {len(c['system']['branches'])} branches"
    if fam == "nf":
        s = c["system"]
        pt = ", ".join(f"{v} = {s['point'][v]}" for v in s["variables"])
        return (f"{s['minimal_polynomial']} is irreducible over ℚ and, at every root {s['symbol']} of it in a field "
                f"of characteristic 0, the point ({pt}) satisfies {conds}")
    scope = show_scope(c["scope"])
    if k == "EMPTY":
        return f"no point over any field of {scope} with {conds}"
    if k == "NONEMPTY":
        return f"has a point in every field of {scope} with {conds}"
    if k == "NOT_IN_IDEAL" and c.get("target") in ("1", None):
        closure = " (over ℂ, for instance)" if "characteristic" not in c["scope"] else ""
        return f"has a point over an algebraically closed field of {scope}{closure} with {conds}"
    return f"{k} {c.get('target')} on {conds}"


def premise_states(out, c):
    """Each named premise and its state: ENCODING-FRAME discharged when the Lean encoder re-derives a
    matroid claim's system (else OPEN); every other named premise OPEN (no admitted checker yet)."""
    return [(p, premise_state(out, c) if p == FRAME else "OPEN") for p in c["named_premises"]]


def conditional(ledger, out):
    """Per claim key: the OPEN premises it rests on, its own and those of every claim its support's rule
    uses. A claim held modulo one of them is conditional and cannot show the goal held."""
    if "_conditional" not in out:
        cond = {c["key"]: {p for p, st in premise_states(out, c) if st == "OPEN"} for c in ledger.claims()}
        deps = {k: (s.get("receipt") or {}).get("premises", []) for k, s in ledger.supports().items()}
        deps = {k: ps for k, ps in deps.items() if ps and k in cond}
        grow = bool(deps)
        while grow:
            grow = False
            for k, ps in deps.items():
                extra = set().union(*(cond.get(q, set()) for q in ps)) - cond[k]
                if extra:
                    cond[k] |= extra
                    grow = True
        out["_conditional"] = cond
    return out["_conditional"]


def premise_tag(out, c):
    """The status row's named premises; with ENCODING-FRAME alone this is the 3a row's tag."""
    parts = [f"premise {FRAME}: {premise_state(out, c)}"] if FRAME in c["named_premises"] else []
    parts += [f"premise {p}: OPEN" for p in c["named_premises"] if p != FRAME]
    return f" [{'; '.join(parts)}]"


def shown3(c, item, cond):
    """Claims the 3b section shows: 3b-decided ones, and 3a ones conditional on a 3b-era OPEN premise."""
    return "family" in item or bool(cond - {FRAME}) or (not c["matroid"] and bool(cond))


def status3(ledger, out, items):
    """The 3b section of `status`: held 3b claims (and conditional ones) in words, with what they rest on."""
    cond = conditional(ledger, out)
    shown = [c for c in ledger.claims() if shown3(c, items[c["key"]], cond[c["key"]])]
    if not shown:
        return
    held = [c for c in shown if items[c["key"]]["held"]]
    modulo = sorted(set().union(*(cond[c["key"]] for c in held))) if held else []
    print("\nReal and number-field claims (held claims only" +
          (f"; some results modulo the OPEN premise{'s' if len(modulo) > 1 else ''} {', '.join(modulo)}):"
           if modulo else "):"))
    for c in held:
        tail = f" (modulo {', '.join(sorted(cond[c['key']]))})" if cond[c["key"]] else ""
        print(f"  {meaning3(c)} ({c['label']}){tail}")
    if not held:
        print("  none held yet")


UNWARRANTED = "COVER-COMPLETENESS (no warrant)"
EXHAUSTIVE_LIMIT = 100000


def exhaustive(n, m, cands):
    """True when the candidates include every labelled graph on n vertices with at least m edges, so the cover
    is complete by `coverComplete_of_all`; False when one is missing; None when there are more than
    EXHAUSTIVE_LIMIT such graphs to check (then completeness needs a named premise such as ENUM-COMPLETE)."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    if sum(math.comb(len(pairs), k) for k in range(m, len(pairs) + 1)) > EXHAUSTIVE_LIMIT:
        return None
    have = {e for cn, e in cands if cn == n}
    return all(es in have for k in range(m, len(pairs) + 1) for es in itertools.combinations(pairs, k))


def exclusion_gap(out, items, c):
    """Why a graph-bound claim does not exclude its graph over ℝ for the spine rule, or None."""
    if c["kind"] != "EMPTY":
        return f"{c['kind']}, not EMPTY"
    if c["scope"].get("context") != "real":
        return (f"held at {show_scope(c['scope'])}, not over ℝ (narrow it: rule narrow)"
                if items[c["key"]]["held"] else f"filed at {show_scope(c['scope'])}, not over ℝ")
    if not items[c["key"]]["held"]:
        return "not held"
    if premise_state(out, c) != "discharged":
        return "its system is not the Lean encoder's for the graph (ENCODING-FRAME unequal)"
    return None


def cover_join(ledger, out, items, cover):
    """One cover's join (trusted Python, TCB.md): each candidate's best exclusion, the completeness warrant,
    and the OPEN premises a not-Q verdict through this cover rests on."""
    cond = conditional(ledger, out)
    graphs = [c for c in ledger.claims() if isinstance(c.get("udg"), dict)]
    rows = []
    for g in cover.get("candidates", []):
        cg = canon(g)
        if cg is not None and cg[0] != cover.get("n"):
            cg = None
        same = [c for c in graphs if cg is not None and canon(c["udg"]) == cg]
        ok = [c for c in same if exclusion_gap(out, items, c) is None]
        best = min(ok, key=lambda c: len(cond[c["key"]]), default=None)
        rows.append({"graph": g, "canon": cg, "exclusion": best, "others": [c for c in same if c not in ok]})
    exh = exhaustive(cover["n"], cover["m"], [r["canon"] for r in rows if r["canon"]]) \
        if type(cover.get("n")) is int and type(cover.get("m")) is int else None
    opens = list(cover.get("named_premises", []))
    if not exh and not opens:
        opens.append(UNWARRANTED)
    inherited = set().union(*(cond[r["exclusion"]["key"]] for r in rows if r["exclusion"])) - set(opens)
    return {"rows": rows, "exhaustive": exh, "open": opens + sorted(inherited),
            "missing": [r for r in rows if not r["exclusion"]]}


def spine_verdict(ledger, out, items, goal):
    """not Q through the spine rule: ("held" | "conditional" | "open" | None, cover, join, mismatched covers)."""
    params = goal_udg(goal)
    covers = ledger.covers()
    if params is None:
        return None, None, None, covers
    match = [cv for cv in covers if (cv.get("n"), cv.get("m")) == params]
    other = [cv for cv in covers if cv not in match]
    joins = [(cv, cover_join(ledger, out, items, cv)) for cv in match]
    for state, test in (("held", lambda j: not j["missing"] and not j["open"]),
                        ("conditional", lambda j: not j["missing"]), ("open", lambda j: True)):
        for cv, j in sorted(joins, key=lambda x: len(x[1]["open"])):
            if test(j):
                return state, cv, j, other
    return None, None, None, other


def status_goal(ledger, out, items):
    """The DECIDE goal: Q by a held, bridged goal claim on no OPEN premise; not Q only by the spine rule."""
    goal = goal_of(ledger)
    if goal is None:
        return
    cond = conditional(ledger, out)
    name = goal.get("name", "Q")
    print(f"Goal: DECIDE {name}" + (f" := {goal['statement']}" if goal.get("statement") else ""))
    if goal.get("readings"):
        print(f"  readings: {'; '.join(goal['readings'])}")
    firm_side = {}
    negation = f"not {name}" + (f" ({goal['negation']})" if goal.get("negation") else "")
    for side, title in (("yes", name), ("no", negation)):
        cs = [c for c in ledger.claims() if c.get("goal") == side and items[c["key"]]["held"]]
        bridged = [c for c in cs if not goal_bridge(c, goal, out)]
        firm = [c for c in bridged if not cond[c["key"]]]
        firm_side[side] = bool(firm)
        if side == "no":
            state, cv, j, other = spine_verdict(ledger, out, items, goal)
            firm_side["no"] = state == "held"
            for o in other:
                print(f"  (cover {o['label']} is for n = {o.get('n')}, m = {o.get('m')}; " +
                      ("the goal states no graph parameters" if goal_udg(goal) is None else
                       "not the goal's n = {}, m = {}".format(*goal_udg(goal))) + "; it does not count)")
            if state == "held":
                print(f"  {title}: held by cover {cv['label']} ({SPINE}; every candidate excluded over ℝ)")
                continue
            if state == "conditional":
                print(f"  {title}: conditional on {', '.join(j['open'])} ({SPINE}; cover {cv['label']}), "
                      f"so not held")
                continue
        if firm:
            print(f"  {title}: held by {', '.join(c['label'] for c in firm)} ({YES_BRIDGE})")
        elif cs and not bridged:
            print(f"  {title}: not held ({', '.join(c['label'] for c in cs)} held, but unbridged: "
                  f"{goal_bridge(cs[0], goal, out)})")
        elif cs:
            print(f"  {title}: conditional only (" + "; ".join(
                f"{c['label']} modulo {', '.join(sorted(cond[c['key']]))}" for c in cs) + f"), so not held")
        elif side == "no" and state == "open":
            print(f"  {title}: open (cover {cv['label']}: no held exclusion over ℝ for " +
                  ", ".join(graph_text(r["graph"]) for r in j["missing"]) + ")")
        else:
            print(f"  {title}: not held")
    verdict = ("CONFLICT between held goal claims (report to the builder)" if firm_side["yes"] and firm_side["no"]
               else f"decided: {name}" if firm_side["yes"] else f"decided: not {name}" if firm_side["no"]
               else "undecided")
    print(f"  verdict: {verdict}\n")


def explain_cover(ledger, out, items, cv):
    """`explain` on a cover: its candidates with each exclusion's state, its premises, and the theorems."""
    j = cover_join(ledger, out, items, cv)
    goal = goal_of(ledger)
    print(f"cover {cv['label']}: CoverComplete {cv.get('n')} {cv.get('m')} L, L = {len(cv.get('candidates', []))} "
          f"candidate graph{'s' if len(cv.get('candidates', [])) != 1 else ''} (GPBinding.UDG.CoverComplete)")
    print(f"  means: every set of {cv.get('n')} points in the plane with at least {cv.get('m')} unit distances "
          f"contains a unit-distance copy of a candidate")
    if j["exhaustive"]:
        print("  completeness: exhaustive, every labelled graph on n vertices with at least m edges is listed "
              "(GPBinding.UDG.coverComplete_of_all)")
    elif cv.get("named_premises"):
        print(f"  completeness: rests on the named premises below "
              f"({'not exhaustive' if j['exhaustive'] is False else 'too many graphs to check exhaustively'})")
    else:
        print(f"  completeness: no warrant ({UNWARRANTED} is OPEN)")
    for p in cv.get("named_premises", []):
        data = (cv.get("premise_notes") or {}).get(p)
        what = OPEN_PREMISES[p].format(of=f" of {', '.join(data)}" if data else "")
        print(f"  premise {p}: OPEN ({what}; no admitted checker yet)")
    for r in j["rows"]:
        print(f"  candidate {graph_text(r['graph'])}:")
        if r["canon"] is None:
            print(f"    not a canonical graph on {cv.get('n')} vertices: it cannot be excluded")
        c = r["exclusion"]
        if c:
            cond = sorted(conditional(ledger, out)[c["key"]])
            print(f"    excluded by {c['label']}: held, EMPTY over ℝ, ENCODING-FRAME discharged "
                  f"(GPBinding.UDG.candidate_isEmpty, {UDG_FRAME_THEOREM}, GPBinding.UDG.holds_iff_holdsE_udg)" +
                  (f"; modulo {', '.join(cond)}" if cond else ""))
        elif r["canon"] is not None:
            print("    no held exclusion over ℝ")
        for o in r["others"]:
            print(f"    {o['label']} does not count: {exclusion_gap(out, items, o)}")
    for label in cv.get("supports", []):
        c = next((x for x in ledger.claims() if x["label"] == label), None)
        st = "missing" if c is None else ("held" if items[c["key"]]["held"] else "not held")
        print(f"  supports (shown, not used by the rule): {label} ({st})")
    print(f"  rule: {SPINE} (CoverComplete n m L and no candidate embeds give not Q(n, m)), each candidate by "
          f"GPBinding.UDG.candidate_isEmpty")
    params = goal_udg(goal)
    if params is None:
        print("  goal: the campaign goal states no graph parameters; this cover decides nothing")
    elif (cv.get("n"), cv.get("m")) != params:
        print("  goal: n = {}, m = {}; this cover is for other parameters and does not count".format(*params))
    elif j["missing"]:
        print(f"  for the goal: open, {len(j['missing'])} candidate{'s' if len(j['missing']) > 1 else ''} not excluded")
    elif j["open"]:
        print(f"  for the goal: conditional on {', '.join(j['open'])}")
    else:
        print("  for the goal: held, not Q, with no OPEN premise")


def case_tree_meaning(cert):
    """What a case-tree receipt rests on, in words (`explain`)."""
    counts = {"split": 0, "unit": 0, "collision": 0, "ordered": 0, "rhombi": 0}
    stack = [cert.get("tree") or {}]
    while stack:
        node = stack.pop()
        if "collision" in node:
            counts["collision"] += 1
            counts["rhombi"] += len(node["collision"].get("rhombi", []))
        elif "unit" in node:
            counts["unit"] += 1
            counts["rhombi"] += len((node["unit"] or {}).get("rhombi", []))
            stack += [node["then"]] if isinstance(node.get("then"), dict) else []
        elif "ordered" in node:
            counts["ordered"] += 1
        else:
            counts["split"] += 1
            stack += [node[k] for k in ("zero", "nonzero", "neg", "pos") if isinstance(node.get(k), dict)]
    units = (f", {counts['unit']} L1b unit steps (each derives the unit edge p_u p_v from rhombus relations and a "
             f"cited edge p_a p_b, unitOk_real)" if counts["unit"] else "")
    return (f"a case tree with {counts['split']} splits{units}, {counts['collision']} L1a collision leaves "
            f"({counts['rhombi']} rhombus relations) and {counts['ordered']} ordered leaves; each rhombus relation "
            f"is P1 (proved in the binding, rhombus_relation) at four cited unit edges and two cited diagonal "
            f"distinctness guards of the system; no OPEN premise")


def explain3_head(ledger, out, c, i, pad):
    cond = conditional(ledger, out)[c["key"]]
    if shown3(c, i, cond):
        print(f"{pad}  means: {meaning3(c)}")
    for p in c["named_premises"]:
        if p != FRAME or not framed(c):
            data = (c.get("premise_notes") or {}).get(p)
            what = OPEN_PREMISES[p].format(of=f" of {', '.join(data)}" if data else "")
            print(f"{pad}  premise {p}: OPEN ({what}; no admitted checker yet)")
    inherited = sorted(cond - set(c["named_premises"]))
    if inherited:
        print(f"{pad}  conditional: rests on claims modulo the OPEN premise{'s' if len(inherited) > 1 else ''} "
              f"{', '.join(inherited)}")
    if c.get("goal"):
        goal = goal_of(ledger) or {}
        gap = goal_bridge(c, goal, out)
        print(f"{pad}  filed as {'' if c['goal'] == 'yes' else 'not '}{goal.get('name', 'the goal')}" +
              (f" (unbridged: {gap})" if gap else " (conditional: it cannot show the goal held)" if cond else
               f" (bridged: {YES_BRIDGE})"))


FAIL_WORDS = {
    "identity": "the exact identity leaves a nonzero residual", "notCanonical": "a polynomial is not canonical",
    "cofactorCount": "one cofactor per equation (ordered: then per zero sign condition)",
    "posCount": "one exponent per strict sign condition", "posIndex": "a cone term names a sign condition that is not strict",
    "arity": "a polynomial has the wrong variables", "budget": "the certificate exceeds the degree or size budget",
    "negativeWeight": "a square has a negative weight", "notSymmetric": "a Gram matrix is not symmetric or not square",
    "notPSD": "a Gram matrix is not positive semidefinite", "kind": "the claim is not EMPTY",
    "badSign": "a sign is not -1, 0 or 1", "guardIndex": "a selected guard index is past the system's guards"}
SCOPE3_RE = re.compile(r'alg \[(true|false),"(finite|cofinite)",\[([\d,]*)\]\]')


def humane(text):
    """Profile scope names and failure constructors, in words."""
    def scope(m):
        ps = [p for p in m.group(3).split(",") if p]
        if m.group(2) == "cofinite":
            return show_scope({"outside": [int(p) for p in ps]})
        return "characteristic " + ", ".join((["0"] if m.group(1) == "true" else []) + ps)
    text = SCOPE3_RE.sub(scope, text or "")
    text = text.replace("GPProfile.Real.OrdFail.block ", "a cone block: ")
    return re.sub(r"GPProfile\.Real\.(?:SOSFail|OrdFail)\.(\w+)", lambda m: FAIL_WORDS.get(m.group(1), m.group(1)), text)


FIX3 = {
    "sos": "recompute (guards)^(2k) + Σ w·p² + Σ cofactor·equation = 0 exactly (with `guards`, only the selected "
           "guards, by index); SOS proves EMPTY in every semireal field or over ℝ, for systems without sign conditions",
    "ordered": "recompute the ordered identity exactly (cofactors for the equations, then the zero sign conditions; one "
               "exponent per strict sign condition; with `guards`, only the selected guards); it proves EMPTY over ℝ "
               "only",
    "real_point": "the interval must hold exactly one root of the polynomial, and every condition must have its sign "
                  "there; a real point proves NONEMPTY over ℝ",
    "alg_point": "every equation must vanish modulo the polynomial and every guard be coprime to it; alg_point proves "
                 "NOT_IN_IDEAL --target 1 at characteristic 0 only",
    "nf": "the minimal polynomial must pass the rational-root test (degree 2 or 3), equations must reduce to 0 and "
          "guards be invertible modulo it",
    "rational_root": "one variable and an integer equation with no rational root; it proves EMPTY over ℚ only",
    "root_cover": "the interval must isolate the parent's root (Descartes) and one branch must hold at that root",
    "case_tree": "every split needs all its branches and every leaf must close its branch: an L1a collision cites "
                 "each rhombus's four unit edges and both diagonal distinctness guards (injectivity is never "
                 "assumed), and its weighted relations must sum exactly to p_u - p_v for a guarded pair; an L1b "
                 "unit step's relations must sum exactly to (p_u - p_v) - sign·(p_a - p_b) with sign ±1 and (a, b) "
                 "an edge of the branch; a case tree proves EMPTY over ℝ only",
}
SUPPORT_TYPE = {"SOS receipt": "sos", "ordered Positivstellensatz receipt": "ordered", "point receipt": "real_point",
                "algPoint receipt": "alg_point", "number-field receipt": "nf", "rational-root receipt": "rational_root",
                "selected-root cover receipt": "root_cover", "case-tree receipt": "case_tree"}
RULE_FIX3 = {
    "narrowing": "narrowing keeps the statement and narrows only from every semireal field to ℝ or ℚ; nothing "
                 "narrows from a characteristic (ℂ) scope into ℝ: certify the real claim directly",
    "rule K1a": "K1a needs one held 3a EMPTY claim on the same system at a scope containing characteristic 0",
    "rule K1b": "K1b needs one held 3a NONEMPTY claim (a rational point) on the same system at a scope containing "
                "characteristic 0; a complex point (NOT_IN_IDEAL(1)) does not give a real one",
    "lifted": "3a rules bind only 3a premises held at 3a scopes",
}


def refusal_of3(item, claim, ledger, items):
    """A 3b refusal: what, the rule, the scope and the smallest fix, from gp_ledger3's report."""
    scope = show_scope(claim["scope"])
    support = item.get("support", "")
    result = (item.get("check") or {}).get("result")
    if item.get("refuter") is not None and result in (None, "accepted"):
        other = ledger.claim_by_key(item["refuter"])["label"]
        return {"message": f"{claim['label']} contradicts held claim {other} on an overlapping scope",
                "rule": "contra", "scope": scope, "smallest_fix": f"retract one of {claim['label']} and {other}"}
    open_ = [c["label"] for c in ledger.claims_with_keys(item.get("premises", [])) if not items[c["key"]]["held"]]
    if open_:
        return {"message": f"{support} needs held premises; not held: {', '.join(open_)}", "rule": support,
                "scope": scope, "smallest_fix": "hold the premises first"}
    if result not in (None, "accepted"):
        fix = FIX3.get(SUPPORT_TYPE.get(support), "recompute the certificate exactly for this system and scope")
        return {"message": f"the {support} is refused: {humane(item.get('diagnosis'))}",
                "rule": f"{support}: exact replay", "scope": scope, "smallest_fix": fix}
    fix = next((f for k, f in RULE_FIX3.items() if support.startswith(k)), "submit a certificate or a rule instance")
    return {"message": humane(item.get("mechanism")) or "no admitted support", "rule": support or "none",
            "scope": scope, "smallest_fix": fix}


def resolve_receipt(ledger, receipt):
    """Rule premises are written as labels; the surface wants keys."""
    receipt = json.loads(json.dumps(receipt))
    if "premises" in receipt:
        receipt["premises"] = [ledger.claim(p)["key"] if isinstance(p, str) else p for p in receipt["premises"]]
    unknown = set(receipt) - {"certificate", "rule", "premises"}
    if unknown or ("certificate" in receipt) == ("rule" in receipt):
        raise Refusal("a receipt has exactly one of `certificate` or `rule` (with `premises`)", "receipt shape",
                      "-", "write {\"certificate\": {...}} or {\"rule\": {...}, \"premises\": [labels]}")
    return receipt


def refusal_of(item, claim, ledger, items):
    """What was refused, under which rule and scope, and the smallest fix, from the profile's check."""
    if "family" in item:
        return refusal_of3(item, claim, ledger, items)
    scope = show_scope(claim["scope"])
    chk = item.get("check") or {}
    result = chk.get("result")
    support = item.get("support", "")
    if item.get("refuter") is not None and result in (None, "accepted"):
        other = ledger.claim_by_key(item["refuter"])["label"]
        return {"message": f"{claim['label']} contradicts held claim {other} on an overlapping scope",
                "rule": "contra", "scope": scope, "smallest_fix": f"retract one of {claim['label']} and {other}"}
    if result == "outside reach":
        reach = show_reach(chk.get("reach"))
        return {"message": f"the certificate reaches {reach}, which does not cover the requested {scope}",
                "rule": f"{support}: computed reach", "scope": scope,
                "smallest_fix": "narrow the claim to the computed reach, or certify the excluded "
                                "characteristics separately (for example mod p)"}
    if result == "replay failed":
        return {"message": "the certificate does not replay exactly: " + item.get("diagnosis", "no detail"),
                "rule": f"{support}: exact replay", "scope": scope,
                "smallest_fix": "recompute the certificate in exact arithmetic for this exact system"}
    if result == "ill-formed":
        return {"message": f"the requested scope meets the statement's denominator primes {chk.get('primes')}",
                "rule": "statement well-formedness", "scope": scope,
                "smallest_fix": "exclude those primes from the requested scope"}
    if support.startswith("rule"):
        premises = item.get("premises", [])
        open_ = [c["label"] for c in ledger.claims_with_keys(premises) if not items[c["key"]]["held"]]
        if open_:
            return {"message": f"{support} needs held premises; not held: {', '.join(open_)}", "rule": support,
                    "scope": scope, "smallest_fix": "hold the premises first"}
        return {"message": f"{support} refused: an obligation certificate fails or the premise scope does not "
                           "cover the conclusion's", "rule": support, "scope": scope,
                "smallest_fix": "check each obligation certificate against the premise and conclusion systems"}
    return {"message": "no admitted support", "rule": support or "none", "scope": scope,
            "smallest_fix": "submit a certificate or a rule instance"}


# --- commands ---------------------------------------------------------------------------------

COVER_PREMISES = ("AMP-THM1", "GP74-NON-UD", "ENUM-COMPLETE")


def cmd_cover(ledger, args):
    """Append a candidate cover: CoverComplete N M L for the listed graphs L, resting on named premises (or
    exhaustive). A ledger record the spine view reads (G-2 staging), never a Kernel claim."""
    if any(c["label"] == args.label for c in ledger.claims()) or any(r["label"] == args.label for r in ledger.covers()):
        raise Refusal(f"label {args.label!r} is taken", "ledger", "-", "choose a new label")
    if args.n < 0 or args.m < 0:
        raise Refusal("n and m are nonnegative", "spine rule", "-", "give --n N --m M with N, M >= 0")
    premises, notes = [], {}
    for raw in args.premise or []:
        name, _, data = raw.partition("=")
        if name not in COVER_PREMISES:
            raise Refusal(f"a cover rests on {', '.join(COVER_PREMISES)}, not {name}", "named premises", "-",
                          "name one of them, e.g. --premise ENUM-COMPLETE=<manifest-sha256>")
        if name not in premises:
            premises.append(name)
        if data:
            notes[name] = [q.strip() for q in data.split(",") if q.strip()]
    text = read_json_or_text(args.candidates)
    items_ = text.get("candidates") if isinstance(text, dict) else text
    if not isinstance(items_, list):
        raise Refusal("the candidates file is a list of graphs", "graph surface", "-",
                      'write a JSON list of graph6 strings or {"n", "edges"} objects, or one graph6 line per graph')
    cands, seen = [], set()
    for k, item in enumerate(items_):
        g = read_graph(item if isinstance(item, dict) else str(item), f"candidate {k}")
        if g["n"] != args.n:
            raise Refusal(f"candidate {k} has {g['n']} vertices, not {args.n}", "spine rule", "-",
                          f"every candidate is a graph on the cover's {args.n} vertices")
        h = graph_sha(g["n"], g["edges"])
        if h in seen:
            raise Refusal(f"candidate {k} is listed twice", "spine rule", "-", "list each graph once")
        seen.add(h)
        cands.append(dict({"n": g["n"], "edges": g["edges"], "sha256": h}, **({"name": g["name"]} if g.get("name") else {})))
    supports = [x.strip() for x in (args.supports or "").split(",") if x.strip()]
    labels = {c["label"] for c in ledger.claims()}
    missing = [x for x in supports if x not in labels]
    if missing:
        raise Refusal(f"no claim labelled {', '.join(missing)}", "ledger", "-", "file the supporting claims first")
    exh = exhaustive(args.n, args.m, [(c["n"], tuple(map(tuple, c["edges"]))) for c in cands])
    if not exh and not premises:
        raise Refusal("a cover's completeness needs a warrant", "spine rule", "-",
                      f"name the premise it rests on (--premise ENUM-COMPLETE=<manifest-sha256>), or list every "
                      f"labelled graph on {args.n} vertices with at least {args.m} edges")
    record = {"op": "cover", "label": args.label, "n": args.n, "m": args.m, "candidates": cands,
              "named_premises": premises, "supports": supports, "exhaustive": exh}
    if notes:
        record["premise_notes"] = notes
    ledger.append(record)
    tag = "".join(f" [premise {p}: OPEN]" for p in premises)
    print(f"cover {args.label} filed: {len(cands)} candidate{'s' if len(cands) != 1 else ''} for n = {args.n}, "
          f"m = {args.m}" + ("; exhaustive" if exh else "") + tag)


def read_json_or_text(path):
    """A JSON file, or else its non-empty lines."""
    try:
        text = Path(path).read_text(encoding="utf-8")
    except OSError as e:
        raise Refusal(f"cannot read {path}: {e}", "graph surface", "-", "give a readable file")
    try:
        return json.loads(text)
    except ValueError:
        return [l.strip() for l in text.splitlines() if l.strip()]


def cmd_init(ledger, args):
    statement = ledger.dir / "campaign.json"
    if not statement.exists():
        raise Refusal("no campaign statement", "campaign", "-", f"write {statement}")
    if ledger.records:
        raise Refusal("the ledger already exists", "append-only ledger", "-", "keep using it")
    ledger.append({"op": "init", "schema": SCHEMA, "statement_sha256": sha(statement.read_bytes())})
    print(f"ledger started for {statement}")


def cmd_claim(ledger, args):
    if args.udg and (args.matroid or args.system or args.nf):
        raise Refusal("--udg names the graph; its system comes from the encoder", "statement surface", "-",
                      "drop --system, --matroid or --nf")
    if not (args.udg or args.matroid or args.system or args.nf):
        raise Refusal("a claim needs a statement", "statement surface", "-",
                      "give one of --matroid, --system, --nf or --udg")
    if args.gauge and not args.udg:
        raise Refusal("--gauge pins a graph's first edge", "statement surface", "-", "use it with --udg")
    if claim_is_3b(args):
        return cmd_claim3(ledger, args)
    if any(c["label"] == args.label for c in ledger.claims() + ledger.covers()):
        raise Refusal(f"label {args.label!r} is taken", "ledger", "-", "choose a new label")
    if args.kind not in KINDS:
        raise Refusal(f"unknown kind {args.kind}", "statement kinds", "-", f"one of {', '.join(KINDS)}")
    if args.matroid:
        m = matroid_file(ledger.dir, args.matroid)
        enc = encoder.encode(m)
        system = {k: enc[k] for k in ("variables", "equations", "nonzero")}
        inputs = [f"encoding:{enc['digest']}"]
        premises = [enc["premise"]["name"]]
    else:
        raw = json.loads(Path(args.system).read_text(encoding="utf-8"))
        system = {k: raw[k] for k in ("variables", "equations", "nonzero")}
        inputs = [f"system:{sha(json.dumps(system, sort_keys=True).encode())}"]
        premises = []
    body = {"label": args.label, "matroid": args.matroid, "system": system, "kind": args.kind,
            "target": args.target, "scope": scope_of(args), "inputs": inputs, "named_premises": premises}
    key = new_key(ledger, body)
    record = ledger.append(dict({"op": "claim", "key": key}, **body))
    print(f"claim {args.label} (key {key}) filed: {args.kind} at {show_scope(record['scope'])}; open")


def decimals(x):
    """Floats, or strings written with a decimal point: not exact numbers."""
    if isinstance(x, float):
        return [repr(x)]
    if isinstance(x, str):
        return [x] if re.search(r"\d\.\d", x) else []
    if isinstance(x, dict):
        return [d for v in x.values() for d in decimals(v)]
    if isinstance(x, list):
        return [d for v in x for d in decimals(v)]
    return []


def prepare(ledger, label, receipt_path):
    """A receipt read and checked before any fold: its claim, its JSON and its exact numbers."""
    claim = ledger.claim(label)
    path = Path(receipt_path)
    if not path.is_file():
        raise Refusal(f"no receipt file at {path}", "receipt", show_scope(claim["scope"]),
                      "write the receipt first; paths are read by this machine's Python")
    data = path.read_bytes()
    try:
        raw = json.loads(data.decode("utf-8"))
    except ValueError as e:
        raise Refusal(f"the receipt is not JSON: {e}", "receipt", show_scope(claim["scope"]), "fix the JSON")
    bad = decimals(raw)
    if bad:
        raise Refusal(f"decimals are not exact numbers: {', '.join(bad[:3])}", "exact replay",
                      show_scope(claim["scope"]), "write each value as an integer or a fraction p/q")
    return claim, resolve_receipt(ledger, raw), sha(data)


def elaboration_refusal(ledger, label, claim, receipt, digest, out):
    body = {"message": out.get("error") or out.get("elaboration"), "rule": "elaboration",
            "scope": show_scope(claim["scope"]), "smallest_fix": "fix the receipt's syntax or variables"}
    ledger.append({"op": "refused", "label": label, "key": claim["key"], "receipt": receipt,
                   "receipt_sha256": digest, "refusal": body})
    return body


def record(ledger, label, claim, receipt, digest, out):
    """Append a fold's verdict on one submitted receipt: its support line, or its refusal body."""
    item = next(i for i in out["items"] if i["key"] == claim["key"])
    if item["held"]:
        ledger.append({"op": "support", "label": label, "key": claim["key"], "receipt_ref": ledger.store_receipt(receipt),
                       "receipt_sha256": digest, "reach": (item.get("check") or {}).get("reach")})
        widened = next((w for w in out["widened"] if w["key"] == claim["key"]), None)
        return (f"held: {label} at {show_scope(claim['scope'])}" +
                (f"; earned, unclaimed: {show_reach(widened['reach'])}" if widened else "")), None
    body = refusal_of(item, claim, ledger, {i["key"]: i for i in out["items"]})
    ledger.append({"op": "refused", "label": label, "key": claim["key"], "receipt": receipt,
                   "receipt_sha256": digest, "refusal": body})
    return None, body


def submit_one(ledger, label, claim, receipt, digest):
    """One receipt, one fold: (held line, None) or (None, refusal body)."""
    out = run_profile(surface(ledger, {claim["key"]: receipt}))
    if out.get("error") or out.get("elaboration"):
        return None, elaboration_refusal(ledger, label, claim, receipt, digest, out)
    return record(ledger, label, claim, receipt, digest, out)


def cmd_submit(ledger, args):
    claim, receipt, digest = prepare(ledger, args.label, args.receipt)
    line, body = submit_one(ledger, args.label, claim, receipt, digest)
    if line:
        print(line)
        return
    raise Refusal(body["message"], body["rule"], body["scope"], body["smallest_fix"])


def refusal_line(label, body):
    return (f"refused: {label}: {body['message']} [rule: {body['rule']}; scope: {body['scope']}]; "
            f"smallest fix: {body['smallest_fix']}")


def cmd_submit_batch(ledger, args):
    """Many receipts, one fold. Every support appended is held by the ledger the batch leaves."""
    try:
        entries = json.loads(Path(args.batch).read_text(encoding="utf-8"))
    except (OSError, ValueError) as e:
        raise Refusal(f"cannot read the batch file: {e}", "batch", "-",
                      'write a JSON list of {"label": ..., "receipt": PATH}')
    if not isinstance(entries, list) or not all(isinstance(e, dict) for e in entries):
        raise Refusal("the batch is not a list of objects", "batch", "-",
                      'write a JSON list of {"label": ..., "receipt": PATH}')
    prepared, refused, seen = [], 0, set()
    for e in entries:
        label = e.get("label")
        try:
            if label in seen:
                raise Refusal(f"{label} appears twice in the batch", "batch", "-", "submit each label once per batch")
            seen.add(label)
            prepared.append((label, *prepare(ledger, label, e.get("receipt", ""))))
        except Refusal as r:
            refused += 1
            print(refusal_line(label, r.body), file=sys.stderr)
    folds = 0

    def fold(batch):
        nonlocal folds
        folds += 1
        return run_profile(surface(ledger, {c["key"]: rc for _, c, rc, _ in batch}))

    def one_at_a_time(batch):
        nonlocal refused, folds
        for label, claim, receipt, digest in batch:
            folds += 1
            line, body = submit_one(ledger, label, claim, receipt, digest)
            if line:
                print(line)
            else:
                refused += 1
                print(refusal_line(label, body), file=sys.stderr)

    trial = fold(prepared) if prepared else {"items": [], "widened": []}
    if trial.get("error") or trial.get("elaboration"):
        print("the batch does not elaborate as a whole; submitting its items one at a time", file=sys.stderr)
        one_at_a_time(prepared)
    else:
        held = {i["key"] for i in trial["items"] if i["held"]}
        keep = [p for p in prepared if p[1]["key"] in held]
        # Batch receipts can interact (a contradiction between two of them, or a rule on a refused
        # premise): keep only what holds without the others, until nothing more drops.
        final = trial
        while len(keep) < len(prepared) and keep:
            final = fold(keep)
            if final.get("error") or final.get("elaboration"):
                keep = []
                break
            still = {i["key"] for i in final["items"] if i["held"]}
            if all(p[1]["key"] in still for p in keep):
                break
            keep = [p for p in keep if p[1]["key"] in still]
        kept = {p[1]["key"] for p in keep}
        retry = []
        for p in prepared:
            label, claim, receipt, digest = p
            if claim["key"] in kept:
                print(record(ledger, label, claim, receipt, digest, final)[0])
            elif claim["key"] in held:
                retry.append(p)
            else:
                refused += 1
                print(refusal_line(label, record(ledger, label, claim, receipt, digest, trial)[1]), file=sys.stderr)
        if retry:
            print(f"{len(retry)} held only alongside other batch receipts; submitting them one at a time",
                  file=sys.stderr)
            one_at_a_time(retry)
    print(f"batch: {len(entries) - refused} held, {refused} refused, in {folds} folds")
    if refused:
        raise Refusal(f"{refused} of {len(entries)} batch items refused (listed above)", "batch", "-",
                      "fix each refused item and resubmit it")


def state(ledger, candidates=False):
    out = run_profile(surface(ledger), candidates)
    if out.get("error"):
        raise RuntimeError(f"the ledger no longer folds: {out['error']}")
    return out, {i["key"]: i for i in out["items"]}


class CharSet:
    """A set of characteristics: 0 or not, and a finite or a cofinite set of primes."""

    def __init__(self, char0=False, cofinite=False, primes=()):
        self.char0, self.cofinite, self.primes = char0, cofinite, frozenset(primes)

    @staticmethod
    def of_scope(scope):
        if "characteristic" in scope:
            return CharSet(False, False, [scope["characteristic"]])
        if "outside" in scope:
            return CharSet(True, True, scope["outside"])
        return CharSet(True, False, [])

    @staticmethod
    def of_reach(r):
        if "finite" in r["primes"]:
            return CharSet(r["char0"], False, r["primes"]["finite"])
        return CharSet(r["char0"], True, r["primes"]["cofinite"])

    def union(self, o):
        c0 = self.char0 or o.char0
        if self.cofinite and o.cofinite:
            return CharSet(c0, True, self.primes & o.primes)
        if self.cofinite:
            return CharSet(c0, True, self.primes - o.primes)
        if o.cofinite:
            return CharSet(c0, True, o.primes - self.primes)
        return CharSet(c0, False, self.primes | o.primes)

    def meet_nonempty(self, o):
        if self.char0 and o.char0:
            return True
        if self.cofinite and o.cofinite:
            return True
        if self.cofinite:
            return bool(o.primes - self.primes)
        if o.cofinite:
            return bool(self.primes - o.primes)
        return bool(self.primes & o.primes)

    def text(self):
        ps = ", ".join(map(str, sorted(self.primes)))
        if self.cofinite:
            head = "every characteristic" if self.char0 else "every prime characteristic"
            return head + (f" except {{{ps}}}" if ps else "")
        items = (["0"] if self.char0 else []) + sorted(map(str, self.primes), key=int)
        return "{" + ", ".join(items) + "}" if items else "∅"

    def missing(self):
        """What the set leaves out of {0} ∪ primes, in words, or None if nothing."""
        gaps = [] if self.char0 else ["characteristic 0"]
        if self.cofinite:
            gaps += [f"p = {p}" for p in sorted(self.primes)]
        else:
            gaps.append("all but finitely many primes")
        return ", ".join(gaps) or None


def chi_summary(ledger, items, widened):
    """Per matroid: χ(M) from held realizability claims, its complement from held EMPTY claims."""
    rows = []
    by = {}
    for c in ledger.claims():
        if c["matroid"] and items[c["key"]]["held"]:
            by.setdefault(c["matroid"], []).append(c)
    for m, cs in sorted(by.items()):
        inside, outside = CharSet(), CharSet()
        for c in cs:
            reach = CharSet.of_scope(c["scope"])
            if c["key"] in widened:
                reach = reach.union(CharSet.of_reach(widened[c["key"]]))
            if c["kind"] == "NONEMPTY" or (c["kind"] == "NOT_IN_IDEAL" and c.get("target") in ("1", None)):
                inside = inside.union(reach)
            elif c["kind"] == "EMPTY":
                outside = outside.union(reach)
        if inside.meet_nonempty(outside):
            rows.append(f"{m}: CONFLICT between held realizability and held emptiness (report to the builder)")
            continue
        gap = inside.union(outside).missing()
        verdict = f"χ({m}) = {inside.text()}"
        rows.append(f"{verdict}, fully held" if gap is None else f"{verdict} so far; unknown: {gap}")
    return rows


def label_status(item, ledger, claim):
    if item["held"]:
        return "held"
    return "refused" if ledger.attempts(claim["label"]) else "open"


def cmd_status(ledger, args):
    out, items = state(ledger)
    status_goal(ledger, out, items)
    widened = {w["key"]: w["reach"] for w in out["widened"]}
    summary = chi_summary(ledger, items, widened)
    open_frame = any(c["matroid"] and c["named_premises"] and items[c["key"]]["held"] and
                     premise_state(out, c) == "OPEN" for c in ledger.claims())
    if summary:
        print("Characteristic sets (held claims only" +
              ("; some results modulo the OPEN premise ENCODING-FRAME):" if open_frame else "):"))
        print("\n".join("  " + r for r in summary))
        print()
    rows = []
    for c in ledger.claims():
        i = items[c["key"]]
        st = label_status(i, ledger, c)
        premise = premise_tag(out, c) if c["named_premises"] and st == "held" else ""
        earned = f"; earned, unclaimed: {show_reach(widened[c['key']])}" if c["key"] in widened else ""
        rows.append(f"{st:8} {c['label']:28} {c['kind']:12} {show_scope(c['scope'])}{earned}{premise}")
    print("\n".join(rows) if rows else "no claims")
    for cv in ledger.covers():
        tag = "".join(f" [premise {p}: OPEN]" for p in cv.get("named_premises", []))
        print(f"{'cover':8} {cv['label']:28} n = {cv.get('n')}, m = {cv.get('m')}, "
              f"{len(cv.get('candidates', []))} candidates{tag}")
    by = {}
    for c in ledger.claims():
        if c["matroid"] and items[c["key"]]["held"]:
            by.setdefault(c["matroid"], []).append(c)
    for m, cs in sorted(by.items()):
        modulo = " (modulo ENCODING-FRAME)" if any(premise_state(out, c) == "OPEN" for c in cs) else ""
        print(f"\n{m}{modulo}:")
        for c in cs:
            whole = c["kind"] != "NOT_IN_IDEAL" or c.get("target") in ("1", None)
            what = MEANING.get(c["kind"], c["kind"]) if whole else c["kind"]
            earned = f"; earned at {show_reach(widened[c['key']])}" if c["key"] in widened else ""
            print(f"  {what}: held at {show_scope(c['scope'])}{earned} ({c['label']})")
    status3(ledger, out, items)


def cmd_explain(ledger, args):
    out, items = state(ledger)
    cover = next((r for r in ledger.covers() if r["label"] == args.label), None)
    if cover is not None:
        return explain_cover(ledger, out, items, cover)
    claims = {c["key"]: c for c in ledger.claims()}
    supports = ledger.supports()

    def tree(key, depth):
        c = claims[key]
        i = items[key]
        pad = "  " * depth
        line = f"{pad}{c['label']}: {c['kind']} at {show_scope(c['scope'])}: {'held' if i['held'] else 'not held'}"
        print(line)
        names = [p for p in c["named_premises"] if p == FRAME and framed(c)]
        if c.get("udg"):
            print(f"{pad}  graph: {graph_text(c['udg'])}" + (", gauged" if c["udg"].get("gauge") else ""))
        if names:
            if premise_state(out, c) == "OPEN":
                print(f"{pad}  premise {', '.join(names)}: OPEN (encoding {c['inputs'][0]})" +
                      ("; the system is not the Lean encoder's for this graph" if c.get("udg") else ""))
            else:
                print(f"{pad}  premise {', '.join(names)}: discharged (proved: "
                      f"{FRAME_THEOREM if c['matroid'] else UDG_FRAME_THEOREM}; "
                      f"system checked equal to the Lean encoder's)")
        explain3_head(ledger, out, c, i, pad)
        s = supports.get(key)
        if not s:
            print(f"{pad}  no admitted support")
            return
        if "certificate" in s["receipt"] and "family" in i:
            print(f"{pad}  by {s['receipt']['certificate'].get('type')} certificate (receipt "
                  f"{s['receipt_sha256'][:12]}): {humane(i.get('diagnosis', i.get('mechanism', '')))}")
            if s["receipt"]["certificate"].get("type") == "case_tree":
                print(f"{pad}  meaning: {case_tree_meaning(s['receipt']['certificate'])}")
        elif "certificate" in s["receipt"]:
            cert = s["receipt"]["certificate"]
            print(f"{pad}  by {cert.get('type')} certificate (receipt {s['receipt_sha256'][:12]}), reach "
                  f"{show_reach((i.get('check') or {}).get('reach'))}")
        else:
            print(f"{pad}  by rule {s['receipt']['rule'].get('type')} from:")
            for p in s["receipt"].get("premises", []):
                tree(p, depth + 2)
    tree(ledger.claim(args.label)["key"], 0)


def frontier_goal(ledger, out, items):
    """Render DECIDE obligations from the existing goal bridges and spine join; no admission or writes.
    Return whether the goal remains unresolved, even when every filed claim is held."""
    goal = goal_of(ledger)
    if goal is None:
        return False
    name = goal.get("name", "Q")
    params = goal_udg(goal)
    cond = conditional(ledger, out)
    yes = [c for c in ledger.claims() if c.get("goal") == "yes" and items[c["key"]]["held"]]
    bridged = [c for c in yes if not goal_bridge(c, goal, out)]
    firm = [c for c in bridged if not cond[c["key"]]]
    no_state, selected, selected_join, other = spine_verdict(ledger, out, items, goal)
    no_held = no_state == "held"
    conflict = bool(firm) and no_held
    verdict = ("CONFLICT between held goal claims (report to the builder)" if conflict
               else f"decided: {name}" if firm else f"decided: not {name}" if no_held else "undecided")
    print(f"\nGoal: DECIDE {name}")
    if firm:
        print(f"  {name}: held by {', '.join(c['label'] for c in firm)} ({YES_BRIDGE})")
    else:
        print(f"  {name}: not held")
    candidates = [c for c in ledger.claims() if items[c["key"]]["held"] and
                  (c.get("goal") == "yes" or c["kind"] == "NONEMPTY" and c.get("udg"))]
    for c in candidates:
        gap = goal_bridge(c, goal, out)
        if gap:
            print(f"  held claim {c['label']} does not count for {name}: {gap}")
        elif c.get("goal") != "yes":
            print(f"  held claim {c['label']} does not count for {name}: not filed --goal yes")
        for p in sorted(cond[c["key"]]):
            print(f"  claim {c['label']}: premise {p}: OPEN")
    if selected:
        print(f"  not {name}: {no_state} by cover {selected['label']}")
    elif params is None:
        print(f"  not {name}: not held; the goal states no graph parameters")
    else:
        print(f"  not {name}: not held; no cover for n = {params[0]}, m = {params[1]}")
    for cv in ledger.covers():
        j = selected_join if cv is selected else cover_join(ledger, out, items, cv)
        if cv in other:
            mismatch = ("the goal states no graph parameters" if params is None else
                        f"not the goal's n = {params[0]}, m = {params[1]}")
            print(f"  cover {cv['label']} is for n = {cv.get('n')}, m = {cv.get('m')}; "
                  f"{mismatch}; it does not count")
        elif cv is not selected:
            print(f"  cover {cv['label']}: alternative cover for the goal")
        for p in j["open"]:
            print(f"  cover {cv['label']}: premise {p}: OPEN")
        for row in j["missing"]:
            print(f"  cover {cv['label']}: missing held exclusion over R for {graph_text(row['graph'])}")
            for c in row["others"]:
                if items[c["key"]]["held"]:
                    print(f"    held claim {c['label']} does not count: {exclusion_gap(out, items, c)}")
    print(f"  verdict: {verdict}")
    unresolved = conflict or not (firm or no_held)
    if unresolved:
        print("  goal frontier remains open")
    return unresolved


def cmd_frontier(ledger, args):
    out, items = state(ledger)
    open_ = [c for c in ledger.claims() if not items[c["key"]]["held"]]
    # Re-check each refused claim's last receipt in one pass, so the reason reads in today's terms;
    # the recorded refusal stays in the ledger and is shown when the wording has changed.
    last = {c["key"]: ledger.attempts(c["label"])[-1] for c in open_ if ledger.attempts(c["label"])}
    now = {}
    if last:
        trial = run_profile(surface(ledger, {k: r["receipt"] for k, r in last.items()}))
        if not (trial.get("error") or trial.get("elaboration")):
            titems = {i["key"]: i for i in trial["items"]}
            open_by_key = {}
            for c in open_:
                open_by_key.setdefault(c["key"], c)
            now = {k: refusal_of(titems[k], open_by_key[k], ledger, titems)
                   for k in last if k in titems and not titems[k]["held"]}
    for c in open_:
        if c["key"] not in last:
            print(f"{c['label']}: open, no attempt yet")
            continue
        recorded = last[c["key"]]["refusal"]
        r = now.get(c["key"], recorded)
        print(f"{c['label']}: refused: {r['message']} [rule: {r['rule']}; scope: {r['scope']}]; "
              f"smallest fix: {r['smallest_fix']}")
        if r["message"] != recorded["message"]:
            print(f"    (recorded then: {recorded['message']})")
    goal_open = frontier_goal(ledger, out, items)
    if not open_ and not goal_open:
        print("frontier empty: every claim is held" + (" and the goal is decided" if goal_of(ledger) else ""))


def tailings(ledger):
    out, items = state(ledger)
    claims = {c["key"]: c for c in ledger.claims()}
    rows = []
    for r in ledger.attempts():
        rows.append({"kind": "refused attempt", "claim": r["label"], "source": f"receipt {r['receipt_sha256'][:12]}",
                     "reliability": "refused by GP", "completeness": r["refusal"]["message"]})
    for w in out["widened"]:
        rows.append({"kind": "earned widening", "claim": claims[w["key"]]["label"],
                     "source": "re-replay of the held receipt", "reliability": "held by GP",
                     "completeness": f"earned at {show_reach(w['reach'])}, not claimed"})
    for c in ledger.claims():
        if not items[c["key"]]["held"]:
            rows.append({"kind": "open item", "claim": c["label"], "source": "ledger",
                         "reliability": "open", "completeness": "untagged"})
        if c["named_premises"] and items[c["key"]]["held"] and premise_state(out, c) == "OPEN":
            rows.append({"kind": "open premise", "claim": c["label"], "source": c["inputs"][0],
                         "reliability": "held modulo premise", "completeness": f"{', '.join(c['named_premises'])} OPEN"})
    for cv in ledger.covers():
        if cv.get("named_premises"):
            rows.append({"kind": "open premise", "claim": cv["label"], "source": "cover",
                         "reliability": "cover modulo premise",
                         "completeness": f"{', '.join(cv['named_premises'])} OPEN"})
    return rows


def cmd_tailings(ledger, args):
    rows = tailings(ledger)
    text = json.dumps({"schema": "gp-tailings/v1", "tailings": rows}, indent=2, ensure_ascii=False) + "\n"
    if args.export and args.export != "-":
        Path(args.export).write_bytes(text.encode("utf-8"))
        print(f"{len(rows)} tailings written to {args.export}")
    else:
        sys.stdout.write(text)


RAT_LIT = re.compile(r"^\((-?\d+)(?:/(\d+))? : Rat\)$")


def lean_name(label):
    return "w_" + re.sub(r"[^A-Za-z0-9]", "_", label)


def int_values(lits):
    """Rat literals that are all integers, else None."""
    out = []
    for lit in lits:
        m = RAT_LIT.match(lit)
        if not m or (m.group(2) and m.group(2) != "1"):
            return None
        out.append(int(m.group(1)))
    return out


def factors(v):
    """Prime factors of |v| with multiplicity (trial division; the kernel re-checks the product)."""
    v, out, d = abs(v), [], 2
    while d * d <= v:
        while v % d == 0:
            out.append(d)
            v //= d
        d += 1
    return out + ([v] if v > 1 else [])


def eval_int(terms, a):
    total = 0
    for exps, c in terms:
        assert c.denominator == 1
        term = int(c)
        for i, e in enumerate(exps):
            term *= (a[i] if i < len(a) else 0) ** e
        total += term
    return total


KIND_SUFFIX = re.compile(r", (\.empty|\.nonempty|\(\.(?:notInIdeal|inIdeal|vanishesOn) .*\))⟩$", re.S)


def warrants(ledger):
    """Lean theorem warrants for held claims within the generator's coverage (post-G3a decision 9).

    Each distinct polynomial is one small `def`, and statements name them: elaborating one huge
    literal per theorem is quadratic and timed out on PG(2,3). Returns (theorems in dependency
    order as {key: (name, text, polynomial names)}, uncovered {key: reason}, polynomial defs, gen)."""
    out, items = state(ledger, candidates=True)
    _gen = importlib.util.spec_from_file_location("gen_warrants", ROOT / "tools/gen-warrants.py")
    gen = importlib.util.module_from_spec(_gen)
    _gen.loader.exec_module(gen)
    cands = {c["key"]: c for c in out.get("candidates", [])}
    supports = ledger.supports()
    claims = {c["key"]: c for c in ledger.claims()}
    done, missing, systems, polys = {}, {}, {}, {}

    def pname(lit):
        return polys.setdefault(lit, f"p{len(polys)}")

    def stmt_ref(vars_, eqs, guards, kind):
        e = [pname(x) for x in eqs]
        g = [pname(x) for x in guards]
        return f"⟨{json.dumps(vars_)}, [{', '.join(e)}], [{', '.join(g)}], {kind}⟩", e + g

    def kind_of(lit):
        m = KIND_SUFFIX.search(lit)
        assert m, lit[-120:]
        return m.group(1)

    def emit(key):
        if key in done or key in missing:
            return key in done
        c, item = claims[key], items[key]
        name = lean_name(c["label"])
        if not item["held"]:
            missing[key] = "not held"
            return False
        receipt = supports[key]["receipt"]
        if "certificate" in receipt:
            cand = cands.get(key)
            if not cand:
                missing[key] = "outside coverage (no candidate)"
                return False
            cert = cand.get("cert", {})
            systems[key] = (cand["vars"], cand["eqs"], cand["guards"])
            ref, used = stmt_ref(cand["vars"], cand["eqs"], cand["guards"], kind_of(cand["stmt"]))
            head = f"theorem {name} :\n    Warranted {ref}\n      {cand['scope']} :=\n"
            if gen.eligible(dict(cand, case=c["label"])):
                gname, text = gen.theorem(dict(cand, case=c["label"], stmt=ref))
                text = text.replace(gname, name, 1).replace("simp only [", f"simp only [{', '.join(used)}, ", 1)
                done[key] = (name, text, used)
            elif cert.get("type") == "point" and int_values(cert["values"]) is not None:
                a = int_values(cert["values"])
                fss = [factors(eval_int(gen.terms(g), a)) for g in cand["guards"]]
                primes = sorted({q for fs in fss for q in fs})
                done[key] = (name, head + f"  warranted_point {a} {primes} {fss} rfl (by norm_num) "
                                          "(by decide +kernel) (by decide +kernel)", used)
            elif cert.get("type") == "proper_coefficient":
                coeff = sum(int(x) for e, x in gen.terms(cand["eqs"][0]) if e == cert["monomial"])
                done[key] = (name, head + f"  warranted_properCoeff {cert['monomial']} {factors(coeff)} (by norm_num) "
                                          "(by decide +kernel) (by decide +kernel) (by decide +kernel) "
                                          "(by decide +kernel) (by decide +kernel)", used)
            else:
                missing[key] = f"outside coverage ({cert.get('type', 'no candidate')}" + \
                    (", mod p" if "prime" in cert.get("field", "") and cert.get("type") == "ideal" else "") + ")"
                return False
            return True
        rule = receipt["rule"]["type"]
        prem = receipt.get("premises", [])
        if rule == "bridge" and len(prem) == 1 and emit(prem[0]):
            vars_, eqs, guards = systems[prem[0]]
            systems[key] = systems[prem[0]]
            ref, used = stmt_ref(vars_, eqs, guards, kind_of(item["stmtLit"]))
            done[key] = (name, f"theorem {name} :\n    Warranted {ref}\n      {item['scopeLit']} :=\n"
                               f"  Warranted.mono (warranted_bridge {done[prem[0]][0]}) (by decide +kernel)", used)
            return True
        missing[key] = f"outside coverage (rule {rule})" if rule != "bridge" else "premise outside coverage"
        return False

    for key in claims:
        emit(key)
    return done, missing, polys, gen


def cmd_emit_lean(ledger, args):
    if args.all:
        args.label = "--all"
    elif not args.label:
        raise Refusal("emit-lean needs a claim label or --all", "emit-lean", "-", "name a held claim")
    done, missing, polys, gen = warrants(ledger)
    held = [c for c in ledger.claims() if c["key"] in done or missing.get(c["key"]) != "not held"]
    if args.label == "--all":
        keys = list(done)
    else:
        claim = ledger.claim(args.label)
        if claim["key"] not in done:
            reason = missing.get(claim["key"], "outside coverage")
            raise Refusal(f"{args.label}: no Lean warrant ({reason})", "emit-lean coverage", show_scope(claim["scope"]),
                          "keep the receipt; the claim stays receipt-held")
        # The claim's theorem and the premise theorems it uses, in order.
        keys = [k for k in done if k == claim["key"] or done[k][0] in done[claim["key"]][1]]
    header = gen.header_text("GPBinding.Campaign", f"`gp emit-lean {args.label}`: Lean theorem warrants for held "
                             "claims, at each receipt's widest computed reach.")
    header = header.replace("import GPBinding.Binder.Registry\n",
                            "import GPBinding.Binder.Registry\nimport GPBinding.Warrants.Generic\n")
    header = header.replace("open GPProfile GPBinding.Binder MvPolynomial", "open GPProfile GPBinding.Binder "
                            "GPBinding.Warrants MvPolynomial")
    used = {n for k in keys for n in done[k][2]}
    defs = "\n".join(f"def {n} : Sparse := {lit}" for lit, n in polys.items() if n in used)
    # The larger linear_combination proofs need more than the default heartbeats.
    body = "\n\n".join("set_option maxHeartbeats 4000000 in\n" + done[k][1] for k in keys)
    print(header + "/-! The polynomials, one definition each. -/\n\n" + defs + "\n\n" + body +
          "\n\nend GPBinding.Campaign")
    if args.label == "--all":
        print(f"coverage: {len(done)} of {len(held)} held claims", file=sys.stderr)
        for k, r in missing.items():
            if r != "not held":
                print(f"  no warrant: {ledger.claim_by_key(k)['label']}: {r}", file=sys.stderr)


# --- branches and merges (post-G2 §1.5: the commit/merge guard) -------------------------------

# Claim keys are content-derived: a hash of the claim's label and statement, mapped into
# [2^32, 2^32 + 2^52). Two branches of one ledger never allocate the same key for different claims
# except by a hash collision (about n^2 / 2^53 for n claims), and a collision is not silent: the
# merge guard refuses it as a same-version current tie. Keys below 2^32 are the counter keys of
# ledgers filed before this scheme; they stay as filed. The range stays below 2^53, exact in JSON.
KEY_BASE, KEY_SPACE = 1 << 32, 1 << 52
LIFECYCLE = ("retract", "supersede")


def new_key(ledger, body):
    """The key for a new claim: its content hash, salted past any key already in this ledger."""
    used = {c["key"] for c in ledger.claims()}
    text = json.dumps(body, ensure_ascii=False, sort_keys=True)
    salt = 0
    while True:
        key = KEY_BASE + int(sha(f"{text}#{salt}".encode("utf-8")), 16) % KEY_SPACE
        if key not in used:
            return key
        salt += 1


def content(record):
    """A record without its timestamp: two branches that append the same record agree on this. A support
    filed by reference is compared as filed (its reference, so its receipt's SHA-256), not as read back."""
    return json.dumps({k: v for k, v in as_filed(record).items() if k != "at"}, ensure_ascii=False, sort_keys=True)


def as_filed(record):
    """A record as the ledger holds it: a support filed by reference without its read-back receipt."""
    return {k: v for k, v in record.items() if not ("receipt_ref" in record and k == "receipt")}


def lifecycle_events(records):
    """Ledger lifecycle records as Kernel events. `gp` writes none yet: the profile files only
    declarations, currents and warrants (`Guard.Simple`), so these reach only the merge guard."""
    out = []
    for r in records:
        if r["op"] == "retract":
            out.append({"kind": "retract", "target": r["target"]})
        elif r["op"] == "supersede":
            out.append({"kind": "supersede", "target": r["target"], "successor": r["successor"]})
    return out


def merge_refusal(message, fix):
    return Refusal(message, "merge guard", "-", fix)


def merge_plan(ours, theirs):
    """The merged records, and the Kernel log the merge guard checks.

    The merged ledger is ours, then every record of theirs that ours lacks (`content`). A claim's
    support is its branch's latest. Where the branches' supports differ, the one the other branch has
    already seen is older and gives way; where neither has seen the other's, the claim is split: both
    warrants go into the guard's log, so the Kernel sees them under the claim's one warrant id."""
    have = {content(r) for r in ours.records}
    theirs_have = {content(r) for r in theirs.records}
    new = [r for r in theirs.records if content(r) not in have]
    ours_s, theirs_s = ours.supports(), theirs.supports()
    split, chosen = set(), {}
    for k in ours_s.keys() & theirs_s.keys():
        o, t = ours_s[k], theirs_s[k]
        if receipt_digest(o) == receipt_digest(t) or content(t) in have:
            chosen[k] = o
        elif content(o) in theirs_have:
            chosen[k] = t
        else:
            split.add(k)
    merged = Ledger(ours.dir)
    merged.receipt_dirs = [ours.dir, theirs.dir]  # their receipt files, checked on read like ours
    merged.records = ours.records + new
    # Later supports win: restate a chosen support that the merged order would bury.
    late = merged.supports()
    new += [as_filed(chosen[k]) for k in sorted(chosen) if content(late[k]) != content(chosen[k])]
    merged.records = ours.records + new
    plan = surface(merged)
    plan["lifecycle"] = lifecycle_events(merged.records)
    entries = {c["key"]: c for c in plan["claims"]}
    for k in sorted(split):
        head = {x: v for x, v in entries[k].items() if x not in ("certificate", "rule", "premises")}
        plan["claims"] += [dict(head, **ours_s[k]["receipt"]), dict(head, **theirs_s[k]["receipt"])]
    return merged, new, plan, split


def cmd_merge(ledger, args):
    """Land another branch's records here only if the merged log still folds; else change nothing."""
    other = Ledger(args.other)
    if not other.records:
        raise merge_refusal(f"no ledger at {args.other}", "merge from a campaign directory with a ledger")
    if other.records[0].get("statement_sha256") != ledger.records[0].get("statement_sha256"):
        raise merge_refusal("the branches are ledgers of different campaign statements",
                            "merge only branches of one campaign")
    merged, new, plan, split = merge_plan(ledger, other)
    if not new:
        print("nothing to merge: every record of the other branch is already here")
        return
    out = run_profile(plan, guard=True)
    if out.get("error") or out.get("elaboration"):
        raise merge_refusal(f"the merged log does not fold: {out.get('error') or out.get('elaboration')}",
                            "resolve the collision on one branch, then merge again")
    # Adapter conflicts the Kernel log cannot see: receipts are named per claim, and labels are ours.
    if split:
        k = min(split)
        raise merge_refusal(f"conflicting warrant contents: {k} (the branches support "
                            f"{merged.claim_by_key(k)['label']} by different receipts)",
                            "submit one receipt on both branches, then merge again")
    by_key, by_label = {}, {}
    for c in merged.claims():
        if content(by_key.setdefault(c["key"], c)) != content(c):
            raise merge_refusal(f"conflicting claims under key {c['key']}: {by_key[c['key']]['label']} and "
                                f"{c['label']}", "refile one of them on its branch under a fresh key")
        if by_label.setdefault(c["label"], c)["key"] != c["key"]:
            raise merge_refusal(f"label {c['label']!r} names different claims on the two branches",
                                "relabel one of them on its branch")
    if plan["lifecycle"]:
        raise merge_refusal("the merged log folds, but it carries retraction or supersession records, which "
                            "the profile does not apply yet", "merge without them")
    try:
        state(merged)
    except RuntimeError as e:
        raise merge_refusal(str(e), "resolve the collision on one branch, then merge again")
    for r in new:  # their receipt files land here, each checked against its recorded SHA-256 first
        if r["op"] == "support" and "receipt_ref" in r:
            ledger.copy_receipt(r, merged.receipt_file(r))
    with ledger.path.open("ab") as f:
        for r in new:
            f.write((json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n").encode("utf-8"))
    ledger.records += new
    ledger.append({"op": "merge", "records": len(new), "from_sha256": sha(other.path.read_bytes())})
    ops = {o: sum(r["op"] == o for r in new) for o in ("claim", "support", "refused")}
    print(f"merged {len(new)} records ({ops['claim']} claims, {ops['support']} supports, {ops['refused']} refusals); "
          "the merged log folds")


def main(argv=None):
    ap = argparse.ArgumentParser(prog="gp", description=__doc__.splitlines()[0])
    ap.add_argument("--campaign", required=True)
    sub = ap.add_subparsers(dest="command", required=True)
    sub.add_parser("init")
    c = sub.add_parser("claim")
    c.add_argument("label")
    src = c.add_mutually_exclusive_group()
    src.add_argument("--matroid")
    src.add_argument("--system")
    src.add_argument("--nf", help="a number-field point file (3b)")
    c.add_argument("--udg", help="a graph (graph6, or a file with graph6 or JSON {n, edges}): its unit-distance system")
    c.add_argument("--gauge", action="store_true", help="with --udg: pin the first edge at (0, 0), (1, 0)")
    c.add_argument("--kind", required=True)
    c.add_argument("--target")
    sc = c.add_mutually_exclusive_group(required=True)
    sc.add_argument("--char", type=int)
    sc.add_argument("--char0", action="store_true")
    sc.add_argument("--outside")
    sc.add_argument("--real", action="store_true", help="over the field R (3b)")
    sc.add_argument("--semireal", action="store_true", help="in every semireal field (3b)")
    sc.add_argument("--rat-field", action="store_true", help="over the field Q itself (3b)")
    c.add_argument("--premise", action="append", help=f"a named OPEN premise, e.g. {KUMMER}[=q1,q2,...]")
    c.add_argument("--goal", choices=["yes", "no"], help="file the claim as the DECIDE goal (yes) or its negation (no)")
    cv = sub.add_parser("cover", help="a candidate cover for the goal's spine rule (a ledger record)")
    cv.add_argument("label")
    cv.add_argument("--candidates", required=True, help="JSON list of graphs (graph6 or {n, edges}), or graph6 lines")
    cv.add_argument("--n", type=int, required=True)
    cv.add_argument("--m", type=int, required=True)
    cv.add_argument("--premise", action="append", help="AMP-THM1, GP74-NON-UD[=names], ENUM-COMPLETE[=manifest-sha]")
    cv.add_argument("--supports", help="labels of claims backing the cover's argument (shown, not used)")
    s = sub.add_parser("submit")
    s.add_argument("label")
    s.add_argument("receipt")
    sb = sub.add_parser("submit-batch", help='a JSON list of {"label", "receipt"}, folded once')
    sb.add_argument("batch")
    sub.add_parser("status")
    e = sub.add_parser("explain")
    e.add_argument("label")
    sub.add_parser("frontier")
    t = sub.add_parser("tailings")
    t.add_argument("--export", nargs="?", const="-")
    w = sub.add_parser("emit-lean")
    w.add_argument("label", nargs="?")
    w.add_argument("--all", action="store_true", help="every covered claim, with coverage on stderr")
    mg = sub.add_parser("merge", help="land another branch's ledger records here if the merged log folds")
    mg.add_argument("other", help="the other branch's campaign directory")
    args = ap.parse_args(argv)
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8")  # Lean output and labels are not cp1252
    ledger = Ledger(args.campaign)
    if args.command != "init" and not ledger.records:
        print("refused: no ledger here [rule: ledger; scope: -]; smallest fix: run `gp init`", file=sys.stderr)
        return 2
    try:
        {"init": cmd_init, "claim": cmd_claim, "cover": cmd_cover, "submit": cmd_submit,
         "submit-batch": cmd_submit_batch, "status": cmd_status,
         "explain": cmd_explain, "frontier": cmd_frontier, "tailings": cmd_tailings,
         "emit-lean": cmd_emit_lean, "merge": cmd_merge}[args.command](ledger, args)
    except Refusal as r:
        b = r.body
        print(f"refused: {b['message']} [rule: {b['rule']}; scope: {b['scope']}]; smallest fix: {b['smallest_fix']}",
              file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
