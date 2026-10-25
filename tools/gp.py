"""gp: the 3P campaign CLI (post-G3a handoff §4.6). Lean-first: every verdict comes from the profile.

usage: python tools/gp.py --campaign <dir> <command> ...

  init                                  start a ledger for the campaign statement in <dir>/campaign.json
  restate --reason TEXT                 bind an edited campaign.json (a versioned event; edits are refused until then)
  claim <label> (--matroid M | --system FILE | --nf FILE | --udg GRAPH [--gauge]) --kind KIND [--target POLY]
        (--char P | --char0 | --outside P,Q | --real | --semireal | --rat-field) [--premise NAME]
                                        file a claim; it is open until a receipt supports it
  cover <label> --candidates FILE --n N --m M [--premise NAME[=data] ...] [--supports L1,L2]
                                        a candidate cover: the Kernel claims cover n m L and spine n m L
  submit <label> <receipt.json>         offer a certificate or a rule instance; GP replays it
  withdraw <label> --reason TEXT [--cascade]
                                        withdraw a claim permanently; --cascade when other held claims rest on it
  status                             held, open, refused and earned, per claim and per matroid
  explain <label>                       the licence tree of one claim, or a cover's join
  frontier                              open claims, each with its last refusal and smallest fix
  tailings --export [FILE]              by-products: refused attempts, earned widenings, open items
  emit-lean (<label> | --all)           Lean theorem warrants for held claims the generator covers
  merge <other-campaign-dir>            land another branch's records here, only if the merged log folds

Lane P campaigns (campaign.json "profile": "P"; tools/gp_lanep.py, GP 0.52 P1 and P2):
  register <Decl> [--as NAME] | register --prose TEXT --as NAME [--process KIND]
         | register --bridge DIR:LABEL --as NAME | register <Decl> <Decl>... | register --batch FILE
                                        bind a statement code: declaration, closure hash, environment stamp; a
                                        process condition (review, merge, wording, fidelity-review); a bridge code,
                                        generated as the literal 3a/3b meaning of claim LABEL of campaign DIR;
                                        several statements with one bind (0.54)
  claim <label> (--lean X | --prose X) [--premise H]... [--condition C]...
        [--theorem T | --from L | --comparator T | --bridge DIR:LABEL]
                                        a claim of X under premises H (X may be ¬Y), with open process conditions C;
                                        held by a lean_theorem (tier 2), a Comparator receipt (tier 1: the challenge
                                        is emitted into the package) or a bridge (tier 3)
  claim --batch FILE                    many claims (a JSON list or JSON lines of {label, lean|prose, premises,
                                        conditions, theorem|from|bridge}) with one bind, all or nothing (0.55)
  discharge <label> --premise H --by L2 [--as NEW]
                                        from L = (s, S u {H}) and L2 = (H, T), T a subset of S: the claim (s, S)
  submit <label> (--hand-proof P --state complete|sketch [--condition H]... | --script P | --numerical P
                 | --external P --tier N)   a recorded-only warrant: it never holds a claim
  submit <label> --citation REF [--theorem-number N] [--locator TEXT] [--doi DOI] [--file P] [--condition H]...
                                        a published result (tier 5, recorded only; a local copy is re-hashed) (0.55)
  submit <label> --comparator RECEIPT [--log LOG]
                                        a Comparator receipt (tools/lanep-comparator.sh); held only at the pins
  fidelity <X> --level LEVEL --by WHO --ref REF; present <label> --venue V --tag TAG [--premise H]...
  bind [--replay]                       build the package and run the P binder (drift is detected on every bind);
                                        --replay: replay the package with lean4checker (tier 2 is final after it;
                                        a replay that cannot run is not a kernel rejection and changes nothing)

The ledger (<dir>/ledger.jsonl, gp-ledger/v1) is append-only and written only by this CLI. Each claim
binds its encoding digest; each support records the receipt it was replayed from, inline (as older
supports are) or by reference: receipts/<sha256>.json, whose SHA-256 is checked on every command
before anything folds. The Kernel fold over the whole ledger decides every status, on every command.
A refused submission is logged with the refusal and never becomes support. A withdrawal (GP 0.51) is a
`withdraw` record: both runners retract the claim's warrants, so it and what rests only on it are not held.
"""
import argparse
import datetime
from fractions import Fraction
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
GP_VERSION = "0.55.0"  # the release version; recorded in each ledger's init record
EXE = PROFILE / (".lake/build/bin/gp_ledger" + (".exe" if os.name == "nt" else ""))
ELAN_HOME = Path(os.environ.get("ELAN_HOME") or Path.home() / ".elan")
SCHEMA = "gp-ledger/v1"
SCHEMAS = (SCHEMA,)  # ledger schemas this gp reads (within v1, the compatible changes USING-GP.md lists)
# A new campaign's init record names the oldest gp that may read it (`min_reader`, a v1 extension, GP 0.52 P2): the
# version that started it. Readers from this one on refuse a ledger whose min_reader is newer than themselves; older
# readers ignore the field.
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
_spec_lanep = importlib.util.spec_from_file_location("gp_lanep", ROOT / "tools/gp_lanep.py")
lanep = importlib.util.module_from_spec(_spec_lanep)  # Lane P (GP 0.52 P1, P2): P campaigns only
_spec_lanep.loader.exec_module(lanep)


class Refusal(Exception):
    """A CLI-level refusal: what was refused, under which rule and scope, and the smallest fix."""

    def __init__(self, what, rule, scope, fix, detail=None):
        super().__init__(what)
        self.body = {"message": what, "rule": rule, "scope": scope, "smallest_fix": fix}
        self.detail = list(detail or [])  # lines printed after the refusal (a failed build's output)


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


def version_key(text):
    """A release version as a comparable tuple (0.52.0 -> (0, 52, 0)), or None if it is not one."""
    m = re.fullmatch(r"(\d+)\.(\d+)\.(\d+)", str(text))
    return tuple(int(x) for x in m.groups()) if m else None


class Ledger:
    def __init__(self, campaign):
        self.dir = Path(campaign)
        self.path = self.dir / "ledger.jsonl"
        self.records = []
        self._refused = None
        self._claims = None
        self._supports = None
        self._withdrawn = None
        # Where receipt files are looked up, in order (a merge adds the other branch's directory).
        # Files are content-addressed and checked on every read, so no directory is trusted.
        self.receipt_dirs = [self.dir]
        self._statement = None
        self.set_aside = None  # {key: why}: claims whose text does not parse, once a fold has failed (fold_ledger)
        if self.path.exists():
            self.records = [json.loads(l) for l in self.path.read_text(encoding="utf-8").splitlines() if l.strip()]

    def check_schema(self):
        """The ledger's init record must name a schema this gp reads; a newer or foreign ledger is refused."""
        first = self.records[0] if self.records else {}
        if not isinstance(first, dict) or first.get("op") != "init":
            raise Refusal(f"{self.path} does not start with an init record", "ledger schema", "-",
                          "a gp ledger starts with `gp init`; restore the ledger from its branch")
        schema = first.get("schema")
        need = first.get("min_reader")
        if need is not None and (version_key(need) is None or version_key(need) > version_key(GP_VERSION)):
            raise Refusal(f"this ledger needs gp {need} or later to read it (its init record's min_reader); this is gp "
                          f"{GP_VERSION}", "ledger schema", "-", f"use gp {need} or later" if version_key(need) else
                          "restore the ledger's init record from its branch")
        if schema not in SCHEMAS:
            raise Refusal((f"the ledger's schema is {schema!r}" if schema else "the ledger's init record names no schema") +
                          f"; gp {GP_VERSION} reads {', '.join(SCHEMAS)}",
                          "ledger schema", "-", "use a gp release that reads this schema" if schema else
                          f"an init record names its schema ({SCHEMA}); restore the ledger from its branch")

    def bound_statement_sha(self):
        """The statement hash the ledger binds: the init record's, or the latest explicit restatement."""
        bound = None
        for r in self.records:
            if r["op"] == "init":
                bound = r.get("statement_sha256")
            elif r["op"] == "restate":
                bound = r["new_sha256"]
        return bound

    def verify_statement(self):
        """Read campaign.json once, check its bytes against the bound hash and parse those same bytes.
        Every statement read in this command uses the result (the reviewed receipt discipline)."""
        path = self.dir / "campaign.json"
        if not path.exists():
            raise Refusal("the campaign statement is missing", "statement binding", "-", f"restore {path}")
        data = path.read_bytes()
        bound, current = self.bound_statement_sha(), sha(data)
        if bound is not None and current != bound:
            raise Refusal(f"the campaign statement changed since it was bound (bound {bound[:12]}, now {current[:12]})",
                          "statement binding", "-",
                          "restore campaign.json, or record the change with `gp restate --reason ...`")
        self._statement = json.loads(data.decode("utf-8"))
        return self._statement

    @property
    def statement(self):
        return self._statement if self._statement is not None else self.verify_statement()

    def append(self, record):
        record = dict(record, at=now())
        with self.path.open("ab") as f:
            f.write((json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n").encode("utf-8"))
        self.records.append(record)
        self._refused = None
        self._claims = None
        self._supports = None
        self._withdrawn = None
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
        """Legacy cover records (`op` "cover", written by `gp cover` before release plan A2). Views show them as
        refile notices; they are never read as a verdict. Covers are now Kernel claims (family "cover")."""
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

    def withdrawals(self):
        """The withdraw records by claim key, the first per key (GP 0.51; docs/WITHDRAWAL-DESIGN.md). A withdrawal is
        permanent: both runners retract the claim's support and theorem warrants on every fold."""
        stamp = (id(self.records), len(self.records))
        if self._withdrawn is None or self._withdrawn[0] != stamp:
            out = {}
            for r in self.records:
                if r["op"] == "withdraw" and type(r.get("key")) is int:
                    out.setdefault(r["key"], r)
            self._withdrawn = (stamp, out)
        return dict(self._withdrawn[1])


def matroid_file(campaign, name, statement=None):
    """A matroid the statement lists, or one the campaign agent added under matroids/ with a source.
    Callers with a ledger pass its verified statement."""
    if "/" in name or "\\" in name or name.endswith(".json"):
        stem = Path(name).name.removesuffix(".json")
        raise Refusal(f"--matroid takes a family name, not a path: {name!r}", "campaign statement", "-",
                      f"pass the name, for example --matroid {stem}")
    if statement is None:
        statement = json.loads((Path(campaign) / "campaign.json").read_text(encoding="utf-8"))
    family = statement.get("family") if isinstance(statement, dict) else None
    if family is not None and not (isinstance(family, list) and all(isinstance(s, dict) for s in family)):
        raise Refusal("the campaign statement's family is not a list of stages", "campaign statement", "-",
                      'write "family": [{"matroids": [{"name": ..., "elements": [...], "lines": [...]}]}]')
    for stage in family or []:
        for m in stage.get("matroids", []):
            if isinstance(m, dict) and m.get("name") == name:
                return checked_matroid(m, f"--matroid {name}")
    added = Path(campaign) / "matroids" / f"{name}.json"
    if added.exists():
        m = json.loads(added.read_text(encoding="utf-8"))
        if m.get("name") != name or not m.get("source"):
            raise Refusal(f"{added.name} needs its own name and a cited source", "campaign statement: F1",
                          "-", "add \"name\" and \"source\" (tagged [VERIFY] until checked)")
        return checked_matroid(m, f"matroids/{added.name}")
    if family is None:
        raise Refusal(f"--matroid {name}: the campaign statement has no family", "campaign statement", "-",
                      'list the matroid under "family": [{"matroids": [...]}] in campaign.json (then `gp restate`), '
                      f"or add matroids/{name}.json with a cited source")
    raise Refusal(f"matroid {name!r} is not in the campaign family", "campaign statement", "-",
                  f"use a listed matroid, or add matroids/{name}.json with a cited source")


MATROID_KEYS = {"name", "elements", "lines", "source", "answer_key"}


def checked_matroid(m, where):
    """A matroid record the encoder reads in full: a simple rank-3 matroid given by its lines. Keys the
    encoder would ignore (a rank, a matrix) are refused, so a record is never filed as another matroid
    (C3a: a rank-9 record was once filed as U(3,18))."""
    extra = sorted(set(m) - MATROID_KEYS)
    if extra:
        raise Refusal(f"{where}: {', '.join(extra)} {'is' if len(extra) == 1 else 'are'} not read: --matroid "
                      "takes simple rank-3 matroids given by \"elements\" and \"lines\" only",
                      "matroid statement", "-",
                      "remove the extra keys, or state other matroids (any rank, a matrix) as a --system claim")
    missing = [k for k in ("elements", "lines") if k not in m]
    if missing:
        raise Refusal(f"{where}: the record has no {' or '.join(missing)}", "matroid statement", "-",
                      'give "elements" and "lines" (write "lines": [] for the uniform matroid U(3, n))')
    try:
        encoder.canonical(m)
    except (ValueError, KeyError, TypeError) as err:
        raise Refusal(f"{where}: {err}", "matroid statement", "-", "fix the record: a simple rank-3 matroid")
    return m


def scope_of(args):
    if args.char is not None:
        return {"characteristic": args.char}
    if args.outside is not None:
        return {"outside": sorted({int(p) for p in args.outside.split(",") if p.strip()})}
    return {"char0": True}


def prime_set(ps):
    """A set of primes as every view prints it: {2, 3}."""
    return "{" + ", ".join(str(p) for p in sorted(ps)) + "}"


def show_scope(scope):
    """A requested scope, as filed."""
    if "context" in scope:
        return CONTEXTS[scope["context"]]
    if "characteristic" in scope:
        return f"characteristic {scope['characteristic']}"
    if "outside" in scope:
        return "characteristic 0 and every prime" + (f" except {prime_set(scope['outside'])}" if scope["outside"] else "")
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
    return ("0 and " if r["char0"] else "") + "every prime" + (f" except {prime_set(ex)}" if ex else "")


# --- the profile ------------------------------------------------------------------------------

def surface(ledger, extra=None):
    """The ledger as the explicit statement surface, with one trial support optionally swapped in."""
    supports = ledger.supports()
    routed = routed_3b(ledger, extra)  # decided by gp_ledger3 (`surface3`), not by gp_ledger
    claims = []
    aside = ledger.set_aside or {}
    for c in ledger.claims():
        if c["key"] in routed or c["key"] in aside:
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
    plan = {"claims": claims, "requested": [c["key"] for c in ledger.claims()
                                            if c["key"] not in routed and c["key"] not in aside],
            "frames": frames(ledger)}
    routed = {k for k in routed if k not in aside}
    if routed:
        plan["_3b"] = surface3(ledger, routed, extra)
    # Withdrawn keys go to both runners, which retract each one's warrants in their folds (GPProfile.Withdraw). A 3a
    # premise copied into the 3b part is retracted there too; retracting an id a part lacks is harmless. Sent only
    # when there is one, so a ledger with no withdrawal gives the runners exactly what 0.50 gave them.
    withdrawn = sorted(ledger.withdrawals())
    if withdrawn:
        plan["withdrawn"] = withdrawn
        if routed:
            plan["_3b"]["withdrawn"] = withdrawn
    return plan


def frames(ledger):
    """Each matroid claim's matroid as index lines, for the Lean encoder to re-derive its system. A claim
    whose record is not read in full is left out, so its ENCODING-FRAME stays OPEN (matroid_notes says why);
    the rest of the ledger stays usable."""
    out = []
    for c in ledger.claims():
        if c["matroid"]:
            try:
                record = matroid_file(ledger.dir, c["matroid"], ledger.statement)
            except Refusal:
                continue
            m, _ = encoder.canonical(record)
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


def runner_sources():
    """Every file a runner is built from: the profile and Kernel sources, their build files and the toolchain pin."""
    files = [PROFILE / "lakefile.toml", PROFILE / "lake-manifest.json", PROFILE / "lean-toolchain",
             ROOT / "phase2/lean/lakefile.toml"]
    files += sorted((PROFILE / "GPProfile").rglob("*.lean")) + sorted((ROOT / "phase2/lean/GP50").rglob("*.lean"))
    return [f for f in files if f.exists()]


def tree_identity(files, base=ROOT):
    """The content identity of a source set: SHA-256 over each file's relative path and content hash
    (release plan A3). Modification times play no part, so a touch is not a change and an edit is
    detected whatever its timestamp."""
    lines = []
    for f in sorted(files, key=lambda f: f.as_posix()):
        try:
            rel = f.resolve().relative_to(Path(base).resolve()).as_posix()
        except ValueError:
            rel = f.as_posix()
        lines.append(f"{sha(f.read_bytes())}  {rel}\n")
    return sha("".join(lines).encode("utf-8"))


def stamp_path(exe):
    return exe.with_name(exe.name + ".gpstamp")


def stale(exe=EXE):
    """A runner is fresh only if its stamp records the current source identity: never run a stale checker."""
    if not exe.exists():
        return True
    stamp = stamp_path(exe)
    if not stamp.exists():
        return True
    try:
        recorded = json.loads(stamp.read_text(encoding="utf-8")).get("sources_sha256")
    except (ValueError, OSError):
        return True
    return recorded != tree_identity(runner_sources())


def write_stamp(exe, identity):
    stamp_path(exe).write_text(json.dumps({"sources_sha256": identity}) + "\n", encoding="utf-8")


def run_profile(plan, candidates=False, guard=False):
    global _built
    if "_3b" in plan:
        return run_guard(plan) if guard else run_mixed(plan, candidates)
    if not _built and stale():
        lake_build("gp_ledger", EXE)
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
# The DECIDE goal family (release plan A2): goal n m true|false, cover n m L, spine n m L, all over ℝ.
GOAL_FAMILIES = ("goal", "cover", "spine")
FAMILIES3 = ("orderFree", "real", "realCover", "nf") + GOAL_FAMILIES
CERTS3 = ("alg_point", "sos", "ordered", "real_point", "nf", "rational_root", "root_cover", "case_tree", "cover_all")
RULES3 = ("k1a", "k1b", "narrow", "realize", "spine", "decide")
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
    elif fam in GOAL_FAMILIES:
        s["context"] = c["scope"]["context"]
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
    claims = [c for c in ledger.claims() if c["key"] not in (ledger.set_aside or {})]
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


_announced = False
BUILD_TAIL = 12  # lines of lake's output a failed build's refusal shows


def toolchain_lake():
    """The pinned toolchain's directory and its `lake`, or a refusal saying how to install it."""
    pin = (PROFILE / "lean-toolchain").read_text(encoding="utf-8").strip()
    toolchain = ELAN_HOME / "toolchains" / pin.replace("/", "--").replace(":", "---")
    lake = toolchain / ("bin/lake" + (".exe" if os.name == "nt" else ""))
    if not lake.is_file():
        raise Refusal(f"the GP runners need the Lean toolchain {pin}, which is not installed (no {lake})",
                      "runner build", "-", "install elan (https://github.com/leanprover/elan), then run `lake build "
                      f"gp_ledger gp_ledger3` in {PROFILE}: elan installs the pinned toolchain first")
    return toolchain, lake


def lake_build(target, exe=None):
    """Build a runner, then stamp it with the source identity it was built from (computed first, so an
    edit made during the build is caught by the next freshness check). The first build of a command says
    so on stderr; a failed build is a refusal naming the target, with the last lines of lake's output."""
    global _announced
    identity = tree_identity(runner_sources())
    toolchain, lake = toolchain_lake()
    if not _announced:
        _announced = True
        print("building the GP runners (one-time, several minutes)…" if exe is None or not exe.exists() else
              f"checking the GP runners: lake build {target} (no stamp yet)…" if not stamp_path(exe).exists() else
              f"rebuilding the GP runners: their sources changed (lake build {target})…", file=sys.stderr, flush=True)
    env = dict(os.environ, PATH=str(toolchain / "bin") + os.pathsep + os.environ["PATH"])
    p = subprocess.run([str(lake), "build", target], cwd=PROFILE, env=env, capture_output=True)
    if p.returncode != 0:
        text = ((p.stdout or b"") + b"\n" + (p.stderr or b"")).decode("utf-8", "replace").replace("\r\n", "\n")
        tail = [line for line in text.splitlines() if line.strip()][-BUILD_TAIL:]
        raise Refusal(f"building the runner {target} failed (lake build exited {p.returncode})", "runner build", "-",
                      f"run `lake build {target}` in {PROFILE} for Lean's full message",
                      detail=["lake's last lines:"] + ["  " + line for line in tail])
    if exe is not None:
        write_stamp(exe, identity)


def run_ledger3(plan, guard=False):
    global _built3
    if not _built3 and stale(EXE3):
        lake_build("gp_ledger3", EXE3)
    _built3 = True
    out = subprocess.run([str(EXE3)] + (["--guard"] if guard else []), input=json.dumps(plan), capture_output=True,
                         text=True, encoding="utf-8")
    if out.returncode != 0:
        raise RuntimeError(out.stderr.strip() or "gp_ledger3 failed")
    return json.loads(out.stdout)


def run_guard(plan):
    """The merge guard on a ledger with 3b claims (post-G2 §1.5): the Kernel's `resolve` decides the merged log of
    each runner. gp_ledger --guard files the 3a part; gp_ledger3 --guard files the 3b part: its routed claims, the 3a
    premises they rest on (one `alg` copy each) and each split claim's two warrants (`merge_plan`). Conflicts are per
    claim id and warrant id, and each key's records all go to the one part that owns it (`routed_3b`; the copies
    are single entries and cannot conflict), so the two checks see every collision a merge can make. A lifecycle
    event goes with its target's part."""
    plan = dict(plan)
    part3 = dict(plan.pop("_3b"))
    life = plan.pop("lifecycle", [])
    mine3 = set(part3["requested"])
    part3["lifecycle"] = [e for e in life if e.get("target") in mine3 or not plan["claims"]]
    if plan["claims"]:
        plan["lifecycle"] = [e for e in life if e not in part3["lifecycle"]]
        out = run_profile(plan, guard=True)
        if out.get("error") or out.get("elaboration"):
            return out
    return run_ledger3(part3, guard=True)


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
    goal = ledger.statement.get("goal")
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


# HW61 G-1, G-2 and release plan A2. The DECIDE goal's verdict is the Kernel's. For a goal with graph parameters
# ("udg": {"n": n, "m": m}) and Q(n, m) := ∃ P : Finset ℝ², P.card = n ∧ m ≤ unitDistNum P, the ledger carries two goal
# claims (family "goal": `goal n m true`, `goal n m false`), filed at init or by an older ledger's first filing command,
# and `gp cover` files `cover n m L` and `spine n m L`. gp_ledger3 admits; the fold decides:
# - realize (`GPBinding.Real.realizeRuleOk_sound`): a held --udg NONEMPTY claim over ℝ whose statement equals the Lean
#   encoder's for its graph, on n vertices with at least m canonical edges, holds `goal n m true`;
# - spine (`spineRuleOk_sound`): one held encoder-exact --udg EMPTY claim over ℝ per cover graph holds `spine n m L`;
# - cover_all (`coverAllCheck_sound`): an exhaustive list holds `cover n m L`; a named premise never does;
# - decide (`decideRuleOk_sound`): spine and cover with the same n, m and L hold `goal n m false`.
# This file proposes rule instances (`goal_sync`: untrusted, each folded) and renders fold results. `goal_bridge`
# stays as G-1's filing pre-check and as display text; it decides nothing.
GOAL_FIX = {"yes": "file the realization with --udg GRAPH --kind NONEMPTY --real, for a graph on the goal's n "
                   "vertices with at least its m edges",
            "no": "file each exclusion without --goal (--udg GRAPH --kind EMPTY --real); not Q is held only "
                  "through a candidate cover (`gp cover`)"}
SPINE = "GPBinding.UDG.spine_sound"
RULE_THEOREMS = {"realize": "GPBinding.Real.realizeRuleOk_sound: udg_frame_iff, realize_sound",
                 "spine": "GPBinding.Real.spineRuleOk_sound: spine_sound, candidate_isEmpty",
                 "decide": "GPBinding.Real.decideRuleOk_sound",
                 "cover_all": "GPBinding.Real.coverAllCheck_sound"}


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
    """G-1's filing pre-check, and display text: None when a goal-tagged claim could stand for its side; otherwise
    why not. It decides nothing: the Kernel's rule realize does (A2). `out` (the runner's output) supplies the frame
    check, which filing does in its own elaboration run."""
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


def goal_labels(goal):
    name = (goal or {}).get("name", "Q")
    return {True: f"goal:{name}", False: f"goal:not-{name}"}


def family_claims(ledger, fam):
    return [c for c in ledger.claims() if c.get("family") == fam]


def goal_claims(ledger):
    """The Kernel's goal statements for the campaign's DECIDE goal: {True: Q(n, m), False: not Q(n, m)}, each the first
    such claim in the ledger, or None when not filed (always None when the goal has no graph parameters)."""
    params = goal_udg(goal_of(ledger))
    out = {True: None, False: None}
    for c in family_claims(ledger, "goal") if params else []:
        st = c["system"]
        if (st.get("n"), st.get("m")) == params and st.get("value") in out and out[st["value"]] is None:
            out[st["value"]] = c
    return out


def file_goal_family(ledger, label, family, system, kind, premises=(), **meta):
    """Append one goal-family claim (A2), at scope ℝ; its statement is profile data that gp_ledger3 reads."""
    body = {"label": label, "matroid": None, "system": system, "kind": kind, "target": None,
            "scope": {"context": "real"}, "family": family, "named_premises": list(premises),
            "inputs": [f"{family}:{sha(json.dumps(system, sort_keys=True).encode())}"]}
    body.update({k: v for k, v in meta.items() if v})
    return ledger.append(dict({"op": "claim", "key": new_key(ledger, body)}, **body))


def ensure_goal_claims(ledger):
    """File the DECIDE goal's two claims, Q(n, m) and not Q(n, m), when the goal has graph parameters and the ledger
    lacks them: at init, or on an older ledger's first filing command. Idempotent."""
    goal = goal_of(ledger)
    params = goal_udg(goal)
    if params is None:
        return
    have = goal_claims(ledger)
    taken = {c["label"] for c in ledger.claims()} | {r["label"] for r in ledger.covers()}
    for value, label in goal_labels(goal).items():
        if have[value] is None:
            while label in taken:
                label += "'"
            file_goal_family(ledger, label, "goal", {"n": params[0], "m": params[1], "value": value}, "GOAL")
            print(f"goal claim {label} filed: {'' if value else 'not '}{goal.get('name', 'Q')} (n = {params[0]}, "
                  f"m = {params[1]}) over ℝ; open until the Kernel holds it")


def rule_premises(ledger, c):
    """The premise keys of a claim's accepted rule support ([] otherwise)."""
    sup = ledger.supports().get(c["key"]) if c else None
    return list(((sup or {}).get("receipt") or {}).get("premises", []))


def realize_receipt(c):
    """Rule realize from a graph-bound claim: its graph is rule data, and Lean compares the statements."""
    return {"rule": {"type": "realize", "edges": c["udg"]["edges"], "gauge": c["udg"].get("gauge") is True},
            "premises": [c["key"]]}


def goal_attempt(ledger, claim, receipt, why):
    """Offer one receipt for a goal-family claim exactly as `gp submit` does: an untrusted proposal that the fold
    checks. A proposal already refused on its merits (not merely for unheld premises) is not offered again."""
    digest = sha(receipt_bytes(receipt))
    if any(r.get("receipt_sha256") == digest and "needs held premises" not in r["refusal"]["message"]
           for r in ledger.attempts(claim["label"])):
        return None
    line, body = submit_one(ledger, claim["label"], claim, receipt, digest)
    print(f"{line} ({why})" if line else f"goal: {claim['label']} not held ({why}): {body['message']}")
    return line


def exclusion_choice(ledger, out, items, cond, n, g):
    """A held graph-bound EMPTY claim over ℝ on graph g, for a spine proposal (frame-equal first, then fewest OPEN
    premises). Matching only proposes: rule spine compares statements in Lean."""
    cg = canon({"n": n, "edges": g})
    wd = ledger.withdrawals()  # never proposed (they are not held either)
    cs = [c for c in ledger.claims() if isinstance(c.get("udg"), dict) and cg is not None and canon(c["udg"]) == cg
          and c["kind"] == "EMPTY" and c["scope"].get("context") == "real" and items[c["key"]]["held"]
          and c["key"] not in wd]
    return min(cs, key=lambda c: (premise_state(out, c) != "discharged", len(cond[c["key"]])), default=None)


def goal_proposals(ledger, out, items):
    """Rule instances worth offering now, as (claim, receipt, why): spines whose every graph has a held exclusion,
    decide from the goal's held spine and cover, realize from held --goal yes graph-bound claims. Withdrawn claims
    are never offered and never premises."""
    cond = conditional(ledger, out)
    wd = ledger.withdrawals()
    for sp in family_claims(ledger, "spine"):
        if not items[sp["key"]]["held"]:
            st = sp["system"]
            picks = [exclusion_choice(ledger, out, items, cond, st["n"], g) for g in st["graphs"]]
            if all(picks):
                yield sp, {"rule": {"type": "spine"}, "premises": [c["key"] for c in picks]}, \
                    "rule spine from " + (", ".join(c["label"] for c in picks) or "no graphs")
    gc, params = goal_claims(ledger), goal_udg(goal_of(ledger))
    no, yes = gc[False], gc[True]
    if no and not items[no["key"]]["held"]:
        for cv in family_claims(ledger, "cover"):
            sp = spine_for(ledger, cv)
            if (cv["system"]["n"], cv["system"]["m"]) == params and sp and items[cv["key"]]["held"] and \
                    items[sp["key"]]["held"] and cv["key"] not in wd:
                yield no, {"rule": {"type": "decide"}, "premises": [sp["key"], cv["key"]]}, \
                    f"rule decide from {sp['label']} and {cv['label']}"
    if yes and not items[yes["key"]]["held"]:
        for c in ledger.claims():
            if c.get("goal") == "yes" and isinstance(c.get("udg"), dict) and items[c["key"]]["held"] and \
                    c["key"] not in wd:
                yield yes, realize_receipt(c), f"rule realize from {c['label']}"


def goal_pending(ledger):
    """A cheap pre-check without a fold (supports stand in for held): could any goal proposal be new?"""
    if goal_udg(goal_of(ledger)) is None:
        return False
    # A withdrawn claim, and a support resting on one, is not held: it does not stand in for held here.
    gone = withdrawn_roots(ledger)
    sup = {k: s for k, s in ledger.supports().items() if k not in gone}
    gc = goal_claims(ledger)
    if any(c is None or c["key"] in sup for c in gc.values()):
        return False
    excl = {canon(c["udg"]) for c in ledger.claims() if isinstance(c.get("udg"), dict) and c["kind"] == "EMPTY"
            and c["scope"].get("context") == "real" and c["key"] in sup}
    if any(c["key"] not in sup and all(canon({"n": c["system"]["n"], "edges": g}) in excl for g in c["system"]["graphs"])
           for c in family_claims(ledger, "spine")):
        return True
    if any(c.get("goal") == "yes" and isinstance(c.get("udg"), dict) and c["key"] in sup for c in ledger.claims()):
        return True
    held_spines = [c["system"] for c in family_claims(ledger, "spine") if c["key"] in sup]
    return any(cv["key"] in sup and cv["system"] in held_spines for cv in family_claims(ledger, "cover"))


def goal_sync(ledger):
    """After a filing command: offer the goal rules the ledger now supports (A2). Proposals only; the fold decides."""
    for _ in range(8):
        if not goal_pending(ledger):
            return
        out, items = state(ledger)
        if not any(goal_attempt(ledger, *prop) for prop in list(goal_proposals(ledger, out, items))):
            return


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


def system3a(raw):
    """A characteristic-scoped system: variables and equations, and `nonzero` guards (none if absent)."""
    if not isinstance(raw, dict) or not isinstance(raw.get("variables"), list) or \
            not isinstance(raw.get("equations"), list) or not isinstance(raw.get("nonzero", []), list):
        raise Refusal("the system file needs variables and equations (lists), and optionally nonzero",
                      "statement surface", "-", 'write {"variables": ["x"], "equations": ["x - 1"], "nonzero": []}')
    if raw.get("signs"):
        raise Refusal("sign conditions are read only over ℝ", "statement surface", "-",
                      "claim it with --real, or drop the sign conditions")
    return {"variables": raw["variables"], "equations": raw["equations"], "nonzero": raw.get("nonzero", [])}


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
            enc = encoder.encode(matroid_file(ledger.dir, args.matroid, ledger.statement))
            system = {k: enc[k] for k in ("variables", "equations", "nonzero")}
            inputs = [f"encoding:{enc['digest']}"]
            premises = [enc["premise"]["name"]] + premises
        else:
            system = system3a(read_json(args.system, "system"))
    if udg:
        inputs = [f"udg:{udg['sha256']}"]
    elif not args.matroid:
        inputs = [f"system:{sha(json.dumps(system, sort_keys=True).encode())}"]
    bad = decimals(system)
    if bad:
        raise Refusal(f"decimals are not exact numbers: {', '.join(bad[:3])}", "exact statements", show_scope(scope),
                      "write each value as an integer or a fraction p/q")
    refuse_zero_guards(system, show_scope(scope))
    if args.goal:
        check_goal_side(ledger, args, family, scope, kind, udg)
    args.target = target_of(args)
    refuse_unparsable(system, args.target, show_scope(scope))
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
    yes = goal_claims(ledger)[True] if args.goal == "yes" and udg else None
    if yes is not None:  # A2: the realize attempt; it is offered again once this claim is held (`goal_sync`)
        goal_attempt(ledger, yes, realize_receipt(record), f"rule realize from {args.label}")


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
    if c.get("family") in GOAL_FAMILIES:
        st = c["system"]
        if c["family"] == "goal":
            return (f"some {st['n']} points in the plane have at least {st['m']} unit distances" if st["value"] else
                    f"no {st['n']} points in the plane have at least {st['m']} unit distances")
        cover = (f"every {st['n']}-point set with at least {st['m']} unit distances contains a unit-distance copy of "
                 f"one of {len(st['graphs'])} candidate graph{'s' if len(st['graphs']) != 1 else ''}")
        return cover if c["family"] == "cover" else f"if {cover}, then no {st['n']} points have at least {st['m']} unit distances"
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


def cover_claims(ledger):
    """Cover claims (`gp cover`, family "cover"): Kernel claims since release plan A2. Withdrawn covers are left out of
    the goal views (their `status` row says they are withdrawn)."""
    wd = ledger.withdrawals()
    return [c for c in family_claims(ledger, "cover") if c["key"] not in wd]


def spine_for(ledger, cover):
    """The spine claim filed with a cover (`<label>:spine`), else another with the same n, m and graphs."""
    same = [c for c in family_claims(ledger, "spine") if c["system"] == cover["system"]]
    return next((c for c in same if c["label"] == f"{cover['label']}:spine"), same[0] if same else None)


def last_refusal(ledger, c):
    attempts = ledger.attempts(c["label"]) if c else []
    return attempts[-1]["refusal"]["message"] if attempts else None


def cover_join(ledger, out, items, cover):
    """Display only: a cover claim as the fold holds it, with its spine and, per candidate, the exclusion the held spine
    rests on (else the graph-bound claims a reader could use). Nothing here decides."""
    cond = conditional(ledger, out)
    st = cover["system"]
    sp = spine_for(ledger, cover)
    sp_held = bool(sp) and items[sp["key"]]["held"]
    used = rule_premises(ledger, sp) if sp_held else []
    graphs = [c for c in ledger.claims() if isinstance(c.get("udg"), dict)]
    names = cover.get("candidates") or []
    rows = []
    for k, g in enumerate(st["graphs"]):
        cg = canon({"n": st["n"], "edges": g})
        same = [c for c in graphs if cg is not None and canon(c["udg"]) == cg]
        ok = [c for c in same if exclusion_gap(out, items, c) is None]
        ex = ledger.claim_by_key(used[k]) if k < len(used) else min(ok, key=lambda c: len(cond[c["key"]]), default=None)
        rows.append({"graph": names[k] if k < len(names) else {"n": st["n"], "edges": g}, "canon": cg,
                     "exclusion": ex, "others": [c for c in same if c not in ok]})
    held = items[cover["key"]]["held"]
    opens = [] if held else (list(cover.get("named_premises", [])) or [UNWARRANTED])
    inherited = sorted(cond[sp["key"]] - set(opens)) if sp_held else []
    return {"rows": rows, "held": held, "spine": sp, "spine_held": sp_held, "open": opens + inherited,
            "missing": [] if sp_held else [r for r in rows if not r["exclusion"]]}


def goal_rule_text(ledger, c):
    """How the Kernel holds a goal-family claim: its rule and premises, or its receipt."""
    r = (ledger.supports().get(c["key"]) or {}).get("receipt") or {}
    if "rule" in r:
        t = r["rule"].get("type")
        labels = ", ".join(ledger.claim_by_key(k)["label"] for k in r.get("premises", [])) or "no premises"
        return f"rule {t} from {labels}; {RULE_THEOREMS.get(t, 'no theorem')}"
    t = (r.get("certificate") or {}).get("type")
    return f"{t} receipt; {RULE_THEOREMS.get(t, 'no theorem')}"


def spine_verdict(ledger, out, items, goal):
    """Display only: ("held" | "spine" | "open" | None, cover, join, covers for other parameters), read from the fold:
    held when the Kernel holds not Q by rule decide from this cover; spine when it holds the cover's spine while the
    cover is open; open otherwise."""
    params = goal_udg(goal)
    covers = cover_claims(ledger)
    if params is None:
        return None, None, None, covers
    match = [cv for cv in covers if (cv["system"]["n"], cv["system"]["m"]) == params]
    other = [cv for cv in covers if cv not in match]
    no = goal_claims(ledger)[False]
    by = rule_premises(ledger, no) if no and items[no["key"]]["held"] else []
    joins = sorted(((cv, cover_join(ledger, out, items, cv)) for cv in match), key=lambda x: len(x[1]["open"]))
    for verdict, test in (("held", lambda cv, j: cv["key"] in by), ("spine", lambda cv, j: j["spine_held"]),
                          ("open", lambda cv, j: True)):
        for cv, j in joins:
            if test(cv, j):
                return verdict, cv, j, other
    return None, None, None, other


def goal_side_held(ledger, out, items, g):
    """Display only: (the fold holds the goal claim, the OPEN named premises it inherits)."""
    if g is None or not items[g["key"]]["held"]:
        return False, set()
    return True, conditional(ledger, out)[g["key"]]


def yes_gap(ledger, out, items, c):
    """Display only: why a held --goal yes claim does not hold Q: G-1's pre-check, else the Kernel's refusal of rule
    realize from it."""
    gap = goal_bridge(c, goal_of(ledger), out)
    if gap:
        return gap
    g = goal_claims(ledger)[True]
    if g is None:
        return "no goal claim is filed yet"
    digest = sha(receipt_bytes(realize_receipt(c)))
    refused = [r for r in ledger.attempts(g["label"]) if r.get("receipt_sha256") == digest]
    return (f"the Kernel refused rule realize from it: {refused[-1]['refusal']['message']}" if refused
            else "no realize attempt from it yet")


def matroid_notes(ledger):
    """Matroid claims whose record is no longer read in full (filed before v0.50.1, or edited since)."""
    notes = []
    for c in ledger.claims():
        if c["matroid"]:
            try:
                matroid_file(ledger.dir, c["matroid"], ledger.statement)
            except Refusal as r:
                notes.append(f"{c['label']}: {r.body['message']}; its ENCODING-FRAME stays OPEN, so it is not a "
                             f"claim about matroid {c['matroid']!r}")
    return notes


def legacy_notes(ledger):
    return [f"legacy cover record {r['label']} (n = {r.get('n')}, m = {r.get('m')}): refile with `gp cover`; "
            "it decides nothing" for r in ledger.covers()]


def other_cover_text(o, params):
    mismatch = ("the goal states no graph parameters" if params is None else
                "not the goal's n = {}, m = {}".format(*params))
    return f"cover {o['label']} is for n = {o['system']['n']}, m = {o['system']['m']}; {mismatch}; it does not count"


def status_goal(ledger, out, items):
    """Display only: the DECIDE goal as the fold holds it (release plan A2). Q and not Q are the Kernel's goal claims;
    nothing here makes either held. A held one that rests on claims tagged with OPEN named premises (metadata the
    Kernel does not read) is shown with them and not counted as decided."""
    goal = goal_of(ledger)
    if goal is None:
        return
    name = goal.get("name", "Q")
    print(f"Goal: DECIDE {name}" + (f" := {goal['statement']}" if goal.get("statement") else ""))
    if goal.get("readings"):
        print(f"  readings: {'; '.join(goal['readings'])}")
    params = goal_udg(goal)
    gc = goal_claims(ledger)
    if params is not None and None in gc.values():
        print("  the goal claims are not filed yet: the next claim, submit or cover command files them")
    negation = f"not {name}" + (f" ({goal['negation']})" if goal.get("negation") else "")
    firm = {}
    for side, title in ((True, name), (False, negation)):
        held, cond = goal_side_held(ledger, out, items, gc[side])
        firm[side] = held and not cond
        if held:
            print(f"  {title}: held by the Kernel ({gc[side]['label']}: {goal_rule_text(ledger, gc[side])})" +
                  (f", modulo the OPEN premise{'s' if len(cond) > 1 else ''} {', '.join(sorted(cond))}, so not decided"
                   if cond else ""))
            continue
        cs = [c for c in ledger.claims() if c.get("goal") == ("yes" if side else "no") and items[c["key"]]["held"]]
        if side:
            print(f"  {title}: not held" + (f" ({', '.join(c['label'] for c in cs)} held, but unbridged: "
                                            f"{yes_gap(ledger, out, items, cs[0])})" if cs else ""))
            continue
        if cs:  # a --goal no tag from before G-1
            print(f"  ({', '.join(c['label'] for c in cs)} filed --goal no: {goal_bridge(cs[0], goal, out)})")
        for line in legacy_notes(ledger):
            print(f"  ({line})")
        verdict, cv, j, other = spine_verdict(ledger, out, items, goal)
        for o in other:
            print(f"  ({other_cover_text(o, params)})")
        if verdict == "spine" and j["held"]:
            why = last_refusal(ledger, gc[False])
            print(f"  {title}: open; the Kernel holds spine {j['spine']['label']} and cover {cv['label']}, but not "
                  f"rule decide" + (f": {why}" if why else ""))
        elif verdict == "spine":
            print(f"  {title}: open; the Kernel holds spine {j['spine']['label']} (if cover {cv['label']} is complete "
                  f"then not {name}); the cover is open, resting on the named premises {', '.join(j['open'])}")
        elif verdict == "open" and j["missing"]:
            print(f"  {title}: open (cover {cv['label']}: no held exclusion over ℝ for " +
                  ", ".join(graph_text(r["graph"]) for r in j["missing"]) + ")")
        elif verdict == "open":
            why = last_refusal(ledger, j["spine"])
            print(f"  {title}: open (cover {cv['label']}: spine {j['spine']['label'] if j['spine'] else '-'} not held" +
                  (f": {why}" if why else "") + ")")
        else:
            print(f"  {title}: not held" + ("; the goal states no graph parameters" if params is None else ""))
    verdict = ("CONFLICT between held goal claims (report to the builder)" if firm[True] and firm[False]
               else f"decided: {name}" if firm[True] else f"decided: not {name}" if firm[False]
               else "undecided")
    print(f"  verdict: {verdict}\n")


def explain_cover(ledger, out, items, cv):
    """`explain` on a cover claim (display only): completeness, its spine, each candidate's exclusion, the theorems."""
    j = cover_join(ledger, out, items, cv)
    goal = goal_of(ledger)
    n, m, graphs = cv["system"]["n"], cv["system"]["m"], cv["system"]["graphs"]
    print(f"cover {cv['label']}: CoverComplete {n} {m} L, L = {len(graphs)} candidate graph{'s' if len(graphs) != 1 else ''} "
          f"(GPBinding.UDG.CoverComplete): {'held by the Kernel' if j['held'] else 'open'}")
    print(f"  means: every set of {n} points in the plane with at least {m} unit distances contains a unit-distance "
          f"copy of a candidate")
    if j["held"]:
        print(f"  completeness: exhaustive, every labelled graph on n vertices with at least m edges is listed; the "
              f"Kernel's check holds it ({RULE_THEOREMS['cover_all']}, GPBinding.UDG.coverComplete_of_all)")
    else:
        e = exhaustive(n, m, [r["canon"] for r in j["rows"] if r["canon"]])
        why = ("not exhaustive" if e is False else "too many graphs to check exhaustively" if e is None
               else "the list is exhaustive, but it was filed on named premises: file it again without them for the "
                    "Kernel's check")
        print(f"  completeness: open, resting on the named premises below ({why}); a named premise never holds a cover")
        if last_refusal(ledger, cv):
            print(f"  last attempt refused: {last_refusal(ledger, cv)}")
    for p in cv.get("named_premises", []):
        data = (cv.get("premise_notes") or {}).get(p)
        what = OPEN_PREMISES[p].format(of=f" of {', '.join(data)}" if data else "")
        print(f"  premise {p}: OPEN ({what}; no admitted checker yet)")
    sp = j["spine"]
    if sp:
        why = last_refusal(ledger, sp)
        print(f"  spine {sp['label']}: " + (f"held by the Kernel ({goal_rule_text(ledger, sp)})" if j["spine_held"] else
                                             "not held" + (f" (last attempt refused: {why})" if why else "")))
    for r in j["rows"]:
        print(f"  candidate {graph_text(r['graph'])}:")
        if r["canon"] is None:
            print(f"    not a canonical graph on {n} vertices: it cannot be excluded")
        c = r["exclusion"]
        if c:
            cond = sorted(conditional(ledger, out)[c["key"]])
            print(f"    excluded by {c['label']}: held, EMPTY over ℝ, ENCODING-FRAME discharged "
                  f"(GPBinding.UDG.candidate_isEmpty, {UDG_FRAME_THEOREM}, GPBinding.UDG.holds_iff_holdsE_udg)" +
                  ("" if j["spine_held"] else "; not yet used by a held spine") +
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
          f"GPBinding.UDG.candidate_isEmpty; in the Kernel, rules spine and decide ({RULE_THEOREMS['spine']}; "
          f"{RULE_THEOREMS['decide']})")
    params = goal_udg(goal)
    no = goal_claims(ledger)[False]
    if params is None:
        print("  goal: the campaign goal states no graph parameters; this cover decides nothing")
    elif (n, m) != params:
        print("  goal: n = {}, m = {}; this cover is for other parameters and does not count".format(*params))
    elif no and items[no["key"]]["held"] and cv["key"] in rule_premises(ledger, no):
        cond = sorted(conditional(ledger, out)[no["key"]])
        print("  for the goal: held, not Q, with no OPEN premise" if not cond else
              f"  for the goal: held by the Kernel, modulo {', '.join(cond)}, so not decided")
    elif j["missing"]:
        print(f"  for the goal: open, {len(j['missing'])} candidate{'s' if len(j['missing']) > 1 else ''} not excluded")
    elif j["spine_held"] and not j["held"]:
        print(f"  for the goal: open; the Kernel holds the spine, and the cover rests on {', '.join(j['open'])}")
    else:
        print("  for the goal: open; the Kernel does not hold " + ("rule decide" if j["spine_held"] else "the spine"))


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
        name = goal.get("name", "the goal")
        g = goal_claims(ledger)[True]
        via = (c["goal"] == "yes" and g is not None and c["key"] in rule_premises(ledger, g) and
               any(x["key"] == g["key"] and x["held"] for x in out["items"]))
        gap = goal_bridge(c, goal, out)
        if via:
            print(f"{pad}  filed as {name}: the Kernel holds {g['label']} through it (rule realize; "
                  f"{RULE_THEOREMS['realize']})" + (" (modulo its OPEN premises: not decided)" if cond else ""))
        else:
            print(f"{pad}  filed as {'' if c['goal'] == 'yes' else 'not '}{name}" +
                  (f" (unbridged: {gap})" if gap else " (conditional: it cannot show the goal held)" if cond else
                   " (the Kernel does not hold the goal through it yet)"))


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
    "cover_all": "list every labelled graph on n vertices with at least m edges (at most 100000 of them); otherwise the "
                 "cover stays open on its named premises, which never hold it",
    "case_tree": "every split needs all its branches and every leaf must close its branch: an L1a collision cites "
                 "each rhombus's four unit edges and both diagonal distinctness guards (injectivity is never "
                 "assumed), and its weighted relations must sum exactly to p_u - p_v for a guarded pair; an L1b "
                 "unit step's relations must sum exactly to (p_u - p_v) - sign·(p_a - p_b) with sign ±1 and (a, b) "
                 "an edge of the branch; a case tree proves EMPTY over ℝ only",
}
SUPPORT_TYPE = {"SOS receipt": "sos", "ordered Positivstellensatz receipt": "ordered", "point receipt": "real_point",
                "algPoint receipt": "alg_point", "number-field receipt": "nf", "rational-root receipt": "rational_root",
                "selected-root cover receipt": "root_cover", "case-tree receipt": "case_tree",
                "exhaustive cover receipt": "cover_all"}
RULE_FIX3 = {
    "narrowing": "narrowing keeps the statement and narrows only from every semireal field to ℝ or ℚ; nothing "
                 "narrows from a characteristic (ℂ) scope into ℝ: certify the real claim directly",
    "rule K1a": "K1a needs one held 3a EMPTY claim on the same system at a scope containing characteristic 0",
    "rule K1b": "K1b needs one held 3a NONEMPTY claim (a rational point) on the same system at a scope containing "
                "characteristic 0; a complex point (NOT_IN_IDEAL(1)) does not give a real one",
    "lifted": "3a rules bind only 3a premises held at 3a scopes",
    "rule realize": "offer one held --udg NONEMPTY claim over ℝ on the goal's n vertices with at least its m edges, with "
                    "that claim's own graph as the rule's edges: its statement must be the Lean encoder's for that graph",
    "rule spine": "offer one held --udg EMPTY claim over ℝ per cover graph, in the cover's order, each on exactly that "
                  "graph (narrow a semireal exclusion to ℝ first; a characteristic-0 claim does not reach ℝ)",
    "rule decide": "offer the spine and the cover that `gp cover` filed together, for the goal's n and m",
}


def unheld_label(ledger, c):
    """An unheld premise's label, marked when the claim was withdrawn."""
    return c["label"] + (" (withdrawn)" if c["key"] in ledger.withdrawals() else "")


def refusal_of3(item, claim, ledger, items):
    """A 3b refusal: what, the rule, the scope and the smallest fix, from gp_ledger3's report."""
    scope = show_scope(claim["scope"])
    support = item.get("support", "")
    result = (item.get("check") or {}).get("result")
    if item.get("refuter") is not None and result in (None, "accepted"):
        other = ledger.claim_by_key(item["refuter"])["label"]
        return {"message": f"{claim['label']} contradicts held claim {other} on an overlapping scope",
                "rule": "contra", "scope": scope, "smallest_fix": f"retract one of {claim['label']} and {other}"}
    open_ = [unheld_label(ledger, c) for c in ledger.claims_with_keys(item.get("premises", []))
             if not items[c["key"]]["held"]]
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
        return {"message": "the requested scope meets the statement's denominator primes "
                           f"{prime_set(chk.get('primes') or [])}",
                "rule": "statement well-formedness", "scope": scope,
                "smallest_fix": "exclude those primes from the requested scope"}
    if support.startswith("rule"):
        premises = item.get("premises", [])
        open_ = [unheld_label(ledger, c) for c in ledger.claims_with_keys(premises) if not items[c["key"]]["held"]]
        if open_:
            return {"message": f"{support} needs held premises; not held: {', '.join(open_)}", "rule": support,
                    "scope": scope, "smallest_fix": "hold the premises first"}
        return {"message": f"{support} refused: an obligation certificate fails or the premise scope does not "
                           "cover the conclusion's", "rule": support, "scope": scope,
                "smallest_fix": "check each obligation certificate against the premise and conclusion systems"}
    return {"message": "no admitted support", "rule": support or "none", "scope": scope,
            "smallest_fix": "submit a certificate or a rule instance"}


# --- withdrawal (GP 0.51, docs/WITHDRAWAL-DESIGN.md) ------------------------------------------
#
# `gp withdraw` appends a `withdraw` record. On every fold both runners retract the claim's support warrant (id = key)
# and theorem warrant (2^60 + key): the claim, and every claim whose only derivations pass through it, stop being
# held (GPProfile.Withdraw: W1 withdraw_antitone, W2 withdraw_resolves, W3 withdraw_unholds). Nothing here decides;
# the helpers below only render what the fold says.

OLD_READERS = ("readers older than 0.51 will not see this withdrawal: an older gp skips the record and shows the claim, "
               "and what rests on it, as held again")


def withdrawn_roots(ledger):
    """Display and pre-checks only: per claim key, the withdrawn claims its accepted support rests on through rule
    premises (a withdrawn claim is its own root). Empty when nothing is withdrawn."""
    wd = ledger.withdrawals()
    if not wd:
        return {}
    roots = {k: {k} for k in wd}
    deps = {k: (s.get("receipt") or {}).get("premises", []) for k, s in ledger.supports().items() if k not in wd}
    grow = True
    while grow:
        grow = False
        for k, ps in deps.items():
            extra = set().union(*(roots.get(p, set()) for p in ps)) - roots.get(k, set())
            if extra:
                roots.setdefault(k, set()).update(extra)
                grow = True
    return roots


def rests_on_withdrawn(ledger, items):
    """Display only: {key: labels of the withdrawn claims it rests on} for claims that are not held and not withdrawn."""
    roots, wd = withdrawn_roots(ledger), ledger.withdrawals()
    return {c["key"]: sorted(ledger.claim_by_key(r)["label"] for r in roots[c["key"]])
            for c in ledger.claims() if c["key"] in roots and c["key"] not in wd and not items[c["key"]]["held"]}


def withdrawn_text(record):
    return f"withdrawn {record.get('at', '-')}: {record.get('reason', '')}"


def support_text(ledger, c):
    """How a claim was supported: its rule and premises, or its certificate type."""
    r = (ledger.supports().get(c["key"]) or {}).get("receipt") or {}
    if "rule" in r:
        labels = ", ".join(ledger.claim_by_key(k)["label"] for k in r.get("premises", []) if ledger.claim_by_key(k))
        return f"rule {r['rule'].get('type')} from {labels or 'no premises'}"
    return f"{(r.get('certificate') or {}).get('type')} certificate" if r else "no support"


def goal_verdict(ledger, out, items):
    """Display only: the DECIDE goal's verdict as `status` and `frontier` print it, or None without a goal."""
    goal = goal_of(ledger)
    if goal is None:
        return None
    name = goal.get("name", "Q")
    gc = goal_claims(ledger)
    yes_held, yes_cond = goal_side_held(ledger, out, items, gc[True])
    no_held, no_cond = goal_side_held(ledger, out, items, gc[False])
    firm_yes, firm_no = yes_held and not yes_cond, no_held and not no_cond
    return ("CONFLICT between held goal claims (report to the builder)" if firm_yes and firm_no
            else f"decided: {name}" if firm_yes else f"decided: not {name}" if firm_no else "undecided")


def ledger_with(ledger, extra):
    """An in-memory copy of the ledger with `extra` records appended; nothing is written."""
    trial = Ledger.__new__(Ledger)
    trial.__dict__.update(ledger.__dict__)
    trial.records = ledger.records + list(extra)
    trial._refused = trial._claims = trial._supports = trial._withdrawn = None
    return trial


def cmd_withdraw(ledger, args):
    """Withdraw a claim, permanently: fold before and after, refuse if other held claims would lose their hold without
    --cascade, then append the record and print what changed."""
    if any(r["label"] == args.label for r in ledger.covers()):
        raise Refusal(f"{args.label} is a legacy cover record, not a claim; it decides nothing", "withdrawal", "-",
                      "nothing to withdraw: refile the cover with `gp cover` if it is still wanted")
    claim = ledger.claim(args.label)
    key, scope = claim["key"], show_scope(claim["scope"])
    prior = ledger.withdrawals().get(key)
    if prior:
        raise Refusal(f"{args.label} is already {withdrawn_text(prior)}", "withdrawal", scope,
                      "nothing to do: a withdrawal is permanent")
    reason = (args.reason or "").strip()
    if not reason:
        raise Refusal("a withdrawal needs a reason", "withdrawal", scope, 'give --reason "why the claim is withdrawn"')
    if claim.get("family") in ("goal", "spine"):
        raise Refusal(f"{args.label} is a {claim['family']} claim, which gp files itself", "withdrawal", scope,
                      "withdraw the cover or the exclusion it rests on instead")
    record = {"op": "withdraw", "label": args.label, "key": key, "reason": reason}
    before, items0 = state(ledger)
    trial = ledger_with(ledger, [record])
    after, items1 = state(trial)
    lost, seen = [], {key}
    for c in ledger.claims():
        if c["key"] not in seen and items0[c["key"]]["held"] and not items1[c["key"]]["held"]:
            seen.add(c["key"])
            lost.append(c)
    if lost and not args.cascade:
        raise Refusal(f"withdrawing {args.label} would un-hold {len(lost)} other held "
                      f"claim{'s' if len(lost) > 1 else ''}: " + ", ".join(c["label"] for c in lost), "withdrawal", scope,
                      "rerun with --cascade to withdraw it anyway, or support those claims without it first")
    v0, v1 = goal_verdict(ledger, before, items0), goal_verdict(trial, after, items1)
    ledger.append(record)
    was = f"was held at {scope}" if items0[key]["held"] else "was not held"
    print(f"withdrawn: {args.label} (key {key}): {reason}; {was}")
    if lost:
        print("  no longer held: " + "; ".join(f"{c['label']} ({support_text(ledger, c)})" for c in lost))
    if v0 != v1:
        print(f"  goal verdict: {v0} -> {v1}")
    print(f"  note: {OLD_READERS}")


# --- commands ---------------------------------------------------------------------------------

COVER_PREMISES = ("AMP-THM1", "GP74-NON-UD", "ENUM-COMPLETE")


def cmd_cover(ledger, args):
    """File a candidate cover as two Kernel claims (release plan A2): `cover n m L` (CoverComplete n m L, held only by an
    exhaustive list: the cover_all receipt) and `spine n m L` (if the cover is complete then not Q(n, m), held by rule
    spine from one held exclusion over ℝ per graph). Named premises are metadata on an open cover: never evidence."""
    spine_label = f"{args.label}:spine"
    taken = {c["label"] for c in ledger.claims()} | {r["label"] for r in ledger.covers()}
    for label in (args.label, spine_label):
        if label in taken:
            raise Refusal(f"label {label!r} is taken", "ledger", "-", "choose a new label")
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
    system = {"n": args.n, "m": args.m, "graphs": [c["edges"] for c in cands]}
    # Named premises say the cover rests on them: it stays open. Without them the list must be exhaustive, and the
    # Kernel's own check (cover_all) is offered as its evidence.
    cover = file_goal_family(ledger, args.label, "cover", system, "COVER_COMPLETE", premises,
                             candidates=cands, supports=supports, premise_notes=notes)
    spine = file_goal_family(ledger, spine_label, "spine", system, "SPINE")
    tag = "".join(f" [premise {p}: OPEN]" for p in cover["named_premises"])
    print(f"cover {args.label} filed: {len(cands)} candidate{'s' if len(cands) != 1 else ''} for n = {args.n}, "
          f"m = {args.m}" + ("; exhaustive" if exh and not premises else "") + tag + f"; spine {spine['label']} filed")
    if not premises:  # the Kernel's check, not this one, holds the cover
        goal_attempt(ledger, cover, {"certificate": {"type": "cover_all"}}, "the exhaustive list")
    goal_sync(ledger)


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
    ledger.append({"op": "init", "schema": SCHEMA, "gp_version": GP_VERSION, "min_reader": GP_VERSION,
                   "statement_sha256": sha(statement.read_bytes())})
    print(f"ledger started for {statement}")
    ensure_goal_claims(ledger)


def cmd_restate(ledger, args):
    """Record a deliberate change to campaign.json as a ledger event carrying both hashes."""
    path = ledger.dir / "campaign.json"
    data = path.read_bytes()
    old, new = ledger.bound_statement_sha(), sha(data)
    if new == old:
        raise Refusal("the campaign statement is unchanged", "statement binding", "-", "nothing to restate")
    json.loads(data.decode("utf-8"))  # a restated statement must still parse
    ledger.append({"op": "restate", "old_sha256": old, "new_sha256": new, "reason": args.reason})
    version = sum(r["op"] == "restate" for r in ledger.records) + 1
    print(f"statement restated (version {version}): {old[:12]} -> {new[:12]}")


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
        m = matroid_file(ledger.dir, args.matroid, ledger.statement)
        enc = encoder.encode(m)
        system = {k: enc[k] for k in ("variables", "equations", "nonzero")}
        inputs = [f"encoding:{enc['digest']}"]
        premises = [enc["premise"]["name"]]
    else:
        system = system3a(read_json(args.system, "system"))
        inputs = [f"system:{sha(json.dumps(system, sort_keys=True).encode())}"]
        premises = []
    refuse_zero_guards(system, show_scope(scope_of(args)))
    args.target = target_of(args)
    refuse_unparsable(system, args.target, show_scope(scope_of(args)))
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


# --- zero guards (DECISIONS 2026-10-13, N6a) --------------------------------------------------
#
# A guard that is the zero polynomial holds nowhere: an EMPTY claim over it ("no point with every guard
# nonzero") is true vacuously, and a NONEMPTY claim over it is false. `gp` refuses such a claim when it is
# filed and when a receipt is submitted for it. Zero is decided on the guard's canonical form over ℚ: the
# text is read by a mirror of the runner's parser, `GPProfile.Poly.parse` (the same tokens, precedence,
# unary minus, literal exponents and division by nonzero constants), so `0` and `(x+1)^2 - x^2 - 2*x - 1`
# are both zero. A guard this reader does not read is left to the runner, which refuses it on elaboration.
# Subtler vacuity (a guard vanishing wherever the equations do) is not detected: see LIMITS.md.

class _Unread(Exception):
    """A guard the zero test does not read; the runner decides it."""


ZERO_TEST_TERMS = 100_000  # the largest intermediate polynomial the zero test expands
ZERO_TEST_EXPONENT = 4096  # the largest exponent it expands


def _guard_tokens(text):
    """`GPProfile.Poly.tokenize`: ASCII numerals, identifiers and the operators + - * / ^ ( ), with ** as ^."""
    out, i = [], 0
    while i < len(text):
        c = text[i]
        if c in " \t\r\n":
            i += 1
        elif "0" <= c <= "9":
            j = i
            while j < len(text) and "0" <= text[j] <= "9":
                j += 1
            out.append(("num", int(text[i:j])))
            i = j
        elif c.isascii() and (c.isalpha() or c == "_"):
            j = i
            while j < len(text) and text[j].isascii() and (text[j].isalnum() or text[j] == "_"):
                j += 1
            out.append(("ident", text[i:j]))
            i = j
        elif c == "*" and text[i + 1:i + 2] == "*":
            out.append(("op", "^"))
            i += 2
        elif c in "+-*/^()":
            out.append(("op", c))
            i += 1
        else:
            raise _Unread(f"unexpected character {c!r}")
    return out


def _p_add(a, b, sign=1):
    out = dict(a)
    for m, c in b.items():
        v = out.get(m, 0) + sign * c
        if v:
            out[m] = v
        else:
            out.pop(m, None)
    return out


def _p_mul(a, b):
    if len(a) * len(b) > ZERO_TEST_TERMS * 10:
        raise _Unread("too large to expand")
    out = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            m = tuple(x + y for x, y in zip(ma, mb))
            v = out.get(m, 0) + ca * cb
            if v:
                out[m] = v
            else:
                out.pop(m, None)
    if len(out) > ZERO_TEST_TERMS:
        raise _Unread("too large to expand")
    return out


def guard_canonical(variables, text):
    """The canonical form over ℚ of one polynomial text in `variables`, as {exponents: Fraction}; {} is zero.
    Raises _Unread where `GPProfile.Poly.parse` would refuse the text (or it is too large to expand here)."""
    n = len(variables)
    toks = _guard_tokens(text)
    pos = 0
    one = (0,) * n

    def peek(kind, value=None):
        return pos < len(toks) and toks[pos][0] == kind and (value is None or toks[pos][1] == value)

    def take():
        nonlocal pos
        pos += 1
        return toks[pos - 1]

    def expr():  # a leading - or + applies to the first term
        if peek("op", "-"):
            take()
            acc = _p_add({}, term(), -1)
        elif peek("op", "+"):
            take()
            acc = term()
        else:
            acc = term()
        while peek("op", "+") or peek("op", "-"):
            sign = 1 if take()[1] == "+" else -1
            acc = _p_add(acc, term(), sign)
        return acc

    def term():
        acc = power()
        while peek("op", "*") or peek("op", "/"):
            if take()[1] == "*":
                acc = _p_mul(acc, power())
            else:
                d = power()
                if set(d) - {one}:
                    raise _Unread("division by a nonconstant polynomial")
                if not d:
                    raise _Unread("division by zero")
                acc = {m: c / d[one] for m, c in acc.items()}
        return acc

    def power():  # one literal exponent, as in the runner: x^2^3 is refused
        base = atom()
        if peek("op", "^"):
            take()
            if not peek("num"):
                raise _Unread("exponent must be a natural literal")
            k = take()[1]
            if k == 0:
                return {one: Fraction(1)}
            if not base:
                return {}
            if k > ZERO_TEST_EXPONENT:
                raise _Unread("exponent too large to expand")
            out = {one: Fraction(1)}
            for _ in range(k):
                out = _p_mul(out, base)
            return out
        return base

    def atom():  # a unary minus here binds tighter than ^: in x - -y^2 the square is of -y
        if peek("num"):
            v = take()[1]
            return {one: Fraction(v)} if v else {}
        if peek("ident"):
            name = take()[1]
            if name not in variables:
                raise _Unread(f"undeclared variable: {name}")
            i = variables.index(name)
            return {tuple(1 if j == i else 0 for j in range(n)): Fraction(1)}
        if peek("op", "("):
            take()
            e = expr()
            if not peek("op", ")"):
                raise _Unread("missing ')'")
            take()
            return e
        if peek("op", "-"):
            take()
            return _p_add({}, atom(), -1)
        raise _Unread("unexpected token")

    try:
        p = expr()
    except RecursionError:
        raise _Unread("nested too deeply")
    if pos != len(toks):
        raise _Unread("trailing input")
    return p


def zero_guards(system):
    """The guards of a claim's system that are the zero polynomial: [(where, index, text)], where `where` is ""
    for the system's own `nonzero` list and "branch b " for a cover branch's."""
    variables = system.get("variables") if isinstance(system, dict) else None
    if not isinstance(variables, list) or not all(isinstance(v, str) for v in variables):
        return []
    groups = [("", system.get("nonzero"))]
    branches = system.get("branches")
    if isinstance(branches, list):
        groups += [(f"branch {b} ", br.get("nonzero")) for b, br in enumerate(branches) if isinstance(br, dict)]
    found = []
    for where, guards in groups:
        for i, g in enumerate(guards if isinstance(guards, list) else []):
            try:
                zero = isinstance(g, str) and guard_canonical(variables, g) == {}
            except _Unread:
                zero = False
            if zero:
                found.append((where, i, g))
    return found


def refuse_zero_guards(system, scope_text):
    """N6a: refuse a claim whose guard is the zero polynomial, naming the guard by its index."""
    found = zero_guards(system)
    if not found:
        return
    where, i, g = found[0]
    shown = g if len(g) <= 60 else g[:57] + "..."
    more = f" ({len(found) - 1} more guard{'s' if len(found) > 2 else ''} {'are' if len(found) > 2 else 'is'} " \
           f"zero too)" if len(found) > 1 else ""
    raise Refusal(f"{where}guard {i} ({shown}) is the zero polynomial{more}: no point makes it nonzero, so the "
                  f"claim's conditions hold nowhere", "nonzero guards", scope_text,
                  f"drop {where}guard {i}, or write the condition you meant (a nonzero constant guard is allowed)")


# --- polynomial text that does not parse (0.50 Trials C3b) ------------------------------------
#
# The runner parses every claim's polynomial text at each fold, so one unparsable text (say `--target @f`)
# used to stop the whole ledger from folding. `claim` now refuses such text, and a ledger that already holds
# one sets that claim aside (not held, with a notice) and folds the rest.

def poly_syntax_error(variables, text):
    """Why `GPProfile.Poly.parse` would refuse `text` on syntax alone, or None. It mirrors the runner's grammar
    (see guard_canonical) without expanding, so it is cheap on large text; a division by a nonconstant is
    left to the runner."""
    if not isinstance(text, str):
        return "not a polynomial text"
    try:
        toks = _guard_tokens(text)
    except _Unread as err:
        return str(err)
    pos = 0

    def peek(kind, value=None):
        return pos < len(toks) and toks[pos][0] == kind and (value is None or toks[pos][1] == value)

    def take():
        nonlocal pos
        pos += 1

    def expr():
        if peek("op", "-") or peek("op", "+"):
            take()
        term()
        while peek("op", "+") or peek("op", "-"):
            take()
            term()

    def term():
        power()
        while peek("op", "*") or peek("op", "/"):
            take()
            power()

    def power():
        atom()
        if peek("op", "^"):
            take()
            if not peek("num"):
                raise _Unread("exponent must be a natural literal")
            take()

    def atom():
        if peek("num"):
            take()
        elif peek("ident"):
            if toks[pos][1] not in variables:
                raise _Unread(f"undeclared variable: {toks[pos][1]}")
            take()
        elif peek("op", "("):
            take()
            expr()
            if not peek("op", ")"):
                raise _Unread("missing ')'")
            take()
        elif peek("op", "-"):
            take()
            atom()
        else:
            raise _Unread("unexpected token" if pos < len(toks) else "unexpected end of text")

    try:
        expr()
    except _Unread as err:
        return str(err)
    except RecursionError:
        return "nested too deeply"
    return "trailing input" if pos != len(toks) else None


def claim_texts(system, target=None):
    """Every polynomial text of a claim, with where it sits: equations[i], nonzero[i], signs[i], branch b's, target."""
    out = []
    if not isinstance(system, dict):
        return out

    def group(prefix, s):
        for name in ("equations", "nonzero"):
            for i, t in enumerate(s.get(name) or []):
                out.append((f"{prefix}{name}[{i}]", t))
        for i, sg in enumerate(s.get("signs") or []):
            out.append((f"{prefix}signs[{i}]", sg[0] if isinstance(sg, (list, tuple)) and sg else sg))

    group("", system)
    for b, br in enumerate(system.get("branches") or []):
        if isinstance(br, dict):
            group(f"branch {b} ", br)
    if target is not None:
        out.append(("target", target))
    return out


def text_error(system, target=None):
    """The first polynomial text of a claim that does not parse, as 'where: why', or None."""
    variables = system.get("variables") if isinstance(system, dict) else None
    if not isinstance(variables, list):
        return None
    for where, text in claim_texts(system, target):
        why = poly_syntax_error(variables, text)
        if why:
            return f"{where}: {why}"
    return None


def refuse_unparsable(system, target, scope_text):
    why = text_error(system, target)
    if why:
        raise Refusal(f"a polynomial text does not parse ({why})", "exact statements", scope_text,
                      "fix that text: integers, fractions p/q, declared variables, + - * / ^ and parentheses")


def target_of(args):
    """--target TEXT, or --target @FILE for a long target read from a file."""
    t = args.target
    if isinstance(t, str) and t.startswith("@"):
        path = Path(t[1:])
        if not path.is_file():
            raise Refusal(f"--target {t}: no such file", "exact statements", "-", "give an existing file after @")
        return path.read_text(encoding="utf-8").strip()
    return t


def unparsable_claims(ledger):
    """Claims whose polynomial text does not parse: {key: 'where: why'}."""
    return {c["key"]: why for c in ledger.claims()
            if (why := text_error(c.get("system"), c.get("target")))}


def fold_failure(out):
    """Why a runner's output is not a fold, or None. The runners report a parse or elaboration failure as
    `elaboration` and a fold failure as `error`; either means the output has no items (0.51: a check of only
    `error` once took an elaboration failure for an empty fold, and the ledger's claims vanished)."""
    return out.get("error") or out.get("elaboration")


def fold_ledger(ledger, extra=None, candidates=False):
    """One fold of the ledger (with trial receipts swapped in). If it fails, claims whose text does not parse are
    set aside, not held and with a notice, and the rest folds; the normal path parses nothing in Python."""
    out = run_profile(surface(ledger, extra), candidates)
    if fold_failure(out) and ledger.set_aside is None:
        ledger.set_aside = unparsable_claims(ledger)
        if ledger.set_aside:
            out = run_profile(surface(ledger, extra), candidates)
    if ledger.set_aside and not fold_failure(out):
        out["items"] = out["items"] + [
            {"key": k, "held": False, "support": "", "premises": [],
             "check": {"result": "set aside", "diagnosis": why}} for k, why in ledger.set_aside.items()]
    return out


def set_aside_notes(ledger):
    labels = {c["key"]: c["label"] for c in ledger.claims()}
    return [f"{labels.get(k, k)}: {why} does not parse; it is not held, and the rest of the ledger folds without it"
            for k, why in (ledger.set_aside or {}).items()]


def prepare(ledger, label, receipt_path):
    """A receipt read and checked before any fold: its claim, its JSON and its exact numbers."""
    claim = ledger.claim(label)
    withdrawn = ledger.withdrawals().get(claim["key"])
    if withdrawn:  # labels stay taken: a withdrawn claim is never supported again
        raise Refusal(f"{label} was withdrawn ({withdrawn.get('at')}: {withdrawn.get('reason')})", "withdrawal",
                      show_scope(claim["scope"]), "file the corrected claim under a new label")
    refuse_zero_guards(claim.get("system"), show_scope(claim["scope"]))  # a claim filed before N6a
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
    out = fold_ledger(ledger, {claim["key"]: receipt})
    if out.get("error") or out.get("elaboration"):
        return None, elaboration_refusal(ledger, label, claim, receipt, digest, out)
    return record(ledger, label, claim, receipt, digest, out)


def cmd_submit(ledger, args):
    claim, receipt, digest = prepare(ledger, args.label, args.receipt)
    line, body = submit_one(ledger, args.label, claim, receipt, digest)
    if line:
        print(line)
        goal_sync(ledger)
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
        return fold_ledger(ledger, {c["key"]: rc for _, c, rc, _ in batch})

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
    goal_sync(ledger)
    if refused:
        raise Refusal(f"{refused} of {len(entries)} batch items refused (listed above)", "batch", "-",
                      "fix each refused item and resubmit it")


def state(ledger, candidates=False):
    out = fold_ledger(ledger, candidates=candidates)
    if fold_failure(out):
        raise Refusal(f"the ledger does not fold: {fold_failure(out)}", "ledger fold", "-",
                      "find the record it names; a claim whose text does not parse is set aside automatically, "
                      "so this is a receipt or rule record")
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
        if self.cofinite:
            head = "every characteristic" if self.char0 else "every prime characteristic"
            return head + (f" except {prime_set(self.primes)}" if self.primes else "")
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
    if claim["key"] in ledger.withdrawals():
        return "withdrawn"
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
    wd, rests = ledger.withdrawals(), rests_on_withdrawn(ledger, items)
    for c in ledger.claims():
        i = items[c["key"]]
        st = label_status(i, ledger, c)
        premise = premise_tag(out, c) if c["named_premises"] and st == "held" else ""
        earned = f"; earned, unclaimed: {show_reach(widened[c['key']])}" if c["key"] in widened else ""
        gone = (f"; {withdrawn_text(wd[c['key']])}" if st == "withdrawn" else
                f"; not held: rests on withdrawn {', '.join(rests[c['key']])}" if c["key"] in rests else "")
        rows.append(f"{st:8} {c['label']:28} {c['kind']:12} {show_scope(c['scope'])}{earned}{premise}{gone}")
    print("\n".join(rows) if rows else "no claims")
    for line in legacy_notes(ledger):
        print(f"{'legacy':8} {line}")
    for line in matroid_notes(ledger):
        print(f"{'unread':8} {line}")
    for line in set_aside_notes(ledger):
        print(f"{'unparsed':8} {line}")
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


def receipt_ids(support):
    """A support's receipt identities for `explain`: the stored receipt (the SHA-256 of receipts/<sha256>.json, or of
    an inline receipt's canonical bytes), and the submitted file's SHA-256 when it differs."""
    stored, submitted = receipt_digest(support), support.get("receipt_sha256")
    return f"stored receipt {stored[:12]}" + (f", submitted file {submitted[:12]}" if submitted and submitted != stored
                                              else "")


def cmd_explain(ledger, args):
    out, items = state(ledger)
    legacy = next((r for r in ledger.covers() if r["label"] == args.label), None)
    if legacy is not None:
        print(f"{args.label}: legacy cover record (filed before release plan A2): refile with `gp cover`; "
              "it decides nothing")
        return
    wd, rests = ledger.withdrawals(), rests_on_withdrawn(ledger, items)
    if ledger.claim(args.label).get("family") == "cover":
        if ledger.claim(args.label)["key"] in wd:
            print(f"{args.label}: {withdrawn_text(wd[ledger.claim(args.label)['key']])}; not held")
        return explain_cover(ledger, out, items, ledger.claim(args.label))
    claims = {c["key"]: c for c in ledger.claims()}
    supports = ledger.supports()

    def tree(key, depth):
        c = claims[key]
        i = items[key]
        pad = "  " * depth
        verdict = ("held" if i["held"] else f"not held ({withdrawn_text(wd[key])})" if key in wd else
                   f"not held (rests on withdrawn {', '.join(rests[key])})" if key in rests else "not held")
        line = f"{pad}{c['label']}: {c['kind']} at {show_scope(c['scope'])}: {verdict}"
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
            print(f"{pad}  by {s['receipt']['certificate'].get('type')} certificate ({receipt_ids(s)}): "
                  f"{humane(i.get('diagnosis', i.get('mechanism', '')))}")
            if s["receipt"]["certificate"].get("type") == "case_tree":
                print(f"{pad}  meaning: {case_tree_meaning(s['receipt']['certificate'])}")
        elif "certificate" in s["receipt"]:
            cert = s["receipt"]["certificate"]
            print(f"{pad}  by {cert.get('type')} certificate ({receipt_ids(s)}), reach "
                  f"{show_reach((i.get('check') or {}).get('reach'))}")
        else:
            print(f"{pad}  by rule {s['receipt']['rule'].get('type')} from:")
            for p in s["receipt"].get("premises", []):
                tree(p, depth + 2)
    tree(ledger.claim(args.label)["key"], 0)


def frontier_goal(ledger, out, items):
    """Display only: the DECIDE goal's obligations, read from the fold (no admission, no writes). Return whether the
    goal remains unresolved, even when every filed claim is held."""
    goal = goal_of(ledger)
    if goal is None:
        return False
    name = goal.get("name", "Q")
    params = goal_udg(goal)
    cond = conditional(ledger, out)
    gc = goal_claims(ledger)
    yes_held, yes_cond = goal_side_held(ledger, out, items, gc[True])
    no_held, no_cond = goal_side_held(ledger, out, items, gc[False])
    firm_yes, firm_no = yes_held and not yes_cond, no_held and not no_cond
    conflict = firm_yes and firm_no
    verdict = ("CONFLICT between held goal claims (report to the builder)" if conflict
               else f"decided: {name}" if firm_yes else f"decided: not {name}" if firm_no else "undecided")
    print(f"\nGoal: DECIDE {name}")
    if params is not None and None in gc.values():
        print("  the goal claims are not filed yet: the next claim, submit or cover command files them")
    via = rule_premises(ledger, gc[True]) if yes_held else []
    if yes_held:
        print(f"  {name}: held by {', '.join(ledger.claim_by_key(k)['label'] for k in via)} (Kernel: "
              f"{gc[True]['label']}, rule realize; {RULE_THEOREMS['realize']})" +
              (f", modulo {', '.join(sorted(yes_cond))}, so not decided" if yes_cond else ""))
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
        elif c["key"] not in via:
            print(f"  held claim {c['label']} does not count for {name}: {yes_gap(ledger, out, items, c)}")
        for p in sorted(cond[c["key"]]):
            print(f"  claim {c['label']}: premise {p}: OPEN")
    state_, selected, selected_join, other = spine_verdict(ledger, out, items, goal)
    if no_held:
        print(f"  not {name}: held by cover {selected['label'] if selected else '-'} (Kernel: {gc[False]['label']}, "
              f"rule decide; {RULE_THEOREMS['decide']})" +
              (f", modulo {', '.join(sorted(no_cond))}, so not decided" if no_cond else ""))
    elif selected and state_ == "spine":
        print(f"  not {name}: open; the Kernel holds spine {selected_join['spine']['label']} (if cover "
              f"{selected['label']} is complete then not {name}); the cover is open")
    elif selected:
        print(f"  not {name}: open by cover {selected['label']}")
    elif params is None:
        print(f"  not {name}: not held; the goal states no graph parameters")
    else:
        print(f"  not {name}: not held; no cover for n = {params[0]}, m = {params[1]}")
    for line in legacy_notes(ledger):
        print(f"  {line}")
    for cv in cover_claims(ledger):
        j = selected_join if cv is selected else cover_join(ledger, out, items, cv)
        if cv in other:
            print(f"  {other_cover_text(cv, params)}")
        elif cv is not selected:
            print(f"  cover {cv['label']}: alternative cover for the goal")
        for p in j["open"]:
            print(f"  cover {cv['label']}: premise {p}: OPEN")
        for row in j["missing"]:
            print(f"  cover {cv['label']}: missing held exclusion over R for {graph_text(row['graph'])}")
            for c in row["others"]:
                if items[c["key"]]["held"]:
                    print(f"    held claim {c['label']} does not count: {exclusion_gap(out, items, c)}")
        if j["spine"] and not j["spine_held"] and not j["missing"]:
            why = last_refusal(ledger, j["spine"])
            print(f"  cover {cv['label']}: spine {j['spine']['label']} not held" + (f": {why}" if why else ""))
    print(f"  verdict: {verdict}")
    unresolved = conflict or not (firm_yes or firm_no)
    if unresolved:
        print("  goal frontier remains open")
    return unresolved


def cmd_frontier(ledger, args):
    out, items = state(ledger)
    # Goal-family claims (A2) are the goal section's obligations, rendered by `frontier_goal`. Withdrawn claims are off
    # the frontier; a claim that rests on one says so.
    wd, rests = ledger.withdrawals(), rests_on_withdrawn(ledger, items)
    open_ = [c for c in ledger.claims() if not items[c["key"]]["held"] and c.get("family") not in GOAL_FAMILIES
             and c["key"] not in wd]
    # Re-check each refused claim's last receipt in one pass, so the reason reads in today's terms;
    # the recorded refusal stays in the ledger and is shown when the wording has changed.
    last = {c["key"]: ledger.attempts(c["label"])[-1] for c in open_ if ledger.attempts(c["label"])}
    now = {}
    if last:
        trial = fold_ledger(ledger, {k: r["receipt"] for k, r in last.items()})
        if not (trial.get("error") or trial.get("elaboration")):
            titems = {i["key"]: i for i in trial["items"]}
            open_by_key = {}
            for c in open_:
                open_by_key.setdefault(c["key"], c)
            now = {k: refusal_of(titems[k], open_by_key[k], ledger, titems)
                   for k in last if k in titems and not titems[k]["held"]}
    for c in open_:
        if c["key"] in rests:
            print(f"{c['label']}: not held: rests on withdrawn {', '.join(rests[c['key']])}; smallest fix: support it "
                  "without the withdrawn claim, or file the corrected claim under a new label")
            continue
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
        print("frontier empty: every claim is held" + (f" or withdrawn ({len(wd)} withdrawn)" if wd else "") +
              (" and the goal is decided" if goal_of(ledger) else ""))


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
    wd = ledger.withdrawals()
    for c in ledger.claims():
        if c["key"] in wd:
            w = wd[c["key"]]
            rows.append({"kind": "withdrawn claim", "claim": c["label"], "source": f"withdraw {w.get('at', '-')}",
                         "reliability": "withdrawn by its owner; not held", "completeness": w.get("reason", "")})
        elif not items[c["key"]]["held"]:
            rows.append({"kind": "open item", "claim": c["label"], "source": "ledger",
                         "reliability": "open", "completeness": "untagged"})
        if c["named_premises"] and items[c["key"]]["held"] and premise_state(out, c) == "OPEN":
            rows.append({"kind": "open premise", "claim": c["label"], "source": c["inputs"][0],
                         "reliability": "held modulo premise", "completeness": f"{', '.join(c['named_premises'])} OPEN"})
    for cv in ledger.covers():
        rows.append({"kind": "legacy cover record", "claim": cv["label"], "source": "cover", "reliability":
                     "decides nothing", "completeness": "refile with `gp cover`"})
    for cv in cover_claims(ledger):
        if cv.get("named_premises") and not items[cv["key"]]["held"] and cv["key"] not in wd:
            rows.append({"kind": "open premise", "claim": cv["label"], "source": "cover", "reliability": "cover open",
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
            missing[key] = "withdrawn" if key in ledger.withdrawals() else "not held"
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
    """Raw ledger lifecycle records as Kernel events. `gp` writes none: a withdrawal is a `withdraw` record, sent to the
    runners as a withdrawn key (`surface`). Raw records reach only the merge guard, and `merge` refuses them."""
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
    # A split claim whose receipts are 3a on one branch and 3b on the other goes to gp_ledger3, which reads both.
    trial = {k: r for k in split for r in (ours_s[k]["receipt"], theirs_s[k]["receipt"]) if is_3b_receipt(r)}
    plan = surface(merged, trial)
    plan["lifecycle"] = lifecycle_events(merged.records)
    part3 = plan.get("_3b")
    if part3:
        # `surface3` offers the first claim per key; the guard also sees every other claim filed under a 3b key.
        routed, first = set(part3["requested"]), {}
        supports = merged.supports()
        for c in merged.claims():
            if c["key"] in routed and first.setdefault(c["key"], c) is not c:
                part3["claims"].append(claim_surface3(c, receipt_of(supports, c, trial)))
    for k in sorted(split):
        where = part3 if part3 and k in part3["requested"] else plan
        entry = next(c for c in where["claims"] if c["key"] == k)
        head = {x: v for x, v in entry.items() if x not in ("certificate", "rule", "premises")}
        where["claims"] += [dict(head, **ours_s[k]["receipt"]), dict(head, **theirs_s[k]["receipt"])]
    return merged, new, plan, split


def cmd_merge(ledger, args):
    """Land another branch's records here only if the merged log still folds; else change nothing."""
    other = Ledger(args.other)
    if not other.records:
        raise merge_refusal(f"no ledger at {args.other}", "merge from a campaign directory with a ledger")
    other.check_schema()
    if other.bound_statement_sha() != ledger.bound_statement_sha():
        raise merge_refusal("the branches bind different versions of the campaign statement",
                            "restate on one branch so both bind the same statement, then merge again")
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
    for r in new:
        c = by_key.get(r.get("key")) if r["op"] == "withdraw" else None
        if r["op"] == "withdraw" and (c is None or c["label"] != r.get("label")):
            raise merge_refusal(f"a withdraw record names no claim of the merged ledger ({r.get('label')!r}, key "
                                f"{r.get('key')})", "restore the other branch's ledger from its history")
    if plan["lifecycle"]:
        raise merge_refusal("the merged log folds, but it carries raw retraction or supersession records, which "
                            "the profile does not apply yet", "merge without them; withdraw a claim with `gp withdraw`")
    # A withdrawal persists in the merged event set, so it beats a support filed on the other branch, in either merge
    # order (W1, W2; the fold depends only on the set of records). Say what it un-holds here.
    theirs_wd = [r for r in new if r["op"] == "withdraw"]
    try:
        before = state(ledger)[1] if theirs_wd else None
        _, after = state(merged)
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
    ops = {o: sum(r["op"] == o for r in new) for o in ("claim", "support", "refused", "withdraw")}
    print(f"merged {len(new)} records ({ops['claim']} claims, {ops['support']} supports, {ops['refused']} refusals" +
          (f", {ops['withdraw']} withdrawals" if ops["withdraw"] else "") + "); the merged log folds")
    for r in theirs_wd:
        print(f"  withdrawn on the other branch: {r['label']}: {r.get('reason', '')}")
    rests = rests_on_withdrawn(merged, after)
    if before is not None:
        lost = [c for c in ledger.claims() if before.get(c["key"], {}).get("held") and not after[c["key"]]["held"]]
        for c in {c["key"]: c for c in lost}.values():
            why = rests.get(c["key"])
            print(f"  no longer held here: {c['label']}" + (f" (rests on withdrawn {', '.join(why)})" if why else
                                                          " (withdrawn)"))
    theirs_keys = {r["key"] for r in new if r["op"] in ("claim", "support") and type(r.get("key")) is int}
    mine_wd = set(merged.withdrawals()) - {r["key"] for r in theirs_wd}
    for c in {c["key"]: c for c in merged.claims() if c["key"] in theirs_keys}.values():
        if c["key"] in mine_wd:
            print(f"  not held here: {c['label']}, supported on the other branch (withdrawn here)")
        elif c["key"] in rests:
            print(f"  not held here: {c['label']}, from the other branch (rests on withdrawn "
                  f"{', '.join(rests[c['key']])})")


def main(argv=None):
    ap = argparse.ArgumentParser(prog="gp", description=__doc__.splitlines()[0])
    ap.add_argument("--version", action="version", version=f"gp {GP_VERSION}")
    ap.add_argument("--campaign", required=True)
    sub = ap.add_subparsers(dest="command", required=True)
    sub.add_parser("init")
    rg = sub.add_parser("register", help="Lane P: bind a statement code to a declaration or a prose text")
    rg.add_argument("decl", nargs="*", help="a declaration; several are registered with one bind (0.54)")
    rg.add_argument("--batch", help="a file of `DECL [NAME]` lines, or a JSON list of {decl|prose, as, process}: one "
                                    "bind for all (0.54)")
    rg.add_argument("--as", dest="as_", help="the statement's name in this ledger (default: the declaration's last component)")
    rg.add_argument("--prose", help="a prose statement's text (never holdable)")
    rg.add_argument("--process", help="with --prose: a process condition (review, merge, wording, fidelity-review)")
    rg.add_argument("--bridge", help="DIR:LABEL: a bridge code, the literal 3a/3b meaning of that claim (P2)")
    dc = sub.add_parser("discharge", help="Lane P: discharge a premise of a claim by a claim of that premise")
    dc.add_argument("label")
    dc.add_argument("--premise", required=True)
    dc.add_argument("--by", required=True)
    dc.add_argument("--as", dest="as_")
    fd = sub.add_parser("fidelity", help="Lane P: record a statement's fidelity review")
    fd.add_argument("name")
    fd.add_argument("--level", required=True)
    fd.add_argument("--by", required=True)
    fd.add_argument("--ref", required=True)
    pr = sub.add_parser("present", help="Lane P: record a presentation of a claim; views mark it OVERSTATED")
    pr.add_argument("label")
    pr.add_argument("--venue", required=True)
    pr.add_argument("--tag", required=True)
    pr.add_argument("--premise", action="append")
    pr.add_argument("--locator")
    bd = sub.add_parser("bind", help="Lane P: build the campaign package and run the P binder")
    bd.add_argument("--replay", action="store_true", help="replay the package with lean4checker (tier 2 final)")
    rs = sub.add_parser("restate", help="record a deliberate change to campaign.json as a versioned ledger event")
    rs.add_argument("--reason", required=True, help="why the statement changed")
    c = sub.add_parser("claim")
    c.add_argument("label", nargs="?")
    c.add_argument("--batch", help="Lane P: a JSON list or JSON lines of claim specs, filed with one bind, all or "
                                   "nothing (0.55)")
    src = c.add_mutually_exclusive_group()
    src.add_argument("--matroid")
    src.add_argument("--system")
    src.add_argument("--nf", help="a number-field point file (3b)")
    c.add_argument("--udg", help="a graph (graph6, or a file with graph6 or JSON {n, edges}): its unit-distance system")
    c.add_argument("--gauge", action="store_true", help="with --udg: pin the first edge at (0, 0), (1, 0)")
    c.add_argument("--kind")
    c.add_argument("--target")
    c.add_argument("--lean", help="Lane P: a registered Lean statement (or ¬X)")
    c.add_argument("--prose", help="Lane P: a registered prose statement")
    c.add_argument("--theorem", help="Lane P: the lean_theorem that holds the claim")
    c.add_argument("--from", dest="from_", help="Lane P: weaken this claim (same statement, more premises)")
    c.add_argument("--comparator", help="Lane P: the theorem a Comparator solution applies (tier 1; emits the challenge)")
    c.add_argument("--bridge", help="Lane P: DIR:LABEL (or LABEL), the bridged 3a/3b claim of a bridge code (tier 3)")
    c.add_argument("--condition", action="append", help="Lane P: an open process condition (registered with --process)")
    sc = c.add_mutually_exclusive_group()
    sc.add_argument("--char", type=int)
    sc.add_argument("--char0", action="store_true")
    sc.add_argument("--outside")
    sc.add_argument("--real", action="store_true", help="over the field R (3b)")
    sc.add_argument("--semireal", action="store_true", help="in every semireal field (3b)")
    sc.add_argument("--rat-field", action="store_true", help="over the field Q itself (3b)")
    c.add_argument("--premise", action="append", help=f"a named OPEN premise, e.g. {KUMMER}[=q1,q2,...]")
    c.add_argument("--goal", choices=["yes", "no"], help="file the claim as the DECIDE goal (yes) or its negation (no)")
    cv = sub.add_parser("cover", help="a candidate cover: the Kernel claims cover n m L and spine n m L")
    cv.add_argument("label")
    cv.add_argument("--candidates", required=True, help="JSON list of graphs (graph6 or {n, edges}), or graph6 lines")
    cv.add_argument("--n", type=int, required=True)
    cv.add_argument("--m", type=int, required=True)
    cv.add_argument("--premise", action="append", help="AMP-THM1, GP74-NON-UD[=names], ENUM-COMPLETE[=manifest-sha]")
    cv.add_argument("--supports", help="labels of claims backing the cover's argument (shown, not used)")
    s = sub.add_parser("submit")
    s.add_argument("label")
    s.add_argument("receipt", nargs="?")
    s.add_argument("--hand-proof", dest="hand_proof", help="Lane P: a hand proof file (recorded only)")
    s.add_argument("--state", help="Lane P: a hand proof's declared state, complete or sketch")
    s.add_argument("--condition", action="append", help="Lane P: a reviewer's condition, a registered statement")
    s.add_argument("--script", help="Lane P: an exact script's output (recorded only)")
    s.add_argument("--numerical", help="Lane P: numerical evidence (recorded only)")
    s.add_argument("--external", help="Lane P: a checker's log from another pin or repository (recorded only)")
    s.add_argument("--tier", type=int, help="Lane P: the tier an --external checker earned")
    s.add_argument("--what", help="Lane P: what checked an --external warrant")
    s.add_argument("--citation", help="Lane P: a published result's reference (recorded only, tier 5; 0.55)")
    s.add_argument("--theorem-number", dest="theorem_number", help="Lane P: with --citation, the result's number")
    s.add_argument("--locator", help="Lane P: with --citation, where in the reference (page, section)")
    s.add_argument("--doi", help="Lane P: with --citation, the reference's DOI")
    s.add_argument("--file", help="Lane P: with --citation, a local copy of the reference (re-hashed on every view)")
    s.add_argument("--comparator", help="Lane P: a Comparator receipt (tools/lanep-comparator.sh)")
    s.add_argument("--log", help="Lane P: the Comparator log, if not next to the receipt")
    sb = sub.add_parser("submit-batch", help='a JSON list of {"label", "receipt"}, folded once')
    sb.add_argument("batch")
    wd = sub.add_parser("withdraw", help="withdraw a claim permanently; its warrants are retracted on every fold")
    wd.add_argument("label")
    wd.add_argument("--reason", required=True, help="why the claim is withdrawn (recorded in the ledger)")
    wd.add_argument("--cascade", action="store_true", help="withdraw even if other held claims lose their hold")
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
    p_flags = bool(args.command == "claim" and (args.lean or args.prose or args.batch) or
                   args.command == "submit" and (args.hand_proof or args.script or args.numerical or args.external or
                                                 args.comparator or args.citation is not None or
                                                 any(x is not None for x in (args.theorem_number, args.locator,
                                                                             args.doi, args.file))))
    if args.command == "claim" and args.label is None and not args.batch:
        ap.error("the following arguments are required: label")
    if args.command == "claim" and not p_flags and (args.kind is None or not any(
            getattr(args, k) not in (None, False) for k in ("char", "char0", "outside", "real", "semireal", "rat_field"))):
        ap.error("the following arguments are required: --kind and one of --char --char0 --outside --real "
                 "--semireal --rat-field")
    if args.command == "submit" and not p_flags and args.receipt is None:
        ap.error("the following arguments are required: receipt")
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8")  # Lean output and labels are not cp1252
    ledger = Ledger(args.campaign)
    if args.command != "init" and not ledger.records:
        print("refused: no ledger here [rule: ledger; scope: -]; smallest fix: run `gp init`", file=sys.stderr)
        return 2
    try:
        if args.command != "init":
            ledger.check_schema()  # before any record is read as v1
        if args.command not in ("init", "restate"):
            ledger.verify_statement()  # every command runs against the bound statement (release plan A1)
        if args.command not in ("init", "restate") and lanep.is_p(ledger):
            if args.command not in lanep.COMMANDS:
                raise Refusal(f"`gp {args.command}` is not a Lane P command", "lane P", "-",
                              f"use one of {', '.join(sorted(lanep.COMMANDS))}")
            lanep.COMMANDS[args.command](ledger, args)
            return 0
        if args.command in lanep.P_ONLY or p_flags:
            raise Refusal(f"`gp {args.command}` with Lane P arguments needs a P campaign", "lane P", "-",
                          'start a campaign whose campaign.json says "profile": "P"')
        if args.command in ("claim", "cover", "submit", "submit-batch"):
            ensure_goal_claims(ledger)  # an older ledger's first filing command files the goal claims (A2)
        {"init": cmd_init, "restate": cmd_restate, "claim": cmd_claim, "cover": cmd_cover, "submit": cmd_submit,
         "submit-batch": cmd_submit_batch, "withdraw": cmd_withdraw, "status": cmd_status,
         "explain": cmd_explain, "frontier": cmd_frontier, "tailings": cmd_tailings,
         "emit-lean": cmd_emit_lean, "merge": cmd_merge}[args.command](ledger, args)
    except Refusal as r:
        b = r.body
        print(f"refused: {b['message']} [rule: {b['rule']}; scope: {b['scope']}]; smallest fix: {b['smallest_fix']}",
              file=sys.stderr)
        for line in r.detail:
            print(line, file=sys.stderr)
        return 1
    return 0


class _Globals:
    """This module's globals as attributes, for tools/gp_lanep.py (live: it sees later assignments)."""


_globals = _Globals()
_globals.__dict__ = globals()
lanep.G = _globals


if __name__ == "__main__":
    sys.exit(main())
