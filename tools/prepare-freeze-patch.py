
"""Prepare a doc-only freeze patch outside the frozen oracle."""
import difflib, re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
ORACLE = ROOT/"oracle/checkout"
out = ROOT/"reports/freeze-v0.37.1"
out.mkdir(exist_ok=True)
changes = {}
readme = (ORACLE/"README.md").read_text(encoding="utf-8")
bad = "\u00e2\u20ac\u201d"
count = readme.count(bad)
assert count == 17, ("unexpected mojibake count",count)
banner = "> *Frozen at v0.37.0. This repository remains the reference implementation and fixture source for a successor now in design. No further feature development here.*\n\n"
fixed = banner+readme.replace(bad,"\u2014")
fixed = fixed.replace("[HISTORY/](HISTORY/)", "HISTORY/ (private workspace archive; unavailable in the public snapshot)")
changes["README.md"] = (readme,fixed)
spec = (ORACLE/"SPEC.md").read_text(encoding="utf-8")
start = spec.index("All five layers are built and gated:")
end = spec.index("\n* **[QUICKSTART.md]",start)
replacement = """Frozen reference: package version 0.37.0, graph format 8, kernel epoch 12.
The release records <!--checks-->1811<!--/checks--> checks; this is a historical
release count, not a new verification run. See
[review/v0.37/README.md](review/v0.37/README.md) for the frozen boundary.
[docs/first-run/](docs/first-run/) retains the first campaign record.
Known limitations and misleading guidance are recorded in
[known issues](review/v0.37/KNOWN-ISSUES.md).

* **[COMPATIBILITY.md](COMPATIBILITY.md) — graph format 8, kernel epoch 12, field context, verifier-earned reach, and conservative migration**"""
fixed_spec = spec[:start]+replacement+spec[end:]
fixed_spec = re.sub(r"\[([^\]]+)\]\((KILL-CRITERIA\.md|HISTORY/[^)]*)\)",
                    lambda m:m.group(2)+" (private workspace material)",fixed_spec)
changes["SPEC.md"] = (spec,fixed_spec)
known = """# Known issues in frozen GP v0.37.0

The frozen implementation is retained unchanged. These are limitations of
its advice or expressiveness, not claims that the new rework is implemented.

## Point containment versus ideal containment

The NOT_BY_IDEAL finding in grandportage/check.py recommends radical
membership as an alternative way to establish containment and says every
licensed cell rests on that containment. Radical membership earns point
containment, not every coordinate-ring identity pullback. With the models
(x^2) and (x), point containment does not make x zero in Q[x]/(x^2).
IDENTITY transport needs the relevant ideal-containment or ring-map evidence.
Do not apply the radical-membership advice to those identity cells.

This is a diagnostic/admission-guidance defect. The existence of that advice
alone is not a reproduced end-to-end false-authority result.

## Specialization conservatism described as a theorem

The SPECIALIZATION table refuses EMPTY and NONEMPTY transport across a
characteristic change even with additional p-integral evidence. SPEC.md and
the specialization discharge text overstate that refusal as a theorem.

Unconditional transport is unsound. With suitable integral model data, a
p-integral unit-ideal certificate can instead be replayed after reduction,
and a p-integral rational witness can be reduced and checked in characteristic
p. Any open-locus guards must also survive reduction. The frozen table does
not express these sufficient conditions.

For example, 1=(2*x)+(1-2*x) replays modulo 3, while x=1/2 on 2*x-1=0 reduces
to x=2 modulo 3. These do not authorize arbitrary characteristic changes.

Sources: the frozen grandportage/kernel.py transport table,
grandportage/check.py NOT_BY_IDEAL finding, grandportage/discharge.py
specialization guidance, and SPEC.md's corresponding transport notes.
"""
changes["review/v0.37/KNOWN-ISSUES.md"] = ("",known)
patch = []
for name,(old,new) in changes.items():
    (out/name).parent.mkdir(parents=True,exist_ok=True)
    (out/name).write_text(new,encoding="utf-8")
    patch.extend(difflib.unified_diff(old.splitlines(keepends=True),new.splitlines(keepends=True),
                 fromfile="a/"+name if old else "/dev/null",tofile="b/"+name))
(out/"freeze-docs.patch").write_bytes("".join(patch).encode("utf-8"))
(out/"README-REVIEW.md").write_text(
    "# Freeze patch — prepared only\n\n"
    "Base: ac4155787207e2847d248cffed7be871d5dcd577 (v0.37.0).\n\n"
    "- Adds the packet's verbatim freeze banner at the top of README.\n"
    "- Repairs exactly 17 mojibake em dashes.\n"
    "- Annotates private README/SPEC links; updates the SPEC status block.\n"
    "- Adds KNOWN-ISSUES for containment advice and specialization conservatism.\n\n"
    "The oracle and public repositories are unchanged. This is a proposed doc-only\n"
    "v0.37.1 patch, not a release, a new tag, or a version change to executable code.\n",
    encoding="utf-8")
print("Prepared",len(changes),"documentation files; repaired",count,"mojibake em dashes.")
