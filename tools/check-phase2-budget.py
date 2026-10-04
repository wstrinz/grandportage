"""Conservative Phase 2 source/documentation budget checks; no build or writes."""
import json
from pathlib import Path
import re
import subprocess
ROOT = Path(__file__).resolve().parents[1]
def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True, encoding="utf-8")
def has_executable_declaration(source):
    pattern = re.compile(r"^\s*(?:(?:private|protected|noncomputable|partial)\s+)*(def|abbrev|structure|inductive|instance|opaque)\b", re.M)
    for match in pattern.finditer(source):
        if match.group(1) in {"def", "abbrev"}:
            header = source[match.end():].split(":=", 1)[0].strip()
            if header.endswith(": Prop"):
                continue  # Erased proposition; no production executable helper.
        if match.group(1) == "structure":
            header = source[match.end():].split("where", 1)[0].strip()
            if header.endswith(": Prop"):
                continue  # Proof records are erased as well as proposition defs.
        return True
    return False

def kernel_modules():
    """Kernel tier module stems, read from the lakefile so the budget tracks the build."""
    lake = (ROOT / "phase2/lean/lakefile.toml").read_text(encoding="utf-8")
    block = lake[lake.index('name = "Kernel"'):]
    block = block[:block.index("[[lean_lib]]")] if "[[lean_lib]]" in block else block
    return {name.split(".")[-1] for name in re.findall(r'"(GP50\.\w+)"', block)}
# Phase 2.5 markdown is measured from the last Phase 2 commit. Will-authored verbatim
# authority text (the post-G2 handoff and its §1 copy) is reported, not charged.
PHASE_25_BASE = "31ae372"
VERBATIM_AUTHORITY = ("docs/GP-0.50-POST-G2-HANDOFF.md", "docs/GP-0.50-POST-G2-ADDENDUM-A.md")
def phase25_markdown():
    # Will's authority docs, and any added line copied from them verbatim (e.g. into DECISIONS.md),
    # are not builder words.
    authority = set()
    for name in VERBATIM_AUTHORITY:
        authority |= {l.strip() for l in (ROOT / name).read_text(encoding="utf-8").splitlines() if l.strip()}
    words, verbatim, current = 0, 0, None
    for line in git("diff", "--unified=0", PHASE_25_BASE, "--", "*.md").splitlines():
        if line.startswith("+++ "):
            current = line[6:] if line.startswith("+++ b/") else None
        elif line.startswith("+") and not line.startswith("+++"):
            n = len(line[1:].split())
            if current in VERBATIM_AUTHORITY or line[1:].strip() in authority:
                verbatim += n
            else:
                words += n
    return {"builder_words": words, "verbatim_authority_words": verbatim, "target": 2000}

def measure():
    baseline = json.loads((ROOT / "reports/PHASE-2-BASELINE.json").read_text(encoding="utf-8"))
    # Phase 2 closed at PHASE_25_BASE; its Markdown count is frozen there.
    change = git("diff", "--unified=0", baseline["base_commit"], PHASE_25_BASE, "--", "*.md")
    words = sum(len(line[1:].split()) for line in change.splitlines()
                if line.startswith("+") and not line.startswith("+++"))
    counts = {"logic": 0, "decoder": 0, "statement": 0, "proof": 0}
    modules = []
    for path in sorted((ROOT / "phase2/lean/GP50").rglob("*.lean")):
        source = path.read_text(encoding="utf-8")
        if "Proof" in path.stem or "Completeness" in path.stem:
            # A mixed proof/executable-helper file gets charged entirely to logic.
            category = "logic" if has_executable_declaration(source) else "proof"
        elif "Decod" in path.stem:
            category = "decoder"
        elif path.stem in {"Statement", "Semantics"}:
            category = "statement"
        else:
            category = "logic"
        size = len(source.splitlines())
        counts[category] += size
        modules.append({"path": str(path.relative_to(ROOT)), "category": category, "lines": size})
    limits = {"logic": (500, 750), "decoder": (400, 600), "statement": (80, 120)}
    failures = [f"{name} tripwire: {counts[name]} > {stop}"
                for name, (_, stop) in limits.items() if counts[name] >= stop]
    if words >= 15000:
        failures.append(f"Markdown tripwire: {words} > 15000")
    status_words = len((ROOT / "STATUS.md").read_text(encoding="utf-8").split())
    if status_words > 300:
        failures.append(f"STATUS cap: {status_words} > 300")
    for path in (ROOT / "reports").glob("PHASE-2*.md"):
        cap = 500 if path.stem == "PHASE-2-SLICE" else 800
        size = len(path.read_text(encoding="utf-8").split())
        if size > cap:
            failures.append(f"{path.name}: {size} > {cap}")
    kernel = kernel_modules()
    kernel_counts = {"logic": 0, "decoder": 0, "statement": 0, "proof": 0}
    for module in modules:
        if Path(module["path"]).stem in kernel:
            kernel_counts[module["category"]] += module["lines"]
            module["tier"] = "Kernel"
    # From Phase 2.5 (post-G2 handoff §1.6) the D8 limits bind on the Kernel tier only.
    failures = [f for f in failures if not f.split()[0] in limits]
    failures += [f"Kernel {name} tripwire: {kernel_counts[name]} > {stop}"
                 for name, (_, stop) in limits.items() if kernel_counts[name] >= stop]
    return {"baseline": baseline["base_commit"], "counts": counts, "modules": modules,
            "kernel_module_count": len(kernel), "kernel_counts": kernel_counts,
            "kernel_targets_exceeded": [name for name, (target, _) in limits.items()
                                        if kernel_counts[name] > target],
            "phase25_markdown": phase25_markdown(),
            "markdown_added_words": words, "markdown_target": 10000,
            "markdown_tripwire": 15000, "status_words": status_words,
            "targets_exceeded": [name for name, (target, _) in limits.items()
                                 if counts[name] > target],
            "failures": failures}
if __name__ == "__main__":
    result = measure()
    print(json.dumps(result, indent=2))
    raise SystemExit(1 if result["failures"] else 0)
