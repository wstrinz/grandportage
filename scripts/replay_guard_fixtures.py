"""Replay v0.32 CLI controls in fresh roots; preserve each command's full output."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

REPO = Path(__file__).resolve().parents[1]
FIXTURES = REPO / "tests/fixtures/dk_retrodiction"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--live", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    manifest = json.loads((FIXTURES / "manifest.json").read_text(encoding="utf-8"))
    for name, digest in manifest["files"].items():
        if hashlib.sha256((FIXTURES / name).read_bytes().replace(b"\r\n", b"\n")).hexdigest() != digest:
            raise ValueError("fixture digest mismatch: " + name)
    report = {"source_commit": manifest["source_commit"], "live": args.live, "steps": []}

    def run(root, case, command, expected, contains=None):
        argv = [sys.executable, "-m", "grandportage.cli", "--root", str(root)] + command
        try:
            result = subprocess.run(argv, cwd=REPO, capture_output=True, text=True,
                                    encoding="utf-8", timeout=120)
            code, out, err = result.returncode, result.stdout, result.stderr
        except subprocess.TimeoutExpired as exc:
            code = None
            out = (exc.stdout or b"").decode("utf-8", errors="replace")
            err = (exc.stderr or b"").decode("utf-8", errors="replace") + "\nRUNNER TIMEOUT"
        passed = code == expected and (contains is None or contains in out + err)
        report["steps"].append(dict(case=case, command=command, exit_code=code,
                                    expected_exit=expected, stdout=out, stderr=err, passed=passed))
        return passed

    with tempfile.TemporaryDirectory(prefix="gp-v032-") as scratch:
        for case, file, expected, marker in [
            ("D1", "D1-inference-on-family-claim/input.json", 2, "DISCHARGE"),
            ("D3-before", "D3-inert-disposition/before.json", 2, "COUNT"),
            ("D3-after", "D3-inert-disposition/after.json", 0, None),
        ]:
            root = Path(scratch) / case
            run(root, case, ["init"], 0)
            run(root, case, ["declare", "--file", str(FIXTURES / "fixtures" / file)], expected, marker)
            # A refused declaration leaves an empty graph. Its clean check is a
            # separate observation and must never mask the declaration refusal.
            run(root, case, ["check"], 1 if case == "D3-after" else 0,
                "FAMILY:C-SPLIT" if case == "D3-after" else None)
        if args.live:
            for size, name in [(96, "pass-96vars.json"), (97, "fail-97vars.json")]:
                for repeat in range(3):
                    case = "D2-%d-%d" % (size, repeat + 1)
                    root = Path(scratch) / case
                    run(root, case, ["init"], 0)
                    run(root, case, ["declare", "--file", str(FIXTURES / "fixtures/D2-witness-substitution-scaling" / name)], 0)
                    run(root, case, ["verify", "--timeout", "30"], 0, "VERIFIED         witness")
                    run(root, case, ["check"], 0)
    report["passed"] = all(step["passed"] for step in report["steps"])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("%d commands; passed=%s; %s" % (len(report["steps"]), report["passed"], args.output))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
