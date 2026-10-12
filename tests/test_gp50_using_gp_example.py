"""Release plan C1: the worked example in docs/USING-GP.md replays exactly, so the guide cannot drift.

Every ```console block in the guide is a step of the example. A line starting with `$ ` is a command;
the lines after it, up to the next command, are its output as the guide shows it. A `...` line skips
any number of output lines, and a line ending in ` ...` matches any line that starts with the rest. The example runs in a fresh copy of docs/examples/using-gp, outside the
repository, with `gp` run as a subprocess: `python <repo>/tools/gp.py`. Besides `gp`, a block may use
`mkdir DIR`, `cp FILE DEST`, `cp -r DIR DEST` and `ls DIR` (sorted names). A command whose output starts with `refused:` must
exit 1; every other command must exit 0. Backslashes in output are read as slashes (Windows paths).
"""
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
GUIDE = ROOT / "docs/USING-GP.md"
EXAMPLE = ROOT / "docs/examples/using-gp"
BLOCK = re.compile(r"^```console\n(.*?)^```$", re.S | re.M)


def steps(text):
    """The guide's example as (command, expected output lines), in order."""
    out = []
    for block in BLOCK.findall(text):
        for line in block.splitlines():
            if line.startswith("$ "):
                out.append((line[2:], []))
            elif out:
                out[-1][1].append(line)
            elif line.strip():
                raise ValueError(f"output before any command: {line!r}")
    return out


def run(command, cwd):
    """Run one example command in `cwd`: (exit code, output lines with slashes normalised)."""
    argv = shlex.split(command)
    if argv[0] == "gp":
        env = dict(os.environ, PYTHONUNBUFFERED="1", PYTHONIOENCODING="utf-8")
        p = subprocess.run([sys.executable, str(ROOT / "tools/gp.py"), *argv[1:]], cwd=cwd, env=env,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=1800)
        text = p.stdout.decode("utf-8").replace("\r\n", "\n").replace("\\", "/")
        return p.returncode, text.splitlines()
    if argv[0] == "mkdir" and len(argv) == 2:
        (cwd / argv[1]).mkdir()
    elif argv[:2] == ["cp", "-r"] and len(argv) == 4:
        shutil.copytree(cwd / argv[2], cwd / argv[3])
    elif argv[0] == "cp" and len(argv) == 3:
        shutil.copy(cwd / argv[1], cwd / argv[2])
    elif argv[0] == "ls" and len(argv) == 2:
        return 0, sorted(p.name for p in (cwd / argv[1]).iterdir())
    else:
        raise ValueError(f"the example may only use gp, mkdir, cp and ls: {command}")
    return 0, []


def matches(expected, actual):
    """Whether `actual` is `expected`, where a `...` line stands for any run of lines."""
    if not expected:
        return not actual
    if expected[0] == "...":
        return any(matches(expected[1:], actual[i:]) for i in range(len(actual) + 1))
    head = expected[0][:-4] if expected[0].endswith(" ...") else None
    same = bool(actual) and (actual[0].startswith(head) if head else expected[0] == actual[0])
    return same and matches(expected[1:], actual[1:])


def replay(work):
    """Replay the guide in `work`; yield (command, expected, code, actual) per step."""
    for command, expected in steps(GUIDE.read_text(encoding="utf-8")):
        while expected and not expected[-1].strip():
            expected = expected[:-1]
        code, actual = run(command, work)
        yield command, expected, code, actual


class UsingGpExample(unittest.TestCase):
    def test_guide_example_replays(self):
        self.assertTrue(steps(GUIDE.read_text(encoding="utf-8")), "the guide has no console steps")
        work = Path(tempfile.mkdtemp(prefix="gp-using-")) / "work"
        self.addCleanup(shutil.rmtree, work.parent, ignore_errors=True)
        self.assertFalse(work.resolve().is_relative_to(ROOT.resolve()), "the example must run outside the repo")
        shutil.copytree(EXAMPLE, work)
        for command, expected, code, actual in replay(work):
            with self.subTest(command=command):
                shown = "\n".join(actual)
                self.assertTrue(matches(expected, actual),
                                f"$ {command}\n--- the guide shows:\n" + "\n".join(expected) + f"\n--- gp printed:\n{shown}")
                refused = bool(actual) and actual[0].startswith("refused:")
                self.assertEqual(code, 1 if refused else 0, f"$ {command}\n{shown}")

    def test_matcher(self):
        self.assertTrue(matches(["a", "...", "d"], ["a", "b", "c", "d"]))
        self.assertTrue(matches(["a", "..."], ["a"]))
        self.assertFalse(matches(["a", "...", "d"], ["a", "b"]))
        self.assertFalse(matches(["a"], ["a", "b"]))
        self.assertTrue(matches(["ab ..."], ["ab cd"]))
        self.assertFalse(matches(["ab ..."], ["ac"]))


if __name__ == "__main__":
    unittest.main()
