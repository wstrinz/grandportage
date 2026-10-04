"""Addendum A §2.5e dependency layout: the executable profile is Mathlib-free and shares Hex pins with the binding."""
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
PROFILE = ROOT / "profile"
BINDING = ROOT / "binding"
KERNEL_TOOLCHAIN = (ROOT / "phase2/lean/lean-toolchain").read_text(encoding="utf-8").strip()


def manifest(package):
    return {p["name"]: p for p in json.loads((package / "lake-manifest.json").read_text(encoding="utf-8"))["packages"]}


class ProfileLayoutTests(unittest.TestCase):
    def test_profile_manifest_has_no_mathlib(self):
        names = {name.lower() for name in manifest(PROFILE)}
        self.assertFalse({n for n in names if "mathlib" in n}, names)
        self.assertNotIn("batteries", names)

    def test_profile_sources_import_no_mathlib(self):
        for source in sorted((PROFILE / "GPProfile").rglob("*.lean")) + [PROFILE / "GPProfile.lean"]:
            with self.subTest(source=source.name):
                self.assertNotRegex(source.read_text(encoding="utf-8"), re.compile(r"^import (Mathlib|Hex\w*Mathlib)", re.M))

    def test_shared_hex_revisions_agree(self):
        profile, binding = manifest(PROFILE), manifest(BINDING)
        shared = {n for n in profile if n.startswith("Hex")} & set(binding)
        self.assertTrue(shared)
        for name in sorted(shared):
            with self.subTest(package=name):
                self.assertEqual(profile[name]["rev"], binding[name]["rev"])
                self.assertEqual(profile[name]["inputRev"], "v0.6.0")

    def test_binding_requires_profile(self):
        self.assertIn("gp_profile", manifest(BINDING))
        self.assertIn('path = "../profile"', (BINDING / "lakefile.toml").read_text(encoding="utf-8"))

    def test_toolchains_agree(self):
        for package in (PROFILE, BINDING):
            with self.subTest(package=package.name):
                self.assertEqual((package / "lean-toolchain").read_text(encoding="utf-8").strip(), KERNEL_TOOLCHAIN)


if __name__ == "__main__":
    unittest.main()
