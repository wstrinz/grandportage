"""Tiny offline replay for the synthetic campaign fixture."""

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


expected = json.loads((ROOT / "synthetic-receipt.json").read_text(encoding="utf-8"))
observed = {
    "authority_sha256": digest(ROOT.parent / "authority" / "authority.md"),
    "proof_sha256": digest(ROOT.parent / "receipts" / "proof.txt"),
    "status": "PASS",
}
if observed != expected:
    raise SystemExit("synthetic replay mismatch")
print("synthetic replay passed")
