# Freeze patch — prepared only

Base: ac4155787207e2847d248cffed7be871d5dcd577 (v0.37.0).

- Adds the packet's verbatim freeze banner at the top of README.
- Repairs exactly 17 mojibake em dashes.
- Annotates private README/SPEC links; updates the SPEC status block.
- Adds KNOWN-ISSUES for containment advice and specialization conservatism.

The oracle and public repositories are unchanged. This is a proposed doc-only
v0.37.1 patch, not a release, a new tag, or a version change to executable code.

Final private-preparation audit passed on 2026-09-28. See AUDIT.json and RELEASE-HANDOFF.md for exact hashes, isolated application, publication-policy checks and the existing release-tag distinction. Preparation is verified; no release was applied or published.

Architecture follow-up: prepared README is 160 lines after joining one prose wrap; the banner is unchanged. The frozen line-limit test and regenerated patch application both pass. See ARCHITECTURE-CHECK-BOUNDARIES.json in the parent reports directory.
