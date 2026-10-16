#!/usr/bin/env bash
# Lane P (GP 0.52 P2): run stock Comparator on one emitted P challenge, on WSL's own ext4, and write its receipt.
#
# usage (inside WSL or Linux, from the workspace root):
#   bash tools/lanep-comparator.sh <campaign-dir> <config.json>     run Comparator, write <config>.receipt.json + .log
#   bash tools/lanep-comparator.sh --prepare <campaign-dir>          build the pinned tools, fetch the Mathlib cache
#
# `gp claim L --lean X ... --comparator T` emits the challenge and solution modules into the campaign package
# (<root>/GPComparator/K<key>/) and the Comparator config into <campaign-dir>/comparator/. This script copies the
# package's sources to ${GP_LANEP_HOME:-~/gp-lanep}/<campaign> on ext4 (docs/ROPE-CHECKLIST.md "Running Comparator
# under WSL": never a /mnt/<drive> mount), keeping that copy's .lake between runs; builds Comparator, lean4export and
# landrun at the revisions pinned in .github/workflows/comparator.yml (the v4.35.0-rc3 tags); fetches the Mathlib
# cache; builds the challenge; and runs Comparator once (one job at a time; it refuses below 8 GB available).
#
# The receipt binds the challenge's SHA-256, the theorem name, the Comparator, lean4export and landrun revisions, the
# toolchain, the SHA-256 of the package sources it ran on (gp's tree identity, computed before the copy's
# packagesDir is pointed at its own .lake) and the SHA-256 of the log. `gp submit L --comparator <receipt>` checks it.
# Exit 0 iff Comparator printed "Your solution is okay".
set -euo pipefail

die() { echo "lanep-comparator: $*" >&2; exit 2; }
step() { echo "[$(date -u +%H:%M:%S)] $*"; }
prepare=0
if [ "${1:-}" = "--prepare" ]; then prepare=1; shift; fi
[ $# -ge 1 ] || die "usage: bash tools/lanep-comparator.sh [--prepare] <campaign-dir> [<config.json>]"
ws=$(cd "$(dirname "$0")/.." && pwd)
camp=$(cd "$1" && pwd) || die "no such campaign directory: $1"
config=""
if [ $prepare -eq 0 ]; then
  [ $# -ge 2 ] || die "give the Comparator config gp emitted (<campaign-dir>/comparator/K<key>.json)"
  config=$(cd "$(dirname "$2")" && pwd)/$(basename "$2")
  [ -f "$config" ] || die "no such config: $2"
fi
export PATH="$HOME/.elan/bin:$HOME/.local/bin:/usr/local/go/bin:$PATH"
for t in elan lake git go rsync python3; do command -v $t >/dev/null || die "$t not found on PATH"; done

pin() { sed -n "s/^ *$1: \([0-9a-f]\{40\}\).*/\1/p" "$ws/.github/workflows/comparator.yml" | head -n 1; }
COMPARATOR_REV=$(pin COMPARATOR_REV); LEAN4EXPORT_REV=$(pin LEAN4EXPORT_REV); LANDRUN_REV=$(pin LANDRUN_REV)
[ -n "$COMPARATOR_REV" ] && [ -n "$LEAN4EXPORT_REV" ] && [ -n "$LANDRUN_REV" ] || die "cannot read the pins"
TOOLCHAIN=$(tr -d '\r\n' < "$ws/profile/lean-toolchain")

read -r pkgrel name < <(python3 -c 'import json,sys; c=json.load(open(sys.argv[1],encoding="utf-8")); print(c.get("package","lean"), c.get("name","campaign"))' "$camp/campaign.json")
case "$pkgrel" in /*) pkg=$pkgrel ;; *) pkg="$camp/$pkgrel" ;; esac
[ -d "$pkg" ] || die "no campaign package at $pkg"
[ "$(tr -d '\r\n' < "$pkg/lean-toolchain")" = "$TOOLCHAIN" ] || die "the package is not pinned to $TOOLCHAIN"

# gp's tree identity (tools/gp_lanep.py package_sources, tools/gp.py tree_identity): computed on the source package.
tree=$(python3 - "$camp/campaign.json" "$pkg" <<'PY'
import hashlib, json, sys
from pathlib import Path
c = json.load(open(sys.argv[1], encoding="utf-8")); pkg = Path(sys.argv[2])
files = [pkg / f for f in ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain") if (pkg / f).exists()]
for r in c.get("roots") or []:
    if (pkg / f"{r}.lean").exists():
        files.append(pkg / f"{r}.lean")
    files += sorted((pkg / r).rglob("*.lean")) if (pkg / r).is_dir() else []
lines = "".join(f"{hashlib.sha256(f.read_bytes()).hexdigest()}  {f.relative_to(pkg).as_posix()}\n"
                for f in sorted(files, key=lambda f: f.as_posix()))
print(hashlib.sha256(lines.encode("utf-8")).hexdigest())
PY
)

home="${GP_LANEP_HOME:-$HOME/gp-lanep}"
case "$home" in /mnt/*) die "GP_LANEP_HOME must be on ext4, not $home" ;; esac
dest="$home/$name"
mkdir -p "$dest"
rsync -a --delete --exclude '.lake/' "$pkg/" "$dest/"
# The copy keeps its own packages (Mathlib at the manifest's revisions) in its own .lake.
sed -i '/^packagesDir *=/d' "$dest/lakefile.toml"
python3 - "$dest/lake-manifest.json" <<'PY'
import json, sys
p = sys.argv[1]; m = json.load(open(p, encoding="utf-8")); m["packagesDir"] = ".lake/packages"
open(p, "w", encoding="utf-8").write(json.dumps(m, indent=1) + "\n")
PY
cd "$dest"
LOGS="$dest/.lake/gp-comparator"
mkdir -p "$LOGS"

T="${GP_LANEP_TOOLS:-$HOME/gp-lanep-tools}/${COMPARATOR_REV:0:12}-${LEAN4EXPORT_REV:0:12}-${LANDRUN_REV:0:12}"
mkdir -p "$T/src" "$T/bin"
if [ ! -x "$T/bin/comparator" ] || [ ! -x "$T/bin/lean4export" ] || [ ! -x "$T/bin/landrun" ]; then
  for spec in "comparator https://github.com/leanprover/comparator.git $COMPARATOR_REV" \
              "lean4export https://github.com/leanprover/lean4export.git $LEAN4EXPORT_REV" \
              "landrun https://github.com/Zouuup/landrun.git $LANDRUN_REV"; do
    set -- $spec
    [ -d "$T/src/$1" ] || git clone --quiet "$2" "$T/src/$1" || die "cloning $1 failed"
    git -C "$T/src/$1" checkout --quiet "$3" || die "checking out $1 $3 failed"
  done
  for t in comparator lean4export; do
    step "building $t ($TOOLCHAIN)"
    [ "$(tr -d '\r\n' < "$T/src/$t/lean-toolchain")" = "$TOOLCHAIN" ] || die "$t at its pin is not on $TOOLCHAIN"
    (cd "$T/src/$t" && lake build "$t" >"$LOGS/build-$t.log" 2>&1) || die "building $t failed (see $LOGS/build-$t.log)"
    cp "$T/src/$t/.lake/build/bin/$t" "$T/bin/$t"
  done
  step "building landrun"
  (cd "$T/src/landrun" && go build -o "$T/bin/landrun" cmd/landrun/main.go) >"$LOGS/build-landrun.log" 2>&1 \
    || die "building landrun failed (see $LOGS/build-landrun.log)"
fi
export PATH="$T/bin:$PATH"

step "fetching the Mathlib cache"
lake exe cache get >"$LOGS/cache.log" 2>&1 || die "lake exe cache get failed (see $LOGS/cache.log)"
if [ $prepare -eq 1 ]; then
  step "building the package"
  lake build >"$LOGS/build-package.log" 2>&1 || die "the package does not build (see $LOGS/build-package.log)"
  step "prepared $dest (tools in $T)"; exit 0
fi

read -r chal sol thm < <(python3 -c 'import json,sys; c=json.load(open(sys.argv[1],encoding="utf-8")); print(c["challenge_module"], c["solution_module"], " ".join(c["theorem_names"]))' "$config")
chalfile="$dest/$(echo "$chal" | tr . /).lean"
[ -f "$chalfile" ] || die "the challenge $chal is not in the package (emit it with gp claim ... --comparator)"
avail=$(free -g | awk '/^Mem:/{print $7}')
[ "${avail:-0}" -ge 8 ] || die "only ${avail} GB available; Comparator needs about 8 (run one job at a time)"
cp "$config" "$dest/.lake/gp-comparator/config.json"
step "building the challenge $chal"
lake build "$chal" >"$LOGS/build-challenge.log" 2>&1 || die "the challenge does not build (see $LOGS/build-challenge.log)"
stem=$(basename "$config" .json)
log="$LOGS/$stem.log"
hardening=none
step "comparator $stem ($thm)"
t0=$SECONDS
set +e
if systemd-run --user --wait --pipe -q true 2>/dev/null; then
  hardening="systemd-run --user, RestrictAddressFamilies=~AF_UNIX"
  systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --wait --pipe -q \
    -E PATH="$PATH" -E HOME="$HOME" --working-directory "$PWD" -- lake env comparator .lake/gp-comparator/config.json >"$log" 2>&1
else
  lake env comparator .lake/gp-comparator/config.json >"$log" 2>&1
fi
rc=$?
set -e
secs=$((SECONDS - t0))
okay=false
grep -q "Your solution is okay" "$log" && okay=true
out="$(dirname "$config")/$stem"
cp "$log" "$out.log"
python3 - "$out.receipt.json" <<PY
import hashlib, json, sys
log = open("$log", "rb").read()
r = {"schema": "gp-comparator-receipt/v1", "theorem": "$thm", "challenge_module": "$chal",
     "solution_module": "$sol", "challenge_sha256": hashlib.sha256(open("$chalfile", "rb").read()).hexdigest(),
     "tree_sha256": "$tree", "toolchain": "$TOOLCHAIN", "comparator_rev": "$COMPARATOR_REV",
     "lean4export_rev": "$LEAN4EXPORT_REV", "landrun_rev": "$LANDRUN_REV", "hardening": "$hardening",
     "exit": $rc, "okay": "$okay" == "true", "seconds": $secs, "log": "$stem.log",
     "log_sha256": hashlib.sha256(log).hexdigest()}
open(sys.argv[1], "w", encoding="utf-8", newline="\n").write(json.dumps(r, indent=1, sort_keys=True) + "\n")
PY
step "comparator exit $rc after ${secs} s: $([ $okay = true ] && echo okay || echo NOT okay); receipt $out.receipt.json"
[ $okay = true ] && [ $rc -eq 0 ]
