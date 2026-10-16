#!/usr/bin/env bash
# Run a rope's REPRODUCE on WSL's own ext4 filesystem rather than on a Windows drive mounted at /mnt/<drive>.
#
# usage (inside WSL, from the workspace root on /mnt/<drive>/...):
#   bash tools/rope-ext4.sh ropes/r1a [REPRODUCE args...]
#
# Why (0.50 Trials C3a/C3b; docs/ROPE-CHECKLIST.md "Running Comparator under WSL"): on /mnt/<drive> (9p),
# unpacking the Mathlib cache took over 30 minutes and each Comparator run 21 to 86 minutes; landrun refuses
# tools stored there; `systemd-run --user` cannot see the mount, so Comparator lost its AF_UNIX hardening; and
# CRLF checkouts made lake re-hash every package. On ext4 none of this applies.
#
# The rope is copied to ${GP_ROPE_HOME:-~/gp-ropes}/<name> without its build outputs. An existing .lake there
# is kept, so the Mathlib cache, built tools and builds persist between runs. Logs stay in the ext4 copy.
set -euo pipefail

die() { echo "rope-ext4: $*" >&2; exit 1; }
[ $# -ge 1 ] || die "usage: bash tools/rope-ext4.sh <rope-dir> [REPRODUCE args...]"
src=$(cd "$1" && pwd) || die "no such rope directory: $1"
shift
[ -f "$src/REPRODUCE" ] || die "$src has no REPRODUCE"
command -v rsync >/dev/null || die "rsync not found (sudo apt install rsync)"

name=$(basename "$src")
dest="${GP_ROPE_HOME:-$HOME/gp-ropes}/$name"
case "$dest" in /mnt/*) die "GP_ROPE_HOME must be on ext4, not $dest" ;; esac
mkdir -p "$dest"

# Sources only; LF line endings come from the repository's own files (the tree is not converted).
rsync -a --delete --exclude '.lake/' --exclude 'lake-packages/' "$src/" "$dest/"
export PATH="$HOME/.elan/bin:$PATH"
command -v lake >/dev/null || die "elan/lake not found (install elan inside WSL)"

echo "rope-ext4: $src -> $dest"
cd "$dest"
start=$(date +%s)
status=0
bash REPRODUCE "$@" || status=$?
echo "rope-ext4: REPRODUCE exited $status after $(( $(date +%s) - start )) s (in $dest)"
exit $status
