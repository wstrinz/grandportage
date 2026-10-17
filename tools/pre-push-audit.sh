#!/bin/sh
# Leak audit before a push (Will, 2026-10-17): refuse a push whose commit would put a machine path, a secret or
# a withheld campaign name into the public snapshot. It runs scripts/public_snapshot.py --audit-against the
# published public tree. The terms live in the withheld overlay; the refusal names lines, not terms.
#
# usage: sh tools/pre-push-audit.sh <commit>
# The published tree is $GP_PUBLIC_TREE, or a checkout of the public repo next to this one
# (../gp-public-alpha2). If neither exists, the audit is skipped with a warning; it never blocks for that.
# Bypass, deliberately: git push --no-verify
set -u
root=$(git rev-parse --show-toplevel) || exit 0
commit=${1:-HEAD}
public=${GP_PUBLIC_TREE:-"$root/../gp-public-alpha2"}
if [ ! -d "$public" ]; then
  echo "pre-push audit: no published tree at $public (set GP_PUBLIC_TREE); skipped" >&2
  exit 0
fi
out=$(cd "$root" && python scripts/public_snapshot.py --source-root . --revision "$commit" --audit-against "$public" 2>&1)
case "$out" in
  *'"status": "READY"'*) exit 0 ;;
esac
echo "pre-push audit refused $commit:" >&2
printf '%s\n' "$out" | grep -E '"error"|AUD1|REFUSED' >&2
echo "fix the named lines (or, deliberately, git push --no-verify)" >&2
exit 1
