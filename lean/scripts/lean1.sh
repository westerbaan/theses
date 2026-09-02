#!/usr/bin/env bash
# Serialised single-file Lean compile.  USE THIS, never a bare `lean` or `lake build`.
#
# Measured 2026-08-29: one `lean` on Theses/A/VN/Division.lean peaks at 7.2 GB
# RSS.  This box has 14 GB and no swap, so TWO concurrent compiles exhaust it
# and the kernel OOM-kills whatever it likes -- on 2026-08-29 that was six
# agents at once, five of which lost all their unwritten work.
#
# Every compile, in every agent, goes through this script.  It holds an
# exclusive lock for the duration, so concurrent callers queue instead of
# colliding.  Waiting a minute for the lock is always cheaper than an OOM.
#
# Usage:  scripts/lean1.sh Theses/A/VN/Division.lean
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
LP=".lake/build/lib/lean"
for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
exec flock -w 14400 /tmp/lean-compile.lock \
  env LEAN_PATH="$LP" lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 "$@"
