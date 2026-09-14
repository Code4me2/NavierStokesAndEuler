#!/usr/bin/env bash
# Cached-only focused elaboration; never builds dependencies or touches old outputs.
set -euo pipefail
ROOT=/home/velvet/worktrees/unforced-restart-20260909T202951Z
cd "$ROOT"
[[ $# == 2 && $1 == Research/UnforcedRestart/Round2/*.lean && $2 == Research/UnforcedRestart/Round2/* ]]
SRC=$1; OUT=$2
mkdir -p "$OUT/lib/$(dirname "${SRC%.lean}")"
exec 9>Research/UnforcedRestart/Round2/Integration/focused.lock
flock 9
# Lean selects a search root per top-level module; make historical research
# dependencies visible in this exploratory output root (explicit cached reuse).
for p in "$ROOT"/Research/UnforcedRestart/integration/validation/lib/Research/UnforcedRestart/*; do
  [[ $(basename "$p") == integration ]] && continue
  ln -s "$p" "$OUT/lib/Research/UnforcedRestart/$(basename "$p")"
done
PREFIX=$(lean --print-prefix)
LP="$ROOT/$OUT/lib:$ROOT/Research/UnforcedRestart/integration/validation/lib:$ROOT/.lake/build/lib/lean"
for p in "$ROOT"/.lake/packages/*/.lake/build/lib/lean; do LP="$LP:$p"; done
set +e
systemd-run --user --wait --pipe -p WorkingDirectory="$ROOT" -p CPUQuota=100% -p MemoryMax=6G -p MemorySwapMax=0 -p TasksMax=32 \
  /bin/bash -c 'set -eu; cg=$(awk -F: '\''$1==0 {print $3}'\'' /proc/self/cgroup); d=/sys/fs/cgroup$cg; test "$(<"$d/cpu.max")" = "100000 100000"; test "$(<"$d/memory.max")" = 6442450944; test "$(<"$d/memory.swap.max")" = 0; test "$(<"$d/pids.max")" = 32; exec timeout 600 env -u LEAN_SRC_PATH LEAN_NUM_THREADS=1 LEAN_PATH="$1" "$2/bin/lean" -j1 -DautoImplicit=false -DwarningAsError=true -o "$4/lib/${3%.lean}.olean" -i "$4/lib/${3%.lean}.ilean" "$3"' -- "$LP" "$PREFIX" "$SRC" "$OUT" > "$OUT/compile.log" 2>&1
rc=$?
printf '%s\n' "$rc" > "$OUT/compile.exit"
exit "$rc"
