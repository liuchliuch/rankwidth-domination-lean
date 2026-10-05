#!/usr/bin/env bash
# Build unmodified upstream Comparator, exporter, checker, and real Landrun.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "$0")/.." && pwd)"
TOOLS="${RW_COMPARATOR_TOOLS_ROOT:-${XDG_CACHE_HOME:-$HOME/.cache}/rankwidth-comparator/lean4.24}"
mkdir -p "$TOOLS"
TOOLS="$(cd "$TOOLS" && pwd)"
case "$TOOLS/" in "$ROOT/"*) echo 'Tool checkout must be outside the distributed project' >&2; exit 2;; esac
[[ -z ${RW_LEAN_BIN:-} ]] || export PATH="$RW_LEAN_BIN:$PATH"
[[ "$(lean -V)" == '4.24.0' ]] || { echo 'Comparator requires exact Lean 4.24.0' >&2; exit 2; }
GO="${RW_GO:-go}"
"$GO" version | grep -Eq '^go version go1\.(2[4-9]|[3-9][0-9])\.' || {
  echo 'Go >=1.24 is required to build the pinned real Landrun; set RW_GO if needed' >&2; exit 2;
}
read_pin() { python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]][sys.argv[3]])' "$ROOT/verification/comparator/toolchain.lock.json" "$1" "$2"; }
checkout() {
  local name=$1 dir="$TOOLS/$1" url rev
  url="$(read_pin "$name" url)"; rev="$(read_pin "$name" revision)"
  if [[ ! -d "$dir/.git" ]]; then
    [[ ! -e "$dir" ]] || { echo "Refusing non-git directory $dir" >&2; exit 2; }
    git clone "$url" "$dir"
    git -C "$dir" checkout --detach "$rev"
  fi
  [[ "$(git -C "$dir" rev-parse HEAD)" == "$rev" ]] || { echo "Wrong $name revision in $dir" >&2; exit 2; }
  git -C "$dir" diff --exit-code HEAD -- >/dev/null || { echo "Modified $name checkout" >&2; exit 2; }
}
checkout comparator
checkout landrun
(cd "$TOOLS/comparator"; lake build lean4export comparator)
for name in lean4export lean4checker; do
  [[ "$(git -C "$TOOLS/comparator/.lake/packages/$name" rev-parse HEAD)" == "$(read_pin "$name" revision)" ]] || { echo "Wrong $name revision" >&2; exit 2; }
done
mkdir -p "$TOOLS/bin" "$TOOLS/go-cache" "$TOOLS/go-mod-cache"
(cd "$TOOLS/landrun"; GOCACHE="$TOOLS/go-cache" GOMODCACHE="$TOOLS/go-mod-cache" "$GO" build -trimpath -o "$TOOLS/bin/landrun" ./cmd/landrun)
ln -sfn "$TOOLS/comparator/.lake/build/bin/comparator" "$TOOLS/bin/comparator"
ln -sfn "$TOOLS/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export" "$TOOLS/bin/lean4export"
python3 - "$TOOLS" "$ROOT/verification/comparator/toolchain.lock.json" <<'PY'
import hashlib,json,pathlib,sys
root=pathlib.Path(sys.argv[1])
record={'pins':json.loads(pathlib.Path(sys.argv[2]).read_text()),'binaries':{}}
for name in ['comparator','lean4export','landrun']:
 p=root/'bin'/name
 record['binaries'][name]={'path':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
(root/'installation.json').write_text(json.dumps(record,indent=2)+'\n')
PY
printf 'Official pinned tools built at %s\n' "$TOOLS"
printf 'Run scripts/comparator-check.sh with RW_COMPARATOR_TOOLS_ROOT=%q\n' "$TOOLS"

mkdir -p "$TOOLS/adapters"
ln -sfn "$ROOT/scripts/landrun-runner.sh" "$TOOLS/adapters/landrun"
