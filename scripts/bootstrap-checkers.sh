#!/usr/bin/env bash
# Build the two pinned tools used by direct independent proof replay.
# Requires a working project Lean toolchain, git, and Rust/cargo.
set -euo pipefail
cd "$(dirname "$0")/.."
source ./env.sh
for tool in git lean lake cargo; do
  command -v "$tool" >/dev/null || { echo "$tool is required" >&2; exit 1; }
done
mkdir -p tools
checkout_exact() {
  local url="$1" dir="$2" rev="$3"
  if [ ! -d "$dir/.git" ]; then
    git clone --no-checkout --filter=blob:none "$url" "$dir"
    git -C "$dir" fetch --depth 1 origin "$rev"
    git -C "$dir" checkout --detach "$rev"
  fi
  [ "$(git -C "$dir" rev-parse HEAD)" = "$rev" ] || {
    echo "$dir is not at the required commit $rev; use a clean tools directory" >&2; exit 1;
  }
}
checkout_exact https://github.com/leanprover/lean4export.git tools/lean4export f7f95b22c1bff79cfbec7f32c13ced73a1b4fdcd
checkout_exact https://github.com/robsimmons/nanoda_lib.git tools/nanoda 68d5ca9db226849b41a6fff59d796ff19d0a8840
(cd tools/lean4export && lake build lean4export)
cargo build --release --locked --manifest-path tools/nanoda/Cargo.toml
printf 'Independent proof replay tools are ready.\n'
