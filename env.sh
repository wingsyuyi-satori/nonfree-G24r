#!/usr/bin/env bash
LEAN_TWENTYFOUR_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [ -x "$LEAN_TWENTYFOUR_ROOT/tools/lean-4.24.0-linux/bin/lean" ]; then
  export PATH="$LEAN_TWENTYFOUR_ROOT/tools/lean-4.24.0-linux/bin:$PATH"
fi
export XDG_CACHE_HOME="$LEAN_TWENTYFOUR_ROOT/.cache"
if [ -d "$LEAN_TWENTYFOUR_ROOT/tools/cargo-home" ]; then
  export CARGO_HOME="$LEAN_TWENTYFOUR_ROOT/tools/cargo-home"
  export RUSTUP_HOME="$LEAN_TWENTYFOUR_ROOT/tools/rustup-home"
  export PATH="$CARGO_HOME/bin:$PATH"
fi
