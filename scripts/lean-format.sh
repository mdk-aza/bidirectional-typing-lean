#!/usr/bin/env bash
set -euo pipefail

f="$1"
"$HOME/go/bin/lean-fmt" "$f" > "$f.tmp"
mv "$f.tmp" "$f"