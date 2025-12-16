#!/usr/bin/env bash
set -euo pipefail
Q="$*"
rg -n --hidden --follow -S "$Q" .lake/packages/mathlib/Mathlib
