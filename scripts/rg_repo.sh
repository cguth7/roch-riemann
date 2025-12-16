#!/usr/bin/env bash
set -euo pipefail
Q="$*"
rg -n -S "$Q" RrLean agents state problem
