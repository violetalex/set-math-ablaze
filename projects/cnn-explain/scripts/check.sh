#!/usr/bin/env bash
# 唯一验收口径。等价于 `mathlean check`。
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 -I tools/run_mathlean.py check "$@"
