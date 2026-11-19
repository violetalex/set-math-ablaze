#!/usr/bin/env bash
# 兼容旧用法；真正的实现是 `mathlean new`。
#
#   bash scripts/new_project.sh <目标目录> <库名> [mathlib 路径]
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
exec "$ROOT/bin/mathlean" new "$@"
