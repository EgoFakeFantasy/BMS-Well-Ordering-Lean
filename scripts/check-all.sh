#!/usr/bin/env bash
# 构建全部源模块和扫描工具；任何 warning 都使检查失败。需要 Bash 4 或以上。
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
shopt -s globstar nullglob

lean_targets=(YesMetaZFC)
for lean_source in YesMetaZFC/**/*.lean; do
  lean_module="${lean_source%.lean}"
  lean_targets+=("${lean_module//\//.}")
done

printf '检查 %s 个 Lean 模块及 prove_auto_sweep 工具\n' "${#lean_targets[@]}"
lake --wfail build "${lean_targets[@]}"
lake --wfail build prove_auto_sweep
