#!/usr/bin/env bash
# BMS-Well-Ordering-Lean 修改：扩展上游检查，串行验证桥接工程与最终定理公理。
# 串行检查根工程、扫描工具、BMS 桥接工程及最终定理公理依赖。需要 Bash 4 或以上。
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
shopt -s globstar nullglob
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"

lean_targets=(YesMetaZFC)
for lean_source in YesMetaZFC/**/*.lean; do
  lean_module="${lean_source%.lean}"
  lean_targets+=("${lean_module//\//.}")
done

printf '检查 %s 个 Lean 模块及 prove_auto_sweep 工具\n' "${#lean_targets[@]}"
readonly lean_batch_size=64
for ((offset = 0; offset < ${#lean_targets[@]}; offset += lean_batch_size)); do
  lean_batch=("${lean_targets[@]:offset:lean_batch_size}")
  lake --wfail build "${lean_batch[@]}"
done
lake --wfail build prove_auto_sweep

printf '检查 BMS 可构造模型桥接及最终定理公理依赖\n'
(
  cd ConstructibleBridge
  lake build BMSConstructibleBridge
  lake env lean BMSConstructibleBridge/AxiomAudit.lean
)
