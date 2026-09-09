import YesMetaZFC.BMS.Reference

/-!
# BM4 Stage 0 回归向量

这些测试冻结参考规格的计算行为。前十二项覆盖标准 seed；其余项覆盖无 parent、
单行 parent、多列 bad part、多行 ancestry 以及多副本 expansion。固定输出不是在定理中
动态生成的，因此后续重构若改变计算含义会立即使构建失败。
-/

namespace YesMetaZFC
namespace BMS
namespace Stage0Tests

structure ExpansionCase where
  name : String
  input : BMSArray
  index : Nat
  expected : BMSArray
deriving Repr

def expansionCases : List ExpansionCase := [
  ⟨"seed-0-at-0", seed 0, 0, [[]]⟩,
  ⟨"seed-0-at-1", seed 0, 1, [[]]⟩,
  ⟨"seed-1-at-0", seed 1, 0, [[]]⟩,
  ⟨"seed-1-at-1", seed 1, 1, [[], []]⟩,
  ⟨"seed-1-at-2", seed 1, 2, [[], [], []]⟩,
  ⟨"seed-2-at-0", seed 2, 0, [[]]⟩,
  ⟨"seed-2-at-1", seed 2, 1, [[0], [1]]⟩,
  ⟨"seed-2-at-2", seed 2, 2, [[0], [1], [2]]⟩,
  ⟨"seed-3-at-1", seed 3, 1, [[0, 0], [1, 1]]⟩,
  ⟨"seed-3-at-2", seed 3, 2, [[0, 0], [1, 1], [2, 2]]⟩,
  ⟨"seed-4-at-1", seed 4, 1, [[0, 0, 0], [1, 1, 1]]⟩,
  ⟨"seed-4-at-3", seed 4, 3,
    [[0, 0, 0], [1, 1, 1], [2, 2, 2], [3, 3, 3]]⟩,
  ⟨"one-row-chain-at-0", [[0], [1], [2]], 0, [[0], [1]]⟩,
  ⟨"one-row-chain-at-1", [[0], [1], [2]], 1, [[0], [1], [1]]⟩,
  ⟨"one-row-chain-at-3", [[0], [1], [2]], 3,
    [[0], [1], [1], [1], [1]]⟩,
  ⟨"no-parent-at-0", [[0], [1], [0]], 0, [[0], [1]]⟩,
  ⟨"no-parent-index-irrelevant", [[0], [1], [0]], 4, [[0], [1]]⟩,
  ⟨"two-column-block-at-1", [[0], [2], [1]], 1,
    [[0], [2], [0], [2]]⟩,
  ⟨"two-column-block-at-2", [[0], [2], [1]], 2,
    [[0], [2], [0], [2], [0], [2]]⟩,
  ⟨"two-row-trimming-at-1", [[0, 0], [1, 0], [2, 1]], 1,
    [[0], [1], [2]]⟩,
  ⟨"two-row-trimming-at-2", [[0, 0], [1, 0], [2, 1]], 2,
    [[0], [1], [2], [3]]⟩,
  ⟨"two-row-long-block-at-1", [[0, 0], [1, 0], [2, 2], [3, 1]], 1,
    [[0, 0], [1, 0], [2, 2], [3, 0], [4, 2]]⟩,
  ⟨"two-row-long-block-at-2", [[0, 0], [1, 0], [2, 2], [3, 1]], 2,
    [[0, 0], [1, 0], [2, 2], [3, 0], [4, 2], [5, 0], [6, 2]]⟩,
  ⟨"two-row-immediate-parent-at-1", [[0, 0], [1, 1], [2, 0], [3, 2]], 1,
    [[0, 0], [1, 1], [2, 0], [3, 0]]⟩,
  ⟨"three-row-at-1", [[0, 0, 0], [1, 1, 0], [2, 0, 1], [3, 2, 2]], 1,
    [[0, 0, 0], [1, 1, 0], [2, 0, 1], [3, 2, 1]]⟩,
  ⟨"three-row-at-2", [[0, 0, 0], [1, 1, 0], [2, 0, 1], [3, 2, 2]], 2,
    [[0, 0, 0], [1, 1, 0], [2, 0, 1], [3, 2, 1], [4, 4, 1]]⟩
]

theorem expansion_case_count : expansionCases.length = 26 := by
  native_decide

theorem expansion_snapshots :
    expansionCases.all (fun test => expand test.input test.index == test.expected) = true := by
  native_decide

theorem expansion_inputs_normalized :
    expansionCases.all (fun test => normalized test.input) = true := by
  native_decide

theorem expansion_outputs_normalized :
    expansionCases.all (fun test => normalized test.expected) = true := by
  native_decide

theorem expansion_snapshots_lex_decrease :
    expansionCases.all (fun test => compareArray test.expected test.input == .lt) = true := by
  native_decide

theorem seed_parent_rows :
    parent 0 (seed 3) 1 = some 0 ∧
    parent 1 (seed 3) 1 = some 0 ∧
    parent 2 (seed 3) 1 = some 0 ∧
    parent 3 (seed 3) 1 = none ∧
    maximalParentRow (seed 3) = some 2 := by
  native_decide

theorem long_block_parent_rows :
    parent 0 [[0, 0], [1, 0], [2, 2], [3, 1]] 3 = some 2 ∧
    parent 1 [[0, 0], [1, 0], [2, 2], [3, 1]] 3 = some 1 ∧
    maximalParentRow [[0, 0], [1, 0], [2, 2], [3, 1]] = some 1 := by
  native_decide

theorem seed_one_step_regression :
    expand (seed 1) 1 = seed 0 ∧
    expand (seed 2) 1 = seed 1 ∧
    expand (seed 3) 1 = seed 2 ∧
    expand (seed 4) 1 = seed 3 := by
  native_decide

end Stage0Tests
end BMS
end YesMetaZFC
