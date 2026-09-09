import YesMetaZFC.BMS.Expansion

/-!
# BM4 的生成闭包与有限 expansion 路径

本文件落实 Stage 0 冻结的关系方向：`Step smaller larger` 表示从 `larger` 一步下降到
不同的 `smaller`。生成性本身允许所有 expansion，包括退化的相等 expansion。
-/

namespace YesMetaZFC
namespace BMS

theorem normalized_seed (height : Nat) : normalized (seed height) = true := by
  simp [normalized, rectangular, seed, trimZeroRows, trimHeight,
    supportHeight_replicate_zero, supportHeight_replicate_one]

/-- 携带合法性证明的 BM4 初始数组。 -/
def validSeed (height : Nat) : ValidArray where
  raw := seed height
  rectangular_eq := by
    have h := normalized_seed height
    simp [normalized] at h
    exact h.1
  trimmed_eq := by
    have h := normalized_seed height
    simp [normalized] at h
    exact h.2

@[simp]
theorem raw_validSeed (height : Nat) : (validSeed height).raw = seed height := rfl

/-- 忽略是否相等的一次 expansion 边，供生成闭包使用。 -/
def ExpansionEdge (larger smaller : ValidArray) : Prop :=
  ∃ index, smaller = larger.expand index

/-- Stage 0 冻结的严格一步关系。 -/
def Step (smaller larger : ValidArray) : Prop :=
  ExpansionEdge larger smaller ∧ smaller ≠ larger

/-- 从某个 seed 出发、对任意 expansion 封闭的归纳生成集合。 -/
inductive Generated : ValidArray → Prop
  | seed (height : Nat) : Generated (validSeed height)
  | expand {array : ValidArray} (hGenerated : Generated array) (index : Nat) :
      Generated (array.expand index)

/-- 零步或多步 expansion；参数顺序是起点、终点。 -/
inductive ExpansionPath : ValidArray → ValidArray → Prop
  | refl (array : ValidArray) : ExpansionPath array array
  | tail {larger middle smaller : ValidArray}
      (pathToMiddle : ExpansionPath larger middle)
      (last : ExpansionEdge middle smaller) :
      ExpansionPath larger smaller

namespace ExpansionPath

theorem single {larger smaller : ValidArray} (edge : ExpansionEdge larger smaller) :
    ExpansionPath larger smaller :=
  .tail (.refl larger) edge

theorem trans {first second third : ValidArray}
    (left : ExpansionPath first second) (right : ExpansionPath second third) :
    ExpansionPath first third := by
  induction right with
  | refl => exact left
  | tail prior edge ih => exact .tail ih edge

end ExpansionPath

theorem generated_of_edge {larger smaller : ValidArray}
    (hGenerated : Generated larger) (edge : ExpansionEdge larger smaller) :
    Generated smaller := by
  rcases edge with ⟨index, rfl⟩
  exact .expand hGenerated index

theorem generated_of_step {smaller larger : ValidArray}
    (hGenerated : Generated larger) (step : Step smaller larger) :
    Generated smaller :=
  generated_of_edge hGenerated step.1

theorem generated_of_path {larger smaller : ValidArray}
    (hGenerated : Generated larger) (path : ExpansionPath larger smaller) :
    Generated smaller := by
  induction path with
  | refl => exact hGenerated
  | tail prior edge ih => exact generated_of_edge ih edge

theorem generated_iff_seed_path {array : ValidArray} :
    Generated array ↔
      ∃ height, ExpansionPath (validSeed height) array := by
  constructor
  · intro hGenerated
    induction hGenerated with
    | seed height => exact ⟨height, .refl _⟩
    | expand hGenerated index ih =>
        rcases ih with ⟨height, path⟩
        exact ⟨height, .tail path ⟨index, rfl⟩⟩
  · rintro ⟨height, path⟩
    exact generated_of_path (.seed height) path

/-- `Generated` 是包含全部 seed 且对 expansion 封闭的最小谓词。 -/
theorem generated_minimal {predicate : ValidArray → Prop}
    (hSeed : ∀ height, predicate (validSeed height))
    (hExpand : ∀ {array}, predicate array → ∀ index, predicate (array.expand index))
    {array : ValidArray} (hGenerated : Generated array) :
    predicate array := by
  induction hGenerated with
  | seed height => exact hSeed height
  | expand hGenerated index ih => exact hExpand ih index

/-- 非空的严格 expansion 路径。 -/
def StrictDescent (smaller larger : ValidArray) : Prop :=
  Relation.TransGen (fun source target => Step target source) larger smaller

theorem strictDescent_generated {smaller larger : ValidArray}
    (hGenerated : Generated larger) (descent : StrictDescent smaller larger) :
    Generated smaller := by
  induction descent with
  | single step => exact generated_of_step hGenerated step
  | tail prior step ih => exact generated_of_step ih step

end BMS
end YesMetaZFC
