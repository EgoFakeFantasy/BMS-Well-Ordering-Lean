import YesMetaZFC.BMS.ExpansionOrder

/-!
# 初始数组的对角展开

`diagonal_l h n` 有 `n+1` 列：第 `i` 列先写成 `h` 个 `i` 再附加一个零，
随后按原规格裁去底部全零行。附加零正是高一行 seed 展开后失去的那一行；
此定义只使用有限列表和裁剪，不通过 expansion 定义对角数组。

`diagonal_l h 1 = validSeed h` 只识别一个成员。高度归纳仍须证明任意 `n`
对应的对角数组可达，不能以这个单一成员的可达性替代全称结论。
-/

namespace YesMetaZFC.BMS.SeedExpansion

private def columns (h n : Nat) : BMSArray :=
  (List.range (n + 1)).map (fun i => List.replicate h i ++ [0])

private theorem rectangular_columns (h n : Nat) :
    rectangular (columns h n) = true := by
  apply rectangular_iff_exists_uniformHeight.mpr
  refine ⟨h + 1, ?_⟩
  intro c hc
  rcases List.mem_map.mp hc with ⟨i, _, rfl⟩
  simp

/-- 由 `0,…,n` 的常值列及原裁剪操作构成的真实有限数组。 -/
def diagonal_l (h n : Nat) : ValidArray where
  raw := trimZeroRows (columns h n)
  rectangular_eq := rectangular_trimZeroRows (rectangular_columns h n)
  trimmed_eq := trimZeroRows_idempotent _

/-- 对角数组的原始列表规格；最下面附加的零行会被裁剪。 -/
theorem raw_l (h n : Nat) :
    (diagonal_l h n).raw = trimZeroRows
      ((List.range (n + 1)).map (fun i => List.replicate h i ++ [0])) := rfl

/-- 参数 `n` 对应 `n+1` 列，包括 `n=0` 时唯一的全零列。 -/
theorem length_l (h n : Nat) : (diagonal_l h n).raw.length = n + 1 := by
  simp [raw_l, length_trimZeroRows]

private theorem copy_column (h i : Nat) :
    copyBlock (seed (h + 1)) [List.replicate (h + 1) 0] h 0 i
      (List.replicate (h + 1) 1) = [List.replicate h i ++ [0]] := by
  simp only [copyBlock, List.head?_cons, Option.getD_some, List.mapIdx_singleton]
  apply congrArg (fun c : List Nat => [c])
  apply List.ext_getElem?
  intro r
  simp only [List.getElem?_mapIdx, List.getElem?_replicate]
  by_cases h₁ : r < h
  · have h₂ : r < h + 1 := by omega
    simp [ascending, h₁, h₂]
  · by_cases h₂ : r = h
    · subst r
      simp [ascending]
    · have h₃ : ¬ r < h + 1 := by omega
      simp [ascending, h₁, h₃]

/-- 裁剪前，每个复制块就是常值列后附加一个零。 -/
theorem raw_expand_l (h n : Nat) :
    expandRaw (seed (h + 1)) n =
      (List.range (n + 1)).map (fun i => List.replicate h i ++ [0]) := by
  have h₀ : maximalParentRow
      [List.replicate (h + 1) 0, List.replicate (h + 1) 1] = some h := by
    simpa [seed] using maximalParentRow_seed_succ h
  have h₁ : parent h
      [List.replicate (h + 1) 0, List.replicate (h + 1) 1] 1 = some 0 := by
    simpa [seed] using parent_seed_one_of_lt (Nat.lt_succ_self h)
  have h₂ (i : Nat) : copyBlock
      [List.replicate (h + 1) 0, List.replicate (h + 1) 1]
      [List.replicate (h + 1) 0] h 0 i (List.replicate (h + 1) 1) =
        [List.replicate h i ++ [0]] := by
    simpa [seed] using copy_column h i
  simp [expandRaw, seed, h₀, h₁, slice, h₂, ← List.map_eq_flatMap]

/-- 高一行 seed 的任意索引展开，等于明确给出的对角数组。 -/
theorem expand_l (h n : Nat) :
    (validSeed (h + 1)).expand n = diagonal_l h n := by
  apply ValidArray.ext
  simpa only [ValidArray.raw_expand, raw_validSeed, BMS.expand, raw_l] using
    congrArg trimZeroRows (raw_expand_l h n)

/-- 前一高度的 seed 只对应对角族中索引为 `1` 的成员。 -/
theorem one_l (h : Nat) : diagonal_l h 1 = validSeed h := by
  rw [← expand_l, validSeed_succ_expand_one]

/-- 高一行 seed 可达，当且仅当全部真实的一次展开后继可达。 -/
theorem acc_l (h : Nat) :
    Acc Step (validSeed (h + 1)) ↔ ∀ n, Acc Step (diagonal_l h n) := by
  constructor
  · intro h₀ n
    rw [← expand_l]
    by_cases h₁ : (validSeed (h + 1)).expand n = validSeed (h + 1)
    · exact h₁.symm ▸ h₀
    · exact h₀.inv ⟨⟨n, rfl⟩, h₁⟩
  · intro h₀
    apply Acc.intro
    intro a h₁
    rcases h₁.1 with ⟨n, rfl⟩
    simpa only [expand_l] using h₀ n

end YesMetaZFC.BMS.SeedExpansion
