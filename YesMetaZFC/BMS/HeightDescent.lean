import YesMetaZFC.BMS.LocalDescent
import YesMetaZFC.BMS.SeedExpansion

/-!
# 按当前高度分解下降关系

实际展开不会增加裁剪后的行数。因此全体生成数组的一步良基性，可以精确
归约为每个固定当前高度上的一步良基性。这里不是按生成轨迹的起始 seed
高度分层；固定高度的数组仍可来自任意更高 seed。

本文件只证明分层归约及零高度基例，不假定固定正高度已经良基，也不使用
序数或稳定表示。对象算术中的内部化仍需另行完成。
-/

namespace YesMetaZFC.BMS.HeightDescent

open StabilityFrame

set_option autoImplicit false

/-- 合法数组的当前行数，包含空数组与全零数组的零高度情形。 -/
def height_l (a : ValidArray) : Nat := trimHeight a.raw

/-- 合法数组的所有列恰有当前高度。 -/
theorem uniform_l (a : ValidArray) : UniformHeight (height_l a) a.raw := by
  rcases rectangular_iff_exists_uniformHeight.mp a.rectangular_eq with ⟨n, h⟩
  simpa only [height_l, a.trimmed_eq] using uniformHeight_trimZeroRows h

/-- 复制保持列长，裁剪只降低行数；任意展开指标均不增加高度。 -/
theorem expand_le_l (a : ValidArray) (i : Nat) :
    height_l (a.expand i) ≤ height_l a := by
  change trimHeight (trimZeroRows (expandRaw a.raw i)) ≤ height_l a
  rw [trimHeight_trimZeroRows]
  exact trimHeight_le_of_uniform (uniformHeight_expandRaw (uniform_l a))

/-- 严格一步边沿下降方向不增加当前高度。 -/
theorem step_le_l {a b : ValidArray} (h : Step a b) : height_l a ≤ height_l b := by
  rcases h.1 with ⟨i, rfl⟩
  exact expand_le_l b i

/-- 任意有限展开轨迹保持起点的高度上界，包括相等展开。 -/
theorem path_le_l {a b : ValidArray} (h : ExpansionPath a b) :
    height_l b ≤ height_l a := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail p h hᵢ =>
      rcases h with ⟨i, rfl⟩
      exact Nat.le_trans (expand_le_l _ i) hᵢ

/-- 高一层 seed 展开得到的整个对角族，都已落在高度 `h` 以下。 -/
theorem diagonal_le_l (h n : Nat) : height_l (SeedExpansion.diagonal_l h n) ≤ h := by
  rw [height_l, SeedExpansion.raw_l, trimHeight_trimZeroRows]
  have h₀ : UniformHeight h ((List.range (n + 1)).map (fun i => List.replicate h i)) := by
    intro c h₀
    rcases List.mem_map.mp h₀ with ⟨i, _, rfl⟩
    simp
  simpa only [trimHeight, List.foldl_map, supportHeight_append_zero] using
    trimHeight_le_of_uniform h₀

/-- 正指标时，对角数组的高度恰好是 `h`，并非仅有粗上界。 -/
theorem diagonal_eq_l (h : Nat) {n : Nat} (h₀ : 0 < n) :
    height_l (SeedExpansion.diagonal_l h n) = h := by
  apply Nat.le_antisymm (diagonal_le_l h n)
  have h₁ : List.replicate h 1 ++ [0] ∈
      (List.range (n + 1)).map (fun i => List.replicate h i ++ [0]) :=
    List.mem_map.mpr ⟨1, List.mem_range.mpr (by omega), rfl⟩
  simpa only [height_l, SeedExpansion.raw_l, trimHeight_trimZeroRows,
    supportHeight_append_zero, supportHeight_replicate_one] using
    supportHeight_le_trimHeight_of_mem h₁

/-- 固定当前高度的生成数组；不限制其生成轨迹的起始高度。 -/
abbrev fiber_l (n : Nat) := {a : GeneratedArray // height_l a.1 = n}

/-- 仅保留同一高度纤维内的实际严格一步边。 -/
def step_l (n : Nat) (a b : fiber_l n) : Prop := GeneratedStep a.1 b.1

/-- 有限高度内的纤维归纳恢复原可达性，不要求更高纤维良基。 -/
theorem acc_bounded_l {N : Nat} (h : ∀ n, n ≤ N → WellFounded (step_l n)) (n : Nat) :
    n ≤ N → ∀ a : GeneratedArray, height_l a.1 = n → Acc GeneratedStep a := by
  induction n using Nat.strongRecOn with
  | ind n hᵢ =>
      intro hN
      have h₀ : ∀ b : fiber_l n, Acc (step_l n) b → Acc GeneratedStep b.1 := by
        intro b h₀
        induction h₀ with
        | intro b _ hⱼ =>
            apply Acc.intro
            intro c h₁
            have h₂ : height_l c.1 ≤ n := by
              simpa only [b.2] using step_le_l h₁
            by_cases h₃ : height_l c.1 = n
            · exact hⱼ ⟨c, h₃⟩ h₁
            · exact hᵢ (height_l c.1) (by omega) (by omega) c rfl
      intro a h₁
      exact h₀ ⟨a, h₁⟩ ((h n hN).apply _)

/-- 自然数高度归纳结合纤维可达性归纳，恢复原关系的可达性。 -/
theorem acc_l (h : ∀ n, WellFounded (step_l n)) (n : Nat) :
    ∀ a : GeneratedArray, height_l a.1 = n → Acc GeneratedStep a :=
  acc_bounded_l (N := n) (fun k _ => h k) n (Nat.le_refl n)

/-- 高度不超过 `h` 的纤维良基性已足够控制高一层 seed 的全部后继。 -/
theorem seed_acc_l (h : Nat) (h₀ : ∀ n, n ≤ h → WellFounded (step_l n)) :
    Acc Step (validSeed (h + 1)) := by
  apply (SeedExpansion.acc_l h).mpr
  intro n
  let a : GeneratedArray := ⟨SeedExpansion.diagonal_l h n,
    by rw [← SeedExpansion.expand_l]; exact .expand (.seed (h + 1)) n⟩
  have h₁ := acc_bounded_l h₀ (height_l a.1) (diagonal_le_l h n) a rfl
  suffices ∀ b : GeneratedArray, Acc GeneratedStep b → Acc Step b.1 from this a h₁
  intro b h₂
  induction h₂ with
  | intro b _ hᵢ =>
      apply Acc.intro
      intro c h₃
      exact hᵢ ⟨c, generated_of_step b.2 h₃⟩ h₃

/-- 原一步良基性与全部固定当前高度的良基性精确等价。 -/
theorem wf_iff_l : WellFounded GeneratedStep ↔ ∀ n, WellFounded (step_l n) := by
  constructor
  · intro h n
    exact ⟨fun a => InvImage.accessible Subtype.val (h.apply a.1)⟩
  · intro h
    exact ⟨fun a => acc_l h (height_l a.1) a rfl⟩

/-- 固定高度纤维均良基时，恢复原完整严格良序，而非仅得分层命题。 -/
theorem wellOrder_l (h : ∀ n, WellFounded (step_l n)) :
    StrictWellOrder GeneratedArray GeneratedStrictDescent :=
  LocalDescent.wellOrder_of_wf_l (wf_iff_l.mpr h)

/-- 自然数值非增序列必有常值尾部，只需对初值作自然数强归纳。 -/
theorem constant_tail_l (f : Nat → Nat) (h : ∀ n, f (n + 1) ≤ f n) :
    ∃ N, ∀ k, f (N + k) = f N := by
  have h₀ : ∀ r, ∀ g : Nat → Nat, g 0 = r →
      (∀ n, g (n + 1) ≤ g n) → ∃ N, ∀ k, g (N + k) = g N := by
    intro r
    induction r using Nat.strongRecOn with
    | ind r hᵢ =>
        intro g h₁ h₂
        by_cases h₃ : ∀ k, g k = g 0
        · exact ⟨0, by simpa only [Nat.zero_add] using h₃⟩
        · rcases Classical.not_forall.mp h₃ with ⟨j, h₃⟩
          have h₄ : ∀ k, g k ≤ g 0 := by
            intro k
            induction k with
            | zero => exact Nat.le_refl _
            | succ k hⱼ => exact Nat.le_trans (h₂ k) hⱼ
          have h₅ : g j < r := by have := h₄ j; omega
          rcases hᵢ (g j) h₅ (fun k => g (j + k)) (by simp)
              (fun k => by simpa only [Nat.add_assoc] using h₂ (j + k)) with ⟨N, h₆⟩
          exact ⟨j + N, fun k => by simpa only [Nat.add_assoc] using h₆ k⟩
  exact h₀ (f 0) f rfl h

/-- 任何无限下降链最终停留在一个固定当前高度。 -/
theorem tail_l (f : Nat → GeneratedArray)
    (h : ∀ n, GeneratedStep (f (n + 1)) (f n)) :
    ∃ N, ∀ k, height_l (f (N + k)).1 = height_l (f N).1 :=
  constant_tail_l (fun n => height_l (f n).1) (fun n => step_le_l (h n))

/-- 原无限下降链存在，当且仅当某个高度纤维内存在无限下降链。 -/
theorem descent_iff_l :
    (∃ f : Nat → GeneratedArray, ∀ n, GeneratedStep (f (n + 1)) (f n)) ↔
      ∃ k, ∃ f : Nat → fiber_l k, ∀ n, step_l k (f (n + 1)) (f n) := by
  constructor
  · rintro ⟨f, h⟩
    rcases tail_l f h with ⟨N, h₁⟩
    refine ⟨height_l (f N).1, fun n => ⟨f (N + n), h₁ n⟩, ?_⟩
    intro n
    simpa only [step_l, Nat.add_assoc] using h (N + n)
  · rintro ⟨k, f, h⟩
    exact ⟨fun n => (f n).1, h⟩

/-- 零高度合法数组没有可用 parent 行。 -/
theorem zero_parent_l {a : ValidArray} (h : height_l a = 0) :
    maximalParentRow a.raw = none := by
  unfold maximalParentRow
  split
  · rfl
  · next n h₁ =>
      have h₂ : n < a.raw.length := by omega
      have h₃ : a.raw[n]? = some a.raw[n] :=
        List.getElem?_eq_some_iff.mpr ⟨h₂, rfl⟩
      have h₄ := uniform_l a a.raw[n] (List.getElem_mem h₂)
      simp [h₃, h₄, h, greatestBelow?]

/-- 零高度时所有指标的展开都退化为删除末列。 -/
theorem zero_expand_l {a : ValidArray} (h : height_l a = 0) (i : Nat) :
    a.expand i = a.expand 0 := by
  apply ValidArray.ext
  simp only [ValidArray.raw_expand, BMS.expand, expandRaw, zero_parent_l h]

/-- 零高度的严格一步必减少列数。 -/
theorem zero_length_l {a b : ValidArray} (h : height_l b = 0) (h₁ : Step a b) :
    a.raw.length < b.raw.length := by
  rcases h₁.1 with ⟨i, rfl⟩
  by_cases h₂ : b.raw.length = 0
  · exfalso
    apply h₁.2
    apply ValidArray.ext
    have h₃ : b.raw = [] := List.eq_nil_of_length_eq_zero h₂
    rw [ValidArray.raw_expand, h₃]
    rfl
  · rw [zero_expand_l h, ValidArray.length_expand_zero]
    omega

/-- 零高度纤维的良基性由列数严格下降给出，无需稳定标签。 -/
theorem zero_wf_l : WellFounded (step_l 0) := by
  apply Subrelation.wf (r := (measure (fun a : fiber_l 0 => a.1.1.raw.length)).rel)
    (fun {a b} h => zero_length_l b.2 h)
  exact (measure (fun a : fiber_l 0 => a.1.1.raw.length)).wf

/-- 一行 seed 的可达性已经由零高度后继闭合，不需要反射接口。 -/
theorem seed_one_l : Acc Step (validSeed 1) := by
  apply seed_acc_l 0
  intro n h
  have h₀ : n = 0 := by omega
  subst n
  exact zero_wf_l

/-- 只剩正高度纤维的良基性义务；零高度已经由有限列数处理。 -/
theorem positive_iff_l : WellFounded GeneratedStep ↔
    ∀ n, WellFounded (step_l (n + 1)) := by
  rw [wf_iff_l]
  constructor
  · exact fun h n => h (n + 1)
  · intro h n
    cases n with
    | zero => exact zero_wf_l
    | succ n => exact h n

end YesMetaZFC.BMS.HeightDescent
