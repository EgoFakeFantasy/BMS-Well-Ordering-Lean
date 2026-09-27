import BMSConstructibleBridge.PowerlessRelabel

/-!
# 按实际重标号矩阵选择外部层号

先固定具名层总数 H。第 k 级的预算包含 H 个具名边记录及此前各级的顶端迹，
不读取具名边的实际外部层号，故不循环依赖尚未构造的高层号。
层号严格增长并支配实际矩阵预算；不作线性复杂度假设。
递归完成后才选统一支持码，所有级别的最小边界共用这个好标签类。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelLevels

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

/-- 低级层号按逆序存放；顺序不参与预算外的数学条件。 -/
def levels_m (H : Nat) : Nat → List Nat
  | 0 => List.nil
  | k + 1 =>
    let Λ := levels_m H k
    max (Λ.foldr max 0 + 1) (PowerlessRelabelTemplate.budget_m H Λ) :: Λ

def level_m (H k : Nat) : Nat :=
  max ((levels_m H k).foldr max 0 + 1) (PowerlessRelabelTemplate.budget_m H (levels_m H k))

theorem succ_m (H k : Nat) : levels_m H (k + 1) = level_m H k :: levels_m H k := rfl

theorem length_m (H k : Nat) : (levels_m H k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [succ_m, List.length_cons, ih]

private theorem le_fold_l {Λ : List Nat} {j : Nat} (h : j ∈ Λ) : j ≤ Λ.foldr max 0 := by
  induction Λ with
  | nil => exact (List.not_mem_nil h).elim
  | cons k Λ ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact (ih h).trans (Nat.le_max_right _ _)

theorem bound_m (H k : Nat) {j : Nat} (h : j ∈ levels_m H k) : j < level_m H k :=
  (le_fold_l h).trans_lt ((Nat.lt_succ_self _).trans_le (Nat.le_max_left _ _))

theorem mem_m (H : Nat) {j k : Nat} (h : j < k) : level_m H j ∈ levels_m H k := by
  induction k with
  | zero => exact (Nat.not_lt_zero j h).elim
  | succ k ih =>
    rw [succ_m]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h | rfl
    · exact List.mem_cons_of_mem _ (ih h)
    · exact List.mem_cons_self

theorem lt_m (H : Nat) {j k : Nat} (h : j < k) : level_m H j < level_m H k :=
  bound_m H k (mem_m H h)

theorem mono_m (H : Nat) {j k : Nat} (h : j ≤ k) : level_m H j ≤ level_m H k := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact (lt_m H h).le
  · exact Nat.le_refl _

theorem budget_m (H k : Nat) :
    PowerlessRelabelTemplate.budget_m H (levels_m H k) ≤ level_m H k :=
  Nat.le_max_right _ _

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 数码列表实际存在，保持与外部层号逐项对应，不选择模型内部无限序列。 -/
theorem numerals_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (e : carrier_l ℳ) (H k : Nat) :
    ∃ Λ : List (Nat × carrier_l ℳ), Λ.map Prod.fst = levels_m H k ∧
      ∀ t ∈ Λ, PowerlessNumeral.numeral_l e t.1 t.2 := by
  induction k with
  | zero => exact ⟨List.nil, rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | succ k ih =>
    obtain ⟨Λ, hΛ, h⟩ := ih
    obtain ⟨n, hn⟩ := PowerlessNumeral.exists_l hℳ e (level_m H k)
    refine ⟨(level_m H k, n) :: Λ, ?_, ?_⟩
    · simp only [List.map_cons, succ_m, hΛ]
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hn
      · exact h t ht

/-- 固定外部高度后一次选支持码，再为每个实际重编号层分别取得最小边界。 -/
theorem boundaries_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T) (H : Nat) :
    ∃ c N, member_l ℳ c ω ∧ member_l ℳ N ω ∧
      PowerlessGoodBoundary.code_l ω e T t₁ t₂ t₃ c N (level_m H H) ∧
      ∀ k ≤ H, ∃ n σ, PowerlessNumeral.numeral_l e (level_m H k) n ∧
        PowerlessGoodBoundary.boundary_l ω e T t₁ t₂ t₃ c N n σ := by
  obtain ⟨c, N, hc, hN, h, hσ⟩ := PowerlessGoodBoundary.exists_l hℳ hω ht hT (level_m H H)
  exact ⟨c, N, hc, hN, h, fun k hk => hσ (level_m H k) (mono_m H hk)⟩

/-- 统一好标签类的第 k 级边界以下，稳定边对应的原行号严格小于 k。 -/
theorem cutoff_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N n m σ α β : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    {H j k : Nat} (hn : PowerlessNumeral.numeral_l e (level_m H k) n)
    (hm : PowerlessNumeral.numeral_l e (level_m H j) m)
    (hσ : PowerlessGoodBoundary.boundary_l ω e T t₁ t₂ t₃ c N n σ)
    (hα : member_l ℳ α σ)
    (h : PowerlessGoodBoundary.stable_l ω e T t₁ t₂ t₃ c N m α β) : j < k := by
  by_contra h₀
  have h₁ := PowerlessSourceStandardBudget.numeral_le_subset_l hℳ e
    (mono_m H (Nat.le_of_not_gt h₀)) hn hm
  exact hσ.2 α hα ⟨β, PowerlessGoodBoundary.monotone_l hℳ hω he hT
    (PowerlessNumeral.natural_l hℳ hω he hn) h₁ h⟩

/-- 实际构造全高度具名边列表、低行顶端迹列表及共同重标号图。
预算条件由重编号本身保证；内部列数仍可以非标准。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c N n α β A B S R F G p q f g : carrier_l ℳ}
    (hω : omega_l ω) (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F)
    (hB : PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ β B R G)
    {k H : Nat} (hk : k ≤ H)
    (hc : PowerlessGoodBoundary.code_l ω e T t₁ t₂ t₃ c N (level_m H H))
    (hc₀ : member_l ℳ c ω) (hN : member_l ℳ N ω)
    (hn : PowerlessNumeral.numeral_l e (level_m H k) n)
    (hs : PowerlessGoodBoundary.stable_l ω e T t₁ t₂ t₃ c N n α β)
    (hp : member_l ℳ p ω) (hq : member_l ℳ q ω)
    (hf : map_l f p A) (hg : map_l g q B)
    (hG : ∀ i a, value_l g i a → PowerlessCodedDiagram.good_l ω e T t₁ t₂ t₃ c N a)
    (hfg : ∀ i j a b, value_l f i a → value_l g j b → member_l ℳ a b) :
    ∃ Λ Θ h, Λ.map Prod.fst = levels_m H H ∧ Θ.map Prod.fst = levels_m H k ∧
      (∀ t ∈ Λ, PowerlessNumeral.numeral_l e t.1 t.2) ∧
      (∀ t ∈ Θ, PowerlessNumeral.numeral_l e t.1 t.2) ∧ map_l h q A ∧
      PowerlessRelabelPreservation.image_l ω e T t₁ t₂ t₃ c N α β f g h Λ Θ := by
  obtain ⟨Λ, hΛ, hΛ₀⟩ := numerals_l hℳ e H H
  obtain ⟨Θ, hΘ, hΘ₀⟩ := numerals_l hℳ e H k
  have h₀ : ∀ t ∈ Θ, t.1 ≤ level_m H k ∧ PowerlessNumeral.numeral_l e t.1 t.2 := by
    intro t ht
    have h : t.1 ∈ levels_m H k := hΘ ▸ List.mem_map.mpr ⟨t, ht, rfl⟩
    exact ⟨(bound_m H k h).le, hΘ₀ t ht⟩
  obtain ⟨h, hh, h₁⟩ := PowerlessRelabel.exists_l hℳ hω ht hT hA hB hc hc₀ hN
    (mono_m H hk) hn hs hp hq hf hg hG hfg Λ hΛ₀ Θ h₀ (by
      have h : Λ.length = H := by
        simpa only [List.length_map, length_m] using congrArg List.length hΛ
      rw [h, hΘ]
      exact budget_m H k)
  exact ⟨Λ, Θ, h, hΛ, hΘ, hΛ₀, hΘ₀, hh, h₁⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelLevels
