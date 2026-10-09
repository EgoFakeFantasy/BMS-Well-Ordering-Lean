import BMSConstructibleBridge.PowerlessValueBounded

/-! # 集合映射规格的纯 Δ₀ 表达

有序对坐标限制到给定定义域、陪域，唯一性也只比较陪域成员。
与原映射规格对任意纯结构等价，不预设分离、收集或函数存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMapBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (f A D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ := .conj
  (membershipLevyBound.boundedForall f <|
    membershipLevyBound.boundedExists (up A) <|
      membershipLevyBound.boundedExists (up (up D)) <|
        PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here))))
  (membershipLevyBound.boundedForall A <|
    membershipLevyBound.boundedExists (up D) <| .conj
      (PowerlessValueBounded.formula_m (up (up f)) (.bvar (.there .here)) (.bvar .here))
      (membershipLevyBound.boundedForall (up (up D)) <| .imp
        (PowerlessValueBounded.formula_m (up (up (up f))) (.bvar (.there (.there .here))) (.bvar .here))
        (.equal (.bvar .here) (.bvar (.there .here)))))

theorem delta_l {Γ Δ : SortContext ℒ} (f A D : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m f A D) :=
  .conj (.bounded_forall f (.bounded_exists (up A) (.bounded_exists (up (up D))
    (PowerlessPairBounded.ordered_delta_l _ _ _))))
    (.bounded_forall A (.bounded_exists (up D) (.conj (PowerlessValueBounded.delta_l _ _ _)
      (.bounded_forall (up (up D)) (.imp (PowerlessValueBounded.delta_l _ _ _) (.equal _ _))))))

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (f A D : Term ℒ Γ Δ .set) :
    (formula_m f A D).satisfies η ↔ map_l (f.eval η) (A.eval η) (D.eval η) := by
  have h : (formula_m f A D).satisfies η ↔
      (∀ p, member_l 𝒩 p (f.eval η) → ∃ x, member_l 𝒩 x (A.eval η) ∧
        ∃ y, member_l 𝒩 y (D.eval η) ∧ ordered_l (ℳ := 𝒩) x y p) ∧
      (∀ x, member_l 𝒩 x (A.eval η) → ∃ y, member_l 𝒩 y (D.eval η) ∧
        value_l (ℳ := 𝒩) (f.eval η) x y ∧ ∀ z, member_l 𝒩 z (D.eval η) →
          value_l (ℳ := 𝒩) (f.eval η) x z → z = y) := by
    simp only [formula_m, Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
      Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
      PowerlessPairBounded.ordered_formula_l, PowerlessValueBounded.formula_l,
      Arguments.eval, up, Term.eval_weakenBound, Term.eval]
    rfl
  rw [h]
  constructor
  · rintro ⟨hPairs, hValues⟩
    constructor
    · intro p hp
      obtain ⟨x, hx, y, hy, hxy⟩ := hPairs p hp
      exact ⟨x, y, hx, hy, hxy⟩
    · intro x hx
      obtain ⟨y, hy, hxy, hUnique⟩ := hValues x hx
      exact ⟨y, ⟨hy, hxy⟩, fun z hz => hUnique z hz.1 hz.2⟩
  · rintro ⟨hPairs, hValues⟩
    constructor
    · intro p hp
      obtain ⟨x, y, hx, hy, hxy⟩ := hPairs p hp
      exact ⟨x, hx, y, hy, hxy⟩
    · intro x hx
      obtain ⟨y, hy, hUnique⟩ := hValues x hx
      exact ⟨y, hy.1, hy.2, fun z hz hxy => hUnique z ⟨hz, hxy⟩⟩

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMapBounded
