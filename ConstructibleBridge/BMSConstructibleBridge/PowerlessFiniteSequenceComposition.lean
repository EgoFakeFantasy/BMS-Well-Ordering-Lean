import BMSConstructibleBridge.PowerlessMapBounded

/-! # 有限序列复合的纯 Δ₀ 检查关系

有限定义域、数值中间域和值域都显式界定。原始求值关系不借用 Type
函数；检查式本身不要求完整集合论背景。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteSequenceComposition

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def compare_m {Γ Δ : SortContext ℒ} (ω X G g f n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  membershipLevyBound.boundedForall n <| membershipLevyBound.boundedForall (up X) <| .iff
    (PowerlessValueBounded.formula_m (w f) (.bvar (.there .here)) (.bvar .here))
    (membershipLevyBound.boundedExists (w ω) <| .conj
      (PowerlessValueBounded.formula_m (up (w g)) (.bvar (.there (.there .here))) (.bvar .here))
      (PowerlessValueBounded.formula_m (up (w G)) (.bvar .here) (.bvar (.there .here))))

theorem compare_delta_l {Γ Δ : SortContext ℒ} (ω X G g f n : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (compare_m ω X G g f n) :=
  .bounded_forall n (.bounded_forall (up X) (.iff (PowerlessValueBounded.delta_l _ _ _)
    (.bounded_exists (up (up ω)) (.conj (PowerlessValueBounded.delta_l _ _ _)
      (PowerlessValueBounded.delta_l _ _ _)))))

def compare_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω X G g f n : carrier_l 𝒩) : Prop :=
  ∀ k, member_l 𝒩 k n → ∀ y, member_l 𝒩 y X →
    (value_l (ℳ := 𝒩) f k y ↔ ∃ j, member_l 𝒩 j ω ∧
      value_l (ℳ := 𝒩) g k j ∧ value_l (ℳ := 𝒩) G j y)

theorem compare_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω X G g f n : Term ℒ Γ Δ .set) : (compare_m ω X G g f n).satisfies η ↔
      compare_l (ω.eval η) (X.eval η) (G.eval η) (g.eval η) (f.eval η) (n.eval η) := by
  simp only [compare_m, compare_l, Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def formula_m {Γ Δ : SortContext ℒ} (ω X G g f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj
    (PowerlessMapBounded.formula_m (up g) (.bvar .here) (up ω)) <| .conj
      (PowerlessMapBounded.formula_m (up f) (.bvar .here) (up X))
      (compare_m (up ω) (up X) (up G) (up g) (up f) (.bvar .here))

theorem delta_l {Γ Δ : SortContext ℒ} (ω X G g f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω X G g f) :=
  .bounded_exists ω (.conj (PowerlessMapBounded.delta_l _ _ _)
    (.conj (PowerlessMapBounded.delta_l _ _ _) (compare_delta_l _ _ _ _ _ _)))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω X G g f : carrier_l 𝒩) : Prop :=
  ∃ n, member_l 𝒩 n ω ∧ map_l (ℳ := 𝒩) g n ω ∧ map_l (ℳ := 𝒩) f n X ∧
    compare_l (𝒩 := 𝒩) ω X G g f n

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω X G g f : Term ℒ Γ Δ .set) : (formula_m ω X G g f).satisfies η ↔
      holds_l (ω.eval η) (X.eval η) (G.eval η) (g.eval η) (f.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessMapBounded.formula_l,
    compare_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms delta_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteSequenceComposition
