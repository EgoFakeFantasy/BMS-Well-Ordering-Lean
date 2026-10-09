import BMSConstructibleBridge.PowerlessMapBounded
import BMSConstructibleBridge.PowerlessSuccessorBounded

/-! # 给定集合自映射的内部有限轨迹 Δ₀ 检查式

长度后继由 ω 界定，图值由给定陪域界定。该检查式不要求整条无限轨迹
属于相对类，供共同有限图界与后续 Def 切片使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunctionTraceBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def step_m {Γ Δ : SortContext ℒ} (A H n m g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
  membershipLevyBound.boundedForall n <|
    membershipLevyBound.boundedForall (up m) <|
      membershipLevyBound.boundedForall (up (up A)) <|
        membershipLevyBound.boundedForall (up (up (up A))) <|
          .imp (PowerlessSuccessorBounded.formula_m (.bvar (.there (.there (.there .here))))
            (.bvar (.there (.there .here)))) <|
            .imp (PowerlessValueBounded.formula_m (w g) (.bvar (.there (.there (.there .here)))) (.bvar (.there .here))) <|
              .imp (PowerlessValueBounded.formula_m (w g) (.bvar (.there (.there .here))) (.bvar .here))
                (PowerlessValueBounded.formula_m (w H) (.bvar (.there .here)) (.bvar .here))

theorem step_delta_l {Γ Δ : SortContext ℒ} (A H n m g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (step_m A H n m g) :=
  .bounded_forall n (.bounded_forall (up m) (.bounded_forall (up (up A))
    (.bounded_forall (up (up (up A))) (.imp (PowerlessSuccessorBounded.delta_l _ _)
      (.imp (PowerlessValueBounded.delta_l _ _ _) (.imp (PowerlessValueBounded.delta_l _ _ _)
        (PowerlessValueBounded.delta_l _ _ _)))))))

def formula_m {Γ Δ : SortContext ℒ} (ω e A H a n g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj (PowerlessSuccessorBounded.formula_m (up n) (.bvar .here)) <|
    .conj (PowerlessMapBounded.formula_m (up g) (.bvar .here) (up A)) <|
      .conj (PowerlessValueBounded.formula_m (up g) (up e) (up a))
        (step_m (up A) (up H) (up n) (.bvar .here) (up g))

theorem delta_l {Γ Δ : SortContext ℒ} (ω e A H a n g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e A H a n g) :=
  .bounded_exists ω (.conj (PowerlessSuccessorBounded.delta_l _ _)
    (.conj (PowerlessMapBounded.delta_l _ _ _) (.conj (PowerlessValueBounded.delta_l _ _ _)
      (step_delta_l _ _ _ _ _))))

def trace_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e A H a n g : 𝒩.Carrier .set) : Prop :=
  ∃ m, member_l 𝒩 m ω ∧ PowerlessNatural.successor_l (ℳ := 𝒩) n m ∧ map_l (ℳ := 𝒩) g m A ∧
    value_l (ℳ := 𝒩) g e a ∧ ∀ k, member_l 𝒩 k n → ∀ l, member_l 𝒩 l m →
      ∀ x, member_l 𝒩 x A → ∀ y, member_l 𝒩 y A → PowerlessNatural.successor_l (ℳ := 𝒩) k l →
        value_l (ℳ := 𝒩) g k x → value_l (ℳ := 𝒩) g l y → value_l (ℳ := 𝒩) H x y

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e A H a n g : Term ℒ Γ Δ .set) :
    (formula_m ω e A H a n g).satisfies η ↔
      trace_l (ω.eval η) (e.eval η) (A.eval η) (H.eval η) (a.eval η) (n.eval η) (g.eval η) := by
  simp only [formula_m, step_m, trace_l, Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessSuccessorBounded.formula_l, PowerlessMapBounded.formula_l, PowerlessValueBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms delta_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunctionTraceBounded
