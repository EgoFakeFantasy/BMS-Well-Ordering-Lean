import BMSConstructibleBridge.PowerlessMapBounded
import BMSConstructibleBridge.PowerlessSuccessorBounded
import BMSConstructibleBridge.PowerlessAdditionFiniteSyntax

/-! # 有限加法轨迹的 Δ₀ 检查式

长度后继限制到 ω，递推行限制到定义域及自然数值域。
与无界轨迹的等价明确要求自然数后继界和映射坐标界，不能凭语法删去量词。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionTraceBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def step_m {Γ Δ : SortContext ℒ} (ω n m g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
  membershipLevyBound.boundedForall n <|
    membershipLevyBound.boundedForall (up m) <|
      membershipLevyBound.boundedForall (up (up ω)) <|
        membershipLevyBound.boundedForall (up (up (up ω))) <|
          .imp (PowerlessSuccessorBounded.formula_m (.bvar (.there (.there (.there .here))))
            (.bvar (.there (.there .here)))) <|
            .imp (PowerlessValueBounded.formula_m (w g) (.bvar (.there (.there (.there .here)))) (.bvar (.there .here))) <|
              .imp (PowerlessValueBounded.formula_m (w g) (.bvar (.there (.there .here))) (.bvar .here))
                (PowerlessSuccessorBounded.formula_m (.bvar (.there .here)) (.bvar .here))

theorem step_delta_l {Γ Δ : SortContext ℒ} (ω n m g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (step_m ω n m g) :=
  .bounded_forall n (.bounded_forall (up m) (.bounded_forall (up (up ω))
    (.bounded_forall (up (up (up ω))) (.imp (PowerlessSuccessorBounded.delta_l _ _)
      (.imp (PowerlessValueBounded.delta_l _ _ _) (.imp (PowerlessValueBounded.delta_l _ _ _)
        (PowerlessSuccessorBounded.delta_l _ _)))))))

def formula_m {Γ Δ : SortContext ℒ} (ω e a n g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj (PowerlessSuccessorBounded.formula_m (up n) (.bvar .here)) <|
    .conj (PowerlessMapBounded.formula_m (up g) (.bvar .here) (up ω)) <|
      .conj (PowerlessValueBounded.formula_m (up g) (up e) (up a))
        (step_m (up ω) (up n) (.bvar .here) (up g))

theorem delta_l {Γ Δ : SortContext ℒ} (ω e a n g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e a n g) :=
  .bounded_exists ω (.conj (PowerlessSuccessorBounded.delta_l _ _)
    (.conj (PowerlessMapBounded.delta_l _ _ _) (.conj (PowerlessValueBounded.delta_l _ _ _)
      (step_delta_l _ _ _ _))))

def trace_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e a n g : 𝒩.Carrier .set) : Prop :=
  ∃ m, member_l 𝒩 m ω ∧ PowerlessNatural.successor_l (ℳ := 𝒩) n m ∧ map_l (ℳ := 𝒩) g m ω ∧
    value_l (ℳ := 𝒩) g e a ∧ ∀ k, member_l 𝒩 k n → ∀ l, member_l 𝒩 l m →
      ∀ x, member_l 𝒩 x ω → ∀ y, member_l 𝒩 y ω → PowerlessNatural.successor_l (ℳ := 𝒩) k l →
        value_l (ℳ := 𝒩) g k x → value_l (ℳ := 𝒩) g l y → PowerlessNatural.successor_l (ℳ := 𝒩) x y

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e a n g : Term ℒ Γ Δ .set) :
    (formula_m ω e a n g).satisfies η ↔ trace_l (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (g.eval η) := by
  simp only [formula_m, step_m, trace_l, Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessSuccessorBounded.formula_l, PowerlessMapBounded.formula_l, PowerlessValueBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem equiv_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {ω e a n g : 𝒩.Carrier .set}
    (hSucc : ∀ m, PowerlessNatural.successor_l (ℳ := 𝒩) n m → member_l 𝒩 m ω)
    (hBound : ∀ m, PowerlessNatural.successor_l (ℳ := 𝒩) n m → ∀ k l, member_l 𝒩 k n →
      PowerlessNatural.successor_l (ℳ := 𝒩) k l → member_l 𝒩 l m)
    (hValue : ∀ m, map_l (ℳ := 𝒩) g m ω → ∀ x y, value_l (ℳ := 𝒩) g x y →
      member_l 𝒩 x m ∧ member_l 𝒩 y ω) :
    trace_l (𝒩 := 𝒩) ω e a n g ↔ PowerlessAdditionFinite.trace_l (ℳ := 𝒩) ω e a n g := by
  constructor
  · rintro ⟨m, _, hm, hg, h₀, hStep⟩
    exact ⟨m, hm, hg, h₀, fun k l x y hk hl hx hy =>
      hStep k hk l (hBound m hm k l hk hl) x (hValue m hg k x hx).2
        y (hValue m hg l y hy).2 hl hx hy⟩
  · rintro ⟨m, hm, hg, h₀, hStep⟩
    exact ⟨m, hSucc m hm, hm, hg, h₀, fun k hk l _ x _ y _ hl hx hy => hStep k l x y hk hl hx hy⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionTraceBounded
