import BMSConstructibleBridge.PowerlessBoundedMultiplication
import BMSConstructibleBridge.SecondOrderQuotientPowerIteration

/-! # 同一个有限序列集约束幂历史及全部乘加子历史

纯 Δ₀ 检查式没有幂实数参数。任意实际原幂实数仅在正确性证明中出现，
其图与检查式在所有内部指数、任意候选商输出上精确对应。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedExponentiation

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def step_m {Γ Δ : SortContext ℒ} (ω e S a n m g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
  membershipLevyBound.boundedForall n <|
    membershipLevyBound.boundedForall (up m) <|
      membershipLevyBound.boundedForall (up (up ω)) <|
        membershipLevyBound.boundedForall (up (up (up ω))) <|
          .imp (PowerlessSuccessorBounded.formula_m (.bvar (.there (.there (.there .here))))
            (.bvar (.there (.there .here)))) <|
            .imp (PowerlessValueBounded.formula_m (w g) (.bvar (.there (.there (.there .here)))) (.bvar (.there .here))) <|
              .imp (PowerlessValueBounded.formula_m (w g) (.bvar (.there (.there .here))) (.bvar .here))
                (PowerlessBoundedMultiplication.formula_m (w ω) (w e) (w S) (.bvar (.there .here)) (w a) (.bvar .here))

theorem step_delta_l {Γ Δ : SortContext ℒ} (ω e S a n m g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (step_m ω e S a n m g) :=
  .bounded_forall n (.bounded_forall (up m) (.bounded_forall (up (up ω))
    (.bounded_forall (up (up (up ω))) (.imp (PowerlessSuccessorBounded.delta_l _ _)
      (.imp (PowerlessValueBounded.delta_l _ _ _) (.imp (PowerlessValueBounded.delta_l _ _ _)
        (PowerlessBoundedMultiplication.delta_l _ _ _ _ _ _)))))))

def trace_m {Γ Δ : SortContext ℒ} (ω e S one a n g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj (PowerlessSuccessorBounded.formula_m (up n) (.bvar .here)) <|
    .conj (PowerlessMapBounded.formula_m (up g) (.bvar .here) (up ω)) <|
      .conj (PowerlessValueBounded.formula_m (up g) (up e) (up one))
        (step_m (up ω) (up e) (up S) (up a) (up n) (.bvar .here) (up g))

theorem trace_delta_l {Γ Δ : SortContext ℒ} (ω e S one a n g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (trace_m ω e S one a n g) :=
  .bounded_exists ω (.conj (PowerlessSuccessorBounded.delta_l _ _)
    (.conj (PowerlessMapBounded.delta_l _ _ _) (.conj (PowerlessValueBounded.delta_l _ _ _)
      (step_delta_l _ _ _ _ _ _ _))))

def trace_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S one a n g : carrier_l 𝒩) : Prop :=
  ∃ m, member_l 𝒩 m ω ∧ PowerlessNatural.successor_l (ℳ := 𝒩) n m ∧ map_l (ℳ := 𝒩) g m ω ∧
    value_l (ℳ := 𝒩) g e one ∧ ∀ k, member_l 𝒩 k n → ∀ l, member_l 𝒩 l m →
      ∀ x, member_l 𝒩 x ω → ∀ y, member_l 𝒩 y ω → PowerlessNatural.successor_l (ℳ := 𝒩) k l →
        value_l (ℳ := 𝒩) g k x → value_l (ℳ := 𝒩) g l y →
          PowerlessBoundedMultiplication.holds_l (𝒩 := 𝒩) ω e S x a y

theorem trace_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S one a n g : Term ℒ Γ Δ .set) : (trace_m ω e S one a n g).satisfies η ↔
      trace_l (ω.eval η) (e.eval η) (S.eval η) (one.eval η) (a.eval η) (n.eval η) (g.eval η) := by
  simp only [trace_m, step_m, trace_l, Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies, PowerlessSuccessorBounded.formula_l,
    PowerlessMapBounded.formula_l, PowerlessValueBounded.formula_l, PowerlessBoundedMultiplication.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def formula_m {Γ Δ : SortContext ℒ} (ω e S one a b c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists S <| .conj
    (trace_m (up ω) (up e) (up S) (up one) (up a) (up b) (.bvar .here))
    (PowerlessValueBounded.formula_m (.bvar .here) (up b) (up c))

theorem delta_l {Γ Δ : SortContext ℒ} (ω e S one a b c : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e S one a b c) :=
  .bounded_exists S (.conj (trace_delta_l _ _ _ _ _ _ _) (PowerlessValueBounded.delta_l _ _ _))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S one a b c : carrier_l 𝒩) : Prop :=
  ∃ g, member_l 𝒩 g S ∧ trace_l (𝒩 := 𝒩) ω e S one a b g ∧ value_l (ℳ := 𝒩) g b c

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S one a b c : Term ℒ Γ Δ .set) : (formula_m ω e S one a b c).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (S.eval η) (one.eval η) (a.eval η) (b.eval η) (c.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, trace_formula_l, PowerlessValueBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem trace_equiv_l (K : source_coding_l hℳ) {S H n g : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    (i : SecondOrderModel.num_l ℳ)
    (hHPoint : ∀ r : SecondOrderModel.num_l ℳ, ∀ y : type_l hℳ,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) H (numberCode_l K r).val y ↔
        y = (numberCode_l K (SecondOrderModel.mul_l i r)).val) :
    trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S
      (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val (numberCode_l K i).val n g ↔
        PowerlessFunctionTraceBounded.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
          (numberCode_l K (SecondOrderModel.zero_l ℳ)).val K.omega H
          (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val n g := by
  have hRead (x y : type_l hℳ) (hx : member_l (SecondOrderQuotient.structure_l hℳ) x K.omega) :
      PowerlessBoundedMultiplication.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
        (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S x (numberCode_l K i).val y ↔
          value_l (ℳ := SecondOrderQuotient.structure_l hℳ) H x y := by
    obtain ⟨r, hr⟩ := numberCode_surjective_l K ⟨x, hx⟩
    have hr' : x = (numberCode_l K r).val := (congrArg Subtype.val hr).symm
    rw [hr']
    exact (PowerlessBoundedMultiplication.instance_l K hS r i y).trans
      ((Iff.of_eq (congrArg (fun z => y = (numberCode_l K z).val)
        (SecondOrderMultiplication.mul_comm_l hℳ r i))).trans (hHPoint r y).symm)
  constructor
  · rintro ⟨m, hmω, hnm, hMap, h₀, hStep⟩
    exact ⟨m, hmω, hnm, hMap, h₀, fun k hk l hl x hx y hy hkl hnx hmy =>
      (hRead x y hx).mp (hStep k hk l hl x hx y hy hkl hnx hmy)⟩
  · rintro ⟨m, hmω, hnm, hMap, h₀, hStep⟩
    exact ⟨m, hmω, hnm, hMap, h₀, fun k hk l hl x hx y hy hkl hnx hmy =>
      (hRead x y hx).mpr (hStep k hk l hl x hx y hy hkl hnx hmy)⟩

theorem instance_l (K : source_coding_l hℳ) {S : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    {E : SecondOrderModel.set_l ℳ} {i : SecondOrderModel.num_l ℳ}
    (hE : SecondOrderPowers.spec_l i E) (n : SecondOrderModel.num_l ℳ) (c : type_l hℳ) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S
      (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val
      (numberCode_l K i).val (numberCode_l K n).val c ↔
        ∃ j : SecondOrderModel.num_l ℳ, SecondOrderPairing.relation_l E n j ∧ c = (numberCode_l K j).val := by
  obtain ⟨H, hH, hHPoint⟩ := SecondOrderQuotientPowerIteration.multiplier_exists_l K i
  obtain ⟨F, hF, hRead⟩ := SecondOrderQuotientPowerIteration.exists_l K hE hHPoint
  constructor
  · rintro ⟨g, _, hg, hc⟩
    have hg' := (trace_equiv_l K hS i hHPoint).mp hg
    have hValue := SecondOrderFiniteFunctionAgreement.value_l K (n := (numberCode_l K n).val)
      (g := g) (c := c) hH hF (numberCode_l K n).property hg' hc
    exact (hRead n c).mp hValue
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨g, hg, hGraph⟩ := SecondOrderFiniteFunctionRestriction.trace_exists_l K hF n
    have hgS : member_l (SecondOrderQuotient.structure_l hℳ) g S := by
      obtain ⟨m, hmω, _, hgMap, _, _⟩ := hg
      exact (hS g).mpr ⟨m, hmω, hgMap⟩
    refine ⟨g, hgS, (trace_equiv_l K hS i hHPoint).mpr hg,
      (hGraph _ _).mpr ⟨?_, (hRead n _).mpr ⟨j, hj, rfl⟩⟩⟩
    exact (PowerlessBMSQuotientSuccessor.successor_l K n (numberCode_l K n).val).mpr (Or.inr rfl)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedExponentiation
