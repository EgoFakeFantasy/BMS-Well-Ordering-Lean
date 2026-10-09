import BMSConstructibleBridge.PowerlessBoundedAddition
import BMSConstructibleBridge.SecondOrderFiniteFunctionAgreement
import BMSConstructibleBridge.SecondOrderFiniteFunctionRestriction
import BMSConstructibleBridge.PowerlessBMSQuotientMultiplication

/-! # 同一个有限序列集约束乘法及其所有加法步

外层乘法历史与每步加法历史均取自 S；不假定右加算子或无限乘法图属于
检查式的母层。原商实际算子仅用于证明该 Δ₀ 检查式的精确值语义。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedMultiplication

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open PowerlessBMSQuotientArithmetic (numberEquiv_numberCode_l)
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
                (PowerlessBoundedAddition.formula_m (w ω) (w e) (w S) (.bvar (.there .here)) (w a) (.bvar .here))

theorem step_delta_l {Γ Δ : SortContext ℒ} (ω e S a n m g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (step_m ω e S a n m g) :=
  .bounded_forall n (.bounded_forall (up m) (.bounded_forall (up (up ω))
    (.bounded_forall (up (up (up ω))) (.imp (PowerlessSuccessorBounded.delta_l _ _)
      (.imp (PowerlessValueBounded.delta_l _ _ _) (.imp (PowerlessValueBounded.delta_l _ _ _)
        (PowerlessBoundedAddition.delta_l _ _ _ _ _ _)))))))

def trace_m {Γ Δ : SortContext ℒ} (ω e S a n g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj (PowerlessSuccessorBounded.formula_m (up n) (.bvar .here)) <|
    .conj (PowerlessMapBounded.formula_m (up g) (.bvar .here) (up ω)) <|
      .conj (PowerlessValueBounded.formula_m (up g) (up e) (up e))
        (step_m (up ω) (up e) (up S) (up a) (up n) (.bvar .here) (up g))

theorem trace_delta_l {Γ Δ : SortContext ℒ} (ω e S a n g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (trace_m ω e S a n g) :=
  .bounded_exists ω (.conj (PowerlessSuccessorBounded.delta_l _ _)
    (.conj (PowerlessMapBounded.delta_l _ _ _) (.conj (PowerlessValueBounded.delta_l _ _ _)
      (step_delta_l _ _ _ _ _ _ _))))

def trace_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S a n g : carrier_l 𝒩) : Prop :=
  ∃ m, member_l 𝒩 m ω ∧ PowerlessNatural.successor_l (ℳ := 𝒩) n m ∧ map_l (ℳ := 𝒩) g m ω ∧
    value_l (ℳ := 𝒩) g e e ∧ ∀ k, member_l 𝒩 k n → ∀ l, member_l 𝒩 l m →
      ∀ x, member_l 𝒩 x ω → ∀ y, member_l 𝒩 y ω → PowerlessNatural.successor_l (ℳ := 𝒩) k l →
        value_l (ℳ := 𝒩) g k x → value_l (ℳ := 𝒩) g l y →
          PowerlessBoundedAddition.holds_l (𝒩 := 𝒩) ω e S x a y

theorem trace_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S a n g : Term ℒ Γ Δ .set) : (trace_m ω e S a n g).satisfies η ↔
      trace_l (ω.eval η) (e.eval η) (S.eval η) (a.eval η) (n.eval η) (g.eval η) := by
  simp only [trace_m, step_m, trace_l, Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies, PowerlessSuccessorBounded.formula_l,
    PowerlessMapBounded.formula_l, PowerlessValueBounded.formula_l, PowerlessBoundedAddition.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def formula_m {Γ Δ : SortContext ℒ} (ω e S a b c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists S <| .conj (trace_m (up ω) (up e) (up S) (up a) (up b) (.bvar .here))
    (PowerlessValueBounded.formula_m (.bvar .here) (up b) (up c))

theorem delta_l {Γ Δ : SortContext ℒ} (ω e S a b c : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e S a b c) :=
  .bounded_exists S (.conj (trace_delta_l _ _ _ _ _ _) (PowerlessValueBounded.delta_l _ _ _))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S a b c : carrier_l 𝒩) : Prop :=
  ∃ g, member_l 𝒩 g S ∧ trace_l (𝒩 := 𝒩) ω e S a b g ∧ value_l (ℳ := 𝒩) g b c

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S a b c : Term ℒ Γ Δ .set) : (formula_m ω e S a b c).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (S.eval η) (a.eval η) (b.eval η) (c.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, trace_formula_l, PowerlessValueBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem trace_equiv_l (K : source_coding_l hℳ) {S H n g : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    (i : SecondOrderModel.num_l ℳ)
    (hH : PowerlessMultiplication.operator_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val (numberCode_l K i).val H) :
    trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S (numberCode_l K i).val n g ↔
        PowerlessFunctionTraceBounded.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
          (numberCode_l K (SecondOrderModel.zero_l ℳ)).val K.omega H
          (numberCode_l K (SecondOrderModel.zero_l ℳ)).val n g := by
  have hRead (x y : type_l hℳ) (hx : member_l (SecondOrderQuotient.structure_l hℳ) x K.omega) :
      PowerlessBoundedAddition.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
        (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S x (numberCode_l K i).val y ↔
          value_l (ℳ := SecondOrderQuotient.structure_l hℳ) H x y := by
    obtain ⟨r, hr⟩ := numberCode_surjective_l K ⟨x, hx⟩
    have hr' : x = (numberCode_l K r).val := (congrArg Subtype.val hr).symm
    rw [hr']
    have hOp : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) H (numberCode_l K r).val y ↔
        PowerlessAddition.addition_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega
          (numberCode_l K (SecondOrderModel.zero_l ℳ)).val (numberCode_l K r).val (numberCode_l K i).val y :=
      ⟨fun h => ((hH.2 _ _).mp h).2, fun h => (hH.2 _ _).mpr ⟨(numberCode_l K r).property, h⟩⟩
    exact (PowerlessBoundedAddition.instance_l K hS r i y).trans
      ((PowerlessBMSQuotientRecursion.addition_iff_l K r i y).symm.trans hOp.symm)
  constructor
  · rintro ⟨m, hmω, hnm, hMap, h₀, hStep⟩
    exact ⟨m, hmω, hnm, hMap, h₀, fun k hk l hl x hx y hy hkl hnx hmy =>
      (hRead x y hx).mp (hStep k hk l hl x hx y hy hkl hnx hmy)⟩
  · rintro ⟨m, hmω, hnm, hMap, h₀, hStep⟩
    exact ⟨m, hmω, hnm, hMap, h₀, fun k hk l hl x hx y hy hkl hnx hmy =>
      (hRead x y hx).mpr (hStep k hk l hl x hx y hy hkl hnx hmy)⟩

theorem instance_l (K : source_coding_l hℳ) {S : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    (i j : SecondOrderModel.num_l ℳ) (c : type_l hℳ) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S (numberCode_l K i).val (numberCode_l K j).val c ↔
        c = (numberCode_l K (SecondOrderModel.mul_l i j)).val := by
  obtain ⟨H, hH⟩ := PowerlessBMSQuotientMultiplication.operator_exists_l K i
  obtain ⟨F, hMap, hGraph⟩ := PowerlessBMSQuotientArithmetic.multiplicationMapGraph_l K i
  have hF := PowerlessBMSQuotientMultiplication.iteration_l K i H F hH hMap hGraph
  constructor
  · rintro ⟨g, _, hg, hc⟩
    have hg' := (trace_equiv_l K hS i hH).mp hg
    have hValue := SecondOrderFiniteFunctionAgreement.value_l K (n := (numberCode_l K j).val)
      (g := g) (c := c) hH.1 hF
      (numberCode_l K j).property hg' hc
    exact (PowerlessBMSQuotientMultiplication.multiplication_iff_l K i j c).mp ⟨H, F, hH, hF, hValue⟩
  · rintro rfl
    obtain ⟨g, hg, hRead⟩ := SecondOrderFiniteFunctionRestriction.trace_exists_l K hF j
    have hgS : member_l (SecondOrderQuotient.structure_l hℳ) g S := by
      obtain ⟨m, hmω, _, hgMap, _, _⟩ := hg
      exact (hS g).mpr ⟨m, hmω, hgMap⟩
    have hEndpoint : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F (numberCode_l K j).val
        (numberCode_l K (SecondOrderModel.mul_l i j)).val := by
      apply (hGraph (numberCode_l K j) (numberCode_l K (SecondOrderModel.mul_l i j))).mpr
      simp only [numberEquiv_numberCode_l]
    refine ⟨g, hgS, (trace_equiv_l K hS i hH).mpr hg, (hRead _ _).mpr ⟨?_, hEndpoint⟩⟩
    exact (PowerlessBMSQuotientSuccessor.successor_l K j (numberCode_l K j).val).mpr (Or.inr rfl)

#print axioms delta_l
#print axioms instance_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedMultiplication
