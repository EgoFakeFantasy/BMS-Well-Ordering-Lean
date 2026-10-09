import BMSConstructibleBridge.PowerlessLegacyAssignmentBounded
import BMSConstructibleBridge.PowerlessLegacyNumericReading
import BMSConstructibleBridge.SecondOrderLegalFormulaIndex

/-! # 原 Def 合法索引的纯 Δ₀ 检查式

指标仍是原平方配数 p,(l,c)，不是新四标签公式码。参数有效性保留
界外无边，公式合法性检查原 V(p,succ l)。全部见证限于内部 ω；
幂图和合法图以显式数字规格输入，不预设原实数属于 Class。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyLegalIndexBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l)
open SecondOrderModel (num_l set_l zero_l succ_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (ω e N P G i : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <|
    membershipLevyBound.boundedExists (up (up ω)) <|
      membershipLevyBound.boundedExists (up (up (up ω))) <|
        membershipLevyBound.boundedExists (up (up (up (up ω)))) <|
          let w (t : Term ℒ Γ Δ .set) := up (up (up (up (up t))))
          let p : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
            .bvar (.there (.there (.there (.there .here))))
          let l : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
            .bvar (.there (.there (.there .here)))
          let c : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
            .bvar (.there (.there .here))
          let a : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
          let m : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
          .conj (PowerlessBoundedNumericPairing.formula_m (w ω) (w e) (w N) l c a) <|
            .conj (PowerlessBoundedNumericPairing.formula_m (w ω) (w e) (w N) p a (w i)) <|
              .conj (PowerlessLegacyAssignmentBounded.valid_m (w ω) (w e) (w N) (w P) c l) <|
                .conj (PowerlessSuccessorBounded.formula_m l m)
                  (PowerlessValueBounded.formula_m (w G) p m)

theorem delta_l {Γ Δ : SortContext ℒ} (ω e N P G i : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e N P G i) :=
  .bounded_exists ω (.bounded_exists (up ω) (.bounded_exists (up (up ω))
    (.bounded_exists (up (up (up ω))) (.bounded_exists (up (up (up (up ω))))
      (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
        (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
          (.conj (PowerlessLegacyAssignmentBounded.valid_delta_l _ _ _ _ _ _)
            (.conj (PowerlessSuccessorBounded.delta_l _ _) (PowerlessValueBounded.delta_l _ _ _)))))))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e N P G i : carrier_l 𝒩) : Prop :=
  ∃ p, member_l 𝒩 p ω ∧ ∃ l, member_l 𝒩 l ω ∧ ∃ c, member_l 𝒩 c ω ∧
    ∃ a, member_l 𝒩 a ω ∧ ∃ m, member_l 𝒩 m ω ∧
      PowerlessBoundedNumericPairing.holds_l ω e N l c a ∧
      PowerlessBoundedNumericPairing.holds_l ω e N p a i ∧
      PowerlessLegacyAssignmentBounded.valid_holds_l ω e N P c l ∧
      PowerlessNatural.successor_l l m ∧ value_l G p m

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N P G i : Term ℒ Γ Δ .set) :
    (formula_m ω e N P G i).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (N.eval η) (P.eval η) (G.eval η) (i.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedNumericPairing.formula_l,
    PowerlessLegacyAssignmentBounded.valid_formula_l, PowerlessSuccessorBounded.formula_l,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem reading_l (K : source_coding_l hℳ) {N P G : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega N) {E V : set_l ℳ}
    (hP : ∀ n m, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) P
      (code_l K n) (code_l K m) ↔ SecondOrderPairing.relation_l E n m)
    (hG : ∀ n m, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G
      (code_l K n) (code_l K m) ↔ SecondOrderPairing.relation_l V n m) (i : num_l ℳ) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega (code_l K (zero_l ℳ))
      N P G (code_l K i) ↔ SecondOrderLegalFormulaIndex.spec_l V E i := by
  unfold holds_l SecondOrderLegalFormulaIndex.spec_l
  simp only [PowerlessLegacyNumericReading.exists_number_l K]
  constructor
  · rintro ⟨p, l, c, a, m, hPair, hIndex, hValid, hSucc, hLegal⟩
    have hA := (PowerlessLegacyNumericReading.code_eq_l K a _).mp
      ((PowerlessBoundedNumericPairing.instance_l K hN l c _).mp hPair)
    subst a
    have hI := (PowerlessLegacyNumericReading.code_eq_l K i _).mp
      ((PowerlessBoundedNumericPairing.instance_l K hN p (SecondOrderPairing.value_l l c) _).mp hIndex)
    have hM := (PowerlessLegacyNumericReading.code_eq_l K m _).mp
      ((PowerlessNumberSuccessorReading.successor_l K l _).mp hSucc)
    subst m
    exact ⟨p, l, c, hI.symm, (PowerlessLegacyAssignmentBounded.valid_reading_l K hN hP c l).mp hValid,
      (hG p (succ_l l)).mp hLegal⟩
  · rintro ⟨p, l, c, hIndex, hValid, hLegal⟩
    refine ⟨p, l, c, SecondOrderPairing.value_l l c, succ_l l,
      (PowerlessBoundedNumericPairing.instance_l K hN l c _).mpr rfl,
      (PowerlessBoundedNumericPairing.instance_l K hN p (SecondOrderPairing.value_l l c) _).mpr ?_,
      (PowerlessLegacyAssignmentBounded.valid_reading_l K hN hP c l).mpr hValid,
      (PowerlessNumberSuccessorReading.successor_l K l _).mpr rfl, (hG p (succ_l l)).mpr hLegal⟩
    exact congrArg (code_l K) hIndex.symm

#print axioms delta_l
#print axioms reading_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyLegalIndexBounded
