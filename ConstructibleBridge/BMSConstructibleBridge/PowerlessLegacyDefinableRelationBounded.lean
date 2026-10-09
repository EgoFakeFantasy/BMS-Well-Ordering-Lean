import BMSConstructibleBridge.PowerlessLegacyDefinableQueryBounded
import BMSConstructibleBridge.PowerlessLegacyNumericReading
import BMSConstructibleBridge.SecondOrderDefinableFamily

/-! # 原 Def 全部内部指标的统一行关系

原平方索引精确展开为 p,(l,c)，随后调用同一个完整有界参数行证书。
全部参数码取自内部 ω，不用宿主列表枚举原公式。数码读取只展开指标；
原求值与行证书的对应仍由独立保持性接口验证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableRelationBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))

def index_m {Γ Δ : SortContext ℒ} (ω e N p l c i : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj
    (PowerlessBoundedNumericPairing.formula_m (up ω) (up e) (up N) (up l) (up c) (.bvar .here))
    (PowerlessBoundedNumericPairing.formula_m (up ω) (up e) (up N) (up p) (.bvar .here) (up i))

theorem index_delta_l {Γ Δ : SortContext ℒ} (ω e N p l c i : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (index_m ω e N p l c i) :=
  .bounded_exists ω (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
    (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _))

def index_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N p l c i : carrier_l 𝒩) : Prop :=
  ∃ a, member_l 𝒩 a ω ∧ PowerlessBoundedNumericPairing.holds_l ω e N l c a ∧
    PowerlessBoundedNumericPairing.holds_l ω e N p a i

theorem index_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N p l c i : Term ℒ Γ Δ .set) :
    (index_m ω e N p l c i).satisfies η ↔ index_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (p.eval η) (l.eval η) (c.eval η) (i.eval η) := by
  simp only [index_m, index_holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedNumericPairing.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def formula_m {Γ Δ : SortContext ℒ}
    (ω e N P F A S I U R i x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <|
    membershipLevyBound.boundedExists (up (up ω)) <| .conj
      (index_m (up₃ ω) (up₃ e) (up₃ N) (.bvar (.there (.there .here)))
        (.bvar (.there .here)) (.bvar .here) (up₃ i))
      (PowerlessLegacyDefinableQueryBounded.formula_m (up₃ ω) (up₃ e) (up₃ N) (up₃ P)
        (up₃ F) (up₃ A) (up₃ S) (up₃ I) (up₃ U) (up₃ R)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here) (up₃ x))

theorem delta_l {Γ Δ : SortContext ℒ}
    (ω e N P F A S I U R i x : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e N P F A S I U R i x) :=
  .bounded_exists ω (.bounded_exists (up ω) (.bounded_exists (up (up ω))
    (.conj (index_delta_l _ _ _ _ _ _ _) (PowerlessLegacyDefinableQueryBounded.delta_l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N P F A S I U R i x : carrier_l 𝒩) : Prop :=
  ∃ p, member_l 𝒩 p ω ∧ ∃ l, member_l 𝒩 l ω ∧ ∃ c, member_l 𝒩 c ω ∧
    index_holds_l ω e N p l c i ∧
      PowerlessLegacyDefinableQueryBounded.holds_l ω e N P F A S I U R p l c x

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N P F A S I U R i x : Term ℒ Γ Δ .set) :
    (formula_m ω e N P F A S I U R i x).satisfies η ↔ holds_l
      (ω.eval η) (e.eval η) (N.eval η) (P.eval η) (F.eval η) (A.eval η) (S.eval η) (I.eval η)
        (U.eval η) (R.eval η) (i.eval η) (x.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, index_formula_l,
    PowerlessLegacyDefinableQueryBounded.formula_l, Arguments.eval,
    up, up₃, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem index_reading_l (K : source_coding_l hℳ) {N : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega N) (p l c : SecondOrderModel.num_l ℳ) (i : type_l hℳ) :
    index_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (code_l K (SecondOrderModel.zero_l ℳ)) N (code_l K p) (code_l K l) (code_l K c) i ↔
        i = code_l K (SecondOrderDefinableFamily.index_l p l c) := by
  constructor
  · rintro ⟨a, _ha, hPair, hIndex⟩
    rw [(PowerlessBoundedNumericPairing.instance_l K hN l c a).mp hPair] at hIndex
    exact (PowerlessBoundedNumericPairing.instance_l K hN p (SecondOrderPairing.value_l l c) i).mp hIndex
  · intro h
    exact ⟨code_l K (SecondOrderPairing.value_l l c), (numberCode_l K _).property,
      (PowerlessBoundedNumericPairing.instance_l K hN l c _).mpr rfl,
      (PowerlessBoundedNumericPairing.instance_l K hN p (SecondOrderPairing.value_l l c) i).mpr h⟩

theorem reading_l (K : source_coding_l hℳ) {N : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega N) (P F A S I U R i x : type_l hℳ) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (code_l K (SecondOrderModel.zero_l ℳ)) N P F A S I U R i x ↔
        ∃ p l c, i = code_l K (SecondOrderDefinableFamily.index_l p l c) ∧
          PowerlessLegacyDefinableQueryBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
            K.omega (code_l K (SecondOrderModel.zero_l ℳ)) N P F A S I U R
              (code_l K p) (code_l K l) (code_l K c) x := by
  unfold holds_l
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro p
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro l
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro c
  exact and_congr (index_reading_l K hN p l c i) Iff.rfl

#print axioms delta_l
#print axioms index_reading_l
#print axioms reading_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableRelationBounded
