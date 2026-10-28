import BMSConstructibleBridge.PowerlessBoundedSequenceCode
import BMSConstructibleBridge.SecondOrderPairingBounds

/-! # 长度与二进制码合成单一内部编号

编号关系是纯 Δ₀。数值配数只需单射，不要求每个自然数都能反解为配数。
同一编号最多描述一张有限函数图；允许同一图有多个编号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedSequenceIndex

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (ω e S one two I f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <|
    .conj (PowerlessMapBounded.formula_m (w f) (.bvar (.there .here)) (w ω)) <| .conj
      (PowerlessBoundedSequenceCode.formula_m (w ω) (w e) (w S) (w one) (w two)
        (.bvar (.there .here)) (.bvar .here) (w f))
      (PowerlessBoundedNumericPairing.formula_m (w ω) (w e) (w S)
        (.bvar (.there .here)) (.bvar .here) (w I))

theorem delta_l {Γ Δ : SortContext ℒ} (ω e S one two I f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e S one two I f) :=
  .bounded_exists ω (.bounded_exists (up ω) (.conj (PowerlessMapBounded.delta_l _ _ _)
    (.conj (PowerlessBoundedSequenceCode.delta_l _ _ _ _ _ _ _ _)
      (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S one two I f : carrier_l 𝒩) : Prop :=
  ∃ n, member_l 𝒩 n ω ∧ ∃ c, member_l 𝒩 c ω ∧ map_l (ℳ := 𝒩) f n ω ∧
    PowerlessBoundedSequenceCode.holds_l (𝒩 := 𝒩) ω e S one two n c f ∧
      PowerlessBoundedNumericPairing.holds_l (𝒩 := 𝒩) ω e S n c I

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S one two I f : Term ℒ Γ Δ .set) : (formula_m ω e S one two I f).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (S.eval η) (one.eval η) (two.eval η) (I.eval η) (f.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessMapBounded.formula_l,
    PowerlessBoundedSequenceCode.formula_l, PowerlessBoundedNumericPairing.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem pairing_injective_l (K : source_coding_l hℳ) {S n c m d I : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    (hn : mem_l hℳ n K.omega) (hc : mem_l hℳ c K.omega)
    (hm : mem_l hℳ m K.omega) (hd : mem_l hℳ d K.omega)
    (hPair : PowerlessBoundedNumericPairing.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S n c I)
    (hPair' : PowerlessBoundedNumericPairing.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S m d I) : n = m ∧ c = d := by
  obtain ⟨a, ha⟩ := numberCode_surjective_l K ⟨n, hn⟩
  obtain ⟨b, hb⟩ := numberCode_surjective_l K ⟨c, hc⟩
  obtain ⟨x, hx⟩ := numberCode_surjective_l K ⟨m, hm⟩
  obtain ⟨y, hy⟩ := numberCode_surjective_l K ⟨d, hd⟩
  have haEq : n = (numberCode_l K a).val := (congrArg Subtype.val ha).symm
  have hbEq : c = (numberCode_l K b).val := (congrArg Subtype.val hb).symm
  have hxEq : m = (numberCode_l K x).val := (congrArg Subtype.val hx).symm
  have hyEq : d = (numberCode_l K y).val := (congrArg Subtype.val hy).symm
  rw [haEq, hbEq] at hPair
  rw [hxEq, hyEq] at hPair'
  have hI := (PowerlessBoundedNumericPairing.instance_l K hS a b I).mp hPair
  have hI' := (PowerlessBoundedNumericPairing.instance_l K hS x y I).mp hPair'
  have hEq := numberCode_injective_l K (Subtype.ext (hI.symm.trans hI'))
  obtain ⟨rfl, rfl⟩ := SecondOrderPairingBounds.injective_l hℳ a b x y hEq
  exact ⟨haEq.trans hxEq.symm, hbEq.trans hyEq.symm⟩

theorem unique_l (K : source_coding_l hℳ) {S one two I f g : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    (hf : holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S one two I f)
    (hg : holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S one two I g) : f = g := by
  obtain ⟨n, hn, c, hc, hfMap, hfCode, hfPair⟩ := hf
  obtain ⟨m, hm, d, hd, hgMap, hgCode, hgPair⟩ := hg
  obtain ⟨rfl, rfl⟩ := pairing_injective_l K hS hn hc hm hd hfPair hgPair
  exact PowerlessBoundedSequenceCode.unique_l K hn hfMap hgMap hfCode hgCode

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedSequenceIndex
