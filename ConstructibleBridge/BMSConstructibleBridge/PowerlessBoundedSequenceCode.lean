import BMSConstructibleBridge.PowerlessBoundedExponentiation
import BMSConstructibleBridge.PowerlessBoundedNumericPairing
import BMSConstructibleBridge.PowerlessBoundedDigit
import BMSConstructibleBridge.SecondOrderQuotientFiniteSequenceCode

/-! # 内部有限函数的纯 Δ₀ 二进制编码关系

数值配数、二进制幂及位检查全部使用同一个 S 界。编码精确覆盖所有内部
坐标而不是只保存已知值；同一长度与编码不能描述两个不同的实际函数图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedSequenceCode

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def bit_m {Γ Δ : SortContext ℒ} (ω e S one two c i j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj
    (PowerlessBoundedNumericPairing.formula_m (up ω) (up e) (up S) (up i) (up j) (.bvar .here)) <|
    membershipLevyBound.boundedExists (up ω) <| .conj
      (PowerlessBoundedExponentiation.formula_m (up (up ω)) (up (up e)) (up (up S))
        (up (up one)) (up (up two)) (.bvar (.there .here)) (.bvar .here))
      (PowerlessBoundedDigit.formula_m (up (up ω)) (up (up e)) (up (up S)) (up (up c)) (.bvar .here))

theorem bit_delta_l {Γ Δ : SortContext ℒ} (ω e S one two c i j : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (bit_m ω e S one two c i j) :=
  .bounded_exists ω (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
    (.bounded_exists (up ω) (.conj (PowerlessBoundedExponentiation.delta_l _ _ _ _ _ _ _)
      (PowerlessBoundedDigit.delta_l _ _ _ _ _))))

def bit_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S one two c i j : carrier_l 𝒩) : Prop :=
  ∃ z, member_l 𝒩 z ω ∧ PowerlessBoundedNumericPairing.holds_l (𝒩 := 𝒩) ω e S i j z ∧
    ∃ p, member_l 𝒩 p ω ∧ PowerlessBoundedExponentiation.holds_l (𝒩 := 𝒩) ω e S one two z p ∧
      PowerlessBoundedDigit.holds_l (𝒩 := 𝒩) ω e S c p

theorem bit_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S one two c i j : Term ℒ Γ Δ .set) : (bit_m ω e S one two c i j).satisfies η ↔
      bit_l (ω.eval η) (e.eval η) (S.eval η) (one.eval η) (two.eval η) (c.eval η) (i.eval η) (j.eval η) := by
  simp only [bit_m, bit_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedNumericPairing.formula_l,
    PowerlessBoundedExponentiation.formula_l, PowerlessBoundedDigit.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def formula_m {Γ Δ : SortContext ℒ} (ω e S one two n c f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  membershipLevyBound.boundedForall ω <| membershipLevyBound.boundedForall (up ω) <|
    .iff (bit_m (w ω) (w e) (w S) (w one) (w two) (w c) (.bvar (.there .here)) (.bvar .here))
      (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (w n))
        (PowerlessValueBounded.formula_m (w f) (.bvar (.there .here)) (.bvar .here)))

theorem delta_l {Γ Δ : SortContext ℒ} (ω e S one two n c f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e S one two n c f) :=
  .bounded_forall ω (.bounded_forall (up ω) (.iff (bit_delta_l _ _ _ _ _ _ _ _)
    (.conj (.rel _ _) (PowerlessValueBounded.delta_l _ _ _))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S one two n c f : carrier_l 𝒩) : Prop :=
  ∀ i, member_l 𝒩 i ω → ∀ j, member_l 𝒩 j ω →
    (bit_l (𝒩 := 𝒩) ω e S one two c i j ↔ member_l 𝒩 i n ∧ value_l (ℳ := 𝒩) f i j)

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S one two n c f : Term ℒ Γ Δ .set) : (formula_m ω e S one two n c f).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (S.eval η) (one.eval η) (two.eval η) (n.eval η) (c.eval η) (f.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, bit_formula_l, PowerlessValueBounded.formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem bit_instance_l (K : source_coding_l hℳ) {S : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    {E : SecondOrderModel.set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E) (c i j : SecondOrderModel.num_l ℳ) :
    bit_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S
      (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val
      (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)))).val
      (numberCode_l K c).val (numberCode_l K i).val (numberCode_l K j).val ↔
        SecondOrderDigit.holds_l c (SecondOrderPowers.value_l hE (SecondOrderPairing.value_l i j)) := by
  constructor
  · rintro ⟨z, _, hPair, p, _, hPower, hDigit⟩
    have hz := (PowerlessBoundedNumericPairing.instance_l K hS i j z).mp hPair
    rw [hz] at hPower
    obtain ⟨k, hk, hp⟩ := (PowerlessBoundedExponentiation.instance_l K hS hE
      (SecondOrderPairing.value_l i j) p).mp hPower
    have hk' := (SecondOrderPowers.eq_l hE (SecondOrderPairing.value_l i j) k).mp hk
    rw [hk'] at hp
    rw [hp] at hDigit
    exact (PowerlessBoundedDigit.instance_l K hS c _).mp hDigit
  · intro hDigit
    refine ⟨(numberCode_l K (SecondOrderPairing.value_l i j)).val,
      (numberCode_l K (SecondOrderPairing.value_l i j)).property,
      (PowerlessBoundedNumericPairing.instance_l K hS i j _).mpr rfl,
      (numberCode_l K (SecondOrderPowers.value_l hE (SecondOrderPairing.value_l i j))).val,
      (numberCode_l K (SecondOrderPowers.value_l hE (SecondOrderPairing.value_l i j))).property,
      (PowerlessBoundedExponentiation.instance_l K hS hE (SecondOrderPairing.value_l i j) _).mpr
        ⟨_, SecondOrderPowers.edge_l hE _, rfl⟩,
      (PowerlessBoundedDigit.instance_l K hS c _).mpr hDigit⟩

theorem instance_l (K : source_coding_l hℳ) {S : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    {E : SecondOrderModel.set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (n c : SecondOrderModel.num_l ℳ) (f : type_l hℳ) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S
      (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val
      (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)))).val
      (numberCode_l K n).val (numberCode_l K c).val f ↔
        ∀ i j, SecondOrderDigit.holds_l c (SecondOrderPowers.value_l hE (SecondOrderPairing.value_l i j)) ↔
          mem_l hℳ (numberCode_l K i).val (numberCode_l K n).val ∧
            value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f (numberCode_l K i).val (numberCode_l K j).val := by
  constructor
  · intro h i j
    exact (bit_instance_l K hS hE c i j).symm.trans
      (h (numberCode_l K i).val (numberCode_l K i).property (numberCode_l K j).val (numberCode_l K j).property)
  · intro h i hi j hj
    obtain ⟨a, ha⟩ := numberCode_surjective_l K ⟨i, hi⟩
    obtain ⟨b, hb⟩ := numberCode_surjective_l K ⟨j, hj⟩
    have ha' : (numberCode_l K a).val = i := congrArg Subtype.val ha
    have hb' : (numberCode_l K b).val = j := congrArg Subtype.val hb
    rw [← ha', ← hb']
    exact (bit_instance_l K hS hE c a b).trans (h a b)

theorem exists_l (K : source_coding_l hℳ) {S : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    {E : SecondOrderModel.set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (n : SecondOrderModel.num_l ℳ) {f : type_l hℳ}
    (hf : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f (numberCode_l K n).val K.omega) :
    ∃ c : SecondOrderModel.num_l ℳ, holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S
      (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val
      (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)))).val
      (numberCode_l K n).val (numberCode_l K c).val f := by
  obtain ⟨c, hc⟩ := SecondOrderQuotientFiniteSequenceCode.exists_l K hE n hf
  exact ⟨c, (instance_l K hS hE n c f).mpr hc⟩

/-- 同一长度、同一位关系精确描述至多一张实际函数图；不要求编码唯一。 -/
theorem unique_l (K : source_coding_l hℳ) {e S one two n c f g : type_l hℳ}
    (hn : mem_l hℳ n K.omega)
    (hf : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f n K.omega)
    (hg : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) g n K.omega)
    (hcf : holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega e S one two n c f)
    (hcg : holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega e S one two n c g) : f = g := by
  apply PowerlessBMSQuotientRecursion.map_ext_l (hM := hℳ) hf hg
  intro x y
  constructor
  · intro hxy
    have hmem := PowerlessBMSQuotientRecursion.value_mem_l (hM := hℳ) hf hxy
    have hx := SecondOrderOmegaTransitive.member_l hℳ K.omega_spec hn hmem.1
    exact ((hcg x hx y hmem.2).mp ((hcf x hx y hmem.2).mpr ⟨hmem.1, hxy⟩)).2
  · intro hxy
    have hmem := PowerlessBMSQuotientRecursion.value_mem_l (hM := hℳ) hg hxy
    have hx := SecondOrderOmegaTransitive.member_l hℳ K.omega_spec hn hmem.1
    exact ((hcf x hx y hmem.2).mp ((hcg x hx y hmem.2).mpr ⟨hmem.1, hxy⟩)).2

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedSequenceCode
