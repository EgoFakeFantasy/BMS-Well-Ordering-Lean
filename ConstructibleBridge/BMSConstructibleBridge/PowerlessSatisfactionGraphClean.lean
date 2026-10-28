import BMSConstructibleBridge.PowerlessSatisfactionUnique
import BMSConstructibleBridge.PowerlessPairBounded

/-! # 无垃圾 Sat 图的有界证书与对象唯一性

原 Sat 规格只约束有序对读值，不排除非有序对成员。因此相同全部读值
本身不能推出两个图对象相等。这里额外给出纯 Δ₀ 的成员坐标证书；
证书加上全部读值相等，才由 Kuratowski 对唯一性和原商外延性认同对象。

没有改写原 Sat 规格，也没有从 Prop 选择图作为 Type 数据。此模块尚不
构造无垃圾图、统一 Sat 族或层内共同界；这些存在性不能由唯一性代替。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionGraphClean

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (ω S R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall R <|
    membershipLevyBound.boundedExists (up ω) <|
      membershipLevyBound.boundedExists (up (up S)) <|
        PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here)
          (.bvar (.there (.there .here)))

theorem delta_l {Γ Δ : SortContext ℒ} (ω S R : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω S R) :=
  .bounded_forall _ (.bounded_exists _ (.bounded_exists _
    (PowerlessPairBounded.ordered_delta_l _ _ _)))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω S R : carrier_l 𝒩) : Prop :=
  ∀ p, member_l 𝒩 p R → ∃ c f,
    member_l 𝒩 c ω ∧ member_l 𝒩 f S ∧ ordered_l c f p

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω S R : Term ℒ Γ Δ .set) :
    (formula_m ω S R).satisfies η ↔ holds_l (ω.eval η) (S.eval η) (R.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.boundedExists, Formula.LevyBound.membership, membershipLevyBound,
    Formula.satisfies, PowerlessPairBounded.ordered_formula_l, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  constructor
  · intro h p hp
    obtain ⟨c, hc, f, hf, hPair⟩ := h p hp
    exact ⟨c, f, hc, hf, hPair⟩
  · intro h p hp
    obtain ⟨c, f, hc, hf, hPair⟩ := h p hp
    exact ⟨c, hc, f, hf, hPair⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- 对全部 raw 坐标成立的读值相等，配合无垃圾证书，才给出图对象相等。 -/
theorem ext_l {ω S R R' : SecondOrderQuotient.type_l hℳ}
    (hR : holds_l (𝒩 := RawModel) ω S R) (hR' : holds_l (𝒩 := RawModel) ω S R')
    (hValues : ∀ c f, value_l (ℳ := RawModel) R c f ↔ value_l (ℳ := RawModel) R' c f) : R = R' := by
  apply SecondOrderQuotient.ext_l hℳ
  intro p
  constructor
  · intro hp
    obtain ⟨c, f, _hc, _hf, hPair⟩ := hR p hp
    obtain ⟨q, hq, hPair'⟩ := (hValues c f).mp ⟨p, hp, hPair⟩
    have hpq : p = q := SecondOrderPairObjects.ordered_unique_l hℳ hPair hPair'
    exact hpq.symm ▸ hq
  · intro hp
    obtain ⟨c, f, _hc, _hf, hPair⟩ := hR' p hp
    obtain ⟨q, hq, hPair'⟩ := (hValues c f).mpr ⟨p, hp, hPair⟩
    have hpq : p = q := SecondOrderPairObjects.ordered_unique_l hℳ hPair hPair'
    exact hpq.symm ▸ hq

theorem unique_l (K : source_coding_l hℳ) {A T F S R R' : SecondOrderQuotient.type_l hℳ}
    (hT : map_l (ℳ := RawModel) T K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K T)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hF : ∀ c L, value_l (ℳ := RawModel) F c L ↔ PowerlessRelationalCodeValidity.valid_l K V c L)
    (hR : PowerlessSatisfactionUnique.fixed_spec_l K A T F R)
    (hR' : PowerlessSatisfactionUnique.fixed_spec_l K A T F R')
    (hClean : holds_l (𝒩 := RawModel) K.omega S R)
    (hClean' : holds_l (𝒩 := RawModel) K.omega S R') : R = R' :=
  ext_l hClean hClean' (PowerlessSatisfactionUnique.values_l K hT hPair hV hF hR hR')

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionGraphClean
