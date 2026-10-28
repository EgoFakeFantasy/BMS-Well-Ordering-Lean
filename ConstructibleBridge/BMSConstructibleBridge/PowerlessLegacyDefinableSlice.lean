import BMSConstructibleBridge.PowerlessLegacyDefinableRows
import BMSConstructibleBridge.PowerlessLegacyAssignmentRealization
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlots

/-! # 原 Def 行的实际类内集合及环境逐值规格

对指定内部原索引，构造反转填充赋值和指定槽查询，再以实际 Δ₀
分离得到类内切片。环境枚举的满射性把该切片读为全部原数值代表的
精确像，读数的环境量词不被相对化隐藏。本模块不声称整个原 Def
集合属于类，也不声称环境商上的良序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableSlice

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderFiniteAssignmentLift (number_l)
open SecondOrderModel

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase

private theorem query_slice_l (ω A Seq e Sat t : type_l hℳ B) :
    ∃ Z : type_l hℳ B, PowerlessRelativeClassSatisfactionFamilyWellOrder.slice_l
      (ℳ₀ := 𝒩) ω A Seq e Sat t Z := by
  let η : Env 𝒩 [] [.set, .set, .set, .set, .set, .set] :=
    ((((((Env.empty).pushFree t).pushFree Sat).pushFree e).pushFree Seq).pushFree A).pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
    PowerlessRelativeClassSatisfactionRows.query_m
      (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here))))))) (.fvar .here)
  obtain ⟨Z, hZ⟩ := PowerlessRelativeClassDeltaSeparation.exists_l
    (φ := φ) (PowerlessRelativeClassSatisfactionRows.query_delta_l _ _ _ _ _ _ _) η A
  refine ⟨Z, fun x => (hZ x).trans (and_congr Iff.rfl ?_)⟩
  exact PowerlessRelativeClassSatisfactionRows.query_formula_l (η.pushFree x) _ _ _ _ _ _ _

theorem exists_l (K : source_coding_l hℳ) {ω A Seq Sat : type_l hℳ B}
    (hΩ : omega_l (ℳ := 𝒩) ω) (hω : ω.val = K.omega)
    {E D T F C : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (hD : ∀ v, mem_l v D) (hF : SecondOrderDefinableFamily.spec_l E D T F)
    {p l c q L : num_l ℳ} {U : SecondOrderQuotient.type_l hℳ}
    (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (hQuery : SecondOrderLegacyFormulaTranslation.query_l C p (succ_l l) q)
    (hBound : SecondOrderLegacyFormulaTranslationLength.bound_l (succ_l l) p L)
    (hPreservation : ∀ n, PowerlessLegacyEvaluationRow.row_l K B A.val U Sat.val E C T n)
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A.val)
    (hOnto : ∀ y, member_l (SecondOrderQuotient.structure_l hℳ) y A.val →
      ∃ v, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K v).val y)
    (hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω A Seq) :
    ∃ f t Z : type_l hℳ B,
      map_l (ℳ := 𝒩) f (number_l hBase K ω hω L) A ∧
      ordered_l (ℳ := 𝒩) (number_l hBase K ω hω q) f t ∧
      PowerlessRelativeClassSatisfactionFamilyWellOrder.slice_l
        (ℳ₀ := 𝒩) ω A Seq (number_l hBase K ω hω l) Sat t Z ∧
      ∀ y : SecondOrderQuotient.type_l hℳ, SecondOrderQuotient.mem_l hℳ y Z.val ↔
        ∃ v, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K v).val y ∧
          SecondOrderPairing.relation_l F (SecondOrderDefinableFamily.index_l p l c) v := by
  obtain ⟨f, hf, hLink⟩ := PowerlessLegacyAssignmentRealization.exists_l
    (hBase := hBase) K hΩ hω hE hc L (zero_l ℳ) hU
  obtain ⟨t, ht⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (numberCode_l K q).val f.val
  let t' : type_l hℳ B := ⟨t, PowerlessRelativeClassPair.ordered_l hℳ hBase
    (number_l hBase K ω hω q).property f.property ht⟩
  have ht' := (PowerlessRelativeClassFunctionAbsolute.ordered_l
    (hBase := hBase) (number_l hBase K ω hω q) f t').mpr ht
  obtain ⟨Z, hZ⟩ := query_slice_l (hBase := hBase) ω A Seq (number_l hBase K ω hω l) Sat t'
  refine ⟨f, t', Z, hf, ht', hZ, ?_⟩
  intro y
  constructor
  · intro hy
    let y' : type_l hℳ B := ⟨y,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Z.property hy⟩
    obtain ⟨hyA, hQueryY⟩ := (hZ y').mp hy
    obtain ⟨v, hv⟩ := hOnto y hyA
    exact ⟨v, hv, (PowerlessLegacyDefinableRows.read_l (hBase := hBase) K hΩ hω hE hD hF
      hc hQuery hBound hPreservation hU hf hLink hSeq ht' hv).mpr hQueryY⟩
  · rintro ⟨v, hv, hFv⟩
    have hyA := (SecondOrderFunctionProperties.value_mem_l hℳ hU hv).2
    let y' : type_l hℳ B := ⟨y,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hyA⟩
    have hQueryY := (PowerlessLegacyDefinableRows.read_l (hBase := hBase) K hΩ hω hE hD hF
      hc hQuery hBound hPreservation hU hf hLink hSeq ht' (x := y') hv).mp hFv
    exact (hZ y').mpr ⟨hyA, hQueryY⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableSlice
