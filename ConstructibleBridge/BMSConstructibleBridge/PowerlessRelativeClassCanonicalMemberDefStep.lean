import BMSConstructibleBridge.PowerlessRelativeClassCanonicalOrderStep

/-! # 原 Def 的统一规范后继存在（包含空母集）

空分支不用另选良序：零码也是实际空函数，给出全槽空间中的一个指标；
空母集自身是该指标的行，原单元素 Def 因此被同一规范行族覆盖。
非空分支保留固定 Sat，用原五标签呈现证明覆盖。完整后继图存在唯一，
但本模块仍是实际模型工具，尚未收集内部历史或给出最终对象句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalMemberDefStep

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessFormulaValidityReading (code_l)
open PowerlessRelativeClassCanonicalOrderStep (candidate_l step_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒞" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem empty_l (K : source_coding_l hℳ) {ω A P e R D : type_l hℳ B}
    (hΩ : omega_l (ℳ := 𝒞) ω) (hP : wellOrder_l (ℳ := 𝒱) A.val P.val)
    (hω : ω.val = K.omega) (he : e.val = code_l K (SecondOrderModel.zero_l ℳ))
    (hEmpty : ∀ x, ¬SecondOrderQuotient.mem_l hℳ x A.val)
    (hD : SecondOrderPairObjects.pair_l hℳ A.val A.val D.val) :
    ∃ L : type_l hℳ B, candidate_l (hBase := hBase) ω A P R D L := by
  obtain ⟨S, I, J, U, Q, Y, L, hS, hI, hJ, _, hRead, hRows, hGraph, hOrder, _, hIndex⟩ :=
    PowerlessRelativeClassSatisfactionAllSlotsCanonical.exists_l hΩ hP R
  have hZero : ∀ x, ¬SecondOrderQuotient.mem_l hℳ x e.val := he.symm ▸ PowerlessBMSQuotientSuccessor.zero_l K
  have heω : SecondOrderQuotient.mem_l hℳ e.val ω.val :=
    he.symm ▸ hω.symm ▸ (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
  have hMap : map_l (ℳ := 𝒞) e e A :=
    ⟨fun p hp => (hZero p.val hp).elim, fun x hx => (hZero x.val hx).elim⟩
  have heS := (hS e).mpr ⟨e, heω, hMap⟩
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ e.val e.val
  let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassPair.ordered_l hℳ hBase e.property e.property hp⟩
  have hp' : ordered_l (ℳ := 𝒞) e e p' := (PowerlessRelativeClassFunctionAbsolute.ordered_l e e p').mpr hp
  have hpI := (hI p').mpr ⟨e, e, heω, heS, hp'⟩
  obtain ⟨t, ht⟩ := SecondOrderPairObjects.ordered_exists_l hℳ e.val p
  let t' : type_l hℳ B := ⟨t, PowerlessRelativeClassPair.ordered_l hℳ hBase e.property p'.property ht⟩
  have ht' : ordered_l (ℳ := 𝒞) e p' t' := (PowerlessRelativeClassFunctionAbsolute.ordered_l e p' t').mpr ht
  have htJ := (hJ t').mpr ⟨e, p', heω, hpI, ht'⟩
  have hRow : PowerlessRelativeClassRowFamily.row_l (ℳ₀ := 𝒞) A Q t' A :=
    fun x => ⟨fun hx => (hEmpty x.val hx).elim, fun hx => hx.1⟩
  have hAY := (hRows A).mpr ⟨t', htJ, hRow⟩
  have hSubset : subset_l (ℳ := 𝒱) D.val Y.val := by
    intro z hz
    have hEq : z = A.val := ((hD z).mp hz).elim id id
    exact hEq.symm ▸ hAY
  exact ⟨L, S, I, J, U, Q, Y, hIndex, hRead, hRows, hGraph, hSubset, hOrder⟩

theorem of_spec_l (K : source_coding_l hℳ) {ω A P e t₁ t₂ t₃ Pair Valid Sat D : type_l hℳ B}
    (hΩ : omega_l (ℳ := 𝒞) ω) (hP : wellOrder_l (ℳ := 𝒱) A.val P.val)
    (hω : ω.val = K.omega) (he : e.val = code_l K (SecondOrderModel.zero_l ℳ))
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := 𝒞) e t₁ t₂ t₃)
    (hPairMap : map_l (ℳ := 𝒱) Pair.val K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair.val)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hValid : ∀ c N, value_l (ℳ := 𝒱) Valid.val c N ↔ PowerlessRelationalCodeValidity.valid_l K V c N)
    (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒞) ω A e t₁ t₂ t₃ Pair Valid Sat)
    (hD : SecondOrderMemberDef.spec_l hℳ A.val D.val) :
    ∃ L : type_l hℳ B, candidate_l (hBase := hBase) ω A P Sat D L := by
  rcases hD with ⟨hEmpty, hD⟩ | hD
  · exact empty_l K hΩ hP hω he hEmpty hD
  · obtain ⟨A₀, a, ha, W, E, I₀, Q₀, R₀, T₀, F₀, H, hA, hPresentation, hH⟩ := hD
    obtain ⟨S, I, J, U, Q, Y, L, hIndex, hRead, hRows, hGraph, hOrder, hSubset, _⟩ :=
      PowerlessLegacyMemberDefCanonicalAmbient.exists_l K hΩ hP hω he hTags hPairMap hPair hV hValid hSat
        hPresentation hA.symm
    refine ⟨L, S, I, J, U, Q, Y, hIndex, hRead, hRows, hGraph, ?_, hOrder⟩
    intro z hz
    exact hSubset z (hH.symm ▸ hz)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalMemberDefStep
