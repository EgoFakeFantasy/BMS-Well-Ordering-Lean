import BMSConstructibleBridge.SecondOrderFiniteParameterEnvelope
import BMSConstructibleBridge.PowerlessRelativeClassFixedCoding
import BMSConstructibleBridge.SecondOrderCanonicalOrderPreservation

/-! # 任意环境输入的完整规范 Def 后继

当次有限输入被放入一个临时传递基底。完整 Sat 与规范后继先在该辅助类
构造，再传回完整模型。原编码包保持不变；原层次基底也不改变。
这里不要求 A、旧序 P 或 Def 输出 D 属于先前指定的相对类。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderAmbientTotal

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 原模型中的任意合法输入都有完整后继良序，并保持旧序初段。 -/
theorem exists_l (K : source_coding_l hℳ)
    {ω A P e t₁ t₂ t₃ Pair Valid D : SecondOrderQuotient.type_l hℳ}
    (hω : ω = K.omega) (he : e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := 𝒱) e t₁ t₂ t₃)
    (hPairMap : map_l (ℳ := 𝒱) Pair K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hValid : ∀ c N, value_l (ℳ := 𝒱) Valid c N ↔ PowerlessRelationalCodeValidity.valid_l K V c N)
    (hP : wellOrder_l (ℳ := 𝒱) A P)
    (hTrans : ∀ x y, SecondOrderQuotient.mem_l hℳ x A → SecondOrderQuotient.mem_l hℳ y x →
      SecondOrderQuotient.mem_l hℳ y A) (hDef : SecondOrderMemberDef.spec_l hℳ A D) :
    ∃ E : SecondOrderQuotient.type_l hℳ,
      SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱) ω A P e t₁ t₂ t₃ Pair Valid D E ∧
      wellOrder_l (ℳ := 𝒱) D E ∧ SecondOrderWellOrderCoherentUnion.extension_l (ℳ₀ := 𝒱) A P D E := by
  let S := [A, P, e, t₁, t₂, t₃, Pair, Valid, D]
  obtain ⟨B, hBase, hωB, hS⟩ := SecondOrderFiniteParameterEnvelope.exists_l hℳ ω S
  have hClass (x : SecondOrderQuotient.type_l hℳ) (hx : x ∈ S) :
      PowerlessRelativeClassCorrespondence.member_l hℳ B x :=
    PowerlessRelativeClassCorrespondence.base_l hℳ hBase (hS x hx)
  let ω' : type_l hℳ B := ⟨ω, PowerlessRelativeClassCorrespondence.base_l hℳ hBase hωB⟩
  let A' : type_l hℳ B := ⟨A, hClass A (by simp [S])⟩
  let P' : type_l hℳ B := ⟨P, hClass P (by simp [S])⟩
  let e' : type_l hℳ B := ⟨e, hClass e (by simp [S])⟩
  let t₁' : type_l hℳ B := ⟨t₁, hClass t₁ (by simp [S])⟩
  let t₂' : type_l hℳ B := ⟨t₂, hClass t₂ (by simp [S])⟩
  let t₃' : type_l hℳ B := ⟨t₃, hClass t₃ (by simp [S])⟩
  let Pair' : type_l hℳ B := ⟨Pair, hClass Pair (by simp [S])⟩
  let Valid' : type_l hℳ B := ⟨Valid, hClass Valid (by simp [S])⟩
  let D' : type_l hℳ B := ⟨D, hClass D (by simp [S])⟩
  have hΩ : omega_l (ℳ := structure_l hℳ B hBase) ω' :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω').mpr
      (show SecondOrderOmega.omega_l hℳ ω from hω.symm ▸ K.omega_spec)
  have hTagsClass : PowerlessEvaluationTags.tags_l (ℳ := structure_l hℳ B hBase) e' t₁' t₂' t₃' :=
    ⟨(PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e').mpr hTags.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) e' t₁').mpr hTags.2.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₁' t₂').mpr hTags.2.2.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₂' t₃').mpr hTags.2.2.2⟩
  have hSat : ∃ R : type_l hℳ B,
      PowerlessSatisfactionSpecification.spec_l (𝒩 := structure_l hℳ B hBase)
        ω' A' e' t₁' t₂' t₃' Pair' Valid' R :=
    PowerlessRelativeClassFixedCoding.satisfaction_l K hω he hTags hPairMap hPair hV hValid
  obtain ⟨E, ⟨hStep, hOrder, _, _⟩, _⟩ :=
    PowerlessRelativeClassCanonicalOrderUniform.exists_unique_l
      (hBase := hBase) (ω := ω') (A := A') (P := P') (e := e') (t₁ := t₁') (t₂ := t₂')
      (t₃ := t₃') (Pair := Pair') (Valid := Valid') (D := D')
      K hΩ hP hω he hTagsClass hPairMap hPair hV hValid hSat hTrans hDef
  have hRaw := SecondOrderCanonicalOrderUniform.step_ambient_l K hω he hPairMap hPair hStep
  exact ⟨E.val, hRaw, hOrder, SecondOrderCanonicalOrderPreservation.extension_l hRaw hTrans hDef⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderAmbientTotal
