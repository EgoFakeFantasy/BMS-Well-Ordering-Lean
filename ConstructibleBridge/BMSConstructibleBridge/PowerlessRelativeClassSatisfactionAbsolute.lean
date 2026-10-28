import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionSpecification
import BMSConstructibleBridge.PowerlessRelativeClassEvaluationAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequencesDerives

/-! # 完整类内 Sat 规格的环境传输

先在证明内构造全部内部有限赋值集。任意环境合法赋值因此能提升到类，
原构造子用已证反向接口提升，存在分支保留任意环境更新见证。
这不是将任意不受守卫的类内全称命题直接推广到环境。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒞" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem spec_l (K : source_coding_l hℳ) {ω A e t₁ t₂ t₃ T F R : type_l hℳ B}
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hT : map_l (ℳ := 𝒱) T.val K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
    (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒞) ω A e t₁ t₂ t₃ T F R) :
    PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒱)
      ω.val A.val e.val t₁.val t₂.val t₃.val T.val F.val R.val := by
  have hΩ : omega_l (ℳ := 𝒞) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr (hω.symm ▸ K.omega_spec)
  obtain ⟨Seq, hSeq, _⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l
    (hBase := hBase) (X := A) hΩ
  refine ⟨?_, ?_, ?_⟩
  · intro c f hValue
    obtain ⟨hc, hf⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase R hValue
    let c' : type_l hℳ B := ⟨c, hc⟩
    let f' : type_l hℳ B := ⟨f, hf⟩
    obtain ⟨hcω, L, hL, hF, hMap⟩ := hSat.1 c' f'
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R c' f').mpr hValue)
    exact ⟨hcω, L.val, hL,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F c' L).mp hF,
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f' L A).mp hMap⟩
  · intro f hValue
    let f' : type_l hℳ B := ⟨f, (PowerlessRelativeClassValueCoordinates.value_l hBase R hValue).2⟩
    exact hSat.2.1 f' ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R e f').mpr hValue)
  · intro c L f hc hL hf a b
    let c' : type_l hℳ B := ⟨c, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hc⟩
    let L' : type_l hℳ B := ⟨L, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hL⟩
    let f' : type_l hℳ B := ⟨f, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Seq.property
      ((hSeq f).mpr ⟨L, hL, hf⟩)⟩
    have hf' : map_l (ℳ := 𝒞) f' L' A :=
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f' L' A).mpr hf
    have hBranches := hSat.2.2 c' L' f' hc hL hf'
    have hValue : value_l (ℳ := 𝒱) R.val c f ↔ value_l (ℳ := 𝒞) R c' f' :=
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R c' f').symm
    have lift (t : type_l hℳ B)
        (h : PowerlessFormulaConstructor.constructor_l (ℳ := 𝒱) ω.val e.val T.val t.val a b c) :
        ∃ a' b' : type_l hℳ B, a'.val = a ∧ b'.val = b ∧
          PowerlessFormulaConstructor.constructor_l (ℳ := 𝒞) ω e T t a' b' c' := by
      let a' : type_l hℳ B := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property h.1⟩
      let b' : type_l hℳ B := ⟨b, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property h.2.1⟩
      refine ⟨a', b', rfl, rfl, ?_⟩
      apply PowerlessRelativeClassConstructorTotal.constructor_from_ambient_l K hω he hT hPair
      simpa only [hω, he] using h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hCtor ha hb
      obtain ⟨a', b', rfl, rfl, hCtor'⟩ := lift e hCtor
      exact hValue.trans (((hBranches a' b').1 hCtor' ha hb).trans
        (PowerlessRelativeClassEvaluationAbsolute.member_l (hBase := hBase) f' a' b'))
    · intro hCtor ha hb
      obtain ⟨a', b', rfl, rfl, hCtor'⟩ := lift t₁ hCtor
      exact hValue.trans (((hBranches a' b').2.1 hCtor' ha hb).trans
        (PowerlessRelativeClassEvaluationAbsolute.equal_l (hBase := hBase) f' a' b'))
    · intro hCtor ha hb
      obtain ⟨a', b', rfl, rfl, hCtor'⟩ := lift t₂ hCtor
      have ha' := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F a' L').mpr ha
      have hb' := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F b' L').mpr hb
      exact hValue.trans (((hBranches a' b').2.2.1 hCtor' ha' hb').trans
        (not_congr (and_congr
          (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R a' f')
          (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R b' f'))))
    · intro hCtor ha hb
      obtain ⟨a', b', rfl, rfl, hCtor'⟩ := lift t₃ hCtor
      have hb' := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F b' L').mpr hb
      exact hValue.trans (((hBranches a' b').2.2.2 hCtor' ha hb').trans
        (PowerlessRelativeClassEvaluationAbsolute.exists_l (hBase := hBase) ω A Seq R f' a' b' hSeq))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionAbsolute
