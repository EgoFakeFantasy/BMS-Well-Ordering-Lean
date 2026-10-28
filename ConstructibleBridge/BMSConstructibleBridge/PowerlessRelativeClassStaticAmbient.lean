import BMSConstructibleBridge.PowerlessRelativeClassStaticCodingReading
import BMSConstructibleBridge.PowerlessRelativeClassConstructorBounds
import BMSConstructibleBridge.PowerlessRelativeMemberConstructorAbsolute

/-! # 给定原完整静态包从实际 Class 读回原商

原 Z₂、纯隶属 ℒ。逐字段保留给定的零码、标签、配数、全有限
证书与合法性图；三角后继的原加法见证实际读出，构造子唯一性
使用原数码解释。不是把整包分类为 Δ₀，也不假定完整类理论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassStaticAmbient

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem reading_l (K : source_coding_l hℳ) {ω e t₁ t₂ t₃ P N F : M}
    (hω : ω.val = K.omega)
    (h : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒩₀) ω e t₁ t₂ t₃ P N F) :
    PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒱)
      ω.val e.val t₁.val t₂.val t₃.val P.val N.val F.val := by
  have hωRaw : SecondOrderOmega.omega_l hℳ ω.val := hω.symm ▸ K.omega_spec
  obtain ⟨he, _ht₁, _ht₂, _ht₃, hN, hPK, _hPair, _hValid⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l K hω h
  have he' : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := he
  have hP := (PowerlessRelativeClassFunctionAbsolute.map_l P ω ω).mp h.2.1.1
  refine ⟨⟨(PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp h.1.1,
    (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) e t₁).mp h.1.2.1,
    (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₁ t₂).mp h.1.2.2.1,
    (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₂ t₃).mp h.1.2.2.2⟩,
    ⟨hP, (PowerlessRelativeClassFunctionAbsolute.value_l P e e).mp h.2.1.2.1, ?_⟩,
    ?_, (by simpa only [hω] using hN), PowerlessRelativeClassValidityAbsolute.spec_l h.2.2.2.2⟩
  · intro n m x y hn hm hx hy
    obtain ⟨hnClass, hxClass⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase P hx
    obtain ⟨hmClass, hyClass⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase P hy
    let n₀ : M := ⟨n, hnClass⟩
    let m₀ : M := ⟨m, hmClass⟩
    let x₀ : M := ⟨x, hxClass⟩
    let y₀ : M := ⟨y, hyClass⟩
    exact PowerlessRelativeClassConstructorBounds.addition_to_ambient_l hωRaw
      (h.2.1.2.2 n₀ m₀ x₀ y₀ hn
        ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) n₀ m₀).mpr hm)
        ((PowerlessRelativeClassFunctionAbsolute.value_l P n₀ x₀).mpr hx)
        ((PowerlessRelativeClassFunctionAbsolute.value_l P m₀ y₀).mpr hy))
  · intro t ht a ha b hb
    let t₀ : M := ⟨t, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property ht⟩
    let a₀ : M := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property ha⟩
    let b₀ : M := ⟨b, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hb⟩
    obtain ⟨n, hn, hCtor, _⟩ := h.2.2.1 t₀ ht a₀ ha b₀ hb
    have hRaw := PowerlessRelativeClassConstructorBounds.constructor_to_ambient_l hωRaw hCtor
    refine ⟨n.val, hn, hRaw, ?_⟩
    intro m hm
    apply PowerlessRelativeMemberConstructorAbsolute.unique_l K hPK
    · simpa only [hω, he'] using hm
    · simpa only [hω, he'] using hRaw

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassStaticAmbient
