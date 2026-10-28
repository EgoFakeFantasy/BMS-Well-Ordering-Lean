import BMSConstructibleBridge.PowerlessRelativeClassSequenceSlices
import BMSConstructibleBridge.PowerlessRelativeClassFiniteMapLift

/-! # 定长序列切片的环境成员规格

反向成员蕴涵先提升任意环境有限函数图，不能预设该图属于相对类。
任意满足环境精确规格的切片再由外延性与实际类内切片相等，因而
整个切片也属于类。这是环境公式归纳的语义辅助步骤。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceSlicesAbsolute

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem spec_l {ω n X P : type_l hℳ B}
    (hω : omega_l (ℳ := 𝒩) ω) (hn : member_l 𝒩 n ω)
    (hP : PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := 𝒩) n X P) :
    PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := 𝒱) n.val X.val P.val := by
  intro f
  constructor
  · intro hf
    let f' : type_l hℳ B := ⟨f,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase P.property hf⟩
    exact (PowerlessRelativeClassFunctionAbsolute.map_l f' n X).mp ((hP f').mp hf)
  · intro hf
    let f' : type_l hℳ B := ⟨f,
      PowerlessRelativeClassFiniteMapLift.member_l hBase ω.property X.property
        ((PowerlessRelativeClassOmegaAbsolute.omega_l ω).mp hω) hn hf⟩
    exact (hP f').mpr ((PowerlessRelativeClassFunctionAbsolute.map_l f' n X).mpr hf)

theorem lift_l {ω n X : type_l hℳ B} (hω : omega_l (ℳ := 𝒩) ω)
    (hn : member_l 𝒩 n ω) {P : SecondOrderQuotient.type_l hℳ}
    (hP : PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := 𝒱) n.val X.val P) :
    ∃ Q : type_l hℳ B, Q.val = P ∧
      PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := 𝒩) n X Q := by
  obtain ⟨Q, hQ⟩ := PowerlessRelativeClassSequenceSlices.of_omega_l (X := X) hω hn
  refine ⟨Q, ?_, hQ⟩
  apply SecondOrderQuotient.ext_l hℳ
  exact fun f => (spec_l hω hn hQ f).trans (hP f).symm

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceSlicesAbsolute
