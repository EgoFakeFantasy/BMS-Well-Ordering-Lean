import BMSConstructibleBridge.PowerlessHereditaryArithmeticCandidate
import BMSConstructibleBridge.PowerlessHereditarySourceCore
import BMSConstructibleBridge.PowerlessHereditaryRealBasis

/-! # 每个原实数候选的实际完整遗传源

背景原 Z₂。给定原候选 X，以同一商代表 A 的精确基底 ω∪{A}
构造实际遗传模型及其完整原无幂集理论，再接同一源算术和成员代表。
逐候选只给 Nonempty；不抽取 Type 源族，不分全类可数与截断分支。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderHereditaryCandidateSource

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessHereditaryStructure.type_l PowerlessHereditaryStructure.structure_l

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (X : ℳ.Carrier .set) :
    Nonempty (PowerlessBMSMatrixTransfer.candidate_source_l.{u, u} (M := ℳ) X) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  obtain ⟨A, hTrace⟩ := representative_exists_l K X
  obtain ⟨B, hSpec, hAHC, hωHC, hBHC⟩ :=
    PowerlessHereditaryRealBasis.coverage_l hℳ K.omega A.val K.omega_spec A.property
  have hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B := by
    intro x hx y hy
    apply (hSpec y).mpr
    rcases (hSpec x).mp hx with hxω | rfl
    · exact Or.inl (SecondOrderOmegaTransitive.member_l hℳ K.omega_spec hxω hy)
    · exact Or.inl (A.property y hy)
  let O : PowerlessHereditaryStructure.type_l hℳ B := ⟨K.omega, hωHC⟩
  let e : PowerlessHereditaryStructure.type_l hℳ B :=
    ⟨(numberCode_l K (SecondOrderModel.zero_l ℳ)).val,
      PowerlessHereditaryClass.transitive_l hℳ hωHC
        (numberCode_l K (SecondOrderModel.zero_l ℳ)).property⟩
  let A₀ : PowerlessArithmetic.set_l
      (ℳ := PowerlessHereditaryStructure.structure_l hℳ B hBase) O :=
    ⟨⟨A.val, hAHC⟩, fun x hx => A.property x.val hx⟩
  have hNonempty : ∃ d, mem_l hℳ d B := ⟨A.val, (hSpec A.val).mpr (Or.inr rfl)⟩
  have hSource := PowerlessHereditarySourceCore.models_l (hBase := hBase) K hBHC hNonempty
  exact PowerlessHereditaryArithmeticCandidate.candidate_l (hBase := hBase)
    K hSource (ω := O) (e := e) rfl rfl X A₀ hTrace

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderHereditaryCandidateSource
