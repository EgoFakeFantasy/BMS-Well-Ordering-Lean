import BMSConstructibleBridge.PowerlessRelativeCofinalSatisfaction
import BMSConstructibleBridge.PowerlessRelativeLimitStaticCoding

/-! # 给定共尾极限层：先固定实际编码包，再逐域构造 Sat

静态参数的层内成员性在本文件中实际取得，不再由调用者提供。
每个求值域仍必须属于给定层；结论不把该层冒充完整源模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalSatisfactionForDomain

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β C : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase

private abbrev parameters_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set]

theorem exists_l (K : source_coding_l hℳ) (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    (ω : type_l hℳ B) (hωC : mem_l hℳ ω.val C) (hωEq : ω.val = K.omega) :
    ∃ e t₁ t₂ t₃ T N F : type_l hℳ B,
      mem_l hℳ e.val C ∧ mem_l hℳ t₁.val C ∧ mem_l hℳ t₂.val C ∧ mem_l hℳ t₃.val C ∧
        mem_l hℳ T.val C ∧ mem_l hℳ N.val C ∧ mem_l hℳ F.val C ∧
          PowerlessSatisfactionExistenceSyntax.static_l («𝒩» := 𝒩) ω e t₁ t₂ t₃ T N F ∧
            ∀ A : type_l hℳ B, mem_l hℳ A.val C → ∃ R : type_l hℳ B, mem_l hℳ R.val C ∧
              PowerlessSatisfactionSpecification.spec_l («𝒩» := 𝒩) ω A e t₁ t₂ t₃ T F R := by
  obtain ⟨e, t₁, t₂, t₃, T, N, F, heC, ht₁C, ht₂C, ht₃C, hTC, hNC, hFC, hStatic⟩ :=
    PowerlessRelativeLimitStaticCoding.exists_l K hLimit hC ω hωC hωEq
  have hω : omega_l (ℳ := 𝒩) ω := (PowerlessRelativeClassOmegaAbsolute.omega_l
    (hBase := hBase) ω).mpr (hωEq.symm ▸ K.omega_spec)
  refine ⟨e, t₁, t₂, t₃, T, N, F, heC, ht₁C, ht₂C, ht₃C, hTC, hNC, hFC, hStatic, ?_⟩
  intro A hAC
  let η : Env 𝒩 [] parameters_m :=
    (((((((Env.empty.pushFree t₃).pushFree t₂).pushFree t₁).pushFree A).pushFree T).pushFree N).pushFree e).pushFree ω
  let w : Term ℒ [] parameters_m .set := .fvar .here
  let z : Term ℒ [] parameters_m .set := .fvar (.there .here)
  let n : Term ℒ [] parameters_m .set := .fvar (.there (.there .here))
  let t : Term ℒ [] parameters_m .set := .fvar (.there (.there (.there .here)))
  let a : Term ℒ [] parameters_m .set := .fvar (.there (.there (.there (.there .here))))
  let x : Term ℒ [] parameters_m .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let y : Term ℒ [] parameters_m .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let d : Term ℒ [] parameters_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  have hParams : ∀ s (v : Variable parameters_m s), mem_l hℳ (η.freeVal v).val C := by
    intro s v
    cases v with
    | here => exact hωC
    | there v => cases v with
      | here => exact heC
      | there v => cases v with
        | here => exact hNC
        | there v => cases v with
          | here => exact hTC
          | there v => cases v with
            | here => exact hAC
            | there v => cases v with
              | here => exact ht₁C
              | there v => cases v with
                | here => exact ht₂C
                | there v => cases v with
                  | here => exact ht₃C
                  | there v => nomatch v
  exact PowerlessRelativeCofinalSatisfaction.exists_l (F := F) hC hLimit hCofinal
    η w z n t a x y d hParams hω hFC hStatic

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalSatisfactionForDomain
