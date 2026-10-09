import BMSConstructibleBridge.PowerlessRelativeLimitSatisfaction
import BMSConstructibleBridge.PowerlessRelativeClassTriangularSpecification
import BMSConstructibleBridge.PowerlessRelativeClassValidityAbsolute
import BMSConstructibleBridge.PowerlessSatisfactionExistenceSyntax

/-! # 从纯静态规格取得指定层内的完整 Sat 图

公开前提不再出现原算术编码 K、关系 V 或逐码三角读数。给定的 T、N、F
由纯规格恢复实际读数，证明中选取的编码和辅助图不替换这些参数。
层关系仍是原商环境的层关系；正文 Sat 仍在相对类中解释。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSatisfactionStatic

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    {B γ D β C : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    (hD : level_l hℳ B γ D) (hInner : limit_l hℳ γ)
    (hC : level_l hℳ B β C) (hOuter : limit_l hℳ β) (hEarlier : mem_l hℳ γ β)
    {Δ : SortContext ℒ} (η : Env (structure_l hℳ B hBase) [] Δ)
    (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v).val D)
    (hω : omega_l (ℳ := structure_l hℳ B hBase) (ω.eval η))
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase)
      (ω.eval η) (A.eval η) (S.eval η))
    {F : type_l hℳ B} (hFC : mem_l hℳ F.val C)
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := structure_l hℳ B hBase)
      (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (T.eval η) (N.eval η) F) :
    ∃ R : type_l hℳ B, mem_l hℳ R.val C ∧
      PowerlessSatisfactionSpecification.spec_l (𝒩 := structure_l hℳ B hBase)
        (ω.eval η) (A.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (T.eval η) F R := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) (ω.eval η)).mp hω) K.omega_spec
  have heEq := SecondOrderQuotient.ext_l hℳ _ _ (fun x => iff_of_false
    ((PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) (e.eval η)).mp hStatic.1.1 x)
    (PowerlessBMSQuotientSuccessor.zero_l K x))
  have hN := PowerlessRelativeClassSequenceAbsolute.spec_l hω hStatic.2.2.2.1
  have hN' : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega (N.eval η).val := by simpa only [hωEq] using hN
  have hMap : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) (T.eval η).val K.omega K.omega := by
    simpa only [ThirdOrderSemantics.map_l, ThirdOrderSemantics.member_l, ThirdOrderSemantics.value_l,
      ThirdOrderSemantics.ordered_l, ThirdOrderSemantics.pair_l, SecondOrderQuotient.structure_l,
      SecondOrderFunctionObjects.map_l, SecondOrderFunctionObjects.value_l,
      SecondOrderPairObjects.ordered_l, SecondOrderPairObjects.pair_l, hωEq]
      using (PowerlessRelativeClassFunctionAbsolute.map_l
      (hBase := hBase) (T.eval η) (ω.eval η) (ω.eval η)).mp hStatic.2.1.1
  have hSpec := PowerlessRelativeClassTriangularSpecification.spec_l
    (N := N.eval η) K hωEq heEq hN' hStatic.2.1
  obtain ⟨V, hV, _⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
  have hF := PowerlessRelativeClassValidityAbsolute.reading_l K hω hωEq heEq hStatic.1
    hMap hSpec hV hN' hStatic.2.2.2.2
  obtain ⟨_, R, _, hRC, _, _, hSat⟩ := PowerlessRelativeLimitSatisfaction.exists_l K
    hD hInner hC hOuter hEarlier η ω e N T A S t₁ t₂ t₃ hParams hωEq heEq hStatic.1
    hStatic.2.1 hMap hSpec hN (PowerlessRelativeClassSequenceAbsolute.spec_l hω hS) hV hFC hF
  exact ⟨R, hRC, hSat⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSatisfactionStatic
