import BMSConstructibleBridge.PowerlessRelativeClassLegacyRows
import BMSConstructibleBridge.PowerlessRelativeClassLegacyRowFamily

/-! # 原始 Def 呈现的精确 Class 认同

完整旧求值保持性、数值图与指定实际枚举仍显式输入。统一关系图和精确
Class 行族在证明中取得；它们满足原 presentation 的全部 raw collection
字段，故原非空 MemberDef 对象自身属于 Class，而不只是包含在 Class 母集中。

没有修改原 Def、原数域或原推导核，也不把原实数选择为 Type 数据。
本模块完成有证书的语义认同；无条件证书装配、空母集分支、统一历史和
最终原 Z₂ Derives 仍分别处理，不能据此宣称整个形式化完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyMemberDef

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderQuotient (mem_l)
open SecondOrderModel (num_l set_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase
local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ) {ω e A N P F G Seq Idx U Sat : type_l hℳ B}
    (hΩ : omega_l (ℳ := ClassModel) ω) (hω : ω.val = K.omega)
    (he : e.val = code_l K (SecondOrderModel.zero_l ℳ))
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) K.omega K.omega N.val)
    {E C V D Q₀ R₀ T F₀ : set_l ℳ}
    (hPnumeric : ∀ n m, value_l (ℳ := RawModel) P.val (code_l K n) (code_l K m) ↔
      SecondOrderPairing.relation_l E n m)
    (hFnumeric : ∀ n m, value_l (ℳ := RawModel) F.val (code_l K n) (code_l K m) ↔
      SecondOrderPairing.relation_l C n m)
    (hGnumeric : ∀ n m, value_l (ℳ := RawModel) G.val (code_l K n) (code_l K m) ↔
      SecondOrderPairing.relation_l V n m)
    (hE : SecondOrderBinaryPowers.spec_l E) (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) (hD : ∀ v, SecondOrderModel.mem_l v D)
    (hFamily : SecondOrderDefinableFamily.spec_l E D T F₀)
    (hEvaluation : SecondOrderEvaluationEquations.spec_l E D Q₀ R₀ T)
    (hPreservation : ∀ n, PowerlessLegacyEvaluationRow.row_l K B A.val U.val Sat.val E C T n)
    (hU : map_l (ℳ := RawModel) U.val K.omega A.val)
    (hOnto : ∀ x, mem_l hℳ x A.val → ∃ v, value_l (ℳ := RawModel) U.val (code_l K v) x)
    (hEquality : ∀ i j x y, value_l (ℳ := RawModel) U.val (code_l K i) x →
      value_l (ℳ := RawModel) U.val (code_l K j) y → (SecondOrderPairing.relation_l Q₀ i j ↔ x = y))
    (hMembership : ∀ i j x y, value_l (ℳ := RawModel) U.val (code_l K i) x →
      value_l (ℳ := RawModel) U.val (code_l K j) y →
        (SecondOrderPairing.relation_l R₀ i j ↔ mem_l hℳ x y))
    (hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := ClassModel) ω A Seq)
    (hIdx : ∀ t : type_l hℳ B, mem_l hℳ t.val Idx.val ↔
      ∃ q f : type_l hℳ B, mem_l hℳ q.val ω.val ∧ mem_l hℳ f.val Seq.val ∧
        ordered_l (ℳ := ClassModel) q f t) :
    ∃ Y : type_l hℳ B,
      SecondOrderEnumeratedMemberDef.presentation_l K A.val Y.val U.val V E D Q₀ R₀ T F₀ ∧
        SecondOrderMemberDef.nonempty_l hℳ A.val Y.val := by
  obtain ⟨I, hI⟩ := PowerlessRelativeClassLegacyLegalIndices.exists_l
    (hBase := hBase) K hω hN hPnumeric hGnumeric
  obtain ⟨Q, hQ⟩ := PowerlessRelativeClassLegacyRows.exists_l (hBase := hBase)
    K hΩ hω he hN hPnumeric hFnumeric hE hV hC hD hFamily hPreservation hU hOnto hSeq hIdx hI
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassLegacyRowFamily.exists_l (hBase := hBase) K hU hI hQ
  have hOriginalU : SecondOrderFunctionObjects.map_l hℳ U.val K.omega A.val := hU
  have hPresentation :
      SecondOrderEnumeratedMemberDef.presentation_l K A.val Y.val U.val V E D Q₀ R₀ T F₀ := by
    refine ⟨hOriginalU, ?_, hV, hE, hD, hEquality, hMembership, hEvaluation, hFamily, hY⟩
    intro x hx
    obtain ⟨v, hv⟩ := hOnto x hx
    exact ⟨code_l K v, (numberCode_l K v).property, hv⟩
  exact ⟨Y, hPresentation, SecondOrderEnumeratedMemberDef.represents_l K hPresentation⟩

/-- 对已得到的精确 Class 原呈现，原 Def 唯一性认同任意原商见证。 -/
theorem class_l {A Y : type_l hℳ B} {H : SecondOrderQuotient.type_l hℳ}
    (hY : SecondOrderMemberDef.nonempty_l hℳ A.val Y.val)
    (hH : SecondOrderMemberDef.spec_l hℳ A.val H) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B H := by
  have hEq := SecondOrderMemberDef.unique_l hℳ hH (Or.inr hY)
  exact hEq.symm ▸ Y.property

#print axioms exists_l
#print axioms class_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyMemberDef
