import BMSConstructibleBridge.SecondOrderComparisonNativeLocal
import BMSConstructibleBridge.SecondOrderPointwiseOperator
import BMSConstructibleBridge.SecondOrderWellFoundedRecursion

/-! # 实际原比较正文的内部递归历史

算子由同一原语言逐行正文通过二元理解装配；递归关系是实际序数根的规范
前驱实数。内部良基、传递和反自反均由该根证明，不要求模型外部良基。
递归历史的存在唯一性与其行正文还不是各行良序及最终 BMS 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonNativeRecursion

open Logic FirstOrder SecondOrderSyntax ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderComparisonNativeRow (parameters_l environment_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

def operator_m : Formula signature_m [.set, .set]
    (.set :: GraphTranslation.context_m SecondOrderComparisonNativeRow.context_m) :=
  SecondOrderPointwiseOperator.formula_m SecondOrderComparisonNativeRow.formula_m

theorem pure_m : SecondOrderArithmetic.language_m operator_m = true :=
  SecondOrderPointwiseOperator.pure_m _ SecondOrderComparisonNativeRow.pure_m

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def relation_l (K : source_coding_l hℳ) (p : parameters_l ℳ) (H U : SecondOrderModel.set_l ℳ) : Prop :=
  SecondOrderSetOperator.relation_l operator_m (environment_l K p) H U

theorem total_l (K : source_coding_l hℳ) (p : parameters_l ℳ) :
    ∀ H, ∃ U, relation_l K p H U :=
  SecondOrderPointwiseOperator.total_l hℳ _ SecondOrderComparisonNativeRow.pure_m (environment_l K p)

/-- 以实际序数根填满内部递归条件，不保留任意关系的良基占位假设。 -/
theorem exists_l (K : source_coding_l hℳ) (p : parameters_l ℳ)
    (hω : SecondOrderQuotient.mk_l hℳ p.ω = K.omega)
    (he : SecondOrderQuotient.mk_l hℳ p.e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (A : SecondOrderGraph.code_l ℳ)
    (hα : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)
      (SecondOrderQuotient.mk_l hℳ A))
    {Q D R : SecondOrderModel.set_l ℳ} (h : SecondOrderOrdinalHierarchy.presentation_l A Q D R)
    (hJ : map_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.J) (SecondOrderQuotient.mk_l hℳ p.I)
      (SecondOrderQuotient.mk_l hℳ A))
    (hI : subset_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.I) K.omega)
    (hJRead : ∀ x y, value_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.J) x y ↔
      ∃ n, ∃ hn : SecondOrderModel.mem_l n D, x = (numberCode_l K n).val ∧
        y = SecondOrderQuotient.mk_l hℳ (SecondOrderRootCorrespondence.member_code_l hℳ A h n hn)) :
    ∃! S, relation_l K p S S := by
  have hR := SecondOrderStageIndexPredecessors.relation_l K A h hJRead
  apply SecondOrderWellFoundedRecursion.exists_l hℳ operator_m pure_m (environment_l K p) R
  · exact SecondOrderRootOrdinalRelation.wf_l hℳ A h.equality h.representatives h.predecessors
  · exact SecondOrderRootOrdinalRelation.transitive_l hℳ A hα h.equality h.representatives h.predecessors
  · exact SecondOrderRootOrdinalRelation.irreflexive_l hℳ A h.equality h.representatives h.predecessors
  · apply SecondOrderPointwiseOperator.local_l SecondOrderComparisonNativeRow.formula_m (environment_l K p) R
    intro H H' n hPast W
    exact SecondOrderComparisonNativeLocal.local_l K p hω he hJ hI R hR H H' n W hPast
  · exact total_l K p

/-- 真正逐行总唯一时，不动点的切片恰好满足同一原正文。 -/
theorem rows_l (K : source_coding_l hℳ) (p : parameters_l ℳ) {S : SecondOrderModel.set_l ℳ}
    (hS : relation_l K p S S)
    (hTotal : ∀ n, ∃! W : SecondOrderModel.set_l ℳ,
      SecondOrderComparisonNativeRow.formula_m.satisfies
        ((((environment_l K p).pushFree S).pushFree n).pushFree W)) :
    ∀ n W, SecondOrderSections.spec_l S n W ↔
      SecondOrderComparisonNativeRow.formula_m.satisfies
        ((((environment_l K p).pushFree S).pushFree n).pushFree W) := by
  intro n W
  obtain ⟨X, hX, hSection⟩ := SecondOrderPointwiseOperator.rows_l
    SecondOrderComparisonNativeRow.formula_m (environment_l K p) hS hTotal n
  constructor
  · intro hW
    have hWX := SecondOrderSections.unique_l hℳ hW hSection
    exact hWX.symm ▸ hX
  · intro hW
    obtain ⟨Y, _, hOnly⟩ := hTotal n
    have hWX : W = X := (hOnly W hW).trans (hOnly X hX).symm
    exact hWX.symm ▸ hSection

#print axioms total_l
#print axioms exists_l
#print axioms rows_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonNativeRecursion
