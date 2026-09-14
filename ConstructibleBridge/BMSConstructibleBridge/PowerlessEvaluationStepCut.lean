import BMSConstructibleBridge.PowerlessEvaluationStepAbsolute
import BMSConstructibleBridge.PowerlessOperatorClosure

/-!
# 求值真值集合的定义子集成员性

用原局部求值公式定义候选赋值的成员条件。Y 不出现在参数环境中，
其域内子集性由 S 的成员性推出，避免先假定 Y 属于输入域的循环。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationStepCut

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem operator_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {B D Y : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}
    (hBT : PowerlessNaturalOrder.transitive_l B) {ω e T A t₁ t₂ t₃ S H n : type_l B}
    (hω : omega_l ω.val) (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hD : PowerlessEvaluationOperator.operator_l ω.val e.val T.val t₁.val t₂.val t₃.val B D)
    (hC : ∀ f : type_l B,
      PowerlessEvaluationClause.clause_l (ℳ := structure_l B hB) ω e T A t₁ t₂ t₃ H n f ↔
        PowerlessEvaluationClause.clause_l ω.val e.val T.val A.val t₁.val t₂.val t₃.val H.val n.val f.val)
    (hY : PowerlessEvaluationStep.step_l ω.val e.val T.val A.val t₁.val t₂.val t₃.val S.val H.val n.val Y) :
    member_l ℳ Y D := by
  let η : Env (structure_l B hB) [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set] [] :=
    ((((((((((Env.empty (σ := ℒ) (M := structure_l B hB)).pushBound
      (sort := SetTheory.SetSort.set) n).pushBound H).pushBound S).pushBound t₃).pushBound t₂).pushBound t₁).pushBound
      A).pushBound T).pushBound e).pushBound ω
  let φ : Formula ℒ [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] [] :=
    .conj (SecondOrderObjectSyntax.member_m (.bvar .here)
      (.bvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
      (PowerlessEvaluationClause.clause_m
        (.bvar (.there .here))
        (.bvar (.there (.there .here)))
        (.bvar (.there (.there (.there .here))))
        (.bvar (.there (.there (.there (.there .here)))))
        (.bvar (.there (.there (.there (.there (.there .here))))))
        (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
        (.bvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
        (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
        (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
        (.bvar .here))
  apply PowerlessOperatorClosure.specified_l hℳ hω ht hT hD φ η
  intro f
  have h₀ (hf : member_l ℳ f B) : φ.satisfies (η.pushBound ⟨f, hf⟩) ↔ member_l ℳ f Y := by
    simp only [φ, Formula.satisfies, PowerlessEvaluationClause.clause_formula_l]
    change (member_l ℳ f S.val ∧ PowerlessEvaluationClause.clause_l
      (ℳ := structure_l B hB) ω e T A t₁ t₂ t₃ H n ⟨f, hf⟩) ↔ member_l ℳ f Y
    exact (and_congr Iff.rfl (hC ⟨f, hf⟩)).trans (hY f).symm
  constructor
  · intro hf
    have hfB := hBT S.val f S.property ((hY f).mp hf).1
    exact ⟨hfB, (h₀ hfB).mpr hf⟩
  · rintro ⟨hf, h⟩
    exact (h₀ hf).mp h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationStepCut
