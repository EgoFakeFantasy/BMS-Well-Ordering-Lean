import BMSConstructibleBridge.PowerlessEvaluationClauseBounded
import BMSConstructibleBridge.PowerlessEvaluationStep
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparation

/-! # 固定非零极限层内的原求值列

将纯 Δ₀ 矩阵分离所得集合识别为原局部求值算子的实际输出。历史与所有
有限参数必须属于指定层 C；结论仍属于同一 C，成员规格覆盖全部原商对象。
这里只完成一个求值步，并未构造所有内部公式码的有限历史或统一 Sat 图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationStep

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

/-- 赋值是新自由变量，其余参数来自同一旧环境。 -/
def matrix_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ H n : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: Δ) :=
  PowerlessEvaluationClauseBounded.formula_m
    (ω.weakenFree SetTheory.SetSort.set) (e.weakenFree SetTheory.SetSort.set)
    (N.weakenFree SetTheory.SetSort.set) (T.weakenFree SetTheory.SetSort.set)
    (A.weakenFree SetTheory.SetSort.set) (S.weakenFree SetTheory.SetSort.set)
    (t₁.weakenFree SetTheory.SetSort.set) (t₂.weakenFree SetTheory.SetSort.set)
    (t₃.weakenFree SetTheory.SetSort.set) (H.weakenFree SetTheory.SetSort.set)
    (n.weakenFree SetTheory.SetSort.set) (.fvar .here)

theorem matrix_delta_l {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ H n : Term ℒ [] Δ .set) :
    Formula.IsDelta0 membershipLevyBound (matrix_m ω e N T A S t₁ t₂ t₃ H n) :=
  PowerlessEvaluationClauseBounded.delta_l _ _ _ _ _ _ _ _ _ _ _ _

theorem matrix_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env 𝒩 [] Δ) (ω e N T A S t₁ t₂ t₃ H n : Term ℒ [] Δ .set) (f : carrier_l 𝒩) :
    (matrix_m ω e N T A S t₁ t₂ t₃ H n).satisfies (η.pushFree f) ↔
      PowerlessEvaluationClauseBounded.holds_l (ω.eval η) (e.eval η) (N.eval η) (T.eval η)
        (A.eval η) (S.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (H.eval η) (n.eval η) f := by
  simp only [matrix_m, PowerlessEvaluationClauseBounded.formula_l, Term.eval_weakenFree, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β C : type_l hℳ}

theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (ω e N T A S t₁ t₂ t₃ H n : Term ℒ [] Δ .set)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C)
    (hSC : mem_l hℳ (S.eval η) C)
    (hω : omega_l (ℳ := SecondOrderQuotient.structure_l hℳ) (ω.eval η))
    (he : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) (e.eval η))
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (ω.eval η) (ω.eval η) (N.eval η))
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) (T.eval η) (ω.eval η) (ω.eval η))
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (ω.eval η) (A.eval η) (S.eval η)) :
    ∃ Y, mem_l hℳ Y C ∧ PowerlessEvaluationStep.step_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (ω.eval η) (e.eval η) (T.eval η) (A.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
      (S.eval η) (H.eval η) (n.eval η) Y := by
  obtain ⟨Y, hYC, hY⟩ := PowerlessRelativeLimitDeltaSeparation.exists_l hBase hLimit hC
    (matrix_delta_l ω e N T A S t₁ t₂ t₃ H n) η hSC hParams
  refine ⟨Y, hYC, fun f => (hY f).trans (and_congr_right fun hf => ?_)⟩
  exact (matrix_formula_l η ω e N T A S t₁ t₂ t₃ H n f).trans
    (PowerlessEvaluationClauseBounded.guarded_iff_l hω he hN hT hS hf)

theorem unique_l {ω e T A t₁ t₂ t₃ S H n Y Z : type_l hℳ}
    (hY : PowerlessEvaluationStep.step_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      ω e T A t₁ t₂ t₃ S H n Y)
    (hZ : PowerlessEvaluationStep.step_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      ω e T A t₁ t₂ t₃ S H n Z) : Y = Z :=
  SecondOrderQuotient.ext_l hℳ Y Z (fun f => (hY f).trans (hZ f).symm)

#print axioms matrix_delta_l
#print axioms exists_l
#print axioms unique_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationStep
