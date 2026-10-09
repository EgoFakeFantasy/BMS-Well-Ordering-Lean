import BMSConstructibleBridge.PowerlessRelativeLimitRelationalGraph
import BMSConstructibleBridge.PowerlessRelativeLimitEvaluationHistoryBound
import BMSConstructibleBridge.PowerlessFiniteEvaluationRelationEquations
import BMSConstructibleBridge.PowerlessFiniteEvaluationZero
import BMSConstructibleBridge.SecondOrderFiniteSequencesDerives

/-! # 指定外层中的实际有限求值图

历史母层 D 本身作为候选历史界；原商有限参数属于给定外层 C，即可在
该层内构造 ω × S 上的实际图。若 D 是含实际 ω 的非零极限层，则用
环境中的全有限序列集比较查询，取得同一图的四分支方程，不要求该序列集入层。
这里只给求值图及其方程；合法性和精确赋值长度的过滤由后续模块完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationGraph

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 先固定外层及其全部自由参数，所得图覆盖全部原商坐标。 -/
theorem exists_l {B β C : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (D ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C) :
    ∃ G, mem_l hℳ G C ∧
      PowerlessFiniteEvaluationRelation.spec_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        (D.eval η) (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (A.eval η) (S.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (D.eval η) G := by
  have hTerm (t : Term ℒ [] Δ .set) : mem_l hℳ (t.eval η) C := by
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact hParams _ v
    | .app f _ => nomatch f
  obtain ⟨G, hGC, hG⟩ := PowerlessRelativeLimitRelationalGraph.exists_l hBase hLimit hC
    (PowerlessFiniteEvaluationQueryGraph.matrix_delta_l D ω e N T A S t₁ t₂ t₃ D)
    η (hTerm ω) (hTerm S) hParams
  refine ⟨G, hGC, fun n f => ?_⟩
  exact (hG n f).trans (and_congr Iff.rfl (and_congr Iff.rfl
    (PowerlessFiniteEvaluationQueryGraph.matrix_formula_l η D ω e N T A S t₁ t₂ t₃ D n f)))

/-- 用实际序列集恢复既有查询方程；无需该集合属于母层或外层。 -/
theorem equations_l (K : source_coding_l hℳ)
    {B γ D e N T A S t₁ t₂ t₃ G : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ γ) (hD : level_l hℳ B γ D)
    (hωD : mem_l hℳ K.omega D)
    (hS : PowerlessFiniteSequencesSyntax.spec_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega A S)
    (hEquation : PowerlessFiniteEvaluationEquations.equations_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) D K.omega e N T A S t₁ t₂ t₃)
    (hG : PowerlessFiniteEvaluationRelation.spec_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) D K.omega e N T A S t₁ t₂ t₃ D G) :
    PowerlessFiniteEvaluationRelationEquations.equations_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega e T A S t₁ t₂ t₃ G := by
  obtain ⟨Q, hQ⟩ := SecondOrderFiniteSequencesDerives.exists_l hℳ K.omega K.omega_spec D
  have hGQ : PowerlessFiniteEvaluationRelation.spec_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) D K.omega e N T A S t₁ t₂ t₃ Q G := by
    intro n f
    exact (hG n f).trans (and_congr Iff.rfl (and_congr Iff.rfl
      (PowerlessRelativeLimitEvaluationHistoryBound.query_iff_l
        K hBase hLimit hD hωD hQ).symm))
  exact PowerlessFiniteEvaluationRelationEquations.equations_of_query_l hGQ hS hQ hEquation

/-- 零码恒假直接读取同一图的有限历史，不额外假定递归方程。 -/
theorem zero_l {D ω e N T A S t₁ t₂ t₃ G : type_l hℳ}
    (hω : omega_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω)
    (he : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) e)
    (hN : PowerlessFiniteSequencesSyntax.spec_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) ω ω N)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T ω ω)
    (hS : PowerlessFiniteSequencesSyntax.spec_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) ω A S)
    (hG : PowerlessFiniteEvaluationRelation.spec_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) D ω e N T A S t₁ t₂ t₃ D G)
    (f : type_l hℳ) : ¬value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G e f :=
  PowerlessFiniteEvaluationZero.relation_l hω he hN hT hS hG f

#print axioms exists_l
#print axioms equations_l
#print axioms zero_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationGraph
