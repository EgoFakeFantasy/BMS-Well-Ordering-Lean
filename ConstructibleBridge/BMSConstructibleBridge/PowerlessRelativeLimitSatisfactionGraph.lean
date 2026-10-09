import BMSConstructibleBridge.PowerlessRelativeLimitRelationalGraphDerives
import BMSConstructibleBridge.PowerlessSatisfactionGraph

/-! # 指定层内的合法性守卫求值过滤

ω、域、赋值集及实际 F/G 全部属于指定非零极限层时，过滤后的 R 也属于
该层。这里只使用有界查询；F/G 的语义正确性在系统装配时另行消费。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSatisfactionGraph

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β C : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {ω A S F G : type_l hℳ} (hωC : mem_l hℳ ω C) (hAC : mem_l hℳ A C)
    (hSC : mem_l hℳ S C) (hFC : mem_l hℳ F C) (hGC : mem_l hℳ G C) :
    ∃ R, mem_l hℳ R C ∧ ∀ c f : type_l hℳ,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R c f ↔
        PowerlessSatisfactionBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) ω A S F G c f := by
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set, .set, .set] :=
    (((((Env.empty).pushFree G).pushFree F).pushFree S).pushFree A).pushFree ω
  let w : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let a : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let s : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let t : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let g : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  have hParams : ∀ q (v : Variable [SetTheory.SetSort.set, .set, .set, .set, .set] q),
      mem_l hℳ (η.freeVal v) C := by
    intro q v
    cases v with
    | here => exact hωC
    | there v => cases v with
      | here => exact hAC
      | there v => cases v with
        | here => exact hSC
        | there v => cases v with
          | here => exact hFC
          | there v => cases v with
            | here => exact hGC
            | there v => nomatch v
  obtain ⟨R, hRC, hR⟩ := PowerlessRelativeLimitRelationalGraph.exists_l hBase hLimit hC
    (PowerlessSatisfactionGraph.matrix_delta_l w a s t g) η hωC hSC hParams
  refine ⟨R, hRC, fun c f => ?_⟩
  have h := (hR c f).trans (and_congr Iff.rfl (and_congr Iff.rfl
    (PowerlessSatisfactionGraph.matrix_formula_l η w a s t g c f)))
  change value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R c f ↔
    mem_l hℳ c ω ∧ mem_l hℳ f S ∧
      PowerlessSatisfactionBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) ω A S F G c f at h
  exact h.trans ⟨And.right ∘ And.right, fun hQuery => ⟨hQuery.1, hQuery.2.1, hQuery⟩⟩

/-- 固定层构图模式涵盖该实际有界矩阵；取母集 ω 和 S 即得过滤图。 -/
theorem derives_m {Δ : SortContext ℒ} (ω A S F G : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m
      (PowerlessRelativeLimitRelationalGraphDerives.sentence_m (PowerlessSatisfactionGraph.matrix_m ω A S F G))) :=
  PowerlessRelativeLimitRelationalGraphDerives.derives_m (PowerlessSatisfactionGraph.matrix_delta_l ω A S F G)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSatisfactionGraph
