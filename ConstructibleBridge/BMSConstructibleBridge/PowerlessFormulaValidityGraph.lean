import BMSConstructibleBridge.PowerlessFormulaValidityBounded
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph

/-! # 有界合法性查询的类内集合图

对 ω×ω 使用实际 Δ₀ 查询分离，图规格覆盖全部原商坐标。此处构图不要求
编码参数正确；与原内部合法性关系的识别另行消费实际编码规格。
构图模式同时给出纯集合对象句及其原 Z₂ 翻译的正式推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaValidityGraph

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def matrix_m {Δ : SortContext ℒ} (ω e N T t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  let w (t : Term ℒ [] Δ .set) := (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set
  PowerlessFormulaValidityBounded.query_m (w ω) (w e) (w N) (w T) (w t₁) (w t₂) (w t₃)
    (.fvar .here) (.fvar (.there .here))

theorem matrix_delta_l {Δ : SortContext ℒ} (ω e N T t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    Formula.IsDelta0 membershipLevyBound (matrix_m ω e N T t₁ t₂ t₃) :=
  PowerlessFormulaValidityBounded.query_delta_l _ _ _ _ _ _ _ _ _

theorem matrix_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env 𝒩 [] Δ) (ω e N T t₁ t₂ t₃ : Term ℒ [] Δ .set) (c l : carrier_l 𝒩) :
    (matrix_m ω e N T t₁ t₂ t₃).satisfies ((η.pushFree l).pushFree c) ↔
      PowerlessFormulaValidityBounded.query_l (ω.eval η) (e.eval η) (N.eval η) (T.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) c l := by
  simp only [matrix_m, PowerlessFormulaValidityBounded.query_formula_l, Term.eval_weakenFree,
    Term.eval, Env.pushFree_here, Env.pushFree_there]

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    (ω e N T t₁ t₂ t₃ : type_l hℳ B) : ∃ G : type_l hℳ B,
      ∀ c l : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G.val c l ↔
          PowerlessFormulaValidityBounded.query_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
            ω.val e.val N.val T.val t₁.val t₂.val t₃.val c l := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set, .set, .set] :=
    (((((((Env.empty).pushFree t₃).pushFree t₂).pushFree t₁).pushFree T).pushFree N).pushFree e).pushFree ω
  let w : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let z : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let s : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let t : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let a : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let b : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let d : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  obtain ⟨G, hG⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l (matrix_delta_l w z s t a b d) η ω ω
  refine ⟨G, fun c l => ?_⟩
  have h := (hG c l).trans (and_congr Iff.rfl (and_congr Iff.rfl
    (matrix_formula_l (PowerlessRelativeClassRelativization.env_l η) w z s t a b d c l)))
  change value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G.val c l ↔
    mem_l hℳ c ω.val ∧ mem_l hℳ l ω.val ∧
      PowerlessFormulaValidityBounded.query_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val e.val N.val T.val t₁.val t₂.val t₃.val c l at h
  exact h.trans ⟨And.right ∘ And.right, fun hQuery => ⟨hQuery.1, hQuery.2.1, hQuery⟩⟩

def sentence_m {Δ : SortContext ℒ} (ω e N T t₁ t₂ t₃ : Term ℒ [] Δ .set) : Sentence ℒ :=
  PowerlessRelativeClassRelativization.guarded_m
    (SecondOrderDefinableRelationImageDerives.sentence_m (matrix_m ω e N T t₁ t₂ t₃))

theorem derives_m {Δ : SortContext ℒ} (ω e N T t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω e N T t₁ t₂ t₃)) :=
  PowerlessRelativeClassRelation.derives_m (matrix_delta_l ω e N T t₁ t₂ t₃)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaValidityGraph
