import BMSConstructibleBridge.PowerlessSatisfactionBounded
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph

/-! # 合法性守卫求值的类内集合图

在 ω×S 上分离有界查询，取得覆盖全部原商坐标的实际集合图和原 Z₂ 构图
推导。F、G 的正确性仍需由实际编码和求值系统提供；不把图存在当作完整
语义正确性，更不把它当作最终 BMS 良序推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionGraph

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def matrix_m {Δ : SortContext ℒ} (ω A S F G : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  let w (t : Term ℒ [] Δ .set) := (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set
  PowerlessSatisfactionBounded.formula_m (w ω) (w A) (w S) (w F) (w G)
    (.fvar .here) (.fvar (.there .here))

theorem matrix_delta_l {Δ : SortContext ℒ} (ω A S F G : Term ℒ [] Δ .set) :
    Formula.IsDelta0 membershipLevyBound (matrix_m ω A S F G) :=
  PowerlessSatisfactionBounded.delta_l _ _ _ _ _ _ _

theorem matrix_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env 𝒩 [] Δ) (ω A S F G : Term ℒ [] Δ .set) (c f : carrier_l 𝒩) :
    (matrix_m ω A S F G).satisfies ((η.pushFree f).pushFree c) ↔
      PowerlessSatisfactionBounded.holds_l (ω.eval η) (A.eval η) (S.eval η) (F.eval η) (G.eval η) c f := by
  simp only [matrix_m, PowerlessSatisfactionBounded.formula_l, Term.eval_weakenFree,
    Term.eval, Env.pushFree_here, Env.pushFree_there]

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    (ω A S F G : type_l hℳ B) : ∃ R : type_l hℳ B,
      ∀ c f : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val c f ↔
          PowerlessSatisfactionBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
            ω.val A.val S.val F.val G.val c f := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set] :=
    (((((Env.empty).pushFree G).pushFree F).pushFree S).pushFree A).pushFree ω
  let w : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let a : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let s : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let t : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let g : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  obtain ⟨R, hR⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l (matrix_delta_l w a s t g) η ω S
  refine ⟨R, fun c f => ?_⟩
  have h := (hR c f).trans (and_congr Iff.rfl (and_congr Iff.rfl
    (matrix_formula_l (PowerlessRelativeClassRelativization.env_l η) w a s t g c f)))
  change value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val c f ↔
    mem_l hℳ c ω.val ∧ mem_l hℳ f S.val ∧
      PowerlessSatisfactionBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val A.val S.val F.val G.val c f at h
  exact h.trans ⟨And.right ∘ And.right, fun hQuery => ⟨hQuery.1, hQuery.2.1, hQuery⟩⟩

def sentence_m {Δ : SortContext ℒ} (ω A S F G : Term ℒ [] Δ .set) : Sentence ℒ :=
  PowerlessRelativeClassRelativization.guarded_m
    (SecondOrderDefinableRelationImageDerives.sentence_m (matrix_m ω A S F G))

theorem derives_m {Δ : SortContext ℒ} (ω A S F G : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω A S F G)) :=
  PowerlessRelativeClassRelation.derives_m (matrix_delta_l ω A S F G)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionGraph
