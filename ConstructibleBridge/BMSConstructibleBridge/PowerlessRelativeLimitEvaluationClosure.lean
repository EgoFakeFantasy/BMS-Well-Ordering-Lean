import BMSConstructibleBridge.PowerlessRelativeLimitEvaluationGraph
import BMSConstructibleBridge.PowerlessRelativeClassEvaluationClosure

/-! # 严格先前层中的历史与指定外层内的求值图

静态参数先属于内层 D，再将 D 自身加入外层构图环境。内部历史存在性
实际推出递归方程；结论不再假定 hEquation，也不要求 Seq(ω,D) 入层。
早期非零极限层及其参数成员条件仍显式保留，不由外层极限性冒充。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationClosure

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    (K : source_coding_l hℳ) {B γ D β C : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hD : level_l hℳ B γ D) (hInner : limit_l hℳ γ)
    (hC : level_l hℳ B β C) (hOuter : limit_l hℳ β) (hEarlier : mem_l hℳ γ β)
    {Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) D)
    (hωEq : ω.eval η = K.omega)
    (he : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) (e.eval η))
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (ω.eval η) (ω.eval η) (N.eval η))
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) (T.eval η) (ω.eval η) (ω.eval η))
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (ω.eval η) (A.eval η) (S.eval η))
    (hBounds : ∀ t a b n, PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (ω.eval η) (e.eval η) (T.eval η) t a b n → mem_l hℳ a n ∧ mem_l hℳ b n)
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η))
    (hInjective : PowerlessRelativeClassConstructorInjective.injective_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      (ω.eval η) (e.eval η) (T.eval η)) :
    ∃ G, mem_l hℳ G C ∧
      PowerlessFiniteEvaluationRelation.spec_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        D (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (A.eval η) (S.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) D G ∧
      PowerlessFiniteEvaluationRelationEquations.equations_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        (ω.eval η) (e.eval η) (T.eval η) (A.eval η) (S.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) G ∧
      ∀ f, ¬value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G (e.eval η) f := by
  have hTerm (t : Term ℒ [] Δ .set) : mem_l hℳ (t.eval η) D := by
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact hParams _ v
    | .app f _ => nomatch f
  have hω : omega_l (ℳ := SecondOrderQuotient.structure_l hℳ) (ω.eval η) :=
    hωEq ▸ K.omega_spec
  have hEquation := PowerlessRelativeClassEvaluationClosure.equations_l η ω e N T A S t₁ t₂ t₃
    hBase hD hInner hParams (hTerm S) hω (hTerm ω) he hN hT hS hBounds hTags hInjective
  let ξ := η.pushFree (sort := SetTheory.SetSort.set) D
  let w (t : Term ℒ [] Δ .set) := t.weakenFree SetTheory.SetSort.set
  have hParams' : ∀ s (v : Variable (.set :: Δ) s), mem_l hℳ (ξ.freeVal v) C := by
    intro s v
    cases v with
    | here => exact PowerlessRelativeLevelClosure.members_l hℳ hBase hEarlier hD hC
    | there v => exact PowerlessRelativeLevelClosure.subset_l hℳ hBase hEarlier hD hC _ (hParams _ v)
  obtain ⟨G, hGC, hG⟩ := PowerlessRelativeLimitEvaluationGraph.exists_l hBase hOuter hC ξ
    (.fvar .here) (w ω) (w e) (w N) (w T) (w A) (w S) (w t₁) (w t₂) (w t₃) hParams'
  have hGraph : PowerlessFiniteEvaluationRelation.spec_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      D (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (A.eval η) (S.eval η)
      (t₁.eval η) (t₂.eval η) (t₃.eval η) D G := by
    simpa only [w, ξ, Term.eval_weakenFree, Term.eval, Env.pushFree_here] using hG
  refine ⟨G, hGC, hGraph, ?_, PowerlessRelativeLimitEvaluationGraph.zero_l hω he hN hT hS hGraph⟩
  have hωD : mem_l hℳ K.omega D := hωEq ▸ hTerm ω
  have hS' := hS
  have hEquation' := hEquation
  have hGraph' := hGraph
  rw [hωEq] at hS' hEquation' hGraph' ⊢
  exact PowerlessRelativeLimitEvaluationGraph.equations_l K hBase hInner hD hωD hS' hEquation' hGraph'

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationClosure
