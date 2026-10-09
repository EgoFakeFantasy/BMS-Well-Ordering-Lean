import BMSConstructibleBridge.PowerlessRelativeClassEvaluationRelation
import BMSConstructibleBridge.PowerlessRelativeLimitEvaluationEquations
import BMSConstructibleBridge.PowerlessRelativeClassParameterBounds

/-! # 实际静态参数的共同求值层与集合图

共同非零极限层及其全有限序列集均由类内参数实际构造，调用者不再预设
层界、历史或查询递归方程。这里只消费编码规格；它们在系统装配中另行构造。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEvaluationClosure

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

/-- 将已证对象闭模式实例化为实际极限层的查询方程。 -/
theorem equations_l {Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) {β C : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C)
    (hSC : mem_l hℳ (S.eval η) C) (hω : omega_l (ℳ := SecondOrderQuotient.structure_l hℳ) (ω.eval η))
    (hωC : mem_l hℳ (ω.eval η) C) (he : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) (e.eval η))
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) (ω.eval η) (ω.eval η) (N.eval η))
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) (T.eval η) (ω.eval η) (ω.eval η))
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) (ω.eval η) (A.eval η) (S.eval η))
    (hBounds : ∀ t a b n, PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (ω.eval η) (e.eval η) (T.eval η) t a b n → mem_l hℳ a n ∧ mem_l hℳ b n)
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := SecondOrderQuotient.structure_l hℳ) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η))
    (hInjective : PowerlessRelativeClassConstructorInjective.injective_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      (ω.eval η) (e.eval η) (T.eval η)) :
    PowerlessFiniteEvaluationEquations.equations_l C (ω.eval η) (e.eval η) (N.eval η)
      (T.eval η) (A.eval η) (S.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have h := ((_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeLimitEvaluationEquations.models_l hℳ ω e N T A S t₁ t₂ t₃)) η
  simp only [PowerlessRelativeLimitEvaluationEquations.schema_m,
    PowerlessRelativeLimitEvaluationEquation.guarded_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K, PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeLimitDeltaSeparationDerives.parameters_formula_l, omega_formula_l,
    PowerlessFiniteSequencesSyntax.spec_formula_l, map_formula_l,
    PowerlessRelativeClassConstructorBounds.bounds_formula_l, PowerlessEvaluationTags.tags_formula_l,
    PowerlessRelativeClassConstructorInjective.injective_formula_l, PowerlessFiniteEvaluationEquations.equations_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval] at h
  exact h B β C hBase hC hLimit hParams hSC hω hωC he hN hT hS hBounds hTags hInjective

theorem exists_l {Δ : SortContext ℒ} (η : Env (structure_l hℳ B hBase) [] Δ)
    (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set)
    (hω : omega_l (ℳ := structure_l hℳ B hBase) (ω.eval η))
    (he : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) (e.eval η).val)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) (ω.eval η).val (ω.eval η).val (N.eval η).val)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) (T.eval η).val (ω.eval η).val (ω.eval η).val)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) (ω.eval η).val (A.eval η).val (S.eval η).val)
    (hBounds : ∀ t a b n, PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (ω.eval η).val (e.eval η).val (T.eval η).val t a b n → mem_l hℳ a n ∧ mem_l hℳ b n)
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (e.eval η).val (t₁.eval η).val (t₂.eval η).val (t₃.eval η).val)
    (hInjective : PowerlessRelativeClassConstructorInjective.injective_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      (ω.eval η).val (e.eval η).val (T.eval η).val) :
    ∃ C Q G : type_l hℳ B,
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) (ω.eval η).val C.val Q.val ∧
      PowerlessFiniteEvaluationRelation.spec_l (𝒩 := SecondOrderQuotient.structure_l hℳ) C.val (ω.eval η).val (e.eval η).val
        (N.eval η).val (T.eval η).val (A.eval η).val (S.eval η).val (t₁.eval η).val (t₂.eval η).val (t₃.eval η).val Q.val G.val ∧
      PowerlessFiniteEvaluationRelationEquations.equations_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        (ω.eval η).val (e.eval η).val (T.eval η).val (A.eval η).val (S.eval η).val
        (t₁.eval η).val (t₂.eval η).val (t₃.eval η).val G.val ∧
      PowerlessFiniteEvaluationRelationEquations.equations_l (𝒩 := structure_l hℳ B hBase)
        (ω.eval η) (e.eval η) (T.eval η) (A.eval η) (S.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) G := by
  obtain ⟨α, C₀, hC₀, hSC₀, hParams₀⟩ := PowerlessRelativeClassParameterBounds.exists_l η (S.eval η)
  obtain ⟨β, hβ, hαβ, hNoMax⟩ := SecondOrderOrdinalLimitDerives.exists_l hℳ α
    (PowerlessRelativeLevelClosure.ordinal_l hℳ hC₀)
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hβ
  have hParams s (v : Variable Δ s) :=
    PowerlessRelativeLevelClosure.subset_l hℳ hBase hαβ hC₀ hC (η.freeVal v).val (hParams₀ s v)
  have hTerm (t : Term ℒ [] Δ .set) : mem_l hℳ (t.eval η).val C := by
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact hParams _ v
    | .app f _ => nomatch f
  have hEval (t : Term ℒ [] Δ .set) : (t.eval η).val = t.eval (PowerlessRelativeClassRelativization.env_l η) := by
    match t with
    | .bvar v => nomatch v
    | .fvar _ => rfl
    | .app f _ => nomatch f
  have hωRaw := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) (ω.eval η)).mp hω
  have hEquation : PowerlessFiniteEvaluationEquations.equations_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      C (ω.eval η).val (e.eval η).val (N.eval η).val (T.eval η).val (A.eval η).val (S.eval η).val
      (t₁.eval η).val (t₂.eval η).val (t₃.eval η).val := by
    simp only [hEval] at he hN hT hS hBounds hTags hInjective hωRaw ⊢
    exact equations_l (PowerlessRelativeClassRelativization.env_l η) ω e N T A S t₁ t₂ t₃
      hBase hC ⟨⟨α, hαβ⟩, hNoMax⟩ hParams
      (hEval S ▸ PowerlessRelativeLevelClosure.subset_l hℳ hBase hαβ hC₀ hC _ hSC₀)
      hωRaw (hEval ω ▸ hTerm ω) he hN hT hS hBounds hTags hInjective
  let C' : type_l hℳ B := ⟨C, PowerlessRelativeLevelClosure.class_l hℳ hBase hC⟩
  obtain ⟨Q, hQ, _⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l (X := C') hω
  let ξ : Env (structure_l hℳ B hBase) [] (.set :: .set :: Δ) := (η.pushFree C').pushFree Q
  let w (t : Term ℒ [] Δ .set) := (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set
  have hLift (t : Term ℒ [] Δ .set) : (w t).eval (PowerlessRelativeClassRelativization.env_l ξ) = (t.eval η).val := by
    match t with
    | .bvar v => nomatch v
    | .fvar _ => rfl
    | .app f _ => nomatch f
  have hCValue : (Term.fvar (.there .here) : Term ℒ [] (.set :: .set :: Δ) .set).eval
      (PowerlessRelativeClassRelativization.env_l ξ) = C'.val := rfl
  have hQValue : (Term.fvar .here : Term ℒ [] (.set :: .set :: Δ) .set).eval
      (PowerlessRelativeClassRelativization.env_l ξ) = Q.val := rfl
  obtain ⟨G, hG, hRaw, hClass⟩ := PowerlessRelativeClassEvaluationRelation.exists_ambient_l ξ
    (.fvar (.there .here)) (w ω) (w e) (w N) (w T) (w A) (w S) (w t₁) (w t₂) (w t₃) (.fvar .here)
    (by simpa only [hLift] using hωRaw)
    (by simpa only [hLift] using hS)
    (by simpa only [hLift, hCValue, hQValue] using hQ)
    (by simpa only [hLift, hCValue] using hEquation)
  refine ⟨C', Q, G, hQ, ?_⟩
  simpa only [hLift, hCValue, hQValue, ξ, w, Term.eval_weakenFree] using And.intro hG (And.intro hRaw hClass)

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEvaluationClosure
