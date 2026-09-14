import BMSConstructibleBridge.PowerlessEvaluationClosure

/-!
# 求值子集族的总唯一纯算子

固定内部 ω、编码和四个标签。量化掉有限赋值集合与实际求值图，
得到 A↦D 的纯关系；中间对象的唯一性从已有定理逐项消去。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationOperator

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def assignments_l (ω A S : carrier_l ℳ) : Prop :=
  ∀ f, member_l ℳ f S ↔ ∃ n, member_l ℳ n ω ∧ map_l f n A

def assignments_m {Γ Δ : SortContext ℒ} (ω A S : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set (.iff (SecondOrderObjectSyntax.member_m (.bvar .here) (S.weakenBound SetTheory.SetSort.set))
    (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (w ω))
      (SecondOrderObjectSyntax.map_m (.bvar (.there .here)) (.bvar .here) (w A)))))

theorem assignments_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω A S : Term ℒ Γ Δ .set) :
    (assignments_m ω A S).satisfies η ↔ assignments_l (ω.eval η) (A.eval η) (S.eval η) := by
  simp only [assignments_m, assignments_l, Formula.satisfies, map_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def operator_l (ω e T t₁ t₂ t₃ A D : carrier_l ℳ) : Prop :=
  ∃ S F, assignments_l ω A S ∧ PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F ∧
    PowerlessEvaluationFamily.family_l ω A F S D

def operator_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ A D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.existsE .set (.conj (assignments_m (w ω) (w A) (.bvar (.there .here)))
    (.conj (PowerlessEvaluationPresentation.evaluation_m (w ω) (w e) (w T) (w A) (w t₁) (w t₂) (w t₃)
      (.bvar (.there .here)) (.bvar .here))
      (PowerlessEvaluationFamily.family_m (w ω) (w A) (.bvar .here) (.bvar (.there .here)) (w D)))))

theorem operator_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ A D : Term ℒ Γ Δ .set) :
    (operator_m ω e T t₁ t₂ t₃ A D).satisfies η ↔ operator_l (ω.eval η) (e.eval η) (T.eval η)
      (t₁.eval η) (t₂.eval η) (t₃.eval η) (A.eval η) (D.eval η) := by
  simp only [operator_m, operator_l, Formula.satisfies, assignments_formula_l,
    PowerlessEvaluationPresentation.evaluation_formula_l hℳ, PowerlessEvaluationFamily.family_formula_l,
    Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) (e T t₁ t₂ t₃ A : carrier_l ℳ) :
    ∃ D, operator_l ω e T t₁ t₂ t₃ A D := by
  obtain ⟨S, hS⟩ := PowerlessFiniteAssignments.all_exists_l hℳ hω A
  obtain ⟨F, hF, _⟩ := PowerlessEvaluationRecursion.exists_unique_l hℳ hω e T A t₁ t₂ t₃ S
  obtain ⟨_, _, D, _, _, _, hD⟩ := PowerlessEvaluationFamily.exists_l hℳ ω A F S
  exact ⟨D, S, F, hS, hF, hD⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ A D E : carrier_l ℳ} (hω : omega_l ω)
    (hD : operator_l ω e T t₁ t₂ t₃ A D) (hE : operator_l ω e T t₁ t₂ t₃ A E) : D = E := by
  obtain ⟨S, F, hS, hF, hD⟩ := hD
  obtain ⟨Q, G, hQ, hG, hE⟩ := hE
  have h₀ : S = Q := (PowerlessTheory.ext_l hℳ).eq_of_same_members S Q (fun f => (hS f).trans (hQ f).symm)
  subst Q
  obtain ⟨H, _, h₁⟩ := PowerlessEvaluationRecursion.exists_unique_l hℳ hω e T A t₁ t₂ t₃ S
  have h₂ := (h₁ F hF).trans (h₁ G hG).symm
  subst G
  exact PowerlessEvaluationFamily.unique_l hℳ hD hE

theorem subset_l {ω e T t₁ t₂ t₃ A D B : carrier_l ℳ}
    (hD : operator_l ω e T t₁ t₂ t₃ A D) (hB : member_l ℳ B D) : ThirdOrderSemantics.subset_l B A := by
  obtain ⟨_, _, _, _, hD⟩ := hD
  exact PowerlessEvaluationFamily.subset_l hD hB

theorem inclusion_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ A D : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hD : operator_l ω e T t₁ t₂ t₃ A D) (hA : PowerlessNaturalOrder.transitive_l A) : ThirdOrderSemantics.subset_l A D := by
  obtain ⟨_, _, hS, hF, hD⟩ := hD
  exact PowerlessEvaluationClosure.inclusion_l hℳ hω ht hT hF hS hD hA

theorem transitive_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ A D : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hD : operator_l ω e T t₁ t₂ t₃ A D) (hA : PowerlessNaturalOrder.transitive_l A) : PowerlessNaturalOrder.transitive_l D := by
  obtain ⟨_, _, hS, hF, hD⟩ := hD
  exact PowerlessEvaluationClosure.transitive_l hℳ hω ht hT hF hS hD hA

theorem empty_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ A D : carrier_l ℳ} (hω : omega_l ω)
    (hD : operator_l ω e T t₁ t₂ t₃ A D) (hA : PowerlessNatural.zero_l A) (B : carrier_l ℳ) :
    member_l ℳ B D ↔ PowerlessNatural.zero_l B := by
  obtain ⟨_, _, hS, _, hD⟩ := hD
  exact PowerlessEvaluationClosure.empty_l hℳ hω hA hS hD B

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationOperator
