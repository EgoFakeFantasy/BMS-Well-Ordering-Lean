import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ConstantElimination
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.EmptySet

/-!
# 空集常元的纯语法保守性

本模块把零元常元消去内核实例化到空集常量。基理论只取恒假分离实例及其所需的
外延性；定义扩张中的空集常量不增加该基理论对矛盾的证明能力。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ConstantElimination
namespace EmptySet

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 待消去的空集零元函数符号。 -/
def data : Data signature where
  symbol := FunctionSymbol.emptySet
  sort := SetSort.set
  domain_nil := rfl
  codomain_eq := rfl

/-- 空集存在理论的公理均不使用空集常量。 -/
theorem base_avoids
    {φ : SetFormula} (hφ : empty_set_theory φ) :
    FormulaAvoids data φ := by
  rcases hφ with rfl | hφ
  · simp [FormulaAvoids, TermsAvoid, TermAvoids, data,
      empty_predicate, SetPredicate.separation_axiom,
      SetPredicate.separation_exists,
      Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt]
  · rw [extensionality_theory, Theory.singleton] at hφ
    subst φ
    simp [FormulaAvoids, TermsAvoid, TermAvoids, data,
      extensionality_axiom, Metatheory.Formula.forall_close,
      extensionality_instance, agreement_to_equality,
      membership_agreement, Formula.closeFreeAt,
      Formula.next_depth, Term.closeFreeAt]

/-- 空集存在理论的公理均为闭公式。 -/
theorem base_sentence
    {φ : SetFormula} (hφ : empty_set_theory φ) :
    Formula.Sentence φ := by
  rcases hφ with rfl | hφ
  · constructor
    · exact SetPredicate.separation_axiom_admissible
        empty_predicate
    · native_decide
  · exact extensionality_theory_sentence hφ

/--
空集存在理论不含待消去常元且只有闭公理，因此其翻译像严格等于自身。
-/
theorem theory_eq :
    theory data empty_set_theory =
      empty_set_theory := by
  exact theory_eq_of_sentence_avoids data
    (fun _ hφ => base_avoids hφ)
    (fun _ hφ => base_sentence hφ)

/-- 候选集合恰为所有满足空集规格的集合。 -/
def descriptor_body (empty : SetTerm) : SetFormula :=
  (bₛ#0 ≐ₘ empty) ↔ₘ
    (∀ₘ[SetSort.set],
      (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
        ¬ₘ (bₛ#0 ≐ₘ bₛ#0))

/-- 固定空集候选的全称描述子。 -/
def descriptor (empty : SetTerm) : SetFormula :=
  ∀ₘ[SetSort.set], descriptor_body empty

/-- 存在一个实现空集常量定义公理的候选集合。 -/
def descriptor_exists : SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set],
      (bₛ#0 ≐ₘ bₛ#1) ↔ₘ
        (∀ₘ[SetSort.set],
          (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
            ¬ₘ (bₛ#0 ≐ₘ bₛ#0))

/--
一个满足空集规格的集合满足完整定义描述子。

正向使用等词替换，反向只使用外延性给出的空集唯一性。
-/
theorem descriptor_of_spec :
    [empty_set_spec (x#0)] ⊢ₘ[empty_set_theory]
      descriptor (x#0) := by
  have hPoint :
      [empty_set_spec (x#0)] ⊢ₘ[empty_set_theory]
        (x#1 ≐ₘ x#0) ↔ₘ
          empty_set_spec (x#1) := by
    apply FirstOrder.Derives.iffIntro
    · have hEquality :
          (x#1 ≐ₘ x#0) ::
              [empty_set_spec (x#0)]
            ⊢ₘ[empty_set_theory]
              x#1 ≐ₘ x#0 :=
        .assumption (by simp)
      have hTransport :
          (x#1 ≐ₘ x#0) ::
              [empty_set_spec (x#0)]
            ⊢ₘ[empty_set_theory]
              empty_set_spec (x#1) ↔ₘ
                empty_set_spec (x#0) := by
        simpa [empty_set_spec, Formula.substituteFree,
          Term.substituteFree] using
          (Metatheory.Derives.equality_iff_of_equality
            (sort := SetSort.set) (eigen := 1)
            (body := empty_set_spec (x#1))
            hEquality)
      exact FirstOrder.Derives.iffElimLeft
        hTransport (.assumption (by simp))
    · have hUnique :
          [empty_set_spec (x#1),
              empty_set_spec (x#0)]
            ⊢ₘ[empty_set_theory]
              x#1 ≐ₘ x#0 := by
        have hUniqueTheorem :
            ⊢ₘ[empty_set_theory]
              empty_set_spec (x#1) ⟶ₘ
                empty_set_spec (x#0) ⟶ₘ
                  (x#1 ≐ₘ x#0) :=
          FirstOrder.Derives.theory_weaken
            (fun _ h => Or.inr h)
            (empty_set_unique 1 0)
        have hUniqueContext :=
          FirstOrder.Derives.context_weaken
            (Γ := ([] : Context signature))
            (Δ := [empty_set_spec (x#1),
              empty_set_spec (x#0)])
            (by simp) hUniqueTheorem
        exact FirstOrder.Derives.impElim
          (FirstOrder.Derives.impElim hUniqueContext
            (.assumption (by simp)))
          (.assumption (by simp))
      exact hUnique
  have hGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := empty_set_theory)
      (Γ := [empty_set_spec (x#0)])
      (sort := SetSort.set) (eigen := 1)
      (body := (x#1 ≐ₘ x#0) ↔ₘ
        empty_set_spec (x#1))
      (by
        intro φ hφ
        simp [(base_sentence hφ).2])
      (by
        intro φ hφ
        rcases List.mem_singleton.mp hφ with rfl
        native_decide)
      hPoint
  simpa [descriptor, descriptor_body,
    empty_set_spec, Formula.closeFreeAt,
    Formula.next_depth,
    Term.closeFreeAt] using hGeneralized

/--
空集存在性与外延唯一性共同给出定义描述子的存在见证。
-/
theorem descriptor_exists_derives :
    ⊢ₘ[empty_set_theory] descriptor_exists := by
  have hExists :
      ⊢ₘ[empty_set_theory]
        (Formula.existsE SetSort.set <|
          Formula.closeFreeAt SetSort.set 0 0
            (empty_set_spec (x#0))) := by
    simpa [empty_set_exists, empty_set_spec,
      Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt] using
      empty_set_exists_derives
  have hCase :
      [empty_set_spec (x#0)]
        ⊢ₘ[empty_set_theory] descriptor_exists := by
    apply FirstOrder.Derives.exists_intro
      (term := x#0)
    simpa [descriptor_exists, descriptor,
      descriptor_body, empty_set_spec,
      Formula.openAt, Formula.next_depth,
      Term.openAt] using
      descriptor_of_spec
  exact FirstOrder.Derives.exists_elim
    (sort := SetSort.set) (eigen := 0)
    (body := empty_set_spec (x#0))
    (conclusion := descriptor_exists)
    (by
      intro φ hφ
      simp [(base_sentence hφ).2])
    (by simp)
    (by native_decide)
    hExists hCase
    (Formula.check_admissible_complete
      (empty_set_spec_admissible
        (set_variable_admissible 0)))

/--
零元常元翻译后，空集定义公理的存在闭包正是上述描述子存在式。
-/
theorem translated_definition :
    (Formula.existsE data.sort <|
      Formula.closeFreeAt data.sort 0 0 <|
        formula data empty_set_definition_axiom) =
      descriptor_exists := by
  simp [data, descriptor_exists,
    empty_set_definition_axiom,
    empty_set_definition_instance,
    empty_set_spec, formula, term, terms,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt]

/-- 空集常量定义扩张的完整零元消去表示。 -/
def presentation :
    Presentation signature where
  data := data
  base := empty_set_theory
  definition := empty_set_definition_axiom
  definition_admissible :=
    empty_set_definition_axiom_admissible
  base_avoids := by
    intro φ hφ
    exact base_avoids hφ
  definition_exists := by
    rw [theory_eq, translated_definition]
    exact descriptor_exists_derives

/--
向空集存在理论加入空集常量定义公理不会产生新的矛盾。
-/
theorem derives_falsum
    (h :
      HilbertDerives empty_set_symbol_theory
        Formula.falsum) :
    Derives empty_set_theory [] Formula.falsum := by
  have hExtension :
      HilbertDerives presentation.extension
        Formula.falsum := by
    simpa [presentation, Presentation.extension,
      empty_set_symbol_theory] using h
  simpa [presentation, theory_eq] using
    presentation.derives_falsum hExtension

/-- 空集存在理论的一致性推出空集常量定义扩张的 Hilbert 一致性。 -/
theorem consistent_extension
    (hBase :
      Derives.Consistent empty_set_theory []) :
    ¬ HilbertDerives empty_set_symbol_theory
      Formula.falsum := by
  intro hExtension
  exact hBase (derives_falsum hExtension)

end EmptySet
end ConstantElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
