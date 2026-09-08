import YesMetaZFC.Logic.FirstOrder.FormalSystem.SemanticInterpretation
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure

/-!
# 内在结构语义合同

本模块把相关语法解释层的定义公理迁移到 `semantic_interpretation_theory`。调用方只需
提供带类型的开放项；对象语言中的变量顺序和作用域由 `VariableSubstitution` 保证。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

private theorem related_syntax_definition_axiom_derives :
    ([] : Context signature []) ⊢ₘ[semantic_interpretation_theory]
      Formula.fromSentence related_syntax_definition_axiom := by
  have hAxiom :
      ([] : Context signature []) ⊢ₘ[related_syntax_semantics_theory]
        Formula.fromSentence related_syntax_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  exact FirstOrder.Derives.theory_weaken
    (fun {sentence} hSentence =>
      term_value_semantics_theory_subset_semantic_interpretation_theory
        (structure_semantics_theory_subset_term_value_semantics_theory
          (related_syntax_semantics_theory_subset_structure_semantics_theory
            hSentence)))
    hAxiom

theorem related_symbol_definition_axiom_derives :
    ([] : Context signature []) ⊢ₘ[semantic_interpretation_theory]
      Formula.fromSentence related_nonlogical_symbol_set_definition_axiom := by
  have hAxiom :
      ([] : Context signature []) ⊢ₘ[related_symbol_semantics_theory]
        Formula.fromSentence related_nonlogical_symbol_set_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  exact FirstOrder.Derives.theory_weaken
    (fun {sentence} hSentence =>
      term_value_semantics_theory_subset_semantic_interpretation_theory
        (structure_semantics_theory_subset_term_value_semantics_theory
          (related_syntax_semantics_theory_subset_structure_semantics_theory
            (related_symbol_semantics_theory_subset_related_syntax_semantics_theory
              hSentence))))
    hAxiom

/-! ## 相关语法递归方程 -/

/-- 相关项码递归方程可在任意开放上下文中直接实例化。 -/
theorem related_term_code_at_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (symbols depth code : SetOpenTerm free) :
    Γ ⊢ₘ[semantic_interpretation_theory]
      related_term_code_at_definition_instance symbols depth code := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    related_term_code_at_definition_instance
      (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons code
      (VariableSubstitution.cons depth
        (VariableSubstitution.cons symbols VariableSubstitution.empty))
  have hClosed :
      ([] : Context signature []) ⊢ₘ[semantic_interpretation_theory]
        Formula.fromSentence (Metatheory.Formula.forall_close body) := by
    simpa [related_syntax_definition_axiom, body] using!
      FirstOrder.Derives.conj_elim_left related_syntax_definition_axiom_derives
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  change Γ ⊢ₘ[semantic_interpretation_theory] (body.substituteFree τ) at hInstance
  rw [related_term_code_at_definition_instance_substituteFree] at hInstance
  simpa [body, τ, Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons,
    VariableSubstitution.empty, VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound, VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-- 相关参数列码递归方程可在任意开放上下文中直接实例化。 -/
theorem related_term_list_code_at_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (symbols depth length code : SetOpenTerm free) :
    Γ ⊢ₘ[semantic_interpretation_theory]
      related_term_list_code_at_definition_instance
        symbols depth length code := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
    related_term_list_code_at_definition_instance
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons code
      (VariableSubstitution.cons length
        (VariableSubstitution.cons depth
          (VariableSubstitution.cons symbols VariableSubstitution.empty)))
  have hClosed :
      ([] : Context signature []) ⊢ₘ[semantic_interpretation_theory]
        Formula.fromSentence (Metatheory.Formula.forall_close body) := by
    have hPart :
        ([] : Context signature []) ⊢ₘ[semantic_interpretation_theory]
          Formula.fromSentence (Metatheory.Formula.forall_close body) := by
      have hRest :
          ([] : Context signature []) ⊢ₘ[semantic_interpretation_theory]
            (Formula.fromSentence related_term_list_code_at_definition_axiom ∧ₘ
              (Formula.fromSentence related_formula_code_at_definition_axiom ∧ₘ
                (Formula.fromSentence related_term_set_definition_axiom ∧ₘ
                  Formula.fromSentence related_formula_set_definition_axiom))) := by
        simpa [related_syntax_definition_axiom, Formula.fromSentence] using!
          (FirstOrder.Derives.conj_elim_right
            (left := Formula.fromSentence related_term_code_at_definition_axiom)
            (right := Formula.fromSentence
              (related_term_list_code_at_definition_axiom ∧ₘ
                (related_formula_code_at_definition_axiom ∧ₘ
                  (related_term_set_definition_axiom ∧ₘ
                    related_formula_set_definition_axiom))))
            related_syntax_definition_axiom_derives)
      simpa [body] using! FirstOrder.Derives.conj_elim_left hRest
    exact hPart
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  change Γ ⊢ₘ[semantic_interpretation_theory] (body.substituteFree τ) at hInstance
  rw [related_term_list_code_at_definition_instance_substituteFree] at hInstance
  simpa [body, τ, Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons,
    VariableSubstitution.empty, VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound, VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-- 相关公式码递归方程可在任意开放上下文中直接实例化。 -/
theorem related_formula_code_at_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (symbols depth code : SetOpenTerm free) :
    Γ ⊢ₘ[semantic_interpretation_theory]
      related_formula_code_at_definition_instance symbols depth code := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    related_formula_code_at_definition_instance
      (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons code
      (VariableSubstitution.cons depth
        (VariableSubstitution.cons symbols VariableSubstitution.empty))
  have hClosed :
      ([] : Context signature []) ⊢ₘ[semantic_interpretation_theory]
        Formula.fromSentence (Metatheory.Formula.forall_close body) := by
    have hPart :
        ([] : Context signature []) ⊢ₘ[semantic_interpretation_theory]
          Formula.fromSentence (Metatheory.Formula.forall_close body) := by
      have hRest₁ :
          ([] : Context signature []) ⊢ₘ[semantic_interpretation_theory]
            (Formula.fromSentence related_term_list_code_at_definition_axiom ∧ₘ
              (Formula.fromSentence related_formula_code_at_definition_axiom ∧ₘ
                (Formula.fromSentence related_term_set_definition_axiom ∧ₘ
                  Formula.fromSentence related_formula_set_definition_axiom))) := by
        simpa [related_syntax_definition_axiom, Formula.fromSentence] using!
          (FirstOrder.Derives.conj_elim_right
            (left := Formula.fromSentence related_term_code_at_definition_axiom)
            (right := Formula.fromSentence
              (related_term_list_code_at_definition_axiom ∧ₘ
                (related_formula_code_at_definition_axiom ∧ₘ
                  (related_term_set_definition_axiom ∧ₘ
                    related_formula_set_definition_axiom))))
            related_syntax_definition_axiom_derives)
      have hRest₂ :
          ([] : Context signature []) ⊢ₘ[semantic_interpretation_theory]
            (Formula.fromSentence related_formula_code_at_definition_axiom ∧ₘ
              (Formula.fromSentence related_term_set_definition_axiom ∧ₘ
                Formula.fromSentence related_formula_set_definition_axiom)) := by
        simpa [Formula.fromSentence] using!
          (FirstOrder.Derives.conj_elim_right
            (left := Formula.fromSentence related_term_list_code_at_definition_axiom)
            (right := Formula.fromSentence
              (related_formula_code_at_definition_axiom ∧ₘ
                (related_term_set_definition_axiom ∧ₘ
                  related_formula_set_definition_axiom)))
            hRest₁)
      simpa [body] using! FirstOrder.Derives.conj_elim_left hRest₂
    exact hPart
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  change Γ ⊢ₘ[semantic_interpretation_theory] (body.substituteFree τ) at hInstance
  rw [related_formula_code_at_definition_instance_substituteFree] at hInstance
  simpa [body, τ, Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons,
    VariableSubstitution.empty, VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound, VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-! ## 相关语法承载集合 -/

/-- 相关公式承载集合定义可在任意开放上下文中直接实例化。 -/
theorem related_formula_set_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (symbols candidate : SetOpenTerm free) :
    Γ ⊢ₘ[semantic_interpretation_theory]
      related_formula_set_definition_instance symbols candidate := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set] :=
    related_formula_set_definition_instance
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons candidate
      (VariableSubstitution.cons symbols VariableSubstitution.empty)
  have hClosed :
      ([] : Context signature []) ⊢ₘ[semantic_interpretation_theory]
        Formula.fromSentence (Metatheory.Formula.forall_close body) := by
    have hPart :
        ([] : Context signature []) ⊢ₘ[semantic_interpretation_theory]
          Formula.fromSentence (Metatheory.Formula.forall_close body) := by
      simpa [related_syntax_definition_axiom, body] using!
        FirstOrder.Derives.conj_elim_right
          (FirstOrder.Derives.conj_elim_right
            (FirstOrder.Derives.conj_elim_right
              (FirstOrder.Derives.conj_elim_right
                related_syntax_definition_axiom_derives)))
    exact hPart
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  change Γ ⊢ₘ[semantic_interpretation_theory] (body.substituteFree τ) at hInstance
  rw [related_formula_set_definition_instance_substituteFree] at hInstance
  simpa [body, τ, Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons,
    VariableSubstitution.empty, VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound, VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
