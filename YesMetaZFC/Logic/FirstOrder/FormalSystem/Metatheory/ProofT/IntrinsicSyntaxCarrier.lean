import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSyntaxSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.StructuralCorrectness
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.EmptySet

/-!
# 内在结构语法承载层

相关公式集合的成员证明需要真正的子集关系和空集定义；它们不是结构语义核心的
隐含前提，因此在这里显式组成最小承载理论。该层只证明一个可复用的闭式公式
码成员合同，不把承载集合偷换成语法正确性谓词。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open QuineEncoding
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 相关公式承载所需的最小理论：子集、空集定义以及结构语义核心。 -/
def intrinsic_syntax_carrier_theory : SetTheory :=
  Theory.union (Theory.union subset_theory empty_set_symbol_theory)
    semantic_interpretation_theory

theorem subset_theory_subset_intrinsic_syntax_carrier_theory
    {sentence : SetSentence}
    (hSentence : subset_theory sentence) :
    intrinsic_syntax_carrier_theory sentence :=
  Or.inl (Or.inl hSentence)

theorem empty_set_symbol_theory_subset_intrinsic_syntax_carrier_theory
    {sentence : SetSentence}
    (hSentence : empty_set_symbol_theory sentence) :
    intrinsic_syntax_carrier_theory sentence :=
  Or.inl (Or.inr hSentence)

theorem semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
    {sentence : SetSentence}
    (hSentence : semantic_interpretation_theory sentence) :
    intrinsic_syntax_carrier_theory sentence :=
  Or.inr hSentence

theorem expression_encoding_theory_subset_intrinsic_syntax_carrier_theory
    {sentence : SetSentence}
    (hSentence : expression_encoding_theory sentence) :
    intrinsic_syntax_carrier_theory sentence := by
  apply semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
  apply term_value_semantics_theory_subset_semantic_interpretation_theory
  apply structure_semantics_theory_subset_term_value_semantics_theory
  apply related_syntax_semantics_theory_subset_structure_semantics_theory
  apply related_symbol_semantics_theory_subset_related_syntax_semantics_theory
  apply logical_rule_encoding_theory_subset_related_symbol_semantics_theory
  apply logical_axiom_code_theory_subset_logical_rule_encoding_theory
  apply equality_axiom_schema_theory_subset_logical_axiom_code_theory
  apply quantifier_axiom_schema_theory_subset_equality_axiom_schema_theory
  apply propositional_axiom_schema_theory_subset_quantifier_axiom_schema_theory
  exact expression_encoding_theory_subset_propositional_axiom_schema_theory hSentence

theorem formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory
    {sentence : SetSentence}
    (hSentence : formal_language_encoding_theory sentence) :
    intrinsic_syntax_carrier_theory sentence := by
  exact expression_encoding_theory_subset_intrinsic_syntax_carrier_theory
    (formal_language_encoding_theory_subset_expression_encoding_theory hSentence)

private theorem two_free_substitution_beta
    {free : SetContext}
    {body : SetOpenFormula ([SetSort.set, SetSort.set] ++ free)}
    (first second : SetOpenTerm free) :
    Formula.instantiateFreeTop first
      (Formula.substituteFree
        (VariableSubstitution.liftFree SetSort.set
          (VariableSubstitution.instantiateFreeTop second)) body) =
      Formula.substituteFree
        (VariableSubstitution.cons first
          (VariableSubstitution.cons second VariableSubstitution.freeId)) body := by
  change
    Formula.substitute
      (Substitution.instantiateFreeTop first)
      (Formula.substitute
        (Substitution.free_map
          (VariableSubstitution.liftFree SetSort.set
            (VariableSubstitution.instantiateFreeTop second))) body) =
      Formula.substitute
        (Substitution.free_map
          (VariableSubstitution.cons first
            (VariableSubstitution.cons second VariableSubstitution.freeId))) body
  rw [Formula.substitute_comp]
  simp only [Substitution.comp, Substitution.instantiateFreeTop,
    Substitution.free_map]
  congr 1
  change Substitution.map _ _ = Substitution.map _ _
  congr
  funext resultSort entry
  cases entry with
  | here =>
      simp [ VariableSubstitution.cons, VariableSubstitution.liftFree,
        VariableSubstitution.instantiateFreeTop,
        Term.substituteMapped]
  | there previous =>
      cases resultSort
      cases previous with
      | here =>
          simpa [Term.weakenFree, Term.rename, Renaming.weakenFree,
            Renaming.free, Term.renameMapped] using!
            (Term.substituteMapped_weakenFree_instantiateFreeTop
              (σ := signature) SetSort.set first second)
      | there previous =>
          simp [ VariableSubstitution.cons,
            VariableSubstitution.freeId, VariableSubstitution.liftFree,
            VariableSubstitution.instantiateFreeTop, Term.substituteMapped,
            Term.weakenFree, Term.rename, Renaming.weakenFree,
            Renaming.free, Term.renameMapped, VariableRenaming.weaken]

private theorem substitute_two_weaken_free_id
    {free : SetContext}
    (first second : SetOpenTerm free)
    (term : SetOpenTerm free) :
    Term.substituteMapped VariableSubstitution.boundId
      (VariableSubstitution.cons first
        (VariableSubstitution.cons second VariableSubstitution.freeId))
      ((term.weakenFree SetSort.set).weakenFree SetSort.set) = term := by
  exact Term.rec
    (motive_1 := fun _ term =>
      Term.substituteMapped VariableSubstitution.boundId
          (VariableSubstitution.cons first
            (VariableSubstitution.cons second VariableSubstitution.freeId))
          ((term.weakenFree SetSort.set).weakenFree SetSort.set) = term)
    (motive_2 := fun _ arguments =>
      Arguments.substituteMapped VariableSubstitution.boundId
          (VariableSubstitution.cons first
            (VariableSubstitution.cons second VariableSubstitution.freeId))
          ((arguments.weakenFree SetSort.set).weakenFree SetSort.set) = arguments)
    (fun entry => by
      cases entry)
    (fun entry => by
      simp [Term.substituteMapped, Term.weakenFree, Term.rename,
        Renaming.weakenFree, Renaming.free, Term.renameMapped,
        VariableSubstitution.cons, VariableSubstitution.freeId,
        VariableRenaming.weaken])
    (fun function arguments ih => by
      change Term.app function
          (Arguments.substituteMapped VariableSubstitution.boundId
            (VariableSubstitution.cons first
              (VariableSubstitution.cons second VariableSubstitution.freeId))
            ((arguments.weakenFree SetSort.set).weakenFree SetSort.set)) =
        Term.app function arguments
      rw [ih])
    rfl
    (fun head tail ihHead ihTail => by
      change Arguments.cons
          (Term.substituteMapped VariableSubstitution.boundId
            (VariableSubstitution.cons first
              (VariableSubstitution.cons second VariableSubstitution.freeId))
            ((head.weakenFree SetSort.set).weakenFree SetSort.set))
          (Arguments.substituteMapped VariableSubstitution.boundId
            (VariableSubstitution.cons first
              (VariableSubstitution.cons second VariableSubstitution.freeId))
            ((tail.weakenFree SetSort.set).weakenFree SetSort.set)) =
        Arguments.cons head tail
      rw [ihHead, ihTail])
    term

theorem related_nonlogical_symbol_set_subset_derives
    {free : SetContext} {Γ : Context signature free} :
    Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
      (NonlogicalSymₘ : SetOpenTerm free) ⊆ₘ NonlogicalSymₘ := by
  apply subset_intro
    (fun {sentence} hSentence =>
      subset_theory_subset_intrinsic_syntax_carrier_theory hSentence)
  apply FirstOrder.Derives.imp_intro
  exact FirstOrder.Derives.assumption List.mem_cons_self

private theorem related_term_code_at_free_variable_derives
    {free : SetContext} {Γ : Context signature free}
    (symbols depth index code : SetOpenTerm free)
    (hDepth : Γ ⊢ₘ[intrinsic_syntax_carrier_theory] depth ∈ₘ ωₘ)
    (hCode : Γ ⊢ₘ[intrinsic_syntax_carrier_theory] code ∈ₘ ωₘ)
    (hIndex : Γ ⊢ₘ[intrinsic_syntax_carrier_theory] index ∈ₘ ωₘ)
    (hCodeEq : Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ free_var_codeₘ(index)) :
    Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(symbols, depth, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (FirstOrder.Derives.theory_weaken
      semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
      (related_term_code_at_definition_instance_derives
        (Γ := Γ) symbols depth code))
  apply FirstOrder.Derives.conj_intro
  · exact FirstOrder.Derives.conj_intro hDepth hCode
  · apply FirstOrder.Derives.disj_intro_left
    unfold related_term_code_free_condition
    apply FirstOrder.Derives.exists_intro index
    simpa using! FirstOrder.Derives.conj_intro hIndex hCodeEq

theorem intrinsic_syntax_carrier_formula_mem
    {free : SetContext} {Γ : Context signature free} :
    Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
      eq_codeₘ(
        free_var_codeₘ(numₘ(0)),
        free_var_codeₘ(numₘ(0))) ∈ₘ
        syntax_formula_code_set_term := by
  let symbols : SetOpenTerm free := NonlogicalSymₘ
  let depth : SetOpenTerm free := numₘ(0)
  let termCode : SetOpenTerm free := free_var_codeₘ(numₘ(0))
  let formulaCode : SetOpenTerm free := eq_codeₘ(termCode, termCode)
  have hDepthFormal := finite_numeral_mem_formal_language_encoding_theory
    (Γ := Γ) 0
  have hDepth : Γ ⊢ₘ[intrinsic_syntax_carrier_theory] depth ∈ₘ ωₘ := by
    simpa [depth] using
      FirstOrder.Derives.theory_weaken
        formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory
        hDepthFormal
  have hIndex := hDepth
  have hTermCodeFormal :=
    structural_node_code_mem_formal_language_encoding_theory
      (Γ := Γ) .freeVariable [numₘ(0)] (by
        intro field hField
        simp only [List.mem_cons, List.not_mem_nil] at hField
        rcases hField with hField | hField
        · simpa [hField] using hDepthFormal
        · contradiction)
  have hTermCode : Γ ⊢ₘ[intrinsic_syntax_carrier_theory] termCode ∈ₘ ωₘ := by
    simpa [termCode] using
      FirstOrder.Derives.theory_weaken
        formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory
        hTermCodeFormal
  have hTermAt := related_term_code_at_free_variable_derives
    (Γ := Γ) symbols depth (numₘ(0)) termCode hDepth hTermCode hIndex
      (Metatheory.Derives.equality_refl termCode)
  have hFormulaCodeFormal :=
    structural_node_code_mem_formal_language_encoding_theory
      (Γ := Γ) .equality [termCode, termCode] (by
        intro field hField
        simp only [List.mem_cons, List.not_mem_nil] at hField
        rcases hField with hField | hField
        · simpa [hField] using hTermCodeFormal
        · rcases hField with hField | hField
          · simpa [hField] using hTermCodeFormal
          · contradiction)
  have hFormulaCode :
      Γ ⊢ₘ[intrinsic_syntax_carrier_theory] formulaCode ∈ₘ ωₘ := by
    simpa [formulaCode] using
      FirstOrder.Derives.theory_weaken
        formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory
        hFormulaCodeFormal
  have hBinary : Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_binary_condition symbols depth formulaCode
        .equality := by
    unfold related_formula_binary_condition
    apply FirstOrder.Derives.exists_intro termCode
    rw [Formula.instantiateTop_abstractFreeTop,
      Formula.instantiateFreeTop_existsFreeTop]
    apply FirstOrder.Derives.exists_intro termCode
    rw [Formula.instantiateTop_abstractFreeTop]
    let symbolsTwo : SetOpenTerm ([SetSort.set, SetSort.set] ++ free) :=
      @Term.weakenFree signature [] (SetSort.set :: free)
        SetSort.set SetSort.set
        (@Term.weakenFree signature [] free SetSort.set SetSort.set symbols)
    let depthTwo : SetOpenTerm ([SetSort.set, SetSort.set] ++ free) :=
      @Term.weakenFree signature [] (SetSort.set :: free)
        SetSort.set SetSort.set
        (@Term.weakenFree signature [] free SetSort.set SetSort.set depth)
    let codeTwo : SetOpenTerm ([SetSort.set, SetSort.set] ++ free) :=
      @Term.weakenFree signature [] (SetSort.set :: free)
        SetSort.set SetSort.set
        (@Term.weakenFree signature [] free SetSort.set SetSort.set formulaCode)
    let body : SetOpenFormula ([SetSort.set, SetSort.set] ++ free) :=
      ((related_term_code_atₘ(
          symbolsTwo, depthTwo,
          .fvar (.there .here)) ∧ₘ
        related_term_code_atₘ(
          symbolsTwo, depthTwo,
          .fvar .here)) ∧ₘ
        (codeTwo ≐ₘ
          structural_node_code_term .equality
            [.fvar (.there .here), .fvar .here]))
    change Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
      Formula.instantiateFreeTop termCode
        (Formula.substituteFree
          (VariableSubstitution.liftFree SetSort.set
            (VariableSubstitution.instantiateFreeTop termCode)) body)
    rw [two_free_substitution_beta (body := body) termCode termCode]
    simp only [ Formula.substituteFree]
    let τ : VariableSubstitution signature
        ([SetSort.set, SetSort.set] ++ free) [] free :=
      VariableSubstitution.cons termCode
        (VariableSubstitution.cons termCode VariableSubstitution.freeId)
    have hDepthClosed :
        Term.substituteMapped VariableSubstitution.boundId τ
            ((depth.weakenFree SetSort.set).weakenFree SetSort.set) = depth :=
      substitute_two_weaken_free_id termCode termCode depth
    have hSymbolsClosed :
        Term.substituteMapped VariableSubstitution.boundId τ
            ((symbols.weakenFree SetSort.set).weakenFree SetSort.set) = symbols :=
      substitute_two_weaken_free_id termCode termCode symbols
    have hCodeClosed :
        Term.substituteMapped VariableSubstitution.boundId τ
            ((formulaCode.weakenFree SetSort.set).weakenFree SetSort.set) =
          formulaCode :=
      substitute_two_weaken_free_id termCode termCode formulaCode
    have hTargetClosed :
        Term.substituteMapped VariableSubstitution.boundId τ
            (structural_node_code_term .equality
              [.fvar (.there .here), .fvar .here]) =
          structural_node_code_term .equality [termCode, termCode] := by
      simp [structural_node_code_term, structural_list_code_term,
        structural_raw_node_code_term, godel_pairing_term,
        Term.substituteMapped, Arguments.substituteMapped, τ,
        VariableSubstitution.cons]
    change Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
      Formula.substitute (Substitution.free_map τ) body
    have hBody :
        Formula.substitute (Substitution.free_map τ) body =
          ((related_term_code_atₘ(symbols, depth, termCode) ∧ₘ
              related_term_code_atₘ(symbols, depth, termCode)) ∧ₘ
            (formulaCode ≐ₘ
              structural_node_code_term .equality [termCode, termCode])) := by
      change
        ((related_term_code_atₘ(
            Term.substituteMapped VariableSubstitution.boundId τ
              ((symbols.weakenFree SetSort.set).weakenFree SetSort.set),
            Term.substituteMapped VariableSubstitution.boundId τ
              ((depth.weakenFree SetSort.set).weakenFree SetSort.set),
            Term.substituteMapped VariableSubstitution.boundId τ
              (.fvar (.there .here))) ∧ₘ
          related_term_code_atₘ(
            Term.substituteMapped VariableSubstitution.boundId τ
              ((symbols.weakenFree SetSort.set).weakenFree SetSort.set),
            Term.substituteMapped VariableSubstitution.boundId τ
              ((depth.weakenFree SetSort.set).weakenFree SetSort.set),
            Term.substituteMapped VariableSubstitution.boundId τ
              (.fvar .here))) ∧ₘ
          (Term.substituteMapped VariableSubstitution.boundId τ
              ((formulaCode.weakenFree SetSort.set).weakenFree SetSort.set) ≐ₘ
            Term.substituteMapped VariableSubstitution.boundId τ
              (structural_node_code_term .equality
                [.fvar (.there .here), .fvar .here]))) =
          ((related_term_code_atₘ(symbols, depth, termCode) ∧ₘ
              related_term_code_atₘ(symbols, depth, termCode)) ∧ₘ
            (formulaCode ≐ₘ
              structural_node_code_term .equality [termCode, termCode]))
      rw [hSymbolsClosed, hDepthClosed, hCodeClosed, hTargetClosed]
      rfl
    rw [hBody]
    exact FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hTermAt hTermAt)
      (Metatheory.Derives.equality_refl formulaCode)
  have hSubset := related_nonlogical_symbol_set_subset_derives (Γ := Γ)
  have hSetEq :
      (syntax_formula_code_set_term : SetOpenTerm free) =
        RelFormulaCodeₘ(symbols) := by
    induction free <;> rfl
  have hDefinition := FirstOrder.Derives.theory_weaken
    semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
    (related_formula_set_definition_instance_derives
      (Γ := Γ) symbols syntax_formula_code_set_term)
  have hIff := FirstOrder.Derives.imp_elim hDefinition hSubset
  have hSpec := FirstOrder.Derives.iff_elim_left hIff
    (by
      rw [hSetEq]
      exact Metatheory.Derives.equality_refl
        (T := intrinsic_syntax_carrier_theory) (Γ := Γ)
        (RelFormulaCodeₘ(symbols)))
  have hAt := FirstOrder.Derives.forall_elim
    (term := formulaCode) hSpec
  have hAt' : Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
      formulaCode ∈ₘ syntax_formula_code_set_term ↔ₘ
        related_formula_code_condition symbols formulaCode := by
    simpa [symbols, related_formula_set_spec, Formula.instantiateFreeTop,
      Substitution.instantiateFreeTop, Formula.substitute,
      Formula.substituteMapped, Term.substituteFree, Term.substitute,
      Term.substituteMapped, Arguments.substituteMapped,
      Term.substituteMapped_weakenFree_instantiateFreeTop,
      Arguments.substituteMapped_weakenFree_instantiateFreeTop,
      Formula.substituteMapped_weakenFree_instantiateFreeTop,
      VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.liftFree, VariableSubstitution.weakenBound,
      VariableSubstitution.boundId, VariableSubstitution.freeId] using! hAt
  have hFormulaCondition :
      Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_at_condition symbols depth formulaCode := by
    apply FirstOrder.Derives.conj_intro
    · exact FirstOrder.Derives.conj_intro hDepth hFormulaCode
    · apply FirstOrder.Derives.disj_intro_left
      exact hBinary
  have hFormulaAt :
      Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(symbols, depth, formulaCode) := by
    apply FirstOrder.Derives.iff_elim_right
      (FirstOrder.Derives.theory_weaken
        semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
        (related_formula_code_at_definition_instance_derives
          (Γ := Γ) symbols depth formulaCode))
    exact hFormulaCondition
  have hCondition : Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_condition symbols formulaCode := by
    unfold related_formula_code_condition
    apply FirstOrder.Derives.exists_intro depth
    rw [Formula.instantiateTop_abstractFreeTop]
    simpa [Formula.instantiateFreeTop, Formula.substitute,
      Formula.substituteMapped, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.boundId] using! hFormulaAt
  exact FirstOrder.Derives.iff_elim_right hAt' hCondition

theorem intrinsic_syntax_carrier_formula_code_nonempty
    {free : SetContext} {Γ : Context signature free} :
    Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
      syntax_formula_code_set_term ≠ₘ ∅ₘ := by
  have hMember := intrinsic_syntax_carrier_formula_mem (Γ := Γ)
  have hImp : Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
      (eq_codeₘ(
        free_var_codeₘ(numₘ(0)),
        free_var_codeₘ(numₘ(0))) ∈ₘ syntax_formula_code_set_term) ⟶ₘ
        ¬ₘ (syntax_formula_code_set_term ≐ₘ ∅ₘ) := by
    simpa [set_nonempty_condition] using
      FirstOrder.Derives.theory_weaken
        empty_set_symbol_theory_subset_intrinsic_syntax_carrier_theory
        (member_implies_set_nonempty
          (Γ := Γ)
          (eq_codeₘ(
            free_var_codeₘ(numₘ(0)),
            free_var_codeₘ(numₘ(0)))) syntax_formula_code_set_term)
  exact FirstOrder.Derives.imp_elim hImp hMember

theorem intrinsic_syntax_carrier_formula_mem_implies_omega
    {T : SetTheory}
    (hT : Theory.Extends T intrinsic_syntax_carrier_theory)
    {free : SetContext} {Γ : Context signature free}
    (code : SetOpenTerm free)
    (hMember : Γ ⊢ₘ[T] code ∈ₘ syntax_formula_code_set_term) :
    Γ ⊢ₘ[T] code ∈ₘ ωₘ := by
  let symbols : SetOpenTerm free := NonlogicalSymₘ
  have hSubset : Γ ⊢ₘ[T] symbols ⊆ₘ NonlogicalSymₘ := by
    simpa [symbols] using
      FirstOrder.Derives.theory_weaken hT
        (related_nonlogical_symbol_set_subset_derives (Γ := Γ))
  have hDefinition := FirstOrder.Derives.theory_weaken
    (fun hSentence => hT
      (semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
        hSentence))
    (related_formula_set_definition_instance_derives
      (Γ := Γ) symbols syntax_formula_code_set_term)
  have hIff := FirstOrder.Derives.imp_elim hDefinition hSubset
  have hSetEq :
      (syntax_formula_code_set_term : SetOpenTerm free) =
        RelFormulaCodeₘ(symbols) := by
    induction free <;> rfl
  have hSpec := FirstOrder.Derives.iff_elim_left hIff (by
    rw [hSetEq]
    exact Metatheory.Derives.equality_refl
      (T := T) (Γ := Γ) (RelFormulaCodeₘ(symbols)))
  have hAt := FirstOrder.Derives.forall_elim
    (term := code) hSpec
  have hAt' : Γ ⊢ₘ[T]
      code ∈ₘ syntax_formula_code_set_term ↔ₘ
        related_formula_code_condition symbols code := by
    simpa [related_formula_set_spec, related_formula_code_condition,
      Formula.instantiateFreeTop,
      Substitution.instantiateFreeTop, Formula.substitute,
      Formula.substituteMapped, Term.substituteFree, Term.substitute,
      Term.substituteMapped, Arguments.substituteMapped,
      Term.weakenFree, Term.rename, Renaming.weakenFree, Renaming.free,
      Term.renameMapped, VariableRenaming.weaken, VariableRenaming.comp,
      VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.liftFree, VariableSubstitution.weakenBound,
      VariableSubstitution.boundId, VariableSubstitution.freeId] using! hAt
  have hCondition : Γ ⊢ₘ[T]
      related_formula_code_condition symbols code :=
    FirstOrder.Derives.iff_elim_left hAt' hMember
  let body : SetOpenFormula (SetSort.set :: free) :=
    related_formula_code_atₘ(
      symbols.weakenFree SetSort.set,
      (.fvar .here : SetTerm [] (SetSort.set :: free)),
      code.weakenFree SetSort.set)
  have hExist : Γ ⊢ₘ[T] body.existsFreeTop SetSort.set := by
    simpa [body, related_formula_code_condition] using hCondition
  apply FirstOrder.Derives.exists_elim hExist
  let Δ : Context signature (SetSort.set :: free) :=
    body :: FreshVariable.extendContext SetSort.set Γ
  have hBody : Δ ⊢ₘ[T] body :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hAtBody : Δ ⊢ₘ[T]
      related_formula_code_atₘ(
        symbols.weakenFree SetSort.set,
        (.fvar .here : SetTerm [] (SetSort.set :: free)),
        code.weakenFree SetSort.set) := by
    simpa [body] using hBody
  have hBodyCondition := FirstOrder.Derives.iff_elim_left
    (FirstOrder.Derives.theory_weaken
      (fun hSentence => hT
        (semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
          hSentence))
      (related_formula_code_at_definition_instance_derives
        (Γ := Δ)
        (symbols.weakenFree SetSort.set)
        (.fvar .here : SetTerm [] (SetSort.set :: free))
        (code.weakenFree SetSort.set))) hAtBody
  have hCodeOmega : Δ ⊢ₘ[T]
      code.weakenFree SetSort.set ∈ₘ ωₘ :=
    FirstOrder.Derives.conj_elim_right
      (FirstOrder.Derives.conj_elim_left hBodyCondition)
  simpa [Δ, body] using hCodeOmega

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
