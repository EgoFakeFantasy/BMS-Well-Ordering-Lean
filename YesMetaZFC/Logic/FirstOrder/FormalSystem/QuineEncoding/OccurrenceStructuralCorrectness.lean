import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaStructuralCorrectness
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped FormalSystem.Symbols
set_option autoImplicit false
mutual
def Term.free_index_occurs {σ : Signature} {bound free : SortContext σ}
    {sort : σ.SortSymbol} (index : Nat) : Term σ bound free sort → Prop
  | .bvar _ => False
  | .fvar entry => entry.index = index
  | .app _ arguments => Arguments.free_index_occurs index arguments
def Arguments.free_index_occurs {σ : Signature} {bound free : SortContext σ}
    {sorts : List σ.SortSymbol} (index : Nat) : Arguments σ bound free sorts → Prop
  | .nil => False
  | .cons head tail =>
      Term.free_index_occurs index head ∨
        Arguments.free_index_occurs index tail
def Formula.free_index_occurs {σ : Signature} {bound free : SortContext σ}
    (index : Nat) : Formula σ bound free → Prop
  | .falsum => False
  | .truth => False
  | .rel _ arguments => Arguments.free_index_occurs index arguments
  | .equal left right =>
      Term.free_index_occurs index left ∨
        Term.free_index_occurs index right
  | .neg body => Formula.free_index_occurs index body
  | .conj left right =>
      Formula.free_index_occurs index left ∨
        Formula.free_index_occurs index right
  | .disj left right =>
      Formula.free_index_occurs index left ∨
        Formula.free_index_occurs index right
  | .imp left right =>
      Formula.free_index_occurs index left ∨
        Formula.free_index_occurs index right
  | .iff left right =>
      Formula.free_index_occurs index left ∨
        Formula.free_index_occurs index right
  | .forallE _ body => Formula.free_index_occurs index body
  | .existsE _ body => Formula.free_index_occurs index body
end
private theorem finite_numeral_mem_expression_encoding {free : SetContext} {Γ : Context signature free} (number : Nat) :
    Γ ⊢ₘ[expression_encoding_theory] (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ :=
  FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (finite_numeral_mem_formal_language_encoding_theory
      (Γ := Γ) number)
private theorem structural_node_mem_expression_encoding_leaf {free : SetContext} {Γ : Context signature free}
    (tag : StructuralCodeTag) (fields : List (SetOpenTerm free))
    (hFields : ∀ field, field ∈ fields →
      Γ ⊢ₘ[formal_language_encoding_theory] field ∈ₘ ωₘ) :
    Γ ⊢ₘ[expression_encoding_theory]
      structural_node_code_term tag fields ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (structural_node_code_mem_formal_language_encoding_theory
      (Γ := Γ) tag fields hFields)
private theorem term_quote_code_mem_expression_encoding {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (quote_term term : SetOpenTerm []) ∈ₘ ωₘ := by
  exact FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (term_code_at_code_mem_of_derives
      (numₘ(bound.length))
      (quote_term term : SetOpenTerm [])
      (quote_term_code_at term))
private theorem arguments_quote_code_mem_expression_encoding {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (quote_arguments arguments : SetOpenTerm []) ∈ₘ ωₘ := by
  exact FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (term_list_code_at_code_mem_of_derives
      (numₘ(bound.length))
      (numₘ(sorts.length))
      (quote_arguments arguments : SetOpenTerm [])
      (quote_arguments_term_list_code_at arguments))
private theorem arguments_free_index_occurs_nil {σ : Signature}
    {bound free : SortContext σ}
    (index : Nat)
    (arguments : Arguments σ bound free []) :
    ¬ Arguments.free_index_occurs index arguments := by
  cases arguments
  simp [Arguments.free_index_occurs]
private theorem arguments_free_index_occurs_cast {σ : Signature}
    {bound free : SortContext σ}
    {sorts₁ sorts₂ : List σ.SortSymbol}
    (index : Nat) (h : sorts₁ = sorts₂)
    (arguments : Arguments σ bound free sorts₁) :
    Arguments.free_index_occurs index (h ▸ arguments) ↔
      Arguments.free_index_occurs index arguments := by
  subst h
  rfl
private theorem free_variable_occurs_term_leaf (index : Nat) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(
        syntax_code_kind_term .term,
        numₘ(index),
        (free_var_codeₘ(numₘ(index)) : SetOpenTerm [])) := by
  apply FirstOrder.Derives.iff_elim_right
    (free_variable_occurs_definition_instance_derives
      (Γ := ([] : Context signature []))
      (syntax_code_kind_term .term)
      (numₘ(index))
      (free_var_codeₘ(numₘ(index)) : SetOpenTerm []))
  apply FirstOrder.Derives.conj_intro
  · apply FirstOrder.Derives.conj_intro
    · apply FirstOrder.Derives.conj_intro
      · exact finite_numeral_mem_expression_encoding (Γ := []) 0
      · exact finite_numeral_mem_expression_encoding (Γ := []) index
    · exact structural_node_mem_expression_encoding_leaf
        (Γ := []) StructuralCodeTag.freeVariable [numₘ(index)] (by
          intro field hField
          simp only [List.mem_cons, List.not_mem_nil] at hField
          rcases hField with rfl | hField
          · exact finite_numeral_mem_formal_language_encoding_theory
              (Γ := []) index
          · contradiction)
  · apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.conj_intro
    · exact Metatheory.Derives.equality_refl
        (syntax_code_kind_term .term : SetOpenTerm [])
    · apply FirstOrder.Derives.disj_intro_left
      apply FirstOrder.Derives.exists_intro (numₘ(index) : SetOpenTerm [])
      simpa [free_variable_occurs_definition_instance,
        free_variable_occurs_condition,
        structural_list_code_term, Formula.substituteFree,
        Substitution.free_map, Formula.substitute,
        Formula.substituteMapped, Term.substituteFree,
        Term.substitute, Term.substituteMapped,
        Arguments.substituteMapped, Term.instantiateFreeTop,
        Arguments.instantiateFreeTop, Substitution.instantiateFreeTop,
        VariableSubstitution.instantiateFreeTop,
        structural_raw_node_code_term, godel_pairing_term,
        free_variable_code_term, term_weaken_free_two,
        term_weaken_free_three,
        VariableSubstitution.liftFree] using! FirstOrder.Derives.conj_intro
        (finite_numeral_mem_expression_encoding (Γ := []) index)
        (FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (free_var_codeₘ(numₘ(index)) : SetOpenTerm []))
            (Metatheory.Derives.equality_refl
            (numₘ(index) : SetOpenTerm [])))
private theorem gq_occurrence_closed_two_weaken_substitute
    (τ : VariableSubstitution signature [SetSort.set, SetSort.set] [] [])
    {resultSort : signature.SortSymbol}
    (term : Term signature [] [] resultSort) :
    Term.substituteMapped VariableSubstitution.boundId τ
        ((term.weakenFree SetSort.set).weakenFree SetSort.set) =
      term := by
  exact Term.rec
    (motive_1 := fun _ term =>
      Term.substituteMapped VariableSubstitution.boundId τ
          ((term.weakenFree SetSort.set).weakenFree SetSort.set) =
        term)
    (motive_2 := fun _ arguments =>
      Arguments.substituteMapped VariableSubstitution.boundId τ
          ((arguments.weakenFree SetSort.set).weakenFree SetSort.set) =
        arguments)
    (fun entry => by cases entry)
    (fun entry => by cases entry)
    (fun function arguments ih => by
      change
        Term.app function
            (Arguments.substituteMapped VariableSubstitution.boundId τ
              ((arguments.weakenFree SetSort.set).weakenFree SetSort.set)) =
          Term.app function arguments
      rw [ih])
    rfl
    (fun head tail ihHead ihTail => by
      change
        Arguments.cons
            (Term.substituteMapped VariableSubstitution.boundId τ
              ((head.weakenFree SetSort.set).weakenFree SetSort.set))
            (Arguments.substituteMapped VariableSubstitution.boundId τ
              ((tail.weakenFree SetSort.set).weakenFree SetSort.set)) =
          Arguments.cons head tail
      rw [ihHead, ihTail])
    term
private theorem gq_closed_one_weaken_substitute
    (τ : VariableSubstitution signature [SetSort.set] [] [])
    {resultSort : signature.SortSymbol}
    (term : Term signature [] [] resultSort) :
    Term.substituteMapped VariableSubstitution.boundId τ
        (term.weakenFree SetSort.set) =
      term := by
  exact Term.rec
    (motive_1 := fun _ term =>
      Term.substituteMapped VariableSubstitution.boundId τ
          (term.weakenFree SetSort.set) =
        term)
    (motive_2 := fun _ arguments =>
      Arguments.substituteMapped VariableSubstitution.boundId τ
          (arguments.weakenFree SetSort.set) =
        arguments)
    (fun entry => by cases entry)
    (fun entry => by cases entry)
    (fun function arguments ih => by
      change
        Term.app function
            (Arguments.substituteMapped VariableSubstitution.boundId τ
              (arguments.weakenFree SetSort.set)) =
          Term.app function arguments
      rw [ih])
    rfl
    (fun head tail ihHead ihTail => by
      change
        Arguments.cons
            (Term.substituteMapped VariableSubstitution.boundId τ
              (head.weakenFree SetSort.set))
            (Arguments.substituteMapped VariableSubstitution.boundId τ
              (tail.weakenFree SetSort.set)) =
          Arguments.cons head tail
      rw [ihHead, ihTail])
    term
private theorem free_variable_occurs_application_intro
    (index code arity symbol arguments : SetOpenTerm [])
    (hIndex :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        index ∈ₘ ωₘ)
    (hCodeMem :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ∈ₘ ωₘ)
    (hArity :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        arity ∈ₘ ωₘ)
    (hSymbol :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        symbol ∈ₘ ωₘ)
    (hOccurrence :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        free_var_occursₘ(
          syntax_code_kind_term .termList, index, arguments))
    (hCode :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ≐ₘ app_codeₘ(arity, symbol, arguments)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(syntax_code_kind_term .term, index, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (free_variable_occurs_definition_instance_derives
      (Γ := ([] : Context signature []))
      (syntax_code_kind_term .term) index code)
  apply FirstOrder.Derives.conj_intro
  · apply FirstOrder.Derives.conj_intro
    · apply FirstOrder.Derives.conj_intro
      · exact finite_numeral_mem_expression_encoding (Γ := []) 0
      · exact hIndex
    · exact hCodeMem
  · apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.conj_intro
    · exact Metatheory.Derives.equality_refl
        (syntax_code_kind_term .term : SetOpenTerm [])
    · apply FirstOrder.Derives.disj_intro_right
      dsimp
      apply FirstOrder.Derives.exists_intro arity
      rw [Formula.instantiateTop_abstractFreeTop,
        Formula.instantiateFreeTop_existsFreeTop]
      apply FirstOrder.Derives.exists_intro symbol
      rw [Formula.substituteFree_existsFreeTop]
      rw [Formula.instantiateTop_abstractFreeTop,
        Formula.instantiateFreeTop_existsFreeTop]
      apply FirstOrder.Derives.exists_intro arguments
      rw [Formula.instantiateTop_abstractFreeTop]
      rw [three_free_substitution_beta]
      simp only [ Formula.substituteFree]
      let τ : VariableSubstitution signature
          [SetSort.set, SetSort.set, SetSort.set] [] [] :=
        VariableSubstitution.cons arguments
          (VariableSubstitution.cons symbol
            (VariableSubstitution.cons arity VariableSubstitution.empty))
      have hIndexClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              (term_weaken_free_three index) = index := by
        change
          Term.substituteMapped VariableSubstitution.boundId τ
              (((index.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
                SetSort.set) = index
        exact gq_closed_three_weaken_substitute τ index
      have hCodeClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              (term_weaken_free_three code) = code := by
        change
          Term.substituteMapped VariableSubstitution.boundId τ
              (((code.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
                SetSort.set) = code
        exact gq_closed_three_weaken_substitute τ code
      have hArityClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              (term_weaken_free_three arity) = arity := by
        change
          Term.substituteMapped VariableSubstitution.boundId τ
              (((arity.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
                SetSort.set) = arity
        exact gq_closed_three_weaken_substitute τ arity
      have hSymbolClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              (term_weaken_free_three symbol) = symbol := by
        change
          Term.substituteMapped VariableSubstitution.boundId τ
              (((symbol.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
                SetSort.set) = symbol
        exact gq_closed_three_weaken_substitute τ symbol
      have hArgumentsClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              (term_weaken_free_three arguments) = arguments := by
        change
          Term.substituteMapped VariableSubstitution.boundId τ
              (((arguments.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
                SetSort.set) = arguments
        exact gq_closed_three_weaken_substitute τ arguments
      have hAppCodeClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              (term_weaken_free_three
                (app_codeₘ(arity, symbol, arguments) : SetOpenTerm [])) =
            app_codeₘ(arity, symbol, arguments) :=
        gq_closed_three_weaken_substitute τ
          (app_codeₘ(arity, symbol, arguments) : SetOpenTerm [])
      let body : SetOpenFormula
          [SetSort.set, SetSort.set, SetSort.set] :=
        ((.fvar (.there (.there .here)) ∈ₘ ωₘ) ∧ₘ
          (.fvar (.there .here) ∈ₘ ωₘ)) ∧ₘ
            ((term_weaken_free_three code ≐ₘ
                app_codeₘ(.fvar (.there (.there .here)),
                  .fvar (.there .here), .fvar .here)) ∧ₘ
              free_var_occursₘ(
                syntax_code_kind_term .termList,
                term_weaken_free_three index, .fvar .here))
      change ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        Formula.substitute (Substitution.free_map τ) body
      have hBody :
          Formula.substitute (Substitution.free_map τ) body =
            ((arity ∈ₘ ωₘ) ∧ₘ (symbol ∈ₘ ωₘ)) ∧ₘ
              ((code ≐ₘ app_codeₘ(arity, symbol, arguments)) ∧ₘ
                free_var_occursₘ(
                  syntax_code_kind_term .termList, index, arguments)) := by
        simp [body, Formula.substitute, Formula.substituteMapped,
          Substitution.free_map, VariableSubstitution.cons, Term.substituteMapped,
          Arguments.substituteMapped,
          structural_list_code_term, application_code_term,
          structural_node_code_term, structural_raw_node_code_term,
          godel_pairing_term, τ, hIndexClosed, hCodeClosed]
      rw [hBody]
      exact FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro hArity hSymbol)
        (FirstOrder.Derives.conj_intro hCode hOccurrence)
private theorem free_variable_occurs_cons_intro
    (index code head tail : SetOpenTerm [])
    (hIndex :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        index ∈ₘ ωₘ)
    (hCodeMem :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ∈ₘ ωₘ)
    (hCode :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ≐ₘ code_consₘ(head, tail))
    (hBranch :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        (free_var_occursₘ(syntax_code_kind_term .term, index, head) ∨ₘ
          free_var_occursₘ(syntax_code_kind_term .termList, index, tail))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(syntax_code_kind_term .termList, index, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (free_variable_occurs_definition_instance_derives
      (Γ := ([] : Context signature []))
      (syntax_code_kind_term .termList) index code)
  apply FirstOrder.Derives.conj_intro
  · apply FirstOrder.Derives.conj_intro
    · apply FirstOrder.Derives.conj_intro
      · exact finite_numeral_mem_expression_encoding (Γ := []) 1
      · exact hIndex
    · exact hCodeMem
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.conj_intro
    · exact Metatheory.Derives.equality_refl
        (syntax_code_kind_term .termList : SetOpenTerm [])
    · dsimp
      apply FirstOrder.Derives.exists_intro head
      rw [Formula.instantiateTop_abstractFreeTop,
        Formula.instantiateFreeTop_existsFreeTop]
      apply FirstOrder.Derives.exists_intro tail
      rw [Formula.instantiateTop_abstractFreeTop]
      rw [two_free_substitution_beta]
      simp only [ Formula.substituteFree]
      let τ : VariableSubstitution signature
          [SetSort.set, SetSort.set] [] [] :=
        VariableSubstitution.cons tail
          (VariableSubstitution.cons head VariableSubstitution.empty)
      have hIndexClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              ((index.weakenFree SetSort.set).weakenFree SetSort.set) = index := by
        exact gq_occurrence_closed_two_weaken_substitute τ index
      have hCodeClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              ((code.weakenFree SetSort.set).weakenFree SetSort.set) = code := by
        exact gq_occurrence_closed_two_weaken_substitute τ code
      have hHeadClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              ((head.weakenFree SetSort.set).weakenFree SetSort.set) = head := by
        exact gq_occurrence_closed_two_weaken_substitute τ head
      have hTailClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              ((tail.weakenFree SetSort.set).weakenFree SetSort.set) = tail := by
        exact gq_occurrence_closed_two_weaken_substitute τ tail
      have hArgsHead :
          Arguments.substituteMapped VariableSubstitution.boundId τ
              (Arguments.cons
                (syntax_code_kind_term .term : SetOpenTerm [SetSort.set, SetSort.set])
                (Arguments.cons
                  ((index.weakenFree SetSort.set).weakenFree SetSort.set)
                  (Arguments.cons
                    (.fvar (.there .here)) Arguments.nil))) =
            Arguments.cons (syntax_code_kind_term .term)
              (Arguments.cons index (Arguments.cons head Arguments.nil)) := by
        simp [Arguments.substituteMapped, Term.substituteMapped,
          VariableSubstitution.cons, τ,
          hIndexClosed]
      have hArgsTail :
          Arguments.substituteMapped VariableSubstitution.boundId τ
              (Arguments.cons
                (syntax_code_kind_term .termList : SetOpenTerm [SetSort.set, SetSort.set])
                (Arguments.cons
                  ((index.weakenFree SetSort.set).weakenFree SetSort.set)
                  (Arguments.cons
                    (.fvar (.here : Variable [SetSort.set, SetSort.set] SetSort.set))
                    Arguments.nil))) =
            Arguments.cons (syntax_code_kind_term .termList)
              (Arguments.cons index (Arguments.cons tail Arguments.nil)) := by
        simp [Arguments.substituteMapped, Term.substituteMapped,
          VariableSubstitution.cons, τ,
          hIndexClosed]
      have hCodeConsSub :
          Term.substituteMapped VariableSubstitution.boundId τ
              (code_consₘ(.fvar (.there .here), .fvar .here) :
                SetOpenTerm [SetSort.set, SetSort.set]) =
            code_consₘ(head, tail) := by
        simp [Term.substituteMapped, Arguments.substituteMapped,
          VariableSubstitution.cons,
          structural_raw_node_code_term, godel_pairing_term, τ]
      let body : SetOpenFormula [SetSort.set, SetSort.set] :=
        ((((code.weakenFree SetSort.set).weakenFree SetSort.set) ≐ₘ
            code_consₘ(.fvar (.there .here), .fvar .here)) ∧ₘ
          (free_var_occursₘ(
              syntax_code_kind_term .term,
              (index.weakenFree SetSort.set).weakenFree SetSort.set,
              .fvar (.there .here)) ∨ₘ
            free_var_occursₘ(
              syntax_code_kind_term .termList,
              (index.weakenFree SetSort.set).weakenFree SetSort.set,
              .fvar .here)))
      change ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        Formula.substitute (Substitution.free_map τ) body
      have hBody :
          Formula.substitute (Substitution.free_map τ) body =
            ((code ≐ₘ code_consₘ(head, tail)) ∧ₘ
              (free_var_occursₘ(
                  syntax_code_kind_term .term, index, head) ∨ₘ
                free_var_occursₘ(
                  syntax_code_kind_term .termList, index, tail))) := by
        simp only [body, Formula.substitute, Formula.substituteMapped,
          Substitution.free_map, τ]
        rw [hCodeClosed, hCodeConsSub, hArgsHead, hArgsTail]
      rw [hBody]
      exact FirstOrder.Derives.conj_intro hCode hBranch
private theorem free_variable_occurs_binary_formula_intro
    (tag : StructuralCodeTag)
    (hTag : tag = .equality ∨ tag = .membership)
    (index code left right : SetOpenTerm [])
    (hIndex :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        index ∈ₘ ωₘ)
    (hCodeMem :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ∈ₘ ωₘ)
    (hCode :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ≐ₘ structural_node_code_term tag [left, right])
    (hBranch :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        (free_var_occursₘ(syntax_code_kind_term .term, index, left) ∨ₘ
          free_var_occursₘ(syntax_code_kind_term .term, index, right))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(syntax_code_kind_term .formula, index, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (free_variable_occurs_definition_instance_derives
      (Γ := ([] : Context signature []))
      (syntax_code_kind_term .formula) index code)
  apply FirstOrder.Derives.conj_intro
  · apply FirstOrder.Derives.conj_intro
    · apply FirstOrder.Derives.conj_intro
      · exact finite_numeral_mem_expression_encoding (Γ := []) 2
      · exact hIndex
    · exact hCodeMem
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.conj_intro
    · exact Metatheory.Derives.equality_refl
        (syntax_code_kind_term .formula : SetOpenTerm [])
    · rcases hTag with hTag | hTag
      all_goals
        first
        | have : tag = .equality := hTag
          apply FirstOrder.Derives.disj_intro_left
        | have : tag = .membership := hTag
          apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.disj_intro_left
      all_goals
        dsimp
        apply FirstOrder.Derives.exists_intro left
        rw [Formula.instantiateTop_abstractFreeTop,
          Formula.instantiateFreeTop_existsFreeTop]
        apply FirstOrder.Derives.exists_intro right
        rw [Formula.instantiateTop_abstractFreeTop]
        rw [two_free_substitution_beta]
        simp only [ Formula.substituteFree]
        let τ : VariableSubstitution signature
          [SetSort.set, SetSort.set] [] [] :=
          VariableSubstitution.cons right
            (VariableSubstitution.cons left VariableSubstitution.empty)
        have hIndexClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              ((index.weakenFree SetSort.set).weakenFree SetSort.set) = index := by
          exact gq_occurrence_closed_two_weaken_substitute τ index
        have hCodeClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              ((code.weakenFree SetSort.set).weakenFree SetSort.set) = code := by
          exact gq_occurrence_closed_two_weaken_substitute τ code
        have hTargetSub :
          Term.substituteMapped VariableSubstitution.boundId τ
              (structural_node_code_term tag
                [.fvar (.there .here), .fvar .here] :
                SetOpenTerm [SetSort.set, SetSort.set]) =
            structural_node_code_term tag [left, right] := by
          simp [Term.substituteMapped, Arguments.substituteMapped,
            VariableSubstitution.cons,
            structural_node_code_term, structural_list_code_term,
            structural_raw_node_code_term, godel_pairing_term, τ]
        have hBoundId :
            (VariableRenaming.comp
              (outer := (@VariableRenaming.id signature.SortSymbol []))
              (inner := (@VariableRenaming.id signature.SortSymbol [])) :
                VariableRenaming (S := signature.SortSymbol) [] []) =
              (@VariableRenaming.id signature.SortSymbol []) := by
          funext resultSort entry
          cases entry
        have hRename (term : SetOpenTerm []) :
            Term.renameMapped
                (VariableRenaming.comp
                  (outer := (@VariableRenaming.id signature.SortSymbol []))
                  (inner := (@VariableRenaming.id signature.SortSymbol [])))
                (VariableRenaming.comp
                  (outer := VariableRenaming.weaken SetSort.set)
                  (inner := VariableRenaming.weaken SetSort.set)) term =
              (term.weakenFree SetSort.set).weakenFree SetSort.set := by
          rw [hBoundId]
          exact Term.renameMapped_two_weakenFree term
        have hArgsLeft :
          Arguments.substituteMapped VariableSubstitution.boundId τ
              (Arguments.cons
                (syntax_code_kind_term .term : SetOpenTerm [SetSort.set, SetSort.set])
                (Arguments.cons
                  ((index.weakenFree SetSort.set).weakenFree SetSort.set)
                  (Arguments.cons
                    (.fvar (.there .here)) Arguments.nil))) =
            Arguments.cons (syntax_code_kind_term .term)
              (Arguments.cons index (Arguments.cons left Arguments.nil)) := by
          simp [Arguments.substituteMapped, Term.substituteMapped,
            VariableSubstitution.cons, τ,
            hIndexClosed]
        have hArgsRight :
          Arguments.substituteMapped VariableSubstitution.boundId τ
              (Arguments.cons
                (syntax_code_kind_term .term : SetOpenTerm [SetSort.set, SetSort.set])
                (Arguments.cons
                  ((index.weakenFree SetSort.set).weakenFree SetSort.set)
                  (Arguments.cons
                    (.fvar (.here : Variable [SetSort.set, SetSort.set] SetSort.set))
                    Arguments.nil))) =
            Arguments.cons (syntax_code_kind_term .term)
              (Arguments.cons index (Arguments.cons right Arguments.nil)) := by
          simp [Arguments.substituteMapped, Term.substituteMapped,
            VariableSubstitution.cons, τ,
            hIndexClosed]
        let body : SetOpenFormula [SetSort.set, SetSort.set] :=
        ((((code.weakenFree SetSort.set).weakenFree SetSort.set) ≐ₘ
            structural_node_code_term tag
              [.fvar (.there .here), .fvar .here]) ∧ₘ
          (free_var_occursₘ(
              syntax_code_kind_term .term,
              (index.weakenFree SetSort.set).weakenFree SetSort.set,
              .fvar (.there .here)) ∨ₘ
            free_var_occursₘ(
              syntax_code_kind_term .term,
              (index.weakenFree SetSort.set).weakenFree SetSort.set,
              .fvar .here)))
        have hBody :
          Formula.substitute (Substitution.free_map τ) body =
            ((code ≐ₘ structural_node_code_term tag [left, right]) ∧ₘ
              (free_var_occursₘ(syntax_code_kind_term .term, index, left) ∨ₘ
                free_var_occursₘ(syntax_code_kind_term .term, index, right))) := by
          simp only [body, Formula.substitute, Formula.substituteMapped,
            Substitution.free_map, τ]
          rw [hCodeClosed, hTargetSub, hArgsLeft, hArgsRight]
        have hResult :
            ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
              Formula.substitute (Substitution.free_map τ) body := by
          rw [hBody]
          exact FirstOrder.Derives.conj_intro hCode hBranch
        dsimp
        simpa [body, τ, hRename, term_weaken_free_two, hTag] using hResult
private theorem free_variable_occurs_unary_formula_intro
    (tag : StructuralCodeTag)
    (hTag : tag = .negation ∨ tag = .universal)
    (index code body : SetOpenTerm [])
    (hIndex :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        index ∈ₘ ωₘ)
    (hCodeMem :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ∈ₘ ωₘ)
    (hCode :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ≐ₘ structural_node_code_term tag [body])
    (hBody :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        free_var_occursₘ(syntax_code_kind_term .formula, index, body)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(syntax_code_kind_term .formula, index, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (free_variable_occurs_definition_instance_derives
      (Γ := ([] : Context signature []))
      (syntax_code_kind_term .formula) index code)
  apply FirstOrder.Derives.conj_intro
  · apply FirstOrder.Derives.conj_intro
    · apply FirstOrder.Derives.conj_intro
      · exact finite_numeral_mem_expression_encoding (Γ := []) 2
      · exact hIndex
    · exact hCodeMem
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.conj_intro
    · exact Metatheory.Derives.equality_refl
        (syntax_code_kind_term .formula : SetOpenTerm [])
    · rcases hTag with hTag | hTag
      all_goals
        first
        | have : tag = .negation := hTag
          apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.disj_intro_left
        | have : tag = .universal := hTag
          apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.disj_intro_right
      all_goals
        dsimp
        apply FirstOrder.Derives.exists_intro body
        rw [Formula.instantiateTop_abstractFreeTop]
        let τ : VariableSubstitution signature
            [SetSort.set] [] [] :=
          VariableSubstitution.instantiateFreeTop body
        have hIndexClosed :
            Term.substituteMapped VariableSubstitution.boundId τ
                (index.weakenFree SetSort.set) = index :=
          gq_closed_one_weaken_substitute τ index
        have hCodeClosed :
            Term.substituteMapped VariableSubstitution.boundId τ
                (code.weakenFree SetSort.set) = code :=
          gq_closed_one_weaken_substitute τ code
        have hTargetSub :
            Term.substituteMapped VariableSubstitution.boundId τ
                (structural_node_code_term tag
                  [.fvar .here] : SetOpenTerm [SetSort.set]) =
              structural_node_code_term tag [body] := by
          simp [Term.substituteMapped, Arguments.substituteMapped, τ,
            VariableSubstitution.instantiateFreeTop,
            structural_node_code_term, structural_list_code_term,
            structural_raw_node_code_term, godel_pairing_term]
        have hArgs :
            Arguments.substituteMapped VariableSubstitution.boundId τ
                (Arguments.cons
                  (syntax_code_kind_term .formula : SetOpenTerm [SetSort.set])
                  (Arguments.cons
                    (index.weakenFree SetSort.set)
                    (Arguments.cons (.fvar .here) Arguments.nil))) =
              Arguments.cons (syntax_code_kind_term .formula)
                (Arguments.cons index (Arguments.cons body Arguments.nil)) := by
          simp [Arguments.substituteMapped, Term.substituteMapped, τ,
            VariableSubstitution.instantiateFreeTop, hIndexClosed]
        simp only [Formula.instantiateFreeTop]
        let bodyFormula : SetOpenFormula [SetSort.set] :=
          (((code.weakenFree SetSort.set) ≐ₘ
              structural_node_code_term tag [.fvar .here]) ∧ₘ
            free_var_occursₘ(
              syntax_code_kind_term .formula,
              index.weakenFree SetSort.set, .fvar .here))
        have hFormula :
            Formula.substitute (Substitution.free_map τ) bodyFormula =
              ((code ≐ₘ structural_node_code_term tag [body]) ∧ₘ
                free_var_occursₘ(
                  syntax_code_kind_term .formula, index, body)) := by
          simp only [bodyFormula, Formula.substitute, Formula.substituteMapped,
            Substitution.free_map, τ]
          rw [hCodeClosed, hTargetSub, hArgs]
        have hResult :
            ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
              Formula.substitute (Substitution.free_map τ) bodyFormula := by
          rw [hFormula]
          exact FirstOrder.Derives.conj_intro hCode hBody
        simpa [bodyFormula, τ, hTag] using! hResult
private theorem free_variable_occurs_implication_formula_intro
    (index code left right : SetOpenTerm [])
    (hIndex :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        index ∈ₘ ωₘ)
    (hCodeMem :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ∈ₘ ωₘ)
    (hCode :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ≐ₘ imp_codeₘ(left, right))
    (hBranch :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        (free_var_occursₘ(
            syntax_code_kind_term .formula, index, left) ∨ₘ
          free_var_occursₘ(
            syntax_code_kind_term .formula, index, right))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(syntax_code_kind_term .formula, index, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (free_variable_occurs_definition_instance_derives
      (Γ := ([] : Context signature []))
      (syntax_code_kind_term .formula) index code)
  apply FirstOrder.Derives.conj_intro
  · apply FirstOrder.Derives.conj_intro
    · apply FirstOrder.Derives.conj_intro
      · exact finite_numeral_mem_expression_encoding (Γ := []) 2
      · exact hIndex
    · exact hCodeMem
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.conj_intro
    · exact Metatheory.Derives.equality_refl
        (syntax_code_kind_term .formula : SetOpenTerm [])
    · apply FirstOrder.Derives.disj_intro_right
      apply FirstOrder.Derives.disj_intro_right
      apply FirstOrder.Derives.disj_intro_right
      apply FirstOrder.Derives.disj_intro_right
      apply FirstOrder.Derives.disj_intro_left
      dsimp
      apply FirstOrder.Derives.exists_intro left
      rw [Formula.instantiateTop_abstractFreeTop,
        Formula.instantiateFreeTop_existsFreeTop]
      apply FirstOrder.Derives.exists_intro right
      rw [Formula.instantiateTop_abstractFreeTop]
      rw [two_free_substitution_beta]
      simp only [ Formula.substituteFree]
      let τ : VariableSubstitution signature
          [SetSort.set, SetSort.set] [] [] :=
        VariableSubstitution.cons right
          (VariableSubstitution.cons left VariableSubstitution.empty)
      have hIndexClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              ((index.weakenFree SetSort.set).weakenFree SetSort.set) = index :=
        gq_occurrence_closed_two_weaken_substitute τ index
      have hCodeClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              ((code.weakenFree SetSort.set).weakenFree SetSort.set) = code :=
        gq_occurrence_closed_two_weaken_substitute τ code
      have hTargetSub :
          Term.substituteMapped VariableSubstitution.boundId τ
              (imp_codeₘ(.fvar (.there .here), .fvar .here) :
                SetOpenTerm [SetSort.set, SetSort.set]) =
            imp_codeₘ(left, right) := by
        simp [Term.substituteMapped, Arguments.substituteMapped,
          VariableSubstitution.cons,
          implication_formula_code_term,
          structural_node_code_term, structural_list_code_term,
          structural_raw_node_code_term, godel_pairing_term, τ]
      have hBoundId :
          (VariableRenaming.comp
            (outer := (@VariableRenaming.id signature.SortSymbol []))
            (inner := (@VariableRenaming.id signature.SortSymbol [])) :
              VariableRenaming (S := signature.SortSymbol) [] []) =
            (@VariableRenaming.id signature.SortSymbol []) := by
        funext resultSort entry
        cases entry
      have hRename (term : SetOpenTerm []) :
          Term.renameMapped
              (VariableRenaming.comp
                (outer := (@VariableRenaming.id signature.SortSymbol []))
                (inner := (@VariableRenaming.id signature.SortSymbol [])))
              (VariableRenaming.comp
                (outer := VariableRenaming.weaken SetSort.set)
                (inner := VariableRenaming.weaken SetSort.set)) term =
            (term.weakenFree SetSort.set).weakenFree SetSort.set := by
        rw [hBoundId]
        exact Term.renameMapped_two_weakenFree term
      have hArgsLeft :
          Arguments.substituteMapped VariableSubstitution.boundId τ
              (Arguments.cons
                (syntax_code_kind_term .formula :
                  SetOpenTerm [SetSort.set, SetSort.set])
                (Arguments.cons
                  ((index.weakenFree SetSort.set).weakenFree SetSort.set)
                  (Arguments.cons
                    (.fvar (.there .here)) Arguments.nil))) =
            Arguments.cons (syntax_code_kind_term .formula)
              (Arguments.cons index (Arguments.cons left Arguments.nil)) := by
        simp [Arguments.substituteMapped, Term.substituteMapped,
          VariableSubstitution.cons, τ,
          hIndexClosed]
      have hArgsRight :
          Arguments.substituteMapped VariableSubstitution.boundId τ
              (Arguments.cons
                (syntax_code_kind_term .formula :
                  SetOpenTerm [SetSort.set, SetSort.set])
                (Arguments.cons
                  ((index.weakenFree SetSort.set).weakenFree SetSort.set)
                  (Arguments.cons
                    (.fvar (.here :
                      Variable [SetSort.set, SetSort.set] SetSort.set))
                    Arguments.nil))) =
            Arguments.cons (syntax_code_kind_term .formula)
              (Arguments.cons index (Arguments.cons right Arguments.nil)) := by
        simp [Arguments.substituteMapped, Term.substituteMapped,
          VariableSubstitution.cons, τ,
          hIndexClosed]
      let body : SetOpenFormula [SetSort.set, SetSort.set] :=
        ((((code.weakenFree SetSort.set).weakenFree SetSort.set) ≐ₘ
            imp_codeₘ(.fvar (.there .here), .fvar .here)) ∧ₘ
          (free_var_occursₘ(
              syntax_code_kind_term .formula,
              (index.weakenFree SetSort.set).weakenFree SetSort.set,
              .fvar (.there .here)) ∨ₘ
            free_var_occursₘ(
              syntax_code_kind_term .formula,
              (index.weakenFree SetSort.set).weakenFree SetSort.set,
              .fvar .here)))
      have hBody :
          Formula.substitute (Substitution.free_map τ) body =
            ((code ≐ₘ imp_codeₘ(left, right)) ∧ₘ
              (free_var_occursₘ(
                  syntax_code_kind_term .formula, index, left) ∨ₘ
                free_var_occursₘ(
                  syntax_code_kind_term .formula, index, right))) := by
        simp only [body, Formula.substitute, Formula.substituteMapped,
          Substitution.free_map, τ]
        rw [hCodeClosed, hTargetSub, hArgsLeft, hArgsRight]
      have hResult :
          ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
            Formula.substitute (Substitution.free_map τ) body := by
        rw [hBody]
        exact FirstOrder.Derives.conj_intro hCode hBranch
      dsimp
      simpa [body, τ, hRename] using! hResult
private theorem free_variable_occurs_predicate_formula_intro
    (index code arity symbol arguments : SetOpenTerm [])
    (hIndex :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        index ∈ₘ ωₘ)
    (hCodeMem :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ∈ₘ ωₘ)
    (hArity :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        arity ∈ₘ ωₘ)
    (hSymbol :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        symbol ∈ₘ ωₘ)
    (hArguments :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        free_var_occursₘ(
          syntax_code_kind_term .termList, index, arguments))
    (hCode :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ≐ₘ pred_codeₘ(arity, symbol, arguments)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(syntax_code_kind_term .formula, index, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (free_variable_occurs_definition_instance_derives
      (Γ := ([] : Context signature []))
      (syntax_code_kind_term .formula) index code)
  apply FirstOrder.Derives.conj_intro
  · apply FirstOrder.Derives.conj_intro
    · apply FirstOrder.Derives.conj_intro
      · exact finite_numeral_mem_expression_encoding (Γ := []) 2
      · exact hIndex
    · exact hCodeMem
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.conj_intro
    · exact Metatheory.Derives.equality_refl
        (syntax_code_kind_term .formula : SetOpenTerm [])
    · apply FirstOrder.Derives.disj_intro_right
      apply FirstOrder.Derives.disj_intro_right
      apply FirstOrder.Derives.disj_intro_left
      dsimp
      apply FirstOrder.Derives.exists_intro arity
      rw [Formula.instantiateTop_abstractFreeTop,
        Formula.instantiateFreeTop_existsFreeTop]
      apply FirstOrder.Derives.exists_intro symbol
      rw [Formula.substituteFree_existsFreeTop]
      rw [Formula.instantiateTop_abstractFreeTop,
        Formula.instantiateFreeTop_existsFreeTop]
      apply FirstOrder.Derives.exists_intro arguments
      rw [Formula.instantiateTop_abstractFreeTop]
      rw [three_free_substitution_beta]
      simp only [ Formula.substituteFree]
      let τ : VariableSubstitution signature
          [SetSort.set, SetSort.set, SetSort.set] [] [] :=
        VariableSubstitution.cons arguments
          (VariableSubstitution.cons symbol
            (VariableSubstitution.cons arity VariableSubstitution.empty))
      have hIndexClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              (term_weaken_free_three index) = index := by
        change
          Term.substituteMapped VariableSubstitution.boundId τ
              (((index.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
                SetSort.set) = index
        exact gq_closed_three_weaken_substitute τ index
      have hCodeClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              (term_weaken_free_three code) = code := by
        change
          Term.substituteMapped VariableSubstitution.boundId τ
              (((code.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
                SetSort.set) = code
        exact gq_closed_three_weaken_substitute τ code
      have hArityClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              (term_weaken_free_three arity) = arity := by
        change
          Term.substituteMapped VariableSubstitution.boundId τ
              (((arity.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
                SetSort.set) = arity
        exact gq_closed_three_weaken_substitute τ arity
      have hSymbolClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              (term_weaken_free_three symbol) = symbol := by
        change
          Term.substituteMapped VariableSubstitution.boundId τ
              (((symbol.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
                SetSort.set) = symbol
        exact gq_closed_three_weaken_substitute τ symbol
      have hArgumentsClosed :
          Term.substituteMapped VariableSubstitution.boundId τ
              (term_weaken_free_three arguments) = arguments := by
        change
          Term.substituteMapped VariableSubstitution.boundId τ
              (((arguments.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
                SetSort.set) = arguments
        exact gq_closed_three_weaken_substitute τ arguments
      have hTargetSub :
          Term.substituteMapped VariableSubstitution.boundId τ
              (pred_codeₘ(
                .fvar (.there (.there .here)),
                .fvar (.there .here), .fvar .here) :
                SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]) =
            pred_codeₘ(arity, symbol, arguments) := by
        simp [predicate_formula_code_term,
          structural_node_code_term, structural_list_code_term,
          structural_raw_node_code_term, godel_pairing_term,
          Term.substituteMapped, Arguments.substituteMapped,
          VariableSubstitution.cons, τ]
      have hArgs :
          Arguments.substituteMapped VariableSubstitution.boundId τ
              (Arguments.cons
                (syntax_code_kind_term .termList :
                  SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
                (Arguments.cons
                  (term_weaken_free_three index)
                  (Arguments.cons (.fvar .here) Arguments.nil))) =
            Arguments.cons (syntax_code_kind_term .termList)
              (Arguments.cons index (Arguments.cons arguments Arguments.nil)) := by
        simp [Arguments.substituteMapped, Term.substituteMapped,
          VariableSubstitution.cons, τ,
          hIndexClosed]
      let body : SetOpenFormula
          [SetSort.set, SetSort.set, SetSort.set] :=
        ((.fvar (.there (.there .here)) ∈ₘ ωₘ) ∧ₘ
          (.fvar (.there .here) ∈ₘ ωₘ)) ∧ₘ
            ((term_weaken_free_three code ≐ₘ
                pred_codeₘ(.fvar (.there (.there .here)),
                  .fvar (.there .here), .fvar .here)) ∧ₘ
              free_var_occursₘ(
                syntax_code_kind_term .termList,
                term_weaken_free_three index, .fvar .here))
      change ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        Formula.substitute (Substitution.free_map τ) body
      have hBody :
          Formula.substitute (Substitution.free_map τ) body =
            ((arity ∈ₘ ωₘ) ∧ₘ (symbol ∈ₘ ωₘ)) ∧ₘ
              ((code ≐ₘ pred_codeₘ(arity, symbol, arguments)) ∧ₘ
                free_var_occursₘ(
                  syntax_code_kind_term .termList, index, arguments)) := by
        simp [body, Formula.substitute, Formula.substituteMapped,
          Substitution.free_map, VariableSubstitution.cons, Term.substituteMapped,
          Arguments.substituteMapped, τ, hIndexClosed, hCodeClosed, predicate_formula_code_term,
          structural_node_code_term, structural_list_code_term,
          structural_raw_node_code_term, godel_pairing_term]
      rw [hBody]
      exact FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro hArity hSymbol)
        (FirstOrder.Derives.conj_intro hCode hArguments)
theorem quote_term_free_index_occurs
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (index : Nat) (term : Term σ bound free sort)
    (h : Term.free_index_occurs index term) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(
        syntax_code_kind_term .term,
        numₘ(index),
        (quote_term term : SetOpenTerm [])) := by
  refine Term.rec
    (motive_1 := fun _ term =>
      Term.free_index_occurs index term →
        ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
          free_var_occursₘ(
            syntax_code_kind_term .term,
            numₘ(index),
            (quote_term term : SetOpenTerm [])))
    (motive_2 := fun sorts arguments =>
      Arguments.free_index_occurs index arguments →
        ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
          free_var_occursₘ(
            syntax_code_kind_term .termList,
            numₘ(index),
            (quote_arguments arguments : SetOpenTerm [])))
    (fun {sort} entry h => by
      have hFalse : False := by
        simp [Term.free_index_occurs] at h
      exact False.elim hFalse)
    (fun {sort} entry h => by
      have hIndex : entry.index = index := by
        simpa [Term.free_index_occurs] using h
      rw [← hIndex]
      simpa [quote_term] using free_variable_occurs_term_leaf entry.index)
    (fun function arguments ih h => by
      cases hDomain : σ.funcDomain function with
      | nil =>
          have hArguments : Arguments.free_index_occurs index arguments := by
            simpa [Term.free_index_occurs] using h
          have hArgumentsNil :
              Arguments.free_index_occurs index (hDomain ▸ arguments) :=
            (arguments_free_index_occurs_cast index hDomain arguments).2 hArguments
          have hFalse : False := by
            exact arguments_free_index_occurs_nil index (hDomain ▸ arguments) hArgumentsNil
          exact False.elim hFalse
      | cons head tail =>
          have hArguments : Arguments.free_index_occurs index arguments := by
            simpa [Term.free_index_occurs] using h
          have hArgumentsCode := term_list_code_at_code_mem_of_derives
            (numₘ(bound.length))
            (numₘ(σ.funcArity function))
            (quote_arguments arguments : SetOpenTerm [])
            (quote_arguments_term_list_code_at arguments)
          have hCode :
              ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
                (app_codeₘ(
                  numₘ(σ.funcArity function),
                  numₘ(QuotationNumbering.function_number function),
                  (quote_arguments arguments : SetOpenTerm [])) :
                  SetOpenTerm []) ∈ₘ ωₘ := by
            simpa [structural_node_code_term, structural_list_code_term] using!
              (structural_node_mem_expression_encoding_leaf
                (Γ := ([] : Context signature [])) StructuralCodeTag.application
                [numₘ(σ.funcArity function),
                  numₘ(QuotationNumbering.function_number function),
                  (quote_arguments arguments : SetOpenTerm [])] (by
                    intro field hField
                    simp only [List.mem_cons, List.not_mem_nil] at hField
                    rcases hField with hField | hField
                    · simpa [hField] using
                        (finite_numeral_mem_formal_language_encoding_theory
                          (Γ := ([] : Context signature []))
                          (σ.funcArity function))
                    · rcases hField with hField | hField
                      · simpa [hField] using
                          (finite_numeral_mem_formal_language_encoding_theory
                            (Γ := ([] : Context signature []))
                            (QuotationNumbering.function_number function))
                      · rcases hField with hField | hField
                        · simpa [hField] using hArgumentsCode
                        · contradiction))
          have hResult := free_variable_occurs_application_intro
            (numₘ(index) : SetOpenTerm [])
            (app_codeₘ(
              numₘ(σ.funcArity function),
              numₘ(QuotationNumbering.function_number function),
              (quote_arguments arguments : SetOpenTerm [])) :
              SetOpenTerm [])
            (numₘ(σ.funcArity function) : SetOpenTerm [])
            (numₘ(QuotationNumbering.function_number function) : SetOpenTerm [])
            (quote_arguments arguments : SetOpenTerm [])
            (finite_numeral_mem_expression_encoding (Γ := []) index)
            hCode
            (finite_numeral_mem_expression_encoding (Γ := [])
              (σ.funcArity function))
            (finite_numeral_mem_expression_encoding (Γ := [])
              (QuotationNumbering.function_number function))
            (ih hArguments)
            (Metatheory.Derives.equality_refl
              (app_codeₘ(
                numₘ(σ.funcArity function),
                numₘ(QuotationNumbering.function_number function),
                (quote_arguments arguments : SetOpenTerm [])) :
                SetOpenTerm []))
          simpa [quote_term, hDomain] using hResult)
    (by
      intro h
      exact False.elim h)
    (fun {sort} {sorts} head tail ihHead ihTail h => by
      have hHeadCode := term_code_at_code_mem_of_derives
        (numₘ(bound.length))
        (quote_term head : SetOpenTerm [])
        (quote_term_code_at head)
      have hTailCode := term_list_code_at_code_mem_of_derives
        (numₘ(bound.length))
        (numₘ(sorts.length))
        (quote_arguments tail : SetOpenTerm [])
        (quote_arguments_term_list_code_at tail)
      have hCode :
          ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
            (code_consₘ(
              (quote_term head : SetOpenTerm []),
              (quote_arguments tail : SetOpenTerm [])) :
              SetOpenTerm []) ∈ₘ ωₘ := by
        have hPair := godel_pair_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature []))
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          hHeadCode hTailCode
        have hRaw := structural_raw_node_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) StructuralCodeTag.listCons
          (godel_pairₘ(
            (quote_term head : SetOpenTerm []),
            (quote_arguments tail : SetOpenTerm []))) hPair
        exact FirstOrder.Derives.theory_weaken
          (T := formal_language_encoding_theory)
          (U := expression_encoding_theory)
          formal_language_encoding_theory_subset_expression_encoding_theory hRaw
      rcases h with hHead | hTail
      · have hResult := free_variable_occurs_cons_intro
          (numₘ(index) : SetOpenTerm [])
          (code_consₘ(
            (quote_term head : SetOpenTerm []),
            (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm [])
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          (finite_numeral_mem_expression_encoding (Γ := []) index)
          hCode
          (Metatheory.Derives.equality_refl
            (code_consₘ(
              (quote_term head : SetOpenTerm []),
              (quote_arguments tail : SetOpenTerm [])) :
              SetOpenTerm []))
          (FirstOrder.Derives.disj_intro_left (ihHead hHead))
        simpa [quote_arguments] using hResult
      · have hResult := free_variable_occurs_cons_intro
          (numₘ(index) : SetOpenTerm [])
          (code_consₘ(
            (quote_term head : SetOpenTerm []),
            (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm [])
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          (finite_numeral_mem_expression_encoding (Γ := []) index)
          hCode
          (Metatheory.Derives.equality_refl
            (code_consₘ(
              (quote_term head : SetOpenTerm []),
              (quote_arguments tail : SetOpenTerm [])) :
              SetOpenTerm []))
          (FirstOrder.Derives.disj_intro_right (ihTail hTail))
        simpa [quote_arguments] using hResult)
    term h
theorem quote_arguments_free_index_occurs
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (index : Nat) (arguments : Arguments σ bound free sorts)
    (h : Arguments.free_index_occurs index arguments) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(
        syntax_code_kind_term .termList,
        numₘ(index),
        (quote_arguments arguments : SetOpenTerm [])) := by
  refine Arguments.rec (σ := σ) (bound := bound) (free := free)
    (motive_1 := fun _ term =>
      Term.free_index_occurs index term →
        ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
          free_var_occursₘ(
            syntax_code_kind_term .term,
            numₘ(index),
            (quote_term term : SetOpenTerm [])))
    (motive_2 := fun sorts arguments =>
      Arguments.free_index_occurs index arguments →
        ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
          free_var_occursₘ(
            syntax_code_kind_term .termList,
            numₘ(index),
            (quote_arguments arguments : SetOpenTerm [])))
    (fun {sort} entry h => by
      have hFalse : False := by
        simp [Term.free_index_occurs] at h
      exact False.elim hFalse)
    (fun {sort} entry h => by
      exact quote_term_free_index_occurs index (.fvar entry) h)
    (fun function arguments ih h => by
      exact quote_term_free_index_occurs index (.app function arguments) h)
    (by
      intro h
      exact False.elim h)
    (fun {sort} {sorts} head tail ihHead ihTail h => by
      have hHeadCode := term_code_at_code_mem_of_derives
        (numₘ(bound.length))
        (quote_term head : SetOpenTerm [])
        (quote_term_code_at head)
      have hTailCode := term_list_code_at_code_mem_of_derives
        (numₘ(bound.length))
        (numₘ(sorts.length))
        (quote_arguments tail : SetOpenTerm [])
        (quote_arguments_term_list_code_at tail)
      have hCode :
          ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
            (code_consₘ(
              (quote_term head : SetOpenTerm []),
              (quote_arguments tail : SetOpenTerm [])) :
              SetOpenTerm []) ∈ₘ ωₘ := by
        have hPair := godel_pair_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature []))
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          hHeadCode hTailCode
        have hRaw := structural_raw_node_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) StructuralCodeTag.listCons
          (godel_pairₘ(
            (quote_term head : SetOpenTerm []),
            (quote_arguments tail : SetOpenTerm []))) hPair
        exact FirstOrder.Derives.theory_weaken
          (T := formal_language_encoding_theory)
          (U := expression_encoding_theory)
          formal_language_encoding_theory_subset_expression_encoding_theory hRaw
      rcases h with hHead | hTail
      · have hResult := free_variable_occurs_cons_intro
          (numₘ(index) : SetOpenTerm [])
          (code_consₘ(
            (quote_term head : SetOpenTerm []),
            (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm [])
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          (finite_numeral_mem_expression_encoding (Γ := []) index)
          hCode
          (Metatheory.Derives.equality_refl
            (code_consₘ(
              (quote_term head : SetOpenTerm []),
              (quote_arguments tail : SetOpenTerm [])) :
              SetOpenTerm []))
          (FirstOrder.Derives.disj_intro_left (ihHead hHead))
        simpa [quote_arguments] using hResult
      · have hResult := free_variable_occurs_cons_intro
          (numₘ(index) : SetOpenTerm [])
          (code_consₘ(
            (quote_term head : SetOpenTerm []),
            (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm [])
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          (finite_numeral_mem_expression_encoding (Γ := []) index)
          hCode
          (Metatheory.Derives.equality_refl
            (code_consₘ(
              (quote_term head : SetOpenTerm []),
              (quote_arguments tail : SetOpenTerm [])) :
              SetOpenTerm []))
          (FirstOrder.Derives.disj_intro_right (ihTail hTail))
        simpa [quote_arguments] using hResult)
    arguments h
private theorem formula_quote_code_mem_expression_encoding
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (quote formula : SetOpenTerm []) ∈ₘ ωₘ := by
  exact FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (formula_code_at_code_mem_of_derives
      (numₘ(bound.length))
      (quote formula : SetOpenTerm [])
      (quote_formula_code_at formula))
theorem quote_formula_free_index_occurs
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (index : Nat) (formula : Formula σ bound free)
    (h : Formula.free_index_occurs index formula) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(
        syntax_code_kind_term .formula,
        numₘ(index),
        (quote formula : SetOpenTerm [])) := by
  refine Formula.rec
    (motive := fun bound free formula =>
      Formula.free_index_occurs index formula →
        ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
          free_var_occursₘ(
            syntax_code_kind_term .formula,
            numₘ(index),
            (quote formula : SetOpenTerm [])))
    (fun {bound free} h => by
      have hFalse : False := by
        simp [Formula.free_index_occurs] at h
      exact False.elim hFalse)
    (fun {bound free} h => by
      have hFalse : False := by
        simp [Formula.free_index_occurs] at h
      exact False.elim hFalse)
    (fun {bound free} relation arguments h => by
      have hArguments : Arguments.free_index_occurs index arguments := by
        simpa [Formula.free_index_occurs] using h
      generalize hKind : QuotationNumbering.relation_kind relation = kind
      cases kind with
      | membership =>
          generalize hTypedArguments :
            (QuotationNumbering.membership_domain relation hKind ▸ arguments) =
              typedArguments
          have hTypedOccurrence :
              Arguments.free_index_occurs index typedArguments := by
            rw [← hTypedArguments]
            exact (arguments_free_index_occurs_cast index
              (QuotationNumbering.membership_domain relation hKind)
              arguments).2 hArguments
          cases typedArguments with
          | cons left rest =>
              cases rest with
              | cons right tail =>
                  cases tail with
                  | nil =>
                      have hOccurrence :
                          Term.free_index_occurs index left ∨
                            Term.free_index_occurs index right := by
                        simpa [Arguments.free_index_occurs] using
                          hTypedOccurrence
                      have hQuoteRelation :
                          quote_relation relation arguments =
                            mem_codeₘ(
                              (quote_term left : SetOpenTerm []),
                              (quote_term right : SetOpenTerm [])) := by
                        rw [quote_relation_membership_eq
                          relation arguments hKind]
                        exact quote_membership_arguments_cons_eq
                          relation arguments hKind left right hTypedArguments
                      have hQuote :
                          quote (.rel relation arguments) =
                            mem_codeₘ(
                              (quote_term left : SetOpenTerm []),
                              (quote_term right : SetOpenTerm [])) := by
                        simpa [quote, Formula.hilbertize,
                          quote_hilbert] using hQuoteRelation
                      have hCodeMem :=
                        formula_quote_code_mem_expression_encoding
                          (.rel relation arguments)
                      rw [hQuote] at hCodeMem
                      have hIndex :=
                        finite_numeral_mem_expression_encoding
                          (Γ := ([] : Context signature [])) index
                      rcases hOccurrence with hLeft | hRight
                      · have hResult := free_variable_occurs_binary_formula_intro
                          .membership (Or.inr rfl)
                          (numₘ(index) : SetOpenTerm [])
                          (mem_codeₘ(
                            (quote_term left : SetOpenTerm []),
                            (quote_term right : SetOpenTerm [])) :
                            SetOpenTerm [])
                          (quote_term left : SetOpenTerm [])
                          (quote_term right : SetOpenTerm [])
                          hIndex hCodeMem
                          (Metatheory.Derives.equality_refl
                            (mem_codeₘ(
                              (quote_term left : SetOpenTerm []),
                              (quote_term right : SetOpenTerm [])) :
                              SetOpenTerm []))
                          (FirstOrder.Derives.disj_intro_left
                            (quote_term_free_index_occurs index left hLeft))
                        exact hQuote.symm ▸ hResult
                      · have hResult := free_variable_occurs_binary_formula_intro
                          .membership (Or.inr rfl)
                          (numₘ(index) : SetOpenTerm [])
                          (mem_codeₘ(
                            (quote_term left : SetOpenTerm []),
                            (quote_term right : SetOpenTerm [])) :
                            SetOpenTerm [])
                          (quote_term left : SetOpenTerm [])
                          (quote_term right : SetOpenTerm [])
                          hIndex hCodeMem
                          (Metatheory.Derives.equality_refl
                            (mem_codeₘ(
                              (quote_term left : SetOpenTerm []),
                              (quote_term right : SetOpenTerm [])) :
                              SetOpenTerm []))
                          (FirstOrder.Derives.disj_intro_right
                            (quote_term_free_index_occurs index right hRight))
                        exact hQuote.symm ▸ hResult
      | predicate =>
          have hQuoteRelation :
              quote_relation relation arguments =
                pred_codeₘ(
                  numₘ(σ.relArity relation),
                  numₘ(QuotationNumbering.relation_number relation),
                  (quote_arguments arguments : SetOpenTerm [])) := by
            exact quote_relation_predicate_eq
              relation arguments hKind
          have hQuote :
              quote (.rel relation arguments) =
                pred_codeₘ(
                  numₘ(σ.relArity relation),
                  numₘ(QuotationNumbering.relation_number relation),
                  (quote_arguments arguments : SetOpenTerm [])) := by
            simpa [quote, Formula.hilbertize,
              quote_hilbert] using hQuoteRelation
          have hCodeMem :=
            formula_quote_code_mem_expression_encoding
              (.rel relation arguments)
          rw [hQuote] at hCodeMem
          have hIndex :=
            finite_numeral_mem_expression_encoding
              (Γ := ([] : Context signature [])) index
          have hArity := finite_numeral_mem_expression_encoding
            (Γ := ([] : Context signature [])) (σ.relArity relation)
          have hSymbol := finite_numeral_mem_expression_encoding
            (Γ := ([] : Context signature []))
              (QuotationNumbering.relation_number relation)
          have hArguments := quote_arguments_free_index_occurs
            index arguments hArguments
          have hResult := free_variable_occurs_predicate_formula_intro
            (numₘ(index) : SetOpenTerm [])
            (pred_codeₘ(
              numₘ(σ.relArity relation),
              numₘ(QuotationNumbering.relation_number relation),
              (quote_arguments arguments : SetOpenTerm [])) :
              SetOpenTerm [])
            (numₘ(σ.relArity relation) : SetOpenTerm [])
            (numₘ(QuotationNumbering.relation_number relation) : SetOpenTerm [])
            (quote_arguments arguments : SetOpenTerm [])
            hIndex hCodeMem hArity hSymbol hArguments
            (Metatheory.Derives.equality_refl
              (pred_codeₘ(
                numₘ(σ.relArity relation),
                numₘ(QuotationNumbering.relation_number relation),
                (quote_arguments arguments : SetOpenTerm [])) :
                SetOpenTerm []))
          exact hQuote.symm ▸ hResult)
    (fun {bound free} {sort} left right h => by
      have hOccurrence :
          Term.free_index_occurs index left ∨
            Term.free_index_occurs index right := by
        simpa [Formula.free_index_occurs] using h
      have hCodeMem :=
        formula_quote_code_mem_expression_encoding (.equal left right)
      have hQuote :
          quote (.equal left right) =
            eq_codeₘ(
              (quote_term left : SetOpenTerm []),
              (quote_term right : SetOpenTerm [])) := by
        simp [quote, Formula.hilbertize, quote_hilbert]
      rw [hQuote] at hCodeMem
      have hIndex := finite_numeral_mem_expression_encoding
        (Γ := ([] : Context signature [])) index
      rcases hOccurrence with hLeft | hRight
      · have hResult := free_variable_occurs_binary_formula_intro
          .equality (Or.inl rfl)
          (numₘ(index) : SetOpenTerm [])
          (eq_codeₘ(
            (quote_term left : SetOpenTerm []),
            (quote_term right : SetOpenTerm [])) : SetOpenTerm [])
          (quote_term left : SetOpenTerm [])
          (quote_term right : SetOpenTerm [])
          hIndex hCodeMem
          (Metatheory.Derives.equality_refl
            (eq_codeₘ(
              (quote_term left : SetOpenTerm []),
              (quote_term right : SetOpenTerm [])) : SetOpenTerm []))
          (FirstOrder.Derives.disj_intro_left
            (quote_term_free_index_occurs index left hLeft))
        exact hQuote.symm ▸ hResult
      · have hResult := free_variable_occurs_binary_formula_intro
          .equality (Or.inl rfl)
          (numₘ(index) : SetOpenTerm [])
          (eq_codeₘ(
            (quote_term left : SetOpenTerm []),
            (quote_term right : SetOpenTerm [])) : SetOpenTerm [])
          (quote_term left : SetOpenTerm [])
          (quote_term right : SetOpenTerm [])
          hIndex hCodeMem
          (Metatheory.Derives.equality_refl
            (eq_codeₘ(
              (quote_term left : SetOpenTerm []),
              (quote_term right : SetOpenTerm [])) : SetOpenTerm []))
          (FirstOrder.Derives.disj_intro_right
            (quote_term_free_index_occurs index right hRight))
        exact hQuote.symm ▸ hResult)
    (fun {bound free} body ih h => by
      have hBody : Formula.free_index_occurs index body := by
        simpa [Formula.free_index_occurs] using h
      have hBodyResult := ih hBody
      have hCodeMem := formula_quote_code_mem_expression_encoding (.neg body)
      have hQuote :
          quote (.neg body) =
            neg_codeₘ((quote body : SetOpenTerm [])) := by
        simp [quote, Formula.hilbertize, quote_hilbert]
      rw [hQuote] at hCodeMem
      have hResult := free_variable_occurs_unary_formula_intro
        .negation (Or.inl rfl)
        (numₘ(index) : SetOpenTerm [])
        (neg_codeₘ((quote body : SetOpenTerm [])) : SetOpenTerm [])
        (quote body : SetOpenTerm [])
        (finite_numeral_mem_expression_encoding (Γ := []) index)
        hCodeMem
        (Metatheory.Derives.equality_refl
          (neg_codeₘ((quote body : SetOpenTerm [])) : SetOpenTerm []))
        hBodyResult
      exact hQuote.symm ▸ hResult)
    (fun {bound free} left right ihLeft ihRight h => by
      have hOccurrence : Formula.free_index_occurs index left ∨
          Formula.free_index_occurs index right := by
        simpa [Formula.free_index_occurs] using h
      have hLeftResult := ihLeft
      have hRightResult := ihRight
      have hRightNegMem :=
        formula_quote_code_mem_expression_encoding (.neg right)
      have hRightNegQuote :
          quote (.neg right) =
            neg_codeₘ((quote right : SetOpenTerm [])) := by
        simp [quote, Formula.hilbertize, quote_hilbert]
      rw [hRightNegQuote] at hRightNegMem
      have hImpMem :=
        formula_quote_code_mem_expression_encoding (.imp left (.neg right))
      have hImpQuote :
          quote (.imp left (.neg right)) =
            imp_codeₘ(
              (quote left : SetOpenTerm []),
              neg_codeₘ((quote right : SetOpenTerm []))) := by
        simp [quote, Formula.hilbertize, quote_hilbert]
      rw [hImpQuote] at hImpMem
      have hOuterMem := formula_quote_code_mem_expression_encoding
        (.conj left right)
      have hOuterQuote :
          quote (.conj left right) =
            neg_codeₘ(imp_codeₘ(
              (quote left : SetOpenTerm []),
              neg_codeₘ((quote right : SetOpenTerm [])))) := by
        simp [quote, Formula.hilbertize, quote_hilbert,
          Formula.hilbert_conj]
      rw [hOuterQuote] at hOuterMem
      have hIndex := finite_numeral_mem_expression_encoding
        (Γ := ([] : Context signature [])) index
      rcases hOccurrence with hLeft | hRight
      · have hImp := free_variable_occurs_implication_formula_intro
          (numₘ(index) : SetOpenTerm [])
          (imp_codeₘ(
            (quote left : SetOpenTerm []),
            neg_codeₘ((quote right : SetOpenTerm []))) : SetOpenTerm [])
          (quote left : SetOpenTerm [])
          (neg_codeₘ((quote right : SetOpenTerm [])) : SetOpenTerm [])
          hIndex hImpMem
          (Metatheory.Derives.equality_refl
            (imp_codeₘ(
              (quote left : SetOpenTerm []),
              neg_codeₘ((quote right : SetOpenTerm []))) :
              SetOpenTerm []))
          (FirstOrder.Derives.disj_intro_left (ihLeft hLeft))
        have hResult := free_variable_occurs_unary_formula_intro
          .negation (Or.inl rfl)
          (numₘ(index) : SetOpenTerm [])
          (neg_codeₘ(imp_codeₘ(
            (quote left : SetOpenTerm []),
            neg_codeₘ((quote right : SetOpenTerm [])))) : SetOpenTerm [])
          (imp_codeₘ(
            (quote left : SetOpenTerm []),
            neg_codeₘ((quote right : SetOpenTerm []))) : SetOpenTerm [])
          hIndex hOuterMem
          (Metatheory.Derives.equality_refl
            (neg_codeₘ(imp_codeₘ(
              (quote left : SetOpenTerm []),
              neg_codeₘ((quote right : SetOpenTerm [])))) : SetOpenTerm []))
          hImp
        exact hOuterQuote.symm ▸ hResult
      · have hRightNeg := free_variable_occurs_unary_formula_intro
          .negation (Or.inl rfl)
          (numₘ(index) : SetOpenTerm [])
          (neg_codeₘ((quote right : SetOpenTerm [])) : SetOpenTerm [])
          (quote right : SetOpenTerm [])
          hIndex hRightNegMem
          (Metatheory.Derives.equality_refl
            (neg_codeₘ((quote right : SetOpenTerm [])) : SetOpenTerm []))
          (ihRight hRight)
        have hImp := free_variable_occurs_implication_formula_intro
          (numₘ(index) : SetOpenTerm [])
          (imp_codeₘ(
            (quote left : SetOpenTerm []),
            neg_codeₘ((quote right : SetOpenTerm []))) : SetOpenTerm [])
          (quote left : SetOpenTerm [])
          (neg_codeₘ((quote right : SetOpenTerm [])) : SetOpenTerm [])
          hIndex hImpMem
          (Metatheory.Derives.equality_refl
            (imp_codeₘ(
              (quote left : SetOpenTerm []),
              neg_codeₘ((quote right : SetOpenTerm []))) :
              SetOpenTerm []))
          (FirstOrder.Derives.disj_intro_right hRightNeg)
        have hResult := free_variable_occurs_unary_formula_intro
          .negation (Or.inl rfl)
          (numₘ(index) : SetOpenTerm [])
          (neg_codeₘ(imp_codeₘ(
            (quote left : SetOpenTerm []),
            neg_codeₘ((quote right : SetOpenTerm [])))) : SetOpenTerm [])
          (imp_codeₘ(
            (quote left : SetOpenTerm []),
            neg_codeₘ((quote right : SetOpenTerm []))) : SetOpenTerm [])
          hIndex hOuterMem
          (Metatheory.Derives.equality_refl
            (neg_codeₘ(imp_codeₘ(
              (quote left : SetOpenTerm []),
              neg_codeₘ((quote right : SetOpenTerm [])))) : SetOpenTerm []))
          hImp
        exact hOuterQuote.symm ▸ hResult)
    (fun {bound free} left right ihLeft ihRight h => by
      have hOccurrence : Formula.free_index_occurs index left ∨
          Formula.free_index_occurs index right := by
        simpa [Formula.free_index_occurs] using h
      have hLeftNegMem := formula_quote_code_mem_expression_encoding (.neg left)
      have hLeftNegQuote :
          quote (.neg left) =
            neg_codeₘ((quote left : SetOpenTerm [])) := by
        simp [quote, Formula.hilbertize, quote_hilbert]
      rw [hLeftNegQuote] at hLeftNegMem
      have hImpMem := formula_quote_code_mem_expression_encoding
        (.disj left right)
      have hImpQuote :
          quote (.disj left right) =
            imp_codeₘ(
              neg_codeₘ((quote left : SetOpenTerm [])),
              (quote right : SetOpenTerm [])) := by
        simp [quote, Formula.hilbertize, quote_hilbert]
      rw [hImpQuote] at hImpMem
      have hIndex := finite_numeral_mem_expression_encoding
        (Γ := ([] : Context signature [])) index
      rcases hOccurrence with hLeft | hRight
      · have hLeftNeg := free_variable_occurs_unary_formula_intro
          .negation (Or.inl rfl)
          (numₘ(index) : SetOpenTerm [])
          (neg_codeₘ((quote left : SetOpenTerm [])) : SetOpenTerm [])
          (quote left : SetOpenTerm [])
          hIndex hLeftNegMem
          (Metatheory.Derives.equality_refl
            (neg_codeₘ((quote left : SetOpenTerm [])) : SetOpenTerm []))
          (ihLeft hLeft)
        have hResult := free_variable_occurs_implication_formula_intro
          (numₘ(index) : SetOpenTerm [])
          (imp_codeₘ(
            neg_codeₘ((quote left : SetOpenTerm [])),
            (quote right : SetOpenTerm [])) : SetOpenTerm [])
          (neg_codeₘ((quote left : SetOpenTerm [])) : SetOpenTerm [])
          (quote right : SetOpenTerm [])
          hIndex hImpMem
          (Metatheory.Derives.equality_refl
            (imp_codeₘ(
              neg_codeₘ((quote left : SetOpenTerm [])),
              (quote right : SetOpenTerm [])) : SetOpenTerm []))
          (FirstOrder.Derives.disj_intro_left hLeftNeg)
        exact hImpQuote.symm ▸ hResult
      · have hResult := free_variable_occurs_implication_formula_intro
          (numₘ(index) : SetOpenTerm [])
          (imp_codeₘ(
            neg_codeₘ((quote left : SetOpenTerm [])),
            (quote right : SetOpenTerm [])) : SetOpenTerm [])
          (neg_codeₘ((quote left : SetOpenTerm [])) : SetOpenTerm [])
          (quote right : SetOpenTerm [])
          hIndex hImpMem
          (Metatheory.Derives.equality_refl
            (imp_codeₘ(
              neg_codeₘ((quote left : SetOpenTerm [])),
               (quote right : SetOpenTerm [])) : SetOpenTerm []))
          (FirstOrder.Derives.disj_intro_right (ihRight hRight))
        exact hImpQuote.symm ▸ hResult)
    (fun {bound free} left right ihLeft ihRight h => by
      have hOccurrence : Formula.free_index_occurs index left ∨
          Formula.free_index_occurs index right := by
        simpa [Formula.free_index_occurs] using h
      have hImpQuote :
          quote (.imp left right) =
            imp_codeₘ(
              (quote left : SetOpenTerm []),
              (quote right : SetOpenTerm [])) := by
        simp [quote, Formula.hilbertize, quote_hilbert]
      have hImpMem := formula_quote_code_mem_expression_encoding (.imp left right)
      rw [hImpQuote] at hImpMem
      have hIndex := finite_numeral_mem_expression_encoding
        (Γ := ([] : Context signature [])) index
      rcases hOccurrence with hLeft | hRight
      · have hResult := free_variable_occurs_implication_formula_intro
          (numₘ(index) : SetOpenTerm [])
          (imp_codeₘ(
            (quote left : SetOpenTerm []),
            (quote right : SetOpenTerm [])) : SetOpenTerm [])
          (quote left : SetOpenTerm [])
          (quote right : SetOpenTerm [])
          hIndex hImpMem
          (Metatheory.Derives.equality_refl
            (imp_codeₘ(
              (quote left : SetOpenTerm []),
              (quote right : SetOpenTerm [])) : SetOpenTerm []))
          (FirstOrder.Derives.disj_intro_left (ihLeft hLeft))
        exact hImpQuote.symm ▸ hResult
      · have hResult := free_variable_occurs_implication_formula_intro
          (numₘ(index) : SetOpenTerm [])
          (imp_codeₘ(
            (quote left : SetOpenTerm []),
            (quote right : SetOpenTerm [])) : SetOpenTerm [])
          (quote left : SetOpenTerm [])
          (quote right : SetOpenTerm [])
          hIndex hImpMem
          (Metatheory.Derives.equality_refl
            (imp_codeₘ(
              (quote left : SetOpenTerm []),
              (quote right : SetOpenTerm [])) : SetOpenTerm []))
          (FirstOrder.Derives.disj_intro_right (ihRight hRight))
        exact hImpQuote.symm ▸ hResult)
    (fun {bound free} left right ihLeft ihRight h => by
      have hOccurrence : Formula.free_index_occurs index left ∨
          Formula.free_index_occurs index right := by
        simpa [Formula.free_index_occurs] using h
      let leftCode : SetOpenTerm [] := quote left
      let rightCode : SetOpenTerm [] := quote right
      let leftRightCode : SetOpenTerm [] := imp_codeₘ(leftCode, rightCode)
      let rightLeftCode : SetOpenTerm [] := imp_codeₘ(rightCode, leftCode)
      let rightLeftNegCode : SetOpenTerm [] := neg_codeₘ(rightLeftCode)
      let outerImpCode : SetOpenTerm [] :=
        imp_codeₘ(leftRightCode, rightLeftNegCode)
      let code : SetOpenTerm [] := neg_codeₘ(outerImpCode)
      have hLeftRightMem :=
        formula_quote_code_mem_expression_encoding (.imp left right)
      have hLeftRightQuote :
          quote (.imp left right) = leftRightCode := by
        simp [leftCode, rightCode, leftRightCode, quote,
          Formula.hilbertize, quote_hilbert]
      rw [hLeftRightQuote] at hLeftRightMem
      have hRightLeftMem :=
        formula_quote_code_mem_expression_encoding (.imp right left)
      have hRightLeftQuote :
          quote (.imp right left) = rightLeftCode := by
        simp [leftCode, rightCode, rightLeftCode, quote,
          Formula.hilbertize, quote_hilbert]
      rw [hRightLeftQuote] at hRightLeftMem
      have hRightLeftNegMem :=
        formula_quote_code_mem_expression_encoding (.neg (.imp right left))
      have hRightLeftNegQuote :
          quote (.neg (.imp right left)) = rightLeftNegCode := by
        simp [leftCode, rightCode, rightLeftCode, rightLeftNegCode,
          quote, Formula.hilbertize, quote_hilbert]
      rw [hRightLeftNegQuote] at hRightLeftNegMem
      have hOuterImpMem :=
        formula_quote_code_mem_expression_encoding
          (.imp (.imp left right) (.neg (.imp right left)))
      have hOuterImpQuote :
          quote (.imp (.imp left right) (.neg (.imp right left))) =
            outerImpCode := by
        simp [leftCode, rightCode, leftRightCode, rightLeftCode,
          rightLeftNegCode, outerImpCode, quote,
          Formula.hilbertize, quote_hilbert]
      rw [hOuterImpQuote] at hOuterImpMem
      have hCodeMem := formula_quote_code_mem_expression_encoding
        (.iff left right)
      have hQuote : quote (.iff left right) = code := by
        simp [leftCode, rightCode, leftRightCode, rightLeftCode,
          rightLeftNegCode, outerImpCode, code, quote,
          Formula.hilbertize, quote_hilbert, Formula.hilbert_iff,
          Formula.hilbert_conj]
      rw [hQuote] at hCodeMem
      have hIndex := finite_numeral_mem_expression_encoding
        (Γ := ([] : Context signature [])) index
      rcases hOccurrence with hLeft | hRight
      · have hLeftRight := free_variable_occurs_implication_formula_intro
          (numₘ(index) : SetOpenTerm []) leftRightCode leftCode rightCode
          hIndex hLeftRightMem
          (Metatheory.Derives.equality_refl leftRightCode)
          (FirstOrder.Derives.disj_intro_left (ihLeft hLeft))
        have hOuterImp := free_variable_occurs_implication_formula_intro
          (numₘ(index) : SetOpenTerm []) outerImpCode leftRightCode rightLeftNegCode
          hIndex hOuterImpMem
          (Metatheory.Derives.equality_refl outerImpCode)
          (FirstOrder.Derives.disj_intro_left hLeftRight)
        have hResult := free_variable_occurs_unary_formula_intro
          .negation (Or.inl rfl)
          (numₘ(index) : SetOpenTerm []) code outerImpCode
          hIndex hCodeMem (Metatheory.Derives.equality_refl code) hOuterImp
        exact hQuote.symm ▸ hResult
      · have hRightLeft := free_variable_occurs_implication_formula_intro
          (numₘ(index) : SetOpenTerm []) rightLeftCode rightCode leftCode
          hIndex hRightLeftMem
          (Metatheory.Derives.equality_refl rightLeftCode)
          (FirstOrder.Derives.disj_intro_left (ihRight hRight))
        have hRightLeftNeg := free_variable_occurs_unary_formula_intro
          .negation (Or.inl rfl)
          (numₘ(index) : SetOpenTerm []) rightLeftNegCode rightLeftCode
          hIndex hRightLeftNegMem
          (Metatheory.Derives.equality_refl rightLeftNegCode) hRightLeft
        have hOuterImp := free_variable_occurs_implication_formula_intro
          (numₘ(index) : SetOpenTerm []) outerImpCode leftRightCode rightLeftNegCode
          hIndex hOuterImpMem
          (Metatheory.Derives.equality_refl outerImpCode)
          (FirstOrder.Derives.disj_intro_right hRightLeftNeg)
        have hResult := free_variable_occurs_unary_formula_intro
          .negation (Or.inl rfl)
          (numₘ(index) : SetOpenTerm []) code outerImpCode
          hIndex hCodeMem (Metatheory.Derives.equality_refl code) hOuterImp
        exact hQuote.symm ▸ hResult)
    (fun {bound free} sort body ih h => by
      have hBody : Formula.free_index_occurs index body := by
        simpa [Formula.free_index_occurs] using h
      have hBodyResult := ih hBody
      have hCodeMem :=
        formula_quote_code_mem_expression_encoding (.forallE sort body)
      have hQuote :
          quote (.forallE sort body) =
            all_codeₘ((quote body : SetOpenTerm [])) := by
        simp [quote, Formula.hilbertize, quote_hilbert]
      rw [hQuote] at hCodeMem
      have hResult := free_variable_occurs_unary_formula_intro
        .universal (Or.inr rfl)
        (numₘ(index) : SetOpenTerm [])
        (all_codeₘ((quote body : SetOpenTerm [])) : SetOpenTerm [])
        (quote body : SetOpenTerm [])
        (finite_numeral_mem_expression_encoding (Γ := []) index)
        hCodeMem
        (Metatheory.Derives.equality_refl
          (all_codeₘ((quote body : SetOpenTerm [])) : SetOpenTerm []))
        hBodyResult
      simpa [hQuote] using hResult)
    (fun {bound free} sort body ih h => by
      have hBody : Formula.free_index_occurs index body := by
        simpa [Formula.free_index_occurs] using h
      have hBodyResult := ih hBody
      have hNegMem := formula_quote_code_mem_expression_encoding (.neg body)
      have hNegQuote :
          quote (.neg body) =
            neg_codeₘ((quote body : SetOpenTerm [])) := by
        simp [quote, Formula.hilbertize, quote_hilbert]
      rw [hNegQuote] at hNegMem
      have hAllMem :=
        formula_quote_code_mem_expression_encoding
          (.forallE sort (.neg body))
      have hAllQuote :
          quote (.forallE sort (.neg body)) =
            all_codeₘ(neg_codeₘ((quote body : SetOpenTerm []))) := by
        simp [quote, Formula.hilbertize, quote_hilbert]
      rw [hAllQuote] at hAllMem
      have hCodeMem := formula_quote_code_mem_expression_encoding
        (.existsE sort body)
      have hQuote :
          quote (.existsE sort body) =
            neg_codeₘ(all_codeₘ(
              neg_codeₘ((quote body : SetOpenTerm [])))) := by
        simp [quote, Formula.hilbertize, quote_hilbert]
      rw [hQuote] at hCodeMem
      have hIndex := finite_numeral_mem_expression_encoding
        (Γ := ([] : Context signature [])) index
      have hNeg := free_variable_occurs_unary_formula_intro
        .negation (Or.inl rfl)
        (numₘ(index) : SetOpenTerm [])
        (neg_codeₘ((quote body : SetOpenTerm [])) : SetOpenTerm [])
        (quote body : SetOpenTerm [])
        hIndex hNegMem
        (Metatheory.Derives.equality_refl
          (neg_codeₘ((quote body : SetOpenTerm [])) : SetOpenTerm []))
        hBodyResult
      have hAll := free_variable_occurs_unary_formula_intro
        .universal (Or.inr rfl)
        (numₘ(index) : SetOpenTerm [])
        (all_codeₘ(neg_codeₘ(
          (quote body : SetOpenTerm []))) : SetOpenTerm [])
        (neg_codeₘ((quote body : SetOpenTerm [])) : SetOpenTerm [])
        hIndex hAllMem
        (Metatheory.Derives.equality_refl
          (all_codeₘ(neg_codeₘ(
            (quote body : SetOpenTerm []))) : SetOpenTerm []))
        hNeg
      have hResult := free_variable_occurs_unary_formula_intro
        .negation (Or.inl rfl)
        (numₘ(index) : SetOpenTerm [])
        (neg_codeₘ(all_codeₘ(neg_codeₘ(
          (quote body : SetOpenTerm [])))) : SetOpenTerm [])
        (all_codeₘ(neg_codeₘ(
          (quote body : SetOpenTerm []))) : SetOpenTerm [])
        hIndex hCodeMem
        (Metatheory.Derives.equality_refl
          (neg_codeₘ(all_codeₘ(neg_codeₘ(
            (quote body : SetOpenTerm [])))) : SetOpenTerm []))
        hAll
      exact hQuote.symm ▸ hResult)
    formula h
theorem quote_free_variable_term_occurs
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (entry : Variable free sort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(
        syntax_code_kind_term .term,
        numₘ(entry.index),
        (quote_term
          (bound := bound) (free := free) (sort := sort)
          (Term.fvar entry) : SetOpenTerm [])) := by
  simpa [quote_term] using free_variable_occurs_term_leaf entry.index
end YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding
