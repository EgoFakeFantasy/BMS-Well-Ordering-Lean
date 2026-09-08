import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuineCarrier

/-!
# Quine 公式码的相关语法承载

本模块只负责公式节点的相关承载构造；项与参数列的宿主递归接口由
`IntrinsicQuineCarrier` 提供。
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

private theorem ifc_formal_to_carrier
    {free : SetContext} {Γ : Context signature free}
    {φ : SetOpenFormula free}
    (hφ : Γ ⊢ₘ[formal_language_encoding_theory] φ) :
    Γ ⊢ₘ[intrinsic_syntax_carrier_theory] φ :=
  FirstOrder.Derives.theory_weaken
    formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory hφ

private theorem ifc_omega_mem
    {free : SetContext} {Γ : Context signature free}
    (number : Nat) :
    Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
      (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ :=
  ifc_formal_to_carrier
    (finite_numeral_mem_formal_language_encoding_theory
      (Γ := Γ) number)

private theorem ifc_nonlogical_symbol_mem_of_omega
    (code : SetOpenTerm [])
    (hCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ∈ₘ NonlogicalSymₘ := by
  have hEquality :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        NonlogicalSymₘ ≐ₘ ωₘ := by
    exact FirstOrder.Derives.theory_weaken
      semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
      (by simpa using! related_symbol_definition_axiom_derives)
  exact FirstOrder.Derives.iff_elim_right
    (membership_right_iff_of_equality
      (T := intrinsic_syntax_carrier_theory)
      (Γ := ([] : Context signature []))
      code NonlogicalSymₘ ωₘ hEquality)
    (ifc_formal_to_carrier hCode)

private theorem ifc_related_formula_of_condition
    (symbols depth code : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ∈ₘ ωₘ)
    (hBranch : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_binary_condition symbols depth code .equality ∨ₘ
        (related_formula_binary_condition symbols depth code .membership ∨ₘ
          (related_formula_predicate_condition symbols depth code ∨ₘ
            (related_formula_negation_condition symbols depth code ∨ₘ
              (related_formula_implication_condition symbols depth code ∨ₘ
                related_formula_universal_condition symbols depth code))))) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(symbols, depth, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (FirstOrder.Derives.theory_weaken
      semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
      (related_formula_code_at_definition_instance_derives
        (Γ := ([] : Context signature [])) symbols depth code))
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro hDepth hCode) hBranch

private theorem ifc_related_formula_code_mem
    (symbols depth code : SetOpenTerm [])
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(symbols, depth, code)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ∈ₘ ωₘ := by
  have hCondition := FirstOrder.Derives.iff_elim_left
    (FirstOrder.Derives.theory_weaken
      semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
      (related_formula_code_at_definition_instance_derives
        (Γ := ([] : Context signature [])) symbols depth code)) hCode
  exact FirstOrder.Derives.conj_elim_right
    (FirstOrder.Derives.conj_elim_left hCondition)

private theorem ifc_closed_one
    (τ : VariableSubstitution signature [SetSort.set] [] [])
    (term : SetOpenTerm []) :
    Term.substituteMapped VariableSubstitution.boundId τ
        (term.weakenFree SetSort.set) = term := by
  exact Term.rec
    (motive_1 := fun _ term =>
      Term.substituteMapped VariableSubstitution.boundId τ
          (term.weakenFree SetSort.set) = term)
    (motive_2 := fun _ arguments =>
      Arguments.substituteMapped VariableSubstitution.boundId τ
          (arguments.weakenFree SetSort.set) = arguments)
    (fun entry => by cases entry)
    (fun entry => by cases entry)
    (fun function arguments ih => by
      change Term.app function
          (Arguments.substituteMapped VariableSubstitution.boundId τ
            (arguments.weakenFree SetSort.set)) =
        Term.app function arguments
      rw [ih])
    rfl
    (fun head tail ihHead ihTail => by
      change Arguments.cons
          (Term.substituteMapped VariableSubstitution.boundId τ
            (head.weakenFree SetSort.set))
          (Arguments.substituteMapped VariableSubstitution.boundId τ
            (tail.weakenFree SetSort.set)) =
        Arguments.cons head tail
      rw [ihHead, ihTail])
    term

private theorem ifc_related_formula_predicate_condition_intro
    (symbols depth code arity symbol arguments : SetOpenTerm [])
    (hArity : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      arity ∈ₘ ωₘ)
    (hKey : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      predicate_interpretation_key_term arity symbol ∈ₘ symbols)
    (hArguments : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_list_code_atₘ(symbols, depth, arity, arguments))
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ pred_codeₘ(arity, symbol, arguments)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_predicate_condition symbols depth code := by
  unfold related_formula_predicate_condition
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
  have hSymbolsClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (term_weaken_free_three symbols) = symbols := by
    change
      Term.substituteMapped VariableSubstitution.boundId τ
          (((symbols.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
            SetSort.set) = symbols
    exact gq_closed_three_weaken_substitute τ symbols
  have hDepthClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (term_weaken_free_three depth) = depth := by
    change
      Term.substituteMapped VariableSubstitution.boundId τ
          (((depth.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
            SetSort.set) = depth
    exact gq_closed_three_weaken_substitute τ depth
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
  have hKeyClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (term_weaken_free_three
            (predicate_interpretation_key_term arity symbol : SetOpenTerm [])) =
        predicate_interpretation_key_term arity symbol :=
    gq_closed_three_weaken_substitute τ
      (predicate_interpretation_key_term arity symbol : SetOpenTerm [])
  have hPredicateCodeClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (term_weaken_free_three
            (pred_codeₘ(arity, symbol, arguments) : SetOpenTerm [])) =
        pred_codeₘ(arity, symbol, arguments) :=
    gq_closed_three_weaken_substitute τ
      (pred_codeₘ(arity, symbol, arguments) : SetOpenTerm [])
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    ((.fvar (.there (.there .here)) ∈ₘ ωₘ) ∧ₘ
      (predicate_interpretation_key_term
        (.fvar (.there (.there .here)))
        (.fvar (.there .here)) ∈ₘ term_weaken_free_three symbols)) ∧ₘ
        (related_term_list_code_atₘ(
            term_weaken_free_three symbols,
            term_weaken_free_three depth,
            .fvar (.there (.there .here)), .fvar .here) ∧ₘ
          (term_weaken_free_three code ≐ₘ
            pred_codeₘ(.fvar (.there (.there .here)),
              .fvar (.there .here), .fvar .here)))
  change ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
    Formula.substitute (Substitution.free_map τ) body
  have hBody :
      Formula.substitute (Substitution.free_map τ) body =
        ((arity ∈ₘ ωₘ) ∧ₘ
          (predicate_interpretation_key_term arity symbol ∈ₘ symbols)) ∧ₘ
          (related_term_list_code_atₘ(symbols, depth, arity, arguments) ∧ₘ
            (code ≐ₘ pred_codeₘ(arity, symbol, arguments))) := by
    simp [body, Formula.substitute, Formula.substituteMapped,
      Substitution.free_map, VariableSubstitution.cons, Term.substituteMapped,
      Arguments.substituteMapped,
      structural_list_code_term, predicate_formula_code_term,
      structural_node_code_term, structural_raw_node_code_term,
      godel_pairing_term, predicate_interpretation_key_term, τ,
      hSymbolsClosed, hDepthClosed, hCodeClosed]
  rw [hBody]
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro hArity hKey)
    (FirstOrder.Derives.conj_intro hArguments hCode)

private theorem ifc_related_formula_universal_condition_intro
    (symbols depth code body : SetOpenTerm [])
    (hBody : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(symbols, Sₘ(depth), body))
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ all_codeₘ(body)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_universal_condition symbols depth code := by
  unfold related_formula_universal_condition
  apply FirstOrder.Derives.exists_intro body
  rw [Formula.instantiateTop_abstractFreeTop]
  let τ : VariableSubstitution signature [SetSort.set] [] [] :=
    VariableSubstitution.instantiateFreeTop body
  have hSymbolsClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (symbols.weakenFree SetSort.set) = symbols :=
    ifc_closed_one τ symbols
  have hDepthClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (Sₘ(depth.weakenFree SetSort.set)) = Sₘ(depth) := by
    change
      Sₘ(Term.substituteMapped VariableSubstitution.boundId τ
        (depth.weakenFree SetSort.set)) = Sₘ(depth)
    rw [ifc_closed_one τ depth]
  have hCodeClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (code.weakenFree SetSort.set) = code :=
    ifc_closed_one τ code
  have hAllClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          ((all_codeₘ(.fvar .here)) : SetOpenTerm [SetSort.set]) =
        all_codeₘ(body) := by
    simp only [Term.substituteMapped, Arguments.substituteMapped, τ]
    rfl
  simp only [Formula.instantiateFreeTop]
  let bodyFormula : SetOpenFormula [SetSort.set] :=
    related_formula_code_atₘ(
      symbols.weakenFree SetSort.set,
      Sₘ(depth.weakenFree SetSort.set), .fvar .here) ∧ₘ
      ((code.weakenFree SetSort.set) ≐ₘ all_codeₘ(.fvar .here))
  change ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
    Formula.substitute (Substitution.free_map τ) bodyFormula
  have hFormula :
      Formula.substitute (Substitution.free_map τ) bodyFormula =
        related_formula_code_atₘ(symbols, Sₘ(depth), body) ∧ₘ
          (code ≐ₘ all_codeₘ(body)) := by
    change
      (related_formula_code_atₘ(
          Term.substituteMapped VariableSubstitution.boundId τ
            (symbols.weakenFree SetSort.set),
          Term.substituteMapped VariableSubstitution.boundId τ
            (Sₘ(depth.weakenFree SetSort.set)),
          Term.substituteMapped VariableSubstitution.boundId τ
            (.fvar .here)) ∧ₘ
        (Term.substituteMapped VariableSubstitution.boundId τ
            (code.weakenFree SetSort.set) ≐ₘ
          Term.substituteMapped VariableSubstitution.boundId τ
            (all_codeₘ(.fvar .here)))) =
        related_formula_code_atₘ(symbols, Sₘ(depth), body) ∧ₘ
          (code ≐ₘ all_codeₘ(body))
    rw [hSymbolsClosed, hDepthClosed, hAllClosed, hCodeClosed]
    rfl
  rw [hFormula]
  exact FirstOrder.Derives.conj_intro hBody hCode

private theorem ifc_structural_node_code_mem
    (tag : StructuralCodeTag) (fields : List (SetOpenTerm []))
    (hFields : ∀ field ∈ fields,
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        field ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      structural_node_code_term tag fields ∈ₘ ωₘ :=
  ifc_formal_to_carrier
    (structural_node_code_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) tag fields hFields)

private theorem ifc_quote_term_code_mem
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      (quote_term term : SetOpenTerm []) ∈ₘ ωₘ :=
  term_code_at_code_mem_of_derives
    (numₘ(bound.length))
    (quote_term term : SetOpenTerm [])
    (quote_term_code_at term)

private theorem ifc_quote_formula_code_mem
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      (quote_hilbert formula : SetOpenTerm []) ∈ₘ ωₘ :=
  formula_code_at_code_mem_of_derives
    (numₘ(bound.length))
    (quote_hilbert formula : SetOpenTerm [])
    (quote_hilbert_formula_code_at formula)

private theorem ifc_related_formula_equality
    (depth left right : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hLeft : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(NonlogicalSymₘ, depth, left))
    (hRight : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(NonlogicalSymₘ, depth, right))
    (hLeftCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      left ∈ₘ ωₘ)
    (hRightCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      right ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ, depth,
        structural_node_code_term .equality [left, right]) := by
  have hCode := ifc_structural_node_code_mem .equality [left, right] (by
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil] at hField
    rcases hField with hField | hField
    · simpa [hField] using hLeftCode
    · rcases hField with hField | hField
      · simpa [hField] using hRightCode
      · contradiction)
  have hBranch := related_formula_term_binary_condition_intro
    NonlogicalSymₘ depth
    (structural_node_code_term .equality [left, right] : SetOpenTerm [])
    .equality left right hLeft hRight
    (Metatheory.Derives.equality_refl
      (T := intrinsic_syntax_carrier_theory)
      (Γ := ([] : Context signature []))
      (structural_node_code_term .equality [left, right] : SetOpenTerm []))
  exact ifc_related_formula_of_condition
    NonlogicalSymₘ depth
    (structural_node_code_term .equality [left, right] : SetOpenTerm [])
    hDepth
    (by simpa using hCode)
    (FirstOrder.Derives.disj_intro_left hBranch)

theorem related_formula_equality_code_at_intro
    (depth left right : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hLeft : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(NonlogicalSymₘ, depth, left))
    (hRight : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(NonlogicalSymₘ, depth, right))
    (hLeftCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      left ∈ₘ ωₘ)
    (hRightCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      right ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ, depth,
        structural_node_code_term .equality [left, right]) :=
  ifc_related_formula_equality depth left right hDepth hLeft hRight
    hLeftCode hRightCode

private theorem ifc_related_formula_negation
    (depth body : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hBody : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, depth, body))
    (hBodyCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      body ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ, depth, neg_codeₘ(body)) := by
  have hCode := ifc_structural_node_code_mem StructuralCodeTag.negation [body] (by
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil] at hField
    rcases hField with hField | hField
    · simpa [hField] using hBodyCode
    · contradiction)
  have hBranch := related_formula_negation_condition_intro
    NonlogicalSymₘ depth (neg_codeₘ(body) : SetOpenTerm []) body hBody
    (Metatheory.Derives.equality_refl
      (T := intrinsic_syntax_carrier_theory)
      (Γ := ([] : Context signature []))
      (neg_codeₘ(body) : SetOpenTerm []))
  exact ifc_related_formula_of_condition
    NonlogicalSymₘ depth (neg_codeₘ(body) : SetOpenTerm []) hDepth
    (by simpa [structural_node_code_term, structural_list_code_term] using! hCode)
    (FirstOrder.Derives.disj_intro_right
      (FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_left hBranch))))

private theorem ifc_related_formula_implication
    (depth left right : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hLeft : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, depth, left))
    (hRight : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, depth, right))
    (hLeftCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      left ∈ₘ ωₘ)
    (hRightCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      right ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ, depth, imp_codeₘ(left, right)) := by
  have hCode := ifc_structural_node_code_mem StructuralCodeTag.implication
    [left, right] (by
      intro field hField
      simp only [List.mem_cons, List.not_mem_nil] at hField
      rcases hField with hField | hField
      · simpa [hField] using hLeftCode
      · rcases hField with hField | hField
        · simpa [hField] using hRightCode
        · contradiction)
  have hBranch := related_formula_implication_condition_intro
    NonlogicalSymₘ depth (imp_codeₘ(left, right) : SetOpenTerm []) left right
    hLeft hRight
    (Metatheory.Derives.equality_refl
      (T := intrinsic_syntax_carrier_theory)
      (Γ := ([] : Context signature []))
      (imp_codeₘ(left, right) : SetOpenTerm []))
  exact ifc_related_formula_of_condition
    NonlogicalSymₘ depth (imp_codeₘ(left, right) : SetOpenTerm []) hDepth
    (by simpa [structural_node_code_term, structural_list_code_term] using! hCode)
    (FirstOrder.Derives.disj_intro_right
      (FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_left hBranch)))))

private theorem ifc_related_formula_universal
    (depth body : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hBody : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, Sₘ(depth), body))
    (hBodyCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      body ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ, depth, all_codeₘ(body)) := by
  have hCode := ifc_structural_node_code_mem StructuralCodeTag.universal [body] (by
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil] at hField
    rcases hField with hField | hField
    · simpa [hField] using hBodyCode
    · contradiction)
  have hBranch := ifc_related_formula_universal_condition_intro
    NonlogicalSymₘ depth (all_codeₘ(body) : SetOpenTerm []) body hBody
    (Metatheory.Derives.equality_refl
      (T := intrinsic_syntax_carrier_theory)
      (Γ := ([] : Context signature []))
      (all_codeₘ(body) : SetOpenTerm []))
  exact ifc_related_formula_of_condition
    NonlogicalSymₘ depth (all_codeₘ(body) : SetOpenTerm []) hDepth
    (by simpa [structural_node_code_term, structural_list_code_term] using! hCode)
    (FirstOrder.Derives.disj_intro_right
      (FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_right hBranch)))))

theorem related_formula_implication_code_at_intro
    (depth left right : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hLeft : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, depth, left))
    (hRight : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, depth, right))
    (hLeftCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      left ∈ₘ ωₘ)
    (hRightCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      right ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, depth, imp_codeₘ(left, right)) :=
  ifc_related_formula_implication depth left right hDepth hLeft hRight
    hLeftCode hRightCode

theorem related_formula_universal_code_at_intro
    (depth body : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hBody : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, Sₘ(depth), body))
    (hBodyCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      body ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, depth, all_codeₘ(body)) :=
  ifc_related_formula_universal depth body hDepth hBody hBodyCode

private theorem ifc_related_quote_relation_formula_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (relation : σ.RelSymbol)
    (arguments : Arguments σ bound free (σ.relDomain relation)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ,
        numₘ(bound.length),
        (quote_relation relation arguments : SetOpenTerm [])) := by
  have hDepth := ifc_omega_mem
    (Γ := ([] : Context signature [])) bound.length
  generalize hKind : QuotationNumbering.relation_kind relation = kind
  cases kind with
  | membership =>
      generalize hTypedArguments :
        (QuotationNumbering.membership_domain relation hKind ▸ arguments) =
          typedArguments
      cases typedArguments with
      | cons left rest =>
          cases rest with
          | cons right tail =>
              cases tail with
              | nil =>
                  have hLeft := related_quote_term_code_at left
                  have hRight := related_quote_term_code_at right
                  have hLeftFormal := quote_term_code_at left
                  have hRightFormal := quote_term_code_at right
                  have hLeftCode := term_code_at_code_mem_of_derives
                    (numₘ(bound.length))
                    (quote_term left : SetOpenTerm []) hLeftFormal
                  have hRightCode := term_code_at_code_mem_of_derives
                    (numₘ(bound.length))
                    (quote_term right : SetOpenTerm []) hRightFormal
                  have hCodeFormal :=
                    structural_node_code_mem_formal_language_encoding_theory
                      (Γ := ([] : Context signature []))
                      StructuralCodeTag.membership
                      [(quote_term left : SetOpenTerm []),
                        (quote_term right : SetOpenTerm [])] (by
                        intro field hField
                        simp only [List.mem_cons, List.not_mem_nil] at hField
                        rcases hField with hField | hField
                        · simpa [hField] using hLeftCode
                        · rcases hField with hField | hField
                          · simpa [hField] using hRightCode
                          · contradiction)
                  have hCode := ifc_formal_to_carrier hCodeFormal
                  have hBranch := related_formula_term_binary_condition_intro
                    NonlogicalSymₘ
                    (numₘ(bound.length))
                    (mem_codeₘ(
                      (quote_term left : SetOpenTerm []),
                      (quote_term right : SetOpenTerm [])) : SetOpenTerm [])
                    StructuralCodeTag.membership
                    (quote_term left : SetOpenTerm [])
                    (quote_term right : SetOpenTerm [])
                    hLeft hRight
                    (Metatheory.Derives.equality_refl
                      (mem_codeₘ(
                        (quote_term left : SetOpenTerm []),
                        (quote_term right : SetOpenTerm [])) :
                        SetOpenTerm []))
                  have hResult := ifc_related_formula_of_condition
                    NonlogicalSymₘ
                    (numₘ(bound.length))
                    (mem_codeₘ(
                      (quote_term left : SetOpenTerm []),
                      (quote_term right : SetOpenTerm [])) : SetOpenTerm [])
                    hDepth
                    (by
                      simpa [structural_node_code_term,
                        structural_list_code_term] using! hCode)
                    (FirstOrder.Derives.disj_intro_right
                      (FirstOrder.Derives.disj_intro_left hBranch))
                  have hQuote :
                      quote_relation relation arguments =
                        mem_codeₘ(
                          (quote_term left : SetOpenTerm []),
                          (quote_term right : SetOpenTerm [])) := by
                    rw [quote_relation_membership_eq relation arguments hKind]
                    apply quote_membership_arguments_cons_eq
                      relation arguments hKind left right
                    exact hTypedArguments
                  rw [hQuote]
                  exact hResult
  | predicate =>
      have hArguments := related_quote_arguments_term_list_code_at arguments
      have hArgumentsDirect := quote_arguments_term_list_code_at arguments
      have hArity := ifc_omega_mem (Γ := ([] : Context signature []))
        (σ.relArity relation)
      have hArgumentsCode := term_list_code_at_code_mem_of_derives
        (numₘ(bound.length))
        (numₘ(σ.relArity relation))
        (quote_arguments arguments : SetOpenTerm [])
        (by simpa [Signature.relArity] using hArgumentsDirect)
      have hArityFormal := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) (σ.relArity relation)
      have hSymbolFormal := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature []))
          (QuotationNumbering.relation_number relation)
      have hKeyInner := godel_pair_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature []))
        (numₘ(σ.relArity relation) : SetOpenTerm [])
        (numₘ(QuotationNumbering.relation_number relation) : SetOpenTerm [])
        hArityFormal hSymbolFormal
      have hKeyOmega := godel_pair_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature []))
        (numₘ(2) : SetOpenTerm [])
        (godel_pairₘ(
          numₘ(σ.relArity relation),
          numₘ(QuotationNumbering.relation_number relation)))
        (finite_numeral_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) 2)
        hKeyInner
      have hKey := ifc_nonlogical_symbol_mem_of_omega
        (predicate_interpretation_key_term
          (numₘ(σ.relArity relation))
          (numₘ(QuotationNumbering.relation_number relation)))
        (by simpa [predicate_interpretation_key_term] using hKeyOmega)
      have hCodeFormal :=
        structural_node_code_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) StructuralCodeTag.predicate
          [numₘ(σ.relArity relation),
            numₘ(QuotationNumbering.relation_number relation),
            (quote_arguments arguments : SetOpenTerm [])] (by
            intro field hField
            simp only [List.mem_cons, List.not_mem_nil] at hField
            rcases hField with hField | hField
            · simpa [hField] using hArityFormal
            · rcases hField with hField | hField
              · simpa [hField] using hSymbolFormal
              · rcases hField with hField | hField
                · simpa [hField] using hArgumentsCode
                · contradiction)
      have hCode := ifc_formal_to_carrier hCodeFormal
      have hBranch := ifc_related_formula_predicate_condition_intro
        NonlogicalSymₘ
        (numₘ(bound.length))
        (pred_codeₘ(
          numₘ(σ.relArity relation),
          numₘ(QuotationNumbering.relation_number relation),
          (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm [])
        (numₘ(σ.relArity relation))
        (numₘ(QuotationNumbering.relation_number relation))
        (quote_arguments arguments : SetOpenTerm [])
        hArity hKey hArguments
        (Metatheory.Derives.equality_refl
          (pred_codeₘ(
            numₘ(σ.relArity relation),
            numₘ(QuotationNumbering.relation_number relation),
            (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm []))
      have hResult := ifc_related_formula_of_condition
        NonlogicalSymₘ
        (numₘ(bound.length))
        (pred_codeₘ(
          numₘ(σ.relArity relation),
          numₘ(QuotationNumbering.relation_number relation),
          (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm [])
        hDepth
        (by
          simpa [structural_node_code_term, structural_list_code_term] using!
            hCode)
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_left hBranch)))
      rw [quote_relation_predicate_eq relation arguments hKind]
      exact hResult

theorem related_quote_relation_formula_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (relation : σ.RelSymbol)
    (arguments : Arguments σ bound free (σ.relDomain relation))
    (depth : Nat) (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ,
        numₘ(depth),
        (quote_relation relation arguments : SetOpenTerm [])) := by
  have hDepth := ifc_omega_mem
    (Γ := ([] : Context signature [])) depth
  generalize hKind : QuotationNumbering.relation_kind relation = kind
  cases kind with
  | membership =>
      generalize hTypedArguments :
        (QuotationNumbering.membership_domain relation hKind ▸ arguments) =
          typedArguments
      cases typedArguments with
      | cons left rest =>
          cases rest with
          | cons right tail =>
              cases tail with
              | nil =>
                  have hLeft := related_quote_term_code_at_of_depth left depth hBound
                  have hRight := related_quote_term_code_at_of_depth right depth hBound
                  have hLeftFormal := quote_term_code_at_of_depth left depth hBound
                  have hRightFormal := quote_term_code_at_of_depth right depth hBound
                  have hLeftCode := term_code_at_code_mem_of_derives
                    (numₘ(depth))
                    (quote_term left : SetOpenTerm []) hLeftFormal
                  have hRightCode := term_code_at_code_mem_of_derives
                    (numₘ(depth))
                    (quote_term right : SetOpenTerm []) hRightFormal
                  have hCodeFormal :=
                    structural_node_code_mem_formal_language_encoding_theory
                      (Γ := ([] : Context signature []))
                      StructuralCodeTag.membership
                      [(quote_term left : SetOpenTerm []),
                        (quote_term right : SetOpenTerm [])] (by
                        intro field hField
                        simp only [List.mem_cons, List.not_mem_nil] at hField
                        rcases hField with hField | hField
                        · simpa [hField] using hLeftCode
                        · rcases hField with hField | hField
                          · simpa [hField] using hRightCode
                          · contradiction)
                  have hCode := ifc_formal_to_carrier hCodeFormal
                  have hBranch := related_formula_term_binary_condition_intro
                    NonlogicalSymₘ
                    (numₘ(depth))
                    (mem_codeₘ(
                      (quote_term left : SetOpenTerm []),
                      (quote_term right : SetOpenTerm [])) : SetOpenTerm [])
                    StructuralCodeTag.membership
                    (quote_term left : SetOpenTerm [])
                    (quote_term right : SetOpenTerm [])
                    hLeft hRight
                    (Metatheory.Derives.equality_refl
                      (mem_codeₘ(
                        (quote_term left : SetOpenTerm []),
                        (quote_term right : SetOpenTerm [])) :
                        SetOpenTerm []))
                  have hResult := ifc_related_formula_of_condition
                    NonlogicalSymₘ
                    (numₘ(depth))
                    (mem_codeₘ(
                      (quote_term left : SetOpenTerm []),
                      (quote_term right : SetOpenTerm [])) : SetOpenTerm [])
                    hDepth
                    (by
                      simpa [structural_node_code_term,
                        structural_list_code_term] using! hCode)
                    (FirstOrder.Derives.disj_intro_right
                      (FirstOrder.Derives.disj_intro_left hBranch))
                  have hQuote :
                      quote_relation relation arguments =
                        mem_codeₘ(
                          (quote_term left : SetOpenTerm []),
                          (quote_term right : SetOpenTerm [])) := by
                    rw [quote_relation_membership_eq relation arguments hKind]
                    apply quote_membership_arguments_cons_eq
                      relation arguments hKind left right
                    exact hTypedArguments
                  rw [hQuote]
                  exact hResult
  | predicate =>
      have hArguments := related_quote_arguments_term_list_code_at_of_depth arguments depth hBound
      have hArgumentsDirect := quote_arguments_term_list_code_at_of_depth arguments depth hBound
      have hArity := ifc_omega_mem (Γ := ([] : Context signature []))
        (σ.relArity relation)
      have hArgumentsCode := term_list_code_at_code_mem_of_derives
        (numₘ(depth))
        (numₘ(σ.relArity relation))
        (quote_arguments arguments : SetOpenTerm [])
        (by simpa [Signature.relArity] using hArgumentsDirect)
      have hArityFormal := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) (σ.relArity relation)
      have hSymbolFormal := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature []))
          (QuotationNumbering.relation_number relation)
      have hKeyInner := godel_pair_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature []))
        (numₘ(σ.relArity relation) : SetOpenTerm [])
        (numₘ(QuotationNumbering.relation_number relation) : SetOpenTerm [])
        hArityFormal hSymbolFormal
      have hKeyOmega := godel_pair_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature []))
        (numₘ(2) : SetOpenTerm [])
        (godel_pairₘ(
          numₘ(σ.relArity relation),
          numₘ(QuotationNumbering.relation_number relation)))
        (finite_numeral_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) 2)
        hKeyInner
      have hKey := ifc_nonlogical_symbol_mem_of_omega
        (predicate_interpretation_key_term
          (numₘ(σ.relArity relation))
          (numₘ(QuotationNumbering.relation_number relation)))
        (by simpa [predicate_interpretation_key_term] using hKeyOmega)
      have hCodeFormal :=
        structural_node_code_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) StructuralCodeTag.predicate
          [numₘ(σ.relArity relation),
            numₘ(QuotationNumbering.relation_number relation),
            (quote_arguments arguments : SetOpenTerm [])] (by
            intro field hField
            simp only [List.mem_cons, List.not_mem_nil] at hField
            rcases hField with hField | hField
            · simpa [hField] using hArityFormal
            · rcases hField with hField | hField
              · simpa [hField] using hSymbolFormal
              · rcases hField with hField | hField
                · simpa [hField] using hArgumentsCode
                · contradiction)
      have hCode := ifc_formal_to_carrier hCodeFormal
      have hBranch := ifc_related_formula_predicate_condition_intro
        NonlogicalSymₘ
        (numₘ(depth))
        (pred_codeₘ(
          numₘ(σ.relArity relation),
          numₘ(QuotationNumbering.relation_number relation),
          (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm [])
        (numₘ(σ.relArity relation))
        (numₘ(QuotationNumbering.relation_number relation))
        (quote_arguments arguments : SetOpenTerm [])
        hArity hKey hArguments
        (Metatheory.Derives.equality_refl
          (pred_codeₘ(
            numₘ(σ.relArity relation),
            numₘ(QuotationNumbering.relation_number relation),
            (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm []))
      have hResult := ifc_related_formula_of_condition
        NonlogicalSymₘ
        (numₘ(depth))
        (pred_codeₘ(
          numₘ(σ.relArity relation),
          numₘ(QuotationNumbering.relation_number relation),
          (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm [])
        hDepth
        (by
          simpa [structural_node_code_term, structural_list_code_term] using!
            hCode)
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_left hBranch)))
      rw [quote_relation_predicate_eq relation arguments hKind]
      exact hResult
theorem related_quote_hilbert_formula_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) (depth : Nat) (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ,
        numₘ(depth),
        (quote_hilbert formula : SetOpenTerm [])) := by
  exact (Formula.rec
    (motive := fun bound free formula =>
      ∀ depth, bound.length ≤ depth →
        ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
          related_formula_code_atₘ(
            NonlogicalSymₘ,
            numₘ(depth),
          (quote_hilbert formula : SetOpenTerm [])))
    (fun {bound free} => by
      intro depth hBound
      have hDepth := ifc_omega_mem
        (Γ := ([] : Context signature [])) depth
      have hDepthFormal := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hSuccessor := ifc_formal_to_carrier
        (successor_mem_omega_formal_language_encoding_theory
          (numₘ(depth) : SetOpenTerm []) hDepthFormal)
      have hVar := related_quote_term_code_at_of_depth
        (bound := QuotationNumbering.objectSort :: bound)
        (free := free) (sort := QuotationNumbering.objectSort) (.bvar (.here)) (depth + 1) (by
          simp
          omega)
      have hVar' :
          ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
            related_term_code_atₘ(
              NonlogicalSymₘ,
              Sₘ(numₘ(depth)),
              (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])) := by
        simpa [quote_term, finite_numeral_term] using! hVar
      have hVarCode := ifc_quote_term_code_mem
        (bound := QuotationNumbering.objectSort :: bound)
        (free := free) (sort := QuotationNumbering.objectSort) (.bvar (.here))
      have hEqCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (eq_codeₘ(
              (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []),
              (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])) : SetOpenTerm []) ∈ₘ ωₘ :=
        structural_node_code_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) StructuralCodeTag.equality
          [bound_var_codeₘ(numₘ(0)), bound_var_codeₘ(numₘ(0))] (by
            intro field hField
            simp only [List.mem_cons, List.not_mem_nil] at hField
            rcases hField with hField | hField
            · simpa [hField] using! hVarCode
            · rcases hField with hField | hField
              · simpa [hField] using! hVarCode
              · contradiction)
      have hEq := ifc_related_formula_equality
        (Sₘ(numₘ(depth)))
        (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])
        (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])
        hSuccessor hVar' hVar' hVarCode hVarCode
      have hAllCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (all_codeₘ(
              eq_codeₘ(
                (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []),
                (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []))) :
              SetOpenTerm []) ∈ₘ ωₘ :=
        structural_node_code_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) StructuralCodeTag.universal
          [eq_codeₘ(
            (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []),
            (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []))] (by
            intro field hField
            simp only [List.mem_cons, List.not_mem_nil] at hField
            rcases hField with hField | hField
            · simpa [hField] using hEqCode
            · contradiction)
      have hAll := ifc_related_formula_universal
        (numₘ(depth))
        (eq_codeₘ(
          (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []),
          (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])) : SetOpenTerm [])
        hDepth hEq hEqCode
      have hNeg := ifc_related_formula_negation
        (numₘ(depth))
        (all_codeₘ(
          eq_codeₘ(
            (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []),
            (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []))) : SetOpenTerm [])
        hDepth hAll hAllCode
      simpa [quote_hilbert] using hNeg)
    (fun {bound free} => by
      intro depth hBound
      have hDepth := ifc_omega_mem
        (Γ := ([] : Context signature [])) depth
      have hDepthFormal := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hSuccessor := ifc_formal_to_carrier
        (successor_mem_omega_formal_language_encoding_theory
          (numₘ(depth) : SetOpenTerm []) hDepthFormal)
      have hVar := related_quote_term_code_at_of_depth
        (bound := QuotationNumbering.objectSort :: bound)
        (free := free) (sort := QuotationNumbering.objectSort) (.bvar (.here)) (depth + 1) (by
          simp
          omega)
      have hVar' :
          ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
            related_term_code_atₘ(
              NonlogicalSymₘ,
              Sₘ(numₘ(depth)),
              (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])) := by
        simpa [quote_term, finite_numeral_term] using! hVar
      have hVarCode := ifc_quote_term_code_mem
        (bound := QuotationNumbering.objectSort :: bound)
        (free := free) (sort := QuotationNumbering.objectSort) (.bvar (.here))
      have hEqCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (eq_codeₘ(
              (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []),
              (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])) : SetOpenTerm []) ∈ₘ ωₘ :=
        structural_node_code_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) StructuralCodeTag.equality
          [bound_var_codeₘ(numₘ(0)), bound_var_codeₘ(numₘ(0))] (by
            intro field hField
            simp only [List.mem_cons, List.not_mem_nil] at hField
            rcases hField with hField | hField
            · simpa [hField] using! hVarCode
            · rcases hField with hField | hField
              · simpa [hField] using! hVarCode
              · contradiction)
      have hEq := ifc_related_formula_equality
        (Sₘ(numₘ(depth)))
        (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])
        (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])
        hSuccessor hVar' hVar' hVarCode hVarCode
      have hAll := ifc_related_formula_universal
        (numₘ(depth))
        (eq_codeₘ(
          (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []),
          (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])) : SetOpenTerm [])
        hDepth hEq hEqCode
      simpa [quote_hilbert] using hAll)
    (fun {bound free} relation arguments => by
      intro depth hBound
      simpa [quote_hilbert] using
        (related_quote_relation_formula_code_at_of_depth relation arguments depth hBound))
    (fun {bound free} {sort} left right => by
      intro depth hBound
      have hDepth := ifc_omega_mem
        (Γ := ([] : Context signature [])) depth
      have hLeft := related_quote_term_code_at_of_depth left depth hBound
      have hRight := related_quote_term_code_at_of_depth right depth hBound
      have hLeftCode := ifc_quote_term_code_mem left
      have hRightCode := ifc_quote_term_code_mem right
      have hResult := ifc_related_formula_equality
        (numₘ(depth))
        (quote_term left : SetOpenTerm [])
        (quote_term right : SetOpenTerm [])
        hDepth hLeft hRight hLeftCode hRightCode
      simpa [quote_hilbert] using hResult)
    (fun {bound free} body ih => by
      intro depth hBound
      have hDepth := ifc_omega_mem
        (Γ := ([] : Context signature [])) depth
      have hBodyCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (quote_hilbert body : SetOpenTerm []) ∈ₘ ωₘ :=
        ifc_quote_formula_code_mem body
      have hResult := ifc_related_formula_negation
        (numₘ(depth))
        (quote_hilbert body : SetOpenTerm []) hDepth (ih depth hBound) hBodyCode
      simpa [quote_hilbert] using hResult)
    (fun {bound free} left right ihLeft ihRight => by
      intro depth hBound
      have hDepth := ifc_omega_mem
        (Γ := ([] : Context signature [])) depth
      have hLeftCode := ifc_quote_formula_code_mem left
      have hRightCode := ifc_quote_formula_code_mem right
      have hRightNeg := ifc_related_formula_negation
        (numₘ(depth))
        (quote_hilbert right : SetOpenTerm []) hDepth (ihRight depth hBound) hRightCode
      have hRightNegCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (neg_codeₘ(quote_hilbert right) : SetOpenTerm []) ∈ₘ ωₘ := by
        simpa [quote_hilbert] using
          (ifc_quote_formula_code_mem (Formula.neg right))
      have hImp := ifc_related_formula_implication
        (numₘ(depth))
        (quote_hilbert left : SetOpenTerm [])
        (neg_codeₘ(quote_hilbert right) : SetOpenTerm [])
        hDepth (ihLeft depth hBound) hRightNeg hLeftCode hRightNegCode
      have hImpCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (imp_codeₘ(
              (quote_hilbert left : SetOpenTerm []),
              neg_codeₘ(quote_hilbert right)) : SetOpenTerm []) ∈ₘ ωₘ := by
        simpa [quote_hilbert] using
          (ifc_quote_formula_code_mem (Formula.imp left (Formula.neg right)))
      have hNeg := ifc_related_formula_negation
        (numₘ(depth))
        (imp_codeₘ(
          (quote_hilbert left : SetOpenTerm []),
          neg_codeₘ(quote_hilbert right)) : SetOpenTerm [])
        hDepth hImp hImpCode
      simpa [quote_hilbert] using hNeg)
    (fun {bound free} left right ihLeft ihRight => by
      intro depth hBound
      have hDepth := ifc_omega_mem
        (Γ := ([] : Context signature [])) depth
      have hLeftCode := ifc_quote_formula_code_mem left
      have hRightCode := ifc_quote_formula_code_mem right
      have hLeftNeg := ifc_related_formula_negation
        (numₘ(depth))
        (quote_hilbert left : SetOpenTerm []) hDepth (ihLeft depth hBound) hLeftCode
      have hLeftNegCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (neg_codeₘ(quote_hilbert left) : SetOpenTerm []) ∈ₘ ωₘ := by
        simpa [quote_hilbert] using
          (ifc_quote_formula_code_mem (Formula.neg left))
      have hImp := ifc_related_formula_implication
        (numₘ(depth))
        (neg_codeₘ(quote_hilbert left) : SetOpenTerm [])
        (quote_hilbert right : SetOpenTerm [])
        hDepth hLeftNeg (ihRight depth hBound) hLeftNegCode hRightCode
      simpa [quote_hilbert] using hImp)
    (fun {bound free} left right ihLeft ihRight => by
      intro depth hBound
      have hDepth := ifc_omega_mem
        (Γ := ([] : Context signature [])) depth
      have hLeftCode := ifc_quote_formula_code_mem left
      have hRightCode := ifc_quote_formula_code_mem right
      have hResult := ifc_related_formula_implication
        (numₘ(depth))
        (quote_hilbert left : SetOpenTerm [])
        (quote_hilbert right : SetOpenTerm [])
        hDepth (ihLeft depth hBound) (ihRight depth hBound) hLeftCode hRightCode
      simpa [quote_hilbert] using hResult)
    (fun {bound free} left right ihLeft ihRight => by
      intro depth hBound
      have hDepth := ifc_omega_mem
        (Γ := ([] : Context signature [])) depth
      have hLeftCode := ifc_quote_formula_code_mem left
      have hRightCode := ifc_quote_formula_code_mem right
      have hLeftRight := ifc_related_formula_implication
        (numₘ(depth))
        (quote_hilbert left : SetOpenTerm [])
        (quote_hilbert right : SetOpenTerm [])
        hDepth (ihLeft depth hBound) (ihRight depth hBound) hLeftCode hRightCode
      have hRightLeft := ifc_related_formula_implication
        (numₘ(depth))
        (quote_hilbert right : SetOpenTerm [])
        (quote_hilbert left : SetOpenTerm [])
        hDepth (ihRight depth hBound) (ihLeft depth hBound) hRightCode hLeftCode
      have hRightLeftCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (imp_codeₘ(
              (quote_hilbert right : SetOpenTerm []),
              (quote_hilbert left : SetOpenTerm [])) : SetOpenTerm []) ∈ₘ ωₘ := by
        simpa [quote_hilbert] using
          (ifc_quote_formula_code_mem (Formula.imp right left))
      have hRightLeftNeg := ifc_related_formula_negation
        (numₘ(depth))
        (imp_codeₘ(
          (quote_hilbert right : SetOpenTerm []),
          (quote_hilbert left : SetOpenTerm [])) : SetOpenTerm [])
        hDepth hRightLeft hRightLeftCode
      have hLeftRightCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (imp_codeₘ(
              (quote_hilbert left : SetOpenTerm []),
              (quote_hilbert right : SetOpenTerm [])) : SetOpenTerm []) ∈ₘ ωₘ := by
        simpa [quote_hilbert] using
          (ifc_quote_formula_code_mem (Formula.imp left right))
      have hRightLeftNegCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (neg_codeₘ(
              imp_codeₘ(
                (quote_hilbert right : SetOpenTerm []),
                (quote_hilbert left : SetOpenTerm []))) : SetOpenTerm []) ∈ₘ ωₘ := by
        simpa [quote_hilbert] using
          (ifc_quote_formula_code_mem (Formula.neg (Formula.imp right left)))
      have hOuterImp := ifc_related_formula_implication
        (numₘ(depth))
        (imp_codeₘ(
          (quote_hilbert left : SetOpenTerm []),
          (quote_hilbert right : SetOpenTerm [])) : SetOpenTerm [])
        (neg_codeₘ(
          imp_codeₘ(
            (quote_hilbert right : SetOpenTerm []),
            (quote_hilbert left : SetOpenTerm []))) : SetOpenTerm [])
        hDepth hLeftRight hRightLeftNeg hLeftRightCode hRightLeftNegCode
      have hOuterImpCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (imp_codeₘ(
              imp_codeₘ(
                (quote_hilbert left : SetOpenTerm []),
                (quote_hilbert right : SetOpenTerm [])),
              neg_codeₘ(
                imp_codeₘ(
                  (quote_hilbert right : SetOpenTerm []),
                  (quote_hilbert left : SetOpenTerm [])))) : SetOpenTerm []) ∈ₘ ωₘ := by
        simpa [quote_hilbert] using
          (ifc_quote_formula_code_mem
            (Formula.imp (Formula.imp left right)
              (Formula.neg (Formula.imp right left))))
      have hResult := ifc_related_formula_negation
        (numₘ(depth))
        (imp_codeₘ(
          imp_codeₘ(
            (quote_hilbert left : SetOpenTerm []),
            (quote_hilbert right : SetOpenTerm [])),
          neg_codeₘ(
            imp_codeₘ(
              (quote_hilbert right : SetOpenTerm []),
              (quote_hilbert left : SetOpenTerm [])))) : SetOpenTerm [])
        hDepth hOuterImp hOuterImpCode
      simpa [quote_hilbert] using hResult)
    (fun {bound free} sort body ih => by
      intro depth hBound
      have hDepth := ifc_omega_mem
        (Γ := ([] : Context signature [])) depth
      have hBodyBound : (sort :: bound).length ≤ depth + 1 := by
        simp
        omega
      have hBody :
          ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
            related_formula_code_atₘ(
              NonlogicalSymₘ,
              Sₘ(numₘ(depth)),
              (quote_hilbert body : SetOpenTerm [])) := by
        simpa [finite_numeral_term] using ih (depth + 1) hBodyBound
      have hBodyCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (quote_hilbert body : SetOpenTerm []) ∈ₘ ωₘ :=
        ifc_quote_formula_code_mem body
      have hResult := ifc_related_formula_universal
        (numₘ(depth))
        (quote_hilbert body : SetOpenTerm []) hDepth hBody hBodyCode
      simpa [quote_hilbert] using hResult)
    (fun {bound free} sort body ih => by
      intro depth hBound
      have hDepth := ifc_omega_mem
        (Γ := ([] : Context signature [])) depth
      have hDepthFormal := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hSuccessor := ifc_formal_to_carrier
        (successor_mem_omega_formal_language_encoding_theory
          (numₘ(depth) : SetOpenTerm []) hDepthFormal)
      have hBodyBound : (sort :: bound).length ≤ depth + 1 := by
        simp
        omega
      have hBody :
          ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
            related_formula_code_atₘ(
              NonlogicalSymₘ,
              Sₘ(numₘ(depth)),
              (quote_hilbert body : SetOpenTerm [])) := by
        simpa [finite_numeral_term] using ih (depth + 1) hBodyBound
      have hBodyCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (quote_hilbert body : SetOpenTerm []) ∈ₘ ωₘ :=
        ifc_quote_formula_code_mem body
      have hBodyNeg := ifc_related_formula_negation
        (Sₘ(numₘ(depth)))
        (quote_hilbert body : SetOpenTerm []) hSuccessor hBody hBodyCode
      have hBodyNegCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (neg_codeₘ(quote_hilbert body) : SetOpenTerm []) ∈ₘ ωₘ := by
        simpa [quote_hilbert] using
          (ifc_quote_formula_code_mem (Formula.neg body))
      have hAll := ifc_related_formula_universal
        (numₘ(depth))
        (neg_codeₘ(quote_hilbert body) : SetOpenTerm [])
        hDepth hBodyNeg hBodyNegCode
      have hAllCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (all_codeₘ(neg_codeₘ(quote_hilbert body)) : SetOpenTerm []) ∈ₘ ωₘ := by
        simpa [quote_hilbert] using
          (ifc_quote_formula_code_mem
            (Formula.forallE sort (Formula.neg body)))
      have hResult := ifc_related_formula_negation
        (numₘ(depth))
        (all_codeₘ(neg_codeₘ(quote_hilbert body)) : SetOpenTerm [])
        hDepth hAll hAllCode
      simpa [quote_hilbert] using hResult)
    formula) depth hBound

theorem related_quote_hilbert_formula_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ,
        numₘ(bound.length),
        (quote_hilbert formula : SetOpenTerm [])) := by
  exact related_quote_hilbert_formula_code_at_of_depth
    (σ := σ) (bound := bound) (free := free)
    formula bound.length (Nat.le_refl _)

theorem related_quote_formula_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) (depth : Nat) (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ,
        numₘ(depth),
        (quote formula : SetOpenTerm [])) := by
  simpa [quote] using
    (related_quote_hilbert_formula_code_at_of_depth
      (σ := σ) (bound := bound) (free := free)
      (Formula.hilbertize QuotationNumbering.objectSort formula) depth hBound)

theorem related_quote_formula_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ,
        numₘ(bound.length),
        (quote formula : SetOpenTerm [])) := by
  exact related_quote_formula_code_at_of_depth
    (σ := σ) (bound := bound) (free := free)
    formula bound.length (Nat.le_refl _)

theorem intrinsic_syntax_carrier_formula_mem_of_related
    (depth code : SetOpenTerm [])
    (hFormulaAt :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, depth, code)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ∈ₘ syntax_formula_code_set_term := by
  let symbols : SetOpenTerm [] := NonlogicalSymₘ
  have hCondition :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_condition symbols code := by
    unfold related_formula_code_condition
    apply FirstOrder.Derives.exists_intro depth
    rw [Formula.instantiateTop_abstractFreeTop]
    change ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      Formula.substituteMapped
        VariableSubstitution.boundId
        (VariableSubstitution.instantiateFreeTop depth)
        (related_formula_code_atₘ(
          symbols.weakenFree SetSort.set,
          (.fvar .here),
          code.weakenFree SetSort.set))
    simpa [symbols, Formula.instantiateFreeTop, Formula.substitute,
      Formula.substituteMapped, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.boundId,
      Term.substituteMapped_weakenFree_instantiateFreeTop,
      Arguments.substituteMapped_weakenFree_instantiateFreeTop,
      Formula.substituteMapped_weakenFree_instantiateFreeTop] using hFormulaAt
  have hSubset := related_nonlogical_symbol_set_subset_derives
    (Γ := ([] : Context signature []))
  have hSetEq :
      (syntax_formula_code_set_term : SetOpenTerm []) =
        RelFormulaCodeₘ(symbols) := by
    rfl
  have hDefinition := FirstOrder.Derives.theory_weaken
    semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
    (related_formula_set_definition_instance_derives
      (Γ := ([] : Context signature [])) symbols syntax_formula_code_set_term)
  have hIff := FirstOrder.Derives.imp_elim hDefinition hSubset
  have hSpec := FirstOrder.Derives.iff_elim_left hIff
    (by
      rw [hSetEq]
      exact Metatheory.Derives.equality_refl
        (T := intrinsic_syntax_carrier_theory)
        (Γ := ([] : Context signature []))
        (RelFormulaCodeₘ(symbols)))
  have hAt := FirstOrder.Derives.forall_elim
    (term := code) hSpec
  have hAt' :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        code ∈ₘ syntax_formula_code_set_term ↔ₘ
          related_formula_code_condition symbols code := by
    simpa [related_formula_set_spec, related_formula_code_condition,
      Formula.instantiateFreeTop,
      Substitution.instantiateFreeTop, Formula.substitute,
      Formula.substituteMapped, Term.substituteFree, Term.substitute,
      Term.substituteMapped, Arguments.substituteMapped,
      VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.liftFree, VariableSubstitution.weakenBound,
      VariableSubstitution.boundId, VariableSubstitution.freeId,
      Term.substituteMapped_weakenFree_instantiateFreeTop,
      Arguments.substituteMapped_weakenFree_instantiateFreeTop,
      Formula.substituteMapped_weakenFree_instantiateFreeTop] using hAt
  exact FirstOrder.Derives.iff_elim_right hAt' hCondition

theorem intrinsic_syntax_carrier_quote_formula_mem
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      (quote formula : SetOpenTerm []) ∈ₘ syntax_formula_code_set_term := by
  exact intrinsic_syntax_carrier_formula_mem_of_related
    (numₘ(bound.length)) (quote formula : SetOpenTerm [])
    (related_quote_formula_code_at formula)

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
