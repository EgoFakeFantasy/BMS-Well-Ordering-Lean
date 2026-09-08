import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSyntaxCarrier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaStructuralCorrectness

/-!
# Quine 结构码的相关语法承载

本模块把宿主内在语法的 Quine quotation 接入相关项、参数列和公式承载集合。
所有见证都来自 `Term`、`Arguments` 与 `Formula` 的结构递归；承载理论只负责
提供相关语法递归方程及 `NonlogicalSym = ω` 的对象侧合同。
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

private theorem formal_to_carrier
    {free : SetContext} {Γ : Context signature free}
    {φ : SetOpenFormula free}
    (hφ : Γ ⊢ₘ[formal_language_encoding_theory] φ) :
    Γ ⊢ₘ[intrinsic_syntax_carrier_theory] φ :=
  FirstOrder.Derives.theory_weaken
    formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory hφ

private theorem omega_mem_carrier
    {free : SetContext} {Γ : Context signature free}
    (number : Nat) :
    Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
      (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ :=
  formal_to_carrier
    (finite_numeral_mem_formal_language_encoding_theory
      (Γ := Γ) number)

private theorem nonlogical_symbol_mem_of_omega
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
      (by simpa using!
        related_symbol_definition_axiom_derives)
  exact FirstOrder.Derives.iff_elim_right
    (membership_right_iff_of_equality
      (T := intrinsic_syntax_carrier_theory)
      (Γ := ([] : Context signature []))
      code NonlogicalSymₘ ωₘ hEquality)
    (formal_to_carrier hCode)

private theorem related_term_code_free_condition_intro
    (index code : SetOpenTerm [])
    (hIndex : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      index ∈ₘ ωₘ)
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ free_var_codeₘ(index)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_free_condition code := by
  unfold related_term_code_free_condition
  apply FirstOrder.Derives.exists_intro index
  simpa using! FirstOrder.Derives.conj_intro hIndex hCode

private theorem related_term_code_bound_condition_intro
    (depth index code : SetOpenTerm [])
    (hIndex : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      index ∈ₘ depth)
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ bound_var_codeₘ(index)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_bound_condition depth code := by
  unfold related_term_code_bound_condition
  apply FirstOrder.Derives.exists_intro index
  set_option trace.Meta.Tactic.simp.rewrite true in
    simpa [Formula.instantiateFreeTop, Formula.substituteFree,
    Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.liftFree, VariableSubstitution.weakenBound,
    VariableSubstitution.boundId, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_instantiateFreeTop,
    Arguments.substituteMapped_weakenFree_instantiateFreeTop] using
    FirstOrder.Derives.conj_intro hIndex hCode

private theorem related_term_code_constant_condition_intro
    (symbols index code : SetOpenTerm [])
    (hIndex : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      constant_interpretation_key_term index ∈ₘ symbols)
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ const_codeₘ(index)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_constant_condition symbols code := by
  unfold related_term_code_constant_condition
  apply FirstOrder.Derives.exists_intro index
  simpa [Formula.instantiateFreeTop, Formula.substituteFree,
    Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.liftFree, VariableSubstitution.weakenBound,
    VariableSubstitution.boundId, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_instantiateFreeTop,
    Arguments.substituteMapped_weakenFree_instantiateFreeTop,
    constant_interpretation_key_term] using
    FirstOrder.Derives.conj_intro hIndex hCode

private theorem related_term_code_at_of_condition
    (symbols depth code : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ∈ₘ ωₘ)
    (hBranch : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_free_condition code ∨ₘ
        (related_term_code_bound_condition depth code ∨ₘ
          (related_term_code_constant_condition symbols code ∨ₘ
            related_term_code_application_condition symbols depth code))) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(symbols, depth, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (FirstOrder.Derives.theory_weaken
      semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
      (related_term_code_at_definition_instance_derives
        (Γ := ([] : Context signature [])) symbols depth code))
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro hDepth hCode) hBranch

private theorem related_term_list_code_at_of_condition
    (symbols depth length code : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hLength : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      length ∈ₘ ωₘ)
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ∈ₘ ωₘ)
    (hBranch : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      (length ≐ₘ numₘ(0)) ∧ₘ (code ≐ₘ code_nilₘ) ∨ₘ
        related_term_list_code_cons_condition symbols depth length code) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_list_code_atₘ(symbols, depth, length, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (FirstOrder.Derives.theory_weaken
      semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
      (related_term_list_code_at_definition_instance_derives
        (Γ := ([] : Context signature [])) symbols depth length code))
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hDepth hLength) hCode) hBranch

private theorem related_formula_code_at_of_condition
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

private theorem debug_three_free_weakening (term : SetOpenTerm []) :
    Term.renameMapped
        (fun {_s} => VariableRenaming.id)
        (fun {_s} =>
          VariableRenaming.comp
            (fun {_s} => VariableRenaming.weaken SetSort.set)
            (fun {_s} =>
              VariableRenaming.comp
                (fun {_s} => VariableRenaming.weaken SetSort.set)
                (fun {_s} => VariableRenaming.weaken SetSort.set)))
        term =
      term_weaken_free_three term := by
  exact Term.renameMapped_three_weakenFree term

private theorem related_term_list_code_cons_condition_intro
    (symbols depth length code previousLength head tail : SetOpenTerm [])
    (hPreviousLength : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      previousLength ∈ₘ ωₘ)
    (hLength : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      length ≐ₘ Sₘ(previousLength))
    (hHead : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(symbols, depth, head))
    (hTail : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_list_code_atₘ(symbols, depth, previousLength, tail))
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ code_consₘ(head, tail)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_list_code_cons_condition symbols depth length code := by
  unfold related_term_list_code_cons_condition
  apply FirstOrder.Derives.exists_intro tail
  rw [Formula.instantiateTop_abstractFreeTop,
    Formula.instantiateFreeTop_existsFreeTop]
  apply FirstOrder.Derives.exists_intro head
  rw [Formula.substituteFree_existsFreeTop]
  rw [Formula.instantiateTop_abstractFreeTop,
    Formula.instantiateFreeTop_existsFreeTop]
  apply FirstOrder.Derives.exists_intro previousLength
  rw [Formula.instantiateTop_abstractFreeTop]
  rw [three_free_substitution_beta]
  simp only [ Formula.substituteFree]
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set] [] [] :=
    VariableSubstitution.cons previousLength
      (VariableSubstitution.cons head
        (VariableSubstitution.cons tail VariableSubstitution.empty))
  have hBound :
      (VariableRenaming.comp
        (outer := (@VariableRenaming.id signature.SortSymbol []))
        (inner := VariableRenaming.comp
          (outer := (@VariableRenaming.id signature.SortSymbol []))
          (inner := (@VariableRenaming.id signature.SortSymbol []))) :
        VariableRenaming (S := signature.SortSymbol) [] []) =
      (@VariableRenaming.id signature.SortSymbol []) := by
    funext resultSort entry
    cases entry
  have hSymbolsClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (term_weaken_free_three symbols) =
        symbols := by
    change
      Term.substituteMapped VariableSubstitution.boundId τ
          (((symbols.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
            SetSort.set) =
        symbols
    exact gq_closed_three_weaken_substitute τ symbols
  have hLengthClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (term_weaken_free_three length) =
        length := by
    change
      Term.substituteMapped VariableSubstitution.boundId τ
          (((length.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
            SetSort.set) =
        length
    exact gq_closed_three_weaken_substitute τ length
  have hDepthClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (term_weaken_free_three depth) =
        depth := by
    change
      Term.substituteMapped VariableSubstitution.boundId τ
          (((depth.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
            SetSort.set) =
        depth
    exact gq_closed_three_weaken_substitute τ depth
  have hCodeClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (term_weaken_free_three code) =
        code := by
    change
      Term.substituteMapped VariableSubstitution.boundId τ
          (((code.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
            SetSort.set) =
        code
    exact gq_closed_three_weaken_substitute τ code
  have hClosed :
      ∀ term : (SetOpenTerm []),
        Term.substituteMapped
            (fun {sort} => VariableSubstitution.boundId)
            (fun {sort} =>
              VariableSubstitution.cons previousLength
                (VariableSubstitution.cons head
                  (VariableSubstitution.cons tail VariableSubstitution.empty)))
            (Term.renameMapped
              (fun {s} => VariableRenaming.id)
              (fun {s} =>
                VariableRenaming.comp
                  (fun {s} => VariableRenaming.weaken SetSort.set)
                  (fun {s} =>
                    VariableRenaming.comp
                      (fun {s} => VariableRenaming.weaken SetSort.set)
                      (fun {s} => VariableRenaming.weaken SetSort.set)))
              term) =
          term := by
    intro term
    rw [debug_three_free_weakening]
    exact gq_closed_three_weaken_substitute τ term
  simpa [Formula.instantiateFreeTop, Formula.substituteFree,
    Substitution.free_map, Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substitute_comp,
    Formula.substituteMapped, Substitution.comp,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_instantiateFreeTop,
    Arguments.substituteMapped_weakenFree_instantiateFreeTop,
    Term.substituteMapped_weakenFree_boundId,
    Arguments.substituteMapped_weakenFree_boundId,
    Term.weakenFree, Term.rename, Renaming.weakenFree, Renaming.free,
    Term.renameMapped, VariableRenaming.weaken,
    VariableRenaming.comp, VariableRenaming.id,
    Term.renameMapped_three_weakenFree,
    Arguments.renameMapped_three_weakenFree,
    debug_three_free_weakening, hClosed,
    VariableSubstitution.cons,
    VariableSubstitution.empty, τ, hBound, hSymbolsClosed, hLengthClosed,
    hDepthClosed, hCodeClosed, term_weaken_free_three] using
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hPreviousLength hLength)
        (FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro hHead hTail) hCode)

private theorem related_term_code_application_condition_intro
    (symbols depth code arity symbol arguments : SetOpenTerm [])
    (hArity : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      arity ∈ₘ ωₘ)
    (hKey : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      function_interpretation_key_term arity symbol ∈ₘ symbols)
    (hArguments : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_list_code_atₘ(symbols, depth, arity, arguments))
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ app_codeₘ(arity, symbol, arguments)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_application_condition symbols depth code := by
  unfold related_term_code_application_condition
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
  have hBound :
      (VariableRenaming.comp
        (outer := (@VariableRenaming.id signature.SortSymbol []))
        (inner := VariableRenaming.comp
          (outer := (@VariableRenaming.id signature.SortSymbol []))
          (inner := (@VariableRenaming.id signature.SortSymbol []))) :
        VariableRenaming (S := signature.SortSymbol) [] []) =
      (@VariableRenaming.id signature.SortSymbol []) := by
    funext resultSort entry
    cases entry
  have hSymbolsClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (term_weaken_free_three symbols) =
        symbols := by
    change
      Term.substituteMapped VariableSubstitution.boundId τ
          (((symbols.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
            SetSort.set) =
        symbols
    exact gq_closed_three_weaken_substitute τ symbols
  have hDepthClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (term_weaken_free_three depth) =
        depth := by
    change
      Term.substituteMapped VariableSubstitution.boundId τ
          (((depth.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
            SetSort.set) =
        depth
    exact gq_closed_three_weaken_substitute τ depth
  have hCodeClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (term_weaken_free_three code) =
        code := by
    change
      Term.substituteMapped VariableSubstitution.boundId τ
          (((code.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
            SetSort.set) =
        code
    exact gq_closed_three_weaken_substitute τ code
  have hArityClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (term_weaken_free_three arity) =
        arity := by
    change
      Term.substituteMapped VariableSubstitution.boundId τ
          (((arity.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
            SetSort.set) =
        arity
    exact gq_closed_three_weaken_substitute τ arity
  have hSymbolClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (term_weaken_free_three symbol) =
        symbol := by
    change
      Term.substituteMapped VariableSubstitution.boundId τ
          (((symbol.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
            SetSort.set) =
        symbol
    exact gq_closed_three_weaken_substitute τ symbol
  have hArgumentsClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (term_weaken_free_three arguments) =
        arguments := by
    change
      Term.substituteMapped VariableSubstitution.boundId τ
          (((arguments.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
            SetSort.set) =
        arguments
    exact gq_closed_three_weaken_substitute τ arguments
  have hAppCodeClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (term_weaken_free_three
            (app_codeₘ(arity, symbol, arguments) : SetOpenTerm [])) =
        app_codeₘ(arity, symbol, arguments) :=
    gq_closed_three_weaken_substitute τ
      (app_codeₘ(arity, symbol, arguments) : SetOpenTerm [])
  have hKeyClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (term_weaken_free_three
            (function_interpretation_key_term arity symbol)) =
        function_interpretation_key_term arity symbol :=
    gq_closed_three_weaken_substitute τ
      (function_interpretation_key_term arity symbol)
  have hClosed :
      ∀ term : (SetOpenTerm []),
        Term.substituteMapped
            (fun {sort} => VariableSubstitution.boundId)
            (fun {sort} =>
              VariableSubstitution.cons arguments
                (VariableSubstitution.cons symbol
                  (VariableSubstitution.cons arity VariableSubstitution.empty)))
            (Term.renameMapped
              (fun {s} => VariableRenaming.id)
              (fun {s} =>
                VariableRenaming.comp
                  (fun {s} => VariableRenaming.weaken SetSort.set)
                  (fun {s} =>
                    VariableRenaming.comp
                      (fun {s} => VariableRenaming.weaken SetSort.set)
                      (fun {s} => VariableRenaming.weaken SetSort.set)))
              term) =
          term := by
    intro term
    rw [debug_three_free_weakening]
    exact gq_closed_three_weaken_substitute τ term
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    ((.fvar (.there (.there .here)) ∈ₘ ωₘ) ∧ₘ
      (function_interpretation_key_term
          (.fvar (.there (.there .here)))
          (.fvar (.there .here)) ∈ₘ
        term_weaken_free_three symbols)) ∧ₘ
      (related_term_list_code_atₘ(
          term_weaken_free_three symbols,
          term_weaken_free_three depth,
          .fvar (.there (.there .here)), .fvar .here) ∧ₘ
        (term_weaken_free_three code ≐ₘ
          app_codeₘ(.fvar (.there (.there .here)),
            .fvar (.there .here), .fvar .here)))
  change ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
    Formula.substitute (Substitution.free_map τ) body
  have hBody :
      Formula.substitute (Substitution.free_map τ) body =
        ((arity ∈ₘ ωₘ) ∧ₘ
          (function_interpretation_key_term arity symbol ∈ₘ symbols)) ∧ₘ
          (related_term_list_code_atₘ(symbols, depth, arity, arguments) ∧ₘ
            (code ≐ₘ app_codeₘ(arity, symbol, arguments))) := by
    simp [body, Formula.substitute, Formula.substituteMapped,
      Substitution.free_map, VariableSubstitution.cons, Term.substituteMapped,
      Arguments.substituteMapped, Term.weakenFree,
      Term.rename, Renaming.weakenFree, Renaming.free, hClosed, hBound, τ,
      function_interpretation_key_term, godel_pairing_term,
      term_weaken_free_three]
  rw [hBody]
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro hArity hKey)
    (FirstOrder.Derives.conj_intro hArguments hCode)

private theorem related_term_code_at_code_mem_of_derives
    (symbols depth code : SetOpenTerm [])
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(symbols, depth, code)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ∈ₘ ωₘ := by
  have hCondition := FirstOrder.Derives.iff_elim_left
    (FirstOrder.Derives.theory_weaken
      semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
      (related_term_code_at_definition_instance_derives
        (Γ := ([] : Context signature [])) symbols depth code)) hCode
  exact FirstOrder.Derives.conj_elim_right
    (FirstOrder.Derives.conj_elim_left hCondition)

private theorem related_term_list_code_at_code_mem_of_derives
    (symbols depth length code : SetOpenTerm [])
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_list_code_atₘ(symbols, depth, length, code)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ∈ₘ ωₘ := by
  have hCondition := FirstOrder.Derives.iff_elim_left
    (FirstOrder.Derives.theory_weaken
      semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
      (related_term_list_code_at_definition_instance_derives
        (Γ := ([] : Context signature [])) symbols depth length code)) hCode
  exact FirstOrder.Derives.conj_elim_right
    (FirstOrder.Derives.conj_elim_left hCondition)

private theorem related_formula_code_at_code_mem_of_derives
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

theorem related_quote_term_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(
        NonlogicalSymₘ,
        numₘ(bound.length),
        (quote_term term : SetOpenTerm [])) := by
  refine Term.rec
    (motive_1 := fun _ term =>
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_term_code_atₘ(
          NonlogicalSymₘ,
          numₘ(bound.length),
          (quote_term term : SetOpenTerm [])))
    (motive_2 := fun sorts arguments =>
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_term_list_code_atₘ(
          NonlogicalSymₘ,
          numₘ(bound.length),
          numₘ(sorts.length),
          (quote_arguments arguments : SetOpenTerm [])))
    (fun {sort} entry => by
      have hDepth := omega_mem_carrier
        (Γ := ([] : Context signature [])) bound.length
      have hCodeFormal := structural_node_code_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.boundVariable
        [numₘ(entry.index)] (by
          intro field hField
          simp only [List.mem_cons, List.not_mem_nil] at hField
          rcases hField with hField | hField
          · simpa [hField] using
              (finite_numeral_mem_formal_language_encoding_theory
                (Γ := ([] : Context signature [])) entry.index)
          · contradiction)
      have hCode := formal_to_carrier hCodeFormal
      have hIndex := formal_to_carrier
        (finite_numeral_mem_of_lt_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) entry.index_lt_length)
      have hBranch := related_term_code_bound_condition_intro
        (numₘ(bound.length))
        (numₘ(entry.index))
        (bound_var_codeₘ(numₘ(entry.index)) : SetOpenTerm [])
        hIndex
        (Metatheory.Derives.equality_refl
          (bound_var_codeₘ(numₘ(entry.index)) : SetOpenTerm []))
      have hResult := related_term_code_at_of_condition
        NonlogicalSymₘ
        (numₘ(bound.length))
        (bound_var_codeₘ(numₘ(entry.index)) : SetOpenTerm [])
        hDepth hCode
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_left hBranch))
      simpa [quote_term] using hResult)
    (fun {sort} entry => by
      have hDepth := omega_mem_carrier
        (Γ := ([] : Context signature [])) bound.length
      have hCodeFormal := structural_node_code_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.freeVariable
        [numₘ(entry.index)] (by
          intro field hField
          simp only [List.mem_cons, List.not_mem_nil] at hField
          rcases hField with hField | hField
          · simpa [hField] using
              (finite_numeral_mem_formal_language_encoding_theory
                (Γ := ([] : Context signature [])) entry.index)
          · contradiction)
      have hCode := formal_to_carrier hCodeFormal
      have hBranch := related_term_code_free_condition_intro
        (numₘ(entry.index))
        (free_var_codeₘ(numₘ(entry.index)) : SetOpenTerm [])
        (omega_mem_carrier entry.index)
        (Metatheory.Derives.equality_refl
          (free_var_codeₘ(numₘ(entry.index)) : SetOpenTerm []))
      have hResult := related_term_code_at_of_condition
        NonlogicalSymₘ
        (numₘ(bound.length))
        (free_var_codeₘ(numₘ(entry.index)) : SetOpenTerm [])
        (omega_mem_carrier bound.length) hCode
        (FirstOrder.Derives.disj_intro_left hBranch)
      simpa [quote_term] using hResult)
    (fun function arguments ih => by
      cases hDomain : σ.funcDomain function with
      | nil =>
          have hCodeFormal := structural_node_code_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature [])) StructuralCodeTag.constant
            [numₘ(QuotationNumbering.function_number function)] (by
              intro field hField
              simp only [List.mem_cons, List.not_mem_nil] at hField
              rcases hField with hField | hField
              · simpa [hField] using
                  (finite_numeral_mem_formal_language_encoding_theory
                    (Γ := ([] : Context signature []))
                    (QuotationNumbering.function_number function))
              · contradiction)
          have hCode := formal_to_carrier hCodeFormal
          have hKeyOmega := godel_pair_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature []))
            (numₘ(0) : SetOpenTerm [])
            (numₘ(QuotationNumbering.function_number function) : SetOpenTerm [])
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature [])) 0)
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature []))
              (QuotationNumbering.function_number function))
          have hKey := nonlogical_symbol_mem_of_omega
            (godel_pairₘ(
              numₘ(0),
              numₘ(QuotationNumbering.function_number function)) : SetOpenTerm [])
            hKeyOmega
          have hBranch := related_term_code_constant_condition_intro
            NonlogicalSymₘ
            (numₘ(QuotationNumbering.function_number function))
            (const_codeₘ(numₘ(QuotationNumbering.function_number function)) :
              SetOpenTerm [])
            hKey
            (Metatheory.Derives.equality_refl
              (const_codeₘ(numₘ(QuotationNumbering.function_number function)) :
                SetOpenTerm []))
          have hResult := related_term_code_at_of_condition
            NonlogicalSymₘ
            (numₘ(bound.length))
            (const_codeₘ(numₘ(QuotationNumbering.function_number function)) :
              SetOpenTerm [])
            (omega_mem_carrier bound.length) hCode
            (FirstOrder.Derives.disj_intro_right
              (FirstOrder.Derives.disj_intro_right
                (FirstOrder.Derives.disj_intro_left hBranch)))
          simpa [quote_term, hDomain] using hResult
      | cons head tail =>
          have hArguments :
              ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
                related_term_list_code_atₘ(
                  NonlogicalSymₘ,
                  numₘ(bound.length),
                  numₘ(σ.funcArity function),
                  (quote_arguments arguments : SetOpenTerm [])) := by
            simpa [Signature.funcArity, hDomain] using ih
          have hArgumentsDirect :
              ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
                term_list_code_atₘ(
                  numₘ(bound.length),
                  numₘ(σ.funcArity function),
                  (quote_arguments arguments : SetOpenTerm [])) := by
            simpa [Signature.funcArity, hDomain] using
              (quote_arguments_term_list_code_at
                (σ := σ) (bound := bound) (free := free) arguments)
          have hArgumentsCode := term_list_code_at_code_mem_of_derives
            (numₘ(bound.length))
            (numₘ(σ.funcArity function))
            (quote_arguments arguments : SetOpenTerm [])
            hArgumentsDirect
          have hKeyInner := godel_pair_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature []))
            (numₘ(σ.funcArity function) : SetOpenTerm [])
            (numₘ(QuotationNumbering.function_number function) : SetOpenTerm [])
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature [])) (σ.funcArity function))
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature []))
              (QuotationNumbering.function_number function))
          have hKeyOmega := godel_pair_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature []))
            (numₘ(1) : SetOpenTerm [])
            (godel_pairₘ(
              numₘ(σ.funcArity function),
              numₘ(QuotationNumbering.function_number function)))
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature [])) 1)
            hKeyInner
          have hKey := nonlogical_symbol_mem_of_omega
            (function_interpretation_key_term
              (numₘ(σ.funcArity function))
              (numₘ(QuotationNumbering.function_number function)))
            (by simpa [function_interpretation_key_term] using hKeyOmega)
          have hCodeFormal := structural_node_code_mem_formal_language_encoding_theory
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
                    · contradiction)
          have hCode := formal_to_carrier hCodeFormal
          have hBranch := related_term_code_application_condition_intro
            NonlogicalSymₘ
            (numₘ(bound.length))
            (app_codeₘ(
              numₘ(σ.funcArity function),
              numₘ(QuotationNumbering.function_number function),
              (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm [])
            (numₘ(σ.funcArity function))
            (numₘ(QuotationNumbering.function_number function))
            (quote_arguments arguments : SetOpenTerm [])
            (omega_mem_carrier (σ.funcArity function))
            hKey hArguments
            (Metatheory.Derives.equality_refl
              (app_codeₘ(
                numₘ(σ.funcArity function),
                numₘ(QuotationNumbering.function_number function),
                (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm []))
          have hResult := related_term_code_at_of_condition
            NonlogicalSymₘ
            (numₘ(bound.length))
            (app_codeₘ(
              numₘ(σ.funcArity function),
              numₘ(QuotationNumbering.function_number function),
              (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm [])
            (omega_mem_carrier bound.length) hCode
              (FirstOrder.Derives.disj_intro_right
                (FirstOrder.Derives.disj_intro_right
                  (FirstOrder.Derives.disj_intro_right hBranch)))
          simpa [quote_term, hDomain] using hResult)
    (by
      have hDepth := omega_mem_carrier
        (Γ := ([] : Context signature [])) bound.length
      have hLength := omega_mem_carrier
        (Γ := ([] : Context signature [])) 0
      have hCodeFormal := structural_raw_node_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.listNil ∅ₘ
        (finite_numeral_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) 0)
      have hCode := formal_to_carrier hCodeFormal
      have hBranch :
          ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
            ((numₘ(0) ≐ₘ numₘ(0)) ∧ₘ
              (code_nilₘ ≐ₘ code_nilₘ)) ∨ₘ
              related_term_list_code_cons_condition
                NonlogicalSymₘ (numₘ(bound.length)) (numₘ(0))
                (code_nilₘ : SetOpenTerm []) := by
        apply FirstOrder.Derives.disj_intro_left
        exact FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (T := intrinsic_syntax_carrier_theory)
            (Γ := ([] : Context signature []))
            (numₘ(0) : SetOpenTerm []))
          (Metatheory.Derives.equality_refl
            (T := intrinsic_syntax_carrier_theory)
            (Γ := ([] : Context signature []))
            (code_nilₘ : SetOpenTerm []))
      have hResult := related_term_list_code_at_of_condition
        NonlogicalSymₘ
        (numₘ(bound.length))
        (numₘ(0))
        (code_nilₘ : SetOpenTerm [])
        hDepth hLength hCode hBranch
      simpa [quote_arguments] using hResult)
    (fun {sort} {sorts} head tail ihHead ihTail => by
      have hDepth := omega_mem_carrier
        (Γ := ([] : Context signature [])) bound.length
      have hPreviousLength := omega_mem_carrier
        (Γ := ([] : Context signature [])) sorts.length
      have hLengthMem := omega_mem_carrier
        (Γ := ([] : Context signature [])) (sort :: sorts).length
      have hLength :
          ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
            numₘ((sort :: sorts).length) ≐ₘ Sₘ(numₘ(sorts.length)) := by
        simpa [finite_numeral_term] using
          (Metatheory.Derives.equality_refl
            (Sₘ(numₘ(sorts.length)) : SetOpenTerm []))
      have hHeadDirect := quote_term_code_at
        (σ := σ) (bound := bound) (free := free) head
      have hHeadCodeFormal := term_code_at_code_mem_of_derives
        (numₘ(bound.length))
        (quote_term head : SetOpenTerm [])
        hHeadDirect
      have hTailDirect := quote_arguments_term_list_code_at
        (σ := σ) (bound := bound) (free := free) tail
      have hTailCodeFormal := term_list_code_at_code_mem_of_derives
        (numₘ(bound.length))
        (numₘ(sorts.length))
        (quote_arguments tail : SetOpenTerm [])
        hTailDirect
      have hCodeFormal := structural_raw_node_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.listCons
        (godel_pairₘ(
          (quote_term head : SetOpenTerm []),
          (quote_arguments tail : SetOpenTerm [])))
        (godel_pair_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature []))
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          hHeadCodeFormal hTailCodeFormal)
      have hCode := formal_to_carrier hCodeFormal
      have hBranch := related_term_list_code_cons_condition_intro
        NonlogicalSymₘ
        (numₘ(bound.length))
        (numₘ((sort :: sorts).length))
        (code_consₘ(
          (quote_term head : SetOpenTerm []),
          (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm [])
        (numₘ(sorts.length))
        (quote_term head : SetOpenTerm [])
        (quote_arguments tail : SetOpenTerm [])
        hPreviousLength hLength ihHead ihTail
        (Metatheory.Derives.equality_refl
          (code_consₘ(
            (quote_term head : SetOpenTerm []),
            (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm []))
      have hResult := related_term_list_code_at_of_condition
        NonlogicalSymₘ
        (numₘ(bound.length))
        (numₘ((sort :: sorts).length))
        (code_consₘ(
          (quote_term head : SetOpenTerm []),
          (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm [])
        hDepth hLengthMem hCode
        (FirstOrder.Derives.disj_intro_right hBranch)
      simpa [quote_arguments] using hResult)
    term

theorem related_quote_term_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) (depth : Nat)
    (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(
        NonlogicalSymₘ,
        numₘ(depth),
        (quote_term term : SetOpenTerm [])) := by
  exact (Term.rec
    (motive_1 := fun _ term =>
      ∀ depth, bound.length ≤ depth →
        ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
          related_term_code_atₘ(
            NonlogicalSymₘ,
            numₘ(depth),
            (quote_term term : SetOpenTerm [])))
    (motive_2 := fun sorts arguments =>
      ∀ depth, bound.length ≤ depth →
        ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
          related_term_list_code_atₘ(
            NonlogicalSymₘ,
            numₘ(depth),
            numₘ(sorts.length),
            (quote_arguments arguments : SetOpenTerm [])))
    (fun {sort} entry => by
      intro depth hBound
      have hDepth := omega_mem_carrier
        (Γ := ([] : Context signature [])) depth
      have hCodeFormal := structural_node_code_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.boundVariable
        [numₘ(entry.index)] (by
          intro field hField
          simp only [List.mem_cons, List.not_mem_nil] at hField
          rcases hField with hField | hField
          · simpa [hField] using
              (finite_numeral_mem_formal_language_encoding_theory
                (Γ := ([] : Context signature [])) entry.index)
          · contradiction)
      have hCode := formal_to_carrier hCodeFormal
      have hIndex := formal_to_carrier
        (finite_numeral_mem_of_lt_formal_language_encoding_theory
          (Γ := ([] : Context signature []))
          (Nat.lt_of_lt_of_le entry.index_lt_length hBound))
      have hBranch := related_term_code_bound_condition_intro
        (numₘ(depth))
        (numₘ(entry.index))
        (bound_var_codeₘ(numₘ(entry.index)) : SetOpenTerm [])
        hIndex
        (Metatheory.Derives.equality_refl
          (bound_var_codeₘ(numₘ(entry.index)) : SetOpenTerm []))
      have hResult := related_term_code_at_of_condition
        NonlogicalSymₘ
        (numₘ(depth))
        (bound_var_codeₘ(numₘ(entry.index)) : SetOpenTerm [])
        hDepth hCode
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_left hBranch))
      simpa [quote_term] using hResult)
    (fun {sort} entry => by
      intro depth hBound
      have hDepth := omega_mem_carrier
        (Γ := ([] : Context signature [])) depth
      have hCodeFormal := structural_node_code_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.freeVariable
        [numₘ(entry.index)] (by
          intro field hField
          simp only [List.mem_cons, List.not_mem_nil] at hField
          rcases hField with hField | hField
          · simpa [hField] using
              (finite_numeral_mem_formal_language_encoding_theory
                (Γ := ([] : Context signature [])) entry.index)
          · contradiction)
      have hCode := formal_to_carrier hCodeFormal
      have hBranch := related_term_code_free_condition_intro
        (numₘ(entry.index))
        (free_var_codeₘ(numₘ(entry.index)) : SetOpenTerm [])
        (omega_mem_carrier entry.index)
        (Metatheory.Derives.equality_refl
          (free_var_codeₘ(numₘ(entry.index)) : SetOpenTerm []))
      have hResult := related_term_code_at_of_condition
        NonlogicalSymₘ
        (numₘ(depth))
        (free_var_codeₘ(numₘ(entry.index)) : SetOpenTerm [])
        (omega_mem_carrier depth) hCode
        (FirstOrder.Derives.disj_intro_left hBranch)
      simpa [quote_term] using hResult)
    (fun function arguments ih => by
      intro depth hBound
      cases hDomain : σ.funcDomain function with
      | nil =>
          have hCodeFormal := structural_node_code_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature [])) StructuralCodeTag.constant
            [numₘ(QuotationNumbering.function_number function)] (by
              intro field hField
              simp only [List.mem_cons, List.not_mem_nil] at hField
              rcases hField with hField | hField
              · simpa [hField] using
                  (finite_numeral_mem_formal_language_encoding_theory
                    (Γ := ([] : Context signature []))
                    (QuotationNumbering.function_number function))
              · contradiction)
          have hCode := formal_to_carrier hCodeFormal
          have hKeyOmega := godel_pair_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature []))
            (numₘ(0) : SetOpenTerm [])
            (numₘ(QuotationNumbering.function_number function) : SetOpenTerm [])
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature [])) 0)
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature []))
              (QuotationNumbering.function_number function))
          have hKey := nonlogical_symbol_mem_of_omega
            (godel_pairₘ(
              numₘ(0),
              numₘ(QuotationNumbering.function_number function)) : SetOpenTerm [])
            hKeyOmega
          have hBranch := related_term_code_constant_condition_intro
            NonlogicalSymₘ
            (numₘ(QuotationNumbering.function_number function))
            (const_codeₘ(numₘ(QuotationNumbering.function_number function)) :
              SetOpenTerm [])
            hKey
            (Metatheory.Derives.equality_refl
              (const_codeₘ(numₘ(QuotationNumbering.function_number function)) :
                SetOpenTerm []))
          have hResult := related_term_code_at_of_condition
            NonlogicalSymₘ
            (numₘ(depth))
            (const_codeₘ(numₘ(QuotationNumbering.function_number function)) :
              SetOpenTerm [])
            (omega_mem_carrier depth) hCode
            (FirstOrder.Derives.disj_intro_right
              (FirstOrder.Derives.disj_intro_right
                (FirstOrder.Derives.disj_intro_left hBranch)))
          simpa [quote_term, hDomain] using hResult
      | cons head tail =>
          have hArguments :
              ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
                related_term_list_code_atₘ(
                  NonlogicalSymₘ,
                  numₘ(depth),
                  numₘ(σ.funcArity function),
                  (quote_arguments arguments : SetOpenTerm [])) := by
            simpa [Signature.funcArity, hDomain] using ih depth hBound
          have hArgumentsDirect :
              ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
                term_list_code_atₘ(
                  numₘ(depth),
                  numₘ(σ.funcArity function),
                  (quote_arguments arguments : SetOpenTerm [])) := by
            simpa [Signature.funcArity, hDomain] using
              (quote_arguments_term_list_code_at_of_depth
                (σ := σ) (bound := bound) (free := free) arguments depth hBound)
          have hArgumentsCode := term_list_code_at_code_mem_of_derives
            (numₘ(depth))
            (numₘ(σ.funcArity function))
            (quote_arguments arguments : SetOpenTerm [])
            hArgumentsDirect
          have hKeyInner := godel_pair_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature []))
            (numₘ(σ.funcArity function) : SetOpenTerm [])
            (numₘ(QuotationNumbering.function_number function) : SetOpenTerm [])
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature [])) (σ.funcArity function))
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature []))
              (QuotationNumbering.function_number function))
          have hKeyOmega := godel_pair_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature []))
            (numₘ(1) : SetOpenTerm [])
            (godel_pairₘ(
              numₘ(σ.funcArity function),
              numₘ(QuotationNumbering.function_number function)))
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature [])) 1)
            hKeyInner
          have hKey := nonlogical_symbol_mem_of_omega
            (function_interpretation_key_term
              (numₘ(σ.funcArity function))
              (numₘ(QuotationNumbering.function_number function)))
            (by simpa [function_interpretation_key_term] using hKeyOmega)
          have hCodeFormal := structural_node_code_mem_formal_language_encoding_theory
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
                    · contradiction)
          have hCode := formal_to_carrier hCodeFormal
          have hBranch := related_term_code_application_condition_intro
            NonlogicalSymₘ
            (numₘ(depth))
            (app_codeₘ(
              numₘ(σ.funcArity function),
              numₘ(QuotationNumbering.function_number function),
              (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm [])
            (numₘ(σ.funcArity function))
            (numₘ(QuotationNumbering.function_number function))
            (quote_arguments arguments : SetOpenTerm [])
            (omega_mem_carrier (σ.funcArity function))
            hKey hArguments
            (Metatheory.Derives.equality_refl
              (app_codeₘ(
                numₘ(σ.funcArity function),
                numₘ(QuotationNumbering.function_number function),
                (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm []))
          have hResult := related_term_code_at_of_condition
            NonlogicalSymₘ
            (numₘ(depth))
            (app_codeₘ(
              numₘ(σ.funcArity function),
              numₘ(QuotationNumbering.function_number function),
              (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm [])
            (omega_mem_carrier depth) hCode
              (FirstOrder.Derives.disj_intro_right
                (FirstOrder.Derives.disj_intro_right
                  (FirstOrder.Derives.disj_intro_right hBranch)))
          simpa [quote_term, hDomain] using hResult)
    (by
      intro depth hBound
      have hDepth := omega_mem_carrier
        (Γ := ([] : Context signature [])) depth
      have hLength := omega_mem_carrier
        (Γ := ([] : Context signature [])) 0
      have hCodeFormal := structural_raw_node_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.listNil ∅ₘ
        (finite_numeral_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) 0)
      have hCode := formal_to_carrier hCodeFormal
      have hBranch :
          ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
            ((numₘ(0) ≐ₘ numₘ(0)) ∧ₘ
              (code_nilₘ ≐ₘ code_nilₘ)) ∨ₘ
              related_term_list_code_cons_condition
                NonlogicalSymₘ (numₘ(depth)) (numₘ(0))
                (code_nilₘ : SetOpenTerm []) := by
        apply FirstOrder.Derives.disj_intro_left
        exact FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (T := intrinsic_syntax_carrier_theory)
            (Γ := ([] : Context signature []))
            (numₘ(0) : SetOpenTerm []))
          (Metatheory.Derives.equality_refl
            (T := intrinsic_syntax_carrier_theory)
            (Γ := ([] : Context signature []))
            (code_nilₘ : SetOpenTerm []))
      have hResult := related_term_list_code_at_of_condition
        NonlogicalSymₘ
        (numₘ(depth))
        (numₘ(0))
        (code_nilₘ : SetOpenTerm [])
        hDepth hLength hCode hBranch
      simpa [quote_arguments] using hResult)
    (fun {sort} {sorts} head tail ihHead ihTail => by
      intro depth hBound
      have hDepth := omega_mem_carrier
        (Γ := ([] : Context signature [])) depth
      have hPreviousLength := omega_mem_carrier
        (Γ := ([] : Context signature [])) sorts.length
      have hLengthMem := omega_mem_carrier
        (Γ := ([] : Context signature [])) (sort :: sorts).length
      have hLength :
          ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
            numₘ((sort :: sorts).length) ≐ₘ Sₘ(numₘ(sorts.length)) := by
        simpa [finite_numeral_term] using
          (Metatheory.Derives.equality_refl
            (Sₘ(numₘ(sorts.length)) : SetOpenTerm []))
      have hHeadDirect := quote_term_code_at_of_depth
        (σ := σ) (bound := bound) (free := free) head depth hBound
      have hHeadCodeFormal := term_code_at_code_mem_of_derives
        (numₘ(depth))
        (quote_term head : SetOpenTerm [])
        hHeadDirect
      have hTailDirect := quote_arguments_term_list_code_at_of_depth
        (σ := σ) (bound := bound) (free := free) tail depth hBound
      have hTailCodeFormal := term_list_code_at_code_mem_of_derives
        (numₘ(depth))
        (numₘ(sorts.length))
        (quote_arguments tail : SetOpenTerm [])
        hTailDirect
      have hCodeFormal := structural_raw_node_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.listCons
        (godel_pairₘ(
          (quote_term head : SetOpenTerm []),
          (quote_arguments tail : SetOpenTerm [])))
        (godel_pair_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature []))
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          hHeadCodeFormal hTailCodeFormal)
      have hCode := formal_to_carrier hCodeFormal
      have hBranch := related_term_list_code_cons_condition_intro
        NonlogicalSymₘ
        (numₘ(depth))
        (numₘ((sort :: sorts).length))
        (code_consₘ(
          (quote_term head : SetOpenTerm []),
          (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm [])
        (numₘ(sorts.length))
        (quote_term head : SetOpenTerm [])
        (quote_arguments tail : SetOpenTerm [])
        hPreviousLength hLength (ihHead depth hBound) (ihTail depth hBound)
        (Metatheory.Derives.equality_refl
          (code_consₘ(
            (quote_term head : SetOpenTerm []),
            (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm []))
      have hResult := related_term_list_code_at_of_condition
        NonlogicalSymₘ
        (numₘ(depth))
        (numₘ((sort :: sorts).length))
        (code_consₘ(
          (quote_term head : SetOpenTerm []),
          (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm [])
        hDepth hLengthMem hCode
        (FirstOrder.Derives.disj_intro_right hBranch)
      simpa [quote_arguments] using hResult)
    term) depth hBound

theorem related_quote_arguments_term_list_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) (depth : Nat)
    (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_list_code_atₘ(
        NonlogicalSymₘ,
        numₘ(depth),
        numₘ(sorts.length),
        (quote_arguments arguments : SetOpenTerm [])) := by
  exact (Arguments.rec (σ := σ) (bound := bound) (free := free)
    (motive_1 := fun (currentSort : σ.SortSymbol)
        (currentTerm : Term σ bound free currentSort) =>
      ∀ depth, bound.length ≤ depth →
        ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
          related_term_code_atₘ(
            NonlogicalSymₘ,
            numₘ(depth),
            (quote_term currentTerm : SetOpenTerm [])))
    (motive_2 := fun (currentSorts : List σ.SortSymbol)
        (currentArguments : Arguments σ bound free currentSorts) =>
      ∀ depth, bound.length ≤ depth →
        ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
          related_term_list_code_atₘ(
            NonlogicalSymₘ,
            numₘ(depth),
            numₘ(currentSorts.length),
            (quote_arguments currentArguments : SetOpenTerm [])))
    (fun {sort} entry => by
      intro depth hBound
      exact related_quote_term_code_at_of_depth (.bvar entry) depth hBound)
    (fun {sort} entry => by
      intro depth hBound
      exact related_quote_term_code_at_of_depth (.fvar entry) depth hBound)
    (fun function arguments _ih => by
      intro depth hBound
      exact related_quote_term_code_at_of_depth
        (σ := σ) (bound := bound) (free := free)
        (.app function arguments) depth hBound)
    (by
      intro depth hBound
      have hDepth := omega_mem_carrier
        (Γ := ([] : Context signature [])) depth
      have hLength := omega_mem_carrier
        (Γ := ([] : Context signature [])) 0
      have hCodeFormal := structural_raw_node_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.listNil ∅ₘ
        (finite_numeral_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) 0)
      have hCode := formal_to_carrier hCodeFormal
      have hBranch :
          ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
            ((numₘ(0) ≐ₘ numₘ(0)) ∧ₘ
              (code_nilₘ ≐ₘ code_nilₘ)) ∨ₘ
              related_term_list_code_cons_condition
                NonlogicalSymₘ (numₘ(depth)) (numₘ(0))
                (code_nilₘ : SetOpenTerm []) := by
        apply FirstOrder.Derives.disj_intro_left
        exact FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (T := intrinsic_syntax_carrier_theory)
            (Γ := ([] : Context signature []))
            (numₘ(0) : SetOpenTerm []))
          (Metatheory.Derives.equality_refl
            (T := intrinsic_syntax_carrier_theory)
            (Γ := ([] : Context signature []))
            (code_nilₘ : SetOpenTerm []))
      have hResult := related_term_list_code_at_of_condition
        NonlogicalSymₘ
        (numₘ(depth))
        (numₘ(0))
        (code_nilₘ : SetOpenTerm [])
        hDepth hLength hCode hBranch
      simpa [quote_arguments] using hResult)
    (fun {sort} {sorts} head tail ihHead ihTail => by
      intro depth hBound
      have hDepth := omega_mem_carrier
        (Γ := ([] : Context signature [])) depth
      have hPreviousLength := omega_mem_carrier
        (Γ := ([] : Context signature [])) sorts.length
      have hLengthMem := omega_mem_carrier
        (Γ := ([] : Context signature [])) (sort :: sorts).length
      have hLength :
          ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
            numₘ((sort :: sorts).length) ≐ₘ Sₘ(numₘ(sorts.length)) := by
        simpa [finite_numeral_term] using
          (Metatheory.Derives.equality_refl
            (T := intrinsic_syntax_carrier_theory)
            (Γ := ([] : Context signature []))
            (Sₘ(numₘ(sorts.length)) : SetOpenTerm []))
      have hHead := ihHead depth hBound
      have hTail := ihTail depth hBound
      have hHeadDirect := quote_term_code_at_of_depth
        (σ := σ) (bound := bound) (free := free) head depth hBound
      have hHeadCode := term_code_at_code_mem_of_derives
        (numₘ(depth))
        (quote_term head : SetOpenTerm [])
        hHeadDirect
      have hTailDirect := quote_arguments_term_list_code_at_of_depth
        (σ := σ) (bound := bound) (free := free) tail depth hBound
      have hTailCode := term_list_code_at_code_mem_of_derives
        (numₘ(depth))
        (numₘ(sorts.length))
        (quote_arguments tail : SetOpenTerm [])
        hTailDirect
      have hCodeFormal := structural_raw_node_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.listCons
        (godel_pairₘ(
          (quote_term head : SetOpenTerm []),
          (quote_arguments tail : SetOpenTerm [])))
        (godel_pair_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature []))
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          hHeadCode hTailCode)
      have hCode := formal_to_carrier hCodeFormal
      have hBranch := related_term_list_code_cons_condition_intro
        NonlogicalSymₘ
        (numₘ(depth))
        (numₘ((sort :: sorts).length))
        (code_consₘ(
          (quote_term head : SetOpenTerm []),
          (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm [])
        (numₘ(sorts.length))
        (quote_term head : SetOpenTerm [])
        (quote_arguments tail : SetOpenTerm [])
        hPreviousLength hLength hHead hTail
        (Metatheory.Derives.equality_refl
          (T := intrinsic_syntax_carrier_theory)
          (Γ := ([] : Context signature []))
          (code_consₘ(
            (quote_term head : SetOpenTerm []),
            (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm []))
      have hResult := related_term_list_code_at_of_condition
        NonlogicalSymₘ
        (numₘ(depth))
        (numₘ((sort :: sorts).length))
        (code_consₘ(
          (quote_term head : SetOpenTerm []),
          (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm [])
        hDepth hLengthMem hCode
        (FirstOrder.Derives.disj_intro_right hBranch)
      simpa [quote_arguments] using hResult)
    arguments) depth hBound

theorem related_quote_arguments_term_list_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_list_code_atₘ(
        NonlogicalSymₘ,
        numₘ(bound.length),
        numₘ(sorts.length),
        (quote_arguments arguments : SetOpenTerm [])) := by
  refine Arguments.rec (σ := σ) (bound := bound) (free := free)
    (motive_1 := fun sort term =>
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_term_code_atₘ(
          NonlogicalSymₘ,
          numₘ(bound.length),
          (quote_term term : SetOpenTerm [])))
    (motive_2 := fun sorts arguments =>
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_term_list_code_atₘ(
          NonlogicalSymₘ,
          numₘ(bound.length),
          numₘ(sorts.length),
          (quote_arguments arguments : SetOpenTerm [])))
    (fun {sort} entry => related_quote_term_code_at (.bvar entry))
    (fun {sort} entry => related_quote_term_code_at (.fvar entry))
    (fun function arguments _ih =>
      related_quote_term_code_at
        (σ := σ) (bound := bound) (free := free)
        (.app function arguments))
    (by
      have hDepth := omega_mem_carrier
        (Γ := ([] : Context signature [])) bound.length
      have hLength := omega_mem_carrier
        (Γ := ([] : Context signature [])) 0
      have hCodeFormal := structural_raw_node_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.listNil ∅ₘ
        (finite_numeral_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) 0)
      have hCode := formal_to_carrier hCodeFormal
      have hBranch :
          ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
            ((numₘ(0) ≐ₘ numₘ(0)) ∧ₘ
              (code_nilₘ ≐ₘ code_nilₘ)) ∨ₘ
              related_term_list_code_cons_condition
                NonlogicalSymₘ (numₘ(bound.length)) (numₘ(0))
                (code_nilₘ : SetOpenTerm []) := by
        apply FirstOrder.Derives.disj_intro_left
        exact FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (T := intrinsic_syntax_carrier_theory)
            (Γ := ([] : Context signature []))
            (numₘ(0) : SetOpenTerm []))
          (Metatheory.Derives.equality_refl
            (T := intrinsic_syntax_carrier_theory)
            (Γ := ([] : Context signature []))
            (code_nilₘ : SetOpenTerm []))
      have hResult := related_term_list_code_at_of_condition
        NonlogicalSymₘ
        (numₘ(bound.length))
        (numₘ(0))
        (code_nilₘ : SetOpenTerm [])
        hDepth hLength hCode hBranch
      simpa [quote_arguments] using hResult)
    (fun {sort} {sorts} head tail ihHead ihTail => by
      have hDepth := omega_mem_carrier
        (Γ := ([] : Context signature [])) bound.length
      have hPreviousLength := omega_mem_carrier
        (Γ := ([] : Context signature [])) sorts.length
      have hLengthMem := omega_mem_carrier
        (Γ := ([] : Context signature [])) (sort :: sorts).length
      have hLength :
          ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
            numₘ((sort :: sorts).length) ≐ₘ Sₘ(numₘ(sorts.length)) := by
        simpa [finite_numeral_term] using
          (Metatheory.Derives.equality_refl
            (T := intrinsic_syntax_carrier_theory)
            (Γ := ([] : Context signature []))
            (Sₘ(numₘ(sorts.length)) : SetOpenTerm []))
      have hHeadDirect := quote_term_code_at
        (σ := σ) (bound := bound) (free := free) head
      have hHeadCodeFormal := term_code_at_code_mem_of_derives
        (numₘ(bound.length))
        (quote_term head : SetOpenTerm [])
        hHeadDirect
      have hTailDirect := quote_arguments_term_list_code_at
        (σ := σ) (bound := bound) (free := free) tail
      have hTailCodeFormal := term_list_code_at_code_mem_of_derives
        (numₘ(bound.length))
        (numₘ(sorts.length))
        (quote_arguments tail : SetOpenTerm [])
        hTailDirect
      have hCodeFormal := structural_raw_node_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.listCons
        (godel_pairₘ(
          (quote_term head : SetOpenTerm []),
          (quote_arguments tail : SetOpenTerm [])))
        (godel_pair_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature []))
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          hHeadCodeFormal hTailCodeFormal)
      have hCode := formal_to_carrier hCodeFormal
      have hBranch := related_term_list_code_cons_condition_intro
        NonlogicalSymₘ
        (numₘ(bound.length))
        (numₘ((sort :: sorts).length))
        (code_consₘ(
          (quote_term head : SetOpenTerm []),
          (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm [])
        (numₘ(sorts.length))
        (quote_term head : SetOpenTerm [])
        (quote_arguments tail : SetOpenTerm [])
        hPreviousLength hLength ihHead ihTail
        (Metatheory.Derives.equality_refl
          (T := intrinsic_syntax_carrier_theory)
          (Γ := ([] : Context signature []))
          (code_consₘ(
            (quote_term head : SetOpenTerm []),
            (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm []))
      have hResult := related_term_list_code_at_of_condition
        NonlogicalSymₘ
        (numₘ(bound.length))
        (numₘ((sort :: sorts).length))
        (code_consₘ(
          (quote_term head : SetOpenTerm []),
          (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm [])
        hDepth hLengthMem hCode
        (FirstOrder.Derives.disj_intro_right hBranch)
      simpa [quote_arguments] using hResult)
    arguments

private theorem gq_closed_one_weaken_substitute
    (τ : VariableSubstitution signature [SetSort.set] [] [])
    (term : SetOpenTerm []) :
    Term.substituteMapped VariableSubstitution.boundId τ
        (term.weakenFree SetSort.set) =
      term := by
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

theorem related_formula_negation_condition_intro
    (symbols depth code body : SetOpenTerm [])
    (hBody : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(symbols, depth, body))
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ neg_codeₘ(body)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_negation_condition symbols depth code := by
  unfold related_formula_negation_condition
  apply FirstOrder.Derives.exists_intro body
  rw [Formula.instantiateTop_abstractFreeTop]
  let τ : VariableSubstitution signature [SetSort.set] [] [] :=
    VariableSubstitution.instantiateFreeTop body
  have hSymbolsClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (symbols.weakenFree SetSort.set) = symbols :=
    gq_closed_one_weaken_substitute τ symbols
  have hDepthClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (depth.weakenFree SetSort.set) = depth :=
    gq_closed_one_weaken_substitute τ depth
  have hCodeClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (code.weakenFree SetSort.set) = code :=
    gq_closed_one_weaken_substitute τ code
  have hNegClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (neg_codeₘ(.fvar .here) : SetOpenTerm [SetSort.set]) =
        neg_codeₘ(body) := by
    simp only [Term.substituteMapped, Arguments.substituteMapped, τ]
    rfl
  simp only [Formula.instantiateFreeTop]
  let bodyFormula : SetOpenFormula [SetSort.set] :=
    related_formula_code_atₘ(
        symbols.weakenFree SetSort.set,
        depth.weakenFree SetSort.set, .fvar .here) ∧ₘ
      ((code.weakenFree SetSort.set) ≐ₘ neg_codeₘ(.fvar .here))
  change ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
    Formula.substitute (Substitution.free_map τ) bodyFormula
  have hFormula :
      Formula.substitute (Substitution.free_map τ) bodyFormula =
        related_formula_code_atₘ(symbols, depth, body) ∧ₘ
          (code ≐ₘ neg_codeₘ(body)) := by
    change
      (related_formula_code_atₘ(
          Term.substituteMapped VariableSubstitution.boundId τ
            (symbols.weakenFree SetSort.set),
          Term.substituteMapped VariableSubstitution.boundId τ
            (depth.weakenFree SetSort.set),
          Term.substituteMapped VariableSubstitution.boundId τ
            (.fvar .here)) ∧ₘ
        (Term.substituteMapped VariableSubstitution.boundId τ
            (code.weakenFree SetSort.set) ≐ₘ
          Term.substituteMapped VariableSubstitution.boundId τ
            (neg_codeₘ(.fvar .here)))) =
        related_formula_code_atₘ(symbols, depth, body) ∧ₘ
          (code ≐ₘ neg_codeₘ(body))
    rw [hSymbolsClosed, hDepthClosed, hNegClosed, hCodeClosed]
    rfl
  rw [hFormula]
  exact FirstOrder.Derives.conj_intro hBody hCode

theorem related_formula_term_binary_condition_intro
    (symbols depth code : SetOpenTerm [])
    (tag : StructuralCodeTag)
    (left right : SetOpenTerm [])
    (hLeft : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(symbols, depth, left))
    (hRight : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(symbols, depth, right))
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ structural_node_code_term tag [left, right]) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_binary_condition symbols depth code tag := by
  unfold related_formula_binary_condition
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
  have hSymbolsClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          ((symbols.weakenFree SetSort.set).weakenFree SetSort.set) =
        symbols :=
    gq_closed_two_weaken_substitute τ symbols
  have hDepthClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          ((depth.weakenFree SetSort.set).weakenFree SetSort.set) =
        depth :=
    gq_closed_two_weaken_substitute τ depth
  have hCodeClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          ((code.weakenFree SetSort.set).weakenFree SetSort.set) =
        code :=
    gq_closed_two_weaken_substitute τ code
  have hTargetClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (structural_node_code_term tag
            [.fvar (.there .here), .fvar .here]) =
        structural_node_code_term tag [left, right] := by
    simp [structural_node_code_term, structural_list_code_term,
      structural_raw_node_code_term, godel_pairing_term,
      Term.substituteMapped, Arguments.substituteMapped, τ,
      VariableSubstitution.cons]
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    ((related_term_code_atₘ(
        (symbols.weakenFree SetSort.set).weakenFree SetSort.set,
        (depth.weakenFree SetSort.set).weakenFree SetSort.set,
        .fvar (.there .here)) ∧ₘ
      related_term_code_atₘ(
        (symbols.weakenFree SetSort.set).weakenFree SetSort.set,
        (depth.weakenFree SetSort.set).weakenFree SetSort.set,
        .fvar .here)) ∧ₘ
      (((code.weakenFree SetSort.set).weakenFree SetSort.set) ≐ₘ
        structural_node_code_term tag
          [.fvar (.there .here), .fvar .here]))
  change ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
    Formula.substitute (Substitution.free_map τ) body
  have hBody :
      Formula.substitute (Substitution.free_map τ) body =
        ((related_term_code_atₘ(symbols, depth, left) ∧ₘ
            related_term_code_atₘ(symbols, depth, right)) ∧ₘ
          (code ≐ₘ structural_node_code_term tag [left, right])) := by
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
            ((code.weakenFree SetSort.set).weakenFree SetSort.set) ≐ₘ
          Term.substituteMapped VariableSubstitution.boundId τ
            (structural_node_code_term tag
              [.fvar (.there .here), .fvar .here]))) =
      ((related_term_code_atₘ(symbols, depth, left) ∧ₘ
          related_term_code_atₘ(symbols, depth, right)) ∧ₘ
        (code ≐ₘ structural_node_code_term tag [left, right]))
    rw [hSymbolsClosed, hDepthClosed, hCodeClosed, hTargetClosed]
    rfl
  rw [hBody]
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro hLeft hRight) hCode

theorem related_formula_implication_condition_intro
    (symbols depth code left right : SetOpenTerm [])
    (hLeft : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(symbols, depth, left))
    (hRight : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(symbols, depth, right))
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ imp_codeₘ(left, right)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_implication_condition symbols depth code := by
  unfold related_formula_implication_condition
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
  have hSymbolsClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          ((symbols.weakenFree SetSort.set).weakenFree SetSort.set) =
        symbols :=
    gq_closed_two_weaken_substitute τ symbols
  have hDepthClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          ((depth.weakenFree SetSort.set).weakenFree SetSort.set) =
        depth :=
    gq_closed_two_weaken_substitute τ depth
  have hCodeClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          ((code.weakenFree SetSort.set).weakenFree SetSort.set) =
        code :=
    gq_closed_two_weaken_substitute τ code
  have hTargetClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (imp_codeₘ(.fvar (.there .here), .fvar .here) :
            SetOpenTerm [SetSort.set, SetSort.set]) =
        imp_codeₘ(left, right) := by
    simp [implication_formula_code_term, structural_node_code_term,
      structural_list_code_term, structural_raw_node_code_term,
      godel_pairing_term, Term.substituteMapped,
      Arguments.substituteMapped, τ, VariableSubstitution.cons]
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    ((related_formula_code_atₘ(
        (symbols.weakenFree SetSort.set).weakenFree SetSort.set,
        (depth.weakenFree SetSort.set).weakenFree SetSort.set,
        .fvar (.there .here)) ∧ₘ
      related_formula_code_atₘ(
        (symbols.weakenFree SetSort.set).weakenFree SetSort.set,
        (depth.weakenFree SetSort.set).weakenFree SetSort.set,
        .fvar .here)) ∧ₘ
      (((code.weakenFree SetSort.set).weakenFree SetSort.set) ≐ₘ
        imp_codeₘ(.fvar (.there .here), .fvar .here)))
  change ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
    Formula.substitute (Substitution.free_map τ) body
  have hBody :
      Formula.substitute (Substitution.free_map τ) body =
        ((related_formula_code_atₘ(symbols, depth, left) ∧ₘ
            related_formula_code_atₘ(symbols, depth, right)) ∧ₘ
          (code ≐ₘ imp_codeₘ(left, right))) := by
    change
      ((related_formula_code_atₘ(
          Term.substituteMapped VariableSubstitution.boundId τ
            ((symbols.weakenFree SetSort.set).weakenFree SetSort.set),
          Term.substituteMapped VariableSubstitution.boundId τ
            ((depth.weakenFree SetSort.set).weakenFree SetSort.set),
          Term.substituteMapped VariableSubstitution.boundId τ
            (.fvar (.there .here))) ∧ₘ
        related_formula_code_atₘ(
          Term.substituteMapped VariableSubstitution.boundId τ
            ((symbols.weakenFree SetSort.set).weakenFree SetSort.set),
          Term.substituteMapped VariableSubstitution.boundId τ
            ((depth.weakenFree SetSort.set).weakenFree SetSort.set),
          Term.substituteMapped VariableSubstitution.boundId τ
            (.fvar .here))) ∧ₘ
        (Term.substituteMapped VariableSubstitution.boundId τ
            ((code.weakenFree SetSort.set).weakenFree SetSort.set) ≐ₘ
          Term.substituteMapped VariableSubstitution.boundId τ
            (imp_codeₘ(.fvar (.there .here), .fvar .here)))) =
      ((related_formula_code_atₘ(symbols, depth, left) ∧ₘ
          related_formula_code_atₘ(symbols, depth, right)) ∧ₘ
        (code ≐ₘ imp_codeₘ(left, right)))
    rw [hSymbolsClosed, hDepthClosed, hCodeClosed, hTargetClosed]
    rfl
  rw [hBody]
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro hLeft hRight) hCode

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
