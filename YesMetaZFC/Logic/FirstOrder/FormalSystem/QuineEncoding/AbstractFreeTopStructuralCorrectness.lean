import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.TransformStructuralCorrectness

/-!
# 顶部自由变量抽象的 quotation 正确性

对象侧结构变换在递归进入量词时保留局部 binder 的 de Bruijn 位置，并把根部待抽象
自由变量放到这些局部 binder 之后。本模块用尾扩展上下文表达这一递归不变量，根上下文
为空时即退化为公共 `Formula.abstractFreeTop`。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace QuineEncoding

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped FormalSystem.Symbols

set_option autoImplicit false

private theorem finite_numeral_mem_expression
    {free : SetContext} {Γ : Context signature free}
    (number : Nat) :
    Γ ⊢ₘ[expression_encoding_theory]
      (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ :=
  FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (finite_numeral_mem_formal_language_encoding_theory
      (Γ := Γ) number)

private theorem finite_numeral_mem_of_lt_expression
    {free : SetContext} {Γ : Context signature free}
    {left right : Nat} (h : left < right) :
    Γ ⊢ₘ[expression_encoding_theory]
      (numₘ(left) : SetOpenTerm free) ∈ₘ numₘ(right) :=
  FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (finite_numeral_mem_of_lt_formal_language_encoding_theory
      (Γ := Γ) h)

private theorem quote_term_code_at_expression
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(
        numₘ(bound.length),
        (quote_term term : SetOpenTerm [])) :=
  FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (quote_term_code_at term)

private theorem quote_term_code_mem_expression
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (quote_term term : SetOpenTerm []) ∈ₘ ωₘ :=
  FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (term_code_at_code_mem_of_derives
      (numₘ(bound.length)) (quote_term term : SetOpenTerm [])
      (quote_term_code_at term))

private theorem quote_arguments_code_at_expression
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(
        numₘ(bound.length), numₘ(sorts.length),
        (quote_arguments arguments : SetOpenTerm [])) :=
  FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (quote_arguments_term_list_code_at arguments)

private theorem quote_arguments_code_mem_expression
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (quote_arguments arguments : SetOpenTerm []) ∈ₘ ωₘ :=
  FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (term_list_code_at_code_mem_of_derives
      (numₘ(bound.length)) (numₘ(sorts.length))
      (quote_arguments arguments : SetOpenTerm [])
      (quote_arguments_term_list_code_at arguments))


private theorem term_abstract_free_top_scope
    (depth source target : SetOpenTerm [])
    (hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(depth, source))
    (hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(Sₘ(depth), target)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .abstractFreeTop)
        depth (numₘ(0)) (numₘ(0)) source target := by
  dsimp [syntax_transform_scope_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    exact FirstOrder.Derives.conj_intro
      (Metatheory.Derives.equality_refl
        (syntax_transform_operation_term .abstractFreeTop :
          SetOpenTerm []))
      (FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro
          (FirstOrder.Derives.conj_intro hSourceAt hTargetAt)
          (Metatheory.Derives.equality_refl
            (numₘ(0) : SetOpenTerm [])))
        (Metatheory.Derives.equality_refl
          (numₘ(0) : SetOpenTerm [])))

private theorem term_list_abstract_free_top_scope
    (depth length source target : SetOpenTerm [])
    (hLength : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      length ∈ₘ ωₘ)
    (hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(depth, length, source))
    (hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(Sₘ(depth), length, target)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term .termList)
        (syntax_transform_operation_term .abstractFreeTop)
        depth (numₘ(0)) (numₘ(0)) source target := by
  dsimp [syntax_transform_scope_condition]
  apply FirstOrder.Derives.disj_intro_right
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .termList : SetOpenTerm [])
  · apply FirstOrder.Derives.exists_intro length
    simpa [Formula.instantiateFreeTop, Substitution.instantiateFreeTop,
      Formula.substitute, Formula.substituteMapped,
      Term.substituteFree, Term.substitute, Term.substituteMapped,
      Arguments.substituteMapped,
      VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.liftFree,
      VariableSubstitution.weakenBound,
      VariableSubstitution.boundId, VariableSubstitution.freeId,
      Term.substituteMapped_weakenFree_instantiateFreeTop,
      Arguments.substituteMapped_weakenFree_instantiateFreeTop] using
      FirstOrder.Derives.conj_intro hLength
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_right
              (FirstOrder.Derives.disj_intro_right
                (FirstOrder.Derives.conj_intro
                  (Metatheory.Derives.equality_refl
                    (syntax_transform_operation_term .abstractFreeTop :
                      SetOpenTerm []))
                  (FirstOrder.Derives.conj_intro
                    (FirstOrder.Derives.conj_intro
                      (FirstOrder.Derives.conj_intro hSourceAt hTargetAt)
                      (Metatheory.Derives.equality_refl
                        (numₘ(0) : SetOpenTerm [])))
                    (Metatheory.Derives.equality_refl
                      (numₘ(0) : SetOpenTerm []))))))))

private theorem term_abstract_free_top_bound_shape
    (depth index : SetOpenTerm [])
    (hIndex : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      index ∈ₘ depth) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .abstractFreeTop)
        depth (numₘ(0)) (numₘ(0))
        (bound_var_codeₘ(index)) (bound_var_codeₘ(index)) := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.exists_intro index
    simpa [Formula.instantiateFreeTop, Substitution.instantiateFreeTop,
      Formula.substitute, Formula.substituteMapped,
      Term.substituteFree, Term.substitute, Term.substituteMapped,
      Arguments.substituteMapped,
      VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.liftFree,
      VariableSubstitution.weakenBound,
      VariableSubstitution.boundId, VariableSubstitution.freeId,
      structural_list_code_term, structural_node_code_term,
      structural_raw_node_code_term, godel_pairing_term] using!
      FirstOrder.Derives.conj_intro
        (Metatheory.Derives.equality_refl
          (bound_var_codeₘ(index) : SetOpenTerm []))
        (FirstOrder.Derives.disj_intro_left
          (FirstOrder.Derives.conj_intro
            (FirstOrder.Derives.disj_intro_right
              (FirstOrder.Derives.disj_intro_right
                (Metatheory.Derives.equality_refl
                  (syntax_transform_operation_term .abstractFreeTop :
                    SetOpenTerm []))))
            (FirstOrder.Derives.conj_intro hIndex
              (Metatheory.Derives.equality_refl
                (bound_var_codeₘ(index) : SetOpenTerm [])))))

private theorem term_abstract_free_top_here_shape
    (depth : SetOpenTerm []) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .abstractFreeTop)
        depth (numₘ(0)) (numₘ(0))
        (free_var_codeₘ(numₘ(0))) (bound_var_codeₘ(depth)) := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.exists_intro (numₘ(0) : SetOpenTerm [])
    simpa [Formula.instantiateFreeTop, Substitution.instantiateFreeTop,
      Formula.substitute, Formula.substituteMapped,
      Term.substituteFree, Term.substitute, Term.substituteMapped,
      Arguments.substituteMapped,
      VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.liftFree,
      VariableSubstitution.weakenBound,
      VariableSubstitution.boundId, VariableSubstitution.freeId,
      free_variable_code_term, bound_variable_code_term,
      structural_list_code_term, structural_node_code_term,
      structural_raw_node_code_term, godel_pairing_term] using
      FirstOrder.Derives.conj_intro
        (finite_numeral_mem_expression (Γ := []) 0)
        (FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (free_var_codeₘ(numₘ(0)) : SetOpenTerm []))
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_right
              (FirstOrder.Derives.disj_intro_right
                (FirstOrder.Derives.disj_intro_right
                  (FirstOrder.Derives.conj_intro
                    (Metatheory.Derives.equality_refl
                      (syntax_transform_operation_term .abstractFreeTop :
                        SetOpenTerm []))
                    (FirstOrder.Derives.disj_intro_left
                      (FirstOrder.Derives.conj_intro
                        (Metatheory.Derives.equality_refl
                          (numₘ(0) : SetOpenTerm []))
                        (Metatheory.Derives.equality_refl
                          (bound_var_codeₘ(depth) : SetOpenTerm []))))))))))

private theorem term_abstract_free_top_there_shape
    (depth : SetOpenTerm []) (previous : Nat) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .abstractFreeTop)
        depth (numₘ(0)) (numₘ(0))
        (free_var_codeₘ(Sₘ(numₘ(previous))))
        (free_var_codeₘ(numₘ(previous))) := by
  have hPrevious : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (numₘ(previous) : SetOpenTerm []) ∈ₘ Sₘ(numₘ(previous)) := by
    simpa [finite_numeral_term] using
      finite_numeral_mem_of_lt_expression
        (Γ := ([] : Context signature [])) (Nat.lt_succ_self previous)
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.exists_intro
      (Sₘ(numₘ(previous)) : SetOpenTerm [])
    rw [Formula.instantiateTop_abstractFreeTop]
    simp only [Formula.instantiateFreeTop, Formula.substitute,
      Substitution.instantiateFreeTop, Formula.substituteMapped,
      VariableSubstitution.instantiateFreeTop,
      Term.substituteMapped, Arguments.substituteMapped,
      Term.substituteMapped_weakenFree_instantiateFreeTop,
      free_variable_code_term,
      structural_list_code_term, structural_node_code_term,
      structural_raw_node_code_term, godel_pairing_term]
    apply FirstOrder.Derives.conj_intro
    · exact finite_numeral_mem_expression (Γ := []) (previous + 1)
    · apply FirstOrder.Derives.conj_intro
      · exact Metatheory.Derives.equality_refl
          (free_var_codeₘ(Sₘ(numₘ(previous))) : SetOpenTerm [])
      · apply FirstOrder.Derives.disj_intro_right
        apply FirstOrder.Derives.disj_intro_right
        apply FirstOrder.Derives.disj_intro_right
        apply FirstOrder.Derives.disj_intro_right
        apply FirstOrder.Derives.conj_intro
        · exact Metatheory.Derives.equality_refl
            (syntax_transform_operation_term .abstractFreeTop :
              SetOpenTerm [])
        · apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.exists_intro
            (numₘ(previous) : SetOpenTerm [])
          simpa [Formula.instantiateFreeTop,
            Substitution.instantiateFreeTop,
            Formula.instantiateTop, Substitution.instantiateTop,
            Formula.substitute, Formula.substituteMapped,
            Term.instantiateTop, Term.substituteFree,
            Term.substitute, Term.substituteMapped,
            Arguments.substituteMapped,
            syntax_set_levy_bound, Formula.LevyBound.membership,
            VariableSubstitution.instantiateFreeTop,
            VariableSubstitution.instantiateTop,
            VariableSubstitution.liftFree,
            VariableSubstitution.weakenBound,
            VariableSubstitution.boundId, VariableSubstitution.freeId,
            structural_list_code_term, structural_node_code_term,
            structural_raw_node_code_term, godel_pairing_term] using!
            FirstOrder.Derives.conj_intro hPrevious
              (FirstOrder.Derives.conj_intro
                (Metatheory.Derives.equality_refl
                  (Sₘ(numₘ(previous)) : SetOpenTerm []))
                (Metatheory.Derives.equality_refl
                  (free_var_codeₘ(numₘ(previous)) : SetOpenTerm [])))

private theorem term_abstract_free_top_constant_shape
    (depth : SetOpenTerm []) (symbol : Nat) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .abstractFreeTop)
        depth (numₘ(0)) (numₘ(0))
        (const_codeₘ(numₘ(symbol))) (const_codeₘ(numₘ(symbol))) := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.exists_intro (numₘ(symbol) : SetOpenTerm [])
    simpa [Formula.instantiateFreeTop, Substitution.instantiateFreeTop,
      Formula.substitute, Formula.substituteMapped,
      Term.substituteFree, Term.substitute, Term.substituteMapped,
      Arguments.substituteMapped,
      VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.liftFree,
      VariableSubstitution.weakenBound,
      VariableSubstitution.boundId, VariableSubstitution.freeId,
      Term.substituteMapped_weakenFree_instantiateFreeTop,
      Arguments.substituteMapped_weakenFree_instantiateFreeTop] using
      FirstOrder.Derives.conj_intro
        (finite_numeral_mem_expression (Γ := []) symbol)
        (FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (const_codeₘ(numₘ(symbol)) : SetOpenTerm []))
          (Metatheory.Derives.equality_refl
            (const_codeₘ(numₘ(symbol)) : SetOpenTerm [])))

private theorem term_abstract_free_top_application_shape
    (depth arity symbol sourceArguments targetArguments : SetOpenTerm [])
    (hArity : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      arity ∈ₘ ωₘ)
    (hSymbol : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      symbol ∈ₘ ωₘ)
    (hTransform : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term .abstractFreeTop,
        depth, numₘ(0), numₘ(0), sourceArguments, targetArguments)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .abstractFreeTop)
        depth (numₘ(0)) (numₘ(0))
        (app_codeₘ(arity, symbol, sourceArguments))
        (app_codeₘ(arity, symbol, targetArguments)) := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.exists_intro arity
    rw [Formula.instantiateTop_abstractFreeTop,
      Formula.instantiateFreeTop_existsFreeTop]
    apply FirstOrder.Derives.exists_intro symbol
    rw [Formula.substituteFree_existsFreeTop]
    rw [Formula.instantiateTop_abstractFreeTop,
      Formula.instantiateFreeTop_existsFreeTop]
    apply FirstOrder.Derives.exists_intro sourceArguments
    rw [Formula.substituteFree_existsFreeTop,
      Formula.substituteFree_existsFreeTop]
    rw [Formula.instantiateTop_abstractFreeTop,
      Formula.instantiateFreeTop_existsFreeTop]
    apply FirstOrder.Derives.exists_intro targetArguments
    rw [Formula.instantiateTop_abstractFreeTop]
    rw [four_free_substitution_beta]
    simp only [ Formula.substituteFree]
    let τ : VariableSubstitution signature
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] [] [] :=
      VariableSubstitution.cons targetArguments
        (VariableSubstitution.cons sourceArguments
          (VariableSubstitution.cons symbol
            (VariableSubstitution.cons arity VariableSubstitution.empty)))
    have hClosed : ∀ term : (SetOpenTerm []),
        Term.substituteMapped VariableSubstitution.boundId τ
            ((((term.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
              SetSort.set).weakenFree SetSort.set) = term :=
      gq_closed_four_weaken_substitute τ
    simpa [Formula.substitute, Formula.substituteMapped,
      Substitution.free_map, VariableSubstitution.cons,
      VariableSubstitution.empty, VariableSubstitution.liftFree,
      VariableSubstitution.boundId, Term.substituteMapped,
      Arguments.substituteMapped, structural_list_code_term,
      application_code_term, structural_node_code_term,
      structural_raw_node_code_term, godel_pairing_term,
      term_weaken_free_four, τ, hClosed] using
      FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro hArity hSymbol)
        (FirstOrder.Derives.conj_intro
          (FirstOrder.Derives.conj_intro
            (Metatheory.Derives.equality_refl
              (app_codeₘ(arity, symbol, sourceArguments) : SetOpenTerm []))
            (Metatheory.Derives.equality_refl
              (app_codeₘ(arity, symbol, targetArguments) : SetOpenTerm [])))
          hTransform)

private theorem term_list_abstract_free_top_nil_shape
    (depth : SetOpenTerm []) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .termList)
        (syntax_transform_operation_term .abstractFreeTop)
        depth (numₘ(0)) (numₘ(0)) code_nilₘ code_nilₘ := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_right
  apply FirstOrder.Derives.disj_intro_left
  exact FirstOrder.Derives.conj_intro
    (Metatheory.Derives.equality_refl
      (syntax_code_kind_term .termList : SetOpenTerm []))
    (FirstOrder.Derives.disj_intro_left
      (FirstOrder.Derives.conj_intro
        (Metatheory.Derives.equality_refl (code_nilₘ : SetOpenTerm []))
        (Metatheory.Derives.equality_refl (code_nilₘ : SetOpenTerm []))))

private theorem term_list_abstract_free_top_cons_shape
    (depth sourceHead sourceTail targetHead targetTail : SetOpenTerm [])
    (hHead : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .abstractFreeTop,
        depth, numₘ(0), numₘ(0), sourceHead, targetHead))
    (hTail : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term .abstractFreeTop,
        depth, numₘ(0), numₘ(0), sourceTail, targetTail)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .termList)
        (syntax_transform_operation_term .abstractFreeTop)
        depth (numₘ(0)) (numₘ(0))
        (code_consₘ(sourceHead, sourceTail))
        (code_consₘ(targetHead, targetTail)) := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_right
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .termList : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.exists_intro sourceHead
    rw [Formula.instantiateTop_abstractFreeTop,
      Formula.instantiateFreeTop_existsFreeTop]
    apply FirstOrder.Derives.exists_intro sourceTail
    rw [Formula.substituteFree_existsFreeTop]
    rw [Formula.instantiateTop_abstractFreeTop,
      Formula.instantiateFreeTop_existsFreeTop]
    apply FirstOrder.Derives.exists_intro targetHead
    rw [Formula.substituteFree_existsFreeTop,
      Formula.substituteFree_existsFreeTop]
    rw [Formula.instantiateTop_abstractFreeTop,
      Formula.instantiateFreeTop_existsFreeTop]
    apply FirstOrder.Derives.exists_intro targetTail
    rw [Formula.instantiateTop_abstractFreeTop]
    rw [four_free_substitution_beta]
    simp only [Formula.substituteFree]
    let τ : VariableSubstitution signature
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] [] [] :=
      VariableSubstitution.cons targetTail
        (VariableSubstitution.cons targetHead
          (VariableSubstitution.cons sourceTail
            (VariableSubstitution.cons sourceHead VariableSubstitution.empty)))
    have hClosed : ∀ term : (SetOpenTerm []),
        Term.substituteMapped VariableSubstitution.boundId τ
            ((((term.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
              SetSort.set).weakenFree SetSort.set) = term :=
      gq_closed_four_weaken_substitute τ
    simpa [Formula.substitute, Formula.substituteMapped,
      Substitution.free_map, VariableSubstitution.cons,
      VariableSubstitution.empty, VariableSubstitution.liftFree,
      VariableSubstitution.boundId, Term.substituteMapped,
      Arguments.substituteMapped, structural_list_code_term,
      structural_node_code_term, structural_raw_node_code_term,
      godel_pairing_term, term_weaken_free_four, τ, hClosed] using
      FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (code_consₘ(sourceHead, sourceTail) : SetOpenTerm []))
          (Metatheory.Derives.equality_refl
            (code_consₘ(targetHead, targetTail) : SetOpenTerm [])))
        (FirstOrder.Derives.conj_intro hHead hTail)

private theorem quote_term_abstract_free_top_last_of_shape
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    {introduced resultSort : σ.SortSymbol}
    (term : Term σ bound (introduced :: free) resultSort)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .abstractFreeTop)
        (numₘ(bound.length)) (numₘ(0)) (numₘ(0))
        (quote_term term : SetOpenTerm [])
        (quote_term (term.abstractFreeTopLast bound introduced) :
          SetOpenTerm [])) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_term term : SetOpenTerm []),
        (quote_term (term.abstractFreeTopLast bound introduced) :
          SetOpenTerm [])) := by
  have hSourceAt := quote_term_code_at_expression term
  have hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(
        Sₘ(numₘ(bound.length)),
        (quote_term (term.abstractFreeTopLast bound introduced) :
          SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_term_code_at_expression
        (term.abstractFreeTopLast bound introduced)
  apply syntax_transform_intro .term .abstractFreeTop
    bound.length 0 (numₘ(0))
  · exact quote_term_code_mem_expression term
  · exact quote_term_code_mem_expression
      (term.abstractFreeTopLast bound introduced)
  · exact finite_numeral_mem_expression (Γ := []) 0
  · exact term_abstract_free_top_scope
      (numₘ(bound.length)) _ _ hSourceAt hTargetAt
  · exact hShape

private theorem quote_arguments_abstract_free_top_last_of_shape
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    {introduced : σ.SortSymbol}
    (arguments : Arguments σ bound (introduced :: free) sorts)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .termList)
        (syntax_transform_operation_term .abstractFreeTop)
        (numₘ(bound.length)) (numₘ(0)) (numₘ(0))
        (quote_arguments arguments : SetOpenTerm [])
        (quote_arguments
          (arguments.abstractFreeTopLast bound introduced) : SetOpenTerm [])) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_arguments arguments : SetOpenTerm []),
        (quote_arguments
          (arguments.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
  have hSourceAt := quote_arguments_code_at_expression arguments
  have hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(
        Sₘ(numₘ(bound.length)), numₘ(sorts.length),
        (quote_arguments
          (arguments.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_arguments_code_at_expression
        (arguments.abstractFreeTopLast bound introduced)
  apply syntax_transform_intro .termList .abstractFreeTop
    bound.length 0 (numₘ(0))
  · exact quote_arguments_code_mem_expression arguments
  · exact quote_arguments_code_mem_expression
      (arguments.abstractFreeTopLast bound introduced)
  · exact finite_numeral_mem_expression (Γ := []) 0
  · exact term_list_abstract_free_top_scope
      (numₘ(bound.length)) (numₘ(sorts.length)) _ _
      (finite_numeral_mem_expression (Γ := []) sorts.length)
      hSourceAt hTargetAt
  · exact hShape

private theorem quote_bound_variable_abstract_free_top_last
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    {introduced resultSort : σ.SortSymbol}
    (entry : Variable bound resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_term
          (.bvar entry : Term σ bound (introduced :: free) resultSort) :
          SetOpenTerm []),
        (quote_term
          ((.bvar entry : Term σ bound (introduced :: free) resultSort)
            |>.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
  have hSourceAt := quote_term_code_at_expression
    (.bvar entry : Term σ bound (introduced :: free) resultSort)
  have hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(
        Sₘ(numₘ(bound.length)),
        (quote_term
          ((.bvar entry : Term σ bound (introduced :: free) resultSort)
            |>.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_term_code_at_expression
        ((.bvar entry : Term σ bound (introduced :: free) resultSort)
          |>.abstractFreeTopLast bound introduced)
  have hSourceMem := quote_term_code_mem_expression
    (.bvar entry : Term σ bound (introduced :: free) resultSort)
  have hTargetMem := quote_term_code_mem_expression
    ((.bvar entry : Term σ bound (introduced :: free) resultSort)
      |>.abstractFreeTopLast bound introduced)
  have hIndex := finite_numeral_mem_of_lt_expression
    (Γ := ([] : Context signature [])) entry.index_lt_length
  apply syntax_transform_intro .term .abstractFreeTop
    bound.length 0 (numₘ(0))
  · exact hSourceMem
  · exact hTargetMem
  · exact finite_numeral_mem_expression (Γ := []) 0
  · exact term_abstract_free_top_scope
      (numₘ(bound.length)) _ _ hSourceAt hTargetAt
  · simpa [Term.abstractFreeTopLast, Substitution.abstractFreeTopLast,
      Term.substitute, Term.substituteMapped, Arguments.substituteMapped,
      quote_term, Variable.index_appendRight] using
      term_abstract_free_top_bound_shape
        (numₘ(bound.length)) (numₘ(entry.index)) hIndex

private theorem quote_free_variable_abstract_free_top_last
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    {introduced resultSort : σ.SortSymbol}
    (entry : Variable (introduced :: free) resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_term (.fvar entry : Term σ bound
          (introduced :: free) resultSort) : SetOpenTerm []),
        (quote_term
          ((.fvar entry : Term σ bound (introduced :: free) resultSort)
            |>.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
  have hSourceAt := quote_term_code_at_expression
    (.fvar entry : Term σ bound (introduced :: free) resultSort)
  have hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(
        Sₘ(numₘ(bound.length)),
        (quote_term
          ((.fvar entry : Term σ bound (introduced :: free) resultSort)
            |>.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_term_code_at_expression
        ((.fvar entry : Term σ bound (introduced :: free) resultSort)
          |>.abstractFreeTopLast bound introduced)
  have hSourceMem := quote_term_code_mem_expression
    (.fvar entry : Term σ bound (introduced :: free) resultSort)
  have hTargetMem := quote_term_code_mem_expression
    ((.fvar entry : Term σ bound (introduced :: free) resultSort)
      |>.abstractFreeTopLast bound introduced)
  apply syntax_transform_intro .term .abstractFreeTop
    bound.length 0 (numₘ(0))
  · exact hSourceMem
  · exact hTargetMem
  · exact finite_numeral_mem_expression (Γ := []) 0
  · exact term_abstract_free_top_scope
      (numₘ(bound.length)) _ _ hSourceAt hTargetAt
  · cases entry with
    | here =>
        simpa [Term.abstractFreeTopLast, Substitution.abstractFreeTopLast,
          Term.substitute, Term.substituteMapped, Arguments.substituteMapped,
          quote_term, Variable.index, Variable.index_last] using
          term_abstract_free_top_here_shape (numₘ(bound.length))
    | there previous =>
        simpa [Term.abstractFreeTopLast, Substitution.abstractFreeTopLast,
          Term.substitute, Term.substituteMapped, Arguments.substituteMapped,
          quote_term, Variable.index, finite_numeral_term] using
          term_abstract_free_top_there_shape
            (numₘ(bound.length)) previous.index

/-- 项 quotation 与尾槽自由变量抽象交换。 -/
theorem quote_term_abstract_free_top_last
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    {introduced resultSort : σ.SortSymbol}
    (term : Term σ bound (introduced :: free) resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_term term : SetOpenTerm []),
        (quote_term (term.abstractFreeTopLast bound introduced) :
          SetOpenTerm [])) := by
  refine Term.rec
    (motive_1 := fun _ term =>
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        syntax_transformₘ(
          syntax_code_kind_term .term,
          syntax_transform_operation_term .abstractFreeTop,
          numₘ(bound.length), numₘ(0), numₘ(0),
          (quote_term term : SetOpenTerm []),
          (quote_term (term.abstractFreeTopLast bound introduced) :
            SetOpenTerm [])))
    (motive_2 := fun _ arguments =>
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        syntax_transformₘ(
          syntax_code_kind_term .termList,
          syntax_transform_operation_term .abstractFreeTop,
          numₘ(bound.length), numₘ(0), numₘ(0),
          (quote_arguments arguments : SetOpenTerm []),
          (quote_arguments
            (arguments.abstractFreeTopLast bound introduced) :
            SetOpenTerm [])))
    (fun entry => quote_bound_variable_abstract_free_top_last entry)
    (fun entry => quote_free_variable_abstract_free_top_last entry)
    (fun function arguments ih => by
      cases hDomain : σ.funcDomain function with
      | nil =>
          apply quote_term_abstract_free_top_last_of_shape
          simpa [quote_term, hDomain, Term.abstractFreeTopLast,
            Substitution.abstractFreeTopLast, Term.substitute,
            Term.substituteMapped, Arguments.substituteMapped] using
            term_abstract_free_top_constant_shape
              (numₘ(bound.length))
              (QuotationNumbering.function_number function)
      | cons head tail =>
          apply quote_term_abstract_free_top_last_of_shape
          simpa [quote_term, hDomain, Term.abstractFreeTopLast,
            Arguments.abstractFreeTopLast, Substitution.abstractFreeTopLast,
            Term.substitute, Arguments.substitute, Term.substituteMapped,
            Arguments.substituteMapped] using
            term_abstract_free_top_application_shape
              (numₘ(bound.length))
              (numₘ(σ.funcArity function))
              (numₘ(QuotationNumbering.function_number function))
              (quote_arguments arguments : SetOpenTerm [])
              (quote_arguments
                (arguments.abstractFreeTopLast bound introduced) :
                SetOpenTerm [])
              (finite_numeral_mem_expression
                (Γ := ([] : Context signature [])) (σ.funcArity function))
              (finite_numeral_mem_expression
                (Γ := ([] : Context signature []))
                (QuotationNumbering.function_number function))
              ih)
    (by
      apply quote_arguments_abstract_free_top_last_of_shape
      simpa [quote_arguments, Arguments.abstractFreeTopLast,
        Substitution.abstractFreeTopLast, Arguments.substitute,
        Arguments.substituteMapped] using
        term_list_abstract_free_top_nil_shape (numₘ(bound.length)))
    (fun head tail ihHead ihTail => by
      apply quote_arguments_abstract_free_top_last_of_shape
      simpa [quote_arguments, Term.abstractFreeTopLast,
        Arguments.abstractFreeTopLast, Substitution.abstractFreeTopLast,
        Term.substitute, Arguments.substitute, Term.substituteMapped,
        Arguments.substituteMapped] using
        term_list_abstract_free_top_cons_shape
          (numₘ(bound.length))
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          (quote_term (head.abstractFreeTopLast bound introduced) :
            SetOpenTerm [])
          (quote_arguments
            (tail.abstractFreeTopLast bound introduced) : SetOpenTerm [])
          ihHead ihTail)
    term

/-- 参数列 quotation 与尾槽自由变量抽象交换。 -/
theorem quote_arguments_abstract_free_top_last
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    {introduced : σ.SortSymbol}
    (arguments : Arguments σ bound (introduced :: free) sorts) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_arguments arguments : SetOpenTerm []),
        (quote_arguments
          (arguments.abstractFreeTopLast bound introduced) :
          SetOpenTerm [])) := by
  refine Arguments.rec (σ := σ) (bound := bound)
    (free := introduced :: free)
    (motive_1 := fun _ term =>
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        syntax_transformₘ(
          syntax_code_kind_term .term,
          syntax_transform_operation_term .abstractFreeTop,
          numₘ(bound.length), numₘ(0), numₘ(0),
          (quote_term term : SetOpenTerm []),
          (quote_term (term.abstractFreeTopLast bound introduced) :
            SetOpenTerm [])))
    (motive_2 := fun _ arguments =>
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        syntax_transformₘ(
          syntax_code_kind_term .termList,
          syntax_transform_operation_term .abstractFreeTop,
          numₘ(bound.length), numₘ(0), numₘ(0),
          (quote_arguments arguments : SetOpenTerm []),
          (quote_arguments
            (arguments.abstractFreeTopLast bound introduced) :
            SetOpenTerm [])))
    (fun {sort} entry =>
      quote_term_abstract_free_top_last
        (.bvar entry : Term σ bound (introduced :: free) sort))
    (fun {sort} entry =>
      quote_term_abstract_free_top_last
        (.fvar entry : Term σ bound (introduced :: free) sort))
    (fun function arguments _ =>
      quote_term_abstract_free_top_last
        (.app function arguments))
    (by
      apply quote_arguments_abstract_free_top_last_of_shape
      simpa [quote_arguments, Arguments.abstractFreeTopLast,
        Substitution.abstractFreeTopLast, Arguments.substitute,
        Arguments.substituteMapped] using
        term_list_abstract_free_top_nil_shape (numₘ(bound.length)))
    (fun head tail ihHead ihTail => by
      apply quote_arguments_abstract_free_top_last_of_shape
      simpa [quote_arguments, Term.abstractFreeTopLast,
        Arguments.abstractFreeTopLast, Substitution.abstractFreeTopLast,
        Term.substitute, Arguments.substitute, Term.substituteMapped,
        Arguments.substituteMapped] using
        term_list_abstract_free_top_cons_shape
          (numₘ(bound.length))
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          (quote_term (head.abstractFreeTopLast bound introduced) :
            SetOpenTerm [])
          (quote_arguments
            (tail.abstractFreeTopLast bound introduced) : SetOpenTerm [])
          ihHead ihTail)
    arguments

end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
