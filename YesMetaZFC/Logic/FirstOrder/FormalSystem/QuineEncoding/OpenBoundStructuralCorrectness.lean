import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.TransformStructuralCorrectness

/-!
# bound 尾槽打开的项与参数列 quotation 正确性

对象层 `openBound` 删除当前 de Bruijn 深度对应的唯一尾槽，并以 bound-closed 项码
替换。宿主侧使用 `instantiateLastBound` 表达同一操作；局部 binder 只提升 replacement，
因此不需要新鲜性、可替换性或停机旁证。
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

/-! ## scope -/

private theorem term_open_bound_scope
    (depth replacement source target : SetOpenTerm [])
    (hReplacement : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_codeₘ(replacement))
    (hSource : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(Sₘ(depth), source))
    (hTarget : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(depth, target)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .openBound)
        depth (numₘ(0)) replacement source target := by
  dsimp [syntax_transform_scope_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_left
    exact FirstOrder.Derives.conj_intro
      (Metatheory.Derives.equality_refl
        (syntax_transform_operation_term .openBound : SetOpenTerm []))
      (FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro hSource hTarget) hReplacement)

private theorem term_list_open_bound_scope
    (depth length replacement source target : SetOpenTerm [])
    (hLength : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      length ∈ₘ ωₘ)
    (hReplacement : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_codeₘ(replacement))
    (hSource : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(Sₘ(depth), length, source))
    (hTarget : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(depth, length, target)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term .termList)
        (syntax_transform_operation_term .openBound)
        depth (numₘ(0)) replacement source target := by
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
            (FirstOrder.Derives.disj_intro_left
              (FirstOrder.Derives.conj_intro
                (Metatheory.Derives.equality_refl
                  (syntax_transform_operation_term .openBound :
                    SetOpenTerm []))
                (FirstOrder.Derives.conj_intro
                  (FirstOrder.Derives.conj_intro hSource hTarget)
                  hReplacement)))))

/-! ## 叶节点 -/

private theorem term_open_bound_free_shape
    (depth replacement : SetOpenTerm []) (index : Nat) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .openBound)
        depth (numₘ(0)) replacement
        (free_var_codeₘ(numₘ(index))) (free_var_codeₘ(numₘ(index))) := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.exists_intro (numₘ(index) : SetOpenTerm [])
    simpa [Formula.instantiateFreeTop, Substitution.instantiateFreeTop,
      Formula.substitute, Formula.substituteMapped,
      Term.substituteFree, Term.substitute, Term.substituteMapped,
      Arguments.substituteMapped,
      VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.liftFree,
      VariableSubstitution.weakenBound,
      VariableSubstitution.boundId, VariableSubstitution.freeId,
      free_variable_code_term, structural_list_code_term,
      structural_node_code_term, structural_raw_node_code_term,
      godel_pairing_term] using
      FirstOrder.Derives.conj_intro
        (finite_numeral_mem_expression (Γ := []) index)
        (FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (free_var_codeₘ(numₘ(index)) : SetOpenTerm []))
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_right
              (FirstOrder.Derives.disj_intro_left
                (FirstOrder.Derives.conj_intro
                  (Metatheory.Derives.equality_refl
                    (syntax_transform_operation_term .openBound :
                      SetOpenTerm []))
                  (Metatheory.Derives.equality_refl
                    (free_var_codeₘ(numₘ(index)) : SetOpenTerm [])))))))

private theorem term_open_bound_bound_preserve_shape
    (depth replacement : SetOpenTerm []) (index : Nat)
    (hIndexDepth : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (numₘ(index) : SetOpenTerm []) ∈ₘ depth)
    (hIndexSuccessor : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (numₘ(index) : SetOpenTerm []) ∈ₘ Sₘ(depth)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .openBound)
        depth (numₘ(0)) replacement
        (bound_var_codeₘ(numₘ(index))) (bound_var_codeₘ(numₘ(index))) := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.exists_intro (numₘ(index) : SetOpenTerm [])
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
          (bound_var_codeₘ(numₘ(index)) : SetOpenTerm []))
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_left
            (FirstOrder.Derives.conj_intro
              (Metatheory.Derives.equality_refl
                (syntax_transform_operation_term .openBound :
                  SetOpenTerm []))
              (FirstOrder.Derives.conj_intro hIndexSuccessor
                (FirstOrder.Derives.disj_intro_right
                  (FirstOrder.Derives.conj_intro hIndexDepth
                    (Metatheory.Derives.equality_refl
                      (bound_var_codeₘ(numₘ(index)) : SetOpenTerm []))))))))

private theorem term_open_bound_bound_hit_shape
    (depth replacement : SetOpenTerm [])
    (hDepthSuccessor : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      depth ∈ₘ Sₘ(depth)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .openBound)
        depth (numₘ(0)) replacement
        (bound_var_codeₘ(depth)) replacement := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.exists_intro depth
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
          (bound_var_codeₘ(depth) : SetOpenTerm []))
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_left
            (FirstOrder.Derives.conj_intro
              (Metatheory.Derives.equality_refl
                (syntax_transform_operation_term .openBound :
                  SetOpenTerm []))
              (FirstOrder.Derives.conj_intro hDepthSuccessor
                (FirstOrder.Derives.disj_intro_left
                  (FirstOrder.Derives.conj_intro
                    (Metatheory.Derives.equality_refl depth)
                    (Metatheory.Derives.equality_refl replacement)))))))

private theorem term_open_bound_constant_shape
    (depth replacement : SetOpenTerm []) (symbol : Nat) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .openBound)
        depth (numₘ(0)) replacement
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

/-! ## 复合节点 -/

private theorem term_open_bound_application_shape
    (depth replacement arity symbol sourceArguments targetArguments :
      SetOpenTerm [])
    (hArity : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      arity ∈ₘ ωₘ)
    (hSymbol : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      symbol ∈ₘ ωₘ)
    (hTransform : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term .openBound,
        depth, numₘ(0), replacement, sourceArguments, targetArguments)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .openBound)
        depth (numₘ(0)) replacement
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

private theorem term_list_open_bound_nil_shape
    (depth replacement : SetOpenTerm []) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .termList)
        (syntax_transform_operation_term .openBound)
        depth (numₘ(0)) replacement code_nilₘ code_nilₘ := by
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

private theorem term_list_open_bound_cons_shape
    (depth replacement sourceHead sourceTail targetHead targetTail :
      SetOpenTerm [])
    (hHead : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .openBound,
        depth, numₘ(0), replacement, sourceHead, targetHead))
    (hTail : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term .openBound,
        depth, numₘ(0), replacement, sourceTail, targetTail)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .termList)
        (syntax_transform_operation_term .openBound)
        depth (numₘ(0)) replacement
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

/-! ## 结构递归 -/

private theorem quote_term_open_bound_last_of_shape
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ} {prefixContext : SortContext σ}
    {sort resultSort : σ.SortSymbol}
    (replacement : Term σ [] free sort)
    (term : Term σ (prefixContext ++ [sort]) free resultSort)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .openBound)
        (numₘ(prefixContext.length)) (numₘ(0))
        (quote_term replacement : SetOpenTerm [])
        (quote_term term : SetOpenTerm [])
        (quote_term
          (Term.instantiateLastBound prefixContext replacement term) :
          SetOpenTerm [])) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_term term : SetOpenTerm []),
        (quote_term
          (Term.instantiateLastBound prefixContext replacement term) :
          SetOpenTerm [])) := by
  have hReplacementAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_codeₘ((quote_term replacement : SetOpenTerm [])) := by
    simpa using! quote_term_code_at_expression replacement
  have hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(Sₘ(numₘ(prefixContext.length)),
        (quote_term term : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_term_code_at_expression term
  have hTargetAt := quote_term_code_at_expression
    (Term.instantiateLastBound prefixContext replacement term)
  apply syntax_transform_intro .term .openBound prefixContext.length 0
    (quote_term replacement : SetOpenTerm [])
  · exact quote_term_code_mem_expression term
  · exact quote_term_code_mem_expression
      (Term.instantiateLastBound prefixContext replacement term)
  · exact quote_term_code_mem_expression replacement
  · exact term_open_bound_scope
      (numₘ(prefixContext.length)) _ _ _
      hReplacementAt hSourceAt hTargetAt
  · exact hShape

private theorem quote_arguments_open_bound_last_of_shape
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ} {prefixContext : SortContext σ}
    {sort : σ.SortSymbol} {sorts : List σ.SortSymbol}
    (replacement : Term σ [] free sort)
    (arguments : Arguments σ (prefixContext ++ [sort]) free sorts)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .termList)
        (syntax_transform_operation_term .openBound)
        (numₘ(prefixContext.length)) (numₘ(0))
        (quote_term replacement : SetOpenTerm [])
        (quote_arguments arguments : SetOpenTerm [])
        (quote_arguments
          (Arguments.instantiateLastBound prefixContext replacement arguments) :
          SetOpenTerm [])) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_arguments arguments : SetOpenTerm []),
        (quote_arguments
          (Arguments.instantiateLastBound prefixContext replacement arguments) :
          SetOpenTerm [])) := by
  have hReplacementAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_codeₘ((quote_term replacement : SetOpenTerm [])) := by
    simpa using! quote_term_code_at_expression replacement
  have hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(Sₘ(numₘ(prefixContext.length)), numₘ(sorts.length),
        (quote_arguments arguments : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_arguments_code_at_expression arguments
  have hTargetAt := quote_arguments_code_at_expression
    (Arguments.instantiateLastBound prefixContext replacement arguments)
  apply syntax_transform_intro .termList .openBound prefixContext.length 0
    (quote_term replacement : SetOpenTerm [])
  · exact quote_arguments_code_mem_expression arguments
  · exact quote_arguments_code_mem_expression
      (Arguments.instantiateLastBound prefixContext replacement arguments)
  · exact quote_term_code_mem_expression replacement
  · exact term_list_open_bound_scope
      (numₘ(prefixContext.length)) (numₘ(sorts.length)) _ _ _
      (finite_numeral_mem_expression (Γ := []) sorts.length)
      hReplacementAt hSourceAt hTargetAt
  · exact hShape

private theorem quote_bound_variable_open_bound_last
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ} {prefixContext : SortContext σ}
    {sort resultSort : σ.SortSymbol}
    (replacement : Term σ [] free sort)
    (entry : Variable (prefixContext ++ [sort]) resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_term
          (.bvar entry : Term σ (prefixContext ++ [sort]) free resultSort) :
          SetOpenTerm []),
        (quote_term
          (Term.instantiateLastBound prefixContext replacement
            (.bvar entry : Term σ (prefixContext ++ [sort]) free resultSort)) :
          SetOpenTerm [])) := by
  rcases VariableSubstitution.instantiateLastBound_bvar
      prefixContext replacement entry with
    ⟨target, hIndex, hTarget⟩ | ⟨hSort, hIndex, hTarget⟩
  · apply quote_term_open_bound_last_of_shape replacement
    have hDepth : entry.index < prefixContext.length := by
      simpa [hIndex] using target.index_lt_length
    have hIndexDepth := finite_numeral_mem_of_lt_expression
      (Γ := ([] : Context signature [])) hDepth
    have hIndexSuccessor := finite_numeral_mem_of_lt_expression
      (Γ := ([] : Context signature [])) (Nat.lt_succ_of_lt hDepth)
    simpa [Term.instantiateLastBound, Substitution.instantiateLastBound,
      Term.substitute, Term.substituteMapped, quote_term, hTarget, hIndex,
      finite_numeral_term] using
      term_open_bound_bound_preserve_shape
        (numₘ(prefixContext.length))
        (quote_term replacement : SetOpenTerm []) entry.index
        hIndexDepth hIndexSuccessor
  · subst resultSort
    apply quote_term_open_bound_last_of_shape replacement
    have hDepthSuccessor := finite_numeral_mem_of_lt_expression
      (Γ := ([] : Context signature []))
      (Nat.lt_succ_self prefixContext.length)
    simpa [Term.instantiateLastBound, Substitution.instantiateLastBound,
      Term.substitute, Term.substituteMapped, quote_term, hTarget, hIndex,
      finite_numeral_term] using
      term_open_bound_bound_hit_shape
        (numₘ(prefixContext.length))
        (quote_term replacement : SetOpenTerm []) hDepthSuccessor

private theorem quote_free_variable_open_bound_last
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ} {prefixContext : SortContext σ}
    {sort resultSort : σ.SortSymbol}
    (replacement : Term σ [] free sort) (entry : Variable free resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_term
          (.fvar entry : Term σ (prefixContext ++ [sort]) free resultSort) :
          SetOpenTerm []),
        (quote_term
          (Term.instantiateLastBound prefixContext replacement
            (.fvar entry : Term σ (prefixContext ++ [sort]) free resultSort)) :
          SetOpenTerm [])) := by
  apply quote_term_open_bound_last_of_shape replacement
  simpa [Term.instantiateLastBound, Substitution.instantiateLastBound,
    Term.substitute, Term.substituteMapped, quote_term] using!
    term_open_bound_free_shape
      (numₘ(prefixContext.length))
      (quote_term replacement : SetOpenTerm []) entry.index

/-- 项 quotation 与 bound 尾槽闭项实例化交换。 -/
theorem quote_term_open_bound_last
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ} {prefixContext : SortContext σ}
    {sort resultSort : σ.SortSymbol}
    (replacement : Term σ [] free sort)
    (term : Term σ (prefixContext ++ [sort]) free resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_term term : SetOpenTerm []),
        (quote_term
          (Term.instantiateLastBound prefixContext replacement term) :
          SetOpenTerm [])) := by
  refine Term.rec
    (motive_1 := fun _ term =>
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        syntax_transformₘ(
          syntax_code_kind_term .term,
          syntax_transform_operation_term .openBound,
          numₘ(prefixContext.length), numₘ(0),
          (quote_term replacement : SetOpenTerm []),
          (quote_term term : SetOpenTerm []),
          (quote_term
            (Term.instantiateLastBound prefixContext replacement term) :
            SetOpenTerm [])))
    (motive_2 := fun _ arguments =>
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        syntax_transformₘ(
          syntax_code_kind_term .termList,
          syntax_transform_operation_term .openBound,
          numₘ(prefixContext.length), numₘ(0),
          (quote_term replacement : SetOpenTerm []),
          (quote_arguments arguments : SetOpenTerm []),
          (quote_arguments
            (Arguments.instantiateLastBound
              prefixContext replacement arguments) : SetOpenTerm [])))
    (fun entry => quote_bound_variable_open_bound_last replacement entry)
    (fun entry => quote_free_variable_open_bound_last replacement entry)
    (fun function arguments ih => by
      cases hDomain : σ.funcDomain function with
      | nil =>
          apply quote_term_open_bound_last_of_shape replacement
          simpa [quote_term, hDomain, Term.instantiateLastBound,
            Substitution.instantiateLastBound, Term.substitute,
            Term.substituteMapped, Arguments.substituteMapped] using
            term_open_bound_constant_shape
              (numₘ(prefixContext.length))
              (quote_term replacement : SetOpenTerm [])
              (QuotationNumbering.function_number function)
      | cons head tail =>
          apply quote_term_open_bound_last_of_shape replacement
          simpa [quote_term, hDomain, Term.instantiateLastBound,
            Arguments.instantiateLastBound,
            Substitution.instantiateLastBound, Term.substitute,
            Arguments.substitute, Term.substituteMapped,
            Arguments.substituteMapped] using
            term_open_bound_application_shape
              (numₘ(prefixContext.length))
              (quote_term replacement : SetOpenTerm [])
              (numₘ(σ.funcArity function))
              (numₘ(QuotationNumbering.function_number function))
              (quote_arguments arguments : SetOpenTerm [])
              (quote_arguments
                (Arguments.instantiateLastBound
                  prefixContext replacement arguments) : SetOpenTerm [])
              (finite_numeral_mem_expression
                (Γ := ([] : Context signature [])) (σ.funcArity function))
              (finite_numeral_mem_expression
                (Γ := ([] : Context signature []))
                (QuotationNumbering.function_number function))
              ih)
    (by
      apply quote_arguments_open_bound_last_of_shape replacement
      simpa [quote_arguments, Arguments.instantiateLastBound,
        Substitution.instantiateLastBound, Arguments.substitute,
        Arguments.substituteMapped] using
        term_list_open_bound_nil_shape
          (numₘ(prefixContext.length))
          (quote_term replacement : SetOpenTerm []))
    (fun head tail ihHead ihTail => by
      apply quote_arguments_open_bound_last_of_shape replacement
      simpa [quote_arguments, Term.instantiateLastBound,
        Arguments.instantiateLastBound,
        Substitution.instantiateLastBound, Term.substitute,
        Arguments.substitute, Term.substituteMapped,
        Arguments.substituteMapped] using
        term_list_open_bound_cons_shape
          (numₘ(prefixContext.length))
          (quote_term replacement : SetOpenTerm [])
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          (quote_term
            (Term.instantiateLastBound prefixContext replacement head) :
            SetOpenTerm [])
          (quote_arguments
            (Arguments.instantiateLastBound prefixContext replacement tail) :
            SetOpenTerm [])
          ihHead ihTail)
    term

/-- 参数列 quotation 与 bound 尾槽闭项实例化交换。 -/
theorem quote_arguments_open_bound_last
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ} {prefixContext : SortContext σ}
    {introduced : σ.SortSymbol} {sorts : List σ.SortSymbol}
    (replacement : Term σ [] free introduced)
    (arguments : Arguments σ (prefixContext ++ [introduced]) free sorts) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_arguments arguments : SetOpenTerm []),
        (quote_arguments
          (Arguments.instantiateLastBound prefixContext replacement arguments) :
          SetOpenTerm [])) := by
  refine Arguments.rec (σ := σ) (bound := prefixContext ++ [introduced])
    (free := free)
    (motive_1 := fun _ term =>
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        syntax_transformₘ(
          syntax_code_kind_term .term,
          syntax_transform_operation_term .openBound,
          numₘ(prefixContext.length), numₘ(0),
          (quote_term replacement : SetOpenTerm []),
          (quote_term term : SetOpenTerm []),
          (quote_term
            (Term.instantiateLastBound prefixContext replacement term) :
            SetOpenTerm [])))
    (motive_2 := fun _ arguments =>
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        syntax_transformₘ(
          syntax_code_kind_term .termList,
          syntax_transform_operation_term .openBound,
          numₘ(prefixContext.length), numₘ(0),
          (quote_term replacement : SetOpenTerm []),
          (quote_arguments arguments : SetOpenTerm []),
          (quote_arguments
            (Arguments.instantiateLastBound
              prefixContext replacement arguments) : SetOpenTerm [])))
    (fun {sort} entry =>
      quote_term_open_bound_last replacement
        (.bvar entry : Term σ (prefixContext ++ [introduced]) free sort))
    (fun {sort} entry =>
      quote_term_open_bound_last replacement
        (.fvar entry : Term σ (prefixContext ++ [introduced]) free sort))
    (fun function sourceArguments _ =>
      quote_term_open_bound_last replacement
        (.app function sourceArguments))
    (by
      apply quote_arguments_open_bound_last_of_shape replacement
      simpa [quote_arguments, Arguments.instantiateLastBound,
        Substitution.instantiateLastBound, Arguments.substitute,
        Arguments.substituteMapped] using
        term_list_open_bound_nil_shape
          (numₘ(prefixContext.length))
          (quote_term replacement : SetOpenTerm []))
    (fun head tail ihHead ihTail => by
      apply quote_arguments_open_bound_last_of_shape replacement
      simpa [quote_arguments, Term.instantiateLastBound,
        Arguments.instantiateLastBound,
        Substitution.instantiateLastBound, Term.substitute,
        Arguments.substitute, Term.substituteMapped,
        Arguments.substituteMapped] using
        term_list_open_bound_cons_shape
          (numₘ(prefixContext.length))
          (quote_term replacement : SetOpenTerm [])
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          (quote_term
            (Term.instantiateLastBound prefixContext replacement head) :
            SetOpenTerm [])
          (quote_arguments
            (Arguments.instantiateLastBound prefixContext replacement tail) :
            SetOpenTerm [])
          ihHead ihTail)
    arguments

end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
