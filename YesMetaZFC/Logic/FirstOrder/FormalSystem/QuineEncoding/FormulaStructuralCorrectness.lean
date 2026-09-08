import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.StructuralCorrectness

/-!
# 公式结构 quotation 的对象侧正确性

本层在项与参数列正确性的基础上，逐构造子证明公式码递归方程。见证直接来自内在
语法构造，不引入 token、字符串、可满足性或额外的新鲜性假设。
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

/-- 连续实例化两个自由槽等于一次双槽替换。 -/
theorem two_free_substitution_beta
    {body : SetOpenFormula [SetSort.set, SetSort.set]}
    (first second : SetOpenTerm []) :
    Formula.instantiateFreeTop first
      (Formula.substituteFree
        (VariableSubstitution.liftFree SetSort.set
          (VariableSubstitution.instantiateFreeTop second)) body) =
      Formula.substituteFree
        (VariableSubstitution.cons first
          (VariableSubstitution.cons second VariableSubstitution.empty)) body := by
  change
    Formula.substitute (Substitution.instantiateFreeTop first)
      (Formula.substitute
        (Substitution.free_map
          (VariableSubstitution.liftFree SetSort.set
            (VariableSubstitution.instantiateFreeTop second))) body) =
      Formula.substitute
        (Substitution.free_map
          (VariableSubstitution.cons first
            (VariableSubstitution.cons second VariableSubstitution.empty))) body
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
      | there impossible =>
          cases impossible

private theorem gq_closed_one_weaken_substitute
    (τ : VariableSubstitution signature [SetSort.set] [] [])
    {resultSort : signature.SortSymbol}
    (term : Term signature [] [] resultSort) :
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

theorem gq_closed_two_weaken_substitute
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

private theorem formula_code_binary_atomic_condition_intro
    (tag : StructuralCodeTag)
    (depth code left right : SetOpenTerm [])
    (hLeft : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_atₘ(depth, left))
    (hRight : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_atₘ(depth, right))
    (hCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ≐ₘ structural_node_code_term tag [left, right]) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_binary_atomic_condition tag depth code := by
  unfold formula_code_binary_atomic_condition
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
  have hLeftClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          ((left.weakenFree SetSort.set).weakenFree SetSort.set) =
        left :=
    gq_closed_two_weaken_substitute τ left
  have hRightClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          ((right.weakenFree SetSort.set).weakenFree SetSort.set) =
        right :=
    gq_closed_two_weaken_substitute τ right
  have hTargetClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (structural_node_code_term tag
            [.fvar (.there .here), .fvar .here]) =
        structural_node_code_term tag [left, right] := by
    have hHere :
        τ (.here : Variable [SetSort.set, SetSort.set] SetSort.set) = right :=
      rfl
    have hThere :
        τ (.there .here : Variable [SetSort.set, SetSort.set] SetSort.set) = left :=
      rfl
    simp [structural_node_code_term, structural_list_code_term,
      structural_raw_node_code_term, godel_pairing_term,
      Term.substituteMapped, Arguments.substituteMapped, τ,
      VariableSubstitution.cons]
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
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    ((term_code_atₘ(
        (depth.weakenFree SetSort.set).weakenFree SetSort.set,
        .fvar (.there .here)) ∧ₘ
      term_code_atₘ(
        (depth.weakenFree SetSort.set).weakenFree SetSort.set,
        .fvar .here)) ∧ₘ
      (((code.weakenFree SetSort.set).weakenFree SetSort.set) ≐ₘ
        structural_node_code_term tag
          [.fvar (.there .here), .fvar .here]))
  have hArgsLeft :
      Arguments.substituteMapped VariableSubstitution.boundId τ
          (Arguments.cons
            ((depth.weakenFree SetSort.set).weakenFree SetSort.set)
            (Arguments.cons (.fvar (.there .here)) Arguments.nil)) =
        Arguments.cons depth (Arguments.cons left Arguments.nil) := by
    simp [Arguments.substituteMapped, Term.substituteMapped,
      VariableSubstitution.cons, τ,
      hDepthClosed]
  have hArgsRight :
      Arguments.substituteMapped VariableSubstitution.boundId τ
          (Arguments.cons
            ((depth.weakenFree SetSort.set).weakenFree SetSort.set)
            (Arguments.cons (.fvar .here) Arguments.nil)) =
        Arguments.cons depth (Arguments.cons right Arguments.nil) := by
    simp [Arguments.substituteMapped, Term.substituteMapped,
      VariableSubstitution.cons, τ,
      hDepthClosed]
  change ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
    Formula.substitute (Substitution.free_map τ) body
  have hBody :
      Formula.substitute (Substitution.free_map τ) body =
        ((term_code_atₘ(depth, left) ∧ₘ term_code_atₘ(depth, right)) ∧ₘ
          (code ≐ₘ structural_node_code_term tag [left, right])) := by
    simp only [body, Formula.substitute, Formula.substituteMapped,
      Substitution.free_map, τ]
    rw [hArgsLeft, hArgsRight, hCodeClosed, hTargetClosed]
  rw [hBody]
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro hLeft hRight) hCode

private theorem formula_code_negation_condition_intro
    (depth code body : SetOpenTerm [])
    (hBody : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, body))
    (hCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ≐ₘ neg_codeₘ(body)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_negation_condition depth code := by
  unfold formula_code_negation_condition
  apply FirstOrder.Derives.exists_intro body
  rw [Formula.instantiateTop_abstractFreeTop]
  let τ : VariableSubstitution signature [SetSort.set] [] [] :=
    VariableSubstitution.instantiateFreeTop body
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
          (neg_codeₘ(
            (.fvar .here : SetOpenTerm [SetSort.set]))) =
        neg_codeₘ(body) := by
    simp only [Term.substituteMapped, Arguments.substituteMapped, τ]
    rfl
  simp only [Formula.instantiateFreeTop]
  let bodyFormula : SetOpenFormula [SetSort.set] :=
    formula_code_atₘ(depth.weakenFree SetSort.set, .fvar .here) ∧ₘ
      ((code.weakenFree SetSort.set) ≐ₘ
        neg_codeₘ(.fvar .here))
  change ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
    Formula.substitute (Substitution.free_map τ) bodyFormula
  have hFormula :
      Formula.substitute (Substitution.free_map τ) bodyFormula =
        formula_code_atₘ(depth, body) ∧ₘ
          (code ≐ₘ neg_codeₘ(body)) := by
    change
      (formula_code_atₘ(
          Term.substituteMapped VariableSubstitution.boundId τ
            (depth.weakenFree SetSort.set),
          Term.substituteMapped VariableSubstitution.boundId τ
            (.fvar .here)) ∧ₘ
        (Term.substituteMapped VariableSubstitution.boundId τ
            (code.weakenFree SetSort.set) ≐ₘ
          Term.substituteMapped VariableSubstitution.boundId τ
            (neg_codeₘ(.fvar .here)))) =
        formula_code_atₘ(depth, body) ∧ₘ
          (code ≐ₘ neg_codeₘ(body))
    rw [hDepthClosed, hNegClosed, hCodeClosed]
    rfl
  rw [hFormula]
  exact FirstOrder.Derives.conj_intro hBody hCode

private theorem formula_code_implication_condition_intro
    (depth code left right : SetOpenTerm [])
    (hLeft : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, left))
    (hRight : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, right))
    (hCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ≐ₘ imp_codeₘ(left, right)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_implication_condition depth code := by
  unfold formula_code_implication_condition
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
          (structural_node_code_term .implication
            [.fvar (.there .here), .fvar .here]) =
        structural_node_code_term .implication [left, right] := by
    have hHere :
        τ (.here : Variable [SetSort.set, SetSort.set] SetSort.set) = right :=
      rfl
    have hThere :
        τ (.there .here : Variable [SetSort.set, SetSort.set] SetSort.set) = left :=
      rfl
    simp [structural_node_code_term, structural_list_code_term,
      structural_raw_node_code_term, godel_pairing_term,
      Term.substituteMapped, Arguments.substituteMapped, τ,
      VariableSubstitution.cons]
  have hArgsLeft :
      Arguments.substituteMapped VariableSubstitution.boundId τ
          (Arguments.cons
            ((depth.weakenFree SetSort.set).weakenFree SetSort.set)
            (Arguments.cons (.fvar (.there .here)) Arguments.nil)) =
        Arguments.cons depth (Arguments.cons left Arguments.nil) := by
    simp [Arguments.substituteMapped, Term.substituteMapped,
      VariableSubstitution.cons, τ,
      hDepthClosed]
  have hArgsRight :
      Arguments.substituteMapped VariableSubstitution.boundId τ
          (Arguments.cons
            ((depth.weakenFree SetSort.set).weakenFree SetSort.set)
            (Arguments.cons (.fvar .here) Arguments.nil)) =
        Arguments.cons depth (Arguments.cons right Arguments.nil) := by
    simp [Arguments.substituteMapped, Term.substituteMapped,
      VariableSubstitution.cons, τ,
      hDepthClosed]
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    ((formula_code_atₘ(
        (depth.weakenFree SetSort.set).weakenFree SetSort.set,
        .fvar (.there .here)) ∧ₘ
      formula_code_atₘ(
        (depth.weakenFree SetSort.set).weakenFree SetSort.set,
        .fvar .here)) ∧ₘ
      (((code.weakenFree SetSort.set).weakenFree SetSort.set) ≐ₘ
        structural_node_code_term .implication
          [.fvar (.there .here), .fvar .here]))
  change ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
    Formula.substitute (Substitution.free_map τ) body
  have hBody :
      Formula.substitute (Substitution.free_map τ) body =
        ((formula_code_atₘ(depth, left) ∧ₘ formula_code_atₘ(depth, right)) ∧ₘ
          (code ≐ₘ structural_node_code_term .implication [left, right])) := by
    simp only [body, Formula.substitute, Formula.substituteMapped,
      Substitution.free_map, τ]
    rw [hArgsLeft, hArgsRight, hCodeClosed, hTargetClosed]
  rw [hBody]
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro hLeft hRight) hCode

private theorem formula_code_predicate_condition_intro
    (depth code arity symbol arguments : SetOpenTerm [])
    (hArity :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        arity ∈ₘ ωₘ)
    (hSymbol :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        symbol ∈ₘ ωₘ)
    (hArguments :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_list_code_atₘ(depth, arity, arguments))
    (hCode :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        code ≐ₘ pred_codeₘ(arity, symbol, arguments)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_predicate_condition depth code := by
  unfold formula_code_predicate_condition
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
      (.fvar (.there .here) ∈ₘ ωₘ)) ∧ₘ
        (term_list_code_atₘ(
            term_weaken_free_three depth,
            .fvar (.there (.there .here)), .fvar .here) ∧ₘ
          (term_weaken_free_three code ≐ₘ
            pred_codeₘ(.fvar (.there (.there .here)),
              .fvar (.there .here), .fvar .here)))
  change ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
    Formula.substitute (Substitution.free_map τ) body
  have hBody :
      Formula.substitute (Substitution.free_map τ) body =
        ((arity ∈ₘ ωₘ) ∧ₘ (symbol ∈ₘ ωₘ)) ∧ₘ
          (term_list_code_atₘ(depth, arity, arguments) ∧ₘ
            (code ≐ₘ pred_codeₘ(arity, symbol, arguments))) := by
    simp [body, Formula.substitute, Formula.substituteMapped,
      Substitution.free_map, VariableSubstitution.cons, Term.substituteMapped,
      Arguments.substituteMapped,
      structural_list_code_term, predicate_formula_code_term,
      structural_node_code_term, structural_raw_node_code_term,
      godel_pairing_term, τ, hDepthClosed, hCodeClosed]
  rw [hBody]
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro hArity hSymbol)
    (FirstOrder.Derives.conj_intro hArguments hCode)

private theorem formula_code_universal_condition_intro
    (depth code body : SetOpenTerm [])
    (hBody :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(Sₘ(depth), body))
    (hCode :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        code ≐ₘ all_codeₘ(body)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_universal_condition depth code := by
  unfold formula_code_universal_condition
  apply FirstOrder.Derives.exists_intro body
  rw [Formula.instantiateTop_abstractFreeTop]
  let τ : VariableSubstitution signature [SetSort.set] [] [] :=
    VariableSubstitution.instantiateFreeTop body
  have hDepthClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (Sₘ(depth.weakenFree SetSort.set)) =
        Sₘ(depth) := by
    change
      Sₘ(Term.substituteMapped VariableSubstitution.boundId τ
        (depth.weakenFree SetSort.set)) =
        Sₘ(depth)
    rw [gq_closed_one_weaken_substitute τ depth]
  have hCodeClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (code.weakenFree SetSort.set) =
        code :=
    gq_closed_one_weaken_substitute τ code
  have hAllClosed :
      Term.substituteMapped VariableSubstitution.boundId τ
          (all_codeₘ(
            (.fvar .here : SetOpenTerm [SetSort.set]))) =
        all_codeₘ(body) := by
    simp only [Term.substituteMapped, Arguments.substituteMapped, τ]
    rfl
  simp only [Formula.instantiateFreeTop]
  let bodyFormula : SetOpenFormula [SetSort.set] :=
    formula_code_atₘ(Sₘ(depth.weakenFree SetSort.set), .fvar .here) ∧ₘ
      ((code.weakenFree SetSort.set) ≐ₘ
        all_codeₘ(.fvar .here))
  change ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
    Formula.substitute (Substitution.free_map τ) bodyFormula
  have hFormula :
      Formula.substitute (Substitution.free_map τ) bodyFormula =
        formula_code_atₘ(Sₘ(depth), body) ∧ₘ
          (code ≐ₘ all_codeₘ(body)) := by
    change
      (formula_code_atₘ(
          Term.substituteMapped VariableSubstitution.boundId τ
            (Sₘ(depth.weakenFree SetSort.set)),
          Term.substituteMapped VariableSubstitution.boundId τ
            (.fvar .here)) ∧ₘ
        (Term.substituteMapped VariableSubstitution.boundId τ
            (code.weakenFree SetSort.set) ≐ₘ
          Term.substituteMapped VariableSubstitution.boundId τ
            (all_codeₘ(.fvar .here)))) =
        formula_code_atₘ(Sₘ(depth), body) ∧ₘ
          (code ≐ₘ all_codeₘ(body))
    rw [hDepthClosed, hAllClosed, hCodeClosed]
    rfl
  rw [hFormula]
  exact FirstOrder.Derives.conj_intro hBody hCode

private theorem formula_code_at_of_condition_branch
    (depth code : SetOpenTerm [])
    (hDepth :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        depth ∈ₘ ωₘ)
    (hCode :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        code ∈ₘ ωₘ)
    (hBranch :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_binary_atomic_condition .equality depth code ∨ₘ
          (formula_code_binary_atomic_condition .membership depth code ∨ₘ
            (formula_code_predicate_condition depth code ∨ₘ
              (formula_code_negation_condition depth code ∨ₘ
                (formula_code_implication_condition depth code ∨ₘ
                  formula_code_universal_condition depth code))))) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (formula_code_at_definition_instance_derives
      (Γ := ([] : Context signature [])) depth code)
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro hDepth hCode) hBranch

theorem formula_code_at_code_mem_of_derives
    (depth code : SetOpenTerm [])
    (hCode :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(depth, code)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ∈ₘ ωₘ := by
  have hCondition := FirstOrder.Derives.iff_elim_left
    (formula_code_at_definition_instance_derives
      (Γ := ([] : Context signature [])) depth code)
    hCode
  exact FirstOrder.Derives.conj_elim_right
    (FirstOrder.Derives.conj_elim_left hCondition)

private theorem formula_code_at_of_negation
    (depth body : SetOpenTerm [])
    (hDepth :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        depth ∈ₘ ωₘ)
    (hBody :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(depth, body)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, neg_codeₘ(body)) := by
  have hBodyCode := formula_code_at_code_mem_of_derives depth body hBody
  have hCode :=
    structural_node_code_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) StructuralCodeTag.negation [body]
      (by
        intro field hField
        simp only [List.mem_cons, List.not_mem_nil] at hField
        rcases hField with hField | hField
        · simpa [hField] using hBodyCode
        · contradiction)
  have hBranch := formula_code_negation_condition_intro
    depth (neg_codeₘ(body) : SetOpenTerm []) body hBody
    (Metatheory.Derives.equality_refl
      (neg_codeₘ(body) : SetOpenTerm []))
  exact formula_code_at_of_condition_branch depth
    (neg_codeₘ(body) : SetOpenTerm []) hDepth
    (by
      simpa [structural_node_code_term, structural_list_code_term] using! hCode)
    (FirstOrder.Derives.disj_intro_right
      (FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_left hBranch))))

private theorem formula_code_at_of_implication
    (depth left right : SetOpenTerm [])
    (hDepth :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        depth ∈ₘ ωₘ)
    (hLeft :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(depth, left))
    (hRight :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(depth, right)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, imp_codeₘ(left, right)) := by
  have hLeftCode := formula_code_at_code_mem_of_derives depth left hLeft
  have hRightCode := formula_code_at_code_mem_of_derives depth right hRight
  have hCode :=
    structural_node_code_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) StructuralCodeTag.implication
      [left, right] (by
        intro field hField
        simp only [List.mem_cons, List.not_mem_nil] at hField
        rcases hField with hField | hField
        · simpa [hField] using hLeftCode
        · rcases hField with hField | hField
          · simpa [hField] using hRightCode
          · contradiction)
  have hBranch := formula_code_implication_condition_intro
    depth (imp_codeₘ(left, right) : SetOpenTerm []) left right
    hLeft hRight
    (Metatheory.Derives.equality_refl
      (imp_codeₘ(left, right) : SetOpenTerm []))
  exact formula_code_at_of_condition_branch depth
    (imp_codeₘ(left, right) : SetOpenTerm []) hDepth
    (by
      simpa [structural_node_code_term, structural_list_code_term] using! hCode)
    (FirstOrder.Derives.disj_intro_right
      (FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_left hBranch)))))

private theorem formula_code_at_of_universal
    (depth body : SetOpenTerm [])
    (hDepth :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        depth ∈ₘ ωₘ)
    (hBody :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(Sₘ(depth), body)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, all_codeₘ(body)) := by
  have hBodyCode := formula_code_at_code_mem_of_derives
    (Sₘ(depth) : SetOpenTerm []) body hBody
  have hCode :=
    structural_node_code_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) StructuralCodeTag.universal [body]
      (by
        intro field hField
        simp only [List.mem_cons, List.not_mem_nil] at hField
        rcases hField with hField | hField
        · simpa [hField] using hBodyCode
        · contradiction)
  have hBranch := formula_code_universal_condition_intro
    depth (all_codeₘ(body) : SetOpenTerm []) body hBody
    (Metatheory.Derives.equality_refl
      (all_codeₘ(body) : SetOpenTerm []))
  exact formula_code_at_of_condition_branch depth
    (all_codeₘ(body) : SetOpenTerm []) hDepth
    (by
      simpa [structural_node_code_term, structural_list_code_term] using! hCode)
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_right
              (FirstOrder.Derives.disj_intro_right
                (FirstOrder.Derives.disj_intro_right
                  (FirstOrder.Derives.disj_intro_right hBranch)))))

theorem formula_code_at_implication_intro
    (depth left right : SetOpenTerm [])
    (hDepth :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        depth ∈ₘ ωₘ)
    (hLeft :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(depth, left))
    (hRight :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(depth, right)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, imp_codeₘ(left, right)) :=
  formula_code_at_of_implication depth left right hDepth hLeft hRight

theorem formula_code_at_universal_intro
    (depth body : SetOpenTerm [])
    (hDepth :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        depth ∈ₘ ωₘ)
    (hBody :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(Sₘ(depth), body)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, all_codeₘ(body)) :=
  formula_code_at_of_universal depth body hDepth hBody

private theorem formula_code_at_of_equality
    (depth left right : SetOpenTerm [])
    (hDepth :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        depth ∈ₘ ωₘ)
    (hLeft :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(depth, left))
    (hRight :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(depth, right)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(
        depth, structural_node_code_term .equality [left, right]) := by
  have hLeftCode := term_code_at_code_mem_of_derives depth left hLeft
  have hRightCode := term_code_at_code_mem_of_derives depth right hRight
  have hCode :=
    structural_node_code_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) .equality [left, right] (by
        intro field hField
        simp only [List.mem_cons, List.not_mem_nil] at hField
        rcases hField with hField | hField
        · simpa [hField] using hLeftCode
        · rcases hField with hField | hField
          · simpa [hField] using hRightCode
          · contradiction)
  have hBranch := formula_code_binary_atomic_condition_intro
    .equality depth
    (structural_node_code_term .equality [left, right] : SetOpenTerm [])
    left right hLeft hRight
    (Metatheory.Derives.equality_refl
      (structural_node_code_term .equality [left, right] : SetOpenTerm []))
  exact formula_code_at_of_condition_branch depth
    (structural_node_code_term .equality [left, right] : SetOpenTerm []) hDepth
    (by
      simpa using hCode)
    (FirstOrder.Derives.disj_intro_left hBranch)

theorem formula_code_at_equality_intro
    (depth left right : SetOpenTerm [])
    (hDepth :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        depth ∈ₘ ωₘ)
    (hLeft :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(depth, left))
    (hRight :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(depth, right)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(
        depth, structural_node_code_term .equality [left, right]) :=
  formula_code_at_of_equality depth left right hDepth hLeft hRight

/-! ## 外部深度提升 -/

/-- 类型化关系原子在不小于其 bound 上下文长度的任意外部深度下都满足公式码递归谓词。 -/
theorem quote_relation_formula_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (relation : σ.RelSymbol)
    (arguments : Arguments σ bound free (σ.relDomain relation))
    (depth : Nat) (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(
        numₘ(depth),
        (quote_relation relation arguments : SetOpenTerm [])) := by
  have hDepth := finite_numeral_mem_formal_language_encoding_theory
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
                  have hLeft := quote_term_code_at_of_depth
                    left depth hBound
                  have hRight := quote_term_code_at_of_depth
                    right depth hBound
                  have hLeftCode := term_code_at_code_mem_of_derives
                    (numₘ(depth))
                    (quote_term left : SetOpenTerm []) hLeft
                  have hRightCode := term_code_at_code_mem_of_derives
                    (numₘ(depth))
                    (quote_term right : SetOpenTerm []) hRight
                  have hCode :=
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
                  have hBranch := formula_code_binary_atomic_condition_intro
                    StructuralCodeTag.membership
                    (numₘ(depth))
                    (mem_codeₘ(
                      (quote_term left : SetOpenTerm []),
                      (quote_term right : SetOpenTerm [])) :
                      SetOpenTerm [])
                    (quote_term left : SetOpenTerm [])
                    (quote_term right : SetOpenTerm [])
                    hLeft hRight
                    (Metatheory.Derives.equality_refl
                      (mem_codeₘ(
                        (quote_term left : SetOpenTerm []),
                        (quote_term right : SetOpenTerm [])) :
                        SetOpenTerm []))
                  have hResult := formula_code_at_of_condition_branch
                    (numₘ(depth))
                    (mem_codeₘ(
                      (quote_term left : SetOpenTerm []),
                      (quote_term right : SetOpenTerm [])) :
                      SetOpenTerm [])
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
                    rw [quote_relation_membership_eq
                      relation arguments hKind]
                    apply quote_membership_arguments_cons_eq
                      relation arguments hKind left right
                    exact hTypedArguments
                  rw [hQuote]
                  exact hResult
  | predicate =>
      have hArguments := quote_arguments_term_list_code_at_of_depth
        arguments depth hBound
      have hArgumentsCode := term_list_code_at_code_mem_of_derives
        (numₘ(depth))
        (numₘ(σ.relArity relation))
        (quote_arguments arguments : SetOpenTerm [])
        (by simpa [Signature.relArity] using hArguments)
      have hCode :=
        structural_node_code_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) StructuralCodeTag.predicate
          [numₘ(σ.relArity relation),
            numₘ(QuotationNumbering.relation_number relation),
            (quote_arguments arguments : SetOpenTerm [])] (by
            intro field hField
            simp only [List.mem_cons, List.not_mem_nil] at hField
            rcases hField with hField | hField
            · simpa [hField] using
                (finite_numeral_mem_formal_language_encoding_theory
                  (Γ := ([] : Context signature [])) (σ.relArity relation))
            · rcases hField with hField | hField
              · simpa [hField] using
                  (finite_numeral_mem_formal_language_encoding_theory
                    (Γ := ([] : Context signature []))
                    (QuotationNumbering.relation_number relation))
              · rcases hField with hField | hField
                · simpa [hField] using hArgumentsCode
                · contradiction)
      have hBranch := formula_code_predicate_condition_intro
        (numₘ(depth))
        (pred_codeₘ(
          numₘ(σ.relArity relation),
          numₘ(QuotationNumbering.relation_number relation),
          (quote_arguments arguments : SetOpenTerm [])) :
          SetOpenTerm [])
        (numₘ(σ.relArity relation))
        (numₘ(QuotationNumbering.relation_number relation))
        (quote_arguments arguments : SetOpenTerm [])
        (finite_numeral_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) (σ.relArity relation))
        (finite_numeral_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature []))
          (QuotationNumbering.relation_number relation))
        (by simpa [Signature.relArity] using hArguments)
        (Metatheory.Derives.equality_refl
          (pred_codeₘ(
            numₘ(σ.relArity relation),
            numₘ(QuotationNumbering.relation_number relation),
            (quote_arguments arguments : SetOpenTerm [])) :
            SetOpenTerm []))
      have hResult := formula_code_at_of_condition_branch
        (numₘ(depth))
        (pred_codeₘ(
          numₘ(σ.relArity relation),
          numₘ(QuotationNumbering.relation_number relation),
          (quote_arguments arguments : SetOpenTerm [])) :
          SetOpenTerm [])
        hDepth
        (by
          simpa [structural_node_code_term, structural_list_code_term] using!
            hCode)
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_left hBranch)))
      rw [quote_relation_predicate_eq relation arguments hKind]
      exact hResult

private theorem quote_relation_formula_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (relation : σ.RelSymbol)
    (arguments : Arguments σ bound free (σ.relDomain relation)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(
        numₘ(bound.length),
        (quote_relation relation arguments : SetOpenTerm [])) := by
  have hDepth := finite_numeral_mem_formal_language_encoding_theory
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
                  have hLeft := quote_term_code_at left
                  have hRight := quote_term_code_at right
                  have hLeftCode := term_code_at_code_mem_of_derives
                    (numₘ(bound.length))
                    (quote_term left : SetOpenTerm []) hLeft
                  have hRightCode := term_code_at_code_mem_of_derives
                    (numₘ(bound.length))
                    (quote_term right : SetOpenTerm []) hRight
                  have hCode :=
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
                  have hBranch := formula_code_binary_atomic_condition_intro
                    StructuralCodeTag.membership
                    (numₘ(bound.length))
                    (mem_codeₘ(
                      (quote_term left : SetOpenTerm []),
                      (quote_term right : SetOpenTerm [])) :
                      SetOpenTerm [])
                    (quote_term left : SetOpenTerm [])
                    (quote_term right : SetOpenTerm [])
                    hLeft hRight
                    (Metatheory.Derives.equality_refl
                      (mem_codeₘ(
                        (quote_term left : SetOpenTerm []),
                        (quote_term right : SetOpenTerm [])) :
                        SetOpenTerm []))
                  have hResult := formula_code_at_of_condition_branch
                    (numₘ(bound.length))
                    (mem_codeₘ(
                      (quote_term left : SetOpenTerm []),
                      (quote_term right : SetOpenTerm [])) :
                      SetOpenTerm [])
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
                    rw [quote_relation_membership_eq
                      relation arguments hKind]
                    apply quote_membership_arguments_cons_eq
                      relation arguments hKind left right
                    exact hTypedArguments
                  rw [hQuote]
                  exact hResult
  | predicate =>
      have hArguments := quote_arguments_term_list_code_at arguments
      have hArgumentsCode := term_list_code_at_code_mem_of_derives
        (numₘ(bound.length))
        (numₘ(σ.relArity relation))
        (quote_arguments arguments : SetOpenTerm [])
        (by simpa [Signature.relArity] using hArguments)
      have hCode :=
        structural_node_code_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) StructuralCodeTag.predicate
          [numₘ(σ.relArity relation),
            numₘ(QuotationNumbering.relation_number relation),
            (quote_arguments arguments : SetOpenTerm [])] (by
            intro field hField
            simp only [List.mem_cons, List.not_mem_nil] at hField
            rcases hField with hField | hField
            · simpa [hField] using
                (finite_numeral_mem_formal_language_encoding_theory
                  (Γ := ([] : Context signature [])) (σ.relArity relation))
            · rcases hField with hField | hField
              · simpa [hField] using
                  (finite_numeral_mem_formal_language_encoding_theory
                    (Γ := ([] : Context signature []))
                    (QuotationNumbering.relation_number relation))
              · rcases hField with hField | hField
                · simpa [hField] using hArgumentsCode
                · contradiction)
      have hBranch := formula_code_predicate_condition_intro
        (numₘ(bound.length))
        (pred_codeₘ(
          numₘ(σ.relArity relation),
          numₘ(QuotationNumbering.relation_number relation),
          (quote_arguments arguments : SetOpenTerm [])) :
          SetOpenTerm [])
        (numₘ(σ.relArity relation))
        (numₘ(QuotationNumbering.relation_number relation))
        (quote_arguments arguments : SetOpenTerm [])
        (finite_numeral_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) (σ.relArity relation))
        (finite_numeral_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature []))
          (QuotationNumbering.relation_number relation))
        (by simpa [Signature.relArity] using hArguments)
        (Metatheory.Derives.equality_refl
          (pred_codeₘ(
            numₘ(σ.relArity relation),
            numₘ(QuotationNumbering.relation_number relation),
            (quote_arguments arguments : SetOpenTerm [])) :
            SetOpenTerm []))
      have hResult := formula_code_at_of_condition_branch
        (numₘ(bound.length))
        (pred_codeₘ(
          numₘ(σ.relArity relation),
          numₘ(QuotationNumbering.relation_number relation),
          (quote_arguments arguments : SetOpenTerm [])) :
          SetOpenTerm [])
        hDepth
        (by
          simpa [structural_node_code_term, structural_list_code_term] using!
            hCode)
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_left hBranch)))
      rw [quote_relation_predicate_eq relation arguments hKind]
      exact hResult
/-! ## 外部深度提升 -/

/-- 类型化 Hilbert 公式在不小于其 bound 上下文长度的任意外部深度下都满足公式码递归谓词。 -/
theorem quote_hilbert_formula_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) (depth : Nat)
    (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(
        numₘ(depth),
        (quote_hilbert formula : SetOpenTerm [])) := by
  exact (Formula.rec
    (motive := fun (currentBound currentFree : SortContext σ)
        (currentFormula : Formula σ currentBound currentFree) =>
      ∀ depth, currentBound.length ≤ depth →
        ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
          formula_code_atₘ(
            numₘ(depth),
            (quote_hilbert currentFormula : SetOpenTerm [])))
    (fun {bound free} => by
      intro depth hBound
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hSuccessor := successor_mem_omega_formal_language_encoding_theory
        (numₘ(depth) : SetOpenTerm []) hDepth
      have hVar := quote_term_code_at_of_depth
        (σ := σ)
        (bound := QuotationNumbering.objectSort :: bound)
        (free := free) (sort := QuotationNumbering.objectSort)
        (.bvar (.here)) (depth + 1) (by
          simp
          omega)
      have hVar' :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            term_code_atₘ(
              Sₘ(numₘ(depth)),
              (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])) := by
        simpa [quote_term, finite_numeral_term] using! hVar
      have hEq := formula_code_at_of_equality
        (Sₘ(numₘ(depth)))
        (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])
        (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])
        hSuccessor hVar' hVar'
      have hAll := formula_code_at_of_universal
        (numₘ(depth))
        (eq_codeₘ(
          (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []),
          (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])) :
          SetOpenTerm [])
        hDepth
        (by
          simpa [structural_node_code_term, structural_list_code_term] using! hEq)
      have hNeg := formula_code_at_of_negation
        (numₘ(depth))
        (all_codeₘ(
          eq_codeₘ(
            (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []),
            (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []))) :
          SetOpenTerm [])
        hDepth hAll
      simpa [quote_hilbert] using hNeg)
    (fun {bound free} => by
      intro depth hBound
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hSuccessor := successor_mem_omega_formal_language_encoding_theory
        (numₘ(depth) : SetOpenTerm []) hDepth
      have hVar := quote_term_code_at_of_depth
        (σ := σ)
        (bound := QuotationNumbering.objectSort :: bound)
        (free := free) (sort := QuotationNumbering.objectSort)
        (.bvar (.here)) (depth + 1) (by
          simp
          omega)
      have hVar' :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            term_code_atₘ(
              Sₘ(numₘ(depth)),
              (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])) := by
        simpa [quote_term, finite_numeral_term] using! hVar
      have hEq := formula_code_at_of_equality
        (Sₘ(numₘ(depth)))
        (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])
        (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])
        hSuccessor hVar' hVar'
      have hAll := formula_code_at_of_universal
        (numₘ(depth))
        (eq_codeₘ(
          (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []),
          (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])) :
          SetOpenTerm [])
        hDepth
        (by
          simpa [structural_node_code_term, structural_list_code_term] using! hEq)
      simpa [quote_hilbert] using hAll)
    (fun {bound free} relation arguments => by
      intro depth hBound
      simpa [quote_hilbert] using
        (quote_relation_formula_code_at_of_depth
          relation arguments depth hBound))
    (fun {bound free} {sort} left right => by
      intro depth hBound
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hLeft := quote_term_code_at_of_depth left depth hBound
      have hRight := quote_term_code_at_of_depth right depth hBound
      have hResult := formula_code_at_of_equality
        (numₘ(depth))
        (quote_term left : SetOpenTerm [])
        (quote_term right : SetOpenTerm [])
        hDepth hLeft hRight
      simpa [quote_hilbert] using hResult)
    (fun {bound free} body ih => by
      intro depth hBound
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hResult := formula_code_at_of_negation
        (numₘ(depth))
        (quote_hilbert body : SetOpenTerm []) hDepth
        (ih depth hBound)
      simpa [quote_hilbert] using hResult)
    (fun {bound free} left right ihLeft ihRight => by
      intro depth hBound
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hRightNeg := formula_code_at_of_negation
        (numₘ(depth))
        (quote_hilbert right : SetOpenTerm []) hDepth
        (ihRight depth hBound)
      have hImp := formula_code_at_of_implication
        (numₘ(depth))
        (quote_hilbert left : SetOpenTerm [])
        (neg_codeₘ(quote_hilbert right) : SetOpenTerm [])
        hDepth (ihLeft depth hBound) hRightNeg
      have hNeg := formula_code_at_of_negation
        (numₘ(depth))
        (imp_codeₘ(
          (quote_hilbert left : SetOpenTerm []),
          neg_codeₘ(quote_hilbert right)) : SetOpenTerm [])
        hDepth hImp
      simpa [quote_hilbert] using hNeg)
    (fun {bound free} left right ihLeft ihRight => by
      intro depth hBound
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hLeftNeg := formula_code_at_of_negation
        (numₘ(depth))
        (quote_hilbert left : SetOpenTerm []) hDepth
        (ihLeft depth hBound)
      have hImp := formula_code_at_of_implication
        (numₘ(depth))
        (neg_codeₘ(quote_hilbert left) : SetOpenTerm [])
        (quote_hilbert right : SetOpenTerm [])
        hDepth hLeftNeg (ihRight depth hBound)
      simpa [quote_hilbert] using hImp)
    (fun {bound free} left right ihLeft ihRight => by
      intro depth hBound
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hResult := formula_code_at_of_implication
        (numₘ(depth))
        (quote_hilbert left : SetOpenTerm [])
        (quote_hilbert right : SetOpenTerm [])
        hDepth (ihLeft depth hBound) (ihRight depth hBound)
      simpa [quote_hilbert] using hResult)
    (fun {bound free} left right ihLeft ihRight => by
      intro depth hBound
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hLeftRight := formula_code_at_of_implication
        (numₘ(depth))
        (quote_hilbert left : SetOpenTerm [])
        (quote_hilbert right : SetOpenTerm [])
        hDepth (ihLeft depth hBound) (ihRight depth hBound)
      have hRightLeft := formula_code_at_of_implication
        (numₘ(depth))
        (quote_hilbert right : SetOpenTerm [])
        (quote_hilbert left : SetOpenTerm [])
        hDepth (ihRight depth hBound) (ihLeft depth hBound)
      have hRightLeftNeg := formula_code_at_of_negation
        (numₘ(depth))
        (imp_codeₘ(
          (quote_hilbert right : SetOpenTerm []),
          (quote_hilbert left : SetOpenTerm [])) : SetOpenTerm [])
        hDepth hRightLeft
      have hOuterImp := formula_code_at_of_implication
        (numₘ(depth))
        (imp_codeₘ(
          (quote_hilbert left : SetOpenTerm []),
          (quote_hilbert right : SetOpenTerm [])) : SetOpenTerm [])
        (neg_codeₘ(
          imp_codeₘ(
            (quote_hilbert right : SetOpenTerm []),
            (quote_hilbert left : SetOpenTerm []))) : SetOpenTerm [])
        hDepth hLeftRight hRightLeftNeg
      have hResult := formula_code_at_of_negation
        (numₘ(depth))
        (imp_codeₘ(
          imp_codeₘ(
            (quote_hilbert left : SetOpenTerm []),
            (quote_hilbert right : SetOpenTerm [])),
          neg_codeₘ(
            imp_codeₘ(
              (quote_hilbert right : SetOpenTerm []),
              (quote_hilbert left : SetOpenTerm [])))) : SetOpenTerm [])
        hDepth hOuterImp
      simpa [quote_hilbert] using hResult)
    (fun {bound free} sort body ih => by
      intro depth hBound
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hBodyBound : (sort :: bound).length ≤ depth + 1 := by
        simp
        omega
      have hBody :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            formula_code_atₘ(
              Sₘ(numₘ(depth)),
              (quote_hilbert body : SetOpenTerm [])) := by
        simpa [finite_numeral_term] using ih (depth + 1) hBodyBound
      have hResult := formula_code_at_of_universal
        (numₘ(depth))
        (quote_hilbert body : SetOpenTerm []) hDepth hBody
      simpa [quote_hilbert] using hResult)
    (fun {bound free} sort body ih => by
      intro depth hBound
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hSuccessor := successor_mem_omega_formal_language_encoding_theory
        (numₘ(depth) : SetOpenTerm []) hDepth
      have hBodyBound : (sort :: bound).length ≤ depth + 1 := by
        simp
        omega
      have hBody :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            formula_code_atₘ(
              Sₘ(numₘ(depth)),
              (quote_hilbert body : SetOpenTerm [])) := by
        simpa [finite_numeral_term] using ih (depth + 1) hBodyBound
      have hBodyNeg := formula_code_at_of_negation
        (Sₘ(numₘ(depth)))
        (quote_hilbert body : SetOpenTerm []) hSuccessor hBody
      have hAll := formula_code_at_of_universal
        (numₘ(depth))
        (neg_codeₘ(quote_hilbert body) : SetOpenTerm [])
        hDepth hBodyNeg
      have hResult := formula_code_at_of_negation
        (numₘ(depth))
        (all_codeₘ(neg_codeₘ(quote_hilbert body)) : SetOpenTerm [])
        hDepth hAll
      simpa [quote_hilbert] using hResult)
    formula) depth hBound

theorem quote_formula_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) (depth : Nat)
    (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(
        numₘ(depth),
        (quote formula : SetOpenTerm [])) := by
  simpa [quote] using
    (quote_hilbert_formula_code_at_of_depth
      (σ := σ) (bound := bound) (free := free)
      (Formula.hilbertize QuotationNumbering.objectSort formula)
      depth hBound)

theorem quote_hilbert_formula_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(
        numₘ(bound.length),
        (quote_hilbert formula : SetOpenTerm [])) := by
  refine Formula.rec
    (motive := fun bound free formula =>
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(
          numₘ(bound.length),
          (quote_hilbert formula : SetOpenTerm [])))
    (fun {bound free} => by
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) bound.length
      have hSuccessor := successor_mem_omega_formal_language_encoding_theory
        (numₘ(bound.length) : SetOpenTerm []) hDepth
      have hVar := quote_bound_variable_term_code_at
        (bound := QuotationNumbering.objectSort :: bound)
        (free := free) (sort := QuotationNumbering.objectSort) (.here)
      have hVar' :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            term_code_atₘ(
              Sₘ(numₘ(bound.length)),
              (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])) := by
        simpa [quote_term, finite_numeral_term] using! hVar
      have hEq := formula_code_at_of_equality
        (Sₘ(numₘ(bound.length)))
        (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])
        (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])
        hSuccessor hVar' hVar'
      have hAll := formula_code_at_of_universal
        (numₘ(bound.length))
        (eq_codeₘ(
          (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []),
          (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])) :
          SetOpenTerm [])
        hDepth
        (by
          simpa [structural_node_code_term, structural_list_code_term] using! hEq)
      have hNeg := formula_code_at_of_negation
        (numₘ(bound.length))
        (all_codeₘ(
          eq_codeₘ(
            (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []),
            (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []))) :
          SetOpenTerm [])
        hDepth hAll
      simpa [quote_hilbert] using hNeg)
    (fun {bound free} => by
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) bound.length
      have hSuccessor := successor_mem_omega_formal_language_encoding_theory
        (numₘ(bound.length) : SetOpenTerm []) hDepth
      have hVar := quote_bound_variable_term_code_at
        (bound := QuotationNumbering.objectSort :: bound)
        (free := free) (sort := QuotationNumbering.objectSort) (.here)
      have hVar' :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            term_code_atₘ(
              Sₘ(numₘ(bound.length)),
              (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])) := by
        simpa [quote_term, finite_numeral_term] using! hVar
      have hEq := formula_code_at_of_equality
        (Sₘ(numₘ(bound.length)))
        (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])
        (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])
        hSuccessor hVar' hVar'
      have hAll := formula_code_at_of_universal
        (numₘ(bound.length))
        (eq_codeₘ(
          (bound_var_codeₘ(numₘ(0)) : SetOpenTerm []),
          (bound_var_codeₘ(numₘ(0)) : SetOpenTerm [])) :
          SetOpenTerm [])
        hDepth
        (by
          simpa [structural_node_code_term, structural_list_code_term] using! hEq)
      simpa [quote_hilbert] using hAll)
    (fun {bound free} relation arguments => by
      simpa [quote_hilbert] using
        (quote_relation_formula_code_at relation arguments))
    (fun {bound free} {sort} left right => by
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) bound.length
      have hLeft := quote_term_code_at left
      have hRight := quote_term_code_at right
      have hResult := formula_code_at_of_equality
        (numₘ(bound.length))
        (quote_term left : SetOpenTerm [])
        (quote_term right : SetOpenTerm [])
        hDepth hLeft hRight
      simpa [quote_hilbert] using hResult)
    (fun {bound free} body ih => by
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) bound.length
      have hResult := formula_code_at_of_negation
        (numₘ(bound.length))
        (quote_hilbert body : SetOpenTerm []) hDepth ih
      simpa [quote_hilbert] using hResult)
    (fun {bound free} left right ihLeft ihRight => by
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) bound.length
      have hRightNeg := formula_code_at_of_negation
        (numₘ(bound.length))
        (quote_hilbert right : SetOpenTerm []) hDepth ihRight
      have hImp := formula_code_at_of_implication
        (numₘ(bound.length))
        (quote_hilbert left : SetOpenTerm [])
        (neg_codeₘ(quote_hilbert right) : SetOpenTerm [])
        hDepth ihLeft hRightNeg
      have hNeg := formula_code_at_of_negation
        (numₘ(bound.length))
        (imp_codeₘ(
          (quote_hilbert left : SetOpenTerm []),
          neg_codeₘ(quote_hilbert right)) : SetOpenTerm [])
        hDepth hImp
      simpa [quote_hilbert] using hNeg)
    (fun {bound free} left right ihLeft ihRight => by
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) bound.length
      have hLeftNeg := formula_code_at_of_negation
        (numₘ(bound.length))
        (quote_hilbert left : SetOpenTerm []) hDepth ihLeft
      have hImp := formula_code_at_of_implication
        (numₘ(bound.length))
        (neg_codeₘ(quote_hilbert left) : SetOpenTerm [])
        (quote_hilbert right : SetOpenTerm [])
        hDepth hLeftNeg ihRight
      simpa [quote_hilbert] using hImp)
    (fun {bound free} left right ihLeft ihRight => by
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) bound.length
      have hResult := formula_code_at_of_implication
        (numₘ(bound.length))
        (quote_hilbert left : SetOpenTerm [])
        (quote_hilbert right : SetOpenTerm [])
        hDepth ihLeft ihRight
      simpa [quote_hilbert] using hResult)
    (fun {bound free} left right ihLeft ihRight => by
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) bound.length
      have hLeftRight := formula_code_at_of_implication
        (numₘ(bound.length))
        (quote_hilbert left : SetOpenTerm [])
        (quote_hilbert right : SetOpenTerm [])
        hDepth ihLeft ihRight
      have hRightLeft := formula_code_at_of_implication
        (numₘ(bound.length))
        (quote_hilbert right : SetOpenTerm [])
        (quote_hilbert left : SetOpenTerm [])
        hDepth ihRight ihLeft
      have hRightLeftNeg := formula_code_at_of_negation
        (numₘ(bound.length))
        (imp_codeₘ(
          (quote_hilbert right : SetOpenTerm []),
          (quote_hilbert left : SetOpenTerm [])) : SetOpenTerm [])
        hDepth hRightLeft
      have hOuterImp := formula_code_at_of_implication
        (numₘ(bound.length))
        (imp_codeₘ(
          (quote_hilbert left : SetOpenTerm []),
          (quote_hilbert right : SetOpenTerm [])) : SetOpenTerm [])
        (neg_codeₘ(
          imp_codeₘ(
            (quote_hilbert right : SetOpenTerm []),
            (quote_hilbert left : SetOpenTerm []))) : SetOpenTerm [])
        hDepth hLeftRight hRightLeftNeg
      have hResult := formula_code_at_of_negation
        (numₘ(bound.length))
        (imp_codeₘ(
          imp_codeₘ(
            (quote_hilbert left : SetOpenTerm []),
            (quote_hilbert right : SetOpenTerm [])),
          neg_codeₘ(
            imp_codeₘ(
              (quote_hilbert right : SetOpenTerm []),
              (quote_hilbert left : SetOpenTerm [])))) :
          SetOpenTerm [])
        hDepth hOuterImp
      simpa [quote_hilbert] using hResult)
    (fun {bound free} sort body ih => by
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) bound.length
      have hBody :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            formula_code_atₘ(
              Sₘ(numₘ(bound.length)),
              (quote_hilbert body : SetOpenTerm [])) := by
        simpa [finite_numeral_term] using ih
      have hResult := formula_code_at_of_universal
        (numₘ(bound.length))
        (quote_hilbert body : SetOpenTerm []) hDepth hBody
      simpa [quote_hilbert] using hResult)
    (fun {bound free} sort body ih => by
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) bound.length
      have hSuccessor := successor_mem_omega_formal_language_encoding_theory
        (numₘ(bound.length) : SetOpenTerm []) hDepth
      have hBody :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            formula_code_atₘ(
              Sₘ(numₘ(bound.length)),
              (quote_hilbert body : SetOpenTerm [])) := by
        simpa [finite_numeral_term] using ih
      have hBodyNeg := formula_code_at_of_negation
        (Sₘ(numₘ(bound.length)))
        (quote_hilbert body : SetOpenTerm []) hSuccessor hBody
      have hAll := formula_code_at_of_universal
        (numₘ(bound.length))
        (neg_codeₘ(quote_hilbert body) : SetOpenTerm [])
        hDepth hBodyNeg
      have hResult := formula_code_at_of_negation
        (numₘ(bound.length))
        (all_codeₘ(neg_codeₘ(quote_hilbert body)) : SetOpenTerm [])
        hDepth hAll
      simpa [quote_hilbert] using hResult)
    formula

theorem quote_formula_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(
        numₘ(bound.length),
        (quote formula : SetOpenTerm [])) := by
  simpa [quote] using
    (quote_hilbert_formula_code_at
      (σ := σ) (bound := bound) (free := free)
      (Formula.hilbertize QuotationNumbering.objectSort formula))

end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
