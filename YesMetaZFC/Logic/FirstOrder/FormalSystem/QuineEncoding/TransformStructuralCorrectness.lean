import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaStructuralCorrectness

/-!
# 统一语法变换的结构正确性公共内核

本模块只包含与具体语法变换操作无关的组合器及有限自由槽替换快路径。
具体的 `abstractFreeTop`、`openBound` 等递归实现只消费这些接口，不再形成反向依赖。
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

/-- 由码域、scope 与构造形状组合统一语法变换关系。 -/
theorem syntax_transform_intro
    (kind : SyntaxCodeKind) (operation : SyntaxTransformOperation)
    (depth variableIndex : Nat)
    (replacement source target : SetOpenTerm [])
    (hSourceMem : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      source ∈ₘ ωₘ)
    (hTargetMem : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      target ∈ₘ ωₘ)
    (hReplacementMem : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      replacement ∈ₘ ωₘ)
    (hScope : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term kind)
        (syntax_transform_operation_term operation)
        (numₘ(depth)) (numₘ(variableIndex)) replacement
        source target)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term kind)
        (syntax_transform_operation_term operation)
        (numₘ(depth)) (numₘ(variableIndex)) replacement
        source target) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term kind,
        syntax_transform_operation_term operation,
        numₘ(depth), numₘ(variableIndex), replacement,
        source, target) := by
  apply FirstOrder.Derives.iff_elim_right
    (syntax_transform_definition_instance_derives
      (Γ := ([] : Context signature []))
      (syntax_code_kind_term kind)
      (syntax_transform_operation_term operation)
      (numₘ(depth)) (numₘ(variableIndex)) replacement
      source target)
  have hGlobal := FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro
        (finite_numeral_mem_expression (Γ := [])
          (syntax_code_kind kind))
        (finite_numeral_mem_expression (Γ := [])
          (syntax_transform_operation operation)))
      (FirstOrder.Derives.conj_intro
        (finite_numeral_mem_expression (Γ := []) depth)
        (finite_numeral_mem_expression (Γ := []) variableIndex)))
    (FirstOrder.Derives.conj_intro
      hReplacementMem
      (FirstOrder.Derives.conj_intro hSourceMem hTargetMem))
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro hGlobal hScope) hShape

private theorem two_free_substitution_map_beta
    (first second : SetOpenTerm []) :
    ((fun {_sort} entry =>
      Term.substituteMapped VariableSubstitution.boundId
        (VariableSubstitution.instantiateFreeTop first)
        (VariableSubstitution.liftFree SetSort.set
          (VariableSubstitution.instantiateFreeTop second) entry)) :
      VariableSubstitution signature [SetSort.set, SetSort.set] [] []) =
      (VariableSubstitution.cons first
        (VariableSubstitution.cons second
          (VariableSubstitution.empty :
            VariableSubstitution signature [] [] [])) :
        VariableSubstitution signature
          [SetSort.set, SetSort.set] [] []) := by
  funext resultSort entry
  cases entry with
  | here => rfl
  | there previous =>
      cases previous with
      | here =>
          simpa [Term.weakenFree, Term.rename, Renaming.weakenFree,
            Renaming.free, Term.renameMapped] using!
            (Term.substituteMapped_weakenFree_instantiateFreeTop
              (σ := signature) SetSort.set first second)
      | there impossible => cases impossible

private theorem three_free_substitution_map_beta
    (first second third : SetOpenTerm []) :
    ((fun {_sort} entry =>
      Term.substituteMapped VariableSubstitution.boundId
        (fun {_sort} entry =>
          Term.substituteMapped VariableSubstitution.boundId
            (VariableSubstitution.instantiateFreeTop first)
            (VariableSubstitution.liftFree SetSort.set
              (VariableSubstitution.instantiateFreeTop second) entry))
        (VariableSubstitution.liftFree SetSort.set
          (VariableSubstitution.liftFree SetSort.set
            (VariableSubstitution.instantiateFreeTop third)) entry)) :
      VariableSubstitution signature
        [SetSort.set, SetSort.set, SetSort.set] [] []) =
      (VariableSubstitution.cons first
        (VariableSubstitution.cons second
          (VariableSubstitution.cons third
            (VariableSubstitution.empty :
              VariableSubstitution signature [] [] []))) :
        VariableSubstitution signature
          [SetSort.set, SetSort.set, SetSort.set] [] []) := by
  funext resultSort entry
  cases entry with
  | here => rfl
  | there firstRest =>
      cases firstRest with
      | here =>
          simpa [Term.weakenFree, Term.rename, Renaming.weakenFree,
            Renaming.free, Term.renameMapped] using!
            (Term.substituteMapped_weakenFree_instantiateFreeTop
              (σ := signature) SetSort.set first second)
      | there secondRest =>
          cases secondRest with
          | here =>
              simp [VariableSubstitution.liftFree,
                VariableSubstitution.instantiateFreeTop,
                Term.weakenFree, Term.rename, Renaming.weakenFree,
                Renaming.free]
              let ρ : VariableSubstitution signature
                  [SetSort.set, SetSort.set] [] [] :=
                fun {sort} entry =>
                  Term.substituteMapped VariableSubstitution.boundId
                    (VariableSubstitution.instantiateFreeTop first)
                    (VariableSubstitution.liftFree SetSort.set
                      (VariableSubstitution.instantiateFreeTop second) entry)
              change
                Term.substituteMapped VariableSubstitution.boundId ρ
                    (Term.renameMapped
                      (VariableRenaming.comp
                        (outer := (@VariableRenaming.id signature.SortSymbol []))
                        (inner := (@VariableRenaming.id signature.SortSymbol [])))
                      (VariableRenaming.comp
                        (outer := VariableRenaming.weaken SetSort.set)
                        (inner := VariableRenaming.weaken SetSort.set))
                      third) = third
              rw [two_free_substitution_map_beta first second]
              have hBound :
                  (VariableRenaming.comp
                    (outer := (@VariableRenaming.id signature.SortSymbol []))
                    (inner := (@VariableRenaming.id signature.SortSymbol [])) :
                      VariableRenaming (S := signature.SortSymbol) [] []) =
                    (@VariableRenaming.id signature.SortSymbol []) := by
                funext resultSort entry
                cases entry
              rw [hBound, Term.renameMapped_two_weakenFree]
              exact gq_closed_two_weaken_substitute _ third
          | there impossible => cases impossible

/-- 连续实例化四个自由槽等于一次四槽替换。 -/
theorem four_free_substitution_beta
    {body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set]}
    (first second third fourth : SetOpenTerm []) :
    Formula.instantiateFreeTop first
      (Formula.substituteFree
        (VariableSubstitution.liftFree SetSort.set
          (VariableSubstitution.instantiateFreeTop second))
        (Formula.substituteFree
          (VariableSubstitution.liftFree SetSort.set
            (VariableSubstitution.liftFree SetSort.set
              (VariableSubstitution.instantiateFreeTop third)))
          (Formula.substituteFree
            (VariableSubstitution.liftFree SetSort.set
              (VariableSubstitution.liftFree SetSort.set
                (VariableSubstitution.liftFree SetSort.set
                  (VariableSubstitution.instantiateFreeTop fourth))))
            body))) =
      Formula.substituteFree
        (VariableSubstitution.cons first
          (VariableSubstitution.cons second
            (VariableSubstitution.cons third
              (VariableSubstitution.cons fourth
                VariableSubstitution.empty)))) body := by
  change
    Formula.substitute (Substitution.instantiateFreeTop first)
      (Formula.substitute
        (Substitution.free_map
          (VariableSubstitution.liftFree SetSort.set
            (VariableSubstitution.instantiateFreeTop second)))
        (Formula.substitute
          (Substitution.free_map
            (VariableSubstitution.liftFree SetSort.set
              (VariableSubstitution.liftFree SetSort.set
                (VariableSubstitution.instantiateFreeTop third))))
          (Formula.substitute
            (Substitution.free_map
              (VariableSubstitution.liftFree SetSort.set
                (VariableSubstitution.liftFree SetSort.set
                  (VariableSubstitution.liftFree SetSort.set
                    (VariableSubstitution.instantiateFreeTop fourth)))))
            body))) = _
  rw [Formula.substitute_comp, Formula.substitute_comp,
    Formula.substitute_comp]
  simp only [Substitution.comp, Substitution.instantiateFreeTop,
    Substitution.free_map]
  congr 1
  change Substitution.map _ _ = Substitution.map _ _
  congr
  funext resultSort entry
  cases resultSort
  cases entry with
  | here =>
      simp [VariableSubstitution.cons,
        VariableSubstitution.liftFree,
        VariableSubstitution.instantiateFreeTop,
        VariableSubstitution.boundId,
        Term.substituteMapped,
        Term.weakenFree, Term.rename, Renaming.weakenFree,
        Renaming.free]
  | there firstRest =>
      cases firstRest with
      | here =>
          simpa [Term.weakenFree, Term.rename, Renaming.weakenFree,
            Renaming.free, Term.renameMapped] using!
            (Term.substituteMapped_weakenFree_instantiateFreeTop
              (σ := signature) SetSort.set first second)
      | there secondRest =>
          cases secondRest with
          | here =>
              simp [ VariableSubstitution.cons,
                VariableSubstitution.liftFree,
                VariableSubstitution.instantiateFreeTop,
                VariableSubstitution.boundId, Term.substituteMapped,
                Term.weakenFree, Term.rename, Renaming.weakenFree,
                Renaming.free, Term.renameMapped,
                VariableRenaming.weaken]
              let ρ : VariableSubstitution signature
                  [SetSort.set, SetSort.set] [] [] :=
                fun {sort} entry =>
                  Term.substituteMapped VariableSubstitution.boundId
                    (VariableSubstitution.instantiateFreeTop first)
                    (VariableSubstitution.liftFree SetSort.set
                      (VariableSubstitution.instantiateFreeTop second) entry)
              change
                Term.substituteMapped VariableSubstitution.boundId ρ
                    (Term.renameMapped
                      (VariableRenaming.comp
                        (outer := (@VariableRenaming.id signature.SortSymbol []))
                        (inner := (@VariableRenaming.id signature.SortSymbol [])))
                      (VariableRenaming.comp
                        (outer := VariableRenaming.weaken SetSort.set)
                        (inner := VariableRenaming.weaken SetSort.set))
                      third) = third
              rw [two_free_substitution_map_beta first second]
              have hBound :
                  (VariableRenaming.comp
                    (outer := (@VariableRenaming.id signature.SortSymbol []))
                    (inner := (@VariableRenaming.id signature.SortSymbol [])) :
                      VariableRenaming (S := signature.SortSymbol) [] []) =
                    (@VariableRenaming.id signature.SortSymbol []) := by
                funext resultSort entry
                cases entry
              rw [hBound, Term.renameMapped_two_weakenFree]
              exact gq_closed_two_weaken_substitute _ third
          | there thirdRest =>
              cases thirdRest with
              | here =>
                  simp [VariableSubstitution.cons,
                    VariableSubstitution.liftFree,
                    VariableSubstitution.instantiateFreeTop,
                    VariableSubstitution.boundId,
                    Term.substituteMapped,
                    Term.weakenFree, Term.rename, Renaming.weakenFree,
                    Renaming.free]
                  let ρ : VariableSubstitution signature
                      [SetSort.set, SetSort.set, SetSort.set] [] [] :=
                    fun {sort} entry =>
                      Term.substituteMapped VariableSubstitution.boundId
                        (fun {sort} entry =>
                          Term.substituteMapped
                            VariableSubstitution.boundId
                            (VariableSubstitution.instantiateFreeTop first)
                            (VariableSubstitution.liftFree SetSort.set
                              (VariableSubstitution.instantiateFreeTop second)
                              entry))
                        (VariableSubstitution.liftFree SetSort.set
                          (VariableSubstitution.liftFree SetSort.set
                            (VariableSubstitution.instantiateFreeTop third))
                          entry)
                  change
                    Term.substituteMapped VariableSubstitution.boundId ρ
                        (Term.renameMapped
                          (VariableRenaming.comp
                            (outer :=
                              (@VariableRenaming.id signature.SortSymbol []))
                            (inner := VariableRenaming.comp
                              (outer :=
                                (@VariableRenaming.id signature.SortSymbol []))
                              (inner :=
                                (@VariableRenaming.id signature.SortSymbol []))))
                          (VariableRenaming.comp
                            (outer := VariableRenaming.weaken SetSort.set)
                            (inner := VariableRenaming.comp
                              (outer := VariableRenaming.weaken SetSort.set)
                              (inner := VariableRenaming.weaken SetSort.set)))
                          fourth) = fourth
                  rw [three_free_substitution_map_beta first second third]
                  have hBound :
                      (VariableRenaming.comp
                        (outer :=
                          (@VariableRenaming.id signature.SortSymbol []))
                        (inner := VariableRenaming.comp
                          (outer :=
                            (@VariableRenaming.id signature.SortSymbol []))
                          (inner :=
                            (@VariableRenaming.id signature.SortSymbol []))) :
                        VariableRenaming (S := signature.SortSymbol) [] []) =
                      (@VariableRenaming.id signature.SortSymbol []) := by
                    funext resultSort entry
                    cases entry
                  rw [hBound, Term.renameMapped_three_weakenFree]
                  exact gq_closed_three_weaken_substitute _ fourth
              | there impossible => cases impossible

/-- 任意四槽替换消去闭项的四层自由上下文提升。 -/
theorem gq_closed_four_weaken_substitute
    (τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set] [] [])
    {resultSort : signature.SortSymbol}
    (term : Term signature [] [] resultSort) :
    Term.substituteMapped VariableSubstitution.boundId τ
        ((((term.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
          SetSort.set).weakenFree SetSort.set) =
      term := by
  exact Term.rec
    (motive_1 := fun _ term =>
      Term.substituteMapped VariableSubstitution.boundId τ
          ((((term.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
            SetSort.set).weakenFree SetSort.set) =
        term)
    (motive_2 := fun _ arguments =>
      Arguments.substituteMapped VariableSubstitution.boundId τ
          ((((arguments.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
            SetSort.set).weakenFree SetSort.set) =
        arguments)
    (fun entry => by cases entry)
    (fun entry => by cases entry)
    (fun function arguments ih => by
      change
        Term.app function
            (Arguments.substituteMapped VariableSubstitution.boundId τ
              ((((arguments.weakenFree SetSort.set).weakenFree
                SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set)) =
          Term.app function arguments
      rw [ih])
    rfl
    (fun head tail ihHead ihTail => by
      change
        Arguments.cons
            (Term.substituteMapped VariableSubstitution.boundId τ
              ((((head.weakenFree SetSort.set).weakenFree
                SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set))
            (Arguments.substituteMapped VariableSubstitution.boundId τ
              ((((tail.weakenFree SetSort.set).weakenFree
                SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set)) =
          Arguments.cons head tail
      rw [ihHead, ihTail])
    term

end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC

