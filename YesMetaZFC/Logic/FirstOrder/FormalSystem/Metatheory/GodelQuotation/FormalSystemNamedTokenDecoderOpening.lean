import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoderShift
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CanonicalForallOpenEncoding

/-!
# 具名公式行的 canonical 全称开式

本模块只连接两个纯语法事实：具名 decoder 对最外层 binder 的解释，以及
`CanonicalForallOpenTokens` 的逐 token 图。它不涉及证明码、replay 或对象理论。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory

set_option autoImplicit false

/-- 去掉一个最外层 binder 时对具名变量名执行的规范变换。 -/
def fs_named_forall_open_name
    (eigen name : Nat) : Nat :=
  if name % 2 = 0 then
    name
  else
    match name / 2 with
    | 0 => free_name eigen
    | depth + 1 => bound_name depth

/-- 名变换逐点实现 canonical 全称开式。 -/
theorem fs_named_forall_open_name_relation
    (eigen name : Nat) :
    CanonicalForallOpenToken
      (Numbered.variable_token (free_name eigen))
      (Numbered.variable_token name)
      (Numbered.variable_token
        (fs_named_forall_open_name eigen name)) := by
  by_cases hEven : name % 2 = 0
  · have hName : free_name (name / 2) = name := by
      have hDivision := Nat.mod_add_div name 2
      simp [free_name, hEven] at hDivision ⊢
      omega
    rw [← hName]
    simpa [fs_named_forall_open_name, free_name] using
      (CanonicalForallOpenToken.free
        (variableToken :=
          Numbered.variable_token (free_name eigen))
        (name / 2))
  · have hOdd : name % 2 = 1 := by omega
    cases hQuotient : name / 2 with
    | zero =>
        have hName : name = bound_name 0 := by
          have hDivision := Nat.mod_add_div name 2
          simp [hQuotient, hOdd, bound_name] at hDivision ⊢
          omega
        have hTarget :
            fs_named_forall_open_name eigen name =
              free_name eigen := by
          simp [fs_named_forall_open_name, hEven, hQuotient]
        rw [hName] at hTarget
        rw [hName, hTarget]
        exact
          CanonicalForallOpenToken.outer
            (variableToken :=
              Numbered.variable_token (free_name eigen))
    | succ depth =>
        have hName :
            name = bound_name (depth + 1) := by
          have hDivision := Nat.mod_add_div name 2
          simp [hQuotient, hOdd, bound_name] at hDivision ⊢
          omega
        have hTarget :
            fs_named_forall_open_name eigen name =
              bound_name depth := by
          simp [fs_named_forall_open_name, hEven, hQuotient]
        rw [hName] at hTarget
        rw [hName, hTarget]
        exact
          CanonicalForallOpenToken.bound
            (variableToken :=
              Numbered.variable_token (free_name eigen))
            depth

/--
源串不含待打开的自由名时，opening 名变换是现有 binder-close 名变换的右逆。
-/
theorem fs_named_binder_close_forall_open_name
    (eigen name : Nat)
    (hFresh : name ≠ free_name eigen) :
    fs_named_binder_close_name eigen
        (fs_named_forall_open_name eigen name) =
      name := by
  by_cases hEven : name % 2 = 0
  · simp [fs_named_forall_open_name, hEven,
      fs_named_binder_close_name,
      fs_named_binder_shift_name, hFresh]
  · have hOdd : name % 2 = 1 := by omega
    cases hQuotient : name / 2 with
    | zero =>
        have hName : name = bound_name 0 := by
          have hDivision := Nat.mod_add_div name 2
          simp [hQuotient, hOdd, bound_name] at hDivision ⊢
          omega
        have hTarget :
            fs_named_forall_open_name eigen name =
              free_name eigen := by
          simp [fs_named_forall_open_name, hEven, hQuotient]
        rw [hTarget, hName]
        simp [fs_named_binder_close_name]
    | succ depth =>
        have hName :
            name = bound_name (depth + 1) := by
          have hDivision := Nat.mod_add_div name 2
          simp [hQuotient, hOdd, bound_name] at hDivision ⊢
          omega
        have hTarget :
            fs_named_forall_open_name eigen name =
              bound_name depth := by
          simp [fs_named_forall_open_name, hEven, hQuotient]
        have hTargetFresh :
            bound_name depth ≠ free_name eigen :=
          (free_name_ne_bound_name eigen depth).symm
        rw [hTarget, hName]
        simp only [fs_named_binder_close_name,
          if_neg hTargetFresh]
        simp [fs_named_binder_shift_name, bound_name]
        omega

/-- 在项树上去掉一个最外层具名 binder。 -/
def fs_named_term_token_tree_forall_open
    (eigen : Nat) : RawTermTokenTree → RawTermTokenTree
  | .atom token =>
      match fs_variable_name_decode token with
      | some name =>
          .atom (Numbered.variable_token
            (fs_named_forall_open_name eigen name))
      | none =>
          .atom token
  | .application head arguments =>
      .application head
        (arguments.map
          (fs_named_term_token_tree_forall_open eigen))

/-- 在 Hilbert 核公式树上去掉一个最外层具名 binder。 -/
def fs_named_hilbert_token_tree_forall_open
    (eigen : Nat) :
    RawHilbertTokenTree → RawHilbertTokenTree
  | .equality left right =>
      .equality
        (fs_named_term_token_tree_forall_open eigen left)
        (fs_named_term_token_tree_forall_open eigen right)
  | .membership left right =>
      .membership
        (fs_named_term_token_tree_forall_open eigen left)
        (fs_named_term_token_tree_forall_open eigen right)
  | .predicate head arguments =>
      .predicate head
        (arguments.map
          (fs_named_term_token_tree_forall_open eigen))
  | .negation body =>
      .negation
        (fs_named_hilbert_token_tree_forall_open eigen body)
  | .implication left right =>
      .implication
        (fs_named_hilbert_token_tree_forall_open eigen left)
        (fs_named_hilbert_token_tree_forall_open eigen right)
  | .universal variableToken body =>
      .universal
        (match fs_variable_name_decode variableToken with
        | some name =>
            Numbered.variable_token
              (fs_named_forall_open_name eigen name)
        | none =>
            variableToken)
        (fs_named_hilbert_token_tree_forall_open eigen body)

mutual
  private theorem
      fs_named_term_token_tree_binder_close_forall_open
      (eigen : Nat) :
      ∀ tree,
        Numbered.variable_token (free_name eigen) ∉
            tree.tokens →
          fs_named_term_token_tree_binder_close eigen
              (fs_named_term_token_tree_forall_open eigen tree) =
            tree
    | .atom token, hFresh => by
        cases hName : fs_variable_name_decode token with
        | none =>
            simp [fs_named_term_token_tree_forall_open,
              fs_named_term_token_tree_binder_close, hName]
        | some name =>
            have hToken :
                Numbered.variable_token name = token :=
              fs_variable_name_decode_value_of_some hName
            have hNameFresh :
                name ≠ free_name eigen := by
              intro hEqual
              apply hFresh
              simp [RawTermTokenTree.tokens,
                ← hToken, hEqual]
            simp [fs_named_term_token_tree_forall_open,
              fs_named_term_token_tree_binder_close,
              ← hToken, fs_variable_name_decode_encode,
              fs_named_binder_close_forall_open_name
                eigen name hNameFresh]
    | .application head arguments, hFresh => by
        have hHeadFresh :
            head ≠ Numbered.variable_token
              (free_name eigen) := by
          intro hEqual
          apply hFresh
          simp [RawTermTokenTree.tokens, hEqual]
        have hArgumentsFresh :
            Numbered.variable_token (free_name eigen) ∉
              RawTermTokenTree.list_tokens arguments := by
          intro hMember
          apply hFresh
          simp [RawTermTokenTree.tokens, hMember]
        have hArguments :=
          fs_named_term_token_trees_binder_close_forall_open
            eigen arguments hArgumentsFresh
        simp [fs_named_term_token_tree_forall_open,
          fs_named_term_token_tree_binder_close,
          fs_named_token_binder_close, hHeadFresh,
          hArguments]
  termination_by tree => sizeOf tree

  private theorem
      fs_named_term_token_trees_binder_close_forall_open
      (eigen : Nat) :
      ∀ trees,
        Numbered.variable_token (free_name eigen) ∉
            RawTermTokenTree.list_tokens trees →
          (trees.map
              (fs_named_term_token_tree_forall_open eigen)).map
              (fs_named_term_token_tree_binder_close eigen) =
            trees
    | .nil, _ =>
        rfl
    | .cons tree trees, hFresh => by
        have hHeadFresh :
            Numbered.variable_token (free_name eigen) ∉
              tree.tokens := by
          intro hMember
          apply hFresh
          simp [RawTermTokenTree.list_tokens, hMember]
        have hTailFresh :
            Numbered.variable_token (free_name eigen) ∉
              RawTermTokenTree.list_tokens trees := by
          intro hMember
          apply hFresh
          simp [RawTermTokenTree.list_tokens, hMember]
        simp [fs_named_term_token_tree_binder_close_forall_open
            eigen tree hHeadFresh,
          fs_named_term_token_trees_binder_close_forall_open
            eigen trees hTailFresh]
  termination_by trees => sizeOf trees
end

private theorem
    fs_named_hilbert_token_tree_binder_close_forall_open
    (eigen : Nat) :
    ∀ tree,
      Numbered.variable_token (free_name eigen) ∉
          tree.tokens →
        fs_named_hilbert_token_tree_binder_close eigen
            (fs_named_hilbert_token_tree_forall_open eigen tree) =
          tree
  | .equality left right, hFresh => by
      have hLeftFresh :
          Numbered.variable_token (free_name eigen) ∉
            left.tokens := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      have hRightFresh :
          Numbered.variable_token (free_name eigen) ∉
            right.tokens := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      simp [fs_named_hilbert_token_tree_forall_open,
        fs_named_hilbert_token_tree_binder_close,
        fs_named_term_token_tree_binder_close_forall_open
          eigen left hLeftFresh,
        fs_named_term_token_tree_binder_close_forall_open
          eigen right hRightFresh]
  | .membership left right, hFresh => by
      have hLeftFresh :
          Numbered.variable_token (free_name eigen) ∉
            left.tokens := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      have hRightFresh :
          Numbered.variable_token (free_name eigen) ∉
            right.tokens := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      simp [fs_named_hilbert_token_tree_forall_open,
        fs_named_hilbert_token_tree_binder_close,
        fs_named_term_token_tree_binder_close_forall_open
          eigen left hLeftFresh,
        fs_named_term_token_tree_binder_close_forall_open
          eigen right hRightFresh]
  | .predicate head arguments, hFresh => by
      have hHeadFresh :
          head ≠ Numbered.variable_token
            (free_name eigen) := by
        intro hEqual
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hEqual]
      have hArgumentsFresh :
          Numbered.variable_token (free_name eigen) ∉
            RawTermTokenTree.list_tokens arguments := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      simp [fs_named_hilbert_token_tree_forall_open,
        fs_named_hilbert_token_tree_binder_close,
        fs_named_token_binder_close, hHeadFresh,
        fs_named_term_token_trees_binder_close_forall_open
          eigen arguments hArgumentsFresh]
  | .negation body, hFresh => by
      have hBodyFresh :
          Numbered.variable_token (free_name eigen) ∉
            body.tokens := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      simp [fs_named_hilbert_token_tree_forall_open,
        fs_named_hilbert_token_tree_binder_close,
        fs_named_hilbert_token_tree_binder_close_forall_open
          eigen body hBodyFresh]
  | .implication left right, hFresh => by
      have hLeftFresh :
          Numbered.variable_token (free_name eigen) ∉
            left.tokens := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      have hRightFresh :
          Numbered.variable_token (free_name eigen) ∉
            right.tokens := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      simp [fs_named_hilbert_token_tree_forall_open,
        fs_named_hilbert_token_tree_binder_close,
        fs_named_hilbert_token_tree_binder_close_forall_open
          eigen left hLeftFresh,
        fs_named_hilbert_token_tree_binder_close_forall_open
          eigen right hRightFresh]
  | .universal variableToken body, hFresh => by
      have hVariableFresh :
          variableToken ≠ Numbered.variable_token
            (free_name eigen) := by
        intro hEqual
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hEqual]
      have hBodyFresh :
          Numbered.variable_token (free_name eigen) ∉
            body.tokens := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      cases hName : fs_variable_name_decode variableToken with
      | none =>
          simp [fs_named_hilbert_token_tree_forall_open,
            fs_named_hilbert_token_tree_binder_close,
            hName,
            fs_named_hilbert_token_tree_binder_close_forall_open
              eigen body hBodyFresh]
      | some name =>
          have hToken :
              Numbered.variable_token name = variableToken :=
            fs_variable_name_decode_value_of_some hName
          have hNameFresh :
              name ≠ free_name eigen := by
            intro hEqual
            exact hVariableFresh (hToken ▸ congrArg
              Numbered.variable_token hEqual)
          simp [fs_named_hilbert_token_tree_forall_open,
            fs_named_hilbert_token_tree_binder_close,
            ← hToken, fs_variable_name_decode_encode,
            fs_named_binder_close_forall_open_name
              eigen name hNameFresh,
            fs_named_hilbert_token_tree_binder_close_forall_open
              eigen body hBodyFresh]
termination_by tree => sizeOf tree

mutual
  private theorem fs_named_term_token_tree_forall_open_decode
      (freeBase eigen : Nat) (hEigen : eigen < freeBase)
      (names : List Nat) :
      ∀ {tree : RawTermTokenTree} {term : SetTerm},
        Numbered.variable_token (free_name eigen) ∉
            tree.tokens →
        fs_named_term_token_tree_decode freeBase
            (names.map (fs_named_binder_close_name eigen) ++
              [bound_name 0])
            tree =
          some term →
        fs_named_term_token_tree_decode freeBase names
            (fs_named_term_token_tree_forall_open eigen tree) =
          some (Term.openAt SetSort.set names.length
            (Term.var (.fvar SetSort.set eigen)) term)
    | .atom token, term, hFresh, hDecode => by
        cases hName : fs_variable_name_decode token with
        | some name =>
            have hToken :
                Numbered.variable_token name = token :=
              fs_variable_name_decode_value_of_some hName
            have hNameFresh :
                name ≠ free_name eigen := by
              intro hEqual
              apply hFresh
              simp [RawTermTokenTree.tokens,
                ← hToken, hEqual]
            simp [fs_named_term_token_tree_decode,
              fs_named_variable_decode, hName] at hDecode
            subst term
            have hClose :=
              fs_named_variable_of_name_binder_close
                freeBase eigen
                (fs_named_forall_open_name eigen name)
                hEigen names
            rw [fs_named_binder_close_forall_open_name
              eigen name hNameFresh] at hClose
            have hOpen :
                Term.openAt SetSort.set names.length
                    (Term.var (.fvar SetSort.set eigen))
                    (Term.var
                      (fs_named_variable_of_name freeBase
                        (names.map
                            (fs_named_binder_close_name eigen) ++
                          [bound_name 0])
                        name)) =
                  Term.var
                    (fs_named_variable_of_name freeBase names
                      (fs_named_forall_open_name eigen name)) := by
              calc
                _ =
                    Term.openAt SetSort.set names.length
                      (Term.var (.fvar SetSort.set eigen))
                      (Term.closeFreeAt SetSort.set eigen
                        names.length
                        (Term.var
                          (fs_named_variable_of_name
                            freeBase names
                            (fs_named_forall_open_name
                              eigen name)))) :=
                  congrArg
                    (Term.openAt SetSort.set names.length
                      (Term.var (.fvar SetSort.set eigen)))
                    hClose
                _ =
                    Term.var
                      (fs_named_variable_of_name freeBase names
                        (fs_named_forall_open_name eigen name)) :=
                  Term.openAt_closeFreeAt
                    (σ := signature)
                    SetSort.set eigen names.length
                    (Term.var
                      (fs_named_variable_of_name freeBase names
                        (fs_named_forall_open_name eigen name)))
            simp [fs_named_term_token_tree_forall_open,
              fs_named_term_token_tree_decode,
              fs_named_variable_decode, hName,
              fs_variable_name_decode_encode, hOpen]
        | none =>
            cases hSymbol :
                fs_find_encoded
                  (fun symbol : FunctionSymbol =>
                    Numbered.constant_token symbol.ctorIdx)
                  token fs_function_symbols with
            | none =>
                simp [fs_named_term_token_tree_decode,
                  fs_named_variable_decode,
                  hName, hSymbol] at hDecode
            | some symbol =>
                by_cases hDomain :
                    signature.funcDomain symbol = []
                · simp [fs_named_term_token_tree_decode,
                    fs_named_variable_decode,
                    hName, hSymbol, hDomain] at hDecode
                  subst term
                  simp [fs_named_term_token_tree_forall_open,
                    fs_named_term_token_tree_decode,
                    fs_named_variable_decode,
                    hName, hSymbol, hDomain,
                    Term.openAt]
                · simp [fs_named_term_token_tree_decode,
                    fs_named_variable_decode,
                    hName, hSymbol, hDomain] at hDecode
    | .application head arguments, term,
        hFresh, hDecode => by
        have hArgumentsFresh :
            Numbered.variable_token (free_name eigen) ∉
              RawTermTokenTree.list_tokens arguments := by
          intro hMember
          apply hFresh
          simp [RawTermTokenTree.tokens, hMember]
        cases hSymbol :
            fs_find_encoded
              (fun symbol : FunctionSymbol =>
                Numbered.function_token
                  (arguments.length - 1) symbol.ctorIdx)
              head fs_function_symbols with
        | none =>
            simp [fs_named_term_token_tree_decode,
              hSymbol] at hDecode
        | some symbol =>
            cases hArguments :
                arguments.mapM
                  (fs_named_term_token_tree_decode freeBase
                    (names.map
                        (fs_named_binder_close_name eigen) ++
                      [bound_name 0])) with
            | none =>
                simp [fs_named_term_token_tree_decode,
                  hSymbol, hArguments] at hDecode
            | some terms =>
                by_cases hCheck :
                    Term.check_args_wellSorted terms
                        (signature.funcDomain symbol) = true
                · simp [fs_named_term_token_tree_decode,
                    hSymbol, hArguments, hCheck] at hDecode
                  rcases hDecode with
                    ⟨hArgumentsPositive, rfl⟩
                  have hTargetArguments :=
                    fs_named_term_token_trees_forall_open_decode
                      freeBase eigen hEigen names
                      hArgumentsFresh hArguments
                  have hTargetCheck :
                      Term.check_args_wellSorted
                          (terms.map
                            (Term.openAt SetSort.set names.length
                              (Term.var
                                (.fvar SetSort.set eigen))))
                          (signature.funcDomain symbol) = true :=
                    Term.check_args_wellSorted_complete <|
                      ArgsWellSorted.openAt
                        SetSort.set names.length
                        (TermWellSorted.fvar
                          (σ := signature) SetSort.set eigen)
                        (Term.check_args_wellSorted_sound hCheck)
                  simp [fs_named_term_token_tree_forall_open,
                    fs_named_term_token_tree_decode,
                    hArgumentsPositive, hSymbol,
                    hTargetArguments, hTargetCheck,
                    Term.openAt]
                · simp [fs_named_term_token_tree_decode,
                    hSymbol, hArguments, hCheck] at hDecode
  termination_by tree => sizeOf tree

  private theorem fs_named_term_token_trees_forall_open_decode
      (freeBase eigen : Nat) (hEigen : eigen < freeBase)
      (names : List Nat) :
      ∀ {trees : List RawTermTokenTree}
          {terms : List SetTerm},
        Numbered.variable_token (free_name eigen) ∉
            RawTermTokenTree.list_tokens trees →
        trees.mapM
            (fs_named_term_token_tree_decode freeBase
              (names.map
                  (fs_named_binder_close_name eigen) ++
                [bound_name 0])) =
          some terms →
        (trees.map
            (fs_named_term_token_tree_forall_open eigen)).mapM
            (fs_named_term_token_tree_decode freeBase names) =
          some (terms.map
            (Term.openAt SetSort.set names.length
              (Term.var (.fvar SetSort.set eigen))))
    | .nil, terms, _, hDecode => by
        simp at hDecode
        subst terms
        rfl
    | .cons tree trees, terms, hFresh, hDecode => by
        have hHeadFresh :
            Numbered.variable_token (free_name eigen) ∉
              tree.tokens := by
          intro hMember
          apply hFresh
          simp [RawTermTokenTree.list_tokens, hMember]
        have hTailFresh :
            Numbered.variable_token (free_name eigen) ∉
              RawTermTokenTree.list_tokens trees := by
          intro hMember
          apply hFresh
          simp [RawTermTokenTree.list_tokens, hMember]
        cases hHead :
            fs_named_term_token_tree_decode freeBase
              (names.map
                  (fs_named_binder_close_name eigen) ++
                [bound_name 0])
              tree with
        | none =>
            simp [List.mapM_cons, hHead] at hDecode
        | some head =>
            cases hTail :
                trees.mapM
                  (fs_named_term_token_tree_decode freeBase
                    (names.map
                        (fs_named_binder_close_name eigen) ++
                      [bound_name 0])) with
            | none =>
                simp [List.mapM_cons,
                  hHead, hTail] at hDecode
            | some tail =>
                simp [List.mapM_cons,
                  hHead, hTail] at hDecode
                subst terms
                have hHeadOpen :=
                  fs_named_term_token_tree_forall_open_decode
                    freeBase eigen hEigen names
                    hHeadFresh hHead
                have hTailOpen :=
                  fs_named_term_token_trees_forall_open_decode
                    freeBase eigen hEigen names
                    hTailFresh hTail
                simp [List.mapM_cons,
                  hHeadOpen, hTailOpen]
  termination_by trees => sizeOf trees
end

private theorem fs_named_hilbert_token_tree_forall_open_decode
    (freeBase eigen : Nat) (hEigen : eigen < freeBase) :
    ∀ {names : List Nat}
      {tree : RawHilbertTokenTree}
      {formula : SetFormula},
      Numbered.variable_token (free_name eigen) ∉
          tree.tokens →
      fs_named_hilbert_token_tree_decode freeBase
          (names.map (fs_named_binder_close_name eigen) ++
            [bound_name 0])
          tree =
        some formula →
      fs_named_hilbert_token_tree_decode freeBase names
          (fs_named_hilbert_token_tree_forall_open eigen tree) =
        some (Formula.openAt SetSort.set names.length
          (Term.var (.fvar SetSort.set eigen)) formula)
  | names, .equality left right, formula,
      hFresh, hDecode => by
      have hLeftFresh :
          Numbered.variable_token (free_name eigen) ∉
            left.tokens := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      have hRightFresh :
          Numbered.variable_token (free_name eigen) ∉
            right.tokens := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      cases hLeft :
          fs_named_term_token_tree_decode freeBase
            (names.map (fs_named_binder_close_name eigen) ++
              [bound_name 0])
            left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hLeft] at hDecode
      | some leftTerm =>
          cases hRight :
              fs_named_term_token_tree_decode freeBase
                (names.map
                    (fs_named_binder_close_name eigen) ++
                  [bound_name 0])
                right with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
          | some rightTerm =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
              have hLeftOpen :=
                fs_named_term_token_tree_forall_open_decode
                  freeBase eigen hEigen names
                  hLeftFresh hLeft
              have hRightOpen :=
                fs_named_term_token_tree_forall_open_decode
                  freeBase eigen hEigen names
                  hRightFresh hRight
              have hLeftCheck :
                  Term.check_wellSorted SetSort.set
                      (Term.openAt SetSort.set names.length
                        (Term.var (.fvar SetSort.set eigen))
                        leftTerm) = true :=
                Term.check_wellSorted_complete <|
                  TermWellSorted.openAt names.length
                    (Term.check_wellSorted_sound hDecode.1.1)
                    (TermWellSorted.fvar
                      (σ := signature) SetSort.set eigen)
              have hRightCheck :
                  Term.check_wellSorted SetSort.set
                      (Term.openAt SetSort.set names.length
                        (Term.var (.fvar SetSort.set eigen))
                        rightTerm) = true :=
                Term.check_wellSorted_complete <|
                  TermWellSorted.openAt names.length
                    (Term.check_wellSorted_sound hDecode.1.2)
                    (TermWellSorted.fvar
                      (σ := signature) SetSort.set eigen)
              rw [← hDecode.2]
              simp [fs_named_hilbert_token_tree_forall_open,
                fs_named_hilbert_token_tree_decode,
                hLeftOpen, hRightOpen,
                hLeftCheck, hRightCheck,
                Formula.openAt]
  | names, .membership left right, formula,
      hFresh, hDecode => by
      have hLeftFresh :
          Numbered.variable_token (free_name eigen) ∉
            left.tokens := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      have hRightFresh :
          Numbered.variable_token (free_name eigen) ∉
            right.tokens := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      cases hLeft :
          fs_named_term_token_tree_decode freeBase
            (names.map (fs_named_binder_close_name eigen) ++
              [bound_name 0])
            left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hLeft] at hDecode
      | some leftTerm =>
          cases hRight :
              fs_named_term_token_tree_decode freeBase
                (names.map
                    (fs_named_binder_close_name eigen) ++
                  [bound_name 0])
                right with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
          | some rightTerm =>
              by_cases hCheck :
                  Term.check_args_wellSorted
                      [leftTerm, rightTerm]
                      (signature.relDomain
                        RelationSymbol.membership) = true
              · simp [fs_named_hilbert_token_tree_decode,
                  hLeft, hRight, hCheck] at hDecode
                subst formula
                have hLeftOpen :=
                  fs_named_term_token_tree_forall_open_decode
                    freeBase eigen hEigen names
                    hLeftFresh hLeft
                have hRightOpen :=
                  fs_named_term_token_tree_forall_open_decode
                    freeBase eigen hEigen names
                    hRightFresh hRight
                have hTargetCheck :
                    Term.check_args_wellSorted
                        [Term.openAt SetSort.set names.length
                            (Term.var (.fvar SetSort.set eigen))
                            leftTerm,
                          Term.openAt SetSort.set names.length
                            (Term.var (.fvar SetSort.set eigen))
                            rightTerm]
                        (signature.relDomain
                          RelationSymbol.membership) = true := by
                  simpa using
                    Term.check_args_wellSorted_complete <|
                      ArgsWellSorted.openAt
                        SetSort.set names.length
                        (TermWellSorted.fvar
                          (σ := signature) SetSort.set eigen)
                        (Term.check_args_wellSorted_sound hCheck)
                simp [fs_named_hilbert_token_tree_forall_open,
                  fs_named_hilbert_token_tree_decode,
                  hLeftOpen, hRightOpen, hTargetCheck,
                  Formula.openAt]
              · simp [fs_named_hilbert_token_tree_decode,
                  hLeft, hRight, hCheck] at hDecode
  | names, .predicate head arguments, formula,
      hFresh, hDecode => by
      have hArgumentsFresh :
          Numbered.variable_token (free_name eigen) ∉
            RawTermTokenTree.list_tokens arguments := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      cases hRelation :
          fs_find_encoded
            (fun relation : RelationSymbol =>
              Numbered.predicate_token
                (arguments.length - 1) relation.ctorIdx)
            head fs_relation_symbols with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hRelation] at hDecode
      | some relation =>
          by_cases hKind :
              fs_relation_kind relation =
                QuotationRelationKind.predicate
          · cases hArguments :
                arguments.mapM
                  (fs_named_term_token_tree_decode freeBase
                    (names.map
                        (fs_named_binder_close_name eigen) ++
                      [bound_name 0])) with
            | none =>
                simp [fs_named_hilbert_token_tree_decode,
                  hRelation, hArguments] at hDecode
            | some terms =>
                by_cases hCheck :
                    Term.check_args_wellSorted terms
                        (signature.relDomain relation) = true
                · simp [fs_named_hilbert_token_tree_decode,
                    hRelation, hKind,
                    hArguments, hCheck] at hDecode
                  subst formula
                  have hTargetArguments :=
                    fs_named_term_token_trees_forall_open_decode
                      freeBase eigen hEigen names
                      hArgumentsFresh hArguments
                  have hTargetCheck :
                      Term.check_args_wellSorted
                          (terms.map
                            (Term.openAt SetSort.set names.length
                              (Term.var
                                (.fvar SetSort.set eigen))))
                          (signature.relDomain relation) = true :=
                    Term.check_args_wellSorted_complete <|
                      ArgsWellSorted.openAt
                        SetSort.set names.length
                        (TermWellSorted.fvar
                          (σ := signature) SetSort.set eigen)
                        (Term.check_args_wellSorted_sound hCheck)
                  simp [fs_named_hilbert_token_tree_forall_open,
                    fs_named_hilbert_token_tree_decode,
                    hRelation, hKind,
                    hTargetArguments, hTargetCheck,
                    Formula.openAt]
                · simp [fs_named_hilbert_token_tree_decode,
                    hRelation, hKind,
                    hArguments, hCheck] at hDecode
          · simp [fs_named_hilbert_token_tree_decode,
              hRelation, hKind] at hDecode
  | names, .negation body, formula,
      hFresh, hDecode => by
      have hBodyFresh :
          Numbered.variable_token (free_name eigen) ∉
            body.tokens := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      cases hBody :
          fs_named_hilbert_token_tree_decode freeBase
            (names.map (fs_named_binder_close_name eigen) ++
              [bound_name 0])
            body with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hBody] at hDecode
      | some bodyFormula =>
          simp [fs_named_hilbert_token_tree_decode,
            hBody] at hDecode
          subst formula
          have hBodyOpen :=
            fs_named_hilbert_token_tree_forall_open_decode
              freeBase eigen hEigen hBodyFresh hBody
          simp [fs_named_hilbert_token_tree_forall_open,
            fs_named_hilbert_token_tree_decode,
            hBodyOpen, Formula.openAt]
  | names, .implication left right, formula,
      hFresh, hDecode => by
      have hLeftFresh :
          Numbered.variable_token (free_name eigen) ∉
            left.tokens := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      have hRightFresh :
          Numbered.variable_token (free_name eigen) ∉
            right.tokens := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      cases hLeft :
          fs_named_hilbert_token_tree_decode freeBase
            (names.map (fs_named_binder_close_name eigen) ++
              [bound_name 0])
            left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hLeft] at hDecode
      | some leftFormula =>
          cases hRight :
              fs_named_hilbert_token_tree_decode freeBase
                (names.map
                    (fs_named_binder_close_name eigen) ++
                  [bound_name 0])
                right with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
          | some rightFormula =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
              subst formula
              have hLeftOpen :=
                fs_named_hilbert_token_tree_forall_open_decode
                  freeBase eigen hEigen hLeftFresh hLeft
              have hRightOpen :=
                fs_named_hilbert_token_tree_forall_open_decode
                  freeBase eigen hEigen hRightFresh hRight
              simp [fs_named_hilbert_token_tree_forall_open,
                fs_named_hilbert_token_tree_decode,
                hLeftOpen, hRightOpen,
                Formula.openAt]
  | names, .universal variableToken body, formula,
      hFresh, hDecode => by
      have hVariableFresh :
          variableToken ≠ Numbered.variable_token
            (free_name eigen) := by
        intro hEqual
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hEqual]
      have hBodyFresh :
          Numbered.variable_token (free_name eigen) ∉
            body.tokens := by
        intro hMember
        apply hFresh
        simp [RawHilbertTokenTree.tokens, hMember]
      cases hName :
          fs_variable_name_decode variableToken with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hName] at hDecode
      | some name =>
          cases hBody :
              fs_named_hilbert_token_tree_decode freeBase
                (name ::
                  (names.map
                      (fs_named_binder_close_name eigen) ++
                    [bound_name 0]))
                body with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hName, hBody] at hDecode
          | some bodyFormula =>
              simp [fs_named_hilbert_token_tree_decode,
                hName, hBody] at hDecode
              subst formula
              have hToken :
                  Numbered.variable_token name = variableToken :=
                fs_variable_name_decode_value_of_some hName
              have hNameFresh :
                  name ≠ free_name eigen := by
                intro hEqual
                exact hVariableFresh (hToken ▸ congrArg
                  Numbered.variable_token hEqual)
              have hBody' :
                  fs_named_hilbert_token_tree_decode freeBase
                      ((fs_named_forall_open_name eigen name ::
                          names).map
                          (fs_named_binder_close_name eigen) ++
                        [bound_name 0])
                      body =
                    some bodyFormula := by
                simpa [List.map_cons,
                  fs_named_binder_close_forall_open_name
                    eigen name hNameFresh] using hBody
              have hBodyOpen :=
                fs_named_hilbert_token_tree_forall_open_decode
                  freeBase eigen hEigen hBodyFresh hBody'
              simpa [fs_named_hilbert_token_tree_forall_open,
                fs_named_hilbert_token_tree_decode,
                hName, fs_variable_name_decode_encode,
                Formula.openAt, Formula.next_depth] using
                congrArg
                  (fun result =>
                    result.bind
                      (fun bodyFormula =>
                        some (Formula.forallE
                          SetSort.set bodyFormula)))
                  hBodyOpen
termination_by
  _ tree _ _ _ => sizeOf tree

/--
若规范外层 binder 的正文不含待打开的自由变量 token，则正文可以沿
`CanonicalForallOpenTokens` 打开，并继续解码为公式层的 `openAt`。

token 新鲜性恰好排除具名编码中的捕获冲突；内部 binder 名仍可任意选择。
-/
theorem fs_named_hilbert_tokens_decode_with_env_canonical_forall_open
    (freeBase eigen : Nat)
    (bodyTokens : List Nat)
    (body : SetFormula)
    (hEigen : eigen < freeBase)
    (hTokenFresh :
      Numbered.variable_token (free_name eigen) ∉ bodyTokens)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [bound_name 0] bodyTokens =
        some body) :
    ∃ targetTokens,
      CanonicalForallOpenTokens
          (Numbered.variable_token (free_name eigen))
          bodyTokens targetTokens ∧
        fs_named_hilbert_tokens_decode_with_env
            freeBase [] targetTokens =
          some
            body⟦SetSort.set, 0 ↦
              Term.var (.fvar SetSort.set eigen)⟧ₘ := by
  rcases
      (fs_named_hilbert_tokens_decode_with_env_iff
        freeBase [bound_name 0] bodyTokens body).mp hDecode with
    ⟨tree, hParse, hTree⟩
  have hSource :
      bodyTokens = tree.tokens :=
    (RawHilbertTokenTree.parse?_sound hParse).symm
  have hTreeFresh :
      Numbered.variable_token (free_name eigen) ∉ tree.tokens := by
    rw [← hSource]
    exact hTokenFresh
  have hTargetTree :=
    fs_named_hilbert_token_tree_forall_open_decode
      freeBase eigen hEigen (names := []) hTreeFresh hTree
  have hTargetDecode :
      fs_named_hilbert_tokens_decode_with_env freeBase []
          (fs_named_hilbert_token_tree_forall_open eigen tree).tokens =
        some
          body⟦SetSort.set, 0 ↦
            Term.var (.fvar SetSort.set eigen)⟧ₘ := by
    exact
      fs_named_hilbert_tokens_decode_with_env_of_tree
        freeBase [] (by simpa using hTargetTree)
  have hShift :=
    fs_named_hilbert_token_tree_binder_shift_relation
      freeBase (by simpa using hTargetTree)
  have hClose :=
    fs_named_hilbert_token_tree_binder_close_tokens
      eigen
      (fs_named_hilbert_token_tree_forall_open eigen tree)
  rw [fs_named_hilbert_token_tree_binder_close_forall_open
    eigen tree hTreeFresh] at hClose
  have hOpen :
      CanonicalForallOpenTokens
        (Numbered.variable_token (free_name eigen))
        tree.tokens
        (fs_named_hilbert_token_tree_forall_open eigen tree).tokens := by
    rw [hClose]
    exact
      CanonicalForallOpenTokens.of_binder_shift_substitution
        eigen hShift
  refine
    ⟨(fs_named_hilbert_token_tree_forall_open eigen tree).tokens,
      ?_, hTargetDecode⟩
  simpa [hSource] using hOpen

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
