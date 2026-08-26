import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoderComposition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoderFreeSupport

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation

open Nonlogical.BasicSetTheory

private def term_tree_avoids_names
    (names : List Nat) (tree : RawTermTokenTree) : Prop :=
  ∀ name, name ∈ names →
    Numbered.variable_token name ∉ tree.tokens

private def term_trees_avoid_names
    (names : List Nat) (trees : List RawTermTokenTree) : Prop :=
  ∀ tree, tree ∈ trees → term_tree_avoids_names names tree

private theorem mem_term_list_tokens_of_mem
    {tree : RawTermTokenTree} {trees : List RawTermTokenTree}
    {token : Nat}
    (hTree : tree ∈ trees)
    (hToken : token ∈ tree.tokens) :
    token ∈ RawTermTokenTree.list_tokens trees := by
  induction trees with
  | nil =>
      simp at hTree
  | cons head tail ih =>
      rcases List.mem_cons.mp hTree with rfl | hTree
      · simp [RawTermTokenTree.list_tokens, hToken]
      · simp [RawTermTokenTree.list_tokens, ih hTree]

mutual
  private theorem fs_named_term_token_tree_decode_eq_empty_of_avoids
      (freeBase : Nat) (names : List Nat) :
      ∀ tree,
        term_tree_avoids_names names tree →
          fs_named_term_token_tree_decode freeBase names tree =
            fs_named_term_token_tree_decode freeBase [] tree
    | .atom token, hAvoid => by
        cases hName : fs_variable_name_decode token with
        | none =>
            simp [fs_named_term_token_tree_decode,
              fs_named_variable_decode, hName]
        | some name =>
            have hNameNot : name ∉ names := by
              intro hNameMem
              apply hAvoid name hNameMem
              simp [RawTermTokenTree.tokens,
                ← fs_variable_name_decode_value_of_some hName]
            simp [fs_named_term_token_tree_decode,
              fs_named_variable_decode, hName,
              fs_named_variable_of_name,
              fs_bound_name_index,
              fs_bound_name_index_eq_none_of_not_mem name hNameNot]
    | .application head arguments, hAvoid => by
        have hArguments :
            term_trees_avoid_names names arguments := by
          intro tree hTree name hName hToken
          apply hAvoid name hName
          simp [RawTermTokenTree.tokens,
            mem_term_list_tokens_of_mem hTree hToken]
        simp only [fs_named_term_token_tree_decode]
        rw [fs_named_term_token_trees_decode_eq_empty_of_avoids
          freeBase names arguments hArguments]
  termination_by tree => sizeOf tree

  private theorem fs_named_term_token_trees_decode_eq_empty_of_avoids
      (freeBase : Nat) (names : List Nat) :
      ∀ trees,
        term_trees_avoid_names names trees →
          trees.mapM
              (fs_named_term_token_tree_decode freeBase names) =
            trees.mapM
              (fs_named_term_token_tree_decode freeBase [])
    | .nil, _ => rfl
    | .cons tree trees, hAvoid => by
        have hHead :
            term_tree_avoids_names names tree :=
          hAvoid tree (by simp)
        have hTail :
            term_trees_avoid_names names trees := by
          intro candidate hCandidate
          exact hAvoid candidate (by simp [hCandidate])
        simp only [List.mapM_cons]
        rw [fs_named_term_token_tree_decode_eq_empty_of_avoids
          freeBase names tree hHead]
        rw [fs_named_term_token_trees_decode_eq_empty_of_avoids
          freeBase names trees hTail]
  termination_by trees => sizeOf trees
end

private def substitute_term_tree
    (target : Nat) (replacement : RawTermTokenTree) :
    RawTermTokenTree → RawTermTokenTree
  | .atom token =>
      if token = target then replacement else .atom token
  | .application head arguments =>
      .application head
        (arguments.map (substitute_term_tree target replacement))

private def substitute_hilbert_tree
    (target : Nat) (replacement : RawTermTokenTree) :
    RawHilbertTokenTree → RawHilbertTokenTree
  | .equality left right =>
      .equality
        (substitute_term_tree target replacement left)
        (substitute_term_tree target replacement right)
  | .membership left right =>
      .membership
        (substitute_term_tree target replacement left)
        (substitute_term_tree target replacement right)
  | .predicate head arguments =>
      .predicate head
        (arguments.map (substitute_term_tree target replacement))
  | .negation body =>
      .negation (substitute_hilbert_tree target replacement body)
  | .implication left right =>
      .implication
        (substitute_hilbert_tree target replacement left)
        (substitute_hilbert_tree target replacement right)
  | .universal variableToken body =>
      .universal variableToken
        (substitute_hilbert_tree target replacement body)

mutual
  private def term_tree_target_separated
      (target : Nat) : RawTermTokenTree → Prop
    | .atom _ => True
    | .application head arguments =>
        head ≠ target ∧
          term_trees_target_separated target arguments

  private def term_trees_target_separated
      (target : Nat) : List RawTermTokenTree → Prop
    | [] => True
    | tree :: trees =>
        term_tree_target_separated target tree ∧
          term_trees_target_separated target trees
end

private def hilbert_tree_target_separated
    (target : Nat) : RawHilbertTokenTree → Prop
  | .equality left right | .membership left right =>
      term_tree_target_separated target left ∧
        term_tree_target_separated target right
  | .predicate head arguments =>
      head ≠ target ∧
        term_trees_target_separated target arguments
  | .negation body =>
      hilbert_tree_target_separated target body
  | .implication left right =>
      hilbert_tree_target_separated target left ∧
        hilbert_tree_target_separated target right
  | .universal variableToken body =>
      variableToken ≠ target ∧
        hilbert_tree_target_separated target body

def fs_named_hilbert_tree_target_not_bound
    (target : Nat) : RawHilbertTokenTree → Prop
  | .equality _ _ | .membership _ _ | .predicate _ _ => True
  | .negation body =>
      fs_named_hilbert_tree_target_not_bound target body
  | .implication left right =>
      fs_named_hilbert_tree_target_not_bound target left ∧
        fs_named_hilbert_tree_target_not_bound target right
  | .universal variableToken body =>
      variableToken ≠ target ∧
        fs_named_hilbert_tree_target_not_bound target body

mutual
  private theorem substitute_term_tree_tokens
      (targetName : Nat) (replacement : RawTermTokenTree)
      (replacementTokens : List Nat)
      (hReplacement : replacement.tokens = replacementTokens) :
      ∀ tree,
        term_tree_target_separated
            (Numbered.variable_token targetName) tree →
          (substitute_term_tree
              (Numbered.variable_token targetName) replacement tree).tokens =
            substitute_tokens tree.tokens
              (Numbered.variable_token targetName) replacementTokens
    | .atom token, _ => by
        by_cases hToken :
            token = Numbered.variable_token targetName
        · subst token
          simp [substitute_term_tree, RawTermTokenTree.tokens,
            hReplacement]
        · simp [substitute_term_tree, RawTermTokenTree.tokens,
            substitute_tokens, substitution_pieces_tokens,
            substitution_piece_tokens, hToken]
    | .application head arguments, hSeparated => by
        rcases hSeparated with ⟨hHead, hArguments⟩
        simp only [substitute_term_tree, RawTermTokenTree.tokens]
        rw [substitute_term_trees_tokens
          targetName replacement replacementTokens hReplacement
          arguments hArguments]
        simp [substitute_tokens_append,
          logical_token_ne_variable_token, hHead]
  termination_by tree => sizeOf tree

  private theorem substitute_term_trees_tokens
      (targetName : Nat) (replacement : RawTermTokenTree)
      (replacementTokens : List Nat)
      (hReplacement : replacement.tokens = replacementTokens) :
      ∀ trees,
        term_trees_target_separated
            (Numbered.variable_token targetName) trees →
          RawTermTokenTree.list_tokens
              (trees.map (substitute_term_tree
                (Numbered.variable_token targetName) replacement)) =
            substitute_tokens
              (RawTermTokenTree.list_tokens trees)
              (Numbered.variable_token targetName) replacementTokens
    | .nil, _ => by
        simp [RawTermTokenTree.list_tokens]
    | .cons tree trees, hSeparated => by
        rcases hSeparated with ⟨hTree, hTrees⟩
        simp only [List.map_cons, RawTermTokenTree.list_tokens]
        rw [substitute_term_tree_tokens
          targetName replacement replacementTokens hReplacement
          tree hTree]
        rw [substitute_term_trees_tokens
          targetName replacement replacementTokens hReplacement
          trees hTrees]
        exact (substitute_tokens_append
          tree.tokens (RawTermTokenTree.list_tokens trees)
          replacementTokens
          (Numbered.variable_token targetName)).symm
  termination_by trees => sizeOf trees
end

private theorem substitute_hilbert_tree_tokens
    (targetName : Nat) (replacement : RawTermTokenTree)
    (replacementTokens : List Nat)
    (hReplacement : replacement.tokens = replacementTokens) :
    ∀ tree,
      hilbert_tree_target_separated
          (Numbered.variable_token targetName) tree →
        (substitute_hilbert_tree
            (Numbered.variable_token targetName) replacement tree).tokens =
          substitute_tokens tree.tokens
            (Numbered.variable_token targetName) replacementTokens
  | .equality left right, hSeparated => by
      rcases hSeparated with ⟨hLeft, hRight⟩
      simp [substitute_hilbert_tree, RawHilbertTokenTree.tokens,
        substitute_term_tree_tokens targetName replacement
          replacementTokens hReplacement left hLeft,
        substitute_term_tree_tokens targetName replacement
          replacementTokens hReplacement right hRight,
        substitute_tokens_append,
        logical_token_ne_variable_token]
  | .membership left right, hSeparated => by
      rcases hSeparated with ⟨hLeft, hRight⟩
      simp [substitute_hilbert_tree, RawHilbertTokenTree.tokens,
        substitute_term_tree_tokens targetName replacement
          replacementTokens hReplacement left hLeft,
        substitute_term_tree_tokens targetName replacement
          replacementTokens hReplacement right hRight,
        substitute_tokens_append,
        logical_token_ne_variable_token,
        membership_token_ne_variable_token]
  | .predicate head arguments, hSeparated => by
      rcases hSeparated with ⟨hHead, hArguments⟩
      simp [substitute_hilbert_tree, RawHilbertTokenTree.tokens,
        substitute_term_trees_tokens targetName replacement
          replacementTokens hReplacement arguments hArguments,
        substitute_tokens_append,
        logical_token_ne_variable_token, hHead]
  | .negation body, hBound => by
      simp [substitute_hilbert_tree, RawHilbertTokenTree.tokens,
        substitute_hilbert_tree_tokens targetName replacement
          replacementTokens hReplacement body hBound,
        substitute_tokens_append,
        logical_token_ne_variable_token]
  | .implication left right, hBound => by
      simp [hilbert_tree_target_separated] at hBound
      simp [substitute_hilbert_tree, RawHilbertTokenTree.tokens,
        substitute_hilbert_tree_tokens targetName replacement
          replacementTokens hReplacement left hBound.1,
        substitute_hilbert_tree_tokens targetName replacement
          replacementTokens hReplacement right hBound.2,
        substitute_tokens_append,
        logical_token_ne_variable_token]
  | .universal variableToken body, hBound => by
      simp [hilbert_tree_target_separated] at hBound
      simp [substitute_hilbert_tree, RawHilbertTokenTree.tokens,
        substitute_hilbert_tree_tokens targetName replacement
          replacementTokens hReplacement body hBound.2,
        substitute_tokens_append,
        logical_token_ne_variable_token,
        hBound.1]
termination_by tree => sizeOf tree

mutual
  private theorem term_tree_target_separated_of_decode
      (freeBase : Nat) (boundNames : List Nat) (targetName : Nat) :
      ∀ tree term,
        fs_named_term_token_tree_decode freeBase boundNames tree =
            some term →
          term_tree_target_separated
            (Numbered.variable_token targetName) tree
    | .atom _, _, _ => trivial
    | .application head arguments, term, hDecode => by
        simp only [fs_named_term_token_tree_decode] at hDecode
        cases hSymbol :
            fs_find_encoded
              (fun candidate =>
                Numbered.function_token
                  (arguments.length - 1) candidate.ctorIdx)
              head fs_function_symbols with
        | none =>
            simp [hSymbol] at hDecode
        | some symbol =>
            cases hArguments :
                arguments.mapM
                  (fs_named_term_token_tree_decode
                    freeBase boundNames) with
            | none =>
                simp [hSymbol, hArguments] at hDecode
            | some decoded =>
                have hHeadValue :
                    Numbered.function_token
                        (arguments.length - 1) symbol.ctorIdx =
                      head :=
                  fs_find_encoded_value_of_some
                    (encode := fun candidate : FunctionSymbol =>
                      Numbered.function_token
                        (arguments.length - 1) candidate.ctorIdx)
                    hSymbol
                constructor
                · rw [← hHeadValue]
                  exact function_token_ne_variable_token
                    (arguments.length - 1) symbol.ctorIdx targetName
                · exact term_trees_target_separated_of_decode
                    freeBase boundNames targetName
                    arguments decoded hArguments
  termination_by tree => sizeOf tree

  private theorem term_trees_target_separated_of_decode
      (freeBase : Nat) (boundNames : List Nat) (targetName : Nat) :
      ∀ trees terms,
        trees.mapM
            (fs_named_term_token_tree_decode freeBase boundNames) =
            some terms →
          term_trees_target_separated
            (Numbered.variable_token targetName) trees
    | .nil, _, _ => trivial
    | tree :: trees, terms, hDecode => by
        simp only [List.mapM_cons] at hDecode
        cases hTree :
            fs_named_term_token_tree_decode
              freeBase boundNames tree with
        | none =>
            simp [hTree] at hDecode
        | some term =>
            cases hTrees :
                trees.mapM
                  (fs_named_term_token_tree_decode
                    freeBase boundNames) with
            | none =>
                simp [hTree, hTrees] at hDecode
            | some decoded =>
                exact ⟨
                  term_tree_target_separated_of_decode
                    freeBase boundNames targetName tree term hTree,
                  term_trees_target_separated_of_decode
                    freeBase boundNames targetName trees decoded hTrees⟩
  termination_by trees => sizeOf trees
end

private theorem hilbert_tree_target_separated_of_decode
    (freeBase : Nat) (boundNames : List Nat) (targetName : Nat) :
    ∀ tree formula,
      fs_named_hilbert_tree_target_not_bound
          (Numbered.variable_token targetName) tree →
        fs_named_hilbert_token_tree_decode
            freeBase boundNames tree = some formula →
          hilbert_tree_target_separated
            (Numbered.variable_token targetName) tree
  | .equality left right, formula, _, hDecode => by
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hLeft :
          fs_named_term_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [hLeft] at hDecode
      | some leftTerm =>
          cases hRight :
              fs_named_term_token_tree_decode
                freeBase boundNames right with
          | none =>
              simp [hLeft, hRight] at hDecode
          | some rightTerm =>
              exact ⟨
                term_tree_target_separated_of_decode
                  freeBase boundNames targetName
                  left leftTerm hLeft,
                term_tree_target_separated_of_decode
                  freeBase boundNames targetName
                  right rightTerm hRight⟩
  | .membership left right, formula, _, hDecode => by
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hLeft :
          fs_named_term_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [hLeft] at hDecode
      | some leftTerm =>
          cases hRight :
              fs_named_term_token_tree_decode
                freeBase boundNames right with
          | none =>
              simp [hLeft, hRight] at hDecode
          | some rightTerm =>
              exact ⟨
                term_tree_target_separated_of_decode
                  freeBase boundNames targetName
                  left leftTerm hLeft,
                term_tree_target_separated_of_decode
                  freeBase boundNames targetName
                  right rightTerm hRight⟩
  | .predicate head arguments, formula, _, hDecode => by
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hRelation :
          fs_find_encoded
            (fun candidate =>
              Numbered.predicate_token
                (arguments.length - 1) candidate.ctorIdx)
            head fs_relation_symbols with
      | none =>
          simp [hRelation] at hDecode
      | some relation =>
          cases hKind :
              fs_relation_kind relation with
          | membership =>
              simp [hRelation, hKind] at hDecode
          | predicate =>
              cases hArguments :
                  arguments.mapM
                    (fs_named_term_token_tree_decode
                      freeBase boundNames) with
              | none =>
                  simp [hRelation, hArguments] at hDecode
              | some decoded =>
                  have hHeadValue :
                      Numbered.predicate_token
                          (arguments.length - 1) relation.ctorIdx =
                        head :=
                    fs_find_encoded_value_of_some
                      (encode := fun candidate : RelationSymbol =>
                        Numbered.predicate_token
                          (arguments.length - 1) candidate.ctorIdx)
                      hRelation
                  constructor
                  · rw [← hHeadValue]
                    exact predicate_token_ne_variable_token
                      (arguments.length - 1)
                      relation.ctorIdx targetName
                  · exact term_trees_target_separated_of_decode
                      freeBase boundNames targetName
                      arguments decoded hArguments
  | .negation body, formula, hNotBound, hDecode => by
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hBody :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames body with
      | none =>
          simp [hBody] at hDecode
      | some bodyFormula =>
          exact hilbert_tree_target_separated_of_decode
            freeBase boundNames targetName
            body bodyFormula hNotBound hBody
  | .implication left right, formula, hNotBound, hDecode => by
      simp [fs_named_hilbert_tree_target_not_bound] at hNotBound
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hLeft :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [hLeft] at hDecode
      | some leftFormula =>
          cases hRight :
              fs_named_hilbert_token_tree_decode
                freeBase boundNames right with
          | none =>
              simp [hLeft, hRight] at hDecode
          | some rightFormula =>
              exact ⟨
                hilbert_tree_target_separated_of_decode
                  freeBase boundNames targetName
                  left leftFormula hNotBound.1 hLeft,
                hilbert_tree_target_separated_of_decode
                  freeBase boundNames targetName
                  right rightFormula hNotBound.2 hRight⟩
  | .universal variableToken body, formula,
      hNotBound, hDecode => by
      simp [fs_named_hilbert_tree_target_not_bound] at hNotBound
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hName :
          fs_variable_name_decode variableToken with
      | none =>
          simp [hName] at hDecode
      | some name =>
          cases hBody :
              fs_named_hilbert_token_tree_decode
                freeBase (name :: boundNames) body with
          | none =>
              simp [hName, hBody] at hDecode
          | some bodyFormula =>
              exact ⟨hNotBound.1,
                hilbert_tree_target_separated_of_decode
                  freeBase (name :: boundNames) targetName
                  body bodyFormula hNotBound.2 hBody⟩
termination_by tree => sizeOf tree

private theorem fs_named_variable_decode_free_name
    (freeBase id : Nat) (boundNames : List Nat)
    (hFresh : free_name id ∉ boundNames) :
    fs_named_variable_decode freeBase boundNames
        (Numbered.variable_token (free_name id)) =
      some (.fvar SetSort.set id) := by
  have hFresh' : 2 * id ∉ boundNames := by
    simpa [free_name] using hFresh
  simp [fs_named_variable_decode, fs_named_variable_of_name,
    fs_bound_name_index_eq_none_of_not_mem _ hFresh',
    free_name]

mutual
  private theorem fs_named_term_token_tree_decode_substitute_free
      (freeBase id : Nat) (boundNames : List Nat)
      (replacementTree : RawTermTokenTree) (replacement : SetTerm)
      (hId : id < freeBase)
      (hTargetFresh : free_name id ∉ boundNames)
      (hReplacement :
        fs_named_term_token_tree_decode freeBase [] replacementTree =
          some replacement)
      (hReplacementWellSorted :
        TermWellSorted replacement SetSort.set) :
      ∀ tree term,
        (Numbered.variable_token (free_name id) ∈ tree.tokens →
          term_tree_avoids_names boundNames replacementTree) →
        fs_named_term_token_tree_decode freeBase boundNames tree =
            some term →
          fs_named_term_token_tree_decode freeBase boundNames
              (substitute_term_tree
                (Numbered.variable_token (free_name id))
                replacementTree tree) =
            some
              (Term.substituteFree SetSort.set id replacement term)
    | .atom token, term, hAvoid, hDecode => by
        by_cases hToken :
            token = Numbered.variable_token (free_name id)
        · subst token
          have hReplacementAvoids :
              term_tree_avoids_names boundNames replacementTree :=
            hAvoid (by simp [RawTermTokenTree.tokens])
          have hReplacementAt :
              fs_named_term_token_tree_decode
                  freeBase boundNames replacementTree =
                some replacement := by
            rw [fs_named_term_token_tree_decode_eq_empty_of_avoids
              freeBase boundNames replacementTree hReplacementAvoids]
            exact hReplacement
          have hTargetDecode :
              fs_named_term_token_tree_decode freeBase boundNames
                  (.atom
                    (Numbered.variable_token (free_name id))) =
                some (Term.var (.fvar SetSort.set id)) := by
            simp [fs_named_term_token_tree_decode,
              fs_named_variable_decode_free_name
                freeBase id boundNames hTargetFresh]
          have hTerm :
              term = Term.var (.fvar SetSort.set id) :=
            Option.some.inj (hDecode.symm.trans hTargetDecode)
          subst term
          simpa [substitute_term_tree, Term.substituteFree] using
            hReplacementAt
        · have hTargetNotFree :
              ¬(SetSort.set, id) ∈ term.freeSupport := by
            intro hFree
            have hMember :=
              fs_named_term_token_tree_decode_low_fvar_mem
                freeBase boundNames id hDecode hFree hId
            have hEquality :
                Numbered.variable_token (free_name id) = token := by
              simpa [RawTermTokenTree.tokens] using hMember
            exact hToken hEquality.symm
          have hSelf :
              Term.substituteFree SetSort.set id replacement term =
                term :=
            Term.substituteFree_eq_self_of_not_mem
              SetSort.set id replacement term hTargetNotFree
          simpa [substitute_term_tree, hToken, hSelf] using hDecode
    | .application head arguments, term, hAvoid, hDecode => by
        simp only [fs_named_term_token_tree_decode] at hDecode ⊢
        cases hSymbol :
            fs_find_encoded
              (fun candidate =>
                Numbered.function_token
                  (arguments.length - 1) candidate.ctorIdx)
              head fs_function_symbols with
        | none =>
            simp [hSymbol] at hDecode
        | some symbol =>
            cases hArguments :
                arguments.mapM
                  (fs_named_term_token_tree_decode
                    freeBase boundNames) with
            | none =>
                simp [hSymbol, hArguments] at hDecode
            | some decoded =>
                by_cases hSorted :
                    Term.check_args_wellSorted decoded
                      (signature.funcDomain symbol) = true
                · have hTerm :
                      arguments ≠ [] ∧
                        Term.app symbol decoded = term := by
                    simpa [hSymbol, hArguments, hSorted] using hDecode
                  rcases hTerm with
                    ⟨hArgumentsPositive, hTerm⟩
                  subst term
                  have hAvoidArguments :
                      Numbered.variable_token (free_name id) ∈
                          RawTermTokenTree.list_tokens arguments →
                        term_tree_avoids_names
                          boundNames replacementTree := by
                    intro hMember
                    apply hAvoid
                    simp [RawTermTokenTree.tokens, hMember]
                  have hDecoded :=
                    fs_named_term_token_trees_decode_substitute_free
                      freeBase id boundNames replacementTree replacement
                      hId hTargetFresh hReplacement
                      hReplacementWellSorted
                      arguments decoded hAvoidArguments hArguments
                  have hSorted' :
                      Term.check_args_wellSorted
                          (decoded.map
                            (Term.substituteFree
                              SetSort.set id replacement))
                          (signature.funcDomain symbol) = true :=
                    Term.check_args_wellSorted_complete <|
                      ArgsWellSorted.substituteFree
                        SetSort.set id hReplacementWellSorted <|
                          Term.check_args_wellSorted_sound hSorted
                  simp only [substitute_term_tree]
                  simp only [fs_named_term_token_tree_decode]
                  simp only [List.length_map]
                  rw [hSymbol, hDecoded]
                  simp [hArgumentsPositive, hSorted',
                    Term.substituteFree]
                · simp [hSymbol, hArguments, hSorted] at hDecode
  termination_by tree => sizeOf tree

  private theorem fs_named_term_token_trees_decode_substitute_free
      (freeBase id : Nat) (boundNames : List Nat)
      (replacementTree : RawTermTokenTree) (replacement : SetTerm)
      (hId : id < freeBase)
      (hTargetFresh : free_name id ∉ boundNames)
      (hReplacement :
        fs_named_term_token_tree_decode freeBase [] replacementTree =
          some replacement)
      (hReplacementWellSorted :
        TermWellSorted replacement SetSort.set) :
      ∀ trees terms,
        (Numbered.variable_token (free_name id) ∈
            RawTermTokenTree.list_tokens trees →
          term_tree_avoids_names boundNames replacementTree) →
        trees.mapM
            (fs_named_term_token_tree_decode freeBase boundNames) =
            some terms →
          (trees.map
              (substitute_term_tree
                (Numbered.variable_token (free_name id))
                replacementTree)).mapM
              (fs_named_term_token_tree_decode
                freeBase boundNames) =
            some
              (terms.map
                (Term.substituteFree SetSort.set id replacement))
    | .nil, terms, _, hDecode => by
        simp at hDecode
        subst terms
        rfl
    | .cons tree trees, terms, hAvoid, hDecode => by
        simp only [List.mapM_cons] at hDecode ⊢
        cases hTree :
            fs_named_term_token_tree_decode
              freeBase boundNames tree with
        | none =>
            simp [hTree] at hDecode
        | some term =>
            cases hTrees :
                trees.mapM
                  (fs_named_term_token_tree_decode
                    freeBase boundNames) with
            | none =>
                simp [hTree, hTrees] at hDecode
            | some decoded =>
                have hTerms : term :: decoded = terms := by
                  simpa [hTree, hTrees] using hDecode
                subst terms
                have hAvoidTree :
                    Numbered.variable_token (free_name id) ∈
                        tree.tokens →
                      term_tree_avoids_names
                        boundNames replacementTree := by
                  intro hMember
                  apply hAvoid
                  simp [RawTermTokenTree.list_tokens, hMember]
                have hAvoidTrees :
                    Numbered.variable_token (free_name id) ∈
                        RawTermTokenTree.list_tokens trees →
                      term_tree_avoids_names
                        boundNames replacementTree := by
                  intro hMember
                  apply hAvoid
                  simp [RawTermTokenTree.list_tokens, hMember]
                have hTree' :=
                  fs_named_term_token_tree_decode_substitute_free
                    freeBase id boundNames replacementTree replacement
                    hId hTargetFresh hReplacement
                    hReplacementWellSorted
                    tree term hAvoidTree hTree
                have hTrees' :=
                  fs_named_term_token_trees_decode_substitute_free
                    freeBase id boundNames replacementTree replacement
                    hId hTargetFresh hReplacement
                    hReplacementWellSorted
                    trees decoded hAvoidTrees hTrees
                simp [hTree', hTrees']
  termination_by trees => sizeOf trees
end

def fs_named_hilbert_tree_substitution_safe
    (target : Nat) (replacement : RawTermTokenTree) :
    RawHilbertTokenTree → Prop
  | .equality _ _ | .membership _ _ | .predicate _ _ => True
  | .negation body =>
      fs_named_hilbert_tree_substitution_safe target replacement body
  | .implication left right =>
      fs_named_hilbert_tree_substitution_safe target replacement left ∧
        fs_named_hilbert_tree_substitution_safe target replacement right
  | .universal variableToken body =>
      (target ∈ body.tokens →
        variableToken ∉ replacement.tokens) ∧
      fs_named_hilbert_tree_substitution_safe target replacement body

private theorem fs_named_hilbert_token_tree_decode_substitute_free
    (freeBase id : Nat) (boundNames : List Nat)
    (replacementTree : RawTermTokenTree) (replacement : SetTerm)
    (hId : id < freeBase)
    (hTargetFresh : free_name id ∉ boundNames)
    (hReplacement :
      fs_named_term_token_tree_decode freeBase [] replacementTree =
        some replacement)
    (hReplacementWellSorted :
      TermWellSorted replacement SetSort.set) :
    ∀ tree formula,
      fs_named_hilbert_tree_target_not_bound
          (Numbered.variable_token (free_name id)) tree →
      fs_named_hilbert_tree_substitution_safe
          (Numbered.variable_token (free_name id))
          replacementTree tree →
      (Numbered.variable_token (free_name id) ∈ tree.tokens →
        term_tree_avoids_names boundNames replacementTree) →
      fs_named_hilbert_token_tree_decode
          freeBase boundNames tree = some formula →
        fs_named_hilbert_token_tree_decode freeBase boundNames
            (substitute_hilbert_tree
              (Numbered.variable_token (free_name id))
              replacementTree tree) =
          some
            (Formula.substituteFree
              SetSort.set id replacement formula)
  | .equality left right, formula, _, _, hAvoid, hDecode => by
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hLeft :
          fs_named_term_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [hLeft] at hDecode
      | some leftTerm =>
          cases hRight :
              fs_named_term_token_tree_decode
                freeBase boundNames right with
          | none =>
              simp [hLeft, hRight] at hDecode
          | some rightTerm =>
              have hDecodedData :
                  (Term.check_wellSorted SetSort.set leftTerm = true ∧
                    Term.check_wellSorted SetSort.set rightTerm = true) ∧
                  leftTerm ≐ₘ rightTerm = formula := by
                simpa [hLeft, hRight] using hDecode
              rcases hDecodedData with
                ⟨⟨hLeftSorted, hRightSorted⟩, hFormula⟩
              subst formula
              have hAvoidLeft :
                  Numbered.variable_token (free_name id) ∈
                      left.tokens →
                    term_tree_avoids_names
                      boundNames replacementTree := by
                intro hMember
                apply hAvoid
                simp [RawHilbertTokenTree.tokens, hMember]
              have hAvoidRight :
                  Numbered.variable_token (free_name id) ∈
                      right.tokens →
                    term_tree_avoids_names
                      boundNames replacementTree := by
                intro hMember
                apply hAvoid
                simp [RawHilbertTokenTree.tokens, hMember]
              have hLeft' :=
                fs_named_term_token_tree_decode_substitute_free
                  freeBase id boundNames replacementTree replacement
                  hId hTargetFresh hReplacement
                  hReplacementWellSorted
                  left leftTerm hAvoidLeft hLeft
              have hRight' :=
                fs_named_term_token_tree_decode_substitute_free
                  freeBase id boundNames replacementTree replacement
                  hId hTargetFresh hReplacement
                  hReplacementWellSorted
                  right rightTerm hAvoidRight hRight
              have hLeftSorted' :
                  Term.check_wellSorted SetSort.set
                      (Term.substituteFree
                        SetSort.set id replacement leftTerm) =
                    true :=
                Term.check_wellSorted_complete <|
                  TermWellSorted.substituteFree id
                    (Term.check_wellSorted_sound hLeftSorted)
                    hReplacementWellSorted
              have hRightSorted' :
                  Term.check_wellSorted SetSort.set
                      (Term.substituteFree
                        SetSort.set id replacement rightTerm) =
                    true :=
                Term.check_wellSorted_complete <|
                  TermWellSorted.substituteFree id
                    (Term.check_wellSorted_sound hRightSorted)
                    hReplacementWellSorted
              simp only [substitute_hilbert_tree]
              simp only [fs_named_hilbert_token_tree_decode]
              rw [hLeft', hRight']
              simp [hLeftSorted', hRightSorted',
                Formula.substituteFree]
  | .membership left right, formula, _, _, hAvoid, hDecode => by
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hLeft :
          fs_named_term_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [hLeft] at hDecode
      | some leftTerm =>
          cases hRight :
              fs_named_term_token_tree_decode
                freeBase boundNames right with
          | none =>
              simp [hLeft, hRight] at hDecode
          | some rightTerm =>
              have hDecodedData :
                  Term.check_args_wellSorted [leftTerm, rightTerm]
                      (signature.relDomain RelationSymbol.membership) =
                      true ∧
                    Formula.rel RelationSymbol.membership
                        [leftTerm, rightTerm] =
                      formula := by
                simpa [hLeft, hRight] using hDecode
              rcases hDecodedData with ⟨hSorted, hFormula⟩
              subst formula
              have hAvoidLeft :
                  Numbered.variable_token (free_name id) ∈
                      left.tokens →
                    term_tree_avoids_names
                      boundNames replacementTree := by
                intro hMember
                apply hAvoid
                simp [RawHilbertTokenTree.tokens, hMember]
              have hAvoidRight :
                  Numbered.variable_token (free_name id) ∈
                      right.tokens →
                    term_tree_avoids_names
                      boundNames replacementTree := by
                intro hMember
                apply hAvoid
                simp [RawHilbertTokenTree.tokens, hMember]
              have hLeft' :=
                fs_named_term_token_tree_decode_substitute_free
                  freeBase id boundNames replacementTree replacement
                  hId hTargetFresh hReplacement
                  hReplacementWellSorted
                  left leftTerm hAvoidLeft hLeft
              have hRight' :=
                fs_named_term_token_tree_decode_substitute_free
                  freeBase id boundNames replacementTree replacement
                  hId hTargetFresh hReplacement
                  hReplacementWellSorted
                  right rightTerm hAvoidRight hRight
              have hSortedMap :
                  Term.check_args_wellSorted
                      ([leftTerm, rightTerm].map
                        (Term.substituteFree
                          SetSort.set id replacement))
                      (signature.relDomain
                        RelationSymbol.membership) = true :=
                Term.check_args_wellSorted_complete <|
                  ArgsWellSorted.substituteFree
                    SetSort.set id hReplacementWellSorted <|
                      Term.check_args_wellSorted_sound hSorted
              have hSorted' :
                  Term.check_args_wellSorted
                      [Term.substituteFree
                          SetSort.set id replacement leftTerm,
                        Term.substituteFree
                          SetSort.set id replacement rightTerm]
                      (signature.relDomain
                        RelationSymbol.membership) = true := by
                simpa using hSortedMap
              simp only [substitute_hilbert_tree]
              simp only [fs_named_hilbert_token_tree_decode]
              rw [hLeft', hRight']
              simp [hSorted', Formula.substituteFree]
  | .predicate head arguments, formula, _, _, hAvoid, hDecode => by
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hRelation :
          fs_find_encoded
            (fun candidate =>
              Numbered.predicate_token
                (arguments.length - 1) candidate.ctorIdx)
            head fs_relation_symbols with
      | none =>
          simp [hRelation] at hDecode
      | some relation =>
          cases hKind :
              fs_relation_kind relation with
          | membership =>
              simp [hRelation, hKind] at hDecode
          | predicate =>
              cases hArguments :
                  arguments.mapM
                    (fs_named_term_token_tree_decode
                      freeBase boundNames) with
              | none =>
                  simp [hRelation, hArguments] at hDecode
              | some decoded =>
                  have hDecodedData :
                      Term.check_args_wellSorted decoded
                          (signature.relDomain relation) = true ∧
                        Formula.rel relation decoded = formula := by
                    simpa [hRelation, hKind, hArguments] using hDecode
                  rcases hDecodedData with ⟨hSorted, hFormula⟩
                  subst formula
                  have hAvoidArguments :
                      Numbered.variable_token (free_name id) ∈
                          RawTermTokenTree.list_tokens arguments →
                        term_tree_avoids_names
                          boundNames replacementTree := by
                    intro hMember
                    apply hAvoid
                    simp [RawHilbertTokenTree.tokens, hMember]
                  have hArguments' :=
                    fs_named_term_token_trees_decode_substitute_free
                      freeBase id boundNames replacementTree replacement
                      hId hTargetFresh hReplacement
                      hReplacementWellSorted
                      arguments decoded hAvoidArguments hArguments
                  have hSorted' :
                      Term.check_args_wellSorted
                          (decoded.map
                            (Term.substituteFree
                              SetSort.set id replacement))
                          (signature.relDomain relation) = true :=
                    Term.check_args_wellSorted_complete <|
                      ArgsWellSorted.substituteFree
                        SetSort.set id hReplacementWellSorted <|
                          Term.check_args_wellSorted_sound hSorted
                  simp only [substitute_hilbert_tree]
                  simp only [fs_named_hilbert_token_tree_decode]
                  simp only [List.length_map]
                  rw [hRelation]
                  simp [hKind, hArguments', hSorted',
                    Formula.substituteFree]
  | .negation body, formula, hNotBound, hSafe, hAvoid, hDecode => by
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hBody :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames body with
      | none =>
          simp [hBody] at hDecode
      | some bodyFormula =>
          have hFormula : ¬ₘ bodyFormula = formula := by
            simpa [hBody] using hDecode
          subst formula
          have hAvoidBody :
              Numbered.variable_token (free_name id) ∈ body.tokens →
                term_tree_avoids_names
                  boundNames replacementTree := by
            intro hMember
            apply hAvoid
            simp [RawHilbertTokenTree.tokens, hMember]
          have hBody' :=
            fs_named_hilbert_token_tree_decode_substitute_free
              freeBase id boundNames replacementTree replacement
              hId hTargetFresh hReplacement hReplacementWellSorted
              body bodyFormula hNotBound hSafe hAvoidBody hBody
          simp [substitute_hilbert_tree,
            fs_named_hilbert_token_tree_decode, hBody',
            Formula.substituteFree]
  | .implication left right, formula,
      hNotBound, hSafe, hAvoid, hDecode => by
      simp [fs_named_hilbert_tree_target_not_bound] at hNotBound
      simp [fs_named_hilbert_tree_substitution_safe] at hSafe
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hLeft :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [hLeft] at hDecode
      | some leftFormula =>
          cases hRight :
              fs_named_hilbert_token_tree_decode
                freeBase boundNames right with
          | none =>
              simp [hLeft, hRight] at hDecode
          | some rightFormula =>
              have hFormula :
                  leftFormula ⟶ₘ rightFormula = formula := by
                simpa [hLeft, hRight] using hDecode
              subst formula
              have hAvoidLeft :
                  Numbered.variable_token (free_name id) ∈
                      left.tokens →
                    term_tree_avoids_names
                      boundNames replacementTree := by
                intro hMember
                apply hAvoid
                simp [RawHilbertTokenTree.tokens, hMember]
              have hAvoidRight :
                  Numbered.variable_token (free_name id) ∈
                      right.tokens →
                    term_tree_avoids_names
                      boundNames replacementTree := by
                intro hMember
                apply hAvoid
                simp [RawHilbertTokenTree.tokens, hMember]
              have hLeft' :=
                fs_named_hilbert_token_tree_decode_substitute_free
                  freeBase id boundNames replacementTree replacement
                  hId hTargetFresh hReplacement hReplacementWellSorted
                  left leftFormula hNotBound.1 hSafe.1
                  hAvoidLeft hLeft
              have hRight' :=
                fs_named_hilbert_token_tree_decode_substitute_free
                  freeBase id boundNames replacementTree replacement
                  hId hTargetFresh hReplacement hReplacementWellSorted
                  right rightFormula hNotBound.2 hSafe.2
                  hAvoidRight hRight
              simp [substitute_hilbert_tree,
                fs_named_hilbert_token_tree_decode,
                hLeft', hRight', Formula.substituteFree]
  | .universal variableToken body, formula,
      hNotBound, hSafe, hAvoid, hDecode => by
      simp [fs_named_hilbert_tree_target_not_bound] at hNotBound
      simp [fs_named_hilbert_tree_substitution_safe] at hSafe
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hName : fs_variable_name_decode variableToken with
      | none =>
          simp [hName] at hDecode
      | some name =>
          cases hBody :
              fs_named_hilbert_token_tree_decode
                freeBase (name :: boundNames) body with
          | none =>
              simp [hName, hBody] at hDecode
          | some bodyFormula =>
              have hFormula :
                  (∀ₘ[SetSort.set], bodyFormula) = formula := by
                simpa [hName, hBody] using hDecode
              subst formula
              have hVariableValue :
                  Numbered.variable_token name = variableToken :=
                fs_variable_name_decode_value_of_some hName
              have hNameNe : name ≠ free_name id := by
                intro hEquality
                subst name
                exact hNotBound.1 hVariableValue.symm
              have hTargetFresh' :
                  free_name id ∉ name :: boundNames := by
                simp [hNameNe.symm, hTargetFresh]
              have hAvoidBody :
                  Numbered.variable_token (free_name id) ∈
                      body.tokens →
                    term_tree_avoids_names
                      (name :: boundNames) replacementTree := by
                intro hTarget
                have hOuterAvoid :
                    term_tree_avoids_names
                      boundNames replacementTree := by
                  apply hAvoid
                  simp [RawHilbertTokenTree.tokens, hTarget]
                intro candidate hCandidate hCandidateToken
                rcases List.mem_cons.mp hCandidate with
                  rfl | hCandidate
                · apply hSafe.1 hTarget
                  simpa [hVariableValue] using hCandidateToken
                · exact hOuterAvoid
                    candidate hCandidate hCandidateToken
              have hBody' :=
                fs_named_hilbert_token_tree_decode_substitute_free
                  freeBase id (name :: boundNames)
                  replacementTree replacement
                  hId hTargetFresh' hReplacement
                  hReplacementWellSorted
                  body bodyFormula hNotBound.2 hSafe.2
                  hAvoidBody hBody
              simp [substitute_hilbert_tree,
                fs_named_hilbert_token_tree_decode,
                hName, hBody', Formula.substituteFree]
termination_by tree => sizeOf tree

/--
成功具名解码的树中若目标变量确实被某个 binder 绑定，
则给出该 binder 的标准 token 中段、其对象层名字以及体树解码。
这是失败适配器使用的有限结构见证，不是新的反演层。
-/
theorem fs_named_hilbert_tree_target_bound_witness_of_decode
    (freeBase : Nat) (boundNames : List Nat) (target : Nat) :
    ∀ {tree : RawHilbertTokenTree} {formula : SetFormula},
      ¬ fs_named_hilbert_tree_target_not_bound target tree →
        fs_named_hilbert_token_tree_decode
            freeBase boundNames tree = some formula →
          ∃ prefixTokens bodyTree suffixTokens name bodyFormula bodyBoundNames,
            tree.tokens =
              prefixTokens ++
                Numbered.universal_tokens name bodyTree.tokens ++
                  suffixTokens ∧
            Numbered.variable_token name = target ∧
            fs_named_hilbert_token_tree_decode
                freeBase bodyBoundNames bodyTree =
              some bodyFormula
  | .equality left right, _, hNotBound, _ => by
      simp [fs_named_hilbert_tree_target_not_bound] at hNotBound
  | .membership left right, _, hNotBound, _ => by
      simp [fs_named_hilbert_tree_target_not_bound] at hNotBound
  | .predicate head arguments, _, hNotBound, _ => by
      simp [fs_named_hilbert_tree_target_not_bound] at hNotBound
  | .negation body, formula, hNotBound, hDecode => by
      have hBodyNotBound :
          ¬ fs_named_hilbert_tree_target_not_bound
              target body := by
        simpa [fs_named_hilbert_tree_target_not_bound] using hNotBound
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hBody :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames body with
      | none =>
          simp [hBody] at hDecode
      | some bodyFormula =>
          rcases
              fs_named_hilbert_tree_target_bound_witness_of_decode
                freeBase boundNames target hBodyNotBound hBody with
            ⟨prefixTokens, bodyTree, suffixTokens, name,
              bodyFormula', bodyBoundNames, hShape, hTarget, hBody'⟩
          refine ⟨
            [Numbered.logical_token .leftParenthesis,
              Numbered.logical_token .negation] ++ prefixTokens,
            bodyTree, (suffixTokens ++
              [Numbered.logical_token .rightParenthesis]),
            name, bodyFormula', bodyBoundNames, ?_, hTarget, hBody'⟩
          simp [RawHilbertTokenTree.tokens, hShape,
            List.append_assoc]
  | .implication left right, formula, hNotBound, hDecode => by
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hLeft :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [hLeft] at hDecode
      | some leftFormula =>
          cases hRight :
              fs_named_hilbert_token_tree_decode
                freeBase boundNames right with
          | none =>
              simp [hLeft, hRight] at hDecode
          | some rightFormula =>
              by_cases hLeftBound :
                  fs_named_hilbert_tree_target_not_bound
                    target left
              · have hRightNotBound :
                    ¬ fs_named_hilbert_tree_target_not_bound
                        target right := by
                  intro hRightBound
                  apply hNotBound
                  exact ⟨hLeftBound, hRightBound⟩
                rcases
                    fs_named_hilbert_tree_target_bound_witness_of_decode
                      freeBase boundNames target
                      hRightNotBound hRight with
                  ⟨prefixTokens, bodyTree, suffixTokens, name,
                    bodyFormula', bodyBoundNames, hShape, hTarget, hBody⟩
                refine ⟨
                  [Numbered.logical_token .leftParenthesis] ++
                    left.tokens ++
                      [Numbered.logical_token .implication] ++
                        prefixTokens,
                  bodyTree,
                  (suffixTokens ++
                    [Numbered.logical_token .rightParenthesis]),
                  name, bodyFormula', bodyBoundNames, ?_, hTarget, hBody⟩
                simp [RawHilbertTokenTree.tokens,
                  hShape,
                  List.append_assoc]
              · have hLeftNotBound :
                    ¬ fs_named_hilbert_tree_target_not_bound
                        target left :=
                  hLeftBound
                rcases
                  fs_named_hilbert_tree_target_bound_witness_of_decode
                    freeBase boundNames target
                    hLeftNotBound hLeft with
                  ⟨prefixTokens, bodyTree, suffixTokens, name,
                    bodyFormula', bodyBoundNames, hShape, hTarget, hBody⟩
                refine ⟨
                  [Numbered.logical_token .leftParenthesis] ++
                    prefixTokens,
                  bodyTree,
                  (suffixTokens ++
                    [Numbered.logical_token .implication] ++
                      right.tokens ++
                        [Numbered.logical_token .rightParenthesis]),
                  name, bodyFormula', bodyBoundNames, ?_, hTarget, hBody⟩
                simp [RawHilbertTokenTree.tokens,
                  hShape,
                  List.append_assoc]
  | .universal variableToken body, formula, hNotBound, hDecode => by
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hName :
          fs_variable_name_decode variableToken with
      | none =>
          simp [hName] at hDecode
      | some name =>
          cases hBody :
              fs_named_hilbert_token_tree_decode
                freeBase (name :: boundNames) body with
          | none =>
              simp [hName, hBody] at hDecode
          | some bodyFormula =>
              have hVariableValue :
                  Numbered.variable_token name = variableToken :=
                fs_variable_name_decode_value_of_some hName
              by_cases hSame : variableToken = target
              · refine ⟨([] : List Nat), body, ([] : List Nat),
                  name, bodyFormula, (name :: boundNames), ?_,
                  hVariableValue.trans hSame, hBody⟩
                simp [RawHilbertTokenTree.tokens,
                  Numbered.universal_tokens, hVariableValue]
              · have hBodyNotBound :
                    ¬ fs_named_hilbert_tree_target_not_bound
                        target body := by
                  intro hBodyBound
                  apply hNotBound
                  simp [fs_named_hilbert_tree_target_not_bound,
                    hSame, hBodyBound]
                rcases
                    fs_named_hilbert_tree_target_bound_witness_of_decode
                      freeBase (name :: boundNames) target
                      hBodyNotBound hBody with
                  ⟨prefixTokens, bodyTree, suffixTokens, name',
                    bodyFormula', bodyBoundNames, hShape,
                    hTarget, hBody'⟩
                refine ⟨
                  [Numbered.logical_token .leftParenthesis,
                    Numbered.logical_token .universal,
                    variableToken] ++ prefixTokens,
                  bodyTree,
                  (suffixTokens ++
                    [Numbered.logical_token .rightParenthesis]),
                  name', bodyFormula', bodyBoundNames, ?_, hTarget, hBody'⟩
                simp [RawHilbertTokenTree.tokens,
                  hShape, List.append_assoc]
termination_by tree => sizeOf tree

/--
成功具名解码的树若不满足替换安全性，则存在一个具体全称 binder：
目标 token 出现在其体内，而该 binder 的变量 token 出现在替换项中。
该定理只为失败适配器提供有限反例，不扩展成功反演层。
-/
theorem fs_named_hilbert_tree_substitution_unsafe_witness_of_decode
    (freeBase : Nat) (boundNames : List Nat)
    (target : Nat) (replacement : RawTermTokenTree) :
    ∀ {tree : RawHilbertTokenTree} {formula : SetFormula},
      ¬ fs_named_hilbert_tree_substitution_safe
          target replacement tree →
        fs_named_hilbert_token_tree_decode
            freeBase boundNames tree = some formula →
          ∃ prefixTokens bodyTree suffixTokens name bodyFormula bodyBoundNames,
            tree.tokens =
              prefixTokens ++
                Numbered.universal_tokens name bodyTree.tokens ++
                  suffixTokens ∧
            target ∈ bodyTree.tokens ∧
            Numbered.variable_token name ∈ replacement.tokens ∧
            fs_named_hilbert_token_tree_decode
                freeBase bodyBoundNames bodyTree =
              some bodyFormula
  | .equality left right, _, hUnsafe, _ => by
      simp [fs_named_hilbert_tree_substitution_safe] at hUnsafe
  | .membership left right, _, hUnsafe, _ => by
      simp [fs_named_hilbert_tree_substitution_safe] at hUnsafe
  | .predicate head arguments, _, hUnsafe, _ => by
      simp [fs_named_hilbert_tree_substitution_safe] at hUnsafe
  | .negation body, formula, hUnsafe, hDecode => by
      have hBodyUnsafe :
          ¬ fs_named_hilbert_tree_substitution_safe
              target replacement body := by
        simpa [fs_named_hilbert_tree_substitution_safe] using hUnsafe
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hBody :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames body with
      | none =>
          simp [hBody] at hDecode
      | some bodyFormula =>
          rcases
              fs_named_hilbert_tree_substitution_unsafe_witness_of_decode
                freeBase boundNames target replacement
                hBodyUnsafe hBody with
            ⟨prefixTokens, bodyTree, suffixTokens, name,
              bodyFormula', bodyBoundNames, hShape,
              hTarget, hReplacement, hBody'⟩
          refine ⟨
            [Numbered.logical_token .leftParenthesis,
              Numbered.logical_token .negation] ++ prefixTokens,
            bodyTree,
            (suffixTokens ++
              [Numbered.logical_token .rightParenthesis]),
            name, bodyFormula', bodyBoundNames, ?_,
            hTarget, hReplacement, hBody'⟩
          simp [RawHilbertTokenTree.tokens, hShape,
            List.append_assoc]
  | .implication left right, formula, hUnsafe, hDecode => by
      change ¬ (
        fs_named_hilbert_tree_substitution_safe
            target replacement left ∧
          fs_named_hilbert_tree_substitution_safe
            target replacement right) at hUnsafe
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hLeft :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [hLeft] at hDecode
      | some leftFormula =>
          cases hRight :
              fs_named_hilbert_token_tree_decode
                freeBase boundNames right with
          | none =>
              simp [hLeft, hRight] at hDecode
          | some rightFormula =>
              by_cases hLeftSafe :
                  fs_named_hilbert_tree_substitution_safe
                    target replacement left
              · have hRightUnsafe :
                    ¬ fs_named_hilbert_tree_substitution_safe
                        target replacement right := by
                  intro hRightSafe
                  exact hUnsafe ⟨hLeftSafe, hRightSafe⟩
                rcases
                    fs_named_hilbert_tree_substitution_unsafe_witness_of_decode
                      freeBase boundNames target replacement
                      hRightUnsafe hRight with
                  ⟨prefixTokens, bodyTree, suffixTokens, name,
                    bodyFormula', bodyBoundNames, hShape,
                    hTarget, hReplacement, hBody⟩
                refine ⟨
                  [Numbered.logical_token .leftParenthesis] ++
                    left.tokens ++
                      [Numbered.logical_token .implication] ++
                        prefixTokens,
                  bodyTree,
                  (suffixTokens ++
                    [Numbered.logical_token .rightParenthesis]),
                  name, bodyFormula', bodyBoundNames, ?_,
                  hTarget, hReplacement, hBody⟩
                simp [RawHilbertTokenTree.tokens,
                  hShape,
                  List.append_assoc]
              · rcases
                    fs_named_hilbert_tree_substitution_unsafe_witness_of_decode
                      freeBase boundNames target replacement
                      hLeftSafe hLeft with
                  ⟨prefixTokens, bodyTree, suffixTokens, name,
                    bodyFormula', bodyBoundNames, hShape,
                    hTarget, hReplacement, hBody⟩
                refine ⟨
                  [Numbered.logical_token .leftParenthesis] ++
                    prefixTokens,
                  bodyTree,
                  (suffixTokens ++
                    [Numbered.logical_token .implication] ++
                      right.tokens ++
                        [Numbered.logical_token .rightParenthesis]),
                  name, bodyFormula', bodyBoundNames, ?_,
                  hTarget, hReplacement, hBody⟩
                simp [RawHilbertTokenTree.tokens,
                  hShape,
                  List.append_assoc]
  | .universal variableToken body, formula, hUnsafe, hDecode => by
      change ¬ (
        (target ∈ body.tokens →
          variableToken ∉ replacement.tokens) ∧
        fs_named_hilbert_tree_substitution_safe
          target replacement body) at hUnsafe
      simp only [fs_named_hilbert_token_tree_decode] at hDecode
      cases hName :
          fs_variable_name_decode variableToken with
      | none =>
          simp [hName] at hDecode
      | some name =>
          cases hBody :
              fs_named_hilbert_token_tree_decode
                freeBase (name :: boundNames) body with
          | none =>
              simp [hName, hBody] at hDecode
          | some bodyFormula =>
              have hVariableValue :
                  Numbered.variable_token name = variableToken :=
                fs_variable_name_decode_value_of_some hName
              by_cases hTarget : target ∈ body.tokens
              · by_cases hReplacement :
                    Numbered.variable_token name ∈ replacement.tokens
                · refine ⟨([] : List Nat), body, ([] : List Nat),
                    name, bodyFormula, (name :: boundNames), ?_,
                    hTarget, hReplacement, hBody⟩
                  simp [RawHilbertTokenTree.tokens,
                    Numbered.universal_tokens, hVariableValue]
                · have hOuter :
                      target ∈ body.tokens →
                        variableToken ∉ replacement.tokens := by
                    intro _
                    simpa [hVariableValue] using hReplacement
                  have hBodyUnsafe :
                      ¬ fs_named_hilbert_tree_substitution_safe
                          target replacement body := by
                    intro hBodySafe
                    exact hUnsafe ⟨hOuter, hBodySafe⟩
                  rcases
                      fs_named_hilbert_tree_substitution_unsafe_witness_of_decode
                        freeBase (name :: boundNames)
                        target replacement hBodyUnsafe hBody with
                    ⟨prefixTokens, bodyTree, suffixTokens, name',
                      bodyFormula', bodyBoundNames, hShape,
                      hTarget', hReplacement', hBody'⟩
                  refine ⟨
                    [Numbered.logical_token .leftParenthesis,
                      Numbered.logical_token .universal,
                      variableToken] ++ prefixTokens,
                    bodyTree,
                    (suffixTokens ++
                      [Numbered.logical_token .rightParenthesis]),
                    name', bodyFormula', bodyBoundNames, ?_,
                    hTarget', hReplacement', hBody'⟩
                  simp [RawHilbertTokenTree.tokens,
                    hShape, List.append_assoc]
              · have hOuter :
                    target ∈ body.tokens →
                      variableToken ∉ replacement.tokens := by
                  intro hTarget'
                  exact False.elim (hTarget hTarget')
                have hBodyUnsafe :
                    ¬ fs_named_hilbert_tree_substitution_safe
                        target replacement body := by
                  intro hBodySafe
                  exact hUnsafe ⟨hOuter, hBodySafe⟩
                rcases
                    fs_named_hilbert_tree_substitution_unsafe_witness_of_decode
                      freeBase (name :: boundNames)
                      target replacement hBodyUnsafe hBody with
                  ⟨prefixTokens, bodyTree, suffixTokens, name',
                    bodyFormula', bodyBoundNames, hShape,
                    hTarget', hReplacement', hBody'⟩
                refine ⟨
                  [Numbered.logical_token .leftParenthesis,
                    Numbered.logical_token .universal,
                    variableToken] ++ prefixTokens,
                  bodyTree,
                  (suffixTokens ++
                    [Numbered.logical_token .rightParenthesis]),
                  name', bodyFormula', bodyBoundNames, ?_,
                  hTarget', hReplacement', hBody'⟩
                simp [RawHilbertTokenTree.tokens,
                  hShape, List.append_assoc]
termination_by tree => sizeOf tree

theorem fs_named_hilbert_tokens_decode_with_env_substitute_free_of_trees
    (freeBase id : Nat)
    (sourceTokens replacementTokens : List Nat)
    (sourceTree : RawHilbertTokenTree)
    (replacementTree : RawTermTokenTree)
    (formula : SetFormula) (replacement : SetTerm)
    (hId : id < freeBase)
    (hSourceParse :
      RawHilbertTokenTree.parse? sourceTokens = some sourceTree)
    (hReplacementParse :
      RawTermTokenTree.parse? replacementTokens =
        some replacementTree)
    (hSource :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] sourceTokens = some formula)
    (hReplacement :
      fs_named_term_tokens_decode_with_env
          freeBase [] replacementTokens = some replacement)
    (hReplacementWellSorted :
      TermWellSorted replacement SetSort.set)
    (hNotBound :
      fs_named_hilbert_tree_target_not_bound
        (Numbered.variable_token (free_name id)) sourceTree)
    (hSafe :
      fs_named_hilbert_tree_substitution_safe
        (Numbered.variable_token (free_name id))
        replacementTree sourceTree) :
    fs_named_hilbert_tokens_decode_with_env freeBase []
        (substitute_tokens sourceTokens
          (Numbered.variable_token (free_name id))
          replacementTokens) =
      some
        (Formula.substituteFree
          SetSort.set id replacement formula) := by
  have hSourceTreeDecode :
      fs_named_hilbert_token_tree_decode
          freeBase [] sourceTree = some formula := by
    simpa [fs_named_hilbert_tokens_decode_with_env,
      hSourceParse] using hSource
  have hReplacementTreeDecode :
      fs_named_term_token_tree_decode
          freeBase [] replacementTree = some replacement := by
    simpa [fs_named_term_tokens_decode_with_env,
      hReplacementParse] using hReplacement
  have hSubstitutedDecode :=
    fs_named_hilbert_token_tree_decode_substitute_free
      freeBase id [] replacementTree replacement
      hId (by simp) hReplacementTreeDecode
      hReplacementWellSorted
      sourceTree formula hNotBound hSafe
      (by
        intro _
        intro name hName
        simp at hName)
      hSourceTreeDecode
  have hSeparated :
      hilbert_tree_target_separated
        (Numbered.variable_token (free_name id)) sourceTree :=
    hilbert_tree_target_separated_of_decode
      freeBase [] (free_name id)
      sourceTree formula hNotBound hSourceTreeDecode
  have hSourceTokens :
      sourceTree.tokens = sourceTokens :=
    RawHilbertTokenTree.parse?_sound hSourceParse
  have hReplacementTokens :
      replacementTree.tokens = replacementTokens :=
    RawTermTokenTree.parse?_sound hReplacementParse
  have hSubstitutedTokens :
      (substitute_hilbert_tree
          (Numbered.variable_token (free_name id))
          replacementTree sourceTree).tokens =
        substitute_tokens sourceTokens
          (Numbered.variable_token (free_name id))
          replacementTokens := by
    simpa [hSourceTokens] using
      substitute_hilbert_tree_tokens
        (free_name id) replacementTree replacementTokens
        hReplacementTokens sourceTree hSeparated
  have hSubstitutedLexicallySeparated :
      (substitute_hilbert_tree
          (Numbered.variable_token (free_name id))
          replacementTree sourceTree).LexicallySeparated :=
    fs_named_hilbert_token_tree_decode_lexically_separated
      freeBase hSubstitutedDecode
  have hSubstitutedParse :
      RawHilbertTokenTree.parse?
          (substitute_tokens sourceTokens
            (Numbered.variable_token (free_name id))
            replacementTokens) =
        some
          (substitute_hilbert_tree
            (Numbered.variable_token (free_name id))
            replacementTree sourceTree) := by
    rw [← hSubstitutedTokens]
    exact RawHilbertTokenTree.parse?_tokens _
      hSubstitutedLexicallySeparated
  simpa [fs_named_hilbert_tokens_decode_with_env,
    hSubstitutedParse] using hSubstitutedDecode

end YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation
