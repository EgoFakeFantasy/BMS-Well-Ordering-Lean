import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoderComposition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.CanonicalBinderShift.Core

/-!
# 具名解码与规范 binder 平移

本模块只证明一个纯外部计算事实：把任意成功具名解码中的偶数变量名保持不变、
奇数变量名统一后移两个单位，并在环境末端加入新的最外层 binder 后，解码结果
不变。该结论供对象层失败适配器识别规范全称闭包使用。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory

set_option autoImplicit false

/-- 偶数自由名保持不变，奇数 binder 名后移一层。 -/
def fs_named_binder_shift_name (name : Nat) : Nat :=
  if name % 2 = 0 then name else name + 2

private theorem fs_named_binder_shift_name_mod (name : Nat) :
    fs_named_binder_shift_name name % 2 = name % 2 := by
  by_cases h : name % 2 = 0
  · simp [fs_named_binder_shift_name, h]
  · have hOdd : name % 2 = 1 := by omega
    simp [fs_named_binder_shift_name, hOdd]

private theorem fs_named_binder_shift_name_injective :
    Function.Injective fs_named_binder_shift_name := by
  intro left right hEqual
  have hMod := congrArg (fun value => value % 2) hEqual
  change
    fs_named_binder_shift_name left % 2 =
      fs_named_binder_shift_name right % 2 at hMod
  rw [fs_named_binder_shift_name_mod,
    fs_named_binder_shift_name_mod] at hMod
  by_cases hLeft : left % 2 = 0
  · have hRight : right % 2 = 0 := by omega
    simpa [fs_named_binder_shift_name, hLeft, hRight] using hEqual
  · have hRight : right % 2 ≠ 0 := by omega
    simp [fs_named_binder_shift_name, hLeft, hRight] at hEqual
    omega

private theorem fs_named_binder_shift_name_ne_outer (name : Nat) :
    fs_named_binder_shift_name name ≠ bound_name 0 := by
  by_cases h : name % 2 = 0
  · intro hEqual
    have hMod := congrArg (fun value => value % 2) hEqual
    change
      fs_named_binder_shift_name name % 2 =
        bound_name 0 % 2 at hMod
    rw [fs_named_binder_shift_name_mod] at hMod
    simp [bound_name, h] at hMod
  · intro hEqual
    simp [fs_named_binder_shift_name, h, bound_name] at hEqual

/-- 逐项树执行具名 binder 平移。 -/
def fs_named_term_token_tree_binder_shift :
    RawTermTokenTree → RawTermTokenTree
  | .atom token =>
      match fs_variable_name_decode token with
      | some name =>
          .atom (Numbered.variable_token
            (fs_named_binder_shift_name name))
      | none =>
          .atom token
  | .application head arguments =>
      .application head
        (arguments.map fs_named_term_token_tree_binder_shift)

/-- 逐公式树执行具名 binder 平移。 -/
def fs_named_hilbert_token_tree_binder_shift :
    RawHilbertTokenTree → RawHilbertTokenTree
  | .equality left right =>
      .equality
        (fs_named_term_token_tree_binder_shift left)
        (fs_named_term_token_tree_binder_shift right)
  | .membership left right =>
      .membership
        (fs_named_term_token_tree_binder_shift left)
        (fs_named_term_token_tree_binder_shift right)
  | .predicate head arguments =>
      .predicate head
        (arguments.map fs_named_term_token_tree_binder_shift)
  | .negation body =>
      .negation
        (fs_named_hilbert_token_tree_binder_shift body)
  | .implication left right =>
      .implication
        (fs_named_hilbert_token_tree_binder_shift left)
        (fs_named_hilbert_token_tree_binder_shift right)
  | .universal variableToken body =>
      .universal
        (match fs_variable_name_decode variableToken with
        | some name =>
            Numbered.variable_token
              (fs_named_binder_shift_name name)
        | none =>
            variableToken)
        (fs_named_hilbert_token_tree_binder_shift body)

private theorem fs_named_variable_shift_relation
    {token name : Nat}
    (hName : fs_variable_name_decode token = some name) :
    CanonicalBinderShiftToken token
      (Numbered.variable_token
        (fs_named_binder_shift_name name)) := by
  have hToken :
      Numbered.variable_token name = token :=
    fs_variable_name_decode_value_of_some hName
  by_cases hEven : name % 2 = 0
  · have hNameValue : free_name (name / 2) = name := by
      have hDiv := Nat.mod_add_div name 2
      simp [free_name, hEven] at hDiv ⊢
      omega
    rw [← hToken, ← hNameValue]
    simpa [fs_named_binder_shift_name, free_name] using
      (CanonicalBinderShiftToken.free (name / 2))
  · have hOdd : name % 2 = 1 := by omega
    have hNameValue : bound_name (name / 2) = name := by
      have hDiv := Nat.mod_add_div name 2
      simp [bound_name, hOdd] at hDiv ⊢
      omega
    rw [← hToken, ← hNameValue]
    simpa [fs_named_binder_shift_name, bound_name] using
      (CanonicalBinderShiftToken.bound (name / 2))

mutual
  private theorem fs_named_term_token_tree_binder_shift_relation
      (freeBase : Nat) (boundNames : List Nat) :
      ∀ {tree : RawTermTokenTree} {term : SetTerm},
        fs_named_term_token_tree_decode
            freeBase boundNames tree = some term →
        CanonicalBinderShiftTokens tree.tokens
          (fs_named_term_token_tree_binder_shift tree).tokens
    | .atom token, term, hDecode => by
        cases hVariable :
            fs_named_variable_decode freeBase boundNames token with
        | some decodedVariable =>
            unfold fs_named_variable_decode at hVariable
            cases hName : fs_variable_name_decode token with
            | none =>
                simp [hName] at hVariable
            | some name =>
                simp [hName] at hVariable
                subst decodedVariable
                simp [fs_named_term_token_tree_decode,
                  fs_named_variable_decode, hName] at hDecode
                simpa [RawTermTokenTree.tokens,
                  fs_named_term_token_tree_binder_shift, hName] using
                  CanonicalBinderShiftTokens.singleton
                    (fs_named_variable_shift_relation hName)
        | none =>
            cases hSymbol :
                fs_find_encoded
                  (fun symbol : FunctionSymbol =>
                    Numbered.constant_token symbol.ctorIdx)
                  token fs_function_symbols with
            | none =>
                simp [fs_named_term_token_tree_decode,
                  hVariable, hSymbol] at hDecode
            | some symbol =>
                by_cases hDomain : signature.funcDomain symbol = []
                · have hName :
                      fs_variable_name_decode token = none := by
                    unfold fs_named_variable_decode at hVariable
                    cases h : fs_variable_name_decode token <;>
                      simp [h] at hVariable ⊢
                  have hToken :
                      Numbered.constant_token symbol.ctorIdx = token :=
                    fs_find_encoded_value_of_some
                      (encode := fun candidate : FunctionSymbol =>
                        Numbered.constant_token candidate.ctorIdx)
                      (target := token)
                      (items := fs_function_symbols)
                      (item := symbol)
                      hSymbol
                  simp [fs_named_term_token_tree_decode,
                    fs_named_term_token_tree_binder_shift,
                    hVariable, hSymbol, hDomain, hName] at hDecode ⊢
                  subst term
                  rw [← hToken]
                  exact CanonicalBinderShiftTokens.singleton
                    (.constant symbol.ctorIdx)
                · simp [fs_named_term_token_tree_decode,
                    hVariable, hSymbol, hDomain] at hDecode
    | .application head arguments, term, hDecode => by
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
                  (fs_named_term_token_tree_decode
                    freeBase boundNames) with
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
                    ⟨_, hDecode⟩
                  subst term
                  have hRelations :=
                    fs_named_term_token_trees_binder_shift_relation
                      freeBase boundNames hArguments
                  have hToken :
                      Numbered.function_token
                          (arguments.length - 1) symbol.ctorIdx =
                        head :=
                    fs_find_encoded_value_of_some
                      (encode := fun candidate : FunctionSymbol =>
                        Numbered.function_token
                          (arguments.length - 1) candidate.ctorIdx)
                      (target := head)
                      (items := fs_function_symbols)
                      (item := symbol)
                      hSymbol
                  have hTargetArguments :
                      (arguments.map
                          (RawTermTokenTree.tokens ∘
                            fs_named_term_token_tree_binder_shift)).flatten =
                        RawTermTokenTree.list_tokens
                          (arguments.map
                            fs_named_term_token_tree_binder_shift) := by
                    rw [← List.map_map]
                    exact
                      RawTermTokenTree.map_tokens_flatten_eq_list_tokens
                        (arguments.map
                          fs_named_term_token_tree_binder_shift)
                  simpa [fs_named_term_token_tree_binder_shift,
                    RawTermTokenTree.tokens, hToken,
                    Numbered.function_application_tokens,
                    RawTermTokenTree.map_tokens_flatten_eq_list_tokens,
                    hTargetArguments] using
                    CanonicalBinderShiftTokens.function_application
                      (arguments.length - 1) symbol.ctorIdx hRelations
                · simp [fs_named_term_token_tree_decode,
                    hSymbol, hArguments, hCheck] at hDecode
  termination_by tree => sizeOf tree

  private theorem fs_named_term_token_trees_binder_shift_relation
      (freeBase : Nat) (boundNames : List Nat) :
      ∀ {trees : List RawTermTokenTree} {terms : List SetTerm},
        trees.mapM
            (fs_named_term_token_tree_decode freeBase boundNames) =
          some terms →
        CanonicalBinderShiftTokenLists
          (trees.map RawTermTokenTree.tokens)
          ((trees.map fs_named_term_token_tree_binder_shift).map
            RawTermTokenTree.tokens)
    | .nil, terms, hDecode => by
        simp at hDecode
        subst terms
        exact .nil
    | tree :: trees, terms, hDecode => by
        cases hHead :
            fs_named_term_token_tree_decode
              freeBase boundNames tree with
        | none =>
            simp [List.mapM_cons, hHead] at hDecode
        | some head =>
            cases hTail :
                trees.mapM
                  (fs_named_term_token_tree_decode
                    freeBase boundNames) with
            | none =>
                simp [List.mapM_cons, hHead, hTail] at hDecode
            | some tail =>
                simp [List.mapM_cons, hHead, hTail] at hDecode
                subst terms
                have hHeadRelation :=
                  fs_named_term_token_tree_binder_shift_relation
                    freeBase boundNames hHead
                have hTailRelation :=
                  fs_named_term_token_trees_binder_shift_relation
                    freeBase boundNames hTail
                exact .cons hHeadRelation hTailRelation
  termination_by trees => sizeOf trees
end

theorem fs_named_hilbert_token_tree_binder_shift_relation
    (freeBase : Nat) :
    ∀ {boundNames : List Nat}
      {tree : RawHilbertTokenTree} {formula : SetFormula},
      fs_named_hilbert_token_tree_decode
          freeBase boundNames tree = some formula →
      CanonicalBinderShiftTokens tree.tokens
        (fs_named_hilbert_token_tree_binder_shift tree).tokens
  | boundNames, .equality left right, formula, hDecode => by
      cases hLeft :
          fs_named_term_token_tree_decode freeBase boundNames left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode, hLeft] at hDecode
      | some leftTerm =>
          cases hRight :
              fs_named_term_token_tree_decode freeBase boundNames right with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
          | some rightTerm =>
              have hLeftRelation :=
                fs_named_term_token_tree_binder_shift_relation
                  freeBase boundNames hLeft
              have hRightRelation :=
                fs_named_term_token_tree_binder_shift_relation
                  freeBase boundNames hRight
              simpa [fs_named_hilbert_token_tree_binder_shift,
                RawHilbertTokenTree.tokens,
                Numbered.equality_tokens,
                List.append_assoc] using
                CanonicalBinderShiftTokens.equality
                  hLeftRelation hRightRelation
  | boundNames, .membership left right, formula, hDecode => by
      cases hLeft :
          fs_named_term_token_tree_decode freeBase boundNames left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode, hLeft] at hDecode
      | some leftTerm =>
          cases hRight :
              fs_named_term_token_tree_decode freeBase boundNames right with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
          | some rightTerm =>
              have hLeftRelation :=
                fs_named_term_token_tree_binder_shift_relation
                  freeBase boundNames hLeft
              have hRightRelation :=
                fs_named_term_token_tree_binder_shift_relation
                  freeBase boundNames hRight
              simpa [fs_named_hilbert_token_tree_binder_shift,
                RawHilbertTokenTree.tokens,
                Numbered.membership_tokens,
                List.append_assoc] using
                CanonicalBinderShiftTokens.membership
                  hLeftRelation hRightRelation
  | boundNames, .predicate head arguments, formula, hDecode => by
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
                  (fs_named_term_token_tree_decode
                    freeBase boundNames) with
            | none =>
                simp [fs_named_hilbert_token_tree_decode,
                  hRelation, hArguments] at hDecode
            | some terms =>
                by_cases hCheck :
                    Term.check_args_wellSorted terms
                        (signature.relDomain relation) = true
                · simp [fs_named_hilbert_token_tree_decode,
                    hRelation, hKind, hArguments, hCheck] at hDecode
                  have hRelations :=
                    fs_named_term_token_trees_binder_shift_relation
                      freeBase boundNames hArguments
                  have hToken :
                      Numbered.predicate_token
                          (arguments.length - 1) relation.ctorIdx =
                        head :=
                    fs_find_encoded_value_of_some
                      (encode := fun candidate : RelationSymbol =>
                        Numbered.predicate_token
                          (arguments.length - 1) candidate.ctorIdx)
                      (target := head)
                      (items := fs_relation_symbols)
                      (item := relation)
                      hRelation
                  have hTargetArguments :
                      (arguments.map
                          (RawTermTokenTree.tokens ∘
                            fs_named_term_token_tree_binder_shift)).flatten =
                        RawTermTokenTree.list_tokens
                          (arguments.map
                            fs_named_term_token_tree_binder_shift) := by
                    rw [← List.map_map]
                    exact
                      RawTermTokenTree.map_tokens_flatten_eq_list_tokens
                        (arguments.map
                          fs_named_term_token_tree_binder_shift)
                  simpa [fs_named_hilbert_token_tree_binder_shift,
                    RawHilbertTokenTree.tokens, hToken,
                    Numbered.predicate_application_tokens,
                    RawTermTokenTree.map_tokens_flatten_eq_list_tokens,
                    hTargetArguments] using
                    CanonicalBinderShiftTokens.predicate_application
                      (arguments.length - 1) relation.ctorIdx hRelations
                · simp [fs_named_hilbert_token_tree_decode,
                    hRelation, hKind, hArguments, hCheck] at hDecode
          · simp [fs_named_hilbert_token_tree_decode,
              hRelation, hKind] at hDecode
  | boundNames, .negation body, formula, hDecode => by
      cases hBody :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames body with
      | none =>
          simp [fs_named_hilbert_token_tree_decode, hBody] at hDecode
      | some bodyFormula =>
          simp [fs_named_hilbert_token_tree_decode, hBody] at hDecode
          have hRelation :=
            fs_named_hilbert_token_tree_binder_shift_relation
              freeBase hBody
          simpa [fs_named_hilbert_token_tree_binder_shift,
            RawHilbertTokenTree.tokens] using
            CanonicalBinderShiftTokens.negation hRelation
  | boundNames, .implication left right, formula, hDecode => by
      cases hLeft :
          fs_named_hilbert_token_tree_decode freeBase boundNames left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode, hLeft] at hDecode
      | some leftFormula =>
          cases hRight :
              fs_named_hilbert_token_tree_decode freeBase boundNames right with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
          | some rightFormula =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
              have hLeftRelation :=
                fs_named_hilbert_token_tree_binder_shift_relation
                  freeBase hLeft
              have hRightRelation :=
                fs_named_hilbert_token_tree_binder_shift_relation
                  freeBase hRight
              simpa [fs_named_hilbert_token_tree_binder_shift,
                RawHilbertTokenTree.tokens,
                Numbered.implication_tokens,
                List.append_assoc] using
                CanonicalBinderShiftTokens.implication
                  hLeftRelation hRightRelation
  | boundNames, .universal variableToken body, formula, hDecode => by
      cases hName : fs_variable_name_decode variableToken with
      | none =>
          simp [fs_named_hilbert_token_tree_decode, hName] at hDecode
      | some name =>
          cases hBody :
              fs_named_hilbert_token_tree_decode
                freeBase (name :: boundNames) body with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hName, hBody] at hDecode
          | some bodyFormula =>
              simp [fs_named_hilbert_token_tree_decode,
                hName, hBody] at hDecode
              have hRelation :=
                fs_named_hilbert_token_tree_binder_shift_relation
                  freeBase hBody
              simpa [fs_named_hilbert_token_tree_binder_shift,
                RawHilbertTokenTree.tokens,
                Numbered.universal_tokens, hName,
                List.append_assoc] using
                (CanonicalBinderShiftTokens.singleton
                  (.logical .leftParenthesis)).append <|
                (CanonicalBinderShiftTokens.singleton
                  (.logical .universal)).append <|
                (CanonicalBinderShiftTokens.singleton
                  (fs_named_variable_shift_relation hName)).append <|
                hRelation.append <|
                CanonicalBinderShiftTokens.singleton
                  (.logical .rightParenthesis)
termination_by
  _ tree _ _ => sizeOf tree

/-! ## 指定自由变量的规范闭合 -/

/--
在普通 binder 平移后，把指定的规范自由名改为新加入的最外层 binder 名。
其余名字仍按 `fs_named_binder_shift_name` 平移。
-/
def fs_named_binder_close_name
    (id name : Nat) : Nat :=
  if name = free_name id then
    bound_name 0
  else
    fs_named_binder_shift_name name

private theorem fs_named_binder_close_name_injective
    (id : Nat) :
    Function.Injective
      (fs_named_binder_close_name id) := by
  intro left right hEqual
  by_cases hLeft : left = free_name id
  · subst left
    by_cases hRight : right = free_name id
    · exact hRight.symm
    · exfalso
      have hOuter :
          bound_name 0 =
            fs_named_binder_shift_name right := by
        simpa [fs_named_binder_close_name, hRight] using hEqual
      exact
        fs_named_binder_shift_name_ne_outer right
          hOuter.symm
  · by_cases hRight : right = free_name id
    · subst right
      exfalso
      have hOuter :
          fs_named_binder_shift_name left =
            bound_name 0 := by
        simpa [fs_named_binder_close_name, hLeft] using hEqual
      exact
        fs_named_binder_shift_name_ne_outer left hOuter
    · apply fs_named_binder_shift_name_injective
      simpa [fs_named_binder_close_name,
        hLeft, hRight] using hEqual

private theorem fs_bound_name_index_binder_close
    (id name : Nat) :
    ∀ names,
      fs_bound_name_index
          (fs_named_binder_close_name id name)
          (names.map (fs_named_binder_close_name id) ++
            [bound_name 0]) =
        match fs_bound_name_index name names with
        | some index => some index
        | none =>
            if name = free_name id then
              some names.length
            else
              none
  | [] => by
      by_cases hName : name = free_name id
      · subst name
        simp [fs_named_binder_close_name,
          fs_bound_name_index]
      · have hOuter :
            bound_name 0 ≠
              fs_named_binder_shift_name name :=
          Ne.symm
            (fs_named_binder_shift_name_ne_outer name)
        simp [fs_named_binder_close_name,
          fs_bound_name_index, hName, hOuter]
  | head :: tail => by
      by_cases hHead : head = name
      · subst head
        simp [fs_bound_name_index]
      · have hClose :
          fs_named_binder_close_name id head ≠
            fs_named_binder_close_name id name := by
          intro hEqual
          exact hHead
            (fs_named_binder_close_name_injective id hEqual)
        simp only [List.map_cons, List.cons_append,
          fs_bound_name_index, hHead, hClose, if_false]
        rw [fs_bound_name_index_binder_close id name tail]
        cases hTail :
            fs_bound_name_index name tail with
        | none =>
            by_cases hName : name = free_name id
            · simp [hName]
            · simp [hName]
        | some index =>
            simp

theorem fs_named_variable_of_name_binder_close
    (freeBase id name : Nat)
    (hId : id < freeBase) :
    ∀ names,
      Term.var
          (fs_named_variable_of_name freeBase
            (names.map (fs_named_binder_close_name id) ++
              [bound_name 0])
            (fs_named_binder_close_name id name)) =
        Term.closeFreeAt SetSort.set id names.length
          (Term.var
            (fs_named_variable_of_name
              freeBase names name))
  | names => by
      unfold fs_named_variable_of_name
      rw [fs_bound_name_index_binder_close]
      cases hIndex :
          fs_bound_name_index name names with
      | some index =>
          have hIndexBound :
              index < names.length :=
            fs_bound_name_index_lt_length name hIndex
          simp [Term.closeFreeAt]
          omega
      | none =>
          by_cases hName : name = free_name id
          · subst name
            simp [
              free_name, Term.closeFreeAt]
          · by_cases hEven : name % 2 = 0
            · have hDiv : name / 2 ≠ id := by
                intro hEqual
                have hDivision := Nat.mod_add_div name 2
                apply hName
                simp [free_name, hEven] at hDivision ⊢
                omega
              simp [hName, hEven,
                fs_named_binder_close_name,
                fs_named_binder_shift_name,
                Term.closeFreeAt, hDiv]
            · have hOdd : name % 2 = 1 := by
                omega
              have hFreeBase : freeBase ≠ id := by
                omega
              simp [hName, hOdd,
                fs_named_binder_close_name,
                fs_named_binder_shift_name,
                Term.closeFreeAt, hFreeBase]

/-- singleton 替换在单个 token 上的可计算作用。 -/
def fs_named_token_binder_close
    (id token : Nat) : Nat :=
  if token =
      Numbered.variable_token (free_name id) then
    Numbered.variable_token (bound_name 0)
  else
    token

/-- 在原始项树上同时执行 binder 平移与指定自由名闭合。 -/
def fs_named_term_token_tree_binder_close
    (id : Nat) : RawTermTokenTree → RawTermTokenTree
  | .atom token =>
      match fs_variable_name_decode token with
      | some name =>
          .atom (Numbered.variable_token
            (fs_named_binder_close_name id name))
      | none =>
          .atom token
  | .application head arguments =>
      .application
        (fs_named_token_binder_close id head)
        (arguments.map
          (fs_named_term_token_tree_binder_close id))

/-- 在原始 Hilbert 树上同时执行 binder 平移与指定自由名闭合。 -/
def fs_named_hilbert_token_tree_binder_close
    (id : Nat) :
    RawHilbertTokenTree → RawHilbertTokenTree
  | .equality left right =>
      .equality
        (fs_named_term_token_tree_binder_close id left)
        (fs_named_term_token_tree_binder_close id right)
  | .membership left right =>
      .membership
        (fs_named_term_token_tree_binder_close id left)
        (fs_named_term_token_tree_binder_close id right)
  | .predicate head arguments =>
      .predicate
        (fs_named_token_binder_close id head)
        (arguments.map
          (fs_named_term_token_tree_binder_close id))
  | .negation body =>
      .negation
        (fs_named_hilbert_token_tree_binder_close id body)
  | .implication left right =>
      .implication
        (fs_named_hilbert_token_tree_binder_close id left)
        (fs_named_hilbert_token_tree_binder_close id right)
  | .universal variableToken body =>
      .universal
        (match fs_variable_name_decode variableToken with
        | some name =>
            Numbered.variable_token
              (fs_named_binder_close_name id name)
        | none =>
            variableToken)
        (fs_named_hilbert_token_tree_binder_close id body)

mutual
  private theorem fs_named_term_token_tree_binder_close_tokens
      (id : Nat) :
      ∀ tree,
        (fs_named_term_token_tree_binder_close id tree).tokens =
          substitute_tokens
            (fs_named_term_token_tree_binder_shift tree).tokens
            (Numbered.variable_token (free_name id))
            [Numbered.variable_token (bound_name 0)]
  | .atom token => by
      cases hName :
          fs_variable_name_decode token with
      | none =>
          have hToken :
              token ≠ Numbered.variable_token (free_name id) := by
            intro hEqual
            subst token
            simp [fs_variable_name_decode_encode] at hName
          simp [fs_named_term_token_tree_binder_close,
            fs_named_term_token_tree_binder_shift,
            RawTermTokenTree.tokens, hName, hToken]
      | some name =>
          have hToken :
              Numbered.variable_token name = token :=
            fs_variable_name_decode_value_of_some hName
          subst token
          by_cases hNameId : name = free_name id
          · subst name
            simp [fs_named_term_token_tree_binder_close,
              fs_named_term_token_tree_binder_shift,
              fs_named_binder_close_name,
              fs_named_binder_shift_name, free_name,
              RawTermTokenTree.tokens,
              fs_variable_name_decode_encode]
          · have hShift :
                fs_named_binder_shift_name name ≠
                  free_name id := by
              intro hEqual
              apply hNameId
              apply fs_named_binder_shift_name_injective
              simpa [fs_named_binder_shift_name,
                free_name] using hEqual
            simp [fs_named_term_token_tree_binder_close,
              fs_named_term_token_tree_binder_shift,
              fs_named_binder_close_name, hNameId,
              RawTermTokenTree.tokens,
              fs_variable_name_decode_encode,
              variable_token_ne_variable_token hShift]
    | .application head arguments => by
      have hArguments :
          RawTermTokenTree.list_tokens
              (arguments.map
                (fs_named_term_token_tree_binder_close id)) =
            substitute_tokens
              (RawTermTokenTree.list_tokens
                (arguments.map
                  fs_named_term_token_tree_binder_shift))
              (Numbered.variable_token (free_name id))
              [Numbered.variable_token (bound_name 0)] :=
        fs_named_term_token_trees_binder_close_tokens id arguments
      have hLeft :
          Numbered.logical_token .leftParenthesis ≠
            Numbered.variable_token (free_name id) :=
        logical_token_ne_variable_token
          .leftParenthesis (free_name id)
      have hRight :
          Numbered.logical_token .rightParenthesis ≠
            Numbered.variable_token (free_name id) :=
        logical_token_ne_variable_token
          .rightParenthesis (free_name id)
      by_cases hHead :
          head =
            Numbered.variable_token (free_name id)
      · simp [fs_named_term_token_tree_binder_close,
          fs_named_term_token_tree_binder_shift,
          fs_named_token_binder_close,
          RawTermTokenTree.tokens,
          substitute_tokens_append,
          substitution_piece_tokens, hHead,
          hArguments, hLeft, hRight
          ]
      · simp [fs_named_term_token_tree_binder_close,
          fs_named_term_token_tree_binder_shift,
          fs_named_token_binder_close,
          RawTermTokenTree.tokens,
          substitute_tokens_append,
          substitution_piece_tokens, hHead,
          hArguments, hLeft, hRight
          ]
  termination_by tree => sizeOf tree

  private theorem fs_named_term_token_trees_binder_close_tokens
      (id : Nat) :
      ∀ trees : List RawTermTokenTree,
        RawTermTokenTree.list_tokens
            (trees.map
              (fs_named_term_token_tree_binder_close id)) =
          substitute_tokens
            (RawTermTokenTree.list_tokens
              (trees.map
                fs_named_term_token_tree_binder_shift))
            (Numbered.variable_token (free_name id))
            [Numbered.variable_token (bound_name 0)]
    | [] => by
        simp [RawTermTokenTree.list_tokens]
    | tree :: trees => by
        simp only [List.map_cons,
          RawTermTokenTree.list_tokens]
        rw [fs_named_term_token_tree_binder_close_tokens
          id tree,
          fs_named_term_token_trees_binder_close_tokens
            id trees,
          substitute_tokens_append]
  termination_by trees => sizeOf trees
  decreasing_by
    all_goals
      first
      | sizeOf_list_dec
      | simp +arith
end

theorem fs_named_hilbert_token_tree_binder_close_tokens
    (id : Nat) :
    ∀ tree,
      (fs_named_hilbert_token_tree_binder_close id tree).tokens =
        substitute_tokens
          (fs_named_hilbert_token_tree_binder_shift tree).tokens
          (Numbered.variable_token (free_name id))
          [Numbered.variable_token (bound_name 0)]
  | .equality left right => by
      simp [fs_named_hilbert_token_tree_binder_close,
        fs_named_hilbert_token_tree_binder_shift,
        RawHilbertTokenTree.tokens,
        substitute_tokens_append,
        substitution_piece_tokens,
        logical_token_ne_variable_token,
        fs_named_term_token_tree_binder_close_tokens]
  | .membership left right => by
      simp [fs_named_hilbert_token_tree_binder_close,
        fs_named_hilbert_token_tree_binder_shift,
        RawHilbertTokenTree.tokens,
        substitute_tokens_append,
        substitution_piece_tokens,
        logical_token_ne_variable_token,
        membership_token_ne_variable_token,
        fs_named_term_token_tree_binder_close_tokens]
  | .predicate head arguments => by
      have hArguments :
          RawTermTokenTree.list_tokens
              (arguments.map
                (fs_named_term_token_tree_binder_close id)) =
            substitute_tokens
              (RawTermTokenTree.list_tokens
                (arguments.map
                  fs_named_term_token_tree_binder_shift))
              (Numbered.variable_token (free_name id))
              [Numbered.variable_token (bound_name 0)] :=
        fs_named_term_token_trees_binder_close_tokens id arguments
      have hLeft :
          Numbered.logical_token .leftParenthesis ≠
            Numbered.variable_token (free_name id) :=
        logical_token_ne_variable_token
          .leftParenthesis (free_name id)
      have hRight :
          Numbered.logical_token .rightParenthesis ≠
            Numbered.variable_token (free_name id) :=
        logical_token_ne_variable_token
          .rightParenthesis (free_name id)
      by_cases hHead :
          head =
            Numbered.variable_token (free_name id)
      · simp [fs_named_hilbert_token_tree_binder_close,
          fs_named_hilbert_token_tree_binder_shift,
          fs_named_token_binder_close,
          RawHilbertTokenTree.tokens,
          substitute_tokens_append,
          substitution_piece_tokens, hHead,
          hArguments, hLeft, hRight
          ]
      · simp [fs_named_hilbert_token_tree_binder_close,
          fs_named_hilbert_token_tree_binder_shift,
          fs_named_token_binder_close,
          RawHilbertTokenTree.tokens,
          substitute_tokens_append,
          substitution_piece_tokens, hHead,
          hArguments, hLeft, hRight
          ]
  | .negation body => by
      simp only [fs_named_hilbert_token_tree_binder_close,
        fs_named_hilbert_token_tree_binder_shift,
        RawHilbertTokenTree.tokens]
      rw [fs_named_hilbert_token_tree_binder_close_tokens
        id body]
      simp [substitute_tokens_append,
        substitution_piece_tokens,
        logical_token_ne_variable_token]
  | .implication left right => by
      simp only [fs_named_hilbert_token_tree_binder_close,
        fs_named_hilbert_token_tree_binder_shift,
        RawHilbertTokenTree.tokens]
      rw [fs_named_hilbert_token_tree_binder_close_tokens
        id left,
        fs_named_hilbert_token_tree_binder_close_tokens
          id right]
      simp [substitute_tokens_append,
        substitution_piece_tokens,
        logical_token_ne_variable_token]
  | .universal variableToken body => by
      simp only [fs_named_hilbert_token_tree_binder_close,
        fs_named_hilbert_token_tree_binder_shift,
        RawHilbertTokenTree.tokens]
      rw [fs_named_hilbert_token_tree_binder_close_tokens
        id body]
      cases hName :
          fs_variable_name_decode variableToken with
      | none =>
          have hToken :
              variableToken ≠
                Numbered.variable_token (free_name id) := by
            intro hEqual
            subst variableToken
            simp [fs_variable_name_decode_encode] at hName
          simp [


            substitute_tokens_append, hToken,
            substitution_piece_tokens,
            logical_token_ne_variable_token]
      | some name =>
          have hToken :
              Numbered.variable_token name =
                variableToken :=
            fs_variable_name_decode_value_of_some hName
          subst variableToken
          by_cases hNameId : name = free_name id
          · subst name
            simp [

              fs_named_binder_close_name,
              fs_named_binder_shift_name, free_name,

              substitute_tokens_append,
              substitution_piece_tokens,
              logical_token_ne_variable_token
              ]
          · have hShift :
                fs_named_binder_shift_name name ≠
                  free_name id := by
              intro hEqual
              apply hNameId
              apply fs_named_binder_shift_name_injective
              simpa [fs_named_binder_shift_name,
                free_name] using hEqual
            simp [

              fs_named_binder_close_name, hNameId,

              substitute_tokens_append,
              substitution_piece_tokens,
              logical_token_ne_variable_token,

              variable_token_ne_variable_token hShift]
termination_by tree => sizeOf tree

mutual
  private theorem fs_named_term_token_tree_binder_close_decode
      (freeBase id : Nat) (hId : id < freeBase)
      (boundNames : List Nat) :
      ∀ {tree : RawTermTokenTree} {term : SetTerm},
        fs_named_term_token_tree_decode
            freeBase boundNames tree = some term →
        fs_named_term_token_tree_decode freeBase
            (boundNames.map
                (fs_named_binder_close_name id) ++
              [bound_name 0])
            (fs_named_term_token_tree_binder_close id tree) =
          some (Term.closeFreeAt
            SetSort.set id boundNames.length term)
    | .atom token, term, hDecode => by
        cases hVariable :
            fs_named_variable_decode
              freeBase boundNames token with
        | some decodedVariable =>
            simp [fs_named_term_token_tree_decode,
              hVariable] at hDecode
            subst term
            unfold fs_named_variable_decode at hVariable
            cases hName :
                fs_variable_name_decode token with
            | none =>
                simp [hName] at hVariable
            | some name =>
                simp [hName] at hVariable
                subst decodedVariable
                simp [fs_named_term_token_tree_binder_close,
                  fs_named_term_token_tree_decode,
                  fs_named_variable_decode, hName,
                  fs_named_variable_of_name_binder_close
                    freeBase id name hId boundNames]
        | none =>
            cases hSymbol :
                fs_find_encoded
                  (fun symbol : FunctionSymbol =>
                    Numbered.constant_token symbol.ctorIdx)
                  token fs_function_symbols with
            | none =>
                simp [fs_named_term_token_tree_decode,
                  hVariable, hSymbol] at hDecode
            | some symbol =>
                by_cases hDomain :
                    signature.funcDomain symbol = []
                · have hName :
                      fs_variable_name_decode token = none := by
                    unfold fs_named_variable_decode at hVariable
                    cases h :
                        fs_variable_name_decode token <;>
                      simp [h] at hVariable ⊢
                  simp [fs_named_term_token_tree_decode,
                    fs_named_term_token_tree_binder_close,
                    hVariable, hSymbol, hDomain, hName
                    ] at hDecode ⊢
                  subst term
                  have hTargetVariable :
                      fs_named_variable_decode freeBase
                          (boundNames.map
                              (fs_named_binder_close_name id) ++
                            [bound_name 0])
                          token = none := by
                    simp [fs_named_variable_decode, hName]
                  simp [hTargetVariable,
                    Term.closeFreeAt]
                · simp [fs_named_term_token_tree_decode,
                    hVariable, hSymbol, hDomain] at hDecode
    | .application head arguments, term, hDecode => by
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
                  (fs_named_term_token_tree_decode
                    freeBase boundNames) with
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
                    ⟨hArgumentsPositive, hDecode⟩
                  subst term
                  have hTargetArguments :=
                    fs_named_term_token_trees_binder_close_decode
                      freeBase id hId boundNames hArguments
                  have hTargetCheck :
                      Term.check_args_wellSorted
                          (terms.map (Term.closeFreeAt
                            SetSort.set id boundNames.length))
                          (signature.funcDomain symbol) = true :=
                    Term.check_args_wellSorted_complete <|
                      ArgsWellSorted.closeFreeAt
                        SetSort.set id boundNames.length
                        (Term.check_args_wellSorted_sound hCheck)
                  have hHead :
                      head ≠
                        Numbered.variable_token
                          (free_name id) := by
                    intro hEqual
                    have hToken :=
                      fs_find_encoded_value_of_some
                        (encode :=
                          fun candidate : FunctionSymbol =>
                            Numbered.function_token
                              (arguments.length - 1)
                              candidate.ctorIdx)
                        (target := head)
                        (items := fs_function_symbols)
                        (item := symbol) hSymbol
                    exact
                      function_token_ne_variable_token
                        (arguments.length - 1)
                        symbol.ctorIdx (free_name id)
                        (hToken.trans hEqual)
                  simp [fs_named_term_token_tree_decode,
                    fs_named_term_token_tree_binder_close,
                    fs_named_token_binder_close, hHead,
                    hArgumentsPositive, hSymbol,
                    hTargetArguments, hTargetCheck, Term.closeFreeAt]
                · simp [fs_named_term_token_tree_decode,
                    hSymbol, hArguments, hCheck] at hDecode
  termination_by tree => sizeOf tree

  private theorem fs_named_term_token_trees_binder_close_decode
      (freeBase id : Nat) (hId : id < freeBase)
      (boundNames : List Nat) :
      ∀ {trees : List RawTermTokenTree}
          {terms : List SetTerm},
        trees.mapM
            (fs_named_term_token_tree_decode
              freeBase boundNames) = some terms →
        (trees.map
            (fs_named_term_token_tree_binder_close id)).mapM
            (fs_named_term_token_tree_decode freeBase
              (boundNames.map
                  (fs_named_binder_close_name id) ++
                [bound_name 0])) =
          some (terms.map (Term.closeFreeAt
            SetSort.set id boundNames.length))
    | .nil, terms, hDecode => by
        simp at hDecode
        subst terms
        rfl
    | .cons tree trees, terms, hDecode => by
        cases hHead :
            fs_named_term_token_tree_decode
              freeBase boundNames tree with
        | none =>
            simp [List.mapM_cons, hHead] at hDecode
        | some head =>
            cases hTail :
                trees.mapM
                  (fs_named_term_token_tree_decode
                    freeBase boundNames) with
            | none =>
                simp [List.mapM_cons,
                  hHead, hTail] at hDecode
            | some tail =>
                simp [List.mapM_cons,
                  hHead, hTail] at hDecode
                subst terms
                have hHeadClose :=
                  fs_named_term_token_tree_binder_close_decode
                    freeBase id hId boundNames hHead
                have hTailClose :=
                  fs_named_term_token_trees_binder_close_decode
                    freeBase id hId boundNames hTail
                simp [List.mapM_cons,
                  hHeadClose, hTailClose]
  termination_by trees => sizeOf trees
end

private theorem fs_named_hilbert_token_tree_binder_close_decode
    (freeBase id : Nat) (hId : id < freeBase) :
    ∀ {boundNames : List Nat}
      {tree : RawHilbertTokenTree} {formula : SetFormula},
      fs_named_hilbert_token_tree_decode
          freeBase boundNames tree = some formula →
      fs_named_hilbert_token_tree_decode freeBase
          (boundNames.map
              (fs_named_binder_close_name id) ++
            [bound_name 0])
          (fs_named_hilbert_token_tree_binder_close id tree) =
        some (Formula.closeFreeAt
          SetSort.set id boundNames.length formula)
  | boundNames, .equality left right, formula, hDecode => by
      cases hLeft :
          fs_named_term_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hLeft] at hDecode
      | some leftTerm =>
          cases hRight :
              fs_named_term_token_tree_decode
                freeBase boundNames right with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
          | some rightTerm =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
              have hLeftClose :=
                fs_named_term_token_tree_binder_close_decode
                  freeBase id hId boundNames hLeft
              have hRightClose :=
                fs_named_term_token_tree_binder_close_decode
                  freeBase id hId boundNames hRight
              have hLeftCheck :
                  Term.check_wellSorted SetSort.set
                      (Term.closeFreeAt SetSort.set id
                        boundNames.length leftTerm) = true :=
                Term.check_wellSorted_complete <|
                  TermWellSorted.closeFreeAt
                    SetSort.set id boundNames.length
                    (Term.check_wellSorted_sound hDecode.1.1)
              have hRightCheck :
                  Term.check_wellSorted SetSort.set
                      (Term.closeFreeAt SetSort.set id
                        boundNames.length rightTerm) = true :=
                Term.check_wellSorted_complete <|
                  TermWellSorted.closeFreeAt
                    SetSort.set id boundNames.length
                    (Term.check_wellSorted_sound hDecode.1.2)
              rw [← hDecode.2]
              simp [fs_named_hilbert_token_tree_decode,
                fs_named_hilbert_token_tree_binder_close,
                hLeftClose, hRightClose,
                Formula.closeFreeAt,
                hLeftCheck, hRightCheck]
  | boundNames, .membership left right, formula, hDecode => by
      cases hLeft :
          fs_named_term_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hLeft] at hDecode
      | some leftTerm =>
          cases hRight :
              fs_named_term_token_tree_decode
                freeBase boundNames right with
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
                have hLeftClose :=
                  fs_named_term_token_tree_binder_close_decode
                    freeBase id hId boundNames hLeft
                have hRightClose :=
                  fs_named_term_token_tree_binder_close_decode
                    freeBase id hId boundNames hRight
                have hTargetCheck :
                    Term.check_args_wellSorted
                        [Term.closeFreeAt SetSort.set id
                            boundNames.length leftTerm,
                          Term.closeFreeAt SetSort.set id
                            boundNames.length rightTerm]
                        (signature.relDomain
                          RelationSymbol.membership) = true := by
                  simpa using
                    Term.check_args_wellSorted_complete <|
                      ArgsWellSorted.closeFreeAt
                        SetSort.set id boundNames.length
                        (Term.check_args_wellSorted_sound hCheck)
                simp [fs_named_hilbert_token_tree_decode,
                  fs_named_hilbert_token_tree_binder_close,
                  hLeftClose, hRightClose, hTargetCheck,
                  Formula.closeFreeAt]
              · simp [fs_named_hilbert_token_tree_decode,
                  hLeft, hRight, hCheck] at hDecode
  | boundNames, .predicate head arguments, formula, hDecode => by
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
                  (fs_named_term_token_tree_decode
                    freeBase boundNames) with
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
                    fs_named_term_token_trees_binder_close_decode
                      freeBase id hId boundNames hArguments
                  have hTargetCheck :
                      Term.check_args_wellSorted
                          (terms.map (Term.closeFreeAt
                            SetSort.set id boundNames.length))
                          (signature.relDomain relation) = true :=
                    Term.check_args_wellSorted_complete <|
                      ArgsWellSorted.closeFreeAt
                        SetSort.set id boundNames.length
                        (Term.check_args_wellSorted_sound hCheck)
                  have hHead :
                      head ≠
                        Numbered.variable_token
                          (free_name id) := by
                    intro hEqual
                    have hToken :=
                      fs_find_encoded_value_of_some
                        (encode :=
                          fun candidate : RelationSymbol =>
                            Numbered.predicate_token
                              (arguments.length - 1)
                              candidate.ctorIdx)
                        (target := head)
                        (items := fs_relation_symbols)
                        (item := relation) hRelation
                    exact
                      predicate_token_ne_variable_token
                        (arguments.length - 1)
                        relation.ctorIdx (free_name id)
                        (hToken.trans hEqual)
                  simp [fs_named_hilbert_token_tree_decode,
                    fs_named_hilbert_token_tree_binder_close,
                    fs_named_token_binder_close, hHead,
                    hRelation, hKind,
                    hTargetArguments, hTargetCheck,
                    Formula.closeFreeAt]
                · simp [fs_named_hilbert_token_tree_decode,
                    hRelation, hKind,
                    hArguments, hCheck] at hDecode
          · simp [fs_named_hilbert_token_tree_decode,
              hRelation, hKind] at hDecode
  | boundNames, .negation body, formula, hDecode => by
      cases hBody :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames body with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hBody] at hDecode
      | some bodyFormula =>
          simp [fs_named_hilbert_token_tree_decode,
            hBody] at hDecode
          subst formula
          have hBodyClose :=
            fs_named_hilbert_token_tree_binder_close_decode
              freeBase id hId hBody
          simp [fs_named_hilbert_token_tree_decode,
            fs_named_hilbert_token_tree_binder_close,
            hBodyClose, Formula.closeFreeAt]
  | boundNames, .implication left right, formula, hDecode => by
      cases hLeft :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hLeft] at hDecode
      | some leftFormula =>
          cases hRight :
              fs_named_hilbert_token_tree_decode
                freeBase boundNames right with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
          | some rightFormula =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
              subst formula
              have hLeftClose :=
                fs_named_hilbert_token_tree_binder_close_decode
                  freeBase id hId hLeft
              have hRightClose :=
                fs_named_hilbert_token_tree_binder_close_decode
                  freeBase id hId hRight
              simp [fs_named_hilbert_token_tree_decode,
                fs_named_hilbert_token_tree_binder_close,
                hLeftClose, hRightClose,
                Formula.closeFreeAt]
  | boundNames, .universal variableToken body, formula, hDecode => by
      cases hName :
          fs_variable_name_decode variableToken with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hName] at hDecode
      | some name =>
          cases hBody :
              fs_named_hilbert_token_tree_decode
                freeBase (name :: boundNames) body with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hName, hBody] at hDecode
          | some bodyFormula =>
              simp [fs_named_hilbert_token_tree_decode,
                hName, hBody] at hDecode
              subst formula
              have hBodyClose :=
                fs_named_hilbert_token_tree_binder_close_decode
                  freeBase id hId hBody
              simpa [fs_named_hilbert_token_tree_binder_close,
                fs_named_hilbert_token_tree_decode, hName,
                Formula.closeFreeAt, Formula.next_depth,
                List.map_cons] using congrArg
                  (fun result =>
                    result.bind
                      (fun bodyFormula =>
                        some (Formula.forallE
                          SetSort.set bodyFormula)))
                  hBodyClose
termination_by
  _ tree _ _ => sizeOf tree

/--
成功具名解码可直接形成规范全称闭包的 body token：
先取得规范 binder shift，再把指定低编号自由名替换成新外层 binder 名。
-/
theorem fs_named_hilbert_tokens_decode_with_env_binder_close
    (freeBase id : Nat) (boundNames sourceTokens : List Nat)
    (formula : SetFormula) (hId : id < freeBase)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames sourceTokens =
        some formula) :
    ∃ shiftedTokens,
      CanonicalBinderShiftTokens sourceTokens shiftedTokens ∧
      fs_named_hilbert_tokens_decode_with_env freeBase
          (boundNames.map
              (fs_named_binder_close_name id) ++
            [bound_name 0])
          (substitute_tokens shiftedTokens
            (Numbered.variable_token (free_name id))
            [Numbered.variable_token (bound_name 0)]) =
        some (Formula.closeFreeAt
          SetSort.set id boundNames.length formula) := by
  rcases
      (fs_named_hilbert_tokens_decode_with_env_iff
        freeBase boundNames sourceTokens formula).mp hDecode with
    ⟨tree, hParse, hTree⟩
  have hSource :
      sourceTokens = tree.tokens :=
    (RawHilbertTokenTree.parse?_sound hParse).symm
  have hShift :=
    fs_named_hilbert_token_tree_binder_shift_relation
      freeBase hTree
  have hClose :=
    fs_named_hilbert_token_tree_binder_close_decode
      freeBase id hId hTree
  refine
    ⟨(fs_named_hilbert_token_tree_binder_shift tree).tokens,
      ?_, ?_⟩
  · simpa [hSource] using hShift
  · rw [← fs_named_hilbert_token_tree_binder_close_tokens
      id tree]
    exact
      fs_named_hilbert_tokens_decode_with_env_of_tree
        freeBase
        (boundNames.map
            (fs_named_binder_close_name id) ++
          [bound_name 0])
        hClose

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
