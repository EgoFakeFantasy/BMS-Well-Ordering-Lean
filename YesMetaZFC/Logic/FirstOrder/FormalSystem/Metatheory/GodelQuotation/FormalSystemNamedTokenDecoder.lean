import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaCode

/-!
# FormalSystem 具名 binder token 解码

规范 quotation 使用偶数自由变量名与奇数 binder 名，但 `FormulaCodeₘ` 本身并不
要求这种命名范式。负向 checked replay 因而需要一个接受任意变量名的构造性
解码器。

本模块按以下规则恢复变量：

* 当前 binder 名表中第一次出现的位置解释为 de Bruijn index；
* 未绑定偶数名 `2k` 保持为自由变量 `k`；
* 未绑定奇数名统一解释为保留自由变量 `freeBase`。

最后一条使非规范自由名与低于 `freeBase` 的规范自由 ID 不冲突，并使 binder 名
整体平移时未绑定奇数名的语义保持不变。整个过程只遍历有限 token 树，不使用
选择公理。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory

set_option autoImplicit false

/-! ## 变量名环境 -/

/-- 在 binder 名表中查找最内层同名 binder 的 de Bruijn index。 -/
def fs_bound_name_index
    (name : Nat) : List Nat → Option Nat
  | [] =>
      none
  | head :: tail =>
      if head = name then
        some 0
      else
        (fs_bound_name_index name tail).map Nat.succ

/-- 一个变量名对规范自由变量 ID 上界的贡献。 -/
def fs_canonical_free_id_bound
    (name : Nat) : Nat :=
  if name % 2 = 0 then
    name / 2 + 1
  else
    0

/-- 项树中出现的全部可解码变量名。 -/
def fs_term_token_tree_variable_names :
    RawTermTokenTree → List Nat
  | .atom token =>
      (fs_variable_name_decode token).toList
  | .application _ arguments =>
      arguments.flatMap
        fs_term_token_tree_variable_names
termination_by tree => tree

/-- Hilbert 核公式树中出现的全部可解码变量名。 -/
def fs_hilbert_token_tree_variable_names :
    RawHilbertTokenTree → List Nat
  | .equality left right =>
      fs_term_token_tree_variable_names left ++
        fs_term_token_tree_variable_names right
  | .membership left right =>
      fs_term_token_tree_variable_names left ++
        fs_term_token_tree_variable_names right
  | .predicate _ arguments =>
      arguments.flatMap
        fs_term_token_tree_variable_names
  | .negation body =>
      fs_hilbert_token_tree_variable_names body
  | .implication left right =>
      fs_hilbert_token_tree_variable_names left ++
        fs_hilbert_token_tree_variable_names right
  | .universal variableToken body =>
      (fs_variable_name_decode variableToken).toList ++
        fs_hilbert_token_tree_variable_names body
termination_by tree => tree

/--
非规范自由名的起始 ID。该值严格大于树中每个规范偶数自由名对应的 ID。
-/
def fs_hilbert_token_tree_free_base
    (tree : RawHilbertTokenTree) : Nat :=
  (fs_hilbert_token_tree_variable_names tree).foldl
    (fun bound name =>
      max bound (fs_canonical_free_id_bound name))
    0

/-- 在给定 binder 环境与自由 ID 上界下恢复一个变量名。 -/
def fs_named_variable_of_name
    (freeBase : Nat) (boundNames : List Nat)
    (name : Nat) : Var signature :=
  match fs_bound_name_index name boundNames with
  | some index =>
      .bvar SetSort.set index
  | none =>
      if name % 2 = 0 then
        .fvar SetSort.set (name / 2)
      else
        .fvar SetSort.set freeBase

/-- 变量 token 的具名环境解码。 -/
def fs_named_variable_decode
    (freeBase : Nat) (boundNames : List Nat)
    (token : Nat) : Option (Var signature) := do
  let name ← fs_variable_name_decode token
  pure (fs_named_variable_of_name
    freeBase boundNames name)

@[simp]
theorem fs_bound_name_index_head
    (name : Nat) (tail : List Nat) :
    fs_bound_name_index name (name :: tail) =
      some 0 := by
  simp [fs_bound_name_index]

@[simp]
theorem fs_named_variable_of_name_bound_head
    (freeBase name : Nat) (tail : List Nat) :
    fs_named_variable_of_name
        freeBase (name :: tail) name =
      .bvar SetSort.set 0 := by
  simp [fs_named_variable_of_name]

/-! ## 项与公式树解码 -/

/-- 任意变量名环境下的 FormalSystem 项树解码。 -/
def fs_named_term_token_tree_decode
    (freeBase : Nat) (boundNames : List Nat) :
    RawTermTokenTree → Option SetTerm
  | .atom token =>
      match fs_named_variable_decode
          freeBase boundNames token with
      | some decodedVariable =>
          some (.var decodedVariable)
      | none =>
          match fs_find_encoded
              (fun symbol : FunctionSymbol =>
                Numbered.constant_token symbol.ctorIdx)
              token fs_function_symbols with
          | none =>
              none
          | some symbol =>
              if signature.funcDomain symbol = [] then
                some (.app symbol [])
              else
                none
  | .application head arguments =>
      if arguments = [] then
        none
      else do
        let symbol ←
          fs_find_encoded
            (fun candidate : FunctionSymbol =>
              Numbered.function_token
                (arguments.length - 1)
                candidate.ctorIdx)
            head fs_function_symbols
        let decoded ←
          arguments.mapM
            (fs_named_term_token_tree_decode
              freeBase boundNames)
        if Term.check_args_wellSorted decoded
            (signature.funcDomain symbol) then
          some (.app symbol decoded)
        else
          none
termination_by tree => tree

/-- 任意 binder 名表下的 FormalSystem Hilbert 核公式树解码。 -/
def fs_named_hilbert_token_tree_decode
    (freeBase : Nat) :
    List Nat → RawHilbertTokenTree →
      Option SetFormula
  | boundNames, .equality left right => do
      let leftTerm ←
        fs_named_term_token_tree_decode
          freeBase boundNames left
      let rightTerm ←
        fs_named_term_token_tree_decode
          freeBase boundNames right
      if Term.check_wellSorted SetSort.set leftTerm &&
          Term.check_wellSorted SetSort.set rightTerm then
        some (.equal leftTerm rightTerm)
      else
        none
  | boundNames, .membership left right => do
      let leftTerm ←
        fs_named_term_token_tree_decode
          freeBase boundNames left
      let rightTerm ←
        fs_named_term_token_tree_decode
          freeBase boundNames right
      if Term.check_args_wellSorted
          [leftTerm, rightTerm]
          (signature.relDomain
            RelationSymbol.membership) then
        some (.rel RelationSymbol.membership
          [leftTerm, rightTerm])
      else
        none
  | boundNames, .predicate head arguments => do
      let relation ←
        fs_find_encoded
          (fun candidate : RelationSymbol =>
            Numbered.predicate_token
              (arguments.length - 1)
              candidate.ctorIdx)
          head fs_relation_symbols
      if fs_relation_kind relation =
          QuotationRelationKind.predicate then
        let decoded ←
          arguments.mapM
            (fs_named_term_token_tree_decode
              freeBase boundNames)
        if Term.check_args_wellSorted decoded
            (signature.relDomain relation) then
          some (.rel relation decoded)
        else
          none
      else
        none
  | boundNames, .negation body => do
      let bodyFormula ←
        fs_named_hilbert_token_tree_decode
          freeBase boundNames body
      pure (.neg bodyFormula)
  | boundNames, .implication left right => do
      let leftFormula ←
        fs_named_hilbert_token_tree_decode
          freeBase boundNames left
      let rightFormula ←
        fs_named_hilbert_token_tree_decode
          freeBase boundNames right
      pure (.imp leftFormula rightFormula)
  | boundNames, .universal variableToken body => do
      let name ←
        fs_variable_name_decode variableToken
      let bodyFormula ←
        fs_named_hilbert_token_tree_decode
          freeBase (name :: boundNames) body
      pure (.forallE SetSort.set bodyFormula)
termination_by
  _ tree => sizeOf tree

/-! ## Hilbert 核构造分类 -/

/-- 成功的具名树解码必然落在 Hilbert 五种构造子内。 -/
theorem fs_named_hilbert_token_tree_decode_core
    (freeBase : Nat) :
    ∀ {boundNames : List Nat}
      {tree : RawHilbertTokenTree}
      {formula : SetFormula},
      fs_named_hilbert_token_tree_decode
          freeBase boundNames tree =
        some formula →
      Numbered.HilbertCore formula
  | boundNames, .equality left right, formula, hDecode => by
      cases hLeft :
          fs_named_term_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode, hLeft] at hDecode
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
              rw [← hDecode.2]
              exact Numbered.HilbertCore.equality
                leftTerm rightTerm
  | boundNames, .membership left right, formula, hDecode => by
      cases hLeft :
          fs_named_term_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode, hLeft] at hDecode
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
              rw [← hDecode.2]
              exact Numbered.HilbertCore.relation
                RelationSymbol.membership
                [leftTerm, rightTerm]
  | boundNames, .predicate head arguments, formula, hDecode => by
      cases hRelation :
          fs_find_encoded
            (fun candidate : RelationSymbol =>
              Numbered.predicate_token
                (arguments.length - 1)
                candidate.ctorIdx)
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
            | some decoded =>
                by_cases hCheck :
                    Term.check_args_wellSorted decoded
                        (signature.relDomain relation) =
                      true
                · simp [fs_named_hilbert_token_tree_decode,
                    hRelation, hKind, hArguments, hCheck] at hDecode
                  subst formula
                  exact Numbered.HilbertCore.relation
                    relation decoded
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
          subst formula
          exact Numbered.HilbertCore.negation
            (fs_named_hilbert_token_tree_decode_core
              freeBase hBody)
  | boundNames, .implication left right, formula, hDecode => by
      cases hLeft :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode, hLeft] at hDecode
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
              exact Numbered.HilbertCore.implication
                (fs_named_hilbert_token_tree_decode_core
                  freeBase hLeft)
                (fs_named_hilbert_token_tree_decode_core
                  freeBase hRight)
  | boundNames, .universal variableToken body, formula, hDecode => by
      cases hName :
          fs_variable_name_decode variableToken with
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
              subst formula
              exact Numbered.HilbertCore.universal
                SetSort.set
                (fs_named_hilbert_token_tree_decode_core
                  freeBase hBody)

/-! ## 成功解码的良构性 -/

/-- binder 名查找成功时，所得 de Bruijn 位置严格落在当前名字表内。 -/
theorem fs_bound_name_index_lt_length
    (name : Nat) :
    ∀ {names : List Nat} {index : Nat},
      fs_bound_name_index name names = some index →
        index < names.length
  | .nil, index, hIndex => by
      simp [fs_bound_name_index] at hIndex
  | .cons head tail, index, hIndex => by
      by_cases hHead : head = name
      · subst head
        simp [fs_bound_name_index] at hIndex
        subst index
        simp
      · cases hTail :
          fs_bound_name_index name tail with
        | none =>
            simp [fs_bound_name_index, hHead, hTail] at hIndex
        | some tailIndex =>
            simp [fs_bound_name_index, hHead, hTail] at hIndex
            subst index
            exact Nat.succ_lt_succ
              (fs_bound_name_index_lt_length
                name hTail)

/-- 变量 token 成功解码时，所得变量在当前名字表对应的 scope 中合法。 -/
theorem fs_named_variable_decode_admissible
    (freeBase : Nat) (boundNames : List Nat)
    (token : Nat) {decodedVariable : Var signature}
    (hDecode :
      fs_named_variable_decode
          freeBase boundNames token =
        some decodedVariable) :
    Term.AdmissibleAt
      (Numbered.scope_of_names boundNames)
      (.var decodedVariable) SetSort.set := by
  unfold fs_named_variable_decode at hDecode
  cases hName :
      fs_variable_name_decode token with
  | none =>
      simp [hName] at hDecode
  | some name =>
      simp [hName] at hDecode
      unfold fs_named_variable_of_name at hDecode
      cases hBound :
          fs_bound_name_index name boundNames with
      | some index =>
          simp [hBound] at hDecode
          subst decodedVariable
          exact Term.AdmissibleAt.bvar <| by
            simpa [Numbered.scope_of_names] using
              fs_bound_name_index_lt_length
                name hBound
      | none =>
          by_cases hEven : name % 2 = 0
          · simp [hBound, hEven] at hDecode
            subst decodedVariable
            exact Term.AdmissibleAt.fvar
              (σ := signature)
              SetSort.set (name / 2)
          · simp [hBound, hEven] at hDecode
            subst decodedVariable
            exact Term.AdmissibleAt.fvar
              (σ := signature)
              SetSort.set freeBase

mutual
  /--
  具名项树成功解码时，所得项在当前名字表对应的 scope 中合法。
  -/
  theorem fs_named_term_token_tree_decode_admissible
      (freeBase : Nat) (boundNames : List Nat) :
      ∀ {tree : RawTermTokenTree} {term : SetTerm},
        fs_named_term_token_tree_decode
            freeBase boundNames tree =
          some term →
        Term.AdmissibleAt
          (Numbered.scope_of_names boundNames)
          term SetSort.set
    | .atom token, term, hDecode => by
        cases hVariable :
            fs_named_variable_decode
              freeBase boundNames token with
        | some decodedVariable =>
            simp [fs_named_term_token_tree_decode,
              hVariable] at hDecode
            subst term
            exact fs_named_variable_decode_admissible
              freeBase boundNames token hVariable
        | none =>
            cases hSymbol :
                fs_find_encoded
                  (fun symbol : FunctionSymbol =>
                    Numbered.constant_token
                      symbol.ctorIdx)
                  token fs_function_symbols with
            | none =>
                simp [fs_named_term_token_tree_decode,
                  hVariable, hSymbol] at hDecode
            | some symbol =>
                by_cases hDomain :
                    signature.funcDomain symbol = []
                · simp [fs_named_term_token_tree_decode,
                    hVariable, hSymbol,
                    hDomain] at hDecode
                  subst term
                  constructor
                  · have hArguments :
                        ArgsWellSorted []
                          (signature.funcDomain symbol) := by
                      rw [hDomain]
                      exact .nil
                    simpa using
                      TermWellSorted.app
                        (σ := signature)
                        symbol hArguments
                  · exact TermScoped.app
                      (σ := signature) symbol [] <| by
                      simp
                · simp [fs_named_term_token_tree_decode,
                    hVariable, hSymbol,
                    hDomain] at hDecode
    | .application head arguments, term, hDecode => by
        cases hSymbol :
            fs_find_encoded
              (fun candidate : FunctionSymbol =>
                Numbered.function_token
                  (arguments.length - 1)
                  candidate.ctorIdx)
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
            | some decoded =>
                by_cases hCheck :
                    Term.check_args_wellSorted decoded
                        (signature.funcDomain symbol) =
                      true
                · simp [fs_named_term_token_tree_decode,
                    hSymbol, hArguments,
                    hCheck] at hDecode
                  rcases hDecode with
                    ⟨_, hDecode⟩
                  subst term
                  have hDecodedScoped :=
                    fs_named_term_token_trees_decode_scoped
                      freeBase boundNames hArguments
                  have hArgumentsAdmissible :
                      ArgsAdmissibleAt
                        (Numbered.scope_of_names boundNames)
                        decoded
                        (signature.funcDomain symbol) :=
                    ⟨Term.check_args_wellSorted_sound hCheck,
                      hDecodedScoped⟩
                  simpa using
                    Term.AdmissibleAt.app
                      (σ := signature)
                      symbol hArgumentsAdmissible
                · simp [fs_named_term_token_tree_decode,
                    hSymbol, hArguments,
                    hCheck] at hDecode
  termination_by tree => sizeOf tree

  /-- 成功解码的具名项树列表中，每个结果项都满足当前 scope。 -/
  theorem fs_named_term_token_trees_decode_scoped
      (freeBase : Nat) (boundNames : List Nat) :
      ∀ {trees : List RawTermTokenTree}
          {terms : List SetTerm},
        trees.mapM
            (fs_named_term_token_tree_decode
              freeBase boundNames) =
          some terms →
        ∀ term, term ∈ terms →
          TermScoped
            (Numbered.scope_of_names boundNames)
            term
    | .nil, terms, hDecode => by
        have hTerms : terms = [] := by
          simpa using Option.some.inj hDecode.symm
        subst terms
        simp
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
                intro term hTerm
                rcases List.mem_cons.mp hTerm with
                  rfl | hTerm
                · exact
                    (fs_named_term_token_tree_decode_admissible
                      freeBase boundNames hHead).2
                · exact
                    fs_named_term_token_trees_decode_scoped
                      freeBase boundNames hTail
                      term hTerm
  termination_by trees => sizeOf trees
end

/-
成功解码轨迹只能穿过奇数非逻辑首部。该事实正是原始 parser 的词法前提，
后续可以据此把解码成功重新序列化为可解析 token 串。
-/
mutual
  /-- 成功解码的具名项树具有奇数非逻辑首部。 -/
  theorem fs_named_term_token_tree_decode_heads_odd
      (freeBase : Nat) (boundNames : List Nat) :
      ∀ {tree : RawTermTokenTree} {term : SetTerm},
        fs_named_term_token_tree_decode
            freeBase boundNames tree =
          some term →
        tree.HeadsOdd
    | .atom token, term, hDecode => by
        cases hVariable :
            fs_named_variable_decode
              freeBase boundNames token with
        | some decodedVariable =>
            unfold fs_named_variable_decode at hVariable
            cases hName :
                fs_variable_name_decode token with
            | none =>
                simp [hName] at hVariable
            | some name =>
                have hToken :
                    Numbered.variable_token name =
                      token :=
                  fs_variable_name_decode_value_of_some
                    hName
                simpa [RawTermTokenTree.HeadsOdd,
                  ← hToken] using
                    variable_token_odd name
        | none =>
            cases hSymbol :
                fs_find_encoded
                  (fun symbol : FunctionSymbol =>
                    Numbered.constant_token
                      symbol.ctorIdx)
                  token fs_function_symbols with
            | none =>
                simp [fs_named_term_token_tree_decode,
                  hVariable, hSymbol] at hDecode
            | some symbol =>
                by_cases hDomain :
                    signature.funcDomain symbol = []
                · have hToken :
                      Numbered.constant_token
                          symbol.ctorIdx =
                        token :=
                    fs_find_encoded_value_of_some
                      (encode :=
                        fun candidate : FunctionSymbol =>
                          Numbered.constant_token
                            candidate.ctorIdx)
                      (target := token)
                      (items := fs_function_symbols)
                      (item := symbol)
                      hSymbol
                  simpa [RawTermTokenTree.HeadsOdd,
                    ← hToken] using
                      constant_token_odd symbol.ctorIdx
                · simp [fs_named_term_token_tree_decode,
                    hVariable, hSymbol,
                    hDomain] at hDecode
    | .application head arguments, term, hDecode => by
        cases hSymbol :
            fs_find_encoded
              (fun symbol : FunctionSymbol =>
                Numbered.function_token
                  (arguments.length - 1)
                  symbol.ctorIdx)
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
            | some decoded =>
                by_cases hCheck :
                    Term.check_args_wellSorted decoded
                        (signature.funcDomain symbol) =
                      true
                · have hToken :
                      Numbered.function_token
                          (arguments.length - 1)
                          symbol.ctorIdx =
                        head :=
                    fs_find_encoded_value_of_some
                      (encode :=
                        fun candidate : FunctionSymbol =>
                          Numbered.function_token
                            (arguments.length - 1)
                            candidate.ctorIdx)
                      (target := head)
                      (items := fs_function_symbols)
                      (item := symbol)
                      hSymbol
                  have hHeadOdd : head % 2 = 1 := by
                    rw [← hToken]
                    exact function_token_odd
                      (arguments.length - 1)
                      symbol.ctorIdx
                  have hArgumentsOdd :
                      RawTermTokenTree.ListHeadsOdd
                        arguments :=
                    fs_named_term_token_trees_decode_heads_odd
                      freeBase boundNames hArguments
                  simpa only [RawTermTokenTree.HeadsOdd,
                    RawTermTokenTree.ListHeadsOdd] using
                      And.intro hHeadOdd hArgumentsOdd
                · simp [fs_named_term_token_tree_decode,
                    hSymbol, hArguments,
                    hCheck] at hDecode
  termination_by tree => sizeOf tree

  /-- 成功解码的具名项树列表逐项具有奇数非逻辑首部。 -/
  theorem fs_named_term_token_trees_decode_heads_odd
      (freeBase : Nat) (boundNames : List Nat) :
      ∀ {trees : List RawTermTokenTree}
          {terms : List SetTerm},
        trees.mapM
            (fs_named_term_token_tree_decode
              freeBase boundNames) =
          some terms →
        RawTermTokenTree.ListHeadsOdd trees
    | .nil, terms, hDecode => by
        intro tree hTree
        simp at hTree
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
                have hTreeOdd :
                    tree.HeadsOdd :=
                  fs_named_term_token_tree_decode_heads_odd
                    freeBase boundNames hHead
                have hTreesOdd :
                    RawTermTokenTree.ListHeadsOdd
                      trees :=
                  fs_named_term_token_trees_decode_heads_odd
                    freeBase boundNames hTail
                intro candidate hCandidate
                rcases List.mem_cons.mp hCandidate with
                  rfl | hCandidate
                · exact hTreeOdd
                · exact hTreesOdd candidate hCandidate
  termination_by trees => sizeOf trees
end

/--
具名 Hilbert 树成功解码时，原始树满足公开 parser 的全部词法分离条件。
-/
theorem fs_named_hilbert_token_tree_decode_lexically_separated
    (freeBase : Nat) :
    ∀ {boundNames : List Nat}
        {tree : RawHilbertTokenTree}
        {formula : SetFormula},
      fs_named_hilbert_token_tree_decode
          freeBase boundNames tree =
        some formula →
      tree.LexicallySeparated
  | boundNames, .equality left right,
      formula, hDecode => by
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
              exact
                ⟨fs_named_term_token_tree_decode_heads_odd
                    freeBase boundNames hLeft,
                  fs_named_term_token_tree_decode_heads_odd
                    freeBase boundNames hRight⟩
  | boundNames, .membership left right,
      formula, hDecode => by
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
              exact
                ⟨fs_named_term_token_tree_decode_heads_odd
                    freeBase boundNames hLeft,
                  fs_named_term_token_tree_decode_heads_odd
                    freeBase boundNames hRight⟩
  | boundNames, .predicate head arguments,
      formula, hDecode => by
      cases hRelation :
          fs_find_encoded
            (fun relation : RelationSymbol =>
              Numbered.predicate_token
                (arguments.length - 1)
                relation.ctorIdx)
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
                  hRelation,
                  hArguments] at hDecode
            | some decoded =>
                have hToken :
                    Numbered.predicate_token
                        (arguments.length - 1)
                        relation.ctorIdx =
                      head :=
                  fs_find_encoded_value_of_some
                    (encode :=
                      fun candidate : RelationSymbol =>
                        Numbered.predicate_token
                          (arguments.length - 1)
                          candidate.ctorIdx)
                    (target := head)
                    (items := fs_relation_symbols)
                    (item := relation)
                    hRelation
                constructor
                · rw [← hToken]
                  exact predicate_token_odd
                    (arguments.length - 1)
                    relation.ctorIdx
                · exact
                    fs_named_term_token_trees_decode_heads_odd
                      freeBase boundNames hArguments
          · simp [fs_named_hilbert_token_tree_decode,
              hRelation, hKind] at hDecode
  | boundNames, .negation body,
      formula, hDecode => by
      cases hBody :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames body with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hBody] at hDecode
      | some bodyFormula =>
          exact
            fs_named_hilbert_token_tree_decode_lexically_separated
              freeBase
              (boundNames := boundNames)
              (tree := body)
              (formula := bodyFormula)
              hBody
  | boundNames, .implication left right,
      formula, hDecode => by
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
              exact
                ⟨fs_named_hilbert_token_tree_decode_lexically_separated
                    freeBase hLeft,
                  fs_named_hilbert_token_tree_decode_lexically_separated
                    freeBase hRight⟩
  | boundNames, .universal variableToken body,
      formula, hDecode => by
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
              exact
                fs_named_hilbert_token_tree_decode_lexically_separated
                  freeBase
                  (boundNames := name :: boundNames)
                  (tree := body)
                  (formula := bodyFormula)
                  hBody
termination_by
  _ tree _ _ => sizeOf tree

/--
具名 Hilbert 树成功解码时，所得公式在当前名字表对应的 scope 中合法。
-/
theorem fs_named_hilbert_token_tree_decode_admissible
    (freeBase : Nat) :
    ∀ {boundNames : List Nat}
        {tree : RawHilbertTokenTree}
        {formula : SetFormula},
      fs_named_hilbert_token_tree_decode
          freeBase boundNames tree =
        some formula →
      Formula.AdmissibleAt
        (Numbered.scope_of_names boundNames)
        formula
  | boundNames, .equality left right,
      formula, hDecode => by
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
              have hLeftAdmissible :=
                fs_named_term_token_tree_decode_admissible
                  freeBase boundNames hLeft
              have hRightAdmissible :=
                fs_named_term_token_tree_decode_admissible
                  freeBase boundNames hRight
              have hLeftCheck :=
                Term.check_wellSorted_complete
                  hLeftAdmissible.1
              have hRightCheck :=
                Term.check_wellSorted_complete
                  hRightAdmissible.1
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight, hLeftCheck,
                hRightCheck] at hDecode
              subst formula
              exact Formula.AdmissibleAt.equal
                hLeftAdmissible hRightAdmissible
  | boundNames, .membership left right,
      formula, hDecode => by
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
                        RelationSymbol.membership) =
                    true
              · simp [fs_named_hilbert_token_tree_decode,
                  hLeft, hRight, hCheck] at hDecode
                subst formula
                have hLeftAdmissible :=
                  fs_named_term_token_tree_decode_admissible
                    freeBase boundNames hLeft
                have hRightAdmissible :=
                  fs_named_term_token_tree_decode_admissible
                    freeBase boundNames hRight
                apply Formula.AdmissibleAt.rel
                exact
                  ⟨Term.check_args_wellSorted_sound hCheck,
                    by
                      intro term hTerm
                      simp only [List.mem_cons,
                        List.not_mem_nil, or_false] at hTerm
                      rcases hTerm with rfl | rfl
                      · exact hLeftAdmissible.2
                      · exact hRightAdmissible.2⟩
              · simp [fs_named_hilbert_token_tree_decode,
                  hLeft, hRight, hCheck] at hDecode
  | boundNames, .predicate head arguments,
      formula, hDecode => by
      cases hRelation :
          fs_find_encoded
            (fun candidate : RelationSymbol =>
              Numbered.predicate_token
                (arguments.length - 1)
                candidate.ctorIdx)
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
                  hRelation,
                  hArguments] at hDecode
            | some decoded =>
                by_cases hCheck :
                    Term.check_args_wellSorted decoded
                        (signature.relDomain relation) =
                      true
                · simp [fs_named_hilbert_token_tree_decode,
                    hRelation, hKind,
                    hArguments, hCheck] at hDecode
                  subst formula
                  apply Formula.AdmissibleAt.rel
                  exact
                    ⟨Term.check_args_wellSorted_sound hCheck,
                      fs_named_term_token_trees_decode_scoped
                        freeBase boundNames hArguments⟩
                · simp [fs_named_hilbert_token_tree_decode,
                    hRelation, hKind,
                    hArguments, hCheck] at hDecode
          · simp [fs_named_hilbert_token_tree_decode,
              hRelation, hKind] at hDecode
  | boundNames, .negation body,
      formula, hDecode => by
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
          exact Formula.AdmissibleAt.neg <|
            fs_named_hilbert_token_tree_decode_admissible
              freeBase hBody
  | boundNames, .implication left right,
      formula, hDecode => by
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
              exact Formula.AdmissibleAt.imp
                (fs_named_hilbert_token_tree_decode_admissible
                  freeBase hLeft)
                (fs_named_hilbert_token_tree_decode_admissible
                  freeBase hRight)
  | boundNames, .universal variableToken body,
      formula, hDecode => by
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
              have hBodyAdmissible :=
                fs_named_hilbert_token_tree_decode_admissible
                  freeBase hBody
              rw [Numbered.scope_of_names_cons
                name boundNames SetSort.set] at hBodyAdmissible
              exact Formula.AdmissibleAt.forallE
                (σ := signature)
                (scope :=
                  Numbered.scope_of_names boundNames)
                SetSort.set hBodyAdmissible
termination_by
  _ tree _ _ => sizeOf tree

/--
任意具名 token 串到 admissible FormalSystem Hilbert 核公式的 checked 解码。
-/
def fs_named_hilbert_tokens_decode
    (tokens : List Nat) :
    Option SetFormula := do
  let tree ← RawHilbertTokenTree.parse? tokens
  let formula ←
    fs_named_hilbert_token_tree_decode
      (fs_hilbert_token_tree_free_base tree)
      [] tree
  pure formula

/-- 具名 checked token 解码成功时，结果满足公共 admissibility 边界。 -/
theorem fs_named_hilbert_tokens_decode_admissible
    {tokens : List Nat}
    {formula : SetFormula}
    (hDecode :
      fs_named_hilbert_tokens_decode tokens =
        some formula) :
    Formula.Admissible formula := by
  unfold fs_named_hilbert_tokens_decode at hDecode
  cases hParse :
      RawHilbertTokenTree.parse? tokens with
  | none =>
      simp [hParse] at hDecode
  | some tree =>
      cases hTree :
          fs_named_hilbert_token_tree_decode
            (fs_hilbert_token_tree_free_base tree)
            [] tree with
      | none =>
          simp [hParse, hTree] at hDecode
      | some decoded =>
          simp [hParse, hTree] at hDecode
          subst formula
          simpa [Numbered.scope_of_names,
            Scope.empty] using
            fs_named_hilbert_token_tree_decode_admissible
              (fs_hilbert_token_tree_free_base tree)
              hTree

/-! ## 核心构造子的成功闭包 -/

/--
具名 decoder 对否定外壳封闭。

正文与否定树共享全部变量名，因此自由变量基数无需重新运输；该事实是
parser 失败反演把整行失败压回正文失败的第一条构造子接口。
-/
theorem fs_named_hilbert_tokens_decode_negation
    {bodyTokens : List Nat}
    {bodyFormula : SetFormula}
    (hBody :
      fs_named_hilbert_tokens_decode bodyTokens =
        some bodyFormula) :
    fs_named_hilbert_tokens_decode
        (Numbered.negation_tokens bodyTokens) =
      some (.neg bodyFormula) := by
  unfold fs_named_hilbert_tokens_decode at hBody ⊢
  cases hParse :
      RawHilbertTokenTree.parse? bodyTokens with
  | none =>
      simp [hParse] at hBody
  | some bodyTree =>
      cases hTree :
          fs_named_hilbert_token_tree_decode
            (fs_hilbert_token_tree_free_base bodyTree)
            [] bodyTree with
      | none =>
          simp [hParse, hTree] at hBody
      | some decodedBody =>
          have hFormula :
              decodedBody = bodyFormula := by
            simpa [hParse, hTree] using hBody
          subst bodyFormula
          have hTreeTokens :
              bodyTree.tokens = bodyTokens :=
            RawHilbertTokenTree.parse?_sound hParse
          let negTree : RawHilbertTokenTree :=
            .negation bodyTree
          have hNegTokens :
              negTree.tokens =
                Numbered.negation_tokens bodyTokens := by
            simp [negTree, RawHilbertTokenTree.tokens,
              Numbered.negation_tokens, hTreeTokens
              ]
          have hSeparated :
              negTree.LexicallySeparated := by
            simpa [negTree,
              RawHilbertTokenTree.LexicallySeparated] using
              fs_named_hilbert_token_tree_decode_lexically_separated
                (fs_hilbert_token_tree_free_base bodyTree)
                hTree
          have hNegParse :
              RawHilbertTokenTree.parse?
                  (Numbered.negation_tokens bodyTokens) =
                some negTree := by
            rw [← hNegTokens]
            exact RawHilbertTokenTree.parse?_tokens
              negTree hSeparated
          have hFreeBase :
              fs_hilbert_token_tree_free_base negTree =
                fs_hilbert_token_tree_free_base bodyTree := by
            simp [negTree, fs_hilbert_token_tree_free_base,
              fs_hilbert_token_tree_variable_names]
          have hNegTree :
              fs_named_hilbert_token_tree_decode
                  (fs_hilbert_token_tree_free_base negTree)
                  [] negTree =
                some (.neg decodedBody) := by
            simp [negTree, hFreeBase,
              fs_named_hilbert_token_tree_decode,
              hTree]
          simp [hNegParse, hNegTree]

/-! ## 规范 decoder 成功轨迹的扩张 -/

/-- 查找不到的名字不产生 binder 索引。 -/
theorem fs_bound_name_index_eq_none_of_not_mem
    (name : Nat) :
    ∀ {names : List Nat},
      name ∉ names →
        fs_bound_name_index name names = none
  | .nil, _ => rfl
  | .cons head tail, hMissing => by
      have hHead : head ≠ name := by
        intro hEqual
        exact hMissing (by simp [hEqual])
      have hTail : name ∉ tail := by
        intro hMember
        exact hMissing (by simp [hMember])
      simp [fs_bound_name_index, hHead,
        fs_bound_name_index_eq_none_of_not_mem
          name hTail]

/--
无重复名字表中，已知位置的名字由最内层优先查找精确恢复到该位置。
-/
theorem fs_bound_name_index_of_getElem?
    {name : Nat} :
    ∀ {names : List Nat} {index : Nat},
      names.Nodup →
      names[index]? = some name →
        fs_bound_name_index name names = some index
  | .nil, index, hNodup, hGet => by
      simp at hGet
  | .cons head tail, 0, hNodup, hGet => by
      simp only [List.getElem?_cons_zero] at hGet
      have hEqual : head = name :=
        Option.some.inj hGet
      subst head
      simp [fs_bound_name_index]
  | .cons head tail, index + 1, hNodup, hGet => by
      simp only [List.getElem?_cons_succ] at hGet
      have hNodupData := List.nodup_cons.mp hNodup
      have hNameMem : name ∈ tail :=
        List.mem_of_getElem? hGet
      have hHead : head ≠ name := by
        intro hEqual
        subst head
        exact hNodupData.1 hNameMem
      have hTail :=
        fs_bound_name_index_of_getElem?
          hNodupData.2 hGet
      simp [fs_bound_name_index, hHead, hTail]

/-- 规范 binder 环境中的 de Bruijn 位置由具名查找精确恢复。 -/
theorem fs_bound_name_index_canonical
    (depth index : Nat)
    (hIndex : index < depth) :
    fs_bound_name_index
        (bound_name (depth - index - 1))
        (canonical_bound_names depth) =
      some index := by
  exact fs_bound_name_index_of_getElem?
    (canonical_bound_names_nodup depth)
    (canonical_bound_names_getElem?
      depth index hIndex)

/--
规范变量 decoder 的任意成功结果，也是具名 decoder 在同一规范 binder 环境中的
成功结果。
-/
theorem fs_named_variable_decode_of_canonical
    (freeBase depth token : Nat)
    {value : Var signature}
    (hDecode :
      fs_variable_decode depth token =
        some value) :
    fs_named_variable_decode
        freeBase (canonical_bound_names depth) token =
      some value := by
  unfold fs_variable_decode at hDecode
  unfold fs_named_variable_decode
  cases hName :
      fs_variable_name_decode token with
  | none =>
      simp [hName] at hDecode
  | some name =>
      simp only [hName] at hDecode ⊢
      unfold fs_variable_of_name at hDecode
      by_cases hEven : name % 2 = 0
      · by_cases hCanonical :
          free_name (name / 2) = name
        · have hBound :
              fs_bound_name_index name
                  (canonical_bound_names depth) =
                none := by
            rw [← hCanonical]
            exact
              fs_bound_name_index_eq_none_of_not_mem
                (free_name (name / 2))
                (free_name_not_mem_canonical
                  (name / 2) depth)
          simp [hEven, hCanonical] at hDecode
          subst value
          simp [fs_named_variable_of_name,
            hBound, hEven]
        · simp [hEven, hCanonical] at hDecode
      · by_cases hPrior : name / 2 < depth
        · have hNameBound :
              bound_name (name / 2) = name := by
            unfold bound_name
            omega
          have hIndex :
              depth - name / 2 - 1 < depth := by
            omega
          have hBound :
              fs_bound_name_index name
                  (canonical_bound_names depth) =
                some (depth - name / 2 - 1) := by
            have hArithmetic :
                depth -
                    (depth - name / 2 - 1) -
                    1 =
                  name / 2 := by
              omega
            simpa [hNameBound, hArithmetic] using
              fs_bound_name_index_canonical
                depth (depth - name / 2 - 1)
                hIndex
          simp [hEven, hPrior] at hDecode
          subst value
          simp [fs_named_variable_of_name,
            hBound]
        · simp [hEven, hPrior] at hDecode

mutual
  /--
  规范项树 decoder 的成功轨迹在具名环境中保持成功。
  -/
  theorem fs_named_term_token_tree_decode_of_canonical
      (freeBase depth : Nat) :
      ∀ {tree : RawTermTokenTree} {term : SetTerm},
        fs_term_token_tree_decode depth tree =
            some term →
          fs_named_term_token_tree_decode
              freeBase (canonical_bound_names depth) tree =
            some term
    | .atom token, term, hDecode => by
        cases hVariable :
            fs_variable_decode depth token with
        | some decodedVariable =>
            simp [fs_term_token_tree_decode,
              hVariable] at hDecode
            subst term
            have hNamed :=
              fs_named_variable_decode_of_canonical
                freeBase depth token hVariable
            simp [fs_named_term_token_tree_decode,
              hNamed]
        | none =>
            cases hConstant :
                fs_find_encoded
                  (fun symbol : FunctionSymbol =>
                    Numbered.constant_token
                      symbol.ctorIdx)
                  token fs_function_symbols with
            | none =>
                simp [fs_term_token_tree_decode,
                  hVariable, hConstant] at hDecode
            | some symbol =>
                by_cases hDomain :
                    signature.funcDomain symbol = []
                · simp [fs_term_token_tree_decode,
                    hVariable, hConstant,
                    hDomain] at hDecode
                  subst term
                  have hToken :
                      Numbered.constant_token
                          symbol.ctorIdx =
                        token :=
                    fs_find_encoded_value_of_some
                      (encode :=
                        fun candidate : FunctionSymbol =>
                          Numbered.constant_token
                            candidate.ctorIdx)
                      (target := token)
                      (items := fs_function_symbols)
                      (item := symbol)
                      hConstant
                  have hNamedVariable :
                      fs_named_variable_decode
                          freeBase
                          (canonical_bound_names depth)
                          token =
                        none := by
                    rw [← hToken]
                    simp [fs_named_variable_decode]
                  simp [fs_named_term_token_tree_decode,
                    hNamedVariable, hConstant, hDomain]
                · simp [fs_term_token_tree_decode,
                    hVariable, hConstant,
                    hDomain] at hDecode
    | .application head arguments, term, hDecode => by
        cases hSymbol :
            fs_find_encoded
              (fun candidate : FunctionSymbol =>
                Numbered.function_token
                  (arguments.length - 1)
                  candidate.ctorIdx)
              head fs_function_symbols with
        | none =>
            simp [fs_term_token_tree_decode,
              hSymbol] at hDecode
        | some symbol =>
            cases hArguments :
                arguments.mapM
                  (fs_term_token_tree_decode depth) with
            | none =>
                simp [fs_term_token_tree_decode,
                  hSymbol, hArguments] at hDecode
            | some decoded =>
                by_cases hCheck :
                    Term.check_args_wellSorted decoded
                        (signature.funcDomain symbol) =
                      true
                · simp [fs_term_token_tree_decode,
                    hSymbol, hArguments,
                    hCheck] at hDecode
                  rcases hDecode with
                    ⟨hNonempty, hDecode⟩
                  subst term
                  have hNamedArguments :=
                    fs_named_term_token_trees_decode_of_canonical
                      freeBase depth hArguments
                  simp [fs_named_term_token_tree_decode,
                    hNonempty, hSymbol,
                    hNamedArguments, hCheck]
                · simp [fs_term_token_tree_decode,
                    hSymbol, hArguments,
                    hCheck] at hDecode
  termination_by tree => sizeOf tree

  /-- 规范项树列表的逐项成功轨迹在具名环境中保持成功。 -/
  theorem fs_named_term_token_trees_decode_of_canonical
      (freeBase depth : Nat) :
      ∀ {trees : List RawTermTokenTree}
          {terms : List SetTerm},
        trees.mapM
            (fs_term_token_tree_decode depth) =
          some terms →
        trees.mapM
            (fs_named_term_token_tree_decode
              freeBase (canonical_bound_names depth)) =
          some terms
    | .nil, terms, hDecode => by
        have hTerms : terms = [] := by
          simpa using Option.some.inj hDecode.symm
        subst terms
        rfl
    | .cons tree trees, terms, hDecode => by
        cases hHead :
            fs_term_token_tree_decode depth tree with
        | none =>
            simp [List.mapM_cons, hHead] at hDecode
        | some head =>
            cases hTail :
                trees.mapM
                  (fs_term_token_tree_decode depth) with
            | none =>
                simp [List.mapM_cons,
                  hHead, hTail] at hDecode
            | some tail =>
                simp [List.mapM_cons,
                  hHead, hTail] at hDecode
                subst terms
                have hNamedHead :=
                  fs_named_term_token_tree_decode_of_canonical
                    freeBase depth hHead
                have hNamedTail :=
                  fs_named_term_token_trees_decode_of_canonical
                    freeBase depth hTail
                simp [List.mapM_cons,
                  hNamedHead, hNamedTail]
  termination_by trees => sizeOf trees
end

/--
规范 Hilbert 公式树 decoder 的成功轨迹在具名 binder 环境中保持成功。
-/
theorem fs_named_hilbert_token_tree_decode_of_canonical
    (freeBase depth : Nat) :
    ∀ {tree : RawHilbertTokenTree}
        {formula : SetFormula},
      fs_hilbert_token_tree_decode depth tree =
          some formula →
        fs_named_hilbert_token_tree_decode
            freeBase (canonical_bound_names depth) tree =
          some formula
  | .equality left right, formula, hDecode => by
      cases hLeft :
          fs_term_token_tree_decode depth left with
      | none =>
          simp [fs_hilbert_token_tree_decode,
            hLeft] at hDecode
      | some leftTerm =>
          cases hRight :
              fs_term_token_tree_decode depth right with
          | none =>
              simp [fs_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
          | some rightTerm =>
              simp [fs_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
              have hNamedLeft :=
                fs_named_term_token_tree_decode_of_canonical
                  freeBase depth hLeft
              have hNamedRight :=
                fs_named_term_token_tree_decode_of_canonical
                  freeBase depth hRight
              rw [← hDecode.2]
              simp [fs_named_hilbert_token_tree_decode,
                hNamedLeft, hNamedRight,
                hDecode.1.1, hDecode.1.2]
  | .membership left right, formula, hDecode => by
      cases hLeft :
          fs_term_token_tree_decode depth left with
      | none =>
          simp [fs_hilbert_token_tree_decode,
            hLeft] at hDecode
      | some leftTerm =>
          cases hRight :
              fs_term_token_tree_decode depth right with
          | none =>
              simp [fs_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
          | some rightTerm =>
              by_cases hCheck :
                  Term.check_args_wellSorted
                      [leftTerm, rightTerm]
                      (signature.relDomain
                        RelationSymbol.membership) =
                    true
              · simp [fs_hilbert_token_tree_decode,
                  hLeft, hRight, hCheck] at hDecode
                subst formula
                have hNamedLeft :=
                  fs_named_term_token_tree_decode_of_canonical
                    freeBase depth hLeft
                have hNamedRight :=
                  fs_named_term_token_tree_decode_of_canonical
                    freeBase depth hRight
                simp [fs_named_hilbert_token_tree_decode,
                  hNamedLeft, hNamedRight, hCheck]
              · simp [fs_hilbert_token_tree_decode,
                  hLeft, hRight, hCheck] at hDecode
  | .predicate head arguments, formula, hDecode => by
      cases hRelation :
          fs_find_encoded
            (fun candidate : RelationSymbol =>
              Numbered.predicate_token
                (arguments.length - 1)
                candidate.ctorIdx)
            head fs_relation_symbols with
      | none =>
          simp [fs_hilbert_token_tree_decode,
            hRelation] at hDecode
      | some relation =>
          by_cases hKind :
              fs_relation_kind relation =
                QuotationRelationKind.predicate
          · cases hArguments :
                arguments.mapM
                  (fs_term_token_tree_decode depth) with
            | none =>
                simp [fs_hilbert_token_tree_decode,
                  hRelation, hArguments] at hDecode
            | some decoded =>
                by_cases hCheck :
                    Term.check_args_wellSorted decoded
                        (signature.relDomain relation) =
                      true
                · simp [fs_hilbert_token_tree_decode,
                    hRelation, hKind,
                    hArguments, hCheck] at hDecode
                  subst formula
                  have hNamedArguments :=
                    fs_named_term_token_trees_decode_of_canonical
                      freeBase depth hArguments
                  simp [fs_named_hilbert_token_tree_decode,
                    hRelation, hKind,
                    hNamedArguments, hCheck]
                · simp [fs_hilbert_token_tree_decode,
                    hRelation, hKind,
                    hArguments, hCheck] at hDecode
          · simp [fs_hilbert_token_tree_decode,
              hRelation, hKind] at hDecode
  | .negation body, formula, hDecode => by
      cases hBody :
          fs_hilbert_token_tree_decode depth body with
      | none =>
          simp [fs_hilbert_token_tree_decode,
            hBody] at hDecode
      | some bodyFormula =>
          simp [fs_hilbert_token_tree_decode,
            hBody] at hDecode
          subst formula
          have hNamedBody :=
            fs_named_hilbert_token_tree_decode_of_canonical
              freeBase depth hBody
          simp [fs_named_hilbert_token_tree_decode,
            hNamedBody]
  | .implication left right, formula, hDecode => by
      cases hLeft :
          fs_hilbert_token_tree_decode depth left with
      | none =>
          simp [fs_hilbert_token_tree_decode,
            hLeft] at hDecode
      | some leftFormula =>
          cases hRight :
              fs_hilbert_token_tree_decode depth right with
          | none =>
              simp [fs_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
          | some rightFormula =>
              simp [fs_hilbert_token_tree_decode,
                hLeft, hRight] at hDecode
              subst formula
              have hNamedLeft :=
                fs_named_hilbert_token_tree_decode_of_canonical
                  freeBase depth hLeft
              have hNamedRight :=
                fs_named_hilbert_token_tree_decode_of_canonical
                  freeBase depth hRight
              simp [fs_named_hilbert_token_tree_decode,
                hNamedLeft, hNamedRight]
  | .universal variableToken body, formula, hDecode => by
      by_cases hVariable :
          variableToken =
            Numbered.variable_token
              (bound_name depth)
      · cases hBody :
            fs_hilbert_token_tree_decode
              (depth + 1) body with
        | none =>
            simp [fs_hilbert_token_tree_decode,
              hVariable, hBody] at hDecode
        | some bodyFormula =>
            simp [fs_hilbert_token_tree_decode,
              hVariable, hBody] at hDecode
            subst formula
            have hName :
                fs_variable_name_decode variableToken =
                  some (bound_name depth) := by
              rw [hVariable]
              exact fs_variable_name_decode_encode
                (bound_name depth)
            have hNamedBody :=
              fs_named_hilbert_token_tree_decode_of_canonical
                freeBase (depth + 1) hBody
            have hNames :
                canonical_bound_names (depth + 1) =
                  bound_name depth ::
                    canonical_bound_names depth := by
              rw [show depth + 1 = Nat.succ depth by omega]
              rfl
            rw [hNames] at hNamedBody
            simp [fs_named_hilbert_token_tree_decode,
              hName, hNamedBody]
      · simp [fs_hilbert_token_tree_decode,
          hVariable] at hDecode
termination_by tree => sizeOf tree

/--
规范整串 decoder 的成功结果也是具名 decoder 的成功结果。
-/
theorem fs_named_hilbert_tokens_decode_of_canonical
    {tokens : List Nat}
    {formula : SetFormula}
    (hDecode :
      fs_hilbert_tokens_decode tokens =
        some formula) :
    fs_named_hilbert_tokens_decode tokens =
      some formula := by
  unfold fs_hilbert_tokens_decode at hDecode
  cases hParse :
      RawHilbertTokenTree.parse? tokens with
  | none =>
      simp [hParse] at hDecode
  | some tree =>
      cases hTree :
          fs_hilbert_token_tree_decode 0 tree with
      | none =>
          simp [hParse, hTree] at hDecode
      | some decoded =>
          by_cases hCheck :
              Formula.check_admissible decoded =
                true
          · have hFormula :
                decoded = formula := by
              simpa [hParse, hTree, hCheck] using
                hDecode
            subst formula
            have hNamedTree :=
              fs_named_hilbert_token_tree_decode_of_canonical
                (fs_hilbert_token_tree_free_base tree)
                0 hTree
            have hNamedTree' :
                fs_named_hilbert_token_tree_decode
                    (fs_hilbert_token_tree_free_base tree)
                    [] tree =
                  some decoded := by
              simpa [canonical_bound_names] using
                hNamedTree
            simp [fs_named_hilbert_tokens_decode,
              hParse, hNamedTree']
          · simp [hParse, hTree, hCheck] at hDecode

/-- 公共规范 quotation 由具名 decoder 精确恢复为 Hilbert 归约公式。 -/
theorem fs_named_hilbert_tokens_decode_quote
    {formula : SetFormula}
    {tokens : List Nat}
    (hFormula : Formula.Admissible formula)
    (hQuote :
      Numbered.quote_tokens? formula =
        some tokens) :
    fs_named_hilbert_tokens_decode tokens =
      some (Formula.hilbertize SetSort.set formula) :=
  fs_named_hilbert_tokens_decode_of_canonical
    (fs_hilbert_tokens_decode_quote
      hFormula hQuote)

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
