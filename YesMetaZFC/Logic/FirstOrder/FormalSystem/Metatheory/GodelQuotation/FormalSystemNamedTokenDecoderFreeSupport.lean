import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoderComposition

/-!
# 具名 decoder 的低位自由变量反演

统一 `freeBase` 以下的自由变量编号不可能来自非规范奇数名字。本模块把这一
数值分离性质沿项树和 Hilbert 公式树提升到原始 token 串。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory

set_option autoImplicit false

/-- 低于 `freeBase` 的自由变量解码只能来自规范偶数名字。 -/
theorem fs_named_variable_decode_low_fvar
    (freeBase : Nat) (boundNames : List Nat)
    {token id : Nat}
    (hDecode :
      fs_named_variable_decode freeBase boundNames token =
        some (.fvar SetSort.set id))
    (hId : id < freeBase) :
    token = Numbered.variable_token (free_name id) := by
  unfold fs_named_variable_decode at hDecode
  cases hName : fs_variable_name_decode token with
  | none =>
      simp [hName] at hDecode
  | some name =>
      have hToken :
          Numbered.variable_token name = token :=
        fs_variable_name_decode_value_of_some hName
      simp [hName] at hDecode
      unfold fs_named_variable_of_name at hDecode
      cases hBound : fs_bound_name_index name boundNames with
      | some index =>
          simp [hBound] at hDecode
      | none =>
          by_cases hEven : name % 2 = 0
          · simp [hBound, hEven] at hDecode
            have hDiv : name / 2 = id := by
              exact hDecode
            have hNameValue :
                name % 2 + 2 * (name / 2) = name :=
              Nat.mod_add_div name 2
            rw [hEven, hDiv] at hNameValue
            subst name
            simpa [free_name] using hToken.symm
          · simp [hBound, hEven] at hDecode
            subst id
            omega

mutual
  /-- 项树解码出的低位自由变量在原始项 token 中出现。 -/
  theorem fs_named_term_token_tree_decode_low_fvar_mem
      (freeBase : Nat) (boundNames : List Nat) (id : Nat) :
      ∀ {tree : RawTermTokenTree} {term : SetTerm},
        fs_named_term_token_tree_decode
            freeBase boundNames tree =
          some term →
        (SetSort.set, id) ∈ Term.freeSupport term →
        id < freeBase →
        Numbered.variable_token (free_name id) ∈ tree.tokens
    | .atom token, term, hDecode, hMember, hId => by
        cases hVariable :
            fs_named_variable_decode
              freeBase boundNames token with
        | some decodedVariable =>
            simp [fs_named_term_token_tree_decode,
              hVariable] at hDecode
            subst term
            cases decodedVariable with
            | bvar sort index =>
                change (SetSort.set, id) ∈ [] at hMember
                exact (List.not_mem_nil hMember).elim
            | fvar sort variableId =>
                change
                  (SetSort.set, id) ∈
                    [(sort, variableId)] at hMember
                have hPair :
                    (SetSort.set, id) =
                      (sort, variableId) := by
                  exact List.mem_singleton.mp hMember
                cases hPair
                have hToken :=
                  fs_named_variable_decode_low_fvar
                    freeBase boundNames hVariable hId
                simpa [RawTermTokenTree.tokens] using hToken.symm
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
                · simp [fs_named_term_token_tree_decode,
                    hVariable, hSymbol, hDomain] at hDecode
                  subst term
                  change (SetSort.set, id) ∈ [] at hMember
                  exact (List.not_mem_nil hMember).elim
                · simp [fs_named_term_token_tree_decode,
                    hVariable, hSymbol, hDomain] at hDecode
    | .application head arguments, term,
        hDecode, hMember, hId => by
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
            | some terms =>
                by_cases hCheck :
                    Term.check_args_wellSorted terms
                        (signature.funcDomain symbol) =
                      true
                · simp [fs_named_term_token_tree_decode,
                    hSymbol, hArguments, hCheck] at hDecode
                  rcases hDecode with
                    ⟨_, hDecode⟩
                  subst term
                  have hMember' :
                      (SetSort.set, id) ∈
                        Term.freeSupportList terms := by
                    simpa [Term.freeSupport] using hMember
                  have hToken :=
                    fs_named_term_token_trees_decode_low_fvar_mem
                      freeBase boundNames id hArguments
                      hMember' hId
                  simp [RawTermTokenTree.tokens, hToken]
                · simp [fs_named_term_token_tree_decode,
                    hSymbol, hArguments, hCheck] at hDecode
  termination_by tree => sizeOf tree

  /-- 项树列表解码出的低位自由变量在原始扁平 token 中出现。 -/
  theorem fs_named_term_token_trees_decode_low_fvar_mem
      (freeBase : Nat) (boundNames : List Nat) (id : Nat) :
      ∀ {trees : List RawTermTokenTree}
          {terms : List SetTerm},
        trees.mapM
            (fs_named_term_token_tree_decode
              freeBase boundNames) =
          some terms →
        (SetSort.set, id) ∈ Term.freeSupportList terms →
        id < freeBase →
        Numbered.variable_token (free_name id) ∈
          RawTermTokenTree.list_tokens trees
    | .nil, terms, hDecode, hMember, hId => by
        simp at hDecode
        subst terms
        change (SetSort.set, id) ∈ [] at hMember
        exact (List.not_mem_nil hMember).elim
    | .cons tree trees, terms, hDecode, hMember, hId => by
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
                have hMember' :
                    (SetSort.set, id) ∈
                        Term.freeSupport head ∨
                      (SetSort.set, id) ∈
                        Term.freeSupportList tail := by
                  exact List.mem_append.mp hMember
                rcases hMember' with hMember | hMember
                · have hToken :=
                    fs_named_term_token_tree_decode_low_fvar_mem
                      freeBase boundNames id hHead hMember hId
                  simp [RawTermTokenTree.list_tokens, hToken]
                · have hToken :=
                    fs_named_term_token_trees_decode_low_fvar_mem
                      freeBase boundNames id hTail hMember hId
                  simp [RawTermTokenTree.list_tokens, hToken]
  termination_by trees => sizeOf trees
end

/-- Hilbert 树解码出的低位自由变量在原始公式 token 中出现。 -/
theorem fs_named_hilbert_token_tree_decode_low_fvar_mem
    (freeBase id : Nat) :
    ∀ {boundNames : List Nat}
        {tree : RawHilbertTokenTree}
        {formula : SetFormula},
      fs_named_hilbert_token_tree_decode
          freeBase boundNames tree =
        some formula →
      (SetSort.set, id) ∈ Formula.freeSupport formula →
      id < freeBase →
      Numbered.variable_token (free_name id) ∈ tree.tokens
  | boundNames, .equality left right, formula,
      hDecode, hMember, hId => by
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
              rcases hDecode with ⟨_, rfl⟩
              have hMember' :
                  (SetSort.set, id) ∈
                      Term.freeSupport leftTerm ∨
                    (SetSort.set, id) ∈
                      Term.freeSupport rightTerm := by
                have hMember0 :
                    (SetSort.set, id) ∈
                      Term.freeSupport leftTerm ++
                        Term.freeSupport rightTerm := by
                  simpa [Formula.freeSupport,
                    Term.freeSupportList] using hMember
                exact List.mem_append.mp hMember0
              rcases hMember' with hMember | hMember
              · have hToken :=
                  fs_named_term_token_tree_decode_low_fvar_mem
                    freeBase boundNames id hLeft hMember hId
                simp [RawHilbertTokenTree.tokens, hToken]
              · have hToken :=
                  fs_named_term_token_tree_decode_low_fvar_mem
                    freeBase boundNames id hRight hMember hId
                simp [RawHilbertTokenTree.tokens, hToken]
  | boundNames, .membership left right, formula,
      hDecode, hMember, hId => by
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
              rcases hDecode with ⟨_, rfl⟩
              have hMember' :
                  (SetSort.set, id) ∈
                      Term.freeSupport leftTerm ∨
                    (SetSort.set, id) ∈
                      Term.freeSupport rightTerm := by
                have hMember0 :
                    (SetSort.set, id) ∈
                      Term.freeSupport leftTerm ++
                        Term.freeSupport rightTerm := by
                  simpa [Formula.freeSupport,
                    Term.freeSupportList] using hMember
                exact List.mem_append.mp hMember0
              rcases hMember' with hMember | hMember
              · have hToken :=
                  fs_named_term_token_tree_decode_low_fvar_mem
                    freeBase boundNames id hLeft hMember hId
                simp [RawHilbertTokenTree.tokens, hToken]
              · have hToken :=
                  fs_named_term_token_tree_decode_low_fvar_mem
                    freeBase boundNames id hRight hMember hId
                simp [RawHilbertTokenTree.tokens, hToken]
  | boundNames, .predicate head arguments, formula,
      hDecode, hMember, hId => by
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
                  hRelation, hArguments] at hDecode
            | some terms =>
                by_cases hCheck :
                    Term.check_args_wellSorted terms
                        (signature.relDomain relation) =
                      true
                · simp [fs_named_hilbert_token_tree_decode,
                    hRelation, hKind, hArguments,
                    hCheck] at hDecode
                  subst formula
                  have hMember' :
                      (SetSort.set, id) ∈
                        Term.freeSupportList terms := by
                    simpa [Formula.freeSupport] using hMember
                  have hToken :=
                    fs_named_term_token_trees_decode_low_fvar_mem
                      freeBase boundNames id hArguments
                      hMember' hId
                  simp [RawHilbertTokenTree.tokens, hToken]
                · simp [fs_named_hilbert_token_tree_decode,
                    hRelation, hKind, hArguments,
                    hCheck] at hDecode
          · simp [fs_named_hilbert_token_tree_decode,
              hRelation, hKind] at hDecode
  | boundNames, .negation body, formula,
      hDecode, hMember, hId => by
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
          have hMember' :
              (SetSort.set, id) ∈
                Formula.freeSupport bodyFormula := by
            simpa [Formula.freeSupport] using hMember
          have hToken :=
            fs_named_hilbert_token_tree_decode_low_fvar_mem
              freeBase id hBody hMember' hId
          simp [RawHilbertTokenTree.tokens, hToken]
  | boundNames, .implication left right, formula,
      hDecode, hMember, hId => by
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
              have hMember' :
                  (SetSort.set, id) ∈
                      Formula.freeSupport leftFormula ∨
                    (SetSort.set, id) ∈
                      Formula.freeSupport rightFormula := by
                exact List.mem_append.mp hMember
              rcases hMember' with hLeftMember | hRightMember
              · have hToken :=
                  fs_named_hilbert_token_tree_decode_low_fvar_mem
                    freeBase id hLeft hLeftMember hId
                simp [RawHilbertTokenTree.tokens, hToken]
              · have hToken :=
                  fs_named_hilbert_token_tree_decode_low_fvar_mem
                    freeBase id hRight hRightMember hId
                simp [RawHilbertTokenTree.tokens, hToken]
  | boundNames, .universal variableToken body, formula,
      hDecode, hMember, hId => by
      cases hName : fs_variable_name_decode variableToken with
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
              have hMember' :
                  (SetSort.set, id) ∈
                    Formula.freeSupport bodyFormula := by
                simpa [Formula.freeSupport] using hMember
              have hToken :=
                fs_named_hilbert_token_tree_decode_low_fvar_mem
                  freeBase id hBody hMember' hId
              simp [RawHilbertTokenTree.tokens, hToken]
termination_by
  _ tree _ _ _ _ => sizeOf tree

/-- 完整 token 串解码出的低位自由变量在原始串中出现。 -/
theorem fs_named_hilbert_tokens_decode_with_env_low_fvar_mem
    (freeBase : Nat) (boundNames : List Nat)
    {tokens : List Nat} {formula : SetFormula} {id : Nat}
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        some formula)
    (hMember :
      (SetSort.set, id) ∈ Formula.freeSupport formula)
    (hId : id < freeBase) :
    Numbered.variable_token (free_name id) ∈ tokens := by
  rcases
      (fs_named_hilbert_tokens_decode_with_env_iff
        freeBase boundNames tokens formula).mp hDecode with
    ⟨tree, hParse, hTree⟩
  have hToken :=
    fs_named_hilbert_token_tree_decode_low_fvar_mem
      freeBase id hTree hMember hId
  rw [RawHilbertTokenTree.parse?_sound hParse] at hToken
  exact hToken

/--
全称公式解码出的低位自由变量必然出现在原始正文 token 串中。

结论同时恢复原始 binder 名与正文串，避免下游再次反演 parser。
-/
theorem fs_named_hilbert_tokens_decode_with_env_forall_low_fvar_mem
    (freeBase : Nat) (boundNames : List Nat)
    {tokens : List Nat} {body : SetFormula} {id : Nat}
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        some (.forallE SetSort.set body))
    (hMember :
      (SetSort.set, id) ∈ Formula.freeSupport body)
    (hId : id < freeBase) :
    ∃ name bodyTokens,
      tokens =
          Numbered.universal_tokens name bodyTokens ∧
        fs_named_hilbert_tokens_decode_with_env
            freeBase (name :: boundNames) bodyTokens =
          some body ∧
        Numbered.variable_token (free_name id) ∈
          bodyTokens := by
  rcases
      fs_named_hilbert_tokens_decode_with_env_forall_elim
        freeBase boundNames hDecode with
    ⟨name, bodyTokens, hTokens, hBody⟩
  exact
    ⟨name, bodyTokens, hTokens, hBody,
      fs_named_hilbert_tokens_decode_with_env_low_fvar_mem
        freeBase (name :: boundNames)
        hBody hMember hId⟩

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
