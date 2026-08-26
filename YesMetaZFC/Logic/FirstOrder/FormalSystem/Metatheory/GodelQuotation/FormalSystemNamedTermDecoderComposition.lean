import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoder
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.TermQuotation

/-!
# FormalSystem 具名项 token 解码的构造闭包

本模块只把公共项 parser 与具名项树 decoder 接成显式环境接口。它不复制
parser，也不引入新的符号判定；后续项码反演和原子公式反演共享这里的树级
成功见证。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 显式自由变量基数与 binder 环境下的完整项 token 解码。 -/
def fs_named_term_tokens_decode_with_env
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat) : Option SetTerm := do
  let tree ← RawTermTokenTree.parse? tokens
  fs_named_term_token_tree_decode
    freeBase boundNames tree

/-- 显式环境项解码成功等价于存在同一 parser 树及其树级解码轨迹。 -/
theorem fs_named_term_tokens_decode_with_env_iff
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat) (term : SetTerm) :
    fs_named_term_tokens_decode_with_env
        freeBase boundNames tokens =
      some term ↔
    ∃ tree,
      RawTermTokenTree.parse? tokens = some tree ∧
        fs_named_term_token_tree_decode
            freeBase boundNames tree =
          some term := by
  unfold fs_named_term_tokens_decode_with_env
  cases hParse : RawTermTokenTree.parse? tokens with
  | none =>
      simp
  | some tree =>
      simp

/-- 成功的树级项解码可沿规范序列化提升为显式环境项解码。 -/
theorem fs_named_term_tokens_decode_with_env_of_tree
    (freeBase : Nat) (boundNames : List Nat)
    {tree : RawTermTokenTree}
    {term : SetTerm}
    (hDecode :
      fs_named_term_token_tree_decode
          freeBase boundNames tree =
        some term) :
    fs_named_term_tokens_decode_with_env
        freeBase boundNames tree.tokens =
      some term := by
  have hSeparated :
      tree.HeadsOdd :=
    fs_named_term_token_tree_decode_heads_odd
      freeBase boundNames hDecode
  unfold fs_named_term_tokens_decode_with_env
  rw [RawTermTokenTree.parse?_tokens tree hSeparated]
  exact hDecode

/-- 规范变量 token 在任意显式环境下都能恢复为对应具名变量。 -/
theorem fs_named_term_tokens_decode_with_env_variable
    (freeBase : Nat) (boundNames : List Nat)
    (name : Nat) :
    fs_named_term_tokens_decode_with_env
        freeBase boundNames
        [Numbered.variable_token name] =
      some (.var
        (fs_named_variable_of_name
          freeBase boundNames name)) := by
  let tree : RawTermTokenTree :=
    .atom (Numbered.variable_token name)
  have hTreeDecode :
      fs_named_term_token_tree_decode
          freeBase boundNames tree =
        some (.var
          (fs_named_variable_of_name
            freeBase boundNames name)) := by
    simp [tree, fs_named_term_token_tree_decode,
      fs_named_variable_decode,
      fs_variable_name_decode_encode]
  simpa [tree, RawTermTokenTree.tokens] using
    fs_named_term_tokens_decode_with_env_of_tree
      freeBase boundNames hTreeDecode

/-- 常元 token 在其对应函数符号为零元时可被具名项 decoder 接受。 -/
theorem fs_named_term_tokens_decode_with_env_constant
    (freeBase : Nat) (boundNames : List Nat)
    (symbol : FunctionSymbol)
    (hNullary : signature.funcDomain symbol = []) :
    fs_named_term_tokens_decode_with_env
        freeBase boundNames
        [Numbered.constant_token symbol.ctorIdx] =
      some (.app symbol []) := by
  have hVariableName :
      fs_variable_name_decode
          (Numbered.constant_token symbol.ctorIdx) =
        none := by
    unfold fs_variable_name_decode
    apply fs_find_encoded_eq_none
    intro name hName
    exact
      (token_reflection_constant_token_ne_variable_token
        symbol.ctorIdx name).symm
  let tree : RawTermTokenTree :=
    .atom (Numbered.constant_token symbol.ctorIdx)
  have hTreeDecode :
      fs_named_term_token_tree_decode
          freeBase boundNames tree =
        some (.app symbol []) := by
    simp [tree, fs_named_term_token_tree_decode,
      fs_named_variable_decode, hVariableName,
      fs_constant_symbol_lookup, hNullary]
  simpa [tree, RawTermTokenTree.tokens] using
    fs_named_term_tokens_decode_with_env_of_tree
      freeBase boundNames hTreeDecode

/--
一列完整 token 串逐项解码成功时，可恢复同序 parser 树列及其树级解码轨迹。
-/
theorem fs_named_term_token_lists_decode_with_env_trees
    (freeBase : Nat) (boundNames : List Nat) :
    ∀ {tokenLists : List (List Nat)}
        {terms : List SetTerm},
      tokenLists.mapM
          (fs_named_term_tokens_decode_with_env
            freeBase boundNames) =
        some terms →
      ∃ trees : List RawTermTokenTree,
        trees.map RawTermTokenTree.tokens =
            tokenLists ∧
          trees.mapM
              (fs_named_term_token_tree_decode
                freeBase boundNames) =
            some terms
  | .nil, terms, hDecode => by
      have hTerms : terms = [] := by
        simpa using Option.some.inj hDecode.symm
      subst terms
      exact
        ⟨([] : List RawTermTokenTree), rfl, rfl⟩
  | .cons tokens tokenLists, terms, hDecode => by
      cases hHead :
          fs_named_term_tokens_decode_with_env
            freeBase boundNames tokens with
      | none =>
          simp [List.mapM_cons, hHead] at hDecode
      | some head =>
          cases hTail :
              tokenLists.mapM
                (fs_named_term_tokens_decode_with_env
                  freeBase boundNames) with
          | none =>
              simp [List.mapM_cons,
                hHead, hTail] at hDecode
          | some tail =>
              simp [List.mapM_cons,
                hHead, hTail] at hDecode
              subst terms
              rcases
                  (fs_named_term_tokens_decode_with_env_iff
                    freeBase boundNames tokens head).mp
                    hHead with
                ⟨tree, hParse, hTreeDecode⟩
              rcases
                  fs_named_term_token_lists_decode_with_env_trees
                    freeBase boundNames hTail with
                ⟨trees, hTreeTokens, hTreeDecodes⟩
              have hTokens :
                  tree.tokens = tokens :=
                RawTermTokenTree.parse?_sound hParse
              refine ⟨tree :: trees, ?_, ?_⟩
              · simp [hTokens, hTreeTokens]
              · simp [List.mapM_cons,
                  hTreeDecode, hTreeDecodes]
  termination_by tokenLists => sizeOf tokenLists

/--
树列逐项解码成功时，单排序集合论语言自动给出与结果长度同长的参数
良排序证书。
-/
theorem fs_named_term_token_trees_decode_wellSorted
    (freeBase : Nat) (boundNames : List Nat) :
    ∀ {trees : List RawTermTokenTree}
        {terms : List SetTerm},
      trees.mapM
          (fs_named_term_token_tree_decode
            freeBase boundNames) =
        some terms →
      ArgsWellSorted terms
        (List.replicate terms.length SetSort.set)
  | .nil, terms, hDecode => by
      have hTerms : terms = [] := by
        simpa using Option.some.inj hDecode.symm
      subst terms
      exact .nil
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
              simpa using ArgsWellSorted.cons
                (fs_named_term_token_tree_decode_admissible
                  freeBase boundNames hHead).1
                (fs_named_term_token_trees_decode_wellSorted
                  freeBase boundNames hTail)
  termination_by trees => sizeOf trees

/--
在单排序集合论签名中，成功解码的树列只要长度匹配符号元数，就必然
通过参数 sort 检查。
-/
theorem fs_named_term_token_trees_decode_check
    (freeBase : Nat) (boundNames : List Nat)
    (symbol : FunctionSymbol)
    {trees : List RawTermTokenTree}
    {arguments : List SetTerm}
    (hArguments :
      trees.mapM
          (fs_named_term_token_tree_decode
            freeBase boundNames) =
        some arguments)
    (hArity :
      arguments.length =
        (signature.funcDomain symbol).length) :
    Term.check_args_wellSorted
        arguments (signature.funcDomain symbol) =
      true := by
  apply Term.check_args_wellSorted_complete
  rw [set_function_domain_replicate, ← hArity]
  exact fs_named_term_token_trees_decode_wellSorted
    freeBase boundNames hArguments

/-- 正元函数 token 与已解码参数树列可组合为成功项解码。 -/
theorem fs_named_term_tokens_decode_with_env_application
    (freeBase : Nat) (boundNames : List Nat)
    (symbol : FunctionSymbol)
    {trees : List RawTermTokenTree}
    {arguments : List SetTerm}
    (hArguments :
      trees.mapM
          (fs_named_term_token_tree_decode
            freeBase boundNames) =
        some arguments)
    (hArity :
      arguments.length =
        (signature.funcDomain symbol).length)
    (hPositive : arguments ≠ []) :
    fs_named_term_tokens_decode_with_env
        freeBase boundNames
        (Numbered.function_application_tokens
          (arguments.length - 1)
          symbol.ctorIdx
          (trees.map RawTermTokenTree.tokens)) =
      some (.app symbol arguments) := by
  let tree : RawTermTokenTree :=
    .application
      (Numbered.function_token
        (arguments.length - 1) symbol.ctorIdx)
      trees
  have hLength :
      arguments.length = trees.length :=
    fs_option_mapM_length hArguments
  have hWellSorted :
      Term.check_args_wellSorted
          arguments (signature.funcDomain symbol) =
        true :=
    fs_named_term_token_trees_decode_check
      freeBase boundNames symbol hArguments hArity
  have hTreesPositive : trees ≠ [] := by
    intro hTrees
    apply hPositive
    apply List.eq_nil_of_length_eq_zero
    simpa [hTrees] using hLength
  have hTreeDecode :
      fs_named_term_token_tree_decode
          freeBase boundNames tree =
        some (.app symbol arguments) := by
    simp [tree, fs_named_term_token_tree_decode,
      hTreesPositive, hLength,
      fs_function_symbol_lookup, hArguments, hWellSorted]
  have hWhole :=
    fs_named_term_tokens_decode_with_env_of_tree
      freeBase boundNames hTreeDecode
  simpa [tree, RawTermTokenTree.tokens,
    RawTermTokenTree.list_tokens,
    RawTermTokenTree.map_tokens_flatten_eq_list_tokens,
    Numbered.function_application_tokens,
    List.append_assoc] using hWhole

/--
一列参数 token 串逐项完整解码成功且数量匹配函数元数时，可直接组合为完整应用
解码；parser 树列由本接口内部恢复。
-/
theorem fs_named_term_token_lists_decode_with_env_application
    (freeBase : Nat) (boundNames : List Nat)
    (symbol : FunctionSymbol)
    {tokenLists : List (List Nat)}
    {arguments : List SetTerm}
    (hArguments :
      tokenLists.mapM
          (fs_named_term_tokens_decode_with_env
            freeBase boundNames) =
        some arguments)
    (hArity :
      arguments.length =
        (signature.funcDomain symbol).length)
    (hPositive : arguments ≠ []) :
    fs_named_term_tokens_decode_with_env
        freeBase boundNames
        (Numbered.function_application_tokens
          (arguments.length - 1)
          symbol.ctorIdx tokenLists) =
      some (.app symbol arguments) := by
  rcases
      fs_named_term_token_lists_decode_with_env_trees
        freeBase boundNames hArguments with
    ⟨trees, hTreeTokens, hTreeDecodes⟩
  simpa [hTreeTokens] using
    fs_named_term_tokens_decode_with_env_application
      freeBase boundNames symbol
      hTreeDecodes hArity hPositive

/-! ## 成功解码的对象项码闭包 -/

/-- 已知项码与标准 token 序列相等时，把项码谓词运输到该标准序列。 -/
private theorem gq_term_code_of_eq_standard
    (code : SetTerm) (tokens : List Nat)
    (hCode : Term.Admissible code SetSort.set)
    (hTermCode :
      ⊢ₘ[godel_quotation_theory] term_codeₘ(code))
    (hEquality :
      ⊢ₘ[godel_quotation_theory]
        code ≐ₘ standard_token_sequence tokens) :
    ⊢ₘ[godel_quotation_theory]
      term_codeₘ(standard_token_sequence tokens) := by
  have hMember :
      ⊢ₘ[godel_quotation_theory]
        code ∈ₘ TermCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (gq_term_code_definition_instance code hCode)
      hTermCode
  have hStandardMember :
      ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ∈ₘ TermCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (membership_left_iff_of_equality
        code (standard_token_sequence tokens) TermCodeₘ
        hCode
        (standard_token_sequence_admissible tokens)
        term_code_set_term_admissible
        hEquality)
      hMember
  exact FirstOrder.Derives.iffElimLeft
    (gq_term_code_definition_instance
      (standard_token_sequence tokens)
      (standard_token_sequence_admissible tokens))
    hStandardMember

mutual
  /--
  成功具名解码的项树，其原始标准 token 序列满足对象谓词 `term_codeₘ`。
  -/
  theorem fs_named_term_token_tree_decode_standard_term_code
      (freeBase : Nat) (boundNames : List Nat) :
      ∀ {tree : RawTermTokenTree} {term : SetTerm},
        fs_named_term_token_tree_decode
            freeBase boundNames tree =
          some term →
        ⊢ₘ[godel_quotation_theory]
          term_codeₘ(standard_token_sequence tree.tokens)
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
                    Numbered.variable_token name = token :=
                  fs_variable_name_decode_value_of_some hName
                have hCode :
                    Term.Admissible
                      (Numbered.named_variable_code name)
                      SetSort.set :=
                  variable_code_term_admissible
                    (numₘ(name))
                    (finite_numeral_term_admissible name)
                simpa [RawTermTokenTree.tokens, ← hToken] using
                  gq_term_code_of_eq_standard
                    (Numbered.named_variable_code name)
                    [Numbered.variable_token name]
                    hCode
                    (named_variable_code_is_term_code name)
                    (named_variable_code_eq_standard_token_sequence
                      name)
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
                · have hToken :
                    Numbered.constant_token symbol.ctorIdx =
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
                  have hCode :
                      Term.Admissible
                        (const_codeₘ(numₘ(symbol.ctorIdx)))
                        SetSort.set :=
                    constant_code_term_admissible
                      (numₘ(symbol.ctorIdx))
                      (finite_numeral_term_admissible
                        symbol.ctorIdx)
                  simpa [RawTermTokenTree.tokens, ← hToken] using
                    gq_term_code_of_eq_standard
                      (const_codeₘ(numₘ(symbol.ctorIdx)))
                      [Numbered.constant_token symbol.ctorIdx]
                      hCode
                      (constant_code_is_term_code symbol.ctorIdx)
                      (constant_code_eq_standard_token_sequence
                        symbol.ctorIdx)
                · simp [fs_named_term_token_tree_decode,
                    hVariable, hSymbol, hDomain] at hDecode
    | .application head arguments, term, hDecode => by
        by_cases hNonempty : arguments = []
        · subst arguments
          simp [fs_named_term_token_tree_decode] at hDecode
        · cases hSymbol :
              fs_find_encoded
                (fun candidate : FunctionSymbol =>
                  Numbered.function_token
                    (arguments.length - 1)
                    candidate.ctorIdx)
                head fs_function_symbols with
          | none =>
              simp [fs_named_term_token_tree_decode,
                hNonempty, hSymbol] at hDecode
          | some symbol =>
              cases hArguments :
                  arguments.mapM
                    (fs_named_term_token_tree_decode
                      freeBase boundNames) with
              | none =>
                  simp [fs_named_term_token_tree_decode,
                    hNonempty, hSymbol, hArguments] at hDecode
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
                    rcases
                        fs_named_term_token_trees_decode_standard_term_codes
                          freeBase boundNames hArguments with
                      ⟨hAligned, hTermCodes⟩
                    cases arguments with
                    | nil =>
                        exact (hNonempty rfl).elim
                    | cons first rest =>
                        have hApplicationCode :=
                          gq_term_application_code_is_term_code_of_aligned
                            symbol.ctorIdx hAligned hTermCodes
                        have hEqualityRaw :=
                          gq_term_application_code_eq_standard_token_sequence
                            rest.length symbol.ctorIdx hAligned
                        have hEquality :
                            ⊢ₘ[godel_quotation_theory]
                              term_application_code_term
                                  (numₘ(rest.length))
                                  (numₘ(symbol.ctorIdx))
                                  (standard_sequence
                                    ((first :: rest).map
                                      (fun tree =>
                                        standard_token_sequence
                                          tree.tokens))) ≐ₘ
                                standard_token_sequence
                                  (RawTermTokenTree.application
                                    head (first :: rest)).tokens := by
                          simpa [RawTermTokenTree.tokens,
                            RawTermTokenTree.list_tokens,
                            RawTermTokenTree.map_tokens_flatten_eq_list_tokens,
                            Numbered.function_application_tokens,
                            ← hToken, List.append_assoc] using
                              hEqualityRaw
                        have hApplicationCode' :
                            ⊢ₘ[godel_quotation_theory]
                              term_codeₘ(
                                term_application_code_term
                                  (numₘ(rest.length))
                                  (numₘ(symbol.ctorIdx))
                                  (standard_sequence
                                    ((first :: rest).map
                                      (fun tree =>
                                        standard_token_sequence
                                          tree.tokens)))) := by
                          simpa using hApplicationCode
                        have hElements :
                            ∀ element,
                              element ∈
                                (first :: rest).map
                                  (fun tree =>
                                    standard_token_sequence
                                      tree.tokens) →
                              Term.CheckCertificate
                                element SetSort.set := by
                          intro element hElement
                          exact
                            (gq_aligned_codes_boundary
                              hAligned element hElement).check_certificate
                        have hFamilyCheck :
                            Term.CheckCertificate
                              (standard_sequence
                                ((first :: rest).map
                                  (fun tree =>
                                    standard_token_sequence
                                      tree.tokens)))
                              SetSort.set := by
                          apply standard_sequence_from_check
                          exact hElements
                        have hFamily :
                            Term.Admissible
                              (standard_sequence
                                ((first :: rest).map
                                  (fun tree =>
                                    standard_token_sequence
                                      tree.tokens)))
                              SetSort.set :=
                          hFamilyCheck.admissible
                        exact
                          gq_term_code_of_eq_standard
                            (term_application_code_term
                              (numₘ(rest.length))
                              (numₘ(symbol.ctorIdx))
                              (standard_sequence
                                ((first :: rest).map
                                  (fun tree =>
                                    standard_token_sequence
                                      tree.tokens))))
                            (RawTermTokenTree.application
                              head (first :: rest)).tokens
                            (term_application_code_term_admissible
                              (numₘ(rest.length))
                              (numₘ(symbol.ctorIdx))
                              (standard_sequence
                                ((first :: rest).map
                                  (fun tree =>
                                    standard_token_sequence
                                      tree.tokens)))
                              (finite_numeral_term_admissible
                                rest.length)
                              (finite_numeral_term_admissible
                                symbol.ctorIdx)
                              hFamily)
                            hApplicationCode' hEquality
                  · simp [fs_named_term_token_tree_decode,
                      hNonempty, hSymbol,
                      hArguments, hCheck] at hDecode
  termination_by tree => sizeOf tree

  /--
  成功解码的项树列同时给出标准代码列与原始 token 分片的逐项对齐，
  以及每个标准代码的 `term_codeₘ` 证书。
  -/
  theorem fs_named_term_token_trees_decode_standard_term_codes
      (freeBase : Nat) (boundNames : List Nat) :
      ∀ {trees : List RawTermTokenTree}
          {terms : List SetTerm},
        trees.mapM
            (fs_named_term_token_tree_decode
              freeBase boundNames) =
          some terms →
        gq_term_code_token_aligned_list
          (trees.map
            (fun tree =>
              standard_token_sequence tree.tokens))
          (trees.map RawTermTokenTree.tokens)
    | .nil, terms, hDecode => by
        have hTerms : terms = [] := by
          simpa using Option.some.inj hDecode.symm
        subst terms
        exact ⟨.nil, by simp⟩
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
                rcases
                    fs_named_term_token_trees_decode_standard_term_codes
                      freeBase boundNames hTail with
                  ⟨hTailAligned, hTailCodes⟩
                refine ⟨.cons ?_ hTailAligned, ?_⟩
                · exact
                    ⟨⟨standard_token_sequence_admissible tree.tokens,
                        standard_token_sequence_freeSupport_nil
                          tree.tokens⟩,
                      FirstOrder.Derives.eq_refl_m
                        (standard_token_sequence tree.tokens)⟩
                · intro code hCode
                  simp only [List.map_cons,
                    List.mem_cons] at hCode
                  rcases hCode with rfl | hCode
                  · exact
                      fs_named_term_token_tree_decode_standard_term_code
                        freeBase boundNames hHead
                  · exact hTailCodes code hCode
  termination_by trees => sizeOf trees
end

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
