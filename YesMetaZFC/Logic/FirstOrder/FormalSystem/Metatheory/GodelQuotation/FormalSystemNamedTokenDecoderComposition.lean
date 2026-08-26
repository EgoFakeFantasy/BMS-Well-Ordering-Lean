import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTermDecoderComposition

/-!
# FormalSystem 具名 token 解码的构造闭包

本模块把具名 decoder 的自由变量基数与 binder 名环境显式提升到整串 token
接口。递归反演因此可以让父式与全部子式共享同一个 `freeBase`，而不必在每个
子式之间运输非规范自由变量编号。
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

/--
在显式自由变量基数与 binder 名环境下解码完整 Hilbert token 串。

公开 decoder 是该接口在 parser 返回树自身的自由变量基数及空 binder 环境下的
特例。
-/
def fs_named_hilbert_tokens_decode_with_env
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat) : Option SetFormula := do
  let tree ← RawHilbertTokenTree.parse? tokens
  fs_named_hilbert_token_tree_decode
    freeBase boundNames tree

/-- 显式环境整串解码成功等价于存在同一 parser 树及其树级解码轨迹。 -/
theorem fs_named_hilbert_tokens_decode_with_env_iff
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat) (formula : SetFormula) :
    fs_named_hilbert_tokens_decode_with_env
        freeBase boundNames tokens =
      some formula ↔
    ∃ tree,
      RawHilbertTokenTree.parse? tokens = some tree ∧
        fs_named_hilbert_token_tree_decode
            freeBase boundNames tree =
          some formula := by
  unfold fs_named_hilbert_tokens_decode_with_env
  cases hParse : RawHilbertTokenTree.parse? tokens with
  | none =>
      simp
  | some tree =>
      simp

/-- 合法具名公式 token 串不能以裸否定 token 起首。 -/
theorem fs_named_hilbert_tokens_decode_with_env_negation_head_none
    (freeBase : Nat) (boundNames : List Nat)
    (tail : List Nat) :
    fs_named_hilbert_tokens_decode_with_env
        freeBase boundNames
        (Numbered.logical_token .negation :: tail) =
      none := by
  cases hDecode :
      fs_named_hilbert_tokens_decode_with_env
        freeBase boundNames
        (Numbered.logical_token .negation :: tail) with
  | none =>
      rfl
  | some formula =>
      rcases
          (fs_named_hilbert_tokens_decode_with_env_iff
            freeBase boundNames
            (Numbered.logical_token .negation :: tail)
            formula).mp hDecode with
        ⟨tree, hParse, hTree⟩
      have hTokens :=
        RawHilbertTokenTree.parse?_sound hParse
      have hSeparated :=
        fs_named_hilbert_token_tree_decode_lexically_separated
          freeBase hTree
      cases tree with
      | equality left right =>
          have hHead :
              Numbered.logical_token .leftParenthesis =
                Numbered.logical_token .negation := by
            have hHead' := congrArg List.head? hTokens
            simpa [RawHilbertTokenTree.tokens] using hHead'
          have hNe :
              Numbered.logical_token .leftParenthesis ≠
                Numbered.logical_token .negation := by
            native_decide
          exact False.elim (hNe hHead)
      | membership left right =>
          have hHead :
              Numbered.logical_token .leftParenthesis =
                Numbered.logical_token .negation := by
            have hHead' := congrArg List.head? hTokens
            simpa [RawHilbertTokenTree.tokens] using hHead'
          have hNe :
              Numbered.logical_token .leftParenthesis ≠
                Numbered.logical_token .negation := by
            native_decide
          exact False.elim (hNe hHead)
      | negation body =>
          have hHead :
              Numbered.logical_token .leftParenthesis =
                Numbered.logical_token .negation := by
            have hHead' := congrArg List.head? hTokens
            simpa [RawHilbertTokenTree.tokens] using hHead'
          have hNe :
              Numbered.logical_token .leftParenthesis ≠
                Numbered.logical_token .negation := by
            native_decide
          exact False.elim (hNe hHead)
      | implication left right =>
          have hHead :
              Numbered.logical_token .leftParenthesis =
                Numbered.logical_token .negation := by
            have hHead' := congrArg List.head? hTokens
            simpa [RawHilbertTokenTree.tokens] using hHead'
          have hNe :
              Numbered.logical_token .leftParenthesis ≠
                Numbered.logical_token .negation := by
            native_decide
          exact False.elim (hNe hHead)
      | universal variableToken body =>
          have hHead :
              Numbered.logical_token .leftParenthesis =
                Numbered.logical_token .negation := by
            have hHead' := congrArg List.head? hTokens
            simpa [RawHilbertTokenTree.tokens] using hHead'
          have hNe :
              Numbered.logical_token .leftParenthesis ≠
                Numbered.logical_token .negation := by
            native_decide
          exact False.elim (hNe hHead)
      | predicate head arguments =>
          have hHead :
              head = Numbered.logical_token .negation := by
            have hHead' := congrArg List.head? hTokens
            simpa [RawHilbertTokenTree.tokens] using hHead'
          exact False.elim <|
            (odd_token_ne_logical
              hSeparated.1 .negation) hHead

/-- 成功的树级解码可沿规范序列化提升为显式环境整串解码。 -/
theorem fs_named_hilbert_tokens_decode_with_env_of_tree
    (freeBase : Nat) (boundNames : List Nat)
    {tree : RawHilbertTokenTree}
    {formula : SetFormula}
    (hDecode :
      fs_named_hilbert_token_tree_decode
          freeBase boundNames tree =
        some formula) :
    fs_named_hilbert_tokens_decode_with_env
        freeBase boundNames tree.tokens =
      some formula := by
  have hSeparated :
      tree.LexicallySeparated :=
    fs_named_hilbert_token_tree_decode_lexically_separated
      freeBase hDecode
  unfold fs_named_hilbert_tokens_decode_with_env
  rw [RawHilbertTokenTree.parse?_tokens
    tree hSeparated]
  exact hDecode

/-- 显式环境下，否定外壳保持 checked 解码成功。 -/
theorem fs_named_hilbert_tokens_decode_with_env_negation
    (freeBase : Nat) (boundNames : List Nat)
    {bodyTokens : List Nat}
    {bodyFormula : SetFormula}
    (hBody :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames bodyTokens =
        some bodyFormula) :
    fs_named_hilbert_tokens_decode_with_env
        freeBase boundNames
        (Numbered.negation_tokens bodyTokens) =
      some (.neg bodyFormula) := by
  rcases
      (fs_named_hilbert_tokens_decode_with_env_iff
        freeBase boundNames bodyTokens bodyFormula).mp
        hBody with
    ⟨bodyTree, hParse, hTree⟩
  let tree : RawHilbertTokenTree :=
    .negation bodyTree
  have hTreeDecode :
      fs_named_hilbert_token_tree_decode
          freeBase boundNames tree =
        some (.neg bodyFormula) := by
    simp [tree, fs_named_hilbert_token_tree_decode,
      hTree]
  have hWhole :=
    fs_named_hilbert_tokens_decode_with_env_of_tree
      freeBase boundNames hTreeDecode
  have hBodyTokens :
      bodyTree.tokens = bodyTokens :=
    RawHilbertTokenTree.parse?_sound hParse
  simpa [tree, RawHilbertTokenTree.tokens,
    Numbered.negation_tokens, hBodyTokens,
    List.append_assoc] using hWhole

/-- 显式环境下，否定整串解码失败必然来自正文解码失败。 -/
theorem fs_named_hilbert_tokens_decode_with_env_negation_none
    (freeBase : Nat) (boundNames : List Nat)
    (bodyTokens : List Nat)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames
          (Numbered.negation_tokens bodyTokens) =
        none) :
    fs_named_hilbert_tokens_decode_with_env
        freeBase boundNames bodyTokens =
      none := by
  cases hBody :
      fs_named_hilbert_tokens_decode_with_env
        freeBase boundNames bodyTokens with
  | none =>
      rfl
  | some bodyFormula =>
      have hWhole :=
        fs_named_hilbert_tokens_decode_with_env_negation
          freeBase boundNames hBody
      simp [hDecode] at hWhole

/-- 显式环境下，蕴含外壳保持左右两棵子树的 checked 解码成功。 -/
theorem fs_named_hilbert_tokens_decode_with_env_implication
    (freeBase : Nat) (boundNames : List Nat)
    {leftTokens rightTokens : List Nat}
    {leftFormula rightFormula : SetFormula}
    (hLeft :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames leftTokens =
        some leftFormula)
    (hRight :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames rightTokens =
        some rightFormula) :
    fs_named_hilbert_tokens_decode_with_env
        freeBase boundNames
        (Numbered.implication_tokens
          leftTokens rightTokens) =
      some (.imp leftFormula rightFormula) := by
  rcases
      (fs_named_hilbert_tokens_decode_with_env_iff
        freeBase boundNames leftTokens leftFormula).mp
        hLeft with
    ⟨leftTree, hLeftParse, hLeftTree⟩
  rcases
      (fs_named_hilbert_tokens_decode_with_env_iff
        freeBase boundNames rightTokens rightFormula).mp
        hRight with
    ⟨rightTree, hRightParse, hRightTree⟩
  let tree : RawHilbertTokenTree :=
    .implication leftTree rightTree
  have hTreeDecode :
      fs_named_hilbert_token_tree_decode
          freeBase boundNames tree =
        some (.imp leftFormula rightFormula) := by
    simp [tree, fs_named_hilbert_token_tree_decode,
      hLeftTree, hRightTree]
  have hWhole :=
    fs_named_hilbert_tokens_decode_with_env_of_tree
      freeBase boundNames hTreeDecode
  have hLeftTokens :
      leftTree.tokens = leftTokens :=
    RawHilbertTokenTree.parse?_sound hLeftParse
  have hRightTokens :
      rightTree.tokens = rightTokens :=
    RawHilbertTokenTree.parse?_sound hRightParse
  simpa [tree, RawHilbertTokenTree.tokens,
    Numbered.implication_tokens,
    hLeftTokens, hRightTokens,
    List.append_assoc] using hWhole

/-- 显式环境下，蕴含整串解码失败必然来自左式或右式解码失败。 -/
theorem fs_named_hilbert_tokens_decode_with_env_implication_none
    (freeBase : Nat) (boundNames : List Nat)
    (leftTokens rightTokens : List Nat)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames
          (Numbered.implication_tokens
            leftTokens rightTokens) =
        none) :
    fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames leftTokens =
        none ∨
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames rightTokens =
        none := by
  cases hLeft :
      fs_named_hilbert_tokens_decode_with_env
        freeBase boundNames leftTokens with
  | none =>
      exact Or.inl rfl
  | some leftFormula =>
      cases hRight :
          fs_named_hilbert_tokens_decode_with_env
            freeBase boundNames rightTokens with
      | none =>
          exact Or.inr rfl
      | some rightFormula =>
          have hWhole :=
            fs_named_hilbert_tokens_decode_with_env_implication
              freeBase boundNames hLeft hRight
          simp [hDecode] at hWhole

/--
显式环境下，全称外壳把新 binder 名压入正文环境，并保持 checked 解码成功。
-/
theorem fs_named_hilbert_tokens_decode_with_env_universal
    (freeBase : Nat) (boundNames : List Nat)
    (name : Nat)
    {bodyTokens : List Nat}
    {bodyFormula : SetFormula}
    (hBody :
      fs_named_hilbert_tokens_decode_with_env
          freeBase (name :: boundNames) bodyTokens =
        some bodyFormula) :
    fs_named_hilbert_tokens_decode_with_env
        freeBase boundNames
        (Numbered.universal_tokens name bodyTokens) =
      some (.forallE SetSort.set bodyFormula) := by
  rcases
      (fs_named_hilbert_tokens_decode_with_env_iff
        freeBase (name :: boundNames)
        bodyTokens bodyFormula).mp hBody with
    ⟨bodyTree, hParse, hTree⟩
  let tree : RawHilbertTokenTree :=
    .universal
      (Numbered.variable_token name) bodyTree
  have hTreeDecode :
      fs_named_hilbert_token_tree_decode
          freeBase boundNames tree =
        some (.forallE SetSort.set bodyFormula) := by
    simp [tree, fs_named_hilbert_token_tree_decode,
      fs_variable_name_decode_encode, hTree]
  have hWhole :=
    fs_named_hilbert_tokens_decode_with_env_of_tree
      freeBase boundNames hTreeDecode
  have hBodyTokens :
      bodyTree.tokens = bodyTokens :=
    RawHilbertTokenTree.parse?_sound hParse
  simpa [tree, RawHilbertTokenTree.tokens,
    Numbered.universal_tokens, hBodyTokens,
    List.append_assoc] using hWhole

/--
显式环境下，全称公式解码成功可反向恢复原始 binder 名与正文 token 串。

该接口只反演 parser 与树级 decoder，不施加规范命名条件；因此可直接供任意
全局 `freeBase` 的 checked replay 使用。
-/
theorem fs_named_hilbert_tokens_decode_with_env_forall_elim
    (freeBase : Nat) (boundNames : List Nat)
    {tokens : List Nat} {bodyFormula : SetFormula}
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        some (.forallE SetSort.set bodyFormula)) :
    ∃ name bodyTokens,
      tokens =
          Numbered.universal_tokens name bodyTokens ∧
        fs_named_hilbert_tokens_decode_with_env
            freeBase (name :: boundNames) bodyTokens =
          some bodyFormula := by
  rcases
      (fs_named_hilbert_tokens_decode_with_env_iff
        freeBase boundNames tokens
        (.forallE SetSort.set bodyFormula)).mp hDecode with
    ⟨tree, hParse, hTree⟩
  cases tree with
  | equality left right =>
      cases hLeft :
          fs_named_term_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hLeft] at hTree
      | some leftTerm =>
          cases hRight :
              fs_named_term_token_tree_decode
                freeBase boundNames right with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hTree
          | some rightTerm =>
              by_cases hCheck :
                  Term.check_wellSorted SetSort.set leftTerm &&
                      Term.check_wellSorted SetSort.set rightTerm =
                    true
              · simp [fs_named_hilbert_token_tree_decode,
                  hLeft, hRight] at hTree
              · simp [fs_named_hilbert_token_tree_decode,
                  hLeft, hRight] at hTree
  | membership left right =>
      cases hLeft :
          fs_named_term_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hLeft] at hTree
      | some leftTerm =>
          cases hRight :
              fs_named_term_token_tree_decode
                freeBase boundNames right with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hTree
          | some rightTerm =>
              by_cases hCheck :
                  Term.check_args_wellSorted
                      [leftTerm, rightTerm]
                      (signature.relDomain
                        RelationSymbol.membership) =
                    true
              · simp [fs_named_hilbert_token_tree_decode,
                  hLeft, hRight, hCheck] at hTree
              · simp [fs_named_hilbert_token_tree_decode,
                  hLeft, hRight, hCheck] at hTree
  | predicate head arguments =>
      cases hRelation :
          fs_find_encoded
            (fun candidate : RelationSymbol =>
              Numbered.predicate_token
                (arguments.length - 1)
                candidate.ctorIdx)
            head fs_relation_symbols with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hRelation] at hTree
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
                  hRelation, hArguments] at hTree
            | some decoded =>
                by_cases hCheck :
                    Term.check_args_wellSorted decoded
                        (signature.relDomain relation) =
                      true
                · simp [fs_named_hilbert_token_tree_decode,
                    hRelation, hKind, hArguments,
                    hCheck] at hTree
                · simp [fs_named_hilbert_token_tree_decode,
                    hRelation, hKind, hArguments,
                    hCheck] at hTree
          · simp [fs_named_hilbert_token_tree_decode,
              hRelation, hKind] at hTree
  | negation body =>
      cases hBody :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames body with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hBody] at hTree
      | some decodedBody =>
          simp [fs_named_hilbert_token_tree_decode,
            hBody] at hTree
  | implication left right =>
      cases hLeft :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hLeft] at hTree
      | some leftFormula =>
          cases hRight :
              fs_named_hilbert_token_tree_decode
                freeBase boundNames right with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hTree
          | some rightFormula =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hTree
  | universal variableToken body =>
      cases hName :
          fs_variable_name_decode variableToken with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hName] at hTree
      | some name =>
          cases hBody :
              fs_named_hilbert_token_tree_decode
                freeBase (name :: boundNames) body with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hName, hBody] at hTree
          | some decodedBody =>
              simp [fs_named_hilbert_token_tree_decode,
                hName, hBody] at hTree
              subst decodedBody
              refine ⟨name, body.tokens, ?_, ?_⟩
              · rw [← RawHilbertTokenTree.parse?_sound hParse]
                have hVariableToken :
                    Numbered.variable_token name =
                      variableToken :=
                  fs_variable_name_decode_value_of_some
                    hName
                simp [RawHilbertTokenTree.tokens,
                  Numbered.universal_tokens,
                  hVariableToken]
              · exact
                  fs_named_hilbert_tokens_decode_with_env_of_tree
                    freeBase (name :: boundNames) hBody

/-- 显式环境下，全称整串解码失败必然来自扩展 binder 环境后的正文失败。 -/
theorem fs_named_hilbert_tokens_decode_with_env_universal_none
    (freeBase : Nat) (boundNames : List Nat)
    (name : Nat) (bodyTokens : List Nat)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames
          (Numbered.universal_tokens
            name bodyTokens) =
        none) :
    fs_named_hilbert_tokens_decode_with_env
        freeBase (name :: boundNames) bodyTokens =
      none := by
  cases hBody :
      fs_named_hilbert_tokens_decode_with_env
        freeBase (name :: boundNames) bodyTokens with
  | none =>
      rfl
  | some bodyFormula =>
      have hWhole :=
        fs_named_hilbert_tokens_decode_with_env_universal
          freeBase boundNames name hBody
      simp [hDecode] at hWhole

/-- 等式原子由两棵成功项树组合得到成功公式解码。 -/
theorem fs_named_hilbert_tokens_decode_with_env_equality
    (freeBase : Nat) (boundNames : List Nat)
    {leftTree rightTree : RawTermTokenTree}
    {leftTerm rightTerm : SetTerm}
    (hLeft :
      fs_named_term_token_tree_decode
          freeBase boundNames leftTree =
        some leftTerm)
    (hRight :
      fs_named_term_token_tree_decode
          freeBase boundNames rightTree =
        some rightTerm)
    (hLeftCheck :
      Term.check_wellSorted
          SetSort.set leftTerm = true)
    (hRightCheck :
      Term.check_wellSorted
          SetSort.set rightTerm = true) :
    fs_named_hilbert_tokens_decode_with_env
        freeBase boundNames
        (Numbered.equality_tokens
          leftTree.tokens rightTree.tokens) =
      some (.equal leftTerm rightTerm) := by
  let tree : RawHilbertTokenTree :=
    .equality leftTree rightTree
  have hTreeDecode :
      fs_named_hilbert_token_tree_decode
          freeBase boundNames tree =
        some (.equal leftTerm rightTerm) := by
    simp [tree, fs_named_hilbert_token_tree_decode,
      hLeft, hRight, hLeftCheck, hRightCheck]
  have hWhole :=
    fs_named_hilbert_tokens_decode_with_env_of_tree
      freeBase boundNames hTreeDecode
  simpa [tree, RawHilbertTokenTree.tokens,
    Numbered.equality_tokens, List.append_assoc] using hWhole

/--
显式环境下，等式公式解码成功可反向恢复左右项 token 串及其项解码。

该接口只消费 parser 与树级 decoder 的确定性，不要求输入使用规范变量命名。
-/
theorem fs_named_hilbert_tokens_decode_with_env_equality_elim
    (freeBase : Nat) (boundNames : List Nat)
    {tokens : List Nat} {leftTerm rightTerm : SetTerm}
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        some (.equal leftTerm rightTerm)) :
    ∃ leftTokens rightTokens,
      tokens =
          Numbered.equality_tokens leftTokens rightTokens ∧
        fs_named_term_tokens_decode_with_env
            freeBase boundNames leftTokens =
          some leftTerm ∧
        fs_named_term_tokens_decode_with_env
            freeBase boundNames rightTokens =
          some rightTerm := by
  rcases
      (fs_named_hilbert_tokens_decode_with_env_iff
        freeBase boundNames tokens
        (.equal leftTerm rightTerm)).mp hDecode with
    ⟨tree, hParse, hTree⟩
  cases tree with
  | equality left right =>
      cases hLeft :
          fs_named_term_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hLeft] at hTree
      | some decodedLeft =>
          cases hRight :
              fs_named_term_token_tree_decode
                freeBase boundNames right with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hTree
          | some decodedRight =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hTree
              rcases hTree with
                ⟨_, hDecodedLeft, hDecodedRight⟩
              cases hDecodedLeft
              cases hDecodedRight
              refine ⟨left.tokens, right.tokens, ?_, ?_, ?_⟩
              · rw [← RawHilbertTokenTree.parse?_sound hParse]
                simp [RawHilbertTokenTree.tokens,
                  Numbered.equality_tokens, List.append_assoc]
              · exact
                  fs_named_term_tokens_decode_with_env_of_tree
                    freeBase boundNames hLeft
              · exact
                  fs_named_term_tokens_decode_with_env_of_tree
                    freeBase boundNames hRight
  | membership left right =>
      cases hLeft :
          fs_named_term_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hLeft] at hTree
      | some decodedLeft =>
          cases hRight :
              fs_named_term_token_tree_decode
                freeBase boundNames right with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hTree
          | some decodedRight =>
              by_cases hCheck :
                  Term.check_args_wellSorted
                      [decodedLeft, decodedRight]
                      (signature.relDomain
                        RelationSymbol.membership) =
                    true
              · simp [fs_named_hilbert_token_tree_decode,
                  hLeft, hRight, hCheck] at hTree
              · simp [fs_named_hilbert_token_tree_decode,
                  hLeft, hRight, hCheck] at hTree
  | predicate head arguments =>
      cases hRelation :
          fs_find_encoded
            (fun candidate : RelationSymbol =>
              Numbered.predicate_token
                (arguments.length - 1)
                candidate.ctorIdx)
            head fs_relation_symbols with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hRelation] at hTree
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
                  hRelation, hArguments] at hTree
            | some decoded =>
                by_cases hCheck :
                    Term.check_args_wellSorted decoded
                        (signature.relDomain relation) =
                      true
                · simp [fs_named_hilbert_token_tree_decode,
                    hRelation, hKind, hArguments,
                    hCheck] at hTree
                · simp [fs_named_hilbert_token_tree_decode,
                    hRelation, hKind, hArguments,
                    hCheck] at hTree
          · simp [fs_named_hilbert_token_tree_decode,
              hRelation, hKind] at hTree
  | negation body =>
      cases hBody :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames body with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hBody] at hTree
      | some bodyFormula =>
          simp [fs_named_hilbert_token_tree_decode,
            hBody] at hTree
  | implication left right =>
      cases hLeft :
          fs_named_hilbert_token_tree_decode
            freeBase boundNames left with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hLeft] at hTree
      | some leftFormula =>
          cases hRight :
              fs_named_hilbert_token_tree_decode
                freeBase boundNames right with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hTree
          | some rightFormula =>
              simp [fs_named_hilbert_token_tree_decode,
                hLeft, hRight] at hTree
  | universal variableToken body =>
      cases hName :
          fs_variable_name_decode variableToken with
      | none =>
          simp [fs_named_hilbert_token_tree_decode,
            hName] at hTree
      | some name =>
          cases hBody :
              fs_named_hilbert_token_tree_decode
                freeBase (name :: boundNames) body with
          | none =>
              simp [fs_named_hilbert_token_tree_decode,
                hName, hBody] at hTree
          | some bodyFormula =>
              simp [fs_named_hilbert_token_tree_decode,
                hName, hBody] at hTree

/-- 隶属原子由两棵成功项树组合得到成功公式解码。 -/
theorem fs_named_hilbert_tokens_decode_with_env_membership
    (freeBase : Nat) (boundNames : List Nat)
    {leftTree rightTree : RawTermTokenTree}
    {leftTerm rightTerm : SetTerm}
    (hLeft :
      fs_named_term_token_tree_decode
          freeBase boundNames leftTree =
        some leftTerm)
    (hRight :
      fs_named_term_token_tree_decode
          freeBase boundNames rightTree =
        some rightTerm)
    (hCheck :
      Term.check_args_wellSorted
          [leftTerm, rightTerm]
          (signature.relDomain
            RelationSymbol.membership) =
        true) :
    fs_named_hilbert_tokens_decode_with_env
        freeBase boundNames
        (Numbered.membership_tokens
          leftTree.tokens rightTree.tokens) =
      some (.rel RelationSymbol.membership
        [leftTerm, rightTerm]) := by
  let tree : RawHilbertTokenTree :=
    .membership leftTree rightTree
  have hTreeDecode :
      fs_named_hilbert_token_tree_decode
          freeBase boundNames tree =
        some (.rel RelationSymbol.membership
          [leftTerm, rightTerm]) := by
    simp [tree, fs_named_hilbert_token_tree_decode,
      hLeft, hRight, hCheck]
  have hWhole :=
    fs_named_hilbert_tokens_decode_with_env_of_tree
      freeBase boundNames hTreeDecode
  simpa [tree, RawHilbertTokenTree.tokens,
    Numbered.membership_tokens, List.append_assoc] using hWhole

/--
左右完整项 token 均成功时，等式原子整串在同一名字环境下成功解码。

parser 树与单排序良排序证书均在本接口内部恢复。
-/
theorem fs_named_hilbert_tokens_decode_with_env_equality_of_term_tokens
    (freeBase : Nat) (boundNames : List Nat)
    {leftTokens rightTokens : List Nat}
    {leftTerm rightTerm : SetTerm}
    (hLeft :
      fs_named_term_tokens_decode_with_env
          freeBase boundNames leftTokens =
        some leftTerm)
    (hRight :
      fs_named_term_tokens_decode_with_env
          freeBase boundNames rightTokens =
        some rightTerm) :
    fs_named_hilbert_tokens_decode_with_env
        freeBase boundNames
        (Numbered.equality_tokens
          leftTokens rightTokens) =
      some (.equal leftTerm rightTerm) := by
  rcases
      (fs_named_term_tokens_decode_with_env_iff
        freeBase boundNames leftTokens leftTerm).mp
        hLeft with
    ⟨leftTree, hLeftParse, hLeftTree⟩
  rcases
      (fs_named_term_tokens_decode_with_env_iff
        freeBase boundNames rightTokens rightTerm).mp
        hRight with
    ⟨rightTree, hRightParse, hRightTree⟩
  have hLeftTokens :
      leftTree.tokens = leftTokens :=
    RawTermTokenTree.parse?_sound hLeftParse
  have hRightTokens :
      rightTree.tokens = rightTokens :=
    RawTermTokenTree.parse?_sound hRightParse
  have hLeftCheck :
      Term.check_wellSorted
          SetSort.set leftTerm =
        true :=
    Term.check_wellSorted_complete
      (fs_named_term_token_tree_decode_admissible
        freeBase boundNames hLeftTree).1
  have hRightCheck :
      Term.check_wellSorted
          SetSort.set rightTerm =
        true :=
    Term.check_wellSorted_complete
      (fs_named_term_token_tree_decode_admissible
        freeBase boundNames hRightTree).1
  simpa [hLeftTokens, hRightTokens] using
    fs_named_hilbert_tokens_decode_with_env_equality
      freeBase boundNames hLeftTree hRightTree
      hLeftCheck hRightCheck

/--
左右完整项 token 均成功时，隶属原子整串在同一名字环境下成功解码。
-/
theorem fs_named_hilbert_tokens_decode_with_env_membership_of_term_tokens
    (freeBase : Nat) (boundNames : List Nat)
    {leftTokens rightTokens : List Nat}
    {leftTerm rightTerm : SetTerm}
    (hLeft :
      fs_named_term_tokens_decode_with_env
          freeBase boundNames leftTokens =
        some leftTerm)
    (hRight :
      fs_named_term_tokens_decode_with_env
          freeBase boundNames rightTokens =
        some rightTerm) :
    fs_named_hilbert_tokens_decode_with_env
        freeBase boundNames
        (Numbered.membership_tokens
          leftTokens rightTokens) =
      some (.rel RelationSymbol.membership
        [leftTerm, rightTerm]) := by
  rcases
      (fs_named_term_tokens_decode_with_env_iff
        freeBase boundNames leftTokens leftTerm).mp
        hLeft with
    ⟨leftTree, hLeftParse, hLeftTree⟩
  rcases
      (fs_named_term_tokens_decode_with_env_iff
        freeBase boundNames rightTokens rightTerm).mp
        hRight with
    ⟨rightTree, hRightParse, hRightTree⟩
  have hLeftTokens :
      leftTree.tokens = leftTokens :=
    RawTermTokenTree.parse?_sound hLeftParse
  have hRightTokens :
      rightTree.tokens = rightTokens :=
    RawTermTokenTree.parse?_sound hRightParse
  have hArguments :
      ArgsWellSorted
          [leftTerm, rightTerm]
          (signature.relDomain
            RelationSymbol.membership) := by
    exact .cons
      (fs_named_term_token_tree_decode_admissible
        freeBase boundNames hLeftTree).1 <|
        .cons
          (fs_named_term_token_tree_decode_admissible
            freeBase boundNames hRightTree).1
          .nil
  have hCheck :
      Term.check_args_wellSorted
          [leftTerm, rightTerm]
          (signature.relDomain
            RelationSymbol.membership) =
        true :=
    Term.check_args_wellSorted_complete hArguments
  simpa [hLeftTokens, hRightTokens] using
    fs_named_hilbert_tokens_decode_with_env_membership
      freeBase boundNames hLeftTree hRightTree hCheck

/--
一列参数 token 串逐项成功解码且数量匹配关系元数时，规范谓词应用串在同一
名字环境下成功解码。
-/
theorem
    fs_named_hilbert_tokens_decode_with_env_predicate_of_term_token_lists
    (freeBase : Nat) (boundNames : List Nat)
    (symbol : RelationSymbol)
    (hSymbol :
      symbol ≠ RelationSymbol.membership)
    {tokenLists : List (List Nat)}
    {arguments : List SetTerm}
    (hArguments :
      tokenLists.mapM
          (fs_named_term_tokens_decode_with_env
            freeBase boundNames) =
        some arguments)
    (hArity :
      arguments.length =
        (signature.relDomain symbol).length) :
    fs_named_hilbert_tokens_decode_with_env
        freeBase boundNames
        (Numbered.predicate_application_tokens
          (arguments.length - 1)
          symbol.ctorIdx tokenLists) =
      some (.rel symbol arguments) := by
  rcases
      fs_named_term_token_lists_decode_with_env_trees
        freeBase boundNames hArguments with
    ⟨trees, hTreeTokens, hTreeDecodes⟩
  let tree : RawHilbertTokenTree :=
    .predicate
      (Numbered.predicate_token
        (arguments.length - 1) symbol.ctorIdx)
      trees
  have hLength :
      arguments.length = trees.length :=
    fs_option_mapM_length hTreeDecodes
  have hWellSorted :
      Term.check_args_wellSorted
          arguments (signature.relDomain symbol) =
        true := by
    apply Term.check_args_wellSorted_complete
    rw [set_relation_domain_replicate, ← hArity]
    exact
      fs_named_term_token_trees_decode_wellSorted
        freeBase boundNames hTreeDecodes
  have hKind :
      fs_relation_kind symbol =
        QuotationRelationKind.predicate :=
    fs_relation_kind_eq_predicate hSymbol
  have hTreeDecode :
      fs_named_hilbert_token_tree_decode
          freeBase boundNames tree =
        some (.rel symbol arguments) := by
    simp [tree, fs_named_hilbert_token_tree_decode,
      hLength, fs_predicate_symbol_lookup,
      hKind,
      hTreeDecodes, hWellSorted]
  have hWhole :=
    fs_named_hilbert_tokens_decode_with_env_of_tree
      freeBase boundNames hTreeDecode
  have hListTokens :
      RawTermTokenTree.list_tokens trees =
        tokenLists.flatten := by
    rw [←
      RawTermTokenTree.map_tokens_flatten_eq_list_tokens,
      hTreeTokens]
  simpa [tree, RawHilbertTokenTree.tokens,
    RawTermTokenTree.list_tokens,
    Numbered.predicate_application_tokens,
    hListTokens, List.append_assoc] using hWhole

/-! ## 成功解码的对象公式码闭包 -/

/-- 已知公式码与标准 token 序列相等时，把集合成员运输到该标准序列。 -/
private theorem gq_formula_code_member_of_eq_standard
    (code : SetTerm) (tokens : List Nat)
    (hCode : Term.Admissible code SetSort.set)
    (hMember :
      ⊢ₘ[godel_quotation_theory]
        code ∈ₘ FormulaCodeₘ)
    (hEquality :
      ⊢ₘ[godel_quotation_theory]
        code ≐ₘ standard_token_sequence tokens) :
    ⊢ₘ[godel_quotation_theory]
      standard_token_sequence tokens ∈ₘ FormulaCodeₘ :=
  FirstOrder.Derives.iffElimRight
    (membership_left_iff_of_equality
      code (standard_token_sequence tokens) FormulaCodeₘ
      hCode
      (standard_token_sequence_admissible tokens)
      formula_code_set_term_admissible
      hEquality)
    hMember

/-- 参数 sort 检查成功时，实参列与 sort 列等长。 -/
private theorem fs_check_args_wellSorted_length
    {arguments : List SetTerm} {sorts : List SetSort}
    (hCheck :
      Term.check_args_wellSorted arguments sorts = true) :
    arguments.length = sorts.length := by
  induction arguments generalizing sorts with
  | nil =>
      cases sorts with
      | nil =>
          rfl
      | cons sort sorts =>
          simp [Term.check_args_wellSorted] at hCheck
  | cons term terms ih =>
      cases sorts with
      | nil =>
          simp [Term.check_args_wellSorted] at hCheck
      | cons sort sorts =>
          have hRest :
              Term.check_args_wellSorted terms sorts = true := by
            simpa [Term.check_args_wellSorted] using
              (Bool.and_eq_true_iff.mp hCheck).2
          simp [ih hRest]

/--
成功具名解码的 Hilbert 树，其原始标准 token 序列属于对象集合 `FormulaCodeₘ`。
证明只按六种原始树构造递归，并复用项树正向闭包及现有公式构造合同。
-/
theorem fs_named_hilbert_token_tree_decode_standard_formula_code
    (freeBase : Nat) :
    ∀ {boundNames : List Nat}
        {tree : RawHilbertTokenTree}
        {formula : SetFormula},
      fs_named_hilbert_token_tree_decode
          freeBase boundNames tree =
        some formula →
      ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tree.tokens ∈ₘ FormulaCodeₘ
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
              by_cases hLeftCheck :
                  Term.check_wellSorted
                      SetSort.set leftTerm =
                    true
              · by_cases hRightCheck :
                    Term.check_wellSorted
                        SetSort.set rightTerm =
                      true
                · have hLeftCode :=
                    fs_named_term_token_tree_decode_standard_term_code
                      freeBase boundNames hLeft
                  have hRightCode :=
                    fs_named_term_token_tree_decode_standard_term_code
                      freeBase boundNames hRight
                  let leftCode :=
                    standard_token_sequence left.tokens
                  let rightCode :=
                    standard_token_sequence right.tokens
                  have hMember :
                      ⊢ₘ[godel_quotation_theory]
                        eq_codeₘ(leftCode, rightCode) ∈ₘ
                          FormulaCodeₘ :=
                    gq_equality_formula_code_mem
                      leftCode rightCode
                      (standard_token_sequence_admissible left.tokens)
                      (standard_token_sequence_admissible right.tokens)
                      (standard_token_sequence_freeSupport_nil left.tokens)
                      (standard_token_sequence_freeSupport_nil right.tokens)
                      (by simpa [leftCode] using hLeftCode)
                      (by simpa [rightCode] using hRightCode)
                  have hEqualityRaw :=
                    equality_formula_code_eq_standard_token_sequence
                      left.tokens right.tokens leftCode rightCode
                      (by simpa [leftCode] using hLeftCode)
                      (by simpa [rightCode] using hRightCode)
                      (FirstOrder.Derives.eq_refl_m leftCode)
                      (FirstOrder.Derives.eq_refl_m rightCode)
                  have hEquality :
                      ⊢ₘ[godel_quotation_theory]
                        eq_codeₘ(leftCode, rightCode) ≐ₘ
                          standard_token_sequence
                            (RawHilbertTokenTree.equality
                              left right).tokens := by
                    simpa [RawHilbertTokenTree.tokens,
                      Numbered.equality_tokens,
                      List.append_assoc] using hEqualityRaw
                  exact
                    gq_formula_code_member_of_eq_standard
                      (eq_codeₘ(leftCode, rightCode))
                      (RawHilbertTokenTree.equality
                        left right).tokens
                      (equality_formula_code_term_admissible
                        leftCode rightCode
                        (standard_token_sequence_admissible
                          left.tokens)
                        (standard_token_sequence_admissible
                          right.tokens))
                      hMember hEquality
                · simp [fs_named_hilbert_token_tree_decode,
                    hLeft, hRight, hRightCheck] at hDecode
              · simp [fs_named_hilbert_token_tree_decode,
                  hLeft, hRight, hLeftCheck] at hDecode
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
                        RelationSymbol.membership) =
                    true
              · have hLeftCode :=
                    fs_named_term_token_tree_decode_standard_term_code
                      freeBase boundNames hLeft
                have hRightCode :=
                    fs_named_term_token_tree_decode_standard_term_code
                      freeBase boundNames hRight
                let leftCode :=
                  standard_token_sequence left.tokens
                let rightCode :=
                  standard_token_sequence right.tokens
                have hMember :
                    ⊢ₘ[godel_quotation_theory]
                      membership_atomic_formula_code_term
                          leftCode rightCode ∈ₘ
                        FormulaCodeₘ :=
                  gq_membership_formula_code_mem
                    leftCode rightCode
                    (standard_token_sequence_admissible left.tokens)
                    (standard_token_sequence_admissible right.tokens)
                    (standard_token_sequence_freeSupport_nil left.tokens)
                    (standard_token_sequence_freeSupport_nil right.tokens)
                    (by simpa [leftCode] using hLeftCode)
                    (by simpa [rightCode] using hRightCode)
                have hEqualityRaw :=
                  membership_formula_string_eq_standard_token_sequence
                    left.tokens right.tokens leftCode rightCode
                    (FirstOrder.Derives.eq_refl_m leftCode)
                    (FirstOrder.Derives.eq_refl_m rightCode)
                have hEquality :
                    ⊢ₘ[godel_quotation_theory]
                      membership_atomic_formula_code_term
                          leftCode rightCode ≐ₘ
                        standard_token_sequence
                          (RawHilbertTokenTree.membership
                            left right).tokens := by
                  simpa [RawHilbertTokenTree.tokens,
                    Numbered.membership_tokens,
                    List.append_assoc] using hEqualityRaw
                exact
                  gq_formula_code_member_of_eq_standard
                    (membership_atomic_formula_code_term
                      leftCode rightCode)
                    (RawHilbertTokenTree.membership
                      left right).tokens
                    (binary_atomic_formula_code_term_admissible
                      membership_symbol_code_term
                      leftCode rightCode
                      membership_symbol_code_term_admissible
                      (standard_token_sequence_admissible
                        left.tokens)
                      (standard_token_sequence_admissible
                        right.tokens))
                    hMember hEquality
              · simp [fs_named_hilbert_token_tree_decode,
                  hLeft, hRight, hCheck] at hDecode
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
                · have hDecodedArity :
                      decoded.length =
                        (signature.relDomain relation).length :=
                    fs_check_args_wellSorted_length hCheck
                  have hInputArity :
                      arguments.length =
                        (signature.relDomain relation).length :=
                    (fs_option_mapM_length hArguments).symm.trans
                      hDecodedArity
                  have hNonempty : arguments ≠ [] := by
                    intro hNil
                    apply
                      fs_quotation_numbering.relation_nonempty
                        relation
                    apply List.eq_nil_of_length_eq_zero
                    simpa [hNil] using hInputArity.symm
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
                  rcases
                      fs_named_term_token_trees_decode_standard_term_codes
                        freeBase boundNames hArguments with
                    ⟨hAligned, hTermCodes⟩
                  cases arguments with
                  | nil =>
                      exact (hNonempty rfl).elim
                  | cons first rest =>
                      let codes :=
                        (first :: rest).map
                          (fun tree =>
                            standard_token_sequence tree.tokens)
                      let family := standard_sequence codes
                      have hElements :
                          ∀ element, element ∈ codes →
                            Term.CheckCertificate
                              element SetSort.set := by
                        intro element hElement
                        exact
                          (gq_aligned_codes_boundary
                            hAligned element hElement).check_certificate
                      have hElementsClosed :
                          ∀ element, element ∈ codes →
                            Term.freeSupport element = [] := by
                        intro element hElement
                        exact
                          (gq_aligned_codes_boundary
                            hAligned element hElement).2
                      have hFamily :
                          Term.CheckCertificate family SetSort.set := by
                        apply standard_sequence_from_check
                        exact hElements
                      have hTermSequence :
                          ⊢ₘ[godel_quotation_theory]
                            family ∈ₘ TermSeqₘ := by
                        simpa [family, codes] using
                          gq_aligned_term_code_family_mem_term_sequence
                            hAligned hTermCodes
                      have hDomain :
                          ⊢ₘ[godel_quotation_theory]
                            domₘ(family) ≐ₘ
                              Sₘ(numₘ(rest.length)) := by
                        have hRaw :=
                          gq_weaken_standard_sequence <|
                            standard_sequence_domain_eq_numeral_length
                              (fun element hElement =>
                                (hElements element hElement).admissible)
                              (stdseq_element_fresh_of_support_nil
                                hElementsClosed 0)
                              (stdseq_element_fresh_of_support_nil
                                hElementsClosed 1)
                        simpa [family, codes,
                          finite_numeral_term] using hRaw
                      have hMember :
                          ⊢ₘ[godel_quotation_theory]
                            predicate_application_code_term
                                (numₘ(rest.length))
                                (numₘ(relation.ctorIdx))
                                family ∈ₘ
                              FormulaCodeₘ :=
                        gq_predicate_application_formula_code_mem
                          rest.length relation.ctorIdx family
                          hFamily.admissible
                          (seq_support_nil_m
                            0 hElementsClosed)
                          hTermSequence hDomain
                      have hEqualityRaw :=
                        gq_predicate_application_code_eq_standard_token_sequence
                          rest.length relation.ctorIdx hAligned
                      have hEquality :
                          ⊢ₘ[godel_quotation_theory]
                            predicate_application_code_term
                                (numₘ(rest.length))
                                (numₘ(relation.ctorIdx))
                                family ≐ₘ
                              standard_token_sequence
                                (RawHilbertTokenTree.predicate
                                  head (first :: rest)).tokens := by
                        simpa [family, codes,
                          RawHilbertTokenTree.tokens,
                          RawTermTokenTree.list_tokens,
                          RawTermTokenTree.map_tokens_flatten_eq_list_tokens,
                          Numbered.predicate_application_tokens,
                          ← hToken, List.append_assoc] using
                            hEqualityRaw
                      exact
                        gq_formula_code_member_of_eq_standard
                          (predicate_application_code_term
                            (numₘ(rest.length))
                            (numₘ(relation.ctorIdx))
                            family)
                          (RawHilbertTokenTree.predicate
                            head (first :: rest)).tokens
                          (predicate_application_code_term_admissible
                            (numₘ(rest.length))
                            (numₘ(relation.ctorIdx))
                            family
                            (finite_numeral_term_admissible
                              rest.length)
                            (finite_numeral_term_admissible
                              relation.ctorIdx)
                            hFamily.admissible)
                          hMember hEquality
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
          let bodyCode :=
            standard_token_sequence body.tokens
          have hBodyMember :=
            fs_named_hilbert_token_tree_decode_standard_formula_code
              freeBase hBody
          have hMember :
              ⊢ₘ[godel_quotation_theory]
                neg_codeₘ(bodyCode) ∈ₘ FormulaCodeₘ :=
            gq_formula_code_mem_negation
              bodyCode
              (standard_token_sequence_admissible body.tokens)
              (by simpa [bodyCode] using hBodyMember)
          have hEqualityRaw :=
            negation_formula_code_eq_standard_token_sequence
              body.tokens bodyCode
              (FirstOrder.Derives.eq_refl_m bodyCode)
          have hEquality :
              ⊢ₘ[godel_quotation_theory]
                neg_codeₘ(bodyCode) ≐ₘ
                  standard_token_sequence
                    (RawHilbertTokenTree.negation body).tokens := by
            simpa [RawHilbertTokenTree.tokens,
              Numbered.negation_tokens,
              List.append_assoc] using hEqualityRaw
          exact
            gq_formula_code_member_of_eq_standard
              (neg_codeₘ(bodyCode))
              (RawHilbertTokenTree.negation body).tokens
              (negation_formula_code_term_admissible
                bodyCode
                (standard_token_sequence_admissible
                  body.tokens))
              hMember hEquality
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
              let leftCode :=
                standard_token_sequence left.tokens
              let rightCode :=
                standard_token_sequence right.tokens
              have hLeftMember :=
                fs_named_hilbert_token_tree_decode_standard_formula_code
                  freeBase hLeft
              have hRightMember :=
                fs_named_hilbert_token_tree_decode_standard_formula_code
                  freeBase hRight
              have hMember :
                  ⊢ₘ[godel_quotation_theory]
                    imp_codeₘ(leftCode, rightCode) ∈ₘ
                      FormulaCodeₘ :=
                gq_formula_code_mem_implication
                  leftCode rightCode
                  (standard_token_sequence_admissible left.tokens)
                  (standard_token_sequence_admissible right.tokens)
                  (by simpa [leftCode] using hLeftMember)
                  (by simpa [rightCode] using hRightMember)
              have hEqualityRaw :=
                implication_formula_code_eq_standard_token_sequence
                  left.tokens right.tokens leftCode rightCode
                  (FirstOrder.Derives.eq_refl_m leftCode)
                  (FirstOrder.Derives.eq_refl_m rightCode)
              have hEquality :
                  ⊢ₘ[godel_quotation_theory]
                    imp_codeₘ(leftCode, rightCode) ≐ₘ
                      standard_token_sequence
                        (RawHilbertTokenTree.implication
                          left right).tokens := by
                simpa [RawHilbertTokenTree.tokens,
                  Numbered.implication_tokens,
                  List.append_assoc] using hEqualityRaw
              exact
                gq_formula_code_member_of_eq_standard
                  (imp_codeₘ(leftCode, rightCode))
                  (RawHilbertTokenTree.implication
                    left right).tokens
                  (implication_formula_code_term_admissible
                    leftCode rightCode
                    (standard_token_sequence_admissible
                      left.tokens)
                    (standard_token_sequence_admissible
                      right.tokens))
                  hMember hEquality
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
              let variableCode :=
                Numbered.named_variable_code name
              let bodyCode :=
                standard_token_sequence body.tokens
              have hVariableToken :
                  Numbered.variable_token name =
                    variableToken :=
                fs_variable_name_decode_value_of_some hName
              have hBodyMember :=
                fs_named_hilbert_token_tree_decode_standard_formula_code
                  freeBase hBody
              have hMember :
                  ⊢ₘ[godel_quotation_theory]
                    forall_codeₘ(variableCode, bodyCode) ∈ₘ
                      FormulaCodeₘ :=
                gq_formula_code_mem_universal
                  variableCode bodyCode
                  (variable_code_term_admissible
                    (numₘ(name))
                    (finite_numeral_term_admissible name))
                  (standard_token_sequence_admissible body.tokens)
                  (by
                    simpa [variableCode] using
                      named_variable_code_mem_variable_symbols name)
                  (by simpa [bodyCode] using hBodyMember)
              have hEqualityRaw :=
                universal_formula_code_eq_standard_token_sequence
                  name body.tokens bodyCode
                  (FirstOrder.Derives.eq_refl_m bodyCode)
              have hEquality :
                  ⊢ₘ[godel_quotation_theory]
                    forall_codeₘ(variableCode, bodyCode) ≐ₘ
                      standard_token_sequence
                        (RawHilbertTokenTree.universal
                          variableToken body).tokens := by
                simpa [variableCode,
                  RawHilbertTokenTree.tokens,
                  Numbered.universal_tokens,
                  hVariableToken, List.append_assoc] using
                    hEqualityRaw
              exact
                gq_formula_code_member_of_eq_standard
                  (forall_codeₘ(variableCode, bodyCode))
                  (RawHilbertTokenTree.universal
                    variableToken body).tokens
                  (universal_formula_code_term_admissible
                    variableCode bodyCode
                    (variable_code_term_admissible
                      (numₘ(name))
                      (finite_numeral_term_admissible name))
                    (standard_token_sequence_admissible
                      body.tokens))
                  hMember hEquality
termination_by _ tree _ _ => sizeOf tree

/--
当 parser 树已固定时，在其自身自由变量基数与空环境下的显式解码可直接回到
公开具名 decoder。
-/
theorem fs_named_hilbert_tokens_decode_of_with_env
    {tokens : List Nat}
    {tree : RawHilbertTokenTree}
    {formula : SetFormula}
    (hParse :
      RawHilbertTokenTree.parse? tokens = some tree)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          (fs_hilbert_token_tree_free_base tree)
          [] tokens =
        some formula) :
    fs_named_hilbert_tokens_decode tokens =
      some formula := by
  unfold fs_named_hilbert_tokens_decode_with_env at hDecode
  unfold fs_named_hilbert_tokens_decode
  simp [hParse] at hDecode ⊢
  exact hDecode

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
