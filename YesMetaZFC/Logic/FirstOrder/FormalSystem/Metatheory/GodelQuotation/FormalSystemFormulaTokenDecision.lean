import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaCodeReplay

/-!
# FormalSystem 公式 token 的可计算判定

本模块把 `FSFormulaToken` 从正向证书命题提升为真正可计算的判定接口。变量 token
使用既有有界名字解码器；其余 token 只在当前有限签名的固定证书表中搜索。

实现不使用 `Classical` 或不可计算实例，供 checked replay 的负向失败定位复用。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory

set_option autoImplicit false

/-- 有限编码搜索成功时，返回值确实来自输入表。 -/
theorem fs_find_encoded_mem_of_some
    {α : Type}
    {encode : α → Nat}
    {target : Nat} :
    ∀ {items : List α} {item : α},
      fs_find_encoded encode target items = some item →
        item ∈ items
  | .nil, item, hFind => by
      simp [fs_find_encoded] at hFind
  | .cons head tail, item, hFind => by
      by_cases hHead : encode head = target
      · simp [fs_find_encoded, hHead] at hFind
        subst item
        simp
      · simp [fs_find_encoded, hHead] at hFind
        exact List.mem_cons_of_mem head
          (fs_find_encoded_mem_of_some hFind)

/--
若有限表中已有一个编码等于目标的元素，则搜索必然返回某个编码相同的元素。
这里不要求编码单射。
-/
theorem fs_find_encoded_some_of_mem_value
    {α : Type}
    {encode : α → Nat}
    {target : Nat}
    {item : α} :
    ∀ {items : List α},
      item ∈ items →
      encode item = target →
        ∃ found,
          fs_find_encoded encode target items =
            some found
  | .nil, hMember, _ => by
      simp at hMember
  | .cons head tail, hMember, hValue => by
      rcases List.mem_cons.mp hMember with rfl | hTail
      · simp [fs_find_encoded, hValue]
      · by_cases hHead : encode head = target
        · exact ⟨head, by simp [fs_find_encoded, hHead]⟩
        · rcases
              fs_find_encoded_some_of_mem_value
                hTail hValue with
            ⟨found, hFound⟩
          exact
            ⟨found, by
              simp [fs_find_encoded, hHead, hFound]⟩

/-- 固定有限 token 及其宿主分类证书。 -/
structure FSFormulaFixedToken where
  token : Nat
  h_token : FSFormulaToken token

/-- token 分类器返回的两类可计算来源。 -/
inductive FSFormulaTokenSource where
  | variable (name : Nat)
  | fixed (token : FSFormulaFixedToken)

private def fs_logical_formula_fixed_tokens :
    List FSFormulaFixedToken :=
  logical_symbol_kinds.map fun symbol =>
    ⟨Numbered.logical_token symbol,
      FSFormulaToken.logical symbol⟩

private def fs_membership_formula_fixed_token :
    FSFormulaFixedToken :=
  ⟨Numbered.membership_token,
    FSFormulaToken.membership⟩

private def fs_function_formula_fixed_tokens :
    List FSFormulaFixedToken :=
  fs_function_symbols.map fun symbol =>
    ⟨fs_function_symbol_token symbol,
      FSFormulaToken.func symbol⟩

private theorem fs_predicate_symbol_ne_membership_of_mem
    {symbol : RelationSymbol}
    (hSymbol : symbol ∈ fs_predicate_symbols) :
    symbol ≠ RelationSymbol.membership :=
  of_decide_eq_true
    (List.mem_filter.mp hSymbol).2

private def fs_predicate_formula_fixed_tokens :
    List FSFormulaFixedToken :=
  fs_predicate_symbols.attach.map fun symbol =>
    ⟨fs_predicate_symbol_token symbol.1,
      FSFormulaToken.pred symbol.1
        (fs_predicate_symbol_ne_membership_of_mem
          symbol.2)⟩

/-- 除变量以外，当前有限签名允许的全部固定 token 证书。 -/
def fs_formula_fixed_tokens :
    List FSFormulaFixedToken :=
  fs_logical_formula_fixed_tokens ++
    [fs_membership_formula_fixed_token] ++
    fs_function_formula_fixed_tokens ++
    fs_predicate_formula_fixed_tokens

/--
一个 token 的可计算分类来源。变量先走有界名字解码，其余分支只搜索固定有限
证书表。
-/
def fs_formula_token_source?
    (token : Nat) : Option FSFormulaTokenSource :=
  match fs_variable_name_decode token with
  | some name =>
      some (.variable name)
  | none =>
      match
          fs_find_encoded FSFormulaFixedToken.token
            token fs_formula_fixed_tokens with
      | some fixed =>
          some (.fixed fixed)
      | none =>
          none

/-- 分类来源成功时，目标自然数确实是合法公式 token。 -/
theorem fs_formula_token_source_sound
    {token : Nat} {source : FSFormulaTokenSource}
    (hSource :
      fs_formula_token_source? token = some source) :
    FSFormulaToken token := by
  unfold fs_formula_token_source? at hSource
  cases hVariable :
      fs_variable_name_decode token with
  | some name =>
      simp [hVariable] at hSource
      subst source
      have hValue :
          Numbered.variable_token name = token :=
        fs_variable_name_decode_value_of_some
          hVariable
      rw [← hValue]
      exact FSFormulaToken.var name
  | none =>
      cases hFixed :
          fs_find_encoded FSFormulaFixedToken.token
            token fs_formula_fixed_tokens with
      | none =>
          simp [hVariable, hFixed] at hSource
      | some fixed =>
          simp [hVariable, hFixed] at hSource
          subst source
          have hValue :
              fixed.token = token :=
            fs_find_encoded_value_of_some hFixed
          rw [← hValue]
          exact fixed.h_token

private theorem
    fs_formula_token_source_is_some_of_fixed_mem
    {fixed : FSFormulaFixedToken}
    (hFixed : fixed ∈ fs_formula_fixed_tokens) :
    (fs_formula_token_source? fixed.token).isSome =
      true := by
  unfold fs_formula_token_source?
  cases hVariable :
      fs_variable_name_decode fixed.token with
  | some name =>
      simp
  | none =>
      rcases
          fs_find_encoded_some_of_mem_value
            (encode := FSFormulaFixedToken.token)
            (target := fixed.token)
            hFixed rfl with
        ⟨found, hFound⟩
      simp [hFound]

private theorem
    fs_logical_formula_fixed_token_mem
    (symbol : LogicalSymbolKind) :
    (⟨Numbered.logical_token symbol,
        FSFormulaToken.logical symbol⟩ :
        FSFormulaFixedToken) ∈
      fs_formula_fixed_tokens := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨symbol, ?_, rfl⟩
  cases symbol <;> simp [logical_symbol_kinds]

private theorem
    fs_membership_formula_fixed_token_mem :
    fs_membership_formula_fixed_token ∈
      fs_formula_fixed_tokens := by
  simp [fs_formula_fixed_tokens]

private theorem
    fs_function_formula_fixed_token_mem
    (symbol : FunctionSymbol) :
    (⟨fs_function_symbol_token symbol,
        FSFormulaToken.func symbol⟩ :
        FSFormulaFixedToken) ∈
      fs_formula_fixed_tokens := by
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_map.mpr
  exact ⟨symbol, fs_function_symbols_complete symbol, rfl⟩

private theorem
    fs_predicate_formula_fixed_token_mem
    (symbol : RelationSymbol)
    (hSymbol : symbol ≠ RelationSymbol.membership) :
    (⟨fs_predicate_symbol_token symbol,
        FSFormulaToken.pred symbol hSymbol⟩ :
        FSFormulaFixedToken) ∈
      fs_formula_fixed_tokens := by
  have hMember :
      symbol ∈ fs_predicate_symbols := by
    apply List.mem_filter.mpr
    exact
      ⟨fs_relation_symbols_complete symbol,
        of_decide_eq_true <| by
          simpa using hSymbol⟩
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine
    ⟨⟨symbol, hMember⟩, ?_, ?_⟩
  · simp
  · rfl

/-- 任意合法公式 token 都能由可计算分类器返回证书。 -/
theorem fs_formula_token_source_is_some
    {token : Nat}
    (hToken : FSFormulaToken token) :
    (fs_formula_token_source? token).isSome =
      true := by
  cases hToken with
  | logical symbol =>
      exact
        fs_formula_token_source_is_some_of_fixed_mem
          (fs_logical_formula_fixed_token_mem symbol)
  | membership =>
      exact
        fs_formula_token_source_is_some_of_fixed_mem
          fs_membership_formula_fixed_token_mem
  | var name =>
      simp [fs_formula_token_source?,
        fs_variable_name_decode_encode]
  | func symbol =>
      exact
        fs_formula_token_source_is_some_of_fixed_mem
          (fs_function_formula_fixed_token_mem symbol)
  | pred symbol hSymbol =>
      exact
        fs_formula_token_source_is_some_of_fixed_mem
          (fs_predicate_formula_fixed_token_mem
            symbol hSymbol)

/-- 分类器返回 `none` 时，该 token 确实不属于当前公式签名。 -/
theorem fs_formula_token_not_of_source_none
    {token : Nat}
    (hSource :
      fs_formula_token_source? token = none) :
    ¬ FSFormulaToken token := by
  intro hToken
  have hSome :=
    fs_formula_token_source_is_some hToken
  rw [hSource] at hSome
  contradiction

/-- `FSFormulaToken` 的构造性判定实例。 -/
instance fs_formula_token_decidable
    (token : Nat) :
    Decidable (FSFormulaToken token) :=
  match hSource :
      fs_formula_token_source? token with
  | some _source =>
      isTrue
        (fs_formula_token_source_sound hSource)
  | none =>
      isFalse
        (fs_formula_token_not_of_source_none
          hSource)

/--
有限 token 行要么全部属于当前签名，要么给出首层递归定位出的具体坏位置。
-/
theorem fs_formula_tokens_or_bad_index
    (tokens : List Nat) :
    FSFormulaTokens tokens ∨
      ∃ index,
        ∃ hIndex : index < tokens.length,
          ¬ FSFormulaToken tokens[index] := by
  induction tokens with
  | nil =>
      exact Or.inl fs_formula_tokens_nil
  | cons head tail ih =>
      by_cases hHead : FSFormulaToken head
      · rcases ih with hTail | hTail
        · exact Or.inl
            (fs_formula_tokens_cons hHead hTail)
        · rcases hTail with
            ⟨index, hIndex, hBad⟩
          have hSucc :
              index + 1 < (head :: tail).length := by
            simpa using Nat.succ_lt_succ hIndex
          refine Or.inr ⟨index + 1, hSucc, ?_⟩
          simpa only [List.getElem_cons_succ] using hBad
      · have hZero : 0 < (head :: tail).length := by
          simp
        refine Or.inr ⟨0, hZero, ?_⟩
        simpa using hHead

/-! ## 正元函数 token 反演 -/

private theorem fs_logical_token_ne_function_token
    (symbol : LogicalSymbolKind)
    (arity index : Nat) :
    Numbered.logical_token symbol ≠
      Numbered.function_token arity index := by
  intro hEquality
  have hParity :=
    congrArg (fun token => token % 2) hEquality
  change Numbered.logical_token symbol % 2 =
    Numbered.function_token arity index % 2 at hParity
  rw [function_token_odd arity index] at hParity
  cases symbol <;>
    simp [Numbered.logical_token,
      logical_symbol_exponent] at hParity

private theorem fs_membership_token_ne_function_token
    (arity index : Nat) :
    Numbered.membership_token ≠
      Numbered.function_token arity index := by
  intro hEquality
  have hParity :=
    congrArg (fun token => token % 2) hEquality
  change Numbered.membership_token % 2 =
    Numbered.function_token arity index % 2 at hParity
  rw [function_token_odd arity index] at hParity
  simp [Numbered.membership_token] at hParity

private theorem fs_function_token_ne_constant_token
    (arity index constantIndex : Nat) :
    Numbered.function_token arity index ≠
      Numbered.constant_token constantIndex := by
  intro hEquality
  have hCoprime :
      Nat.Coprime
        (3 ^ (arity + 1))
        (5 ^ (constantIndex + 1)) :=
    Nat.Coprime.pow
      (arity + 1) (constantIndex + 1)
      (by decide)
  have hDiv :
      3 ^ (arity + 1) ∣
        5 ^ (constantIndex + 1) := by
    refine ⟨5 ^ (index + 1), ?_⟩
    simpa [Numbered.function_token,
      Numbered.constant_token] using hEquality.symm
  have hOne := hCoprime.eq_one_of_dvd hDiv
  simp at hOne

private theorem fs_predicate_token_ne_function_token
    (predicateArity predicateIndex
      functionArity functionIndex : Nat) :
    Numbered.predicate_token
        predicateArity predicateIndex ≠
      Numbered.function_token
        functionArity functionIndex := by
  intro hEquality
  have hCoprime :
      Nat.Coprime
        (5 ^ (functionIndex + 1))
        (3 ^ (predicateArity + 1) *
          7 ^ (predicateIndex + 1)) :=
    (Nat.Coprime.pow
      (functionIndex + 1)
      (predicateArity + 1)
      (by decide)).mul_right
        (Nat.Coprime.pow
          (functionIndex + 1)
          (predicateIndex + 1)
          (by decide))
  have hDiv :
      5 ^ (functionIndex + 1) ∣
        3 ^ (predicateArity + 1) *
          7 ^ (predicateIndex + 1) := by
    refine ⟨3 ^ (functionArity + 1), ?_⟩
    simpa [Numbered.predicate_token,
      Numbered.function_token, Nat.mul_comm] using
        hEquality
  have hOne := hCoprime.eq_one_of_dvd hDiv
  simp at hOne

/--
合法公式 token 若等于一个正元函数 token，则它唯一来自当前有限签名中的正元
函数符号；同时恢复其精确元数前驱和构造子编号。
-/
theorem fs_formula_token_eq_function_token
    {token arity index : Nat}
    (hToken : FSFormulaToken token)
    (hEquality :
      token = Numbered.function_token arity index) :
    ∃ symbol head tail,
      signature.funcDomain symbol = head :: tail ∧
        arity = tail.length ∧
        index = symbol.ctorIdx := by
  cases hToken with
  | logical symbol =>
      exact False.elim
        (fs_logical_token_ne_function_token
          symbol arity index hEquality)
  | membership =>
      exact False.elim
        (fs_membership_token_ne_function_token
          arity index hEquality)
  | var name =>
      exact False.elim
        (function_token_ne_variable_token
          arity index name hEquality.symm)
  | func symbol =>
      cases hDomain :
          signature.funcDomain symbol with
      | nil =>
          exact False.elim
            (fs_function_token_ne_constant_token
              arity index symbol.ctorIdx <| by
                simpa [fs_function_symbol_token,
                  hDomain] using hEquality.symm)
      | cons head tail =>
          have hFunctionEquality :
              Numbered.function_token
                  tail.length symbol.ctorIdx =
                Numbered.function_token
                  arity index := by
            simpa [fs_function_symbol_token,
              hDomain] using hEquality
          rcases
              token_reflection_function_token_injective
                hFunctionEquality with
            ⟨hArity, hIndex⟩
          exact
            ⟨symbol, head, tail, hDomain,
              hArity.symm, hIndex.symm⟩
  | pred symbol hSymbol =>
      exact False.elim
        (fs_predicate_token_ne_function_token
          (signature.relDomain symbol).length.pred
          symbol.ctorIdx arity index <| by
            simpa [fs_predicate_symbol_token] using
              hEquality)

/-! ## 正元谓词 token 反演 -/

private theorem fs_logical_token_ne_predicate_token
    (symbol : LogicalSymbolKind)
    (arity index : Nat) :
    Numbered.logical_token symbol ≠
      Numbered.predicate_token arity index := by
  intro hEquality
  have hParity :=
    congrArg (fun token => token % 2) hEquality
  change Numbered.logical_token symbol % 2 =
    Numbered.predicate_token arity index % 2 at hParity
  rw [predicate_token_odd arity index] at hParity
  cases symbol <;>
    simp [Numbered.logical_token,
      logical_symbol_exponent] at hParity

private theorem fs_membership_token_ne_predicate_token
    (arity index : Nat) :
    Numbered.membership_token ≠
      Numbered.predicate_token arity index := by
  intro hEquality
  have hParity :=
    congrArg (fun token => token % 2) hEquality
  change Numbered.membership_token % 2 =
    Numbered.predicate_token arity index % 2 at hParity
  rw [predicate_token_odd arity index] at hParity
  simp [Numbered.membership_token] at hParity

private theorem fs_predicate_token_ne_constant_token
    (arity index constantIndex : Nat) :
    Numbered.predicate_token arity index ≠
      Numbered.constant_token constantIndex := by
  intro hEquality
  have hCoprime :
      Nat.Coprime
        (5 ^ (constantIndex + 1))
        (3 ^ (arity + 1) *
          7 ^ (index + 1)) :=
    (Nat.Coprime.pow
      (constantIndex + 1)
      (arity + 1)
      (by decide)).mul_right
        (Nat.Coprime.pow
          (constantIndex + 1)
          (index + 1)
          (by decide))
  have hDiv :
      5 ^ (constantIndex + 1) ∣
        3 ^ (arity + 1) *
          7 ^ (index + 1) := by
    refine ⟨1, ?_⟩
    simpa [Numbered.predicate_token,
      Numbered.constant_token] using hEquality
  have hOne := hCoprime.eq_one_of_dvd hDiv
  simp at hOne

/--
合法公式 token 若等于一个正元谓词 token，则它唯一来自当前有限签名中的
非隶属关系符号，并恢复精确元数前驱与构造子编号。
-/
theorem fs_formula_token_eq_predicate_token
    {token arity index : Nat}
    (hToken : FSFormulaToken token)
    (hEquality :
      token = Numbered.predicate_token arity index) :
    ∃ symbol head tail,
      symbol ≠ RelationSymbol.membership ∧
        signature.relDomain symbol = head :: tail ∧
        arity = tail.length ∧
        index = symbol.ctorIdx := by
  cases hToken with
  | logical symbol =>
      exact False.elim
        (fs_logical_token_ne_predicate_token
          symbol arity index hEquality)
  | membership =>
      exact False.elim
        (fs_membership_token_ne_predicate_token
          arity index hEquality)
  | var name =>
      exact False.elim
        (predicate_token_ne_variable_token
          arity index name hEquality.symm)
  | func symbol =>
      cases hDomain :
          signature.funcDomain symbol with
      | nil =>
          exact False.elim
            (fs_predicate_token_ne_constant_token
              arity index symbol.ctorIdx <| by
                simpa [fs_function_symbol_token,
                  hDomain] using hEquality.symm)
      | cons head tail =>
          exact False.elim
            (fs_predicate_token_ne_function_token
              arity index tail.length symbol.ctorIdx <| by
                simpa [fs_function_symbol_token,
                  hDomain] using hEquality.symm)
  | pred symbol hSymbol =>
      cases hDomain :
          signature.relDomain symbol with
      | nil =>
          exact False.elim
            (fs_quotation_numbering.relation_nonempty
              symbol hDomain)
      | cons head tail =>
          have hPredicateEquality :
              Numbered.predicate_token
                  tail.length symbol.ctorIdx =
                Numbered.predicate_token arity index := by
            simpa [fs_predicate_symbol_token,
              hDomain] using hEquality
          rcases
              token_reflection_predicate_token_injective
                hPredicateEquality with
            ⟨hArity, hIndex⟩
          exact
            ⟨symbol, head, tail, hSymbol,
              hDomain, hArity.symm, hIndex.symm⟩

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
