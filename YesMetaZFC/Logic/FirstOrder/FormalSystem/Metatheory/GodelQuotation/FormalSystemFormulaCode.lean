import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemTokenDecoder

/-!
# FormalSystem 有限签名上的公式编码

`FormulaCodeₘ` 描述可数的一阶编码语法，其中函数和谓词编号没有限制。当前
`FormalSystem` 的宿主解码器却只接受 `FunctionSymbol` 与 `RelationSymbol`
给出的有限签名，因此二者不能直接等同。

本模块把实际有限签名编码成对象语言闭项，并定义精确公式条件：

* 行本身属于 `FormulaCodeₘ`；
* 每个 token 是逻辑符号、隶属符号、变量符号或当前有限签名中的非逻辑符号。

该条件只收紧符号表，不对变量名字施加规范偶奇编码限制。
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

/-! ## 宿主有限签名表 -/

/-- 函数符号在 Gödel token 层的实际头部编码。 -/
def fs_function_symbol_token
    (symbol : FunctionSymbol) : Nat :=
  match signature.funcDomain symbol with
  | [] =>
      Numbered.constant_token symbol.ctorIdx
  | _ :: tail =>
      Numbered.function_token tail.length symbol.ctorIdx

/-- 非隶属关系符号在 Gödel token 层的一般谓词头部编码。 -/
def fs_predicate_symbol_token
    (symbol : RelationSymbol) : Nat :=
  Numbered.predicate_token
    (signature.relDomain symbol).length.pred
    symbol.ctorIdx

/-- 一般谓词符号表；隶属符号由 `MembershipSymₘ` 单独处理。 -/
def fs_predicate_symbols : List RelationSymbol :=
  fs_relation_symbols.filter
    (fun symbol => symbol ≠ RelationSymbol.membership)

/-- 当前有限签名中全部非逻辑 token。 -/
def fs_nonlogical_symbol_tokens : List Nat :=
  fs_function_symbols.map fs_function_symbol_token ++
    fs_predicate_symbols.map fs_predicate_symbol_token

/-! ## 对象语言中的签名闭项 -/

/-- 一个函数符号在对象语言中的 singleton 符号码。 -/
def fs_function_symbol_code_term
    (symbol : FunctionSymbol) : SetTerm :=
  match signature.funcDomain symbol with
  | [] =>
      constant_symbol_code_term (numₘ(symbol.ctorIdx))
  | _ :: tail =>
      coded_function_symbol_code_term
        (numₘ(tail.length)) (numₘ(symbol.ctorIdx))

/-- 一个一般谓词符号在对象语言中的 singleton 符号码。 -/
def fs_predicate_symbol_code_term
    (symbol : RelationSymbol) : SetTerm :=
  coded_predicate_symbol_code_term
    (numₘ((signature.relDomain symbol).length.pred))
    (numₘ(symbol.ctorIdx))

/-- 当前有限签名中全部非逻辑 singleton 符号码。 -/
def fs_nonlogical_symbol_code_terms : List SetTerm :=
  fs_function_symbols.map fs_function_symbol_code_term ++
    fs_predicate_symbols.map fs_predicate_symbol_code_term

/-- 当前 `FormalSystem` 有限非逻辑签名的对象语言集合闭项。 -/
def fs_nonlogical_symbol_code_set_term : SetTerm :=
  finite_set_literal_term fs_nonlogical_symbol_code_terms

theorem fs_function_symbol_code_term_admissible
    (symbol : FunctionSymbol) :
    Term.Admissible
      (fs_function_symbol_code_term symbol)
      SetSort.set := by
  cases hDomain : signature.funcDomain symbol with
  | nil =>
      simpa [fs_function_symbol_code_term, hDomain] using
        constant_symbol_code_term_admissible
          (numₘ(symbol.ctorIdx))
          (finite_numeral_term_admissible symbol.ctorIdx)
  | cons head tail =>
      simpa [fs_function_symbol_code_term, hDomain] using
        coded_function_symbol_code_term_admissible
          (numₘ(tail.length)) (numₘ(symbol.ctorIdx))
          (finite_numeral_term_admissible tail.length)
          (finite_numeral_term_admissible symbol.ctorIdx)

theorem fs_predicate_symbol_code_term_admissible
    (symbol : RelationSymbol) :
    Term.Admissible
      (fs_predicate_symbol_code_term symbol)
      SetSort.set := by
  exact coded_predicate_symbol_code_term_admissible
    (numₘ((signature.relDomain symbol).length.pred))
    (numₘ(symbol.ctorIdx))
    (finite_numeral_term_admissible
      (signature.relDomain symbol).length.pred)
    (finite_numeral_term_admissible symbol.ctorIdx)

theorem fs_nonlogical_symbol_code_terms_admissible
    (code : SetTerm)
    (hCode : code ∈ fs_nonlogical_symbol_code_terms) :
    Term.Admissible code SetSort.set := by
  rcases List.mem_append.mp hCode with hFunction | hPredicate
  · rcases List.mem_map.mp hFunction with
      ⟨symbol, _, rfl⟩
    exact fs_function_symbol_code_term_admissible symbol
  · rcases List.mem_map.mp hPredicate with
      ⟨symbol, _, rfl⟩
    exact fs_predicate_symbol_code_term_admissible symbol

theorem fs_nonlogical_symbol_code_set_term_admissible :
    Term.Admissible
      fs_nonlogical_symbol_code_set_term
      SetSort.set := by
  exact finite_set_literal_term_admissible
    fs_nonlogical_symbol_code_terms
    fs_nonlogical_symbol_code_terms_admissible

@[simp]
theorem fs_nonlogical_symbol_code_set_term_freeSupport :
    Term.freeSupport
      fs_nonlogical_symbol_code_set_term = [] := by
  native_decide

/-! ## 精确公式条件 -/

/--
一个对象自然数 token 是变量 token。

变量名字只在 `S(token)` 内有界搜索；对标准编码 `3^(name+1)` 该界总能容纳
`name`，同时使反向检查保持原始递归可判定强度，不再依赖无限集合 `VarSymₘ`。

参数 `token` 已位于新引入的名字 binder 作用域内；普通闭项条件直接传原 token，
外层签名全称条件则显式传提升后的 `code · bₛ#1`。
-/
def fs_variable_token_condition
    (token : SetTerm) : SetFormula :=
  ∃ₘ[SetSort.set],
    ((bₛ#0 ∈ₘ Sₘ(token)) ∧ₘ
      (sym_codeₘ(token) ≐ₘ
        variable_symbol_code_term (bₛ#0)))

/--
token 条件的作用域显式核心。`token` 用于 binder 外的三个有限分支，
`variableToken` 是进入变量名字 binder 后的同一项。
-/
def fs_formula_token_condition_lifted
    (token variableToken : SetTerm) : SetFormula :=
  ((sym_codeₘ(token) ∈ₘ LogicSymₘ) ∨ₘ
    (sym_codeₘ(token) ∈ₘ MembershipSymₘ)) ∨ₘ
  (fs_variable_token_condition variableToken ∨ₘ
    (sym_codeₘ(token) ∈ₘ
      fs_nonlogical_symbol_code_set_term))

/--
一个 token 可出现在当前 `FormalSystem` 签名的公式中。

逻辑与隶属符号沿用公共编码集合；变量使用上面的有界构造检查；函数、常元及
一般谓词必须出现在有限签名闭项中。
-/
def fs_formula_token_condition
    (token : SetTerm) : SetFormula :=
  fs_formula_token_condition_lifted token token

/-- 显式 token 位置 binder 下的有限签名限制。 -/
def fs_formula_signature_condition_with_id
    (code : SetTerm) (tokenIndexId : FreeVarId) :
    SetFormula :=
  ∀ₘ[SetSort.set, tokenIndexId],
    ((x#tokenIndexId ∈ₘ domₘ(code)) ⟶ₘ
      fs_formula_token_condition
        (code ·ₘ x#tokenIndexId))

/--
规范 de Bruijn binder 下的有限签名限制。

验证器内核直接使用 bound variable，因而该条件沿自由变量代换严格自然；显式
自由变量版本只用于需要具名 eigenvariable 的 Hilbert 回放。
-/
def fs_formula_signature_condition
    (code : SetTerm) : SetFormula :=
  ∀ₘ[SetSort.set],
    ((bₛ#0 ∈ₘ domₘ(code)) ⟶ₘ
      fs_formula_token_condition_lifted
        (code ·ₘ bₛ#0)
        (code ·ₘ bₛ#1))

/-- 显式 token 位置 binder 下的完整有限签名公式条件。 -/
def fs_formula_code_condition_with_id
    (code : SetTerm) (tokenIndexId : FreeVarId) :
    SetFormula :=
  formula_codeₘ(code) ∧ₘ
    fs_formula_signature_condition_with_id
      code tokenIndexId

/-- 规范 de Bruijn binder 下的完整有限签名公式条件。 -/
def fs_formula_code_condition
    (code : SetTerm) : SetFormula :=
  formula_codeₘ(code) ∧ₘ
    fs_formula_signature_condition code

theorem fs_variable_token_condition_admissible
    (token : SetTerm)
    (hToken : Term.Admissible token SetSort.set) :
    Formula.Admissible
      (fs_variable_token_condition token) := by
  have hSymbolCode :
      Term.Admissible (sym_codeₘ(token)) SetSort.set :=
    singleton_symbol_code_term_admissible token hToken
  let nameId :=
    FreshVariable.fresh_id SetSort.set
      [token ≐ₘ token]
  have hName :
      Term.Admissible (x#nameId) SetSort.set :=
    set_variable_admissible nameId
  have hVariableBody :
      Formula.Admissible
        ((x#nameId ∈ₘ Sₘ(token)) ∧ₘ
          (sym_codeₘ(token) ≐ₘ
            variable_symbol_code_term (x#nameId))) :=
    Formula.Admissible.conj
      (membership_formula_admissible
        hName (successor_term_admissible token hToken))
      (Formula.Admissible.equal
        hSymbolCode
        (variable_symbol_code_term_admissible
          (x#nameId) hName))
  have hTokenClose :
      Term.closeFreeAt SetSort.set nameId 0 token =
        token :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set nameId 0 token hToken.2 (by
        dsimp [nameId]
        exact FreshVariable.fresh_term_not_mem_m
          SetSort.set token)
  have hZeroClose :
      Term.closeFreeAt SetSort.set nameId 0
          (numₘ(0)) =
        numₘ(0) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set nameId 0 (numₘ(0))
      (finite_numeral_term_admissible 0).2 (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hThreeClose :
      Term.closeFreeAt SetSort.set nameId 0
          (numₘ(3)) =
        numₘ(3) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set nameId 0 (numₘ(3))
      (finite_numeral_term_admissible 3).2 (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  simpa [fs_variable_token_condition,
    Formula.closeFreeAt, Term.closeFreeAt,
    set_variable, set_bound_variable,
    nameId, hTokenClose,
    hZeroClose, hThreeClose] using
    Formula.Admissible.exists_closeFreeAt
      SetSort.set nameId hVariableBody

theorem fs_formula_token_condition_admissible
    (token : SetTerm)
    (hToken : Term.Admissible token SetSort.set) :
    Formula.Admissible
      (fs_formula_token_condition token) := by
  have hSymbolCode :
      Term.Admissible (sym_codeₘ(token)) SetSort.set :=
    singleton_symbol_code_term_admissible token hToken
  exact Formula.Admissible.disj
    (Formula.Admissible.disj
      (membership_formula_admissible
        hSymbolCode logical_symbol_set_term_admissible)
      (membership_formula_admissible
        hSymbolCode membership_symbol_set_term_admissible))
    (Formula.Admissible.disj
      (fs_variable_token_condition_admissible
        token hToken)
      (membership_formula_admissible
        hSymbolCode
          fs_nonlogical_symbol_code_set_term_admissible))

theorem fs_formula_signature_condition_with_id_admissible
    (code : SetTerm) (tokenIndexId : FreeVarId)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (fs_formula_signature_condition_with_id
        code tokenIndexId) := by
  have hIndex :
      Term.Admissible (x#tokenIndexId) SetSort.set :=
    set_variable_admissible tokenIndexId
  have hDomain :
      Term.Admissible (domₘ(code)) SetSort.set :=
    domain_term_admissible code hCode
  have hValue :
      Term.Admissible
        (code ·ₘ x#tokenIndexId) SetSort.set :=
    function_application_term_admissible
      code (x#tokenIndexId) hCode hIndex
  have hPoint :
      Formula.Admissible
        ((x#tokenIndexId ∈ₘ domₘ(code)) ⟶ₘ
          fs_formula_token_condition
            (code ·ₘ x#tokenIndexId)) :=
    Formula.Admissible.imp
      (membership_formula_admissible hIndex hDomain)
      (fs_formula_token_condition_admissible
        (code ·ₘ x#tokenIndexId) hValue)
  exact Formula.Admissible.forall_closeFreeAt
    SetSort.set tokenIndexId hPoint

theorem fs_formula_signature_condition_with_id_freeSupport_subset
    (code : SetTerm) (tokenIndexId : FreeVarId)
    (freeVariable : FreeVariable signature)
    (hMember :
      freeVariable ∈
        Formula.freeSupport
          (fs_formula_signature_condition_with_id
            code tokenIndexId)) :
    freeVariable ∈ Term.freeSupport code := by
  simp [fs_formula_signature_condition_with_id,
    fs_formula_token_condition,
    fs_formula_token_condition_lifted,
    fs_variable_token_condition,
    Formula.freeSupport, Term.freeSupport,
    Term.freeSupportList,
    finite_numeral_term_freeSupport,
    Formula.mem_freeSupport_closeFreeAt_iff] at hMember
  grind

theorem fs_formula_signature_condition_freeSupport_subset
    (code : SetTerm)
    (freeVariable : FreeVariable signature)
    (hMember :
      freeVariable ∈
        Formula.freeSupport
          (fs_formula_signature_condition code)) :
    freeVariable ∈ Term.freeSupport code := by
  simp [fs_formula_signature_condition,
    fs_formula_token_condition_lifted,
    fs_variable_token_condition,
    Formula.freeSupport, Term.freeSupport,
    Term.freeSupportList,
    finite_numeral_term_freeSupport] at hMember
  grind

/--
具名 binder 对代码新鲜时，显式回放条件与规范 de Bruijn 条件是同一个公式。
-/
theorem fs_formula_signature_condition_with_id_eq
    (code : SetTerm) (tokenIndexId : FreeVarId)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      (SetSort.set, tokenIndexId) ∉
        Term.freeSupport code) :
    fs_formula_signature_condition_with_id
        code tokenIndexId =
      fs_formula_signature_condition code := by
  have hCodeClose (depth : Nat) :
      Term.closeFreeAt SetSort.set tokenIndexId depth code =
        code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set tokenIndexId depth code hCode.2 hFresh
  have hZeroClose (depth : Nat) :
      Term.closeFreeAt SetSort.set tokenIndexId depth
          (numₘ(0)) =
        numₘ(0) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set tokenIndexId depth (numₘ(0))
      (finite_numeral_term_admissible 0).2 (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hThreeClose (depth : Nat) :
      Term.closeFreeAt SetSort.set tokenIndexId depth
          (numₘ(3)) =
        numₘ(3) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set tokenIndexId depth (numₘ(3))
      (finite_numeral_term_admissible 3).2 (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hSymbolsClose :
      Term.closeFreeAt SetSort.set tokenIndexId 0
          fs_nonlogical_symbol_code_set_term =
        fs_nonlogical_symbol_code_set_term :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set tokenIndexId 0
      fs_nonlogical_symbol_code_set_term
      fs_nonlogical_symbol_code_set_term_admissible.2 (by
        rw [fs_nonlogical_symbol_code_set_term_freeSupport]
        exact List.not_mem_nil)
  simp [fs_formula_signature_condition_with_id,
    fs_formula_signature_condition,
    fs_formula_token_condition,
    fs_formula_token_condition_lifted,
    fs_variable_token_condition,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt,
    set_variable, set_bound_variable,
    hCodeClose, hZeroClose, hThreeClose,
    hSymbolsClose]

theorem fs_formula_signature_condition_admissible
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (fs_formula_signature_condition code) := by
  let tokenIndexId :=
    FreshVariable.fresh_id SetSort.set [code ≐ₘ code]
  have hFresh :
      (SetSort.set, tokenIndexId) ∉
        Term.freeSupport code := by
    simpa [tokenIndexId] using
      FreshVariable.fresh_term_not_mem_m
        SetSort.set code
  rw [← fs_formula_signature_condition_with_id_eq
    code tokenIndexId hCode hFresh]
  exact fs_formula_signature_condition_with_id_admissible
    code tokenIndexId hCode

/-- 规范签名条件沿任意自由变量项代换严格保持形状。 -/
theorem fs_formula_signature_condition_substitute
    (code replacement codeResult : SetTerm)
    (sourceId : FreeVarId)
    (hCode :
      Term.substituteFree SetSort.set sourceId replacement code =
        codeResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (fs_formula_signature_condition code) =
      fs_formula_signature_condition codeResult := by
  have hZeroFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (numₘ(0)) =
        numₘ(0) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set sourceId replacement (numₘ(0)) (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hThreeFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (numₘ(3)) =
        numₘ(3) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set sourceId replacement (numₘ(3)) (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hSymbolsFixed :
      Term.substituteFree SetSort.set sourceId replacement
          fs_nonlogical_symbol_code_set_term =
        fs_nonlogical_symbol_code_set_term :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set sourceId replacement
      fs_nonlogical_symbol_code_set_term (by
        rw [fs_nonlogical_symbol_code_set_term_freeSupport]
        exact List.not_mem_nil)
  simp [fs_formula_signature_condition,
    fs_formula_token_condition_lifted,
    fs_variable_token_condition,
    Formula.substituteFree, Term.substituteFree,
    hCode, hZeroFixed, hThreeFixed,
    hSymbolsFixed]

theorem fs_formula_code_condition_with_id_admissible
    (code : SetTerm) (tokenIndexId : FreeVarId)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (fs_formula_code_condition_with_id
        code tokenIndexId) := by
  exact Formula.Admissible.conj
    (is_formula_code_formula_admissible hCode)
    (fs_formula_signature_condition_with_id_admissible
      code tokenIndexId hCode)

theorem fs_formula_code_condition_admissible
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (fs_formula_code_condition code) := by
  exact Formula.Admissible.conj
    (is_formula_code_formula_admissible hCode)
    (fs_formula_signature_condition_admissible code hCode)

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
