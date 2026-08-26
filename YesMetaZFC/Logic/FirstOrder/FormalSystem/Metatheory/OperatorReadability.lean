import YesMetaZFC.Logic.FirstOrder.FormalSystem.LogicalRuleEncoding
/-!
# 编码运算符的元语法唯一可读性
本模块先固定编码证明的零层反演边界：集合论对象语言中的编码运算符仍是 Lean
原始语法树上的函数应用，因此函数标签和参数列可以无损恢复。这里的结论用于后续
定义公理实例化、重写和字符串分解；它们不把 raw 语法相等偷换成任意集合模型中的
值相等。模型内的素数幂反演和有限序列解析将在这些 no-confusion 定理之上继续证明。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
/-! ## 原始语法构造子的反演 -/
/-- 集合论项应用相等，当且仅当函数标签和完整参数列分别相等。 -/
theorem set_term_app_eq_iff
    {function function' : FunctionSymbol}
    {arguments arguments' : List SetTerm} : (Term.app function arguments : SetTerm) =
        Term.app function' arguments' ↔
      function = function' ∧ arguments = arguments' := by
  constructor
  · intro hEquality
    cases hEquality
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl
/-- 集合论关系原子相等，当且仅当关系标签和完整参数列分别相等。 -/
theorem set_formula_rel_eq_iff
    {relation relation' : RelationSymbol}
    {arguments arguments' : List SetTerm} : (Formula.rel relation arguments : SetFormula) =
        Formula.rel relation' arguments' ↔
      relation = relation' ∧ arguments = arguments' := by
  constructor
  · intro hEquality
    cases hEquality
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl
/-! ## 数字与符号标签 -/
/-- 由空集和后继组成的规范有限数字项在 raw 语法层保持单射。 -/
theorem finite_numeral_term_injective :
    Function.Injective (finite_numeral_term : Nat → SetTerm) := by
  intro left right hEquality
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => rfl
      | succ right => cases hEquality
  | succ left ih =>
      cases right with
      | zero => cases hEquality
      | succ right =>
          apply congrArg Nat.succ
          apply ih
          simpa [finite_numeral_term] using hEquality
/-- 八种逻辑符号使用的有限指数互不重复。 -/
theorem logical_symbol_exponent_injective :
    Function.Injective logical_symbol_exponent := by
  intro left right hEquality
  cases left <;> cases right <;>
    simp [logical_symbol_exponent] at hEquality ⊢
/-- 逻辑符号的单字符编码可唯一恢复符号种类。 -/
theorem logical_symbol_code_eq_iff
    {left right : LogicalSymbolKind} :
    logical_symbol_code_term left = logical_symbol_code_term right ↔
      left = right := by
  constructor
  · intro hEquality
    have hOuter := set_term_app_eq_iff.mp hEquality
    have hList := hOuter.2
    have hPair : (⟨numₘ(0), logical_symbol_number_term left⟩ₘ : SetTerm) =
          ⟨numₘ(0), logical_symbol_number_term right⟩ₘ := (List.cons.inj hList).1
    have hCoordinates := (set_term_app_eq_iff.mp hPair).2
    have hNumber :
        logical_symbol_number_term left =
          logical_symbol_number_term right := (List.cons.inj (List.cons.inj hCoordinates).2).1
    apply logical_symbol_exponent_injective
    apply finite_numeral_term_injective
    simpa [logical_symbol_number_term] using hNumber
  · rintro rfl
    rfl
/-! ## 参数化编码运算符的反演 -/
theorem variable_code_eq_iff {index index' : SetTerm} :
    var_codeₘ(index) = var_codeₘ(index') ↔ index = index' := by
  simp [variable_code_term]
theorem constant_code_eq_iff {index index' : SetTerm} :
    const_codeₘ(index) = const_codeₘ(index') ↔ index = index' := by
  simp [constant_code_term]
theorem coded_function_symbol_code_eq_iff
    {arity index arity' index' : SetTerm} :
    func_sym_codeₘ(arity, index) = func_sym_codeₘ(arity', index') ↔
      arity = arity' ∧ index = index' := by
  simp [coded_function_symbol_code_operator_term]
theorem coded_predicate_symbol_code_eq_iff
    {arity index arity' index' : SetTerm} :
    pred_sym_codeₘ(arity, index) = pred_sym_codeₘ(arity', index') ↔
      arity = arity' ∧ index = index' := by
  simp [coded_predicate_symbol_code_operator_term]
theorem equality_formula_code_eq_iff
    {left right left' right' : SetTerm} :
    eq_codeₘ(left, right) = eq_codeₘ(left', right') ↔
      left = left' ∧ right = right' := by
  simp [equality_formula_code_term]
theorem predicate_formula_code_eq_iff
    {arity index arguments arity' index' arguments' : SetTerm} :
    pred_codeₘ(arity, index, arguments) =
        pred_codeₘ(arity', index', arguments') ↔
      arity = arity' ∧ index = index' ∧ arguments = arguments' := by
  simp [predicate_formula_code_term]
theorem negation_formula_code_eq_iff {body body' : SetTerm} :
    neg_codeₘ(body) = neg_codeₘ(body') ↔ body = body' := by
  simp [negation_formula_code_term]
theorem implication_formula_code_eq_iff
    {left right left' right' : SetTerm} :
    imp_codeₘ(left, right) = imp_codeₘ(left', right') ↔
      left = left' ∧ right = right' := by
  simp [implication_formula_code_term]
theorem universal_formula_code_eq_iff
    {boundVariable body boundVariable' body' : SetTerm} :
    forall_codeₘ(boundVariable, body) =
        forall_codeₘ(boundVariable', body') ↔
      boundVariable = boundVariable' ∧ body = body' := by
  simp [universal_formula_code_term]
theorem code_substitution_term_eq_iff
    {source boundVariable replacement source' boundVariable' replacement' :
      SetTerm} :
    subst_codeₘ(source, boundVariable, replacement) =
        subst_codeₘ(source', boundVariable', replacement') ↔
      source = source' ∧ boundVariable = boundVariable' ∧
        replacement = replacement' := by
  simp [code_substitution_term]
/-! ## 编码字符串构造的同形反演 -/
theorem negation_formula_string_eq_iff {body body' : SetTerm} :
    negation_formula_string_term body =
        negation_formula_string_term body' ↔
      body = body' := by
  simp [negation_formula_string_term]
theorem implication_formula_string_eq_iff
    {left right left' right' : SetTerm} :
    implication_formula_string_term left right =
        implication_formula_string_term left' right' ↔
      left = left' ∧ right = right' := by
  simp [implication_formula_string_term]
theorem universal_formula_string_eq_iff
    {boundVariable body boundVariable' body' : SetTerm} :
    universal_formula_string_term boundVariable body =
        universal_formula_string_term boundVariable' body' ↔
      boundVariable = boundVariable' ∧ body = body' := by
  simp [universal_formula_string_term]
/-! ## 公式编码运算符的构造互斥 -/
theorem variable_code_ne_constant_code {index index' : SetTerm} :
    var_codeₘ(index) ≠ const_codeₘ(index') := by
  simp [variable_code_term, constant_code_term]
theorem equality_formula_code_ne_predicate_formula_code
    {left right arity index arguments : SetTerm} :
    eq_codeₘ(left, right) ≠ pred_codeₘ(arity, index, arguments) := by
  simp [equality_formula_code_term, predicate_formula_code_term]
theorem equality_formula_code_ne_negation_formula_code
    {left right body : SetTerm} :
    eq_codeₘ(left, right) ≠ neg_codeₘ(body) := by
  simp [equality_formula_code_term, negation_formula_code_term]
theorem equality_formula_code_ne_implication_formula_code
    {left right left' right' : SetTerm} :
    eq_codeₘ(left, right) ≠ imp_codeₘ(left', right') := by
  simp [equality_formula_code_term, implication_formula_code_term]
theorem equality_formula_code_ne_universal_formula_code
    {left right boundVariable body : SetTerm} :
    eq_codeₘ(left, right) ≠ forall_codeₘ(boundVariable, body) := by
  simp [equality_formula_code_term, universal_formula_code_term]
theorem predicate_formula_code_ne_negation_formula_code
    {arity index arguments body : SetTerm} :
    pred_codeₘ(arity, index, arguments) ≠ neg_codeₘ(body) := by
  simp [predicate_formula_code_term, negation_formula_code_term]
theorem predicate_formula_code_ne_implication_formula_code
    {arity index arguments left right : SetTerm} :
    pred_codeₘ(arity, index, arguments) ≠ imp_codeₘ(left, right) := by
  simp [predicate_formula_code_term, implication_formula_code_term]
theorem predicate_formula_code_ne_universal_formula_code
    {arity index arguments boundVariable body : SetTerm} :
    pred_codeₘ(arity, index, arguments) ≠
      forall_codeₘ(boundVariable, body) := by
  simp [predicate_formula_code_term, universal_formula_code_term]
theorem negation_formula_code_ne_implication_formula_code
    {body left right : SetTerm} :
    neg_codeₘ(body) ≠ imp_codeₘ(left, right) := by
  simp [negation_formula_code_term, implication_formula_code_term]
theorem negation_formula_code_ne_universal_formula_code
    {body boundVariable body' : SetTerm} :
    neg_codeₘ(body) ≠ forall_codeₘ(boundVariable, body') := by
  simp [negation_formula_code_term, universal_formula_code_term]
theorem implication_formula_code_ne_universal_formula_code
    {left right boundVariable body : SetTerm} :
    imp_codeₘ(left, right) ≠ forall_codeₘ(boundVariable, body) := by
  simp [implication_formula_code_term, universal_formula_code_term]
/-! ## 有限序列编码运算符的反演 -/
theorem finite_sequence_concatenation_term_eq_iff
    {left right left' right' : SetTerm} :
    left ⌢ₘ right = left' ⌢ₘ right' ↔
      left = left' ∧ right = right' := by
  simp [finite_sequence_concatenation_term]
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
