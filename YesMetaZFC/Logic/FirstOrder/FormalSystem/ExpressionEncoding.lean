import YesMetaZFC.Logic.FirstOrder.FormalSystem.LanguageEncoding
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Separation
/-!
# 一阶表达式编码
本模块在项与原子公式编码之上建立完整一阶表达式的构造设施：
* 原子公式集合与公式编码的最小闭包；
* 等式、谓词应用、否定、蕴含和全称量化编码运算；
* 变量、常元、函数符号与谓词符号的参数化编码运算；
* 编码级替换、变量收集与自由出现位置；
* 量词出现、受约束出现和自由出现谓词。
文献中的 `cBDS`、`BDS`、`XnDn`、`WCMT`、`FD`、`YHn`、`QYH`、
`BYBM`、`CYBM`、`HSBM`、`WCBM`、`TiHn`、`BYJH`、`LCCX`、
`YSCX`、`ZYCX` 与 `ZYWZ` 仅在注释中保留为检索索引。
公式编码不复刻文献的自然数逐层生成，而采用最小闭包规格。替换与出现性也直接
建立在有限序列、子串位置和量词作用域上，避免把大量编号辅助式固化到公共接口。
本模块只建立定义、理论链和 proof-carrying 良构性边界；唯一可读性、结构归纳、
替换引理与自由变量演算留给后续证明模块。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
/-! ## 公式编码构造 -/
/-- 否定公式的括号化编码。 -/
abbrev negation_formula_string_term (body : SetTerm) :
    SetTerm := (((left_parenthesis_symbol_code_term ⌢ₘ
      logical_symbol_code_term .negation) ⌢ₘ
    body) ⌢ₘ
  right_parenthesis_symbol_code_term)
/-- 蕴含公式的括号化编码。 -/
abbrev implication_formula_string_term (left right : SetTerm) :
    SetTerm := ((((left_parenthesis_symbol_code_term ⌢ₘ
        left) ⌢ₘ
      logical_symbol_code_term .implication) ⌢ₘ
    right) ⌢ₘ
  right_parenthesis_symbol_code_term)
/-- 全称量化公式的括号化编码。 -/
abbrev universal_formula_string_term (boundVariable body : SetTerm) :
    SetTerm := ((((left_parenthesis_symbol_code_term ⌢ₘ
        logical_symbol_code_term .universal) ⌢ₘ
      boundVariable) ⌢ₘ
    body) ⌢ₘ
  right_parenthesis_symbol_code_term)
/--
存在量词按文献 11.5 作为 Hilbert 核语言中的缩写编码：
`∃v φ` 即 `¬∀v¬φ`。
这里不引入新的对象函数符号；这样 `FormulaCodeₘ` 仍只需对
`¬ / → / ∀` 三个核心构造封闭。
-/
abbrev existential_formula_code_term (boundVariable body : SetTerm) :
    SetTerm :=
  neg_codeₘ(forall_codeₘ(
    boundVariable, neg_codeₘ(body)))
/--
合取按文献 11.6 作为 Hilbert 核语言中的缩写编码：
`φ ∧ ψ` 即 `¬(φ → ¬ψ)`。
它与 `Formula.hilbert_conj` 使用同一展开式，因而元语言公式、标准 token 串和对象
公式码可共用一条递归路线。
-/
abbrev conjunction_formula_code_term (left right : SetTerm) :
    SetTerm :=
  neg_codeₘ(imp_codeₘ(
    left, neg_codeₘ(right)))
/-! ## 参数化符号编码运算 -/
/-- 变量符号编码运算的开放定义实例；文献索引为 `BYBM`。 -/
def variable_code_definition_instance (index candidate : SetTerm) :
    SetFormula := (candidate ≐ₘ var_codeₘ(index)) ↔ₘ (candidate ≐ₘ variable_symbol_code_term index)
/-- 常元符号编码运算的开放定义实例；文献索引为 `CYBM`。 -/
def constant_code_definition_instance (index candidate : SetTerm) :
    SetFormula := (candidate ≐ₘ const_codeₘ(index)) ↔ₘ (candidate ≐ₘ constant_symbol_code_term index)
/-- 函数符号编码运算的开放定义实例；文献索引为 `HSBM`、`HSBM₀`。 -/
def coded_function_symbol_code_operator_definition_instance (arityPredecessor symbolIndex candidate : SetTerm) :
    SetFormula := (candidate ≐ₘ
      func_sym_codeₘ(arityPredecessor, symbolIndex)) ↔ₘ (candidate ≐ₘ
      coded_function_symbol_code_term
        arityPredecessor symbolIndex)
/-- 谓词符号编码运算的开放定义实例；文献索引为 `WCBM`、`WCBM₀`。 -/
def coded_predicate_symbol_code_operator_definition_instance (arityPredecessor symbolIndex candidate : SetTerm) :
    SetFormula := (candidate ≐ₘ
      pred_sym_codeₘ(arityPredecessor, symbolIndex)) ↔ₘ (candidate ≐ₘ
      coded_predicate_symbol_code_term
        arityPredecessor symbolIndex)
/-- 参数化符号编码运算的定义公理。 -/
def symbol_code_operator_definition_axiom :
    SetFormula := (∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      variable_code_definition_instance (x#0) (x#1)) ∧ₘ ((∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      constant_code_definition_instance (x#0) (x#1)) ∧ₘ ((∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        coded_function_symbol_code_operator_definition_instance (x#0) (x#1) (x#2)) ∧ₘ (∀ₘ[SetSort.set, 0],
      ∀ₘ[SetSort.set, 1],
        ∀ₘ[SetSort.set, 2],
          coded_predicate_symbol_code_operator_definition_instance (x#0) (x#1) (x#2))))
/-! ## 公式构造运算 -/
/-- 等式公式编码运算的开放定义实例；文献索引为 `XnDn`。 -/
def equality_formula_code_definition_instance (left right candidate : SetTerm) :
    SetFormula := ((term_codeₘ(left) ∧ₘ term_codeₘ(right)) ⟶ₘ (((candidate ≐ₘ eq_codeₘ(left, right)) ↔ₘ (candidate ≐ₘ
        equality_atomic_formula_code_term left right))))
/-- 谓词应用编码运算的开放定义实例；文献索引为 `WCMT`。 -/
def predicate_formula_code_definition_instance (arityPredecessor symbolIndex arguments candidate : SetTerm) :
    SetFormula := (((arityPredecessor ∈ₘ ωₘ) ∧ₘ ((symbolIndex ∈ₘ ωₘ) ∧ₘ ((arguments ∈ₘ TermSeqₘ) ∧ₘ (domₘ(arguments) ≐ₘ
            Sₘ(arityPredecessor))))) ⟶ₘ (((candidate ≐ₘ
        pred_codeₘ(
          arityPredecessor, symbolIndex, arguments)) ↔ₘ (candidate ≐ₘ
        predicate_application_code_term
          arityPredecessor symbolIndex arguments))))
/-- 否定编码运算的开放定义实例；文献索引为 `FD`。 -/
def negation_formula_code_definition_instance (body candidate : SetTerm) :
    SetFormula := (candidate ≐ₘ neg_codeₘ(body)) ↔ₘ (candidate ≐ₘ negation_formula_string_term body)
/-- 蕴含编码运算的开放定义实例；文献索引为 `YHn`。 -/
def implication_formula_code_definition_instance (left right candidate : SetTerm) :
    SetFormula := (candidate ≐ₘ imp_codeₘ(left, right)) ↔ₘ (candidate ≐ₘ
      implication_formula_string_term left right)
/-- 全称量化编码运算的开放定义实例；文献索引为 `QYH`。 -/
def universal_formula_code_definition_instance (boundVariable body candidate : SetTerm) :
    SetFormula := (candidate ≐ₘ
      forall_codeₘ(boundVariable, body)) ↔ₘ (candidate ≐ₘ
      universal_formula_string_term boundVariable body)
/-- 五种公式构造运算的定义公理。 -/
def formula_constructor_definition_axiom :
    SetFormula := (∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        equality_formula_code_definition_instance (x#0) (x#1) (x#2)) ∧ₘ ((∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          predicate_formula_code_definition_instance (x#0) (x#1) (x#2) (x#3)) ∧ₘ ((∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      negation_formula_code_definition_instance (x#0) (x#1)) ∧ₘ ((∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        implication_formula_code_definition_instance (x#0) (x#1) (x#2)) ∧ₘ (∀ₘ[SetSort.set, 0],
      ∀ₘ[SetSort.set, 1],
        ∀ₘ[SetSort.set, 2],
          universal_formula_code_definition_instance (x#0) (x#1) (x#2)))))
/-! ## 原子公式集合与公式最小闭包 -/
/-- 原子公式集合的定义公理；文献索引为 `cBDS`、`Ξ₁₁₁`。 -/
def atomic_formula_code_set_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ AtomicCodeₘ) ↔ₘ
      atomic_formula_codeₘ(x#0))
/-- `candidate` 包含原子公式，并对三种复合公式构造封闭。 -/
def formula_code_closed_condition (candidate : SetTerm) :
    SetFormula := (AtomicCodeₘ ⊆ₘ candidate) ∧ₘ ((∀ₘ[SetSort.set, 300], ((x#300 ∈ₘ candidate) ⟶ₘ (neg_codeₘ(x#300) ∈ₘ candidate))) ∧ₘ ((∀ₘ[SetSort.set, 301],
        ∀ₘ[SetSort.set, 302], (((x#301 ∈ₘ candidate) ∧ₘ (x#302 ∈ₘ candidate)) ⟶ₘ (imp_codeₘ(x#301, x#302) ∈ₘ
              candidate))) ∧ₘ (∀ₘ[SetSort.set, 303],
          ∀ₘ[SetSort.set, 304], ((((x#303 ∈ₘ VarSymₘ) ∧ₘ (x#304 ∈ₘ candidate))) ⟶ₘ (forall_codeₘ(x#303, x#304) ∈ₘ
                candidate)))))
/--
`code` 由原子公式一步生成，或由 `candidate` 中已有代码应用一次复合公式构造生成。
这是完整公式码最小闭包的生成算子；把它独立命名后，成员反演与后续 checked parser
可以共享同一个对象层关系。
-/
def formula_code_generation_condition (candidate code : SetTerm) :
    SetFormula :=
  (code ∈ₘ AtomicCodeₘ) ∨ₘ ((∃ₘ[SetSort.set, 306],
      ((x#306 ∈ₘ candidate) ∧ₘ (code ≐ₘ neg_codeₘ(x#306)))) ∨ₘ
    ((∃ₘ[SetSort.set, 307],
      ∃ₘ[SetSort.set, 308], (((x#307 ∈ₘ candidate) ∧ₘ
          (x#308 ∈ₘ candidate)) ∧ₘ
        (code ≐ₘ imp_codeₘ(x#307, x#308)))) ∨ₘ
      (∃ₘ[SetSort.set, 309],
        ∃ₘ[SetSort.set, 310], ((((x#309 ∈ₘ VarSymₘ) ∧ₘ
            (x#310 ∈ₘ candidate)) ∧ₘ
          (code ≐ₘ forall_codeₘ(x#309, x#310)))))))
/--
从完整公式码集合中筛出可由一步公式构造生成的成员。该谓词只服务于最小闭包的
标准消去证明，不把 generatedness 本身作为定义公理。
-/
def formula_code_generation_predicate :
    SetPredicate where
  body :=
    Formula.closeFreeAt SetSort.set 311 0
      (formula_code_generation_condition FormulaCodeₘ (x#311))
  admissible_at := by
    prove_admissible_at
/--
公式码反演所需的唯一分离实例。它在 `FormulaCodeₘ` 内筛选一步生成成员，使最小性
可以应用到一个实际对象集合；不直接断言筛选结果等于 `FormulaCodeₘ`。
-/
def formula_code_generation_separation_axiom :
    SetFormula :=
  formula_code_generation_predicate.separation_axiom
/--
`candidate` 是完整公式编码组成的最小闭集，并且其中每个编码都是代码字符串。
生成方程必须从本规格的闭包与最小性推出，不能作为额外定义公理加入。
-/
def formula_code_set_spec (candidate : SetTerm) :
    SetFormula :=
  formula_code_closed_condition candidate ∧ₘ ((candidate ⊆ₘ CodeStrₘ) ∧ₘ
    (∀ₘ[SetSort.set, 305], (formula_code_closed_condition (x#305) ⟶ₘ
      (candidate ⊆ₘ (x#305)))))
/-- 公式编码集合定义公理；文献索引为 `BDS`、`Ξ₁₁₂`。 -/
def formula_code_set_definition_axiom :
    SetFormula :=
  formula_code_set_spec FormulaCodeₘ
/-- “是公式编码”谓词的开放定义实例。 -/
def is_formula_code_definition_instance (code : SetTerm) :
    SetFormula :=
  formula_codeₘ(code) ↔ₘ (code ∈ₘ FormulaCodeₘ)
/-- “是公式编码”谓词定义公理。 -/
def is_formula_code_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_formula_code_definition_instance (x#0)
/-- 原子集合、公式闭包和公式谓词的联合定义公理。 -/
def formula_code_definition_axiom :
    SetFormula :=
  atomic_formula_code_set_definition_axiom ∧ₘ (formula_code_set_definition_axiom ∧ₘ
      is_formula_code_definition_axiom)
/-! ## 编码级替换与变量收集 -/
/-- 替换分片在一个源位置上的点态条件。 -/
def substitution_piece_condition (source boundVariable replacement pieces index : SetTerm) :
    SetFormula := (index ∈ₘ domₘ(source)) ⟶ₘ ((((source ·ₘ index) ≐ₘ (boundVariable ·ₘ numₘ(0))) ∧ₘ ((pieces ·ₘ index) ≐ₘ replacement)) ∨ₘ
      (((source ·ₘ index) ≠ₘ (boundVariable ·ₘ numₘ(0))) ∧ₘ ((pieces ·ₘ index) ≐ₘ
          sym_codeₘ(source ·ₘ index))))
/-- `candidate` 是把 `source` 中指定变量符号替换为项编码后的字符串。 -/
def code_substitution_spec (source boundVariable replacement candidate : SetTerm) :
    SetFormula := (candidate ∈ₘ CodeStrₘ) ∧ₘ (∃ₘ[SetSort.set, 310], (((x#310 ∈ₘ seq_spaceₘ(CodeStrₘ)) ∧ₘ (domₘ(x#310) ≐ₘ domₘ(source))) ∧ₘ
        ((∀ₘ[SetSort.set, 311],
          substitution_piece_condition
            source boundVariable replacement (x#310) (x#311)) ∧ₘ (candidate ≐ₘ flattenₘ(x#310)))))
/-- 编码级替换函数的开放定义实例；文献索引为 `TiHn`、`Ξ₁₂₄`。 -/
def code_substitution_definition_instance (source boundVariable replacement candidate : SetTerm) :
    SetFormula := ((((source ∈ₘ (TermCodeₘ ∪ₘ FormulaCodeₘ)) ∧ₘ (boundVariable ∈ₘ VarSymₘ)) ∧ₘ
      term_codeₘ(replacement)) ⟶ₘ (((candidate ≐ₘ
        subst_codeₘ(
          source, boundVariable, replacement)) ↔ₘ
      code_substitution_spec
        source boundVariable replacement candidate)))
/-- 编码级替换函数定义公理。 -/
def code_substitution_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          code_substitution_definition_instance (x#0) (x#1) (x#2) (x#3)
/-- 变量符号在编码字符串某个位置出现。 -/
def variable_symbol_occurs_condition (boundVariable source : SetTerm) :
    SetFormula := (boundVariable ∈ₘ VarSymₘ) ∧ₘ (∃ₘ[SetSort.set, 312], ((x#312 ∈ₘ domₘ(source)) ∧ₘ ((source ·ₘ x#312) ≐ₘ (boundVariable ·ₘ numₘ(0)))))
/-- `candidate` 精确收集编码字符串中出现的变量符号。 -/
def variable_collection_spec (source candidate : SetTerm) :
    SetFormula := (candidate ⊆ₘ VarSymₘ) ∧ₘ (∀ₘ[SetSort.set, 313], ((x#313 ∈ₘ VarSymₘ) ⟶ₘ (((x#313 ∈ₘ candidate) ↔ₘ
          variable_symbol_occurs_condition (x#313) source))))
/-- 变量收集函数的开放定义实例；文献索引为 `BYJH`、`Ξ₁₂₅`。 -/
def variable_collection_definition_instance (source candidate : SetTerm) :
    SetFormula := (source ∈ₘ (TermCodeₘ ∪ₘ FormulaCodeₘ)) ⟶ₘ (((candidate ≐ₘ varsₘ(source)) ↔ₘ
      variable_collection_spec source candidate))
/-- 变量收集函数定义公理。 -/
def variable_collection_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      variable_collection_definition_instance (x#0) (x#1)
/-- 替换与变量收集的联合定义公理。 -/
def substitution_variable_definition_axiom :
    SetFormula :=
  code_substitution_definition_axiom ∧ₘ
    variable_collection_definition_axiom
/-! ## 子串、量词作用域与出现性 -/
/--
`segment` 从 `whole` 的自然数位置 `start` 开始逐点出现。
偏移量放在对象加法的左参数。自然加法按左参数递归，因此固定语法前缀
`0, 1, 2, ...` 可以直接按定义展开，同时仍与通常的 `start + offset`
表示同一个自然数位置。
-/
def code_substring_at_condition (whole segment start : SetTerm) :
    SetFormula := (start ∈ₘ ωₘ) ∧ₘ (∀ₘ[SetSort.set, 320], ((x#320 ∈ₘ domₘ(segment)) ⟶ₘ ((((x#320 +ₘ start) ∈ₘ domₘ(whole)) ∧ₘ ((whole ·ₘ (x#320 +ₘ start)) ≐ₘ
            (segment ·ₘ x#320))))))
/-- 指定变量符号的标签出现在公式编码的给定位置。 -/
def variable_occurs_at_position_condition (boundVariable formula position : SetTerm) :
    SetFormula := (position ∈ₘ domₘ(formula)) ∧ₘ ((formula ·ₘ position) ≐ₘ (boundVariable ·ₘ numₘ(0)))
/-- 从 `start` 开始出现一个以指定变量约束 `body` 的全称量词子公式。 -/
def universal_binder_at_condition (boundVariable formula body start : SetTerm) :
    SetFormula := ((boundVariable ∈ₘ VarSymₘ) ∧ₘ (formula_codeₘ(body) ∧ₘ (body ∈ₘ CodeStrₘ))) ∧ₘ
    code_substring_at_condition
      formula (forall_codeₘ(boundVariable, body))
      start
/-- 指定变量的量词在公式编码中出现。 -/
def quantifier_occurs_condition (boundVariable formula : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 321],
    ∃ₘ[SetSort.set, 322],
      universal_binder_at_condition
        boundVariable formula (x#321) (x#322)
/-- `position` 是某个指定变量量词中的变量声明位置。 -/
def binder_declaration_position_condition (boundVariable formula position : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 323],
    ∃ₘ[SetSort.set, 324], (universal_binder_at_condition
        boundVariable formula (x#323) (x#324) ∧ₘ (position ≐ₘ (numₘ(2) +ₘ (x#324))))
/-- `position` 位于某个指定变量量词的公式体中。 -/
def quantifier_body_position_condition (boundVariable formula position : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 325],
    ∃ₘ[SetSort.set, 326],
      ∃ₘ[SetSort.set, 327], ((universal_binder_at_condition
            boundVariable formula (x#325) (x#326) ∧ₘ ((x#327) ∈ₘ domₘ(x#325))) ∧ₘ (position ≐ₘ ((x#327) +ₘ (numₘ(3) +ₘ (x#326)))))
/-- 指定变量在给定位置受某个同名全称量词约束。 -/
def bound_occurrence_position_condition (boundVariable formula position : SetTerm) :
    SetFormula :=
  variable_occurs_at_position_condition
      boundVariable formula position ∧ₘ (binder_declaration_position_condition
        boundVariable formula position ∨ₘ
      quantifier_body_position_condition
        boundVariable formula position)
/-- 指定变量在给定位置自由出现。 -/
def free_occurrence_position_condition (boundVariable formula position : SetTerm) :
    SetFormula :=
  variable_occurs_at_position_condition
      boundVariable formula position ∧ₘ
    ¬ₘ (bound_occurrence_position_condition
      boundVariable formula position)
/-- “量词出现”谓词的定义公理；文献索引为 `LCCX`、`Ξ₁₂₆`。 -/
def quantifier_occurs_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1], ((quantifier_occursₘ(x#0, x#1)) ↔ₘ
        quantifier_occurs_condition (x#0) (x#1))
/-- “受约束出现”谓词的定义公理；文献索引为 `YSCX`、`Ξ₁₂₆a`。 -/
def bound_occurrence_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1], ((bound_occursₘ(x#0, x#1)) ↔ₘ (∃ₘ[SetSort.set, 328],
          bound_occurrence_position_condition (x#0) (x#1) (x#328)))
/-- “自由出现”谓词的定义公理；文献索引为 `ZYCX`、`Ξ₁₂₈`。 -/
def free_occurrence_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1], ((free_occursₘ(x#0, x#1)) ↔ₘ (∃ₘ[SetSort.set, 329],
          free_occurrence_position_condition (x#0) (x#1) (x#329)))
/-- `candidate` 精确收集指定变量在公式中自由出现的位置。 -/
def free_occurrence_positions_spec (boundVariable formula candidate : SetTerm) :
    SetFormula := (candidate ⊆ₘ domₘ(formula)) ∧ₘ (∀ₘ[SetSort.set, 330], ((x#330 ∈ₘ domₘ(formula)) ⟶ₘ (((x#330 ∈ₘ candidate) ↔ₘ
          free_occurrence_position_condition
            boundVariable formula (x#330)))))
/-- 自由出现位置集合函数的开放定义实例；文献索引为 `ZYWZ`、`Ξ₁₂₉`。 -/
def free_occurrence_positions_definition_instance (boundVariable formula candidate : SetTerm) :
    SetFormula := (((boundVariable ∈ₘ VarSymₘ) ∧ₘ
      formula_codeₘ(formula)) ⟶ₘ (((candidate ≐ₘ
        free_posₘ(boundVariable, formula)) ↔ₘ
      free_occurrence_positions_spec
        boundVariable formula candidate)))
/-- 自由出现位置集合函数定义公理。 -/
def free_occurrence_positions_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        free_occurrence_positions_definition_instance (x#0) (x#1) (x#2)
/-- 出现性谓词与自由位置集合的联合定义公理。 -/
def occurrence_definition_axiom :
    SetFormula :=
  quantifier_occurs_definition_axiom ∧ₘ (bound_occurrence_definition_axiom ∧ₘ (free_occurrence_definition_axiom ∧ₘ
        free_occurrence_positions_definition_axiom))
/-! ## 理论组合 -/
/-- 加入参数化符号编码运算后的理论。 -/
def symbol_code_operator_theory :
    SetTheory :=
  Theory.insert
    symbol_code_operator_definition_axiom
    formal_language_encoding_theory
/-- 加入五种公式构造运算后的理论。 -/
def formula_constructor_theory :
    SetTheory :=
  Theory.insert
    formula_constructor_definition_axiom
    symbol_code_operator_theory
/-- 加入原子公式集合与公式最小闭包后的理论。 -/
def formula_code_theory :
    SetTheory :=
  Theory.insert
    formula_code_definition_axiom
    (Theory.insert
      formula_code_generation_separation_axiom
      formula_constructor_theory)
/-- 加入编码替换与变量收集后的理论。 -/
def substitution_variable_theory :
    SetTheory :=
  Theory.insert
    substitution_variable_definition_axiom
    formula_code_theory
/-- 加入量词、约束与自由出现定义后的理论。 -/
def occurrence_theory :
    SetTheory :=
  Theory.insert
    occurrence_definition_axiom
    substitution_variable_theory
/-- 一阶表达式编码层的稳定理论入口。 -/
def expression_encoding_theory :
    SetTheory :=
  occurrence_theory
/-! ## proof-carrying 项边界 -/
theorem negation_formula_string_term_admissible (body : SetTerm) (hBody : Term.Admissible body SetSort.set) :
    Term.Admissible (negation_formula_string_term body)
      SetSort.set := by
  have hLeft :=
    logical_symbol_code_term_admissible
      .leftParenthesis
  have hNegation :=
    logical_symbol_code_term_admissible
      .negation
  have hRight :=
    logical_symbol_code_term_admissible
      .rightParenthesis
  exact finite_sequence_concatenation_term_admissible (((left_parenthesis_symbol_code_term ⌢ₘ
        logical_symbol_code_term .negation) ⌢ₘ body))
    right_parenthesis_symbol_code_term (finite_sequence_concatenation_term_admissible (left_parenthesis_symbol_code_term ⌢ₘ
        logical_symbol_code_term .negation)
      body (finite_sequence_concatenation_term_admissible
        left_parenthesis_symbol_code_term (logical_symbol_code_term .negation)
        hLeft hNegation)
      hBody)
    hRight
theorem implication_formula_string_term_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible (implication_formula_string_term left right)
      SetSort.set := by
  have hOpen :=
    logical_symbol_code_term_admissible
      .leftParenthesis
  have hImplication :=
    logical_symbol_code_term_admissible
      .implication
  have hClose :=
    logical_symbol_code_term_admissible
      .rightParenthesis
  exact finite_sequence_concatenation_term_admissible ((((left_parenthesis_symbol_code_term ⌢ₘ left) ⌢ₘ
        logical_symbol_code_term .implication) ⌢ₘ right))
    right_parenthesis_symbol_code_term (finite_sequence_concatenation_term_admissible (((left_parenthesis_symbol_code_term ⌢ₘ left) ⌢ₘ
        logical_symbol_code_term .implication))
      right (finite_sequence_concatenation_term_admissible (left_parenthesis_symbol_code_term ⌢ₘ left) (logical_symbol_code_term .implication)
        (finite_sequence_concatenation_term_admissible
          left_parenthesis_symbol_code_term
          left hOpen hLeft)
        hImplication)
      hRight)
    hClose
theorem universal_formula_string_term_admissible (boundVariable body : SetTerm) (hVariable :
      Term.Admissible boundVariable SetSort.set) (hBody :
      Term.Admissible body SetSort.set) :
    Term.Admissible (universal_formula_string_term
        boundVariable body)
      SetSort.set := by
  have hOpen :=
    logical_symbol_code_term_admissible
      .leftParenthesis
  have hUniversal :=
    logical_symbol_code_term_admissible
      .universal
  have hClose :=
    logical_symbol_code_term_admissible
      .rightParenthesis
  exact finite_sequence_concatenation_term_admissible ((((left_parenthesis_symbol_code_term ⌢ₘ
        logical_symbol_code_term .universal) ⌢ₘ
      boundVariable) ⌢ₘ body))
    right_parenthesis_symbol_code_term (finite_sequence_concatenation_term_admissible (((left_parenthesis_symbol_code_term ⌢ₘ
          logical_symbol_code_term .universal) ⌢ₘ
        boundVariable))
      body (finite_sequence_concatenation_term_admissible (left_parenthesis_symbol_code_term ⌢ₘ
          logical_symbol_code_term .universal)
        boundVariable (finite_sequence_concatenation_term_admissible
          left_parenthesis_symbol_code_term (logical_symbol_code_term .universal)
          hOpen hUniversal)
        hVariable)
      hBody)
    hClose
theorem atomic_formula_code_set_term_admissible :
    Term.Admissible AtomicCodeₘ SetSort.set := by
  simpa using
    set_function_application_admissible
      .atomicFormulaCodeSet []
      (by rfl) (by rfl)
theorem formula_code_set_term_admissible :
    Term.Admissible FormulaCodeₘ SetSort.set := by
  simpa using
    set_function_application_admissible
      .formulaCodeSet []
      (by rfl) (by rfl)
theorem equality_formula_code_term_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible (eq_codeₘ(left, right))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .equalityFormulaCode [⟨left, by assumption⟩, ⟨right, by assumption⟩]
      (by rfl) (by rfl)
theorem predicate_formula_code_term_admissible (arityPredecessor symbolIndex arguments : SetTerm) (hArity :
      Term.Admissible arityPredecessor SetSort.set) (hIndex :
      Term.Admissible symbolIndex SetSort.set) (hArguments :
      Term.Admissible arguments SetSort.set) :
    Term.Admissible (pred_codeₘ(
        arityPredecessor, symbolIndex, arguments))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .predicateFormulaCode [⟨arityPredecessor, by assumption⟩, ⟨symbolIndex, by assumption⟩, ⟨arguments, by assumption⟩]
      (by rfl) (by rfl)
theorem negation_formula_code_term_admissible (body : SetTerm) (hBody : Term.Admissible body SetSort.set) :
    Term.Admissible (neg_codeₘ(body))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .negationFormulaCode [⟨body, by assumption⟩]
      (by rfl) (by rfl)
theorem implication_formula_code_term_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible (imp_codeₘ(left, right))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .implicationFormulaCode [⟨left, by assumption⟩, ⟨right, by assumption⟩]
      (by rfl) (by rfl)
theorem universal_formula_code_term_admissible (boundVariable body : SetTerm) (hVariable :
      Term.Admissible boundVariable SetSort.set) (hBody :
      Term.Admissible body SetSort.set) :
    Term.Admissible (forall_codeₘ(boundVariable, body))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .universalFormulaCode [⟨boundVariable, by assumption⟩, ⟨body, by assumption⟩]
      (by rfl) (by rfl)
/-- 存在量词缩写编码的公共良构性边界。 -/
theorem existential_formula_code_term_admissible (boundVariable body : SetTerm) (hVariable :
      Term.Admissible boundVariable SetSort.set) (hBody :
      Term.Admissible body SetSort.set) :
    Term.Admissible (existential_formula_code_term boundVariable body)
      SetSort.set :=
  negation_formula_code_term_admissible (forall_codeₘ(boundVariable, neg_codeₘ(body))) (universal_formula_code_term_admissible
      boundVariable (neg_codeₘ(body))
      hVariable (negation_formula_code_term_admissible body hBody))
/-- 合取缩写编码的公共良构性边界。 -/
theorem conjunction_formula_code_term_admissible (left right : SetTerm) (hLeft :
      Term.Admissible left SetSort.set) (hRight :
      Term.Admissible right SetSort.set) :
    Term.Admissible (conjunction_formula_code_term left right)
      SetSort.set :=
  negation_formula_code_term_admissible (imp_codeₘ(left, neg_codeₘ(right))) (implication_formula_code_term_admissible
      left (neg_codeₘ(right))
      hLeft (negation_formula_code_term_admissible right hRight))
theorem variable_code_term_admissible (index : SetTerm) (hIndex : Term.Admissible index SetSort.set) :
    Term.Admissible (var_codeₘ(index))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .variableCode [⟨index, by assumption⟩]
      (by rfl) (by rfl)
theorem constant_code_term_admissible (index : SetTerm) (hIndex : Term.Admissible index SetSort.set) :
    Term.Admissible (const_codeₘ(index))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .constantCode [⟨index, by assumption⟩]
      (by rfl) (by rfl)
theorem coded_function_symbol_code_operator_term_admissible (arityPredecessor symbolIndex : SetTerm) (hArity :
      Term.Admissible arityPredecessor SetSort.set) (hIndex :
      Term.Admissible symbolIndex SetSort.set) :
    Term.Admissible (func_sym_codeₘ(
        arityPredecessor, symbolIndex))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .codedFunctionSymbolCode [⟨arityPredecessor, by assumption⟩, ⟨symbolIndex, by assumption⟩]
      (by rfl) (by rfl)
theorem coded_predicate_symbol_code_operator_term_admissible (arityPredecessor symbolIndex : SetTerm) (hArity :
      Term.Admissible arityPredecessor SetSort.set) (hIndex :
      Term.Admissible symbolIndex SetSort.set) :
    Term.Admissible (pred_sym_codeₘ(
        arityPredecessor, symbolIndex))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .codedPredicateSymbolCode [⟨arityPredecessor, by assumption⟩, ⟨symbolIndex, by assumption⟩]
      (by rfl) (by rfl)
theorem code_substitution_term_admissible (source boundVariable replacement : SetTerm) (hSource : Term.Admissible source SetSort.set) (hVariable :
      Term.Admissible boundVariable SetSort.set) (hReplacement :
      Term.Admissible replacement SetSort.set) :
    Term.Admissible (subst_codeₘ(
        source, boundVariable, replacement))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .codeSubstitution [⟨source, by assumption⟩, ⟨boundVariable, by assumption⟩, ⟨replacement, by assumption⟩]
      (by rfl) (by rfl)
/--
集合论等式与隶属式的局部良构性构造器。
这里只用于给参数化编码规格组装一次 proof-carrying 边界，不扩张公共语法接口。
-/
private theorem set_equality_formula_admissible
    {left right : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Formula.Admissible (left ≐ₘ right) :=
  ⟨FormulaWellFormed.equal hLeft.1 hRight.1,
    FormulaScoped.equal hLeft.2 hRight.2⟩
private theorem set_membership_formula_admissible
    {element set : SetTerm} (hElement : Term.Admissible element SetSort.set) (hSet : Term.Admissible set SetSort.set) :
    Formula.Admissible (element ∈ₘ set) := by
  prove_admissible
/--
编码级替换规格对任意四个良构集合项都自动满足公式良构性。
该合同封装 `310`、`311` 两个内部 binder 的机械组装；后续 quotation、对角图与
可表示性证明不再各自展开 `code_substitution_spec`。
-/
theorem code_substitution_spec_admissible (source boundVariable replacement candidate : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hBoundVariable : Term.Admissible boundVariable SetSort.set) (hReplacement : Term.Admissible replacement SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (code_substitution_spec source boundVariable replacement candidate) := by
  let pieces : SetTerm := x#310
  let index : SetTerm := x#311
  have hPieces : Term.Admissible pieces SetSort.set :=
    set_variable_admissible 310
  have hIndex : Term.Admissible index SetSort.set :=
    set_variable_admissible 311
  have hCodeString : Term.Admissible CodeStrₘ SetSort.set :=
    code_string_space_term_admissible
  have hCandidateCode :=
    set_membership_formula_admissible hCandidate hCodeString
  have hSequenceSpace :=
    finite_sequence_space_term_admissible CodeStrₘ hCodeString
  have hPiecesSequence :=
    set_membership_formula_admissible hPieces hSequenceSpace
  have hPiecesDomain :=
    domain_term_admissible pieces hPieces
  have hSourceDomain :=
    domain_term_admissible source hSource
  have hDomainEquality :=
    set_equality_formula_admissible hPiecesDomain hSourceDomain
  have hIndexDomain :=
    set_membership_formula_admissible hIndex hSourceDomain
  have hSourceIndex :=
    function_application_term_admissible source index hSource hIndex
  have hZero := finite_numeral_term_admissible 0
  have hBoundHead :=
    function_application_term_admissible boundVariable (numₘ(0))
      hBoundVariable hZero
  have hMatches :=
    set_equality_formula_admissible hSourceIndex hBoundHead
  have hPiecesIndex :=
    function_application_term_admissible pieces index hPieces hIndex
  have hReplacementCase :=
    set_equality_formula_admissible hPiecesIndex hReplacement
  have hSingletonSourceIndex :=
    singleton_symbol_code_term_admissible (source ·ₘ index) hSourceIndex
  have hSourceCase :=
    set_equality_formula_admissible hPiecesIndex hSingletonSourceIndex
  have hPointwise :=
    Formula.Admissible.imp hIndexDomain <|
      Formula.Admissible.disj (Formula.Admissible.conj hMatches hReplacementCase) (Formula.Admissible.conj (Formula.Admissible.neg hMatches) hSourceCase)
  have hPointwiseAll :=
    Formula.Admissible.forall_closeFreeAt SetSort.set 311 hPointwise
  have hFlatten :=
    finite_sequence_flatten_term_admissible pieces hPieces
  have hFlattenEquality :=
    set_equality_formula_admissible hCandidate hFlatten
  have hPiecesBody :=
    Formula.Admissible.conj (Formula.Admissible.conj hPiecesSequence hDomainEquality) (Formula.Admissible.conj hPointwiseAll hFlattenEquality)
  have hPiecesExist :=
    Formula.Admissible.exists_closeFreeAt SetSort.set 310 hPiecesBody
  simpa [code_substitution_spec, substitution_piece_condition,
    pieces, index] using
    Formula.Admissible.conj hCandidateCode hPiecesExist
/-! ## 子串与出现性条件的公式边界 -/
/-- 子串关系保持整串、片段与起点三个公开项的 admissibility。 -/
theorem code_substring_at_condition_admissible (whole segment start : SetTerm) (hWhole : Term.Admissible whole SetSort.set)
    (hSegment : Term.Admissible segment SetSort.set) (hStart : Term.Admissible start SetSort.set) :
    Formula.Admissible (code_substring_at_condition whole segment start) := by
  have hStartNatural :=
    membership_formula_admissible hStart omega_term_admissible
  have hIndex :
      Term.Admissible (x#320) SetSort.set :=
    set_variable_admissible 320
  have hSegmentDomain :=
    domain_term_admissible segment hSegment
  have hIndexSegment :=
    membership_formula_admissible hIndex hSegmentDomain
  have hShiftedIndex :=
    natural_addition_term_admissible (x#320) start hIndex hStart
  have hWholeDomain :=
    domain_term_admissible whole hWhole
  have hShiftedWhole :=
    membership_formula_admissible hShiftedIndex hWholeDomain
  have hWholeValue :=
    function_application_term_admissible
      whole ((x#320) +ₘ start) hWhole hShiftedIndex
  have hSegmentValue :=
    function_application_term_admissible
      segment (x#320) hSegment hIndex
  have hValueEquation :=
    Formula.Admissible.equal hWholeValue hSegmentValue
  have hPointwise :=
    Formula.Admissible.imp hIndexSegment (Formula.Admissible.conj hShiftedWhole hValueEquation)
  have hAllPoints :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set 320 hPointwise
  simpa [code_substring_at_condition] using
    Formula.Admissible.conj hStartNatural hAllPoints
/-- 指定变量在给定位置出现的逐点条件保持三个公开项的 admissibility。 -/
theorem variable_occurs_at_position_condition_admissible (boundVariable formula position : SetTerm) (hBoundVariable : Term.Admissible boundVariable SetSort.set)
    (hFormula : Term.Admissible formula SetSort.set) (hPosition : Term.Admissible position SetSort.set) :
    Formula.Admissible (variable_occurs_at_position_condition
        boundVariable formula position) := by
  have hFormulaDomain :=
    domain_term_admissible formula hFormula
  have hPositionMember :=
    membership_formula_admissible hPosition hFormulaDomain
  have hFormulaValue :=
    function_application_term_admissible
      formula position hFormula hPosition
  have hVariableValue :=
    function_application_term_admissible
      boundVariable (numₘ(0)) hBoundVariable (finite_numeral_term_admissible 0)
  have hValueEquation :=
    Formula.Admissible.equal hFormulaValue hVariableValue
  simpa [variable_occurs_at_position_condition] using
    Formula.Admissible.conj hPositionMember hValueEquation
/-- “变量符号在字符串中出现”条件保持两个公开代码项的 admissibility。 -/
theorem variable_symbol_occurs_condition_admissible (boundVariable source : SetTerm) (hBoundVariable : Term.Admissible boundVariable SetSort.set)
    (hSource : Term.Admissible source SetSort.set) :
    Formula.Admissible (variable_symbol_occurs_condition boundVariable source) := by
  have hVariableSymbol :=
    membership_formula_admissible
      hBoundVariable variable_symbol_set_term_admissible
  have hPosition :
      Term.Admissible (x#312) SetSort.set :=
    set_variable_admissible 312
  have hSourceDomain :=
    domain_term_admissible source hSource
  have hPositionMember :=
    membership_formula_admissible hPosition hSourceDomain
  have hSourceValue :=
    function_application_term_admissible
      source (x#312) hSource hPosition
  have hVariableValue :=
    function_application_term_admissible
      boundVariable (numₘ(0)) hBoundVariable (finite_numeral_term_admissible 0)
  have hValueEquation :=
    Formula.Admissible.equal hSourceValue hVariableValue
  have hPositionBody :=
    Formula.Admissible.conj hPositionMember hValueEquation
  have hPositionExists :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set 312 hPositionBody
  simpa [variable_symbol_occurs_condition] using
    Formula.Admissible.conj hVariableSymbol hPositionExists
/-- 全称量词子公式的 binder 条件保持四个公开代码项的 admissibility。 -/
theorem universal_binder_at_condition_admissible (boundVariable formula body start : SetTerm) (hBoundVariable : Term.Admissible boundVariable SetSort.set)
    (hFormula : Term.Admissible formula SetSort.set) (hBody : Term.Admissible body SetSort.set) (hStart : Term.Admissible start SetSort.set) :
    Formula.Admissible (universal_binder_at_condition
        boundVariable formula body start) := by
  have hVariableSymbol :=
    membership_formula_admissible
      hBoundVariable variable_symbol_set_term_admissible
  have hBodyFormula :=
    is_formula_code_formula_admissible hBody
  have hBodyString :=
    membership_formula_admissible
      hBody code_string_space_term_admissible
  have hBinderCode :=
    universal_formula_code_term_admissible
      boundVariable body hBoundVariable hBody
  have hSubstring :=
    code_substring_at_condition_admissible
      formula (forall_codeₘ(boundVariable, body)) start
      hFormula hBinderCode hStart
  simpa [universal_binder_at_condition] using
    Formula.Admissible.conj (Formula.Admissible.conj hVariableSymbol (Formula.Admissible.conj hBodyFormula hBodyString))
      hSubstring
/-- 量词出现条件保持变量码与公式码的 admissibility。 -/
theorem quantifier_occurs_condition_admissible (boundVariable formula : SetTerm)
    (hBoundVariable : Term.Admissible boundVariable SetSort.set)
    (hFormula : Term.Admissible formula SetSort.set) :
    Formula.Admissible (quantifier_occurs_condition boundVariable formula) := by
  simpa [quantifier_occurs_condition] using
    Formula.Admissible.exists_closeFreeAt SetSort.set 321 <|
      Formula.Admissible.exists_closeFreeAt SetSort.set 322 <|
        universal_binder_at_condition_admissible boundVariable formula
          (x#321) (x#322) hBoundVariable hFormula
          (set_variable_admissible 321) (set_variable_admissible 322)
/-- 量词变量声明位置条件保持三个公开项的 admissibility。 -/
theorem binder_declaration_position_condition_admissible (boundVariable formula position : SetTerm) (hBoundVariable : Term.Admissible boundVariable SetSort.set)
    (hFormula : Term.Admissible formula SetSort.set) (hPosition : Term.Admissible position SetSort.set) :
    Formula.Admissible (binder_declaration_position_condition
        boundVariable formula position) := by
  have hBody :
      Term.Admissible (x#323) SetSort.set :=
    set_variable_admissible 323
  have hStart :
      Term.Admissible (x#324) SetSort.set :=
    set_variable_admissible 324
  have hBinder :=
    universal_binder_at_condition_admissible
      boundVariable formula (x#323) (x#324)
      hBoundVariable hFormula hBody hStart
  have hDeclaredPosition :=
    natural_addition_term_admissible (numₘ(2)) (x#324) (finite_numeral_term_admissible 2) hStart
  have hPositionEquation :=
    Formula.Admissible.equal hPosition hDeclaredPosition
  have hStartBody :=
    Formula.Admissible.conj hBinder hPositionEquation
  have hStartExists :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set 324 hStartBody
  simpa [binder_declaration_position_condition] using
    Formula.Admissible.exists_closeFreeAt
      SetSort.set 323 hStartExists
/-- 量词公式体内部位置条件保持三个公开项的 admissibility。 -/
theorem quantifier_body_position_condition_admissible (boundVariable formula position : SetTerm) (hBoundVariable : Term.Admissible boundVariable SetSort.set)
    (hFormula : Term.Admissible formula SetSort.set) (hPosition : Term.Admissible position SetSort.set) :
    Formula.Admissible (quantifier_body_position_condition
        boundVariable formula position) := by
  have hBody :
      Term.Admissible (x#325) SetSort.set :=
    set_variable_admissible 325
  have hStart :
      Term.Admissible (x#326) SetSort.set :=
    set_variable_admissible 326
  have hIndex :
      Term.Admissible (x#327) SetSort.set :=
    set_variable_admissible 327
  have hBinder :=
    universal_binder_at_condition_admissible
      boundVariable formula (x#325) (x#326)
      hBoundVariable hFormula hBody hStart
  have hBodyDomain :=
    domain_term_admissible (x#325) hBody
  have hIndexBody :=
    membership_formula_admissible hIndex hBodyDomain
  have hBodyOffset :=
    natural_addition_term_admissible (numₘ(3)) (x#326) (finite_numeral_term_admissible 3) hStart
  have hAbsolutePosition :=
    natural_addition_term_admissible (x#327) ((numₘ(3)) +ₘ (x#326))
      hIndex hBodyOffset
  have hPositionEquation :=
    Formula.Admissible.equal hPosition hAbsolutePosition
  have hIndexBodyFormula :=
    Formula.Admissible.conj (Formula.Admissible.conj hBinder hIndexBody)
      hPositionEquation
  have hIndexExists :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set 327 hIndexBodyFormula
  have hStartExists :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set 326 hIndexExists
  simpa [quantifier_body_position_condition] using
    Formula.Admissible.exists_closeFreeAt
      SetSort.set 325 hStartExists
/-- 受约束出现位置条件保持三个公开项的 admissibility。 -/
theorem bound_occurrence_position_condition_admissible (boundVariable formula position : SetTerm) (hBoundVariable : Term.Admissible boundVariable SetSort.set)
    (hFormula : Term.Admissible formula SetSort.set) (hPosition : Term.Admissible position SetSort.set) :
    Formula.Admissible (bound_occurrence_position_condition
        boundVariable formula position) := by
  have hOccurs :=
    variable_occurs_at_position_condition_admissible
      boundVariable formula position
      hBoundVariable hFormula hPosition
  have hDeclaration :=
    binder_declaration_position_condition_admissible
      boundVariable formula position
      hBoundVariable hFormula hPosition
  have hBody :=
    quantifier_body_position_condition_admissible
      boundVariable formula position
      hBoundVariable hFormula hPosition
  simpa [bound_occurrence_position_condition] using
    Formula.Admissible.conj hOccurs (Formula.Admissible.disj hDeclaration hBody)
/-- 自由出现位置条件保持三个公开项的 admissibility。 -/
theorem free_occurrence_position_condition_admissible (boundVariable formula position : SetTerm) (hBoundVariable : Term.Admissible boundVariable SetSort.set)
    (hFormula : Term.Admissible formula SetSort.set) (hPosition : Term.Admissible position SetSort.set) :
    Formula.Admissible (free_occurrence_position_condition
        boundVariable formula position) := by
  have hOccurs :=
    variable_occurs_at_position_condition_admissible
      boundVariable formula position
      hBoundVariable hFormula hPosition
  have hBound :=
    bound_occurrence_position_condition_admissible
      boundVariable formula position
      hBoundVariable hFormula hPosition
  simpa [free_occurrence_position_condition] using
    Formula.Admissible.conj hOccurs (Formula.Admissible.neg hBound)
theorem variable_collection_term_admissible (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    Term.Admissible (varsₘ(source))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .variableCollection [⟨source, by assumption⟩]
      (by rfl) (by rfl)
theorem free_occurrence_positions_term_admissible (boundVariable formula : SetTerm) (hVariable :
      Term.Admissible boundVariable SetSort.set) (hFormula :
      Term.Admissible formula SetSort.set) :
    Term.Admissible (free_posₘ(boundVariable, formula))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .freeOccurrencePositions [⟨boundVariable, by assumption⟩, ⟨formula, by assumption⟩]
      (by rfl) (by rfl)
/-! ## 良构性与闭理论边界 -/
theorem symbol_code_operator_definition_axiom_admissible :
    Formula.Admissible
      symbol_code_operator_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem formula_constructor_definition_axiom_admissible :
    Formula.Admissible
      formula_constructor_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem formula_code_definition_axiom_admissible :
    Formula.Admissible
      formula_code_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem formula_code_generation_separation_axiom_admissible :
    Formula.Admissible
      formula_code_generation_separation_axiom :=
  formula_code_generation_predicate.separation_axiom_admissible
theorem substitution_variable_definition_axiom_admissible :
    Formula.Admissible
      substitution_variable_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem occurrence_definition_axiom_admissible :
    Formula.Admissible
      occurrence_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem symbol_code_operator_theory_admissible :
    Theory.Admissible symbol_code_operator_theory :=
  Theory.admissible_insert
    symbol_code_operator_definition_axiom_admissible
    formal_language_encoding_theory_admissible
theorem formula_constructor_theory_admissible :
    Theory.Admissible formula_constructor_theory :=
  Theory.admissible_insert
    formula_constructor_definition_axiom_admissible
    symbol_code_operator_theory_admissible
theorem formula_code_theory_admissible :
    Theory.Admissible formula_code_theory :=
  Theory.admissible_insert
    formula_code_definition_axiom_admissible
    (Theory.admissible_insert
      formula_code_generation_separation_axiom_admissible
      formula_constructor_theory_admissible)
theorem substitution_variable_theory_admissible :
    Theory.Admissible substitution_variable_theory :=
  Theory.admissible_insert
    substitution_variable_definition_axiom_admissible
    formula_code_theory_admissible
theorem occurrence_theory_admissible :
    Theory.Admissible occurrence_theory :=
  Theory.admissible_insert
    occurrence_definition_axiom_admissible
    substitution_variable_theory_admissible
theorem expression_encoding_theory_admissible :
    Theory.Admissible expression_encoding_theory :=
  occurrence_theory_admissible
@[derive_close_sentence]
theorem symbol_code_operator_theory_sentence
    {formula : SetFormula} (hFormula : symbol_code_operator_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact symbol_code_operator_definition_axiom_admissible
    · native_decide
  · exact formal_language_encoding_theory_sentence hFormula
@[derive_close_sentence]
theorem formula_constructor_theory_sentence
    {formula : SetFormula} (hFormula : formula_constructor_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact formula_constructor_definition_axiom_admissible
    · native_decide
  · exact symbol_code_operator_theory_sentence hFormula
@[derive_close_sentence]
theorem formula_code_theory_sentence
    {formula : SetFormula} (hFormula : formula_code_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact formula_code_definition_axiom_admissible
    · native_decide
  · rcases hFormula with rfl | hFormula
    · constructor
      · exact formula_code_generation_separation_axiom_admissible
      · native_decide
    · exact formula_constructor_theory_sentence hFormula
@[derive_close_sentence]
theorem substitution_variable_theory_sentence
    {formula : SetFormula} (hFormula : substitution_variable_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact substitution_variable_definition_axiom_admissible
    · native_decide
  · exact formula_code_theory_sentence hFormula
@[derive_close_sentence]
theorem occurrence_theory_sentence
    {formula : SetFormula} (hFormula : occurrence_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact occurrence_definition_axiom_admissible
    · native_decide
  · exact substitution_variable_theory_sentence hFormula
@[derive_close_sentence]
theorem expression_encoding_theory_sentence
    {formula : SetFormula} (hFormula : expression_encoding_theory formula) :
    Formula.Sentence formula :=
  occurrence_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem formal_language_encoding_theory_subset_symbol_code_operator_theory
    {formula : SetFormula} (hFormula : formal_language_encoding_theory formula) :
    symbol_code_operator_theory formula :=
  Or.inr hFormula
theorem symbol_code_operator_theory_subset_formula_constructor_theory
    {formula : SetFormula} (hFormula : symbol_code_operator_theory formula) :
    formula_constructor_theory formula :=
  Or.inr hFormula
theorem formula_constructor_theory_subset_formula_code_theory
    {formula : SetFormula} (hFormula : formula_constructor_theory formula) :
    formula_code_theory formula :=
  Or.inr <| Or.inr hFormula
theorem formula_code_theory_subset_substitution_variable_theory
    {formula : SetFormula} (hFormula : formula_code_theory formula) :
    substitution_variable_theory formula :=
  Or.inr hFormula
theorem substitution_variable_theory_subset_expression_encoding_theory
    {formula : SetFormula} (hFormula : substitution_variable_theory formula) :
    expression_encoding_theory formula :=
  Or.inr hFormula
/-! ## 待证明定理索引 -/
/-!
后续证明层将基于本模块处理：
* 原子公式和三种复合公式构造的互斥性与唯一可读性；
* `FormulaCodeₘ` 的结构归纳、构造闭性和反演；
* 参数化符号编码运算与素数幂编码规格的等价性；
* 编码级替换对项、原子公式和复合公式的递归方程；
* `varsₘ` 对各构造的收集方程；
* `quantifier_occursₘ`、`bound_occursₘ`、`free_occursₘ` 与
  `free_posₘ` 的相互刻画；
* 替换保持公式编码、无捕获替换和自由变量定理。
这些结论会优先由 `prove_auto` 压缩纯逻辑与集合规格的机械部分；字符串分解、
构造互斥和搜索器可能自举的结构归纳步骤保留手工证明。
-/
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
