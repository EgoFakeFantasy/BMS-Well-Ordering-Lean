import YesMetaZFC.Logic.FirstOrder.FormalSystem.LogicalRuleEncoding
/-!
# 一阶逻辑语义解释系统
本模块在对象集合论中建立一阶语言的语义解释设施。公共接口分为四层：
* 相对于非逻辑符号集的项、公式编码集合；
* 非空论域及其符号解释组成的结构；
* 结构上的变量赋值空间；
* 由变量、常元和函数应用递归合同约束的项求值函数。
文献中的 `XGFH`、`XXng`、`XBDS`、`XGJG`、`FuZh`、`Θ₃₀₀₀f`、
`Θ₃₀₀₀g` 与 `Θ₃₀₀₀h` 仅保留为检索索引。相关项与相关公式不通过纸面的
逐字符辅助编号定义，而是直接检查编码中出现的符号是否属于允许的符号集。
项求值采用 proof-carrying 图函数边界：每个变量赋值对应一个从相关项编码到论域
的映射，变量按赋值解释、常元按结构解释，函数应用则先逐点求值参数列，再应用
结构给出的函数解释。这样后续塔斯基真谓词可以直接消费统一的项值关系。
本模块只建立定义公理、理论链和良构性边界；结构解释的存在唯一性、项求值递归
定理与换赋值引理留给后续证明层。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
/-! ## 相关语法对象 -/
/-- 一个编码字符可以出现在相对于 `symbols` 的项编码中。 -/
def related_term_token_condition (symbols token : SetTerm) :
    SetFormula := (((sym_codeₘ(token) ∈ₘ VarSymₘ) ∨ₘ (sym_codeₘ(token) ∈ₘ symbols)) ∨ₘ ((sym_codeₘ(token) ≐ₘ
        left_parenthesis_symbol_code_term) ∨ₘ (sym_codeₘ(token) ≐ₘ
        right_parenthesis_symbol_code_term)))
/-- `code` 是只使用给定非逻辑符号集的项编码。 -/
def related_term_code_condition (symbols code : SetTerm) :
    SetFormula :=
  term_codeₘ(code) ∧ₘ (∀ₘ[SetSort.set, 600], ((x#600 ∈ₘ domₘ(code)) ⟶ₘ
        related_term_token_condition
          symbols (code ·ₘ x#600)))
/-- 一个编码字符可以出现在相对于 `symbols` 的公式编码中。 -/
def related_formula_token_condition (symbols token : SetTerm) :
    SetFormula := (((sym_codeₘ(token) ∈ₘ LogicSymₘ) ∨ₘ (sym_codeₘ(token) ∈ₘ MembershipSymₘ)) ∨ₘ ((sym_codeₘ(token) ∈ₘ VarSymₘ) ∨ₘ
      (sym_codeₘ(token) ∈ₘ symbols)))
/-- `code` 是只使用给定非逻辑符号集的公式编码。 -/
def related_formula_code_condition (symbols code : SetTerm) :
    SetFormula :=
  formula_codeₘ(code) ∧ₘ (∀ₘ[SetSort.set, 601], ((x#601 ∈ₘ domₘ(code)) ⟶ₘ
        related_formula_token_condition
          symbols (code ·ₘ x#601)))
/-- `candidate` 精确收集相对于 `symbols` 的全部项编码。 -/
def related_term_set_spec (symbols candidate : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set, 602], ((x#602 ∈ₘ candidate) ↔ₘ
      related_term_code_condition symbols (x#602))
/-- `candidate` 精确收集相对于 `symbols` 的全部公式编码。 -/
def related_formula_set_spec (symbols candidate : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set, 603], ((x#603 ∈ₘ candidate) ↔ₘ
      related_formula_code_condition symbols (x#603))
/-- 全部非逻辑符号编码集合的定义公理；文献索引为 `XGFH`、`Ξ₁₆₀`。 -/
def related_nonlogical_symbol_set_definition_axiom :
    SetFormula :=
  NonlogicalSymₘ ≐ₘ (ConstSymₘ ∪ₘ (FuncSymₘ ∪ₘ PredSymₘ))
/-- 相对项编码集合的开放定义实例；文献索引为 `XXng`、`Ξ₁₆₁`。 -/
def related_term_set_definition_instance (symbols candidate : SetTerm) :
    SetFormula := (symbols ⊆ₘ NonlogicalSymₘ) ⟶ₘ (((candidate ≐ₘ RelTermCodeₘ(symbols)) ↔ₘ
      related_term_set_spec symbols candidate))
/-- 相对项编码集合的定义公理。 -/
def related_term_set_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      related_term_set_definition_instance (x#0) (x#1)
/-- 相对公式编码集合的开放定义实例；文献索引为 `XBDS`、`Ξ₁₆₂`。 -/
def related_formula_set_definition_instance (symbols candidate : SetTerm) :
    SetFormula := (symbols ⊆ₘ NonlogicalSymₘ) ⟶ₘ (((candidate ≐ₘ RelFormulaCodeₘ(symbols)) ↔ₘ
      related_formula_set_spec symbols candidate))
/-- 相对公式编码集合的定义公理。 -/
def related_formula_set_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      related_formula_set_definition_instance (x#0) (x#1)
/-- 相对项与公式编码集合的联合定义公理。 -/
def related_syntax_definition_axiom :
    SetFormula :=
  related_term_set_definition_axiom ∧ₘ
    related_formula_set_definition_axiom
/-! ## 结构 -/
/-- 常元解释落在结构论域中。 -/
def structure_constant_condition (carrier interpretation symbols symbol : SetTerm) :
    SetFormula := ((symbol ∈ₘ (symbols ∩ₘ ConstSymₘ)) ⟶ₘ ((interpretation ·ₘ symbol) ∈ₘ carrier))
/-- 函数符号被解释为集合编码函数。 -/
def structure_function_condition (interpretation symbols symbol : SetTerm) :
    SetFormula := ((symbol ∈ₘ (symbols ∩ₘ FuncSymₘ)) ⟶ₘ
    is_function_formula (interpretation ·ₘ symbol))
/-- 谓词符号被解释为集合编码关系。 -/
def structure_predicate_condition (interpretation symbols symbol : SetTerm) :
    SetFormula := ((symbol ∈ₘ (symbols ∩ₘ PredSymₘ)) ⟶ₘ
    is_relation_formula (interpretation ·ₘ symbol))
/-- `interpretation` 在非空论域上解释 `symbols`。 -/
def structure_condition (carrier interpretation symbols : SetTerm) :
    SetFormula := ((carrier ≠ₘ ∅ₘ) ∧ₘ ((symbols ⊆ₘ NonlogicalSymₘ) ∧ₘ (is_function_formula interpretation ∧ₘ (domₘ(interpretation) ≐ₘ symbols)))) ∧ₘ
    ((∀ₘ[SetSort.set, 604],
        structure_constant_condition
          carrier interpretation symbols (x#604)) ∧ₘ ((∀ₘ[SetSort.set, 605],
          structure_function_condition
            interpretation symbols (x#605)) ∧ₘ (∀ₘ[SetSort.set, 606],
          structure_predicate_condition
            interpretation symbols (x#606))))
/-- 相关结构谓词定义公理；文献索引为 `XGJG`、`Ξ₁₆₃`。 -/
def structure_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2], ((structureₘ(x#0, x#1, x#2)) ↔ₘ
          structure_condition (x#0) (x#1) (x#2))
/-! ## 项求值 -/
/-- 给定论域上的变量赋值空间。 -/
abbrev assignment_space_term (carrier : SetTerm) :
    SetTerm :=
  Mapₘ(VarSymₘ, carrier)
/-- `values` 逐点收集参数项在给定赋值下的值。 -/
def evaluated_argument_sequence_condition (carrier evaluation assignment arguments values : SetTerm) :
    SetFormula := ((values ∈ₘ seq_spaceₘ(carrier)) ∧ₘ (domₘ(values) ≐ₘ domₘ(arguments))) ∧ₘ (∀ₘ[SetSort.set, 607], ((x#607 ∈ₘ domₘ(arguments)) ⟶ₘ
        ((values ·ₘ x#607) ≐ₘ ((evaluation ·ₘ assignment) ·ₘ (arguments ·ₘ x#607)))))
/-- 一个函数应用项满足项求值递归合同。 -/
def function_application_evaluation_condition (carrier interpretation symbols evaluation assignment
      arityPredecessor symbolIndex arguments : SetTerm) :
    SetFormula := ((((arityPredecessor ∈ₘ ωₘ) ∧ₘ (symbolIndex ∈ₘ ωₘ)) ∧ₘ ((func_sym_codeₘ(
          arityPredecessor, symbolIndex) ∈ₘ symbols) ∧ₘ ((arguments ∈ₘ TermSeqₘ) ∧ₘ (domₘ(arguments) ≐ₘ Sₘ(arityPredecessor))))) ∧ₘ (∀ₘ[SetSort.set, 608],
      ((x#608 ∈ₘ domₘ(arguments)) ⟶ₘ ((arguments ·ₘ x#608) ∈ₘ
          RelTermCodeₘ(symbols))))) ⟶ₘ (∃ₘ[SetSort.set, 609], (evaluated_argument_sequence_condition
          carrier evaluation assignment arguments (x#609) ∧ₘ (((evaluation ·ₘ assignment) ·ₘ
            term_application_code_term
              arityPredecessor symbolIndex arguments) ≐ₘ ((interpretation ·ₘ
              func_sym_codeₘ(
                arityPredecessor, symbolIndex)) ·ₘ (x#609)))))
/-- 一个变量赋值下的项求值映射满足三种项构造合同。 -/
def term_evaluation_assignment_condition (carrier interpretation symbols evaluation assignment : SetTerm) :
    SetFormula := ((assignment ∈ₘ assignment_space_term carrier) ∧ₘ
    is_mapping_formula (evaluation ·ₘ assignment)
      RelTermCodeₘ(symbols)
      carrier) ∧ₘ ((∀ₘ[SetSort.set, 610], ((x#610 ∈ₘ VarSymₘ) ⟶ₘ (((evaluation ·ₘ assignment) ·ₘ x#610) ≐ₘ (assignment ·ₘ x#610)))) ∧ₘ ((∀ₘ[SetSort.set, 611],
        ((x#611 ∈ₘ (symbols ∩ₘ ConstSymₘ)) ⟶ₘ (((evaluation ·ₘ assignment) ·ₘ x#611) ≐ₘ (interpretation ·ₘ x#611)))) ∧ₘ (∀ₘ[SetSort.set, 612],
          ∀ₘ[SetSort.set, 613],
            ∀ₘ[SetSort.set, 614],
              function_application_evaluation_condition
                carrier interpretation symbols evaluation assignment (x#612) (x#613) (x#614))))
/-- `evaluation` 是给定结构上完整的项求值函数。 -/
def term_evaluation_condition (carrier interpretation symbols evaluation : SetTerm) :
    SetFormula := (structureₘ(carrier, interpretation, symbols) ∧ₘ
    is_mapping_formula
      evaluation (assignment_space_term carrier)
      Mapₘ(RelTermCodeₘ(symbols), carrier)) ∧ₘ (∀ₘ[SetSort.set, 615], ((x#615 ∈ₘ assignment_space_term carrier) ⟶ₘ
        term_evaluation_assignment_condition
          carrier interpretation symbols evaluation (x#615)))
/-- 项求值函数谓词定义公理；文献索引为 `FuZh`。 -/
def term_evaluation_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3], ((term_evaluationₘ(
              x#0, x#1, x#2, x#3)) ↔ₘ
            term_evaluation_condition (x#0) (x#1) (x#2) (x#3))
/-- `value` 是 `term` 在指定结构与变量赋值下的值。 -/
def term_value_condition (carrier interpretation symbols evaluation assignment term value : SetTerm) :
    SetFormula := ((term_evaluationₘ(
      carrier, interpretation, symbols, evaluation) ∧ₘ (assignment ∈ₘ assignment_space_term carrier)) ∧ₘ ((term ∈ₘ RelTermCodeₘ(symbols)) ∧ₘ
      (value ∈ₘ carrier))) ∧ₘ (value ≐ₘ ((evaluation ·ₘ assignment) ·ₘ term))
/-- 项值关系定义公理。 -/
def term_value_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          ∀ₘ[SetSort.set, 4],
            ∀ₘ[SetSort.set, 5],
              ∀ₘ[SetSort.set, 6], ((term_valueₘ(
                    x#0, x#1, x#2, x#3,
                    x#4, x#5, x#6)) ↔ₘ
                  term_value_condition (x#0) (x#1) (x#2) (x#3) (x#4) (x#5) (x#6))
/-! ## 理论组合 -/
/-- 加入相关非逻辑符号集后的理论。 -/
def related_symbol_semantics_theory :
    SetTheory :=
  Theory.insert
    related_nonlogical_symbol_set_definition_axiom
    logical_rule_encoding_theory
/-- 加入相对项与公式编码集合后的理论。 -/
def related_syntax_semantics_theory :
    SetTheory :=
  Theory.insert
    related_syntax_definition_axiom
    related_symbol_semantics_theory
/-- 加入结构谓词后的理论。 -/
def structure_semantics_theory :
    SetTheory :=
  Theory.insert
    structure_definition_axiom
    related_syntax_semantics_theory
/-- 加入项求值函数合同后的理论。 -/
def term_evaluation_semantics_theory :
    SetTheory :=
  Theory.insert
    term_evaluation_definition_axiom
    structure_semantics_theory
/-- 一阶语义解释层的稳定理论入口。 -/
def semantic_interpretation_theory :
    SetTheory :=
  Theory.insert
    term_value_definition_axiom
    term_evaluation_semantics_theory
/-! ## proof-carrying 项边界 -/
theorem related_nonlogical_symbol_set_term_admissible :
    Term.Admissible NonlogicalSymₘ SetSort.set := by
  simpa using
    set_function_application_admissible
      .relatedNonlogicalSymbolSet []
      (by rfl) (by rfl)
theorem related_term_set_term_admissible (symbols : SetTerm) (hSymbols : Term.Admissible symbols SetSort.set) :
    Term.Admissible (RelTermCodeₘ(symbols))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .relatedTermSet [⟨symbols, by assumption⟩]
      (by rfl) (by rfl)
theorem related_formula_set_term_admissible (symbols : SetTerm) (hSymbols : Term.Admissible symbols SetSort.set) :
    Term.Admissible (RelFormulaCodeₘ(symbols))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .relatedFormulaSet [⟨symbols, by assumption⟩]
      (by rfl) (by rfl)
/-! ## 良构性与闭理论边界 -/
theorem related_nonlogical_symbol_set_definition_axiom_admissible :
    Formula.Admissible
      related_nonlogical_symbol_set_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem related_syntax_definition_axiom_admissible :
    Formula.Admissible
      related_syntax_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem structure_definition_axiom_admissible :
    Formula.Admissible structure_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem term_evaluation_definition_axiom_admissible :
    Formula.Admissible
      term_evaluation_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem term_value_definition_axiom_admissible :
    Formula.Admissible term_value_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem related_symbol_semantics_theory_admissible :
    Theory.Admissible related_symbol_semantics_theory :=
  Theory.admissible_insert
    related_nonlogical_symbol_set_definition_axiom_admissible
    logical_rule_encoding_theory_admissible
theorem related_syntax_semantics_theory_admissible :
    Theory.Admissible related_syntax_semantics_theory :=
  Theory.admissible_insert
    related_syntax_definition_axiom_admissible
    related_symbol_semantics_theory_admissible
theorem structure_semantics_theory_admissible :
    Theory.Admissible structure_semantics_theory :=
  Theory.admissible_insert
    structure_definition_axiom_admissible
    related_syntax_semantics_theory_admissible
theorem term_evaluation_semantics_theory_admissible :
    Theory.Admissible term_evaluation_semantics_theory :=
  Theory.admissible_insert
    term_evaluation_definition_axiom_admissible
    structure_semantics_theory_admissible
theorem semantic_interpretation_theory_admissible :
    Theory.Admissible semantic_interpretation_theory :=
  Theory.admissible_insert
    term_value_definition_axiom_admissible
    term_evaluation_semantics_theory_admissible
@[derive_close_sentence]
theorem related_symbol_semantics_theory_sentence
    {formula : SetFormula} (hFormula : related_symbol_semantics_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact related_nonlogical_symbol_set_definition_axiom_admissible
    · native_decide
  · exact logical_rule_encoding_theory_sentence hFormula
@[derive_close_sentence]
theorem related_syntax_semantics_theory_sentence
    {formula : SetFormula} (hFormula : related_syntax_semantics_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact related_syntax_definition_axiom_admissible
    · native_decide
  · exact related_symbol_semantics_theory_sentence hFormula
@[derive_close_sentence]
theorem structure_semantics_theory_sentence
    {formula : SetFormula} (hFormula : structure_semantics_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact structure_definition_axiom_admissible
    · native_decide
  · exact related_syntax_semantics_theory_sentence hFormula
@[derive_close_sentence]
theorem term_evaluation_semantics_theory_sentence
    {formula : SetFormula} (hFormula : term_evaluation_semantics_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact term_evaluation_definition_axiom_admissible
    · native_decide
  · exact structure_semantics_theory_sentence hFormula
@[derive_close_sentence]
theorem semantic_interpretation_theory_sentence
    {formula : SetFormula} (hFormula : semantic_interpretation_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact term_value_definition_axiom_admissible
    · native_decide
  · exact term_evaluation_semantics_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem logical_rule_encoding_theory_subset_related_symbol_semantics_theory
    {formula : SetFormula} (hFormula : logical_rule_encoding_theory formula) :
    related_symbol_semantics_theory formula :=
  Or.inr hFormula
theorem related_symbol_semantics_theory_subset_related_syntax_semantics_theory
    {formula : SetFormula} (hFormula : related_symbol_semantics_theory formula) :
    related_syntax_semantics_theory formula :=
  Or.inr hFormula
theorem related_syntax_semantics_theory_subset_structure_semantics_theory
    {formula : SetFormula} (hFormula : related_syntax_semantics_theory formula) :
    structure_semantics_theory formula :=
  Or.inr hFormula
theorem structure_semantics_theory_subset_term_evaluation_semantics_theory
    {formula : SetFormula} (hFormula : structure_semantics_theory formula) :
    term_evaluation_semantics_theory formula :=
  Or.inr hFormula
theorem term_evaluation_semantics_theory_subset_semantic_interpretation_theory
    {formula : SetFormula} (hFormula : term_evaluation_semantics_theory formula) :
    semantic_interpretation_theory formula :=
  Or.inr hFormula
/-! ## 待证明定理索引 -/
/-!
后续证明层按需处理：
* 相对项与相对公式集合对语言扩张的单调性；
* 结构解释对常元、函数符号和谓词符号的类型保持；
* 项求值函数的存在唯一性、参数列逐点求值和变量换赋值引理；
* 项值关系的单值性以及对项编码构造的反演。
这些定理将直接消费本模块的图函数合同；不重新引入文献的字符位置辅助式。
-/
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
