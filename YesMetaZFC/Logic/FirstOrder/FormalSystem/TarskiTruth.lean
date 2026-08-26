import YesMetaZFC.Logic.FirstOrder.FormalSystem.SemanticInterpretation
/-!
# 一阶逻辑塔斯基真谓词
本模块在语义解释系统之上给出公式满足、真、模型、语义后承和普遍真公式的对象
集合论编码。核心构造是相对公式编码的阶段集合：零阶段只含原子公式，后继阶段
关闭于否定、蕴含和全称量化；满足关系同步按前一阶段递归。
文献中的 `BDS*`、`Θ₄₀₀₀i` 至 `Θ₄₀₀₀t`、`MnZu`、`ManZ`、`ZhnS`、
`ZhSh`、`LJTL` 与 `PBZS` 仅作为检索索引。纸面中对递归阶段附带的固定编码
长度界限不进入核心接口；阶段参数只表示语法构造深度，因而可供任意语言和任意
公式编码复用。
本模块建立定义公理、理论链和良构性边界。阶段递归的存在唯一性、满足关系的
阶段无关性、换赋值引理、塔斯基真引理以及语义完备性留给后续证明层。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
/-! ## 公式编码阶段 -/
/-- 零阶段只包含相对语言中的原子公式。 -/
def formula_stage_zero_condition (symbols formula : SetTerm) :
    SetFormula := (formula ∈ₘ AtomicCodeₘ) ∧ₘ (formula ∈ₘ RelFormulaCodeₘ(symbols))
/-- 后继阶段中由否定构造得到的公式。 -/
def formula_stage_negation_condition (symbols stage formula : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 700], ((x#700 ∈ₘ FormulaStageₘ(symbols, stage)) ∧ₘ (formula ≐ₘ neg_codeₘ(x#700)))
/-- 后继阶段中由蕴含构造得到的公式。 -/
def formula_stage_implication_condition (symbols stage formula : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 701],
    ∃ₘ[SetSort.set, 702], (((x#701 ∈ₘ FormulaStageₘ(symbols, stage)) ∧ₘ (x#702 ∈ₘ FormulaStageₘ(symbols, stage))) ∧ₘ (formula ≐ₘ imp_codeₘ(x#701, x#702)))
/-- 后继阶段中由全称量化构造得到的公式。 -/
def formula_stage_universal_condition (symbols stage formula : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 703],
    ∃ₘ[SetSort.set, 704], (((x#703 ∈ₘ VarSymₘ) ∧ₘ (x#704 ∈ₘ FormulaStageₘ(symbols, stage))) ∧ₘ (formula ≐ₘ forall_codeₘ(x#703, x#704)))
/-- 后继阶段的公式生成条件。 -/
def formula_stage_successor_condition (symbols stage formula : SetTerm) :
    SetFormula := (formula ∈ₘ FormulaStageₘ(symbols, stage)) ∨ₘ (formula_stage_negation_condition symbols stage formula ∨ₘ
      (formula_stage_implication_condition symbols stage formula ∨ₘ
        formula_stage_universal_condition symbols stage formula))
/-- `BDS*` 风格阶段公式集函数的递归定义公理。 -/
def formula_stage_set_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0], (x#0 ⊆ₘ NonlogicalSymₘ) ⟶ₘ ((∀ₘ[SetSort.set, 1], ((x#1 ∈ₘ FormulaStageₘ(x#0, numₘ(0))) ↔ₘ
            formula_stage_zero_condition (x#0) (x#1))) ∧ₘ (∀ₘ[SetSort.set, 2], (x#2 ∈ₘ ωₘ) ⟶ₘ (∀ₘ[SetSort.set, 3], ((x#3 ∈ₘ FormulaStageₘ(x#0, Sₘ(x#2))) ↔ₘ
                formula_stage_successor_condition (x#0) (x#2) (x#3)))))
/-! ## 原子公式满足 -/
/-- 等式原子在给定结构与赋值下成立。 -/
def equality_atomic_satisfaction_condition (carrier interpretation symbols evaluation assignment formula : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 710],
    ∃ₘ[SetSort.set, 711],
      ∃ₘ[SetSort.set, 712],
        ∃ₘ[SetSort.set, 713], (((formula ≐ₘ eq_codeₘ(x#710, x#711)) ∧ₘ
              term_valueₘ(
                carrier, interpretation, symbols, evaluation,
                assignment, x#710, x#712)) ∧ₘ (term_valueₘ(
              carrier, interpretation, symbols, evaluation,
              assignment, x#711, x#713) ∧ₘ ((x#712) ≐ₘ (x#713))))
/-- 隶属原子在给定结构与赋值下成立。 -/
def membership_atomic_satisfaction_condition (carrier interpretation symbols evaluation assignment formula : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 714],
    ∃ₘ[SetSort.set, 715],
      ∃ₘ[SetSort.set, 716],
        ∃ₘ[SetSort.set, 717], (((formula ≐ₘ
              membership_atomic_formula_code_term (x#714) (x#715)) ∧ₘ
              term_valueₘ(
                carrier, interpretation, symbols, evaluation,
                assignment, x#714, x#716)) ∧ₘ (term_valueₘ(
              carrier, interpretation, symbols, evaluation,
              assignment, x#715, x#717) ∧ₘ ((x#716) ∈ₘ (x#717))))
/-- 一般谓词应用原子在给定结构与赋值下成立。 -/
def predicate_atomic_satisfaction_condition (carrier interpretation symbols evaluation assignment formula : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 718],
    ∃ₘ[SetSort.set, 719],
      ∃ₘ[SetSort.set, 720],
        ∃ₘ[SetSort.set, 721], (((((x#718 ∈ₘ ωₘ) ∧ₘ (x#719 ∈ₘ ωₘ)) ∧ₘ ((pred_sym_codeₘ(
                  x#718, x#719) ∈ₘ symbols) ∧ₘ ((x#720 ∈ₘ TermSeqₘ) ∧ₘ (domₘ(x#720) ≐ₘ Sₘ(x#718))))) ∧ₘ ((formula ≐ₘ pred_codeₘ(
                x#718, x#719, x#720)) ∧ₘ
              evaluated_argument_sequence_condition
                carrier evaluation assignment (x#720) (x#721))) ∧ₘ ((x#721) ∈ₘ (interpretation ·ₘ
              pred_sym_codeₘ(x#718, x#719))))
/-- 原子公式满足条件。 -/
def atomic_satisfaction_condition (carrier interpretation symbols evaluation assignment formula : SetTerm) :
    SetFormula := ((structureₘ(carrier, interpretation, symbols) ∧ₘ
    term_evaluationₘ(carrier, interpretation, symbols, evaluation)) ∧ₘ (formula ∈ₘ AtomicCodeₘ)) ∧ₘ (equality_atomic_satisfaction_condition
        carrier interpretation symbols evaluation assignment formula ∨ₘ (membership_atomic_satisfaction_condition
          carrier interpretation symbols evaluation assignment formula ∨ₘ
        predicate_atomic_satisfaction_condition
          carrier interpretation symbols evaluation assignment formula))
/-- 原子公式满足谓词定义公理；文献索引为 `MnZu₀`、`Ξ₁₆₇`。 -/
def atomic_satisfaction_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          ∀ₘ[SetSort.set, 4],
            ∀ₘ[SetSort.set, 5], ((atomic_satisfiesₘ(
                  x#0, x#1, x#2, x#3,
                  x#4, x#5)) ↔ₘ
                atomic_satisfaction_condition (x#0) (x#1) (x#2) (x#3) (x#4) (x#5))
/-! ## 分阶段满足关系 -/
/-- `updated` 由 `assignment` 在一个变量处改写为 `value` 得到。 -/
def assignment_update_condition (carrier assignment boundVariable value updated : SetTerm) :
    SetFormula := (is_mapping_formula updated VarSymₘ carrier ∧ₘ ((updated ·ₘ boundVariable) ≐ₘ value)) ∧ₘ (∀ₘ[SetSort.set, 722], (((x#722 ∈ₘ VarSymₘ) ∧ₘ
          ((x#722) ≠ₘ boundVariable)) ⟶ₘ ((updated ·ₘ x#722) ≐ₘ (assignment ·ₘ x#722))))
/-- 否定公式的后继阶段满足子句。 -/
def negation_satisfaction_successor_condition (stage carrier interpretation symbols evaluation assignment formula : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 723], (((x#723 ∈ₘ FormulaStageₘ(symbols, stage)) ∧ₘ (formula ≐ₘ neg_codeₘ(x#723))) ∧ₘ
      ¬ₘ satisfies_stageₘ(
        stage, carrier, interpretation, symbols,
        evaluation, assignment, x#723))
/-- 蕴含公式的后继阶段满足子句。 -/
def implication_satisfaction_successor_condition (stage carrier interpretation symbols evaluation assignment formula : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 724],
    ∃ₘ[SetSort.set, 725], ((((x#724 ∈ₘ FormulaStageₘ(symbols, stage)) ∧ₘ (x#725 ∈ₘ FormulaStageₘ(symbols, stage))) ∧ₘ (formula ≐ₘ imp_codeₘ(x#724, x#725))) ∧ₘ
        (¬ₘ satisfies_stageₘ(
            stage, carrier, interpretation, symbols,
            evaluation, assignment, x#724) ∨ₘ
          satisfies_stageₘ(
            stage, carrier, interpretation, symbols,
            evaluation, assignment, x#725)))
/-- 全称公式的后继阶段满足子句。 -/
def universal_satisfaction_successor_condition (stage carrier interpretation symbols evaluation assignment formula : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 726],
    ∃ₘ[SetSort.set, 727], ((((x#726 ∈ₘ VarSymₘ) ∧ₘ (x#727 ∈ₘ FormulaStageₘ(symbols, stage))) ∧ₘ (formula ≐ₘ forall_codeₘ(x#726, x#727))) ∧ₘ
        (∀ₘ[SetSort.set, 728], ((x#728 ∈ₘ carrier) ⟶ₘ (∃ₘ[SetSort.set, 729], (assignment_update_condition
                  carrier assignment (x#726) (x#728) (x#729) ∧ₘ
                satisfies_stageₘ(
                  stage, carrier, interpretation, symbols,
                  evaluation, x#729, x#727))))))
/-- 后继阶段的公式满足子句。 -/
def formula_satisfaction_successor_condition (stage carrier interpretation symbols evaluation assignment formula : SetTerm) :
    SetFormula :=
  atomic_satisfiesₘ(
      carrier, interpretation, symbols, evaluation,
      assignment, formula) ∨ₘ (negation_satisfaction_successor_condition
        stage carrier interpretation symbols evaluation assignment formula ∨ₘ (implication_satisfaction_successor_condition
          stage carrier interpretation symbols evaluation assignment formula ∨ₘ
        universal_satisfaction_successor_condition
          stage carrier interpretation symbols evaluation assignment formula))
/-- 公式在指定递归阶段、结构与赋值下满足的条件。 -/
def formula_satisfaction_at_stage_condition (stage carrier interpretation symbols evaluation assignment formula : SetTerm) :
    SetFormula := (((structureₘ(carrier, interpretation, symbols) ∧ₘ
      term_evaluationₘ(carrier, interpretation, symbols, evaluation)) ∧ₘ (assignment ∈ₘ assignment_space_term carrier)) ∧ₘ ((stage ∈ₘ ωₘ) ∧ₘ
      (formula ∈ₘ FormulaStageₘ(symbols, stage)))) ∧ₘ (((stage ≐ₘ numₘ(0)) ∧ₘ
        atomic_satisfiesₘ(
          carrier, interpretation, symbols, evaluation,
          assignment, formula)) ∨ₘ (∃ₘ[SetSort.set, 730], (((x#730 ∈ₘ ωₘ) ∧ₘ (stage ≐ₘ Sₘ(x#730))) ∧ₘ
          formula_satisfaction_successor_condition (x#730) carrier interpretation symbols evaluation
            assignment formula)))
/-- 分阶段满足关系定义公理；文献索引为 `MnZuⁿ`、`Ξ₁₆₇a` 至 `Ξ₁₇₀`。 -/
def formula_satisfaction_at_stage_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          ∀ₘ[SetSort.set, 4],
            ∀ₘ[SetSort.set, 5],
              ∀ₘ[SetSort.set, 6], ((satisfies_stageₘ(
                    x#0, x#1, x#2, x#3,
                    x#4, x#5, x#6)) ↔ₘ
                  formula_satisfaction_at_stage_condition (x#0) (x#1) (x#2) (x#3) (x#4) (x#5) (x#6))
/-- 最终满足关系：存在一个包含该公式的递归阶段。 -/
def formula_satisfaction_condition (carrier interpretation symbols evaluation assignment formula : SetTerm) :
    SetFormula := (formula ∈ₘ RelFormulaCodeₘ(symbols)) ∧ₘ (∃ₘ[SetSort.set, 731], (((x#731 ∈ₘ ωₘ) ∧ₘ (formula ∈ₘ FormulaStageₘ(symbols, x#731))) ∧ₘ
        satisfies_stageₘ(
          x#731, carrier, interpretation, symbols,
          evaluation, assignment, formula)))
/-- 最终公式满足关系定义公理；文献索引为 `MnZu`、`Ξ₁₇₁`。 -/
def formula_satisfaction_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          ∀ₘ[SetSort.set, 4],
            ∀ₘ[SetSort.set, 5], ((satisfies_codeₘ(
                  x#0, x#1, x#2, x#3,
                  x#4, x#5)) ↔ₘ
                formula_satisfaction_condition (x#0) (x#1) (x#2) (x#3) (x#4) (x#5))
/-! ## 真、模型与语义后承 -/
/-- 公式在结构中对所有变量赋值为真。 -/
def truth_condition (carrier interpretation symbols evaluation formula : SetTerm) :
    SetFormula := ((structureₘ(carrier, interpretation, symbols) ∧ₘ
    term_evaluationₘ(carrier, interpretation, symbols, evaluation)) ∧ₘ (formula ∈ₘ RelFormulaCodeₘ(symbols))) ∧ₘ (∀ₘ[SetSort.set, 732],
      ((x#732 ∈ₘ assignment_space_term carrier) ⟶ₘ
        satisfies_codeₘ(
          carrier, interpretation, symbols, evaluation,
          x#732, formula)))
/-- 真谓词定义公理；文献索引为 `ZhnS`、`Ξ₁₇₃`。 -/
def truth_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          ∀ₘ[SetSort.set, 4], ((true_inₘ(
                x#0, x#1, x#2, x#3,
                x#4)) ↔ₘ
              truth_condition (x#0) (x#1) (x#2) (x#3) (x#4))
/-- 给定结构满足理论中的每一个公式。 -/
def model_condition (carrier interpretation symbols evaluation theory : SetTerm) :
    SetFormula := ((structureₘ(carrier, interpretation, symbols) ∧ₘ
    term_evaluationₘ(carrier, interpretation, symbols, evaluation)) ∧ₘ (theory ⊆ₘ RelFormulaCodeₘ(symbols))) ∧ₘ (∀ₘ[SetSort.set, 733], ((x#733 ∈ₘ theory) ⟶ₘ
        true_inₘ(
          carrier, interpretation, symbols, evaluation,
          x#733)))
/-- 模型谓词定义公理；文献索引为 `ManZ`、`ZhSh`、`Ξ₁₇₂`、`Ξ₁₇₄`。 -/
def model_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          ∀ₘ[SetSort.set, 4], ((model_ofₘ(
                x#0, x#1, x#2, x#3,
                x#4)) ↔ₘ
              model_condition (x#0) (x#1) (x#2) (x#3) (x#4))
/-- 给定语言中的语义后承条件。 -/
def logical_consequence_condition (symbols theory conclusion : SetTerm) :
    SetFormula := ((symbols ⊆ₘ NonlogicalSymₘ) ∧ₘ ((theory ⊆ₘ RelFormulaCodeₘ(symbols)) ∧ₘ (conclusion ∈ₘ RelFormulaCodeₘ(symbols)))) ∧ₘ (∀ₘ[SetSort.set, 734],
      ∀ₘ[SetSort.set, 735],
        ∀ₘ[SetSort.set, 736], ((structureₘ(
              x#734, x#735, symbols) ∧ₘ
            term_evaluationₘ(
              x#734, x#735, symbols, x#736)) ⟶ₘ (model_ofₘ(
                x#734, x#735, symbols, x#736,
                theory) ⟶ₘ
              true_inₘ(
                x#734, x#735, symbols, x#736,
                conclusion))))
/-- 公式在指定语言的所有结构中为真的条件。 -/
def theorem_condition (symbols formula : SetTerm) :
    SetFormula := ((symbols ⊆ₘ NonlogicalSymₘ) ∧ₘ (formula ∈ₘ RelFormulaCodeₘ(symbols))) ∧ₘ (∀ₘ[SetSort.set, 737],
      ∀ₘ[SetSort.set, 738],
        ∀ₘ[SetSort.set, 739], ((structureₘ(
              x#737, x#738, symbols) ∧ₘ
            term_evaluationₘ(
              x#737, x#738, symbols, x#739)) ⟶ₘ
            true_inₘ(
              x#737, x#738, symbols, x#739,
              formula)))
/-- 语义后承与普遍真公式的联合定义公理。 -/
def semantic_truth_definition_axiom :
    SetFormula := ((∀ₘ[SetSort.set, 0],
      ∀ₘ[SetSort.set, 1],
        ∀ₘ[SetSort.set, 2], ((semantic_consequenceₘ(
              x#0, x#1, x#2)) ↔ₘ
            logical_consequence_condition (x#0) (x#1) (x#2))) ∧ₘ (∀ₘ[SetSort.set, 0],
      ∀ₘ[SetSort.set, 1], ((valid_codeₘ(x#0, x#1)) ↔ₘ
          theorem_condition (x#0) (x#1))))
/-! ## 理论组合 -/
/-- 加入相关公式阶段递归后的理论。 -/
def formula_stage_semantics_theory :
    SetTheory :=
  Theory.insert
    formula_stage_set_definition_axiom
    semantic_interpretation_theory
/-- 加入原子公式满足关系后的理论。 -/
def atomic_satisfaction_semantics_theory :
    SetTheory :=
  Theory.insert
    atomic_satisfaction_definition_axiom
    formula_stage_semantics_theory
/-- 加入阶段满足关系后的理论。 -/
def staged_satisfaction_semantics_theory :
    SetTheory :=
  Theory.insert
    formula_satisfaction_at_stage_definition_axiom
    atomic_satisfaction_semantics_theory
/-- 加入最终满足关系后的理论。 -/
def formula_satisfaction_semantics_theory :
    SetTheory :=
  Theory.insert
    formula_satisfaction_definition_axiom
    staged_satisfaction_semantics_theory
/-- 加入真谓词与模型谓词后的理论。 -/
def tarski_truth_model_theory :
    SetTheory :=
  Theory.insert (truth_definition_axiom ∧ₘ model_definition_axiom)
    formula_satisfaction_semantics_theory
/-- 一阶语义与塔斯基真谓词层的稳定理论入口。 -/
def tarski_truth_theory :
    SetTheory :=
  Theory.insert
    semantic_truth_definition_axiom
    tarski_truth_model_theory
/-! ## proof-carrying 项边界 -/
theorem related_formula_stage_set_term_admissible (symbols stage : SetTerm) (hSymbols : Term.Admissible symbols SetSort.set)
    (hStage : Term.Admissible stage SetSort.set) :
    Term.Admissible (FormulaStageₘ(symbols, stage))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .relatedFormulaStageSet [⟨symbols, by assumption⟩, ⟨stage, by assumption⟩]
      (by rfl) (by rfl)
/-! ## 良构性与闭理论边界 -/
theorem formula_stage_set_definition_axiom_admissible :
    Formula.Admissible
      formula_stage_set_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem atomic_satisfaction_definition_axiom_admissible :
    Formula.Admissible
      atomic_satisfaction_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem formula_satisfaction_at_stage_definition_axiom_admissible :
    Formula.Admissible
      formula_satisfaction_at_stage_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem formula_satisfaction_definition_axiom_admissible :
    Formula.Admissible
      formula_satisfaction_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem truth_model_definition_axiom_admissible :
    Formula.Admissible (truth_definition_axiom ∧ₘ model_definition_axiom) := by
  apply Formula.check_admissible_sound
  native_decide
theorem semantic_truth_definition_axiom_admissible :
    Formula.Admissible
      semantic_truth_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem formula_stage_semantics_theory_admissible :
    Theory.Admissible formula_stage_semantics_theory :=
  Theory.admissible_insert
    formula_stage_set_definition_axiom_admissible
    semantic_interpretation_theory_admissible
theorem atomic_satisfaction_semantics_theory_admissible :
    Theory.Admissible atomic_satisfaction_semantics_theory :=
  Theory.admissible_insert
    atomic_satisfaction_definition_axiom_admissible
    formula_stage_semantics_theory_admissible
theorem staged_satisfaction_semantics_theory_admissible :
    Theory.Admissible staged_satisfaction_semantics_theory :=
  Theory.admissible_insert
    formula_satisfaction_at_stage_definition_axiom_admissible
    atomic_satisfaction_semantics_theory_admissible
theorem formula_satisfaction_semantics_theory_admissible :
    Theory.Admissible formula_satisfaction_semantics_theory :=
  Theory.admissible_insert
    formula_satisfaction_definition_axiom_admissible
    staged_satisfaction_semantics_theory_admissible
theorem tarski_truth_model_theory_admissible :
    Theory.Admissible tarski_truth_model_theory :=
  Theory.admissible_insert
    truth_model_definition_axiom_admissible
    formula_satisfaction_semantics_theory_admissible
theorem tarski_truth_theory_admissible :
    Theory.Admissible tarski_truth_theory :=
  Theory.admissible_insert
    semantic_truth_definition_axiom_admissible
    tarski_truth_model_theory_admissible
@[derive_close_sentence]
theorem formula_stage_semantics_theory_sentence
    {formula : SetFormula} (hFormula : formula_stage_semantics_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact formula_stage_set_definition_axiom_admissible
    · native_decide
  · exact semantic_interpretation_theory_sentence hFormula
@[derive_close_sentence]
theorem atomic_satisfaction_semantics_theory_sentence
    {formula : SetFormula} (hFormula : atomic_satisfaction_semantics_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact atomic_satisfaction_definition_axiom_admissible
    · native_decide
  · exact formula_stage_semantics_theory_sentence hFormula
@[derive_close_sentence]
theorem staged_satisfaction_semantics_theory_sentence
    {formula : SetFormula} (hFormula : staged_satisfaction_semantics_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact formula_satisfaction_at_stage_definition_axiom_admissible
    · native_decide
  · exact atomic_satisfaction_semantics_theory_sentence hFormula
@[derive_close_sentence]
theorem formula_satisfaction_semantics_theory_sentence
    {formula : SetFormula} (hFormula : formula_satisfaction_semantics_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact formula_satisfaction_definition_axiom_admissible
    · native_decide
  · exact staged_satisfaction_semantics_theory_sentence hFormula
@[derive_close_sentence]
theorem tarski_truth_model_theory_sentence
    {formula : SetFormula} (hFormula : tarski_truth_model_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact truth_model_definition_axiom_admissible
    · native_decide
  · exact formula_satisfaction_semantics_theory_sentence hFormula
@[derive_close_sentence]
theorem tarski_truth_theory_sentence
    {formula : SetFormula} (hFormula : tarski_truth_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact semantic_truth_definition_axiom_admissible
    · native_decide
  · exact tarski_truth_model_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem semantic_interpretation_theory_subset_formula_stage_semantics_theory
    {formula : SetFormula} (hFormula : semantic_interpretation_theory formula) :
    formula_stage_semantics_theory formula :=
  Or.inr hFormula
theorem formula_stage_semantics_theory_subset_atomic_satisfaction_semantics_theory
    {formula : SetFormula} (hFormula : formula_stage_semantics_theory formula) :
    atomic_satisfaction_semantics_theory formula :=
  Or.inr hFormula
theorem atomic_satisfaction_semantics_theory_subset_staged_satisfaction_semantics_theory
    {formula : SetFormula} (hFormula : atomic_satisfaction_semantics_theory formula) :
    staged_satisfaction_semantics_theory formula :=
  Or.inr hFormula
theorem staged_satisfaction_semantics_theory_subset_formula_satisfaction_semantics_theory
    {formula : SetFormula} (hFormula : staged_satisfaction_semantics_theory formula) :
    formula_satisfaction_semantics_theory formula :=
  Or.inr hFormula
theorem formula_satisfaction_semantics_theory_subset_tarski_truth_model_theory
    {formula : SetFormula} (hFormula : formula_satisfaction_semantics_theory formula) :
    tarski_truth_model_theory formula :=
  Or.inr hFormula
theorem tarski_truth_model_theory_subset_tarski_truth_theory
    {formula : SetFormula} (hFormula : tarski_truth_model_theory formula) :
    tarski_truth_theory formula :=
  Or.inr hFormula
/-! ## 待证明定理索引 -/
/-!
后续证明层按需处理：
* `FormulaStageₘ` 的存在唯一性、单调性与对完整相关公式集的并覆盖；
* 原子、否定、蕴含和全称量化满足子句的反演及阶段无关性；
* 满足关系的换赋值、代入和自由变量局部性；
* 真谓词的塔斯基真引理、模型的理论包含单调性；
* 普遍真公式、语义后承与演绎关系之间的可靠性和完整性。
命题骨架和定义展开优先由 `prove_auto` 处理；阶段递归、变量改写和满足反演保留
为人类数学可读的结构证明。
-/
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
