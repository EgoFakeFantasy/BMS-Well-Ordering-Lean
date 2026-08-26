import YesMetaZFC.Logic.FirstOrder.FormalSystem.ExpressionEncoding
/-!
# 一阶逻辑公理与推理规则编码
本模块把一阶 Hilbert 逻辑的公理模式和 modus ponens 映射到对象集合论中的公式
编码。实现分为四层：
* 七个纯蕴含/否定命题公理模式；
* 全称特化、全称量词分配和无关量词引入；
* 等同律与恒等律；
* 基础模式在全称量化下生成的最小闭包，以及 modus ponens 关系。
文献中的 `CYSa` 至 `CYSg`、`THYL`、`QCFP`、`LCYR`、`DTLv`、`HDLv`、
`LJGL₀`、`LJGL`、`KTHn` 与 `MP` 仅在注释中保留为检索索引。
纸面上的 `L₁` 至 `L₁₂` 映射、值域和递推序列不作为新的原子函数进入签名。
这些映射真正使用的是其像集，因此本模块直接定义相应模式集合。`LJGL` 的逐层
全称闭包也改写为等价的最小闭包规格，以便后续直接使用结构归纳和自动化。
本模块只建立定义公理、理论链和 proof-carrying 良构性边界。各模式属于逻辑
公理集合、闭包反演、代入引理以及 MP 保持公式编码等定理留给后续证明模块。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
/-! ## 七个命题公理模式 -/
/-- 蕴含分配公理 `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`。 -/
abbrev implication_distribution_axiom_code_term (antecedent middle consequent : SetTerm) :
    SetTerm :=
  imp_codeₘ(
    imp_codeₘ(antecedent,
      imp_codeₘ(middle, consequent)),
    imp_codeₘ(
      imp_codeₘ(antecedent, middle),
      imp_codeₘ(antecedent, consequent)))
/-- 自蕴含模式 `φ → (φ → φ)`。 -/
abbrev self_implication_axiom_code_term (formula : SetTerm) :
    SetTerm :=
  imp_codeₘ(formula, imp_codeₘ(formula, formula))
/-- 弱化模式 `φ → (ψ → φ)`。 -/
abbrev weakening_axiom_code_term (formula extra : SetTerm) :
    SetTerm :=
  imp_codeₘ(formula, imp_codeₘ(extra, formula))
/-- 矛盾前件模式 `φ → (¬φ → ψ)`。 -/
abbrev contradiction_axiom_code_term (formula conclusion : SetTerm) :
    SetTerm :=
  imp_codeₘ(
    formula,
    imp_codeₘ(neg_codeₘ(formula), conclusion))
/-- 经典模式 `(¬φ → φ) → φ`。 -/
abbrev classical_axiom_code_term (formula : SetTerm) :
    SetTerm :=
  imp_codeₘ(
    imp_codeₘ(neg_codeₘ(formula), formula),
    formula)
/-- 爆炸律模式 `¬φ → (φ → ψ)`。 -/
abbrev explosion_axiom_code_term (formula conclusion : SetTerm) :
    SetTerm :=
  imp_codeₘ(
    neg_codeₘ(formula),
    imp_codeₘ(formula, conclusion))
/-- 分类讨论模式 `(φ → ψ) → ((¬φ → ψ) → ψ)`。 -/
abbrev case_analysis_axiom_code_term (formula conclusion : SetTerm) :
    SetTerm :=
  imp_codeₘ(
    imp_codeₘ(formula, conclusion),
    imp_codeₘ(
      imp_codeₘ(neg_codeₘ(formula), conclusion),
      conclusion))
/-- 第一类命题公理模式条件；文献索引为 `CYSa`。 -/
def implication_distribution_axiom_condition (code : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 400],
    ∃ₘ[SetSort.set, 401],
      ∃ₘ[SetSort.set, 402], (((formula_codeₘ(x#400) ∧ₘ
            formula_codeₘ(x#401)) ∧ₘ
            formula_codeₘ(x#402)) ∧ₘ (code ≐ₘ
            implication_distribution_axiom_code_term (x#400) (x#401) (x#402)))
/-- 第二类命题公理模式条件；文献索引为 `CYSb`。 -/
def self_implication_axiom_condition (code : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 403], (formula_codeₘ(x#403) ∧ₘ (code ≐ₘ
        self_implication_axiom_code_term (x#403)))
/-- 第三类命题公理模式条件；文献索引为 `CYSc`。 -/
def weakening_axiom_condition (code : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 404],
    ∃ₘ[SetSort.set, 405], ((formula_codeₘ(x#404) ∧ₘ
          formula_codeₘ(x#405)) ∧ₘ (code ≐ₘ
          weakening_axiom_code_term (x#404) (x#405)))
/-- 第四类命题公理模式条件；文献索引为 `CYSd`。 -/
def contradiction_axiom_condition (code : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 406],
    ∃ₘ[SetSort.set, 407], ((formula_codeₘ(x#406) ∧ₘ
          formula_codeₘ(x#407)) ∧ₘ (code ≐ₘ
          contradiction_axiom_code_term (x#406) (x#407)))
/-- 第五类命题公理模式条件；文献索引为 `CYSe`。 -/
def classical_axiom_condition (code : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 408], (formula_codeₘ(x#408) ∧ₘ (code ≐ₘ
        classical_axiom_code_term (x#408)))
/-- 第六类命题公理模式条件；文献索引为 `CYSf`。 -/
def explosion_axiom_condition (code : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 409],
    ∃ₘ[SetSort.set, 410], ((formula_codeₘ(x#409) ∧ₘ
          formula_codeₘ(x#410)) ∧ₘ (code ≐ₘ
          explosion_axiom_code_term (x#409) (x#410)))
/-- 第七类命题公理模式条件；文献索引为 `CYSg`。 -/
def case_analysis_axiom_condition (code : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 411],
    ∃ₘ[SetSort.set, 412], ((formula_codeₘ(x#411) ∧ₘ
          formula_codeₘ(x#412)) ∧ₘ (code ≐ₘ
          case_analysis_axiom_code_term (x#411) (x#412)))
/-- 七类命题公理模式集合的联合定义公理。 -/
def propositional_axiom_schema_definition_axiom :
    SetFormula := (∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ ImpDistribAxiomsₘ) ↔ₘ
      implication_distribution_axiom_condition (x#0))) ∧ₘ ((∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ SelfImpAxiomsₘ) ↔ₘ
      self_implication_axiom_condition (x#0))) ∧ₘ ((∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ WeakeningAxiomsₘ) ↔ₘ
      weakening_axiom_condition (x#0))) ∧ₘ ((∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ ContradictionAxiomsₘ) ↔ₘ
      contradiction_axiom_condition (x#0))) ∧ₘ ((∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ ClassicalAxiomsₘ) ↔ₘ
      classical_axiom_condition (x#0))) ∧ₘ ((∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ ExplosionAxiomsₘ) ↔ₘ
      explosion_axiom_condition (x#0))) ∧ₘ (∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ CaseAnalysisAxiomsₘ) ↔ₘ
        case_analysis_axiom_condition (x#0))))))))
/-! ## 可代入性 -/
/--
替换项可自由代入 `boundVariable` 在 `formula` 中的自由出现位置。
替换项中出现的每个变量都不能在待替换位置上落入同名量词的作用域。
-/
def substitutable_condition (boundVariable replacement formula : SetTerm) :
    SetFormula := ((boundVariable ∈ₘ VarSymₘ) ∧ₘ (term_codeₘ(replacement) ∧ₘ
      formula_codeₘ(formula))) ∧ₘ (∀ₘ[SetSort.set, 420], ((x#420 ∈ₘ varsₘ(replacement)) ⟶ₘ (∀ₘ[SetSort.set, 421], (free_occurrence_position_condition
              boundVariable formula (x#421) ⟶ₘ
            ¬ₘ (quantifier_body_position_condition (x#420) formula (x#421))))))
/-- 可代入性谓词定义公理；文献索引为 `KTHn`。 -/
def substitutable_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2], ((substitutableₘ(x#0, x#1, x#2)) ↔ₘ
          substitutable_condition (x#0) (x#1) (x#2))
/-! ## 量词公理模式 -/
/--
全称特化模式的规范外壳。
`universalCode` 与 `resultCode` 已分别是 canonical 全称闭包和实际打开结果的代码；
二者之间的共享源码、binder 深度平移与逐 token 代入由
`specialization_axiom_condition` 统一验证。
-/
abbrev specialization_axiom_code_term (universalCode resultCode : SetTerm) :
    SetTerm :=
  imp_codeₘ(universalCode, resultCode)
/-- 全称量词分配模式。 -/
abbrev quantifier_distribution_axiom_code_term (boundVariable antecedent consequent : SetTerm) :
    SetTerm :=
  imp_codeₘ(
    forall_codeₘ(
      boundVariable,
      imp_codeₘ(antecedent, consequent)),
    imp_codeₘ(
      forall_codeₘ(boundVariable, antecedent),
      forall_codeₘ(boundVariable, consequent)))
/-! ## 规范 binder 深度平移 -/
/--
为规范 binder 平移条件中的内部见证统一选择严格新鲜的编号。
该关系会直接嵌入量词公理模式，因此不能依赖固定保留编号；见证编号必须随左右代码
动态避开其自由支持。
-/
private def canonical_binder_shift_fresh_base (terms : List SetTerm) : FreeVarId :=
  FreshVariable.fresh_id SetSort.set (terms.map fun term => term ≐ₘ term)
/-- 一个 token 数值等于给定闭项列表中的某一项。 -/
private def token_value_in_terms_condition (sourceValue : SetTerm) : List SetTerm → SetFormula
  | [] => Formula.falsum
  | value :: rest =>
      (sourceValue ≐ₘ value) ∨ₘ
        token_value_in_terms_condition sourceValue rest
/--
quotation 中不受 binder 深度影响的九个固定 token。
这里列出八个逻辑符号以及隶属符号；常元、函数、谓词和自由变量由带自然数见证的
分支单独处理。
-/
def canonical_binder_shift_fixed_token_condition (sourceValue : SetTerm) : SetFormula :=
  token_value_in_terms_condition sourceValue
    [logical_symbol_number_term .equality,
      logical_symbol_number_term .negation,
      logical_symbol_number_term .implication,
      logical_symbol_number_term .universal,
      logical_symbol_number_term .leftParenthesis,
      logical_symbol_number_term .rightParenthesis,
      logical_symbol_number_term .existential,
      logical_symbol_number_term .conjunction,
      membership_symbol_number_term]
/--
固定 token 枚举不引入入口 token 之外的自由支持。

该等价把私有有限析取的语法细节封装在定义模块内。
-/
@[simp]
theorem mem_freeSupport_canonical_binder_shift_fixed_token_condition_iff
    (freeVariable : FreeVariable signature)
    (sourceValue : SetTerm) :
    freeVariable ∈
        Formula.freeSupport
          (canonical_binder_shift_fixed_token_condition sourceValue) ↔
      freeVariable ∈ Term.freeSupport sourceValue := by
  simp [canonical_binder_shift_fixed_token_condition,
    token_value_in_terms_condition,
    Formula.freeSupport, Term.freeSupport,
    Term.freeSupportList,
    finite_numeral_term_freeSupport]

/--
固定 token 枚举对自由变量替换逐项自然。
该引理把私有的有限析取实现封装在本模块内；对象表示层只需看到公开条件本身，而不
必依赖固定 token 列表的递归细节。
-/
@[simp]
theorem canonical_binder_shift_fixed_token_condition_substituteFree (id : FreeVarId) (replacement sourceValue : SetTerm) :
    Formula.substituteFree SetSort.set id replacement (canonical_binder_shift_fixed_token_condition sourceValue) =
      canonical_binder_shift_fixed_token_condition (Term.substituteFree SetSort.set id replacement sourceValue) := by
  have hNumeralFixed (value : Nat) :
      Term.substituteFree SetSort.set id replacement (numₘ(value)) =
        numₘ(value) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement (numₘ(value)) (by simp [finite_numeral_term_freeSupport])
  simp [canonical_binder_shift_fixed_token_condition,
    token_value_in_terms_condition,
    Formula.substituteFree, Term.substituteFree,
    hNumeralFixed]
/--
固定 token 枚举对 de Bruijn 打开逐项自然。
这条自然性用于把外层存在量词见证穿过固定 token 分支；有限析取的实现细节仍被封装
在本模块中。
-/
@[simp]
theorem canonical_binder_shift_fixed_token_condition_openAt (depth : Nat) (replacement sourceValue : SetTerm) :
    Formula.openAt SetSort.set depth replacement (canonical_binder_shift_fixed_token_condition sourceValue) =
      canonical_binder_shift_fixed_token_condition (Term.openAt SetSort.set depth replacement sourceValue) := by
  have hNumeralFixed (value : Nat) :
      Term.openAt SetSort.set depth replacement (numₘ(value)) =
        numₘ(value) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (numₘ(value)) (finite_numeral_term_admissible value).2
  simp [canonical_binder_shift_fixed_token_condition,
    token_value_in_terms_condition,
    Formula.openAt, Term.openAt,
    hNumeralFixed]
/--
固定 token 枚举对自由变量关闭逐项自然。
固定 token 的数值项既不含待关闭自由变量，也没有悬空 de Bruijn 变量，因此关闭操作
只作用于枚举条件的入口项。
-/
@[simp]
theorem canonical_binder_shift_fixed_token_condition_closeFreeAt (id : FreeVarId) (depth : Nat) (sourceValue : SetTerm) :
    Formula.closeFreeAt SetSort.set id depth (canonical_binder_shift_fixed_token_condition sourceValue) =
      canonical_binder_shift_fixed_token_condition (Term.closeFreeAt SetSort.set id depth sourceValue) := by
  have hNumeralFixed (value : Nat) :
      Term.closeFreeAt SetSort.set id depth (numₘ(value)) =
        numₘ(value) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth (numₘ(value)) (finite_numeral_term_admissible value).2 (by simp [finite_numeral_term_freeSupport])
  simp [canonical_binder_shift_fixed_token_condition,
    token_value_in_terms_condition,
    Formula.closeFreeAt, Term.closeFreeAt,
    hNumeralFixed]
/--
一个 token 在 quotation 入口深度增加一层时的精确同步关系。
* 固定逻辑 token、隶属 token、常元、函数、谓词和偶数自由变量保持不变；
* 奇数规范 binder 名 `2d+1` 平移为 `2d+3`；
* 所有可变分支都携带自然数见证，因而后续可以做对象层反演。
-/
def canonical_binder_shift_token_condition_with_ids (sourceValue targetValue : SetTerm) (freeId boundDepthId constantId
      functionArityId functionIndexId
      predicateArityId predicateIndexId : FreeVarId) :
    SetFormula :=
  let fixedCase :=
    canonical_binder_shift_fixed_token_condition sourceValue ∧ₘ (targetValue ≐ₘ sourceValue)
  let freeCase :=
    ∃ₘ[SetSort.set, freeId], ((((x#freeId ∈ₘ ωₘ) ∧ₘ
          (x#freeId ∈ₘ Sₘ(sourceValue))) ∧ₘ (sourceValue ≐ₘ
            variable_symbol_number_term (numₘ(2) *ₘ x#freeId))) ∧ₘ
          (targetValue ≐ₘ sourceValue))
  let boundCase :=
    ∃ₘ[SetSort.set, boundDepthId], ((((x#boundDepthId ∈ₘ ωₘ) ∧ₘ
          (x#boundDepthId ∈ₘ Sₘ(sourceValue))) ∧ₘ (sourceValue ≐ₘ
            variable_symbol_number_term (Sₘ(numₘ(2) *ₘ x#boundDepthId)))) ∧ₘ
          (targetValue ≐ₘ variable_symbol_number_term (Sₘ(Sₘ(Sₘ(
            numₘ(2) *ₘ x#boundDepthId))))))
  let constantCase :=
    ∃ₘ[SetSort.set, constantId], (((x#constantId ∈ₘ ωₘ) ∧ₘ (sourceValue ≐ₘ
          constant_symbol_number_term (x#constantId))) ∧ₘ (targetValue ≐ₘ sourceValue))
  let functionCase :=
    ∃ₘ[SetSort.set, functionArityId],
      ∃ₘ[SetSort.set, functionIndexId], ((((x#functionArityId ∈ₘ ωₘ) ∧ₘ (x#functionIndexId ∈ₘ ωₘ)) ∧ₘ (sourceValue ≐ₘ
            coded_function_symbol_number_term (x#functionArityId) (x#functionIndexId))) ∧ₘ (targetValue ≐ₘ sourceValue))
  let predicateCase :=
    ∃ₘ[SetSort.set, predicateArityId],
      ∃ₘ[SetSort.set, predicateIndexId], ((((x#predicateArityId ∈ₘ ωₘ) ∧ₘ (x#predicateIndexId ∈ₘ ωₘ)) ∧ₘ (sourceValue ≐ₘ
            coded_predicate_symbol_number_term (x#predicateArityId) (x#predicateIndexId))) ∧ₘ (targetValue ≐ₘ sourceValue))
  fixedCase ∨ₘ (freeCase ∨ₘ (boundCase ∨ₘ (constantCase ∨ₘ (functionCase ∨ₘ predicateCase))))
/-- 自动选择内部见证编号的 token 深度平移关系。 -/
def canonical_binder_shift_token_condition (sourceValue targetValue : SetTerm) : SetFormula :=
  let freeId :=
    canonical_binder_shift_fresh_base
      [sourceValue, targetValue]
  canonical_binder_shift_token_condition_with_ids
    sourceValue targetValue
    freeId (freeId + 1) (freeId + 2) (freeId + 3) (freeId + 4) (freeId + 5) (freeId + 6)
/--
两个公式代码逐点实现一次规范 binder 深度平移。
左右代码必须具有相同定义域，并在每个 token 位置满足上面的精确同步关系。该定义只
依赖公共公式码和有限序列接口，因此可供任意可编号 FormalSystem 扩展签名复用。
-/
def canonical_binder_shift_code_condition_with_ids (sourceCode targetCode : SetTerm) (indexId freeId boundDepthId constantId
      functionArityId functionIndexId
      predicateArityId predicateIndexId : FreeVarId) :
    SetFormula := (((formula_codeₘ(sourceCode) ∧ₘ
      formula_codeₘ(targetCode)) ∧ₘ (domₘ(sourceCode) ≐ₘ domₘ(targetCode))) ∧ₘ (∀ₘ[SetSort.set, indexId], (x#indexId ∈ₘ domₘ(sourceCode)) ⟶ₘ
        canonical_binder_shift_token_condition_with_ids (sourceCode ·ₘ x#indexId) (targetCode ·ₘ x#indexId)
          freeId boundDepthId constantId
          functionArityId functionIndexId
          predicateArityId predicateIndexId))
/--
自动选择逐点指标及六类 token 见证编号的规范 binder 深度平移关系。
整条代码关系只做一次统一新鲜分配；这避免逐点公式在等词运输时重新计算内部编号，
也是后续反演定理稳定识别各分支的前提。
-/
def canonical_binder_shift_code_condition (sourceCode targetCode : SetTerm) : SetFormula :=
  let freshBase :=
    canonical_binder_shift_fresh_base
      [sourceCode, targetCode]
  canonical_binder_shift_code_condition_with_ids
    sourceCode targetCode
    freshBase (freshBase + 1) (freshBase + 2) (freshBase + 3) (freshBase + 4) (freshBase + 5) (freshBase + 6) (freshBase + 7)
/-- 固定 token 的有限枚举保持入口项的公式 admissibility。 -/
theorem canonical_binder_shift_fixed_token_condition_admissible (sourceValue : SetTerm) (hSource : Term.Admissible sourceValue SetSort.set) :
    Formula.Admissible (canonical_binder_shift_fixed_token_condition sourceValue) := by
  simp only [canonical_binder_shift_fixed_token_condition,
    token_value_in_terms_condition]
  exact Formula.Admissible.disj (Formula.Admissible.equal hSource (logical_symbol_number_term_admissible .equality)) (Formula.Admissible.disj
      (Formula.Admissible.equal hSource (logical_symbol_number_term_admissible .negation)) (Formula.Admissible.disj (Formula.Admissible.equal hSource
          (logical_symbol_number_term_admissible .implication)) (Formula.Admissible.disj (Formula.Admissible.equal hSource
            (logical_symbol_number_term_admissible .universal)) (Formula.Admissible.disj (Formula.Admissible.equal hSource
              (logical_symbol_number_term_admissible .leftParenthesis)) (Formula.Admissible.disj (Formula.Admissible.equal hSource
                (logical_symbol_number_term_admissible .rightParenthesis)) (Formula.Admissible.disj (Formula.Admissible.equal hSource
                  (logical_symbol_number_term_admissible .existential)) (Formula.Admissible.disj (Formula.Admissible.equal hSource
                    (logical_symbol_number_term_admissible .conjunction)) (Formula.Admissible.disj (Formula.Admissible.equal hSource
                      membership_symbol_number_term_admissible)
                    Formula.Admissible.falsum))))))))
/--
显式编号的单 token binder-shift 条件保持左右值项的 admissibility。
所有存在分支先在自由见证公式上装配，再通过 `exists_closeFreeAt` 关闭对应编号；
因此该边界同时适用于等词运输、具体 numeral 见证和后续关系反演。
-/
theorem canonical_binder_shift_token_condition_with_ids_admissible (sourceValue targetValue : SetTerm) (freeId boundDepthId constantId
      functionArityId functionIndexId
      predicateArityId predicateIndexId : FreeVarId) (hSource : Term.Admissible sourceValue SetSort.set) (hTarget : Term.Admissible targetValue SetSort.set) :
    Formula.Admissible (canonical_binder_shift_token_condition_with_ids
        sourceValue targetValue
        freeId boundDepthId constantId
        functionArityId functionIndexId
        predicateArityId predicateIndexId) := by
  have hTwo : Term.Admissible (numₘ(2)) SetSort.set :=
    finite_numeral_term_admissible 2
  have hFixedCase :
      Formula.Admissible (canonical_binder_shift_fixed_token_condition sourceValue ∧ₘ
          targetValue ≐ₘ sourceValue) :=
    Formula.Admissible.conj (canonical_binder_shift_fixed_token_condition_admissible
        sourceValue hSource) (Formula.Admissible.equal hTarget hSource)
  have hFreeWitness :
      Term.Admissible (x#freeId) SetSort.set :=
    set_variable_admissible freeId
  have hFreeIndex :
      Term.Admissible (numₘ(2) *ₘ x#freeId) SetSort.set :=
    natural_multiplication_term_admissible (numₘ(2)) (x#freeId) hTwo hFreeWitness
  have hFreeBody :
      Formula.Admissible ((((x#freeId ∈ₘ ωₘ) ∧ₘ
            x#freeId ∈ₘ Sₘ(sourceValue)) ∧ₘ
          sourceValue ≐ₘ
            variable_symbol_number_term (numₘ(2) *ₘ x#freeId)) ∧ₘ
          targetValue ≐ₘ sourceValue) :=
    Formula.Admissible.conj (Formula.Admissible.conj
      (Formula.Admissible.conj
        (membership_formula_admissible
          hFreeWitness omega_term_admissible)
        (membership_formula_admissible hFreeWitness
          (successor_term_admissible sourceValue hSource)))
      (Formula.Admissible.equal hSource
        (variable_symbol_number_term_admissible
          (numₘ(2) *ₘ x#freeId) hFreeIndex)))
      (Formula.Admissible.equal hTarget hSource)
  have hFreeCase :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set freeId hFreeBody
  have hBoundWitness :
      Term.Admissible (x#boundDepthId) SetSort.set :=
    set_variable_admissible boundDepthId
  have hBoundProduct :
      Term.Admissible (numₘ(2) *ₘ x#boundDepthId) SetSort.set :=
    natural_multiplication_term_admissible (numₘ(2)) (x#boundDepthId) hTwo hBoundWitness
  have hBoundSourceIndex :
      Term.Admissible (Sₘ(numₘ(2) *ₘ x#boundDepthId)) SetSort.set :=
    successor_term_admissible (numₘ(2) *ₘ x#boundDepthId) hBoundProduct
  have hBoundTargetIndex :
      Term.Admissible (Sₘ(Sₘ(Sₘ(numₘ(2) *ₘ x#boundDepthId)))) SetSort.set :=
    successor_term_admissible (Sₘ(Sₘ(numₘ(2) *ₘ x#boundDepthId))) (successor_term_admissible (Sₘ(numₘ(2) *ₘ x#boundDepthId)) (successor_term_admissible
          (numₘ(2) *ₘ x#boundDepthId) hBoundProduct))
  have hBoundBody :
      Formula.Admissible ((((x#boundDepthId ∈ₘ ωₘ) ∧ₘ
            x#boundDepthId ∈ₘ Sₘ(sourceValue)) ∧ₘ
          sourceValue ≐ₘ
            variable_symbol_number_term (Sₘ(numₘ(2) *ₘ x#boundDepthId))) ∧ₘ
          targetValue ≐ₘ
            variable_symbol_number_term (Sₘ(Sₘ(Sₘ(
                numₘ(2) *ₘ x#boundDepthId))))) :=
    Formula.Admissible.conj (Formula.Admissible.conj
      (Formula.Admissible.conj
        (membership_formula_admissible
          hBoundWitness omega_term_admissible)
        (membership_formula_admissible hBoundWitness
          (successor_term_admissible sourceValue hSource)))
      (Formula.Admissible.equal hSource
        (variable_symbol_number_term_admissible
          (Sₘ(numₘ(2) *ₘ x#boundDepthId))
          hBoundSourceIndex)))
      (Formula.Admissible.equal hTarget
        (variable_symbol_number_term_admissible
          (Sₘ(Sₘ(Sₘ(numₘ(2) *ₘ x#boundDepthId))))
          hBoundTargetIndex))
  have hBoundCase :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set boundDepthId hBoundBody
  have hConstantWitness :
      Term.Admissible (x#constantId) SetSort.set :=
    set_variable_admissible constantId
  have hConstantBody :
      Formula.Admissible (((x#constantId ∈ₘ ωₘ) ∧ₘ
            sourceValue ≐ₘ
              constant_symbol_number_term (x#constantId)) ∧ₘ
          targetValue ≐ₘ sourceValue) :=
    Formula.Admissible.conj (Formula.Admissible.conj (membership_formula_admissible
          hConstantWitness omega_term_admissible) (Formula.Admissible.equal hSource (constant_symbol_number_term_admissible (x#constantId) hConstantWitness)))
      (Formula.Admissible.equal hTarget hSource)
  have hConstantCase :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set constantId hConstantBody
  have hFunctionArity :
      Term.Admissible (x#functionArityId) SetSort.set :=
    set_variable_admissible functionArityId
  have hFunctionIndex :
      Term.Admissible (x#functionIndexId) SetSort.set :=
    set_variable_admissible functionIndexId
  have hFunctionBody :
      Formula.Admissible ((((x#functionArityId ∈ₘ ωₘ) ∧ₘ
              x#functionIndexId ∈ₘ ωₘ) ∧ₘ
            sourceValue ≐ₘ
              coded_function_symbol_number_term (x#functionArityId) (x#functionIndexId)) ∧ₘ
          targetValue ≐ₘ sourceValue) :=
    Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (membership_formula_admissible
            hFunctionArity omega_term_admissible) (membership_formula_admissible
            hFunctionIndex omega_term_admissible)) (Formula.Admissible.equal hSource (coded_function_symbol_number_term_admissible
            (x#functionArityId) (x#functionIndexId)
            hFunctionArity hFunctionIndex))) (Formula.Admissible.equal hTarget hSource)
  have hFunctionCase :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set functionArityId <|
        Formula.Admissible.exists_closeFreeAt
          SetSort.set functionIndexId hFunctionBody
  have hPredicateArity :
      Term.Admissible (x#predicateArityId) SetSort.set :=
    set_variable_admissible predicateArityId
  have hPredicateIndex :
      Term.Admissible (x#predicateIndexId) SetSort.set :=
    set_variable_admissible predicateIndexId
  have hPredicateBody :
      Formula.Admissible ((((x#predicateArityId ∈ₘ ωₘ) ∧ₘ
              x#predicateIndexId ∈ₘ ωₘ) ∧ₘ
            sourceValue ≐ₘ
              coded_predicate_symbol_number_term (x#predicateArityId) (x#predicateIndexId)) ∧ₘ
          targetValue ≐ₘ sourceValue) :=
    Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (membership_formula_admissible
            hPredicateArity omega_term_admissible) (membership_formula_admissible
            hPredicateIndex omega_term_admissible)) (Formula.Admissible.equal hSource (coded_predicate_symbol_number_term_admissible
            (x#predicateArityId) (x#predicateIndexId)
            hPredicateArity hPredicateIndex))) (Formula.Admissible.equal hTarget hSource)
  have hPredicateCase :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set predicateArityId <|
        Formula.Admissible.exists_closeFreeAt
          SetSort.set predicateIndexId hPredicateBody
  simpa [canonical_binder_shift_token_condition_with_ids] using
    Formula.Admissible.disj hFixedCase <|
      Formula.Admissible.disj hFreeCase <|
        Formula.Admissible.disj hBoundCase <|
          Formula.Admissible.disj hConstantCase <|
            Formula.Admissible.disj hFunctionCase hPredicateCase
/--
显式编号 binder-shift 条件的纯函数检查证书。
复杂析取只在此处计算一次；下游证明可直接投影各分支证书，避免重复展开整棵公式。
-/
@[formula_check]
theorem canonical_binder_shift_token_condition_with_ids_check
    (sourceValue targetValue : SetTerm)
    (freeId boundDepthId constantId functionArityId functionIndexId
      predicateArityId predicateIndexId : FreeVarId)
    (hSource : Term.CheckCertificate sourceValue SetSort.set)
    (hTarget : Term.CheckCertificate targetValue SetSort.set) :
    Formula.CheckCertificate
      (canonical_binder_shift_token_condition_with_ids
        sourceValue targetValue
        freeId boundDepthId constantId
        functionArityId functionIndexId
        predicateArityId predicateIndexId) :=
  Formula.check_admissible_complete <|
    canonical_binder_shift_token_condition_with_ids_admissible
      sourceValue targetValue
      freeId boundDepthId constantId
      functionArityId functionIndexId
      predicateArityId predicateIndexId
      hSource.admissible hTarget.admissible
/-- 自动新鲜编号封装保持单 token 条件的 admissibility。 -/
theorem canonical_binder_shift_token_condition_admissible (sourceValue targetValue : SetTerm) (hSource : Term.Admissible sourceValue SetSort.set)
    (hTarget : Term.Admissible targetValue SetSort.set) :
    Formula.Admissible (canonical_binder_shift_token_condition
        sourceValue targetValue) := by
  simpa [canonical_binder_shift_token_condition] using
    canonical_binder_shift_token_condition_with_ids_admissible
      sourceValue targetValue (canonical_binder_shift_fresh_base
        [sourceValue, targetValue]) (canonical_binder_shift_fresh_base
        [sourceValue, targetValue] + 1) (canonical_binder_shift_fresh_base
        [sourceValue, targetValue] + 2) (canonical_binder_shift_fresh_base
        [sourceValue, targetValue] + 3) (canonical_binder_shift_fresh_base
        [sourceValue, targetValue] + 4) (canonical_binder_shift_fresh_base
        [sourceValue, targetValue] + 5) (canonical_binder_shift_fresh_base
        [sourceValue, targetValue] + 6)
      hSource hTarget
/-- 自动新鲜编号封装下的 binder-shift 条件检查证书。 -/
@[formula_check]
theorem canonical_binder_shift_token_condition_check
    (sourceValue targetValue : SetTerm)
    (hSource : Term.CheckCertificate sourceValue SetSort.set)
    (hTarget : Term.CheckCertificate targetValue SetSort.set) :
    Formula.CheckCertificate
      (canonical_binder_shift_token_condition sourceValue targetValue) :=
  Formula.check_admissible_complete <|
    canonical_binder_shift_token_condition_admissible
      sourceValue targetValue hSource.admissible hTarget.admissible
/-- 显式编号的整代码 binder-shift 条件保持左右代码项的 admissibility。 -/
theorem canonical_binder_shift_code_condition_with_ids_admissible (sourceCode targetCode : SetTerm) (indexId freeId boundDepthId constantId
      functionArityId functionIndexId
      predicateArityId predicateIndexId : FreeVarId) (hSource : Term.Admissible sourceCode SetSort.set) (hTarget : Term.Admissible targetCode SetSort.set) :
    Formula.Admissible (canonical_binder_shift_code_condition_with_ids
        sourceCode targetCode
        indexId freeId boundDepthId constantId
        functionArityId functionIndexId
        predicateArityId predicateIndexId) := by
  have hIndex : Term.Admissible (x#indexId) SetSort.set :=
    set_variable_admissible indexId
  have hSourceDomain :
      Term.Admissible (domₘ(sourceCode)) SetSort.set :=
    domain_term_admissible sourceCode hSource
  have hTargetDomain :
      Term.Admissible (domₘ(targetCode)) SetSort.set :=
    domain_term_admissible targetCode hTarget
  have hSourceValue :
      Term.Admissible (sourceCode ·ₘ x#indexId) SetSort.set :=
    function_application_term_admissible
      sourceCode (x#indexId) hSource hIndex
  have hTargetValue :
      Term.Admissible (targetCode ·ₘ x#indexId) SetSort.set :=
    function_application_term_admissible
      targetCode (x#indexId) hTarget hIndex
  have hPointBody :
      Formula.Admissible ((x#indexId ∈ₘ domₘ(sourceCode)) ⟶ₘ
          canonical_binder_shift_token_condition_with_ids (sourceCode ·ₘ x#indexId) (targetCode ·ₘ x#indexId)
            freeId boundDepthId constantId
            functionArityId functionIndexId
            predicateArityId predicateIndexId) :=
    Formula.Admissible.imp (membership_formula_admissible hIndex hSourceDomain) (canonical_binder_shift_token_condition_with_ids_admissible
        (sourceCode ·ₘ x#indexId) (targetCode ·ₘ x#indexId)
        freeId boundDepthId constantId
        functionArityId functionIndexId
        predicateArityId predicateIndexId
        hSourceValue hTargetValue)
  have hPointwise :
      Formula.Admissible (∀ₘ[SetSort.set, indexId], (x#indexId ∈ₘ domₘ(sourceCode)) ⟶ₘ
            canonical_binder_shift_token_condition_with_ids (sourceCode ·ₘ x#indexId) (targetCode ·ₘ x#indexId)
              freeId boundDepthId constantId
              functionArityId functionIndexId
              predicateArityId predicateIndexId) :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set indexId hPointBody
  exact Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (is_formula_code_formula_admissible hSource)
        (is_formula_code_formula_admissible hTarget)) (Formula.Admissible.equal hSourceDomain hTargetDomain))
    hPointwise
/-- 显式编号的整代码 binder-shift 条件由左右代码项证书直接计算。 -/
@[formula_check]
theorem canonical_binder_shift_code_condition_with_ids_check
    (sourceCode targetCode : SetTerm)
    (indexId freeId boundDepthId constantId
      functionArityId functionIndexId
      predicateArityId predicateIndexId : FreeVarId)
    (hSource : Term.CheckCertificate sourceCode SetSort.set)
    (hTarget : Term.CheckCertificate targetCode SetSort.set) :
    Formula.CheckCertificate
      (canonical_binder_shift_code_condition_with_ids
        sourceCode targetCode
        indexId freeId boundDepthId constantId
        functionArityId functionIndexId
        predicateArityId predicateIndexId) :=
  Formula.check_admissible_complete <|
    canonical_binder_shift_code_condition_with_ids_admissible
      sourceCode targetCode
      indexId freeId boundDepthId constantId
      functionArityId functionIndexId
      predicateArityId predicateIndexId
      hSource.admissible hTarget.admissible
/-- 自动新鲜编号封装保持整代码条件的 admissibility。 -/
theorem canonical_binder_shift_code_condition_admissible (sourceCode targetCode : SetTerm) (hSource : Term.Admissible sourceCode SetSort.set)
    (hTarget : Term.Admissible targetCode SetSort.set) :
    Formula.Admissible (canonical_binder_shift_code_condition
        sourceCode targetCode) := by
  simpa [canonical_binder_shift_code_condition] using
    canonical_binder_shift_code_condition_with_ids_admissible
      sourceCode targetCode (canonical_binder_shift_fresh_base
        [sourceCode, targetCode]) (canonical_binder_shift_fresh_base
        [sourceCode, targetCode] + 1) (canonical_binder_shift_fresh_base
        [sourceCode, targetCode] + 2) (canonical_binder_shift_fresh_base
        [sourceCode, targetCode] + 3) (canonical_binder_shift_fresh_base
        [sourceCode, targetCode] + 4) (canonical_binder_shift_fresh_base
        [sourceCode, targetCode] + 5) (canonical_binder_shift_fresh_base
        [sourceCode, targetCode] + 6) (canonical_binder_shift_fresh_base
        [sourceCode, targetCode] + 7)
      hSource hTarget
/--
规范 quotation 最外层 binder 的变量符号码。
规范命名把深度 `0` 的 binder 编为名字 `1`；逻辑规则编码层只记录这个公开数值，
不依赖上层 quotation 模块。
-/
abbrev canonical_outer_binder_variable_code_term : SetTerm :=
  var_codeₘ(numₘ(1))
/--
`variableCode` 是规范 quotation 使用的某个自由变量符号码。
自由变量名固定取偶数 `2 * index`；这与奇数域中的 canonical binder 名严格分离，
也为闭包与打开操作保留从对象码恢复外部自由变量编号的唯一通道。
-/
def canonical_free_variable_code_condition_with_id (variableCode : SetTerm) (indexId : FreeVarId) :
    SetFormula :=
  ∃ₘ[SetSort.set, indexId], ((x#indexId ∈ₘ ωₘ) ∧ₘ (variableCode ≐ₘ
        var_codeₘ(numₘ(2) *ₘ x#indexId)))
/-- 自动选择内部编号的规范自由变量符号码条件。 -/
def canonical_free_variable_code_condition (variableCode : SetTerm) :
    SetFormula :=
  canonical_free_variable_code_condition_with_id
    variableCode 470
/--
一次 locally nameless 全称闭包在对象公式码上的完整规范关系。
该关系依次提升源码中的既有 binder、把指定偶数自由变量替换为最外层奇数 binder，
并验证所得公式体后拼接全称量词。量词特化与逻辑公理全称闭包共同复用这一关系。
-/
def canonical_forall_closure_code_condition_with_ids (sourceCode variableCode targetCode : SetTerm) (shiftedCodeId bodyCodeId
      shiftIndexId shiftFreeId shiftBoundDepthId shiftConstantId
      shiftFunctionArityId shiftFunctionIndexId
      shiftPredicateArityId shiftPredicateIndexId
      freeIndexId : FreeVarId) :
    SetFormula :=
  ∃ₘ[SetSort.set, shiftedCodeId],
    ∃ₘ[SetSort.set, bodyCodeId], (((canonical_free_variable_code_condition_with_id
            variableCode freeIndexId ∧ₘ
          canonical_binder_shift_code_condition_with_ids
            sourceCode (x#shiftedCodeId)
            shiftIndexId shiftFreeId shiftBoundDepthId shiftConstantId
            shiftFunctionArityId shiftFunctionIndexId
            shiftPredicateArityId shiftPredicateIndexId) ∧ₘ (code_substitution_spec (x#shiftedCodeId) variableCode
            canonical_outer_binder_variable_code_term (x#bodyCodeId) ∧ₘ
          formula_codeₘ(x#bodyCodeId))) ∧ₘ (targetCode ≐ₘ
          forall_codeₘ(
            canonical_outer_binder_variable_code_term,
            x#bodyCodeId)))
/-- 固定互异内部编号的 canonical 全称闭包关系。 -/
def canonical_forall_closure_code_condition (sourceCode variableCode targetCode : SetTerm) :
    SetFormula :=
  canonical_forall_closure_code_condition_with_ids
    sourceCode variableCode targetCode
    460 461
    462 463 464 465 466 467 468 469
    470
/--
无关量词引入模式的规范代码。
前件与量词体必须分别给码：进入新 binder 后，原公式内部既有 binder 的规范名字会
整体平移，因此二者通常不是同一个对象项。
-/
abbrev vacuous_quantifier_axiom_code_term (boundVariable antecedent body : SetTerm) :
    SetTerm :=
  imp_codeₘ(
    antecedent,
    forall_codeₘ(boundVariable, body))
/--
全称特化公理模式条件。
同一个 exposed 源公式一方面经 canonical 全称闭包得到前件，另一方面把同一个规范
自由变量替换为可自由代入的项后得到后件；这条交换菱形精确对应 locally nameless
`(∀ φ) → openAt τ φ` 的真实 quotation。
-/
def specialization_axiom_condition (code : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 430],
    ∃ₘ[SetSort.set, 431],
      ∃ₘ[SetSort.set, 432],
        ∃ₘ[SetSort.set, 433],
          ∃ₘ[SetSort.set, 434],
            (((((formula_codeₘ(x#430) ∧ₘ term_codeₘ(x#432)) ∧ₘ
                  (formula_codeₘ(x#433) ∧ₘ formula_codeₘ(x#434))) ∧ₘ
                canonical_forall_closure_code_condition
                  (x#430) (x#431) (x#433)) ∧ₘ
              substitutableₘ(x#431, x#432, x#430)) ∧ₘ
            code_substitution_spec (x#430) (x#431) (x#432) (x#434)) ∧ₘ
            (code ≐ₘ specialization_axiom_code_term (x#433) (x#434))
/-- 全称量词分配公理模式条件。 -/
def quantifier_distribution_axiom_condition (code : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 433],
    ∃ₘ[SetSort.set, 434],
      ∃ₘ[SetSort.set, 435], ((((x#433 ∈ₘ VarSymₘ) ∧ₘ
            formula_codeₘ(x#434)) ∧ₘ
            formula_codeₘ(x#435)) ∧ₘ (code ≐ₘ
            quantifier_distribution_axiom_code_term (x#433) (x#434) (x#435)))
/--
无关量词引入公理模式条件。
该条件只识别规范 quotation：外层 binder 固定为名字 `1`，量词体代码则必须是前件
代码在入口深度增加一层后的逐 token 平移。后一个条件已经同时保证两侧是公式码，
无需再重复携带独立的公式码或自由出现前提。
-/
def vacuous_quantifier_axiom_condition (code : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∃ₘ[SetSort.set], ((canonical_binder_shift_code_condition_with_ids (bₛ#1) (bₛ#0)
          438 439 440 441 442 443 444 445) ∧ₘ (code ≐ₘ
          vacuous_quantifier_axiom_code_term
            canonical_outer_binder_variable_code_term (bₛ#1) (bₛ#0)))
/-- 三类量词公理模式集合的联合定义公理。 -/
def quantifier_axiom_schema_definition_axiom :
    SetFormula := (∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ SpecializationAxiomsₘ) ↔ₘ
      specialization_axiom_condition (x#0))) ∧ₘ ((∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ ForallDistribAxiomsₘ) ↔ₘ
      quantifier_distribution_axiom_condition (x#0))) ∧ₘ (∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ VacuousForallAxiomsₘ) ↔ₘ
        vacuous_quantifier_axiom_condition (x#0))))
/-! ## 等式公理模式 -/
/-- 等同律模式 `(x = y) → (φ → φ[x := y])`。 -/
abbrev equality_substitution_axiom_code_term (boundVariable replacementVariable body : SetTerm) :
    SetTerm :=
  imp_codeₘ(
    eq_codeₘ(boundVariable, replacementVariable),
    imp_codeₘ(
      body,
      subst_codeₘ(
        body, boundVariable, replacementVariable)))
/-- 恒等律模式 `x = x`。 -/
abbrev equality_reflexivity_axiom_code_term (boundVariable : SetTerm) :
    SetTerm :=
  eq_codeₘ(boundVariable, boundVariable)
/-- 等同律公理模式条件。 -/
def equality_substitution_axiom_condition (code : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 440],
    ∃ₘ[SetSort.set, 441],
      ∃ₘ[SetSort.set, 442], (((((x#440 ∈ₘ VarSymₘ) ∧ₘ (x#441 ∈ₘ VarSymₘ)) ∧ₘ
            formula_codeₘ(x#442)) ∧ₘ
            substitutableₘ(
              x#440, x#441, x#442)) ∧ₘ (code ≐ₘ
            equality_substitution_axiom_code_term (x#440) (x#441) (x#442)))
/-- 恒等律公理模式条件。 -/
def equality_reflexivity_axiom_condition (code : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set, 443], ((x#443 ∈ₘ VarSymₘ) ∧ₘ (code ≐ₘ
        equality_reflexivity_axiom_code_term (x#443)))
/-- 等同律与恒等律模式集合的联合定义公理。 -/
def equality_axiom_schema_definition_axiom :
    SetFormula := (∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ EqualitySubstAxiomsₘ) ↔ₘ
      equality_substitution_axiom_condition (x#0))) ∧ₘ (∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ EqualityReflAxiomsₘ) ↔ₘ
        equality_reflexivity_axiom_condition (x#0)))
/-! ## 逻辑公理集合与全称闭包 -/
/-- `code` 属于十二类基础逻辑公理模式之一。 -/
def base_logical_axiom_condition (code : SetTerm) :
    SetFormula := (code ∈ₘ ImpDistribAxiomsₘ) ∨ₘ ((code ∈ₘ SelfImpAxiomsₘ) ∨ₘ ((code ∈ₘ WeakeningAxiomsₘ) ∨ₘ ((code ∈ₘ ContradictionAxiomsₘ) ∨ₘ
          ((code ∈ₘ ClassicalAxiomsₘ) ∨ₘ ((code ∈ₘ ExplosionAxiomsₘ) ∨ₘ ((code ∈ₘ CaseAnalysisAxiomsₘ) ∨ₘ ((code ∈ₘ SpecializationAxiomsₘ) ∨ₘ
                  ((code ∈ₘ ForallDistribAxiomsₘ) ∨ₘ ((code ∈ₘ VacuousForallAxiomsₘ) ∨ₘ ((code ∈ₘ EqualitySubstAxiomsₘ) ∨ₘ
                        (code ∈ₘ EqualityReflAxiomsₘ)))))))))))
/-- 基础逻辑公理编码集合定义公理；文献索引为 `LJGL₀`。 -/
def base_logical_axiom_set_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ BaseLogicAxiomsₘ) ↔ₘ
      base_logical_axiom_condition (x#0))
/-- 显式编号的规范自由变量码条件保持参数项的 admissibility。 -/
theorem canonical_free_variable_code_condition_with_id_admissible (variableCode : SetTerm) (indexId : FreeVarId) (hVariableCode :
      Term.Admissible variableCode SetSort.set) :
    Formula.Admissible (canonical_free_variable_code_condition_with_id
        variableCode indexId) := by
  have hIndex :
      Term.Admissible (x#indexId) SetSort.set :=
    set_variable_admissible indexId
  have hIndexProduct :
      Term.Admissible (numₘ(2) *ₘ x#indexId) SetSort.set :=
    natural_multiplication_term_admissible (numₘ(2)) (x#indexId) (finite_numeral_term_admissible 2) hIndex
  have hBody :
      Formula.Admissible ((x#indexId ∈ₘ ωₘ) ∧ₘ (variableCode ≐ₘ
            var_codeₘ(numₘ(2) *ₘ x#indexId))) :=
    Formula.Admissible.conj (membership_formula_admissible
        hIndex omega_term_admissible) (Formula.Admissible.equal
        hVariableCode (variable_code_term_admissible (numₘ(2) *ₘ x#indexId) hIndexProduct))
  simpa [canonical_free_variable_code_condition_with_id] using
    Formula.Admissible.exists_closeFreeAt
      SetSort.set indexId hBody
/-- 自动编号封装下的规范自由变量码条件保持 admissibility。 -/
theorem canonical_free_variable_code_condition_admissible (variableCode : SetTerm) (hVariableCode :
      Term.Admissible variableCode SetSort.set) :
    Formula.Admissible (canonical_free_variable_code_condition variableCode) := by
  simpa [canonical_free_variable_code_condition] using
    canonical_free_variable_code_condition_with_id_admissible
      variableCode 470 hVariableCode
/--
显式编号的 canonical 全称闭包关系保持源码、变量码和目标码的 admissibility。
内部的 shifted/body 两个见证只作为集合项出现；binder-shift、逐 token 替换和最终
全称拼接的全部良构性在这里统一封装。
-/
theorem canonical_forall_closure_code_condition_with_ids_admissible (sourceCode variableCode targetCode : SetTerm) (shiftedCodeId bodyCodeId
      shiftIndexId shiftFreeId shiftBoundDepthId shiftConstantId
      shiftFunctionArityId shiftFunctionIndexId
      shiftPredicateArityId shiftPredicateIndexId
      freeIndexId : FreeVarId) (hSourceCode :
      Term.Admissible sourceCode SetSort.set) (hVariableCode :
      Term.Admissible variableCode SetSort.set) (hTargetCode :
      Term.Admissible targetCode SetSort.set) :
    Formula.Admissible (canonical_forall_closure_code_condition_with_ids
        sourceCode variableCode targetCode
        shiftedCodeId bodyCodeId
        shiftIndexId shiftFreeId shiftBoundDepthId shiftConstantId
        shiftFunctionArityId shiftFunctionIndexId
        shiftPredicateArityId shiftPredicateIndexId
        freeIndexId) := by
  have hShifted :
      Term.Admissible (x#shiftedCodeId) SetSort.set :=
    set_variable_admissible shiftedCodeId
  have hBodyCode :
      Term.Admissible (x#bodyCodeId) SetSort.set :=
    set_variable_admissible bodyCodeId
  have hOuterBinder :
      Term.Admissible
        canonical_outer_binder_variable_code_term SetSort.set :=
    variable_code_term_admissible (numₘ(1)) (finite_numeral_term_admissible 1)
  have hClosureBody :
      Formula.Admissible (((canonical_free_variable_code_condition_with_id
              variableCode freeIndexId ∧ₘ
            canonical_binder_shift_code_condition_with_ids
              sourceCode (x#shiftedCodeId)
              shiftIndexId shiftFreeId shiftBoundDepthId shiftConstantId
              shiftFunctionArityId shiftFunctionIndexId
              shiftPredicateArityId shiftPredicateIndexId) ∧ₘ (code_substitution_spec (x#shiftedCodeId) variableCode
              canonical_outer_binder_variable_code_term (x#bodyCodeId) ∧ₘ
            formula_codeₘ(x#bodyCodeId))) ∧ₘ (targetCode ≐ₘ
            forall_codeₘ(
              canonical_outer_binder_variable_code_term,
              x#bodyCodeId))) := by
    exact Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (canonical_free_variable_code_condition_with_id_admissible
            variableCode freeIndexId hVariableCode) (canonical_binder_shift_code_condition_with_ids_admissible
            sourceCode (x#shiftedCodeId)
            shiftIndexId shiftFreeId shiftBoundDepthId shiftConstantId
            shiftFunctionArityId shiftFunctionIndexId
            shiftPredicateArityId shiftPredicateIndexId
            hSourceCode hShifted)) (Formula.Admissible.conj (code_substitution_spec_admissible (x#shiftedCodeId) variableCode
            canonical_outer_binder_variable_code_term (x#bodyCodeId)
            hShifted hVariableCode hOuterBinder hBodyCode) (is_formula_code_formula_admissible hBodyCode))) (Formula.Admissible.equal
        hTargetCode (universal_formula_code_term_admissible
          canonical_outer_binder_variable_code_term (x#bodyCodeId) hOuterBinder hBodyCode))
  simpa [canonical_forall_closure_code_condition_with_ids] using
    Formula.Admissible.exists_closeFreeAt
      SetSort.set shiftedCodeId <|
        Formula.Admissible.exists_closeFreeAt
          SetSort.set bodyCodeId hClosureBody
/-- 固定编号封装下的 canonical 全称闭包关系保持 admissibility。 -/
theorem canonical_forall_closure_code_condition_admissible (sourceCode variableCode targetCode : SetTerm) (hSourceCode :
      Term.Admissible sourceCode SetSort.set) (hVariableCode :
      Term.Admissible variableCode SetSort.set) (hTargetCode :
      Term.Admissible targetCode SetSort.set) :
    Formula.Admissible (canonical_forall_closure_code_condition
        sourceCode variableCode targetCode) := by
  simpa [canonical_forall_closure_code_condition] using
    canonical_forall_closure_code_condition_with_ids_admissible
      sourceCode variableCode targetCode
      460 461
      462 463 464 465 466 467 468 469
      470
      hSourceCode hVariableCode hTargetCode
/--
`candidate` 包含基础模式，并在 locally nameless 的 canonical 全称闭包下封闭。
旧规格直接拼接任意变量码与未平移 body，只适用于纸面的具名语法；这里的三元闭包
关系与仓库实际采用的标准 quotation 精确同步。
-/
def logical_axiom_code_closed_condition (candidate : SetTerm) :
    SetFormula := (BaseLogicAxiomsₘ ⊆ₘ candidate) ∧ₘ (∀ₘ[SetSort.set, 450],
      ∀ₘ[SetSort.set, 451],
        ∀ₘ[SetSort.set, 452], ((((x#450 ∈ₘ candidate) ∧ₘ
              canonical_forall_closure_code_condition (x#450) (x#451) (x#452))) ⟶ₘ (x#452 ∈ₘ candidate)))
/--
`code` 由基础逻辑公理一步生成，或由 `candidate` 中已有代码做一次 canonical
全称闭包生成。
该条件是逻辑公理最小闭包的生成算子。把它独立命名后，正向闭包、成员反演和有限
生成轨迹可以共享同一个对象层关系，避免反向识别重新展开十二模式与闭包细节。
-/
def logical_axiom_code_generation_condition (candidate code : SetTerm) :
    SetFormula :=
  base_logical_axiom_condition code ∨ₘ (∃ₘ[SetSort.set, 454],
      ∃ₘ[SetSort.set, 455], ((x#454 ∈ₘ candidate) ∧ₘ
          canonical_forall_closure_code_condition (x#454) (x#455) code))
/--
`candidate` 对逻辑公理生成算子是精确固定点。
最小闭集不仅对生成算子封闭；其每个成员还必须来自一个基础模式或一个严格的一步
闭包生成。这个消去方向是完整反向识别所需的对象层结构反演接口。
-/
def logical_axiom_code_generated_condition (candidate : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set, 456], (((x#456 ∈ₘ candidate) ↔ₘ
      logical_axiom_code_generation_condition
        candidate (x#456)))
/--
`candidate` 是在 canonical 全称闭包下包含基础模式的最小闭集，并携带精确生成方程。
最后一个合取并非额外的逻辑公理集合假设：对单调生成算子的最小前不动点，它正是
标准的最小固定点消去原则。将其纳入定义合同后，内部证明不必再次从集合交构造重做
Knaster–Tarski 论证。
-/
def logical_axiom_set_spec (candidate : SetTerm) :
    SetFormula :=
  logical_axiom_code_closed_condition candidate ∧ₘ ((∀ₘ[SetSort.set, 453], (logical_axiom_code_closed_condition (x#453) ⟶ₘ (candidate ⊆ₘ (x#453)))) ∧ₘ
      logical_axiom_code_generated_condition candidate)
/-- 完整逻辑公理编码集合定义公理；文献索引为 `LJGL`。 -/
def logical_axiom_set_definition_axiom :
    SetFormula :=
  logical_axiom_set_spec LogicAxiomsₘ
/-- “是逻辑公理编码”谓词定义公理。 -/
def is_logical_axiom_code_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0], ((logical_axiom_codeₘ(x#0)) ↔ₘ (x#0 ∈ₘ LogicAxiomsₘ))
/-- 基础集合、全称闭包和逻辑公理谓词的联合定义公理。 -/
def logical_axiom_code_definition_axiom :
    SetFormula :=
  base_logical_axiom_set_definition_axiom ∧ₘ (logical_axiom_set_definition_axiom ∧ₘ
      is_logical_axiom_code_definition_axiom)
/-! ## Modus ponens -/
/-- 三个公式编码构成一次 modus ponens 步骤。 -/
def modus_ponens_condition (premise implication conclusion : SetTerm) :
    SetFormula := ((formula_codeₘ(premise) ∧ₘ
      formula_codeₘ(conclusion)) ∧ₘ
      formula_codeₘ(implication)) ∧ₘ (implication ≐ₘ
      imp_codeₘ(premise, conclusion))
/-- Modus ponens 关系定义公理；文献索引为 `MP`、`Ξ₁₄₉`。 -/
def modus_ponens_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2], ((modus_ponensₘ(x#0, x#1, x#2)) ↔ₘ
          modus_ponens_condition (x#0) (x#1) (x#2))
/-! ## 理论组合 -/
/-- 加入可代入性谓词后的理论。 -/
def substitutability_theory :
    SetTheory :=
  Theory.insert
    substitutable_definition_axiom
    expression_encoding_theory
/-- 加入七类命题公理模式集合后的理论。 -/
def propositional_axiom_schema_theory :
    SetTheory :=
  Theory.insert
    propositional_axiom_schema_definition_axiom
    substitutability_theory
/-- 加入三类量词公理模式集合后的理论。 -/
def quantifier_axiom_schema_theory :
    SetTheory :=
  Theory.insert
    quantifier_axiom_schema_definition_axiom
    propositional_axiom_schema_theory
/-- 加入等同律与恒等律模式集合后的理论。 -/
def equality_axiom_schema_theory :
    SetTheory :=
  Theory.insert
    equality_axiom_schema_definition_axiom
    quantifier_axiom_schema_theory
/-- 加入完整逻辑公理编码集合后的理论。 -/
def logical_axiom_code_theory :
    SetTheory :=
  Theory.insert
    logical_axiom_code_definition_axiom
    equality_axiom_schema_theory
/-- 加入 modus ponens 关系后的理论。 -/
def logical_rule_encoding_theory :
    SetTheory :=
  Theory.insert
    modus_ponens_definition_axiom
    logical_axiom_code_theory
/-! ## proof-carrying 项边界 -/
/-- 一个 admissible 代码项组成 admissible 的“逻辑公理代码”原子。 -/
theorem logical_axiom_code_formula_admissible (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (logical_axiom_codeₘ(code)) := by
  apply Formula.Admissible.rel
  simpa [signature] using (ArgsAdmissible.cons hCode ArgsAdmissible.nil)
/-- 三个 admissible 代码项组成 admissible 的对象 modus ponens 原子。 -/
theorem modus_ponens_formula_admissible (premise implication conclusion : SetTerm) (hPremise : Term.Admissible premise SetSort.set)
    (hImplication : Term.Admissible implication SetSort.set) (hConclusion : Term.Admissible conclusion SetSort.set) :
    Formula.Admissible (modus_ponensₘ(premise, implication, conclusion)) := by
  apply Formula.Admissible.rel
  simpa [signature] using (ArgsAdmissible.cons hPremise (ArgsAdmissible.cons hImplication (ArgsAdmissible.cons hConclusion ArgsAdmissible.nil)))
/-- 零元集合函数项的公共良构性模板。 -/
private theorem nullary_set_function_term_admissible (function : FunctionSymbol) (hDomain : signature.funcDomain function = []) (hCodomain :
      signature.funcCodomain function = SetSort.set) :
    Term.Admissible (Term.app (σ := signature) function [])
      SetSort.set := by
  constructor
  · have hArguments :
        ArgsWellSorted (σ := signature)
          [] (signature.funcDomain function) := by
      rw [hDomain]
      exact .nil
    simpa [hCodomain] using (TermWellSorted.app (σ := signature)
        function hArguments)
  · exact TermScoped.app (σ := signature) (ctx := Scope.empty)
      function [] (by simp)
theorem implication_distribution_axiom_set_term_admissible :
    Term.Admissible ImpDistribAxiomsₘ SetSort.set :=
  nullary_set_function_term_admissible
    FunctionSymbol.implicationDistributionAxiomSet
    rfl rfl
theorem self_implication_axiom_set_term_admissible :
    Term.Admissible SelfImpAxiomsₘ SetSort.set :=
  nullary_set_function_term_admissible
    FunctionSymbol.selfImplicationAxiomSet
    rfl rfl
theorem weakening_axiom_set_term_admissible :
    Term.Admissible WeakeningAxiomsₘ SetSort.set :=
  nullary_set_function_term_admissible
    FunctionSymbol.weakeningAxiomSet
    rfl rfl
theorem contradiction_axiom_set_term_admissible :
    Term.Admissible ContradictionAxiomsₘ SetSort.set :=
  nullary_set_function_term_admissible
    FunctionSymbol.contradictionAxiomSet
    rfl rfl
theorem classical_axiom_set_term_admissible :
    Term.Admissible ClassicalAxiomsₘ SetSort.set :=
  nullary_set_function_term_admissible
    FunctionSymbol.classicalAxiomSet
    rfl rfl
theorem explosion_axiom_set_term_admissible :
    Term.Admissible ExplosionAxiomsₘ SetSort.set :=
  nullary_set_function_term_admissible
    FunctionSymbol.explosionAxiomSet
    rfl rfl
theorem case_analysis_axiom_set_term_admissible :
    Term.Admissible CaseAnalysisAxiomsₘ SetSort.set :=
  nullary_set_function_term_admissible
    FunctionSymbol.caseAnalysisAxiomSet
    rfl rfl
theorem specialization_axiom_set_term_admissible :
    Term.Admissible SpecializationAxiomsₘ SetSort.set :=
  nullary_set_function_term_admissible
    FunctionSymbol.specializationAxiomSet
    rfl rfl
theorem quantifier_distribution_axiom_set_term_admissible :
    Term.Admissible ForallDistribAxiomsₘ SetSort.set :=
  nullary_set_function_term_admissible
    FunctionSymbol.quantifierDistributionAxiomSet
    rfl rfl
theorem vacuous_quantifier_axiom_set_term_admissible :
    Term.Admissible VacuousForallAxiomsₘ SetSort.set :=
  nullary_set_function_term_admissible
    FunctionSymbol.vacuousQuantifierAxiomSet
    rfl rfl
theorem equality_substitution_axiom_set_term_admissible :
    Term.Admissible EqualitySubstAxiomsₘ SetSort.set :=
  nullary_set_function_term_admissible
    FunctionSymbol.equalitySubstitutionAxiomSet
    rfl rfl
theorem equality_reflexivity_axiom_set_term_admissible :
    Term.Admissible EqualityReflAxiomsₘ SetSort.set :=
  nullary_set_function_term_admissible
    FunctionSymbol.equalityReflexivityAxiomSet
    rfl rfl
theorem base_logical_axiom_set_term_admissible :
    Term.Admissible BaseLogicAxiomsₘ SetSort.set :=
  nullary_set_function_term_admissible
    FunctionSymbol.baseLogicalAxiomSet
    rfl rfl
theorem logical_axiom_set_term_admissible :
    Term.Admissible LogicAxiomsₘ SetSort.set :=
  nullary_set_function_term_admissible
    FunctionSymbol.logicalAxiomSet
    rfl rfl
theorem implication_distribution_axiom_code_term_admissible (antecedent middle consequent : SetTerm) (hAntecedent :
      Term.Admissible antecedent SetSort.set) (hMiddle :
      Term.Admissible middle SetSort.set) (hConsequent :
      Term.Admissible consequent SetSort.set) :
    Term.Admissible (implication_distribution_axiom_code_term
        antecedent middle consequent)
      SetSort.set :=
  implication_formula_code_term_admissible (imp_codeₘ(antecedent,
      imp_codeₘ(middle, consequent))) (imp_codeₘ(
      imp_codeₘ(antecedent, middle),
      imp_codeₘ(antecedent, consequent))) (implication_formula_code_term_admissible
      antecedent (imp_codeₘ(middle, consequent))
      hAntecedent (implication_formula_code_term_admissible
        middle consequent hMiddle hConsequent)) (implication_formula_code_term_admissible (imp_codeₘ(antecedent, middle)) (imp_codeₘ(antecedent, consequent))
      (implication_formula_code_term_admissible
        antecedent middle hAntecedent hMiddle) (implication_formula_code_term_admissible
        antecedent consequent hAntecedent hConsequent))
theorem self_implication_axiom_code_term_admissible (formula : SetTerm) (hFormula :
      Term.Admissible formula SetSort.set) :
    Term.Admissible (self_implication_axiom_code_term formula)
      SetSort.set :=
  implication_formula_code_term_admissible
    formula (imp_codeₘ(formula, formula))
    hFormula (implication_formula_code_term_admissible
      formula formula hFormula hFormula)
theorem weakening_axiom_code_term_admissible (formula extra : SetTerm) (hFormula :
      Term.Admissible formula SetSort.set) (hExtra :
      Term.Admissible extra SetSort.set) :
    Term.Admissible (weakening_axiom_code_term formula extra)
      SetSort.set :=
  implication_formula_code_term_admissible
    formula (imp_codeₘ(extra, formula))
    hFormula (implication_formula_code_term_admissible
      extra formula hExtra hFormula)
theorem contradiction_axiom_code_term_admissible (formula conclusion : SetTerm) (hFormula :
      Term.Admissible formula SetSort.set) (hConclusion :
      Term.Admissible conclusion SetSort.set) :
    Term.Admissible (contradiction_axiom_code_term
        formula conclusion)
      SetSort.set :=
  implication_formula_code_term_admissible
    formula (imp_codeₘ(neg_codeₘ(formula), conclusion))
    hFormula (implication_formula_code_term_admissible (neg_codeₘ(formula))
      conclusion (negation_formula_code_term_admissible
        formula hFormula)
      hConclusion)
theorem classical_axiom_code_term_admissible (formula : SetTerm) (hFormula :
      Term.Admissible formula SetSort.set) :
    Term.Admissible (classical_axiom_code_term formula)
      SetSort.set :=
  implication_formula_code_term_admissible (imp_codeₘ(neg_codeₘ(formula), formula))
    formula (implication_formula_code_term_admissible (neg_codeₘ(formula))
      formula (negation_formula_code_term_admissible
        formula hFormula)
      hFormula)
    hFormula
theorem explosion_axiom_code_term_admissible (formula conclusion : SetTerm) (hFormula :
      Term.Admissible formula SetSort.set) (hConclusion :
      Term.Admissible conclusion SetSort.set) :
    Term.Admissible (explosion_axiom_code_term formula conclusion)
      SetSort.set :=
  implication_formula_code_term_admissible (neg_codeₘ(formula)) (imp_codeₘ(formula, conclusion)) (negation_formula_code_term_admissible
      formula hFormula) (implication_formula_code_term_admissible
      formula conclusion hFormula hConclusion)
theorem case_analysis_axiom_code_term_admissible (formula conclusion : SetTerm) (hFormula :
      Term.Admissible formula SetSort.set) (hConclusion :
      Term.Admissible conclusion SetSort.set) :
    Term.Admissible (case_analysis_axiom_code_term
        formula conclusion)
      SetSort.set :=
  implication_formula_code_term_admissible (imp_codeₘ(formula, conclusion)) (imp_codeₘ(
      imp_codeₘ(neg_codeₘ(formula), conclusion),
      conclusion)) (implication_formula_code_term_admissible
      formula conclusion hFormula hConclusion) (implication_formula_code_term_admissible (imp_codeₘ(neg_codeₘ(formula), conclusion))
      conclusion (implication_formula_code_term_admissible (neg_codeₘ(formula))
        conclusion (negation_formula_code_term_admissible
          formula hFormula)
        hConclusion)
      hConclusion)
theorem specialization_axiom_code_term_admissible (universalCode resultCode : SetTerm) (hUniversal :
      Term.Admissible universalCode SetSort.set) (hResult :
      Term.Admissible resultCode SetSort.set) :
    Term.Admissible (specialization_axiom_code_term
        universalCode resultCode)
      SetSort.set :=
  implication_formula_code_term_admissible
    universalCode resultCode hUniversal hResult
theorem quantifier_distribution_axiom_code_term_admissible (boundVariable antecedent consequent : SetTerm) (hVariable :
      Term.Admissible boundVariable SetSort.set) (hAntecedent :
      Term.Admissible antecedent SetSort.set) (hConsequent :
      Term.Admissible consequent SetSort.set) :
    Term.Admissible (quantifier_distribution_axiom_code_term
        boundVariable antecedent consequent)
      SetSort.set :=
  implication_formula_code_term_admissible (forall_codeₘ(
      boundVariable,
      imp_codeₘ(antecedent, consequent))) (imp_codeₘ(
      forall_codeₘ(boundVariable, antecedent),
      forall_codeₘ(boundVariable, consequent))) (universal_formula_code_term_admissible
      boundVariable (imp_codeₘ(antecedent, consequent))
      hVariable (implication_formula_code_term_admissible
        antecedent consequent
        hAntecedent hConsequent)) (implication_formula_code_term_admissible (forall_codeₘ(boundVariable, antecedent)) (forall_codeₘ(boundVariable, consequent))
      (universal_formula_code_term_admissible
        boundVariable antecedent
        hVariable hAntecedent) (universal_formula_code_term_admissible
        boundVariable consequent
        hVariable hConsequent))
theorem vacuous_quantifier_axiom_code_term_admissible (boundVariable antecedent body : SetTerm) (hVariable :
      Term.Admissible boundVariable SetSort.set) (hAntecedent :
      Term.Admissible antecedent SetSort.set) (hBody :
      Term.Admissible body SetSort.set) :
    Term.Admissible (vacuous_quantifier_axiom_code_term
        boundVariable antecedent body)
      SetSort.set :=
  implication_formula_code_term_admissible
    antecedent (forall_codeₘ(boundVariable, body))
    hAntecedent (universal_formula_code_term_admissible
      boundVariable body hVariable hBody)
theorem equality_substitution_axiom_code_term_admissible (boundVariable replacementVariable body : SetTerm) (hVariable :
      Term.Admissible boundVariable SetSort.set) (hReplacement :
      Term.Admissible replacementVariable SetSort.set) (hBody :
      Term.Admissible body SetSort.set) :
    Term.Admissible (equality_substitution_axiom_code_term
        boundVariable replacementVariable body)
      SetSort.set :=
  implication_formula_code_term_admissible (eq_codeₘ(boundVariable, replacementVariable)) (imp_codeₘ(
      body,
      subst_codeₘ(
        body, boundVariable, replacementVariable))) (equality_formula_code_term_admissible
      boundVariable replacementVariable
      hVariable hReplacement) (implication_formula_code_term_admissible
      body (subst_codeₘ(
        body, boundVariable, replacementVariable))
      hBody (code_substitution_term_admissible
        body boundVariable replacementVariable
        hBody hVariable hReplacement))
theorem equality_reflexivity_axiom_code_term_admissible (boundVariable : SetTerm) (hVariable :
      Term.Admissible boundVariable SetSort.set) :
    Term.Admissible (equality_reflexivity_axiom_code_term
        boundVariable)
      SetSort.set :=
  equality_formula_code_term_admissible
    boundVariable boundVariable
    hVariable hVariable
/-! ## 公理模式条件的公共 admissibility 接口 -/
/--
可代入性定义体保持三个公开代码项的 admissibility。
量词内部使用固定的自由变量模板构造，再由 `closeFreeAt` 进入实际 binder；因此该
接口同时封装了 no-capture 条件中两层全称量词的 scope 证明。
-/
theorem substitutable_condition_admissible (boundVariable replacement formula : SetTerm) (hBoundVariable :
      Term.Admissible boundVariable SetSort.set) (hReplacement :
      Term.Admissible replacement SetSort.set) (hFormula :
      Term.Admissible formula SetSort.set) :
    Formula.Admissible (substitutable_condition
        boundVariable replacement formula) := by
  have hVariable :
      Term.Admissible (x#420) SetSort.set :=
    set_variable_admissible 420
  have hPosition :
      Term.Admissible (x#421) SetSort.set :=
    set_variable_admissible 421
  have hMember :=
    membership_formula_admissible hBoundVariable
      variable_symbol_set_term_admissible
  have hReplacementCode :=
    is_term_code_formula_admissible hReplacement
  have hFormulaCode :=
    is_formula_code_formula_admissible hFormula
  have hVariableCollection :=
    variable_collection_term_admissible replacement hReplacement
  have hVariableMember :=
    membership_formula_admissible hVariable hVariableCollection
  have hFreePosition :=
    free_occurrence_position_condition_admissible
      boundVariable formula (x#421)
      hBoundVariable hFormula hPosition
  have hQuantifiedPosition :=
    quantifier_body_position_condition_admissible (x#420) formula (x#421)
      hVariable hFormula hPosition
  have hPositionBody :=
    Formula.Admissible.imp hFreePosition (Formula.Admissible.neg hQuantifiedPosition)
  have hAllPositions :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set 421 hPositionBody
  have hVariableBody :=
    Formula.Admissible.imp hVariableMember hAllPositions
  have hAllVariables :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set 420 hVariableBody
  simpa [substitutable_condition] using
    Formula.Admissible.conj (Formula.Admissible.conj hMember (Formula.Admissible.conj
          hReplacementCode hFormulaCode))
      hAllVariables
/-- 蕴含分配模式条件保持候选代码项的 admissibility。 -/
theorem implication_distribution_axiom_condition_admissible (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (implication_distribution_axiom_condition code) := by
  have hAntecedent :
      Term.Admissible (x#400) SetSort.set :=
    set_variable_admissible 400
  have hMiddle :
      Term.Admissible (x#401) SetSort.set :=
    set_variable_admissible 401
  have hConsequent :
      Term.Admissible (x#402) SetSort.set :=
    set_variable_admissible 402
  have hBody :=
    Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (is_formula_code_formula_admissible hAntecedent)
          (is_formula_code_formula_admissible hMiddle)) (is_formula_code_formula_admissible hConsequent)) (Formula.Admissible.equal hCode
        (implication_distribution_axiom_code_term_admissible (x#400) (x#401) (x#402)
          hAntecedent hMiddle hConsequent))
  simpa [implication_distribution_axiom_condition] using
    Formula.Admissible.exists_closeFreeAt SetSort.set 400 <|
      Formula.Admissible.exists_closeFreeAt SetSort.set 401 <|
        Formula.Admissible.exists_closeFreeAt SetSort.set 402 hBody
/-- 自蕴含模式条件保持候选代码项的 admissibility。 -/
theorem self_implication_axiom_condition_admissible (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (self_implication_axiom_condition code) := by
  have hFormula :
      Term.Admissible (x#403) SetSort.set :=
    set_variable_admissible 403
  have hBody :=
    Formula.Admissible.conj (is_formula_code_formula_admissible hFormula) (Formula.Admissible.equal hCode (self_implication_axiom_code_term_admissible
          (x#403) hFormula))
  simpa [self_implication_axiom_condition] using
    Formula.Admissible.exists_closeFreeAt SetSort.set 403 hBody
/-- 弱化模式条件保持候选代码项的 admissibility。 -/
theorem weakening_axiom_condition_admissible (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (weakening_axiom_condition code) := by
  have hFormula :
      Term.Admissible (x#404) SetSort.set :=
    set_variable_admissible 404
  have hExtra :
      Term.Admissible (x#405) SetSort.set :=
    set_variable_admissible 405
  have hBody :=
    Formula.Admissible.conj (Formula.Admissible.conj (is_formula_code_formula_admissible hFormula) (is_formula_code_formula_admissible hExtra))
      (Formula.Admissible.equal hCode (weakening_axiom_code_term_admissible (x#404) (x#405) hFormula hExtra))
  simpa [weakening_axiom_condition] using
    Formula.Admissible.exists_closeFreeAt SetSort.set 404 <|
      Formula.Admissible.exists_closeFreeAt SetSort.set 405 hBody
/-- 矛盾前件模式条件保持候选代码项的 admissibility。 -/
theorem contradiction_axiom_condition_admissible (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (contradiction_axiom_condition code) := by
  have hFormula :
      Term.Admissible (x#406) SetSort.set :=
    set_variable_admissible 406
  have hConclusion :
      Term.Admissible (x#407) SetSort.set :=
    set_variable_admissible 407
  have hBody :=
    Formula.Admissible.conj (Formula.Admissible.conj (is_formula_code_formula_admissible hFormula) (is_formula_code_formula_admissible hConclusion))
      (Formula.Admissible.equal hCode (contradiction_axiom_code_term_admissible (x#406) (x#407) hFormula hConclusion))
  simpa [contradiction_axiom_condition] using
    Formula.Admissible.exists_closeFreeAt SetSort.set 406 <|
      Formula.Admissible.exists_closeFreeAt SetSort.set 407 hBody
/-- 经典模式条件保持候选代码项的 admissibility。 -/
theorem classical_axiom_condition_admissible (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (classical_axiom_condition code) := by
  have hFormula :
      Term.Admissible (x#408) SetSort.set :=
    set_variable_admissible 408
  have hBody :=
    Formula.Admissible.conj (is_formula_code_formula_admissible hFormula) (Formula.Admissible.equal hCode (classical_axiom_code_term_admissible
          (x#408) hFormula))
  simpa [classical_axiom_condition] using
    Formula.Admissible.exists_closeFreeAt SetSort.set 408 hBody
/-- 爆炸律模式条件保持候选代码项的 admissibility。 -/
theorem explosion_axiom_condition_admissible (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (explosion_axiom_condition code) := by
  have hFormula :
      Term.Admissible (x#409) SetSort.set :=
    set_variable_admissible 409
  have hConclusion :
      Term.Admissible (x#410) SetSort.set :=
    set_variable_admissible 410
  have hBody :=
    Formula.Admissible.conj (Formula.Admissible.conj (is_formula_code_formula_admissible hFormula) (is_formula_code_formula_admissible hConclusion))
      (Formula.Admissible.equal hCode (explosion_axiom_code_term_admissible (x#409) (x#410) hFormula hConclusion))
  simpa [explosion_axiom_condition] using
    Formula.Admissible.exists_closeFreeAt SetSort.set 409 <|
      Formula.Admissible.exists_closeFreeAt SetSort.set 410 hBody
/-- 分类讨论模式条件保持候选代码项的 admissibility。 -/
theorem case_analysis_axiom_condition_admissible (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (case_analysis_axiom_condition code) := by
  have hFormula :
      Term.Admissible (x#411) SetSort.set :=
    set_variable_admissible 411
  have hConclusion :
      Term.Admissible (x#412) SetSort.set :=
    set_variable_admissible 412
  have hBody :=
    Formula.Admissible.conj (Formula.Admissible.conj (is_formula_code_formula_admissible hFormula) (is_formula_code_formula_admissible hConclusion))
      (Formula.Admissible.equal hCode (case_analysis_axiom_code_term_admissible (x#411) (x#412) hFormula hConclusion))
  simpa [case_analysis_axiom_condition] using
    Formula.Admissible.exists_closeFreeAt SetSort.set 411 <|
      Formula.Admissible.exists_closeFreeAt SetSort.set 412 hBody
/-- 全称特化模式条件保持候选代码项的 admissibility。 -/
theorem specialization_axiom_condition_admissible (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (specialization_axiom_condition code) := by
  have hSource :
      Term.Admissible (x#430) SetSort.set :=
    set_variable_admissible 430
  have hVariable :
      Term.Admissible (x#431) SetSort.set :=
    set_variable_admissible 431
  have hReplacement :
      Term.Admissible (x#432) SetSort.set :=
    set_variable_admissible 432
  have hUniversal :
      Term.Admissible (x#433) SetSort.set :=
    set_variable_admissible 433
  have hResult :
      Term.Admissible (x#434) SetSort.set :=
    set_variable_admissible 434
  have hTyping :=
    Formula.Admissible.conj (Formula.Admissible.conj (is_formula_code_formula_admissible hSource) (is_term_code_formula_admissible hReplacement))
      (Formula.Admissible.conj (is_formula_code_formula_admissible hUniversal) (is_formula_code_formula_admissible hResult))
  have hClosure :=
    canonical_forall_closure_code_condition_admissible (x#430) (x#431) (x#433)
      hSource hVariable hUniversal
  have hSubstitutable :=
    is_substitutable_formula_admissible
      hVariable hReplacement hSource
  have hSubstitution :=
    code_substitution_spec_admissible (x#430) (x#431) (x#432) (x#434)
      hSource hVariable hReplacement hResult
  have hCondition :=
    Formula.Admissible.conj
      (Formula.Admissible.conj
        (Formula.Admissible.conj
          (Formula.Admissible.conj hTyping hClosure)
          hSubstitutable)
        hSubstitution)
      (Formula.Admissible.equal hCode
        (specialization_axiom_code_term_admissible
          (x#433) (x#434) hUniversal hResult))
  simpa [specialization_axiom_condition] using
    Formula.Admissible.exists_closeFreeAt SetSort.set 430 <|
      Formula.Admissible.exists_closeFreeAt SetSort.set 431 <|
        Formula.Admissible.exists_closeFreeAt SetSort.set 432 <|
          Formula.Admissible.exists_closeFreeAt SetSort.set 433 <|
            Formula.Admissible.exists_closeFreeAt SetSort.set 434 hCondition
/-- 全称量词分配模式条件保持候选代码项的 admissibility。 -/
theorem quantifier_distribution_axiom_condition_admissible (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (quantifier_distribution_axiom_condition code) := by
  have hBoundVariable :
      Term.Admissible (x#433) SetSort.set :=
    set_variable_admissible 433
  have hAntecedent :
      Term.Admissible (x#434) SetSort.set :=
    set_variable_admissible 434
  have hConsequent :
      Term.Admissible (x#435) SetSort.set :=
    set_variable_admissible 435
  have hCondition :=
    Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (membership_formula_admissible hBoundVariable
            variable_symbol_set_term_admissible) (is_formula_code_formula_admissible hAntecedent)) (is_formula_code_formula_admissible hConsequent))
      (Formula.Admissible.equal hCode (quantifier_distribution_axiom_code_term_admissible (x#433) (x#434) (x#435)
          hBoundVariable hAntecedent hConsequent))
  simpa [quantifier_distribution_axiom_condition] using
    Formula.Admissible.exists_closeFreeAt SetSort.set 433 <|
      Formula.Admissible.exists_closeFreeAt SetSort.set 434 <|
        Formula.Admissible.exists_closeFreeAt SetSort.set 435 hCondition
/--
无关量词模式条件保持候选代码项的 admissibility。
该定义使用匿名双 binder。这里从量词模式联合定义的闭公式边界中取出相应全称分支，
再在候选代码处打开；这样无需为内部 de Bruijn 见证另建一套旁路 scope 证明。
-/
theorem vacuous_quantifier_axiom_condition_admissible (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (vacuous_quantifier_axiom_condition code) := by
  have hCanonicalConditionFixed :
      Formula.substituteFree SetSort.set 0 code (canonical_binder_shift_code_condition_with_ids (bₛ#1) (bₛ#0)
            438 439 440 441 442 443 444 445) =
        canonical_binder_shift_code_condition_with_ids (bₛ#1) (bₛ#0)
          438 439 440 441 442 443 444 445 := by
    apply Formula.substituteFree_eq_self_of_not_mem
    native_decide
  have hNumeralFixed :
      Term.substituteFree SetSort.set 0 code (numₘ(1)) =
        numₘ(1) := by
    apply Term.substituteFree_eq_self_of_not_mem
    simp [finite_numeral_term_freeSupport]
  have hDefinition :
      Formula.Admissible
        quantifier_axiom_schema_definition_axiom := by
    apply Formula.check_admissible_sound
    native_decide
  have hUniversal :
      Formula.Admissible (∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ VacuousForallAxiomsₘ) ↔ₘ
            vacuous_quantifier_axiom_condition (x#0))) :=
    Formula.Admissible.conj_right <|
      Formula.Admissible.conj_right hDefinition
  have hInstance :=
    Formula.Admissible.forall_openAt (term := code) SetSort.set hUniversal hCode
  have hCondition :=
    Formula.Admissible.iff_right hInstance
  simpa [vacuous_quantifier_axiom_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.substituteFree, Term.substituteFree,
    set_variable, set_bound_variable,
    hCanonicalConditionFixed, hNumeralFixed] using hCondition
/-- 等同替换模式条件保持候选代码项的 admissibility。 -/
theorem equality_substitution_axiom_condition_admissible (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (equality_substitution_axiom_condition code) := by
  have hBoundVariable :
      Term.Admissible (x#440) SetSort.set :=
    set_variable_admissible 440
  have hReplacement :
      Term.Admissible (x#441) SetSort.set :=
    set_variable_admissible 441
  have hBody :
      Term.Admissible (x#442) SetSort.set :=
    set_variable_admissible 442
  have hCondition :=
    Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (membership_formula_admissible hBoundVariable
              variable_symbol_set_term_admissible) (membership_formula_admissible hReplacement
              variable_symbol_set_term_admissible)) (is_formula_code_formula_admissible hBody)) (is_substitutable_formula_admissible
          hBoundVariable hReplacement hBody)) (Formula.Admissible.equal hCode (equality_substitution_axiom_code_term_admissible (x#440) (x#441) (x#442)
          hBoundVariable hReplacement hBody))
  simpa [equality_substitution_axiom_condition] using
    Formula.Admissible.exists_closeFreeAt SetSort.set 440 <|
      Formula.Admissible.exists_closeFreeAt SetSort.set 441 <|
        Formula.Admissible.exists_closeFreeAt SetSort.set 442 hCondition
/-- 等式自反模式条件保持候选代码项的 admissibility。 -/
theorem equality_reflexivity_axiom_condition_admissible (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (equality_reflexivity_axiom_condition code) := by
  have hBoundVariable :
      Term.Admissible (x#443) SetSort.set :=
    set_variable_admissible 443
  have hCondition :=
    Formula.Admissible.conj (membership_formula_admissible hBoundVariable
        variable_symbol_set_term_admissible) (Formula.Admissible.equal hCode (equality_reflexivity_axiom_code_term_admissible (x#443) hBoundVariable))
  simpa [equality_reflexivity_axiom_condition] using
    Formula.Admissible.exists_closeFreeAt SetSort.set 443 hCondition
/-- 十二类基础逻辑公理联合条件保持候选代码项的 admissibility。 -/
theorem base_logical_axiom_condition_admissible (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (base_logical_axiom_condition code) := by
  have hImplicationDistribution :=
    membership_formula_admissible hCode
      implication_distribution_axiom_set_term_admissible
  have hSelfImplication :=
    membership_formula_admissible hCode
      self_implication_axiom_set_term_admissible
  have hWeakening :=
    membership_formula_admissible hCode
      weakening_axiom_set_term_admissible
  have hContradiction :=
    membership_formula_admissible hCode
      contradiction_axiom_set_term_admissible
  have hClassical :=
    membership_formula_admissible hCode
      classical_axiom_set_term_admissible
  have hExplosion :=
    membership_formula_admissible hCode
      explosion_axiom_set_term_admissible
  have hCaseAnalysis :=
    membership_formula_admissible hCode
      case_analysis_axiom_set_term_admissible
  have hSpecialization :=
    membership_formula_admissible hCode
      specialization_axiom_set_term_admissible
  have hQuantifierDistribution :=
    membership_formula_admissible hCode
      quantifier_distribution_axiom_set_term_admissible
  have hVacuousQuantifier :=
    membership_formula_admissible hCode
      vacuous_quantifier_axiom_set_term_admissible
  have hEqualitySubstitution :=
    membership_formula_admissible hCode
      equality_substitution_axiom_set_term_admissible
  have hEqualityReflexivity :=
    membership_formula_admissible hCode
      equality_reflexivity_axiom_set_term_admissible
  simpa [base_logical_axiom_condition] using
    Formula.Admissible.disj hImplicationDistribution <|
      Formula.Admissible.disj hSelfImplication <|
        Formula.Admissible.disj hWeakening <|
          Formula.Admissible.disj hContradiction <|
            Formula.Admissible.disj hClassical <|
              Formula.Admissible.disj hExplosion <|
                Formula.Admissible.disj hCaseAnalysis <|
                  Formula.Admissible.disj hSpecialization <|
                    Formula.Admissible.disj hQuantifierDistribution <|
                      Formula.Admissible.disj hVacuousQuantifier <|
                        Formula.Admissible.disj
                          hEqualitySubstitution
                          hEqualityReflexivity
/-- 十二类基础逻辑公理联合条件由候选代码项证书直接计算。 -/
@[formula_check]
theorem base_logical_axiom_condition_check
    (code : SetTerm)
    (hCode : Term.CheckCertificate code SetSort.set) :
    Formula.CheckCertificate
      (base_logical_axiom_condition code) :=
  Formula.check_certificate_of_admissible
    (base_logical_axiom_condition_admissible
      code hCode.admissible)
/-! ## 良构性与闭理论边界 -/
theorem substitutable_definition_axiom_admissible :
    Formula.Admissible
      substitutable_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem propositional_axiom_schema_definition_axiom_admissible :
    Formula.Admissible
      propositional_axiom_schema_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem quantifier_axiom_schema_definition_axiom_admissible :
    Formula.Admissible
      quantifier_axiom_schema_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem equality_axiom_schema_definition_axiom_admissible :
    Formula.Admissible
      equality_axiom_schema_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem logical_axiom_code_definition_axiom_admissible :
    Formula.Admissible
      logical_axiom_code_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem modus_ponens_definition_axiom_admissible :
    Formula.Admissible
      modus_ponens_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem substitutability_theory_admissible :
    Theory.Admissible substitutability_theory :=
  Theory.admissible_insert
    substitutable_definition_axiom_admissible
    expression_encoding_theory_admissible
theorem propositional_axiom_schema_theory_admissible :
    Theory.Admissible propositional_axiom_schema_theory :=
  Theory.admissible_insert
    propositional_axiom_schema_definition_axiom_admissible
    substitutability_theory_admissible
theorem quantifier_axiom_schema_theory_admissible :
    Theory.Admissible quantifier_axiom_schema_theory :=
  Theory.admissible_insert
    quantifier_axiom_schema_definition_axiom_admissible
    propositional_axiom_schema_theory_admissible
theorem equality_axiom_schema_theory_admissible :
    Theory.Admissible equality_axiom_schema_theory :=
  Theory.admissible_insert
    equality_axiom_schema_definition_axiom_admissible
    quantifier_axiom_schema_theory_admissible
theorem logical_axiom_code_theory_admissible :
    Theory.Admissible logical_axiom_code_theory :=
  Theory.admissible_insert
    logical_axiom_code_definition_axiom_admissible
    equality_axiom_schema_theory_admissible
theorem logical_rule_encoding_theory_admissible :
    Theory.Admissible logical_rule_encoding_theory :=
  Theory.admissible_insert
    modus_ponens_definition_axiom_admissible
    logical_axiom_code_theory_admissible
@[derive_close_sentence]
theorem substitutability_theory_sentence
    {formula : SetFormula} (hFormula : substitutability_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact substitutable_definition_axiom_admissible
    · native_decide
  · exact expression_encoding_theory_sentence hFormula
@[derive_close_sentence]
theorem propositional_axiom_schema_theory_sentence
    {formula : SetFormula} (hFormula : propositional_axiom_schema_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact propositional_axiom_schema_definition_axiom_admissible
    · native_decide
  · exact substitutability_theory_sentence hFormula
@[derive_close_sentence]
theorem quantifier_axiom_schema_theory_sentence
    {formula : SetFormula} (hFormula : quantifier_axiom_schema_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact quantifier_axiom_schema_definition_axiom_admissible
    · native_decide
  · exact propositional_axiom_schema_theory_sentence hFormula
@[derive_close_sentence]
theorem equality_axiom_schema_theory_sentence
    {formula : SetFormula} (hFormula : equality_axiom_schema_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact equality_axiom_schema_definition_axiom_admissible
    · native_decide
  · exact quantifier_axiom_schema_theory_sentence hFormula
@[derive_close_sentence]
theorem logical_axiom_code_theory_sentence
    {formula : SetFormula} (hFormula : logical_axiom_code_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact logical_axiom_code_definition_axiom_admissible
    · native_decide
  · exact equality_axiom_schema_theory_sentence hFormula
@[derive_close_sentence]
theorem logical_rule_encoding_theory_sentence
    {formula : SetFormula} (hFormula : logical_rule_encoding_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact modus_ponens_definition_axiom_admissible
    · native_decide
  · exact logical_axiom_code_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem expression_encoding_theory_subset_substitutability_theory
    {formula : SetFormula} (hFormula : expression_encoding_theory formula) :
    substitutability_theory formula :=
  Or.inr hFormula
theorem substitutability_theory_subset_propositional_axiom_schema_theory
    {formula : SetFormula} (hFormula : substitutability_theory formula) :
    propositional_axiom_schema_theory formula :=
  Or.inr hFormula
theorem propositional_axiom_schema_theory_subset_quantifier_axiom_schema_theory
    {formula : SetFormula} (hFormula : propositional_axiom_schema_theory formula) :
    quantifier_axiom_schema_theory formula :=
  Or.inr hFormula
theorem quantifier_axiom_schema_theory_subset_equality_axiom_schema_theory
    {formula : SetFormula} (hFormula : quantifier_axiom_schema_theory formula) :
    equality_axiom_schema_theory formula :=
  Or.inr hFormula
theorem equality_axiom_schema_theory_subset_logical_axiom_code_theory
    {formula : SetFormula} (hFormula : equality_axiom_schema_theory formula) :
    logical_axiom_code_theory formula :=
  Or.inr hFormula
theorem logical_axiom_code_theory_subset_logical_rule_encoding_theory
    {formula : SetFormula} (hFormula : logical_axiom_code_theory formula) :
    logical_rule_encoding_theory formula :=
  Or.inr hFormula
/-! ## 待证明定理索引 -/
/-!
后续证明层将基于本模块处理：
* 七类命题模式、三类量词模式和两类等式模式都生成公式编码；
* 可代入性对公式构造的递归判定，以及与无捕获替换的等价性；
* `LogicAxiomsₘ` 包含所有基础模式，并在全称量化下封闭；
* `LogicAxiomsₘ` 的最小性、结构归纳和纸面逐层递推构造的等价性；
* specialization、全称量词分配、无关量词引入、等同律和恒等律的模式反演；
* `modus_ponensₘ` 的输入输出都是公式编码，以及 MP 对替换和全称闭包的兼容性。
这些定理将优先由 `prove_auto` 处理命题骨架与集合规格；公式编码唯一可读性、
无捕获替换和公理闭包结构归纳保留手工证明。
-/
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
