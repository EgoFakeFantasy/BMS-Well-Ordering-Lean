import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalArithmetic
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure
/-!
# 替换模式与超限递归定义设施
本模块只引入这一层真正需要的基础设施：
* `ReplacementPredicate` 携带一个二元公式及其 proof-carrying 良构性证明；
* `replacement_schema` 是标准替换模式，而不是把模式误缩成单条公理；
* `RecursiveStep` 描述三元递归步公式；
* `transfinite_recursion_definition` 是参数化的递归定义契约。
文献中的 `DGSJ`、`ψ₇₅`--`ψ₇₇` 与映像存在性、唯一性、递归定理等只保留为
本模块的语义说明。由于公式参数不是对象语言项，`DGSJ_φ` 不伪装成一个
固定签名中的普通函数符号。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 公式模式参数 -/
/--
替换模式的二元公式参数。
约定自由变量 `0`、`1` 分别代表输入与输出；其余自由变量可以表示模式参数。
结构中的证明使模式实例可以直接进入 `Theory`，不依赖公式字符串或文献编号。
-/
structure ReplacementPredicate where
  body : SetFormula
  admissible : Formula.Admissible body
/--
超限递归步的三元公式参数。
约定自由变量 `0`、`1`、`2` 分别代表当前指标、当前值与下一值。
-/
structure RecursiveStep where
  body : SetFormula
  admissible : Formula.Admissible body
/-! ## 模式辅助变量 -/
/-- 一个只用于占用自由变量编号的新鲜性标记公式。 -/
def fresh_variable_marker (id : FreeVarId) :
    SetFormula := (set_variable id ≐ₘ set_variable id)
/--
替换模式中函数性条件的第二个输出变量。
自由变量 `0`、`1` 保留给替换关系的输入、输出；该编号避免与模式参数冲突。
-/
def replacement_output_parameter (predicate : ReplacementPredicate) :
    FreeVarId :=
  FreshVariable.fresh_id SetSort.set
    [predicate.body,
      fresh_variable_marker 0,
      fresh_variable_marker 1]
/-- 替换模式的源集变量。 -/
def replacement_source_parameter (predicate : ReplacementPredicate) :
    FreeVarId :=
  FreshVariable.fresh_id SetSort.set
    [predicate.body,
      fresh_variable_marker 0,
      fresh_variable_marker 1,
      fresh_variable_marker (replacement_output_parameter predicate)]
/-- 替换模式的像集变量。 -/
def replacement_target_parameter (predicate : ReplacementPredicate) :
    FreeVarId :=
  FreshVariable.fresh_id SetSort.set
    [predicate.body,
      fresh_variable_marker 0,
      fresh_variable_marker 1,
      fresh_variable_marker (replacement_output_parameter predicate),
      fresh_variable_marker (replacement_source_parameter predicate)]
/-- 替换模式的像集成员变量。 -/
def replacement_member_parameter (predicate : ReplacementPredicate) :
    FreeVarId :=
  FreshVariable.fresh_id SetSort.set
    [predicate.body,
      fresh_variable_marker 0,
      fresh_variable_marker 1,
      fresh_variable_marker (replacement_output_parameter predicate),
      fresh_variable_marker (replacement_source_parameter predicate),
      fresh_variable_marker (replacement_target_parameter predicate)]
/-- 替换模式的像集见证变量。 -/
def replacement_witness_parameter (predicate : ReplacementPredicate) :
    FreeVarId :=
  FreshVariable.fresh_id SetSort.set
    [predicate.body,
      fresh_variable_marker 0,
      fresh_variable_marker 1,
      fresh_variable_marker (replacement_output_parameter predicate),
      fresh_variable_marker (replacement_source_parameter predicate),
      fresh_variable_marker (replacement_target_parameter predicate),
      fresh_variable_marker (replacement_member_parameter predicate)]
/-! ## 替换模式 -/
/-- 把替换关系的输出变量改为指定项。 -/
def replacement_body_at_output (predicate : ReplacementPredicate) (output : SetTerm) :
    SetFormula :=
  predicate.body ⟪SetSort.set, 1 ↦ output⟫ₘ
/-- 把替换关系的输入、输出变量改为指定项。 -/
def replacement_body_at (predicate : ReplacementPredicate) (input output : SetTerm) :
    SetFormula := (replacement_body_at_output predicate output) ⟪SetSort.set, 0 ↦ input⟫ₘ
/-- 替换关系的函数性条件；文献中对应替换公理的前件。 -/
def replacement_functionality_core (predicate : ReplacementPredicate) :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set,
        replacement_output_parameter predicate], ((predicate.body ∧ₘ
            replacement_body_at_output
              predicate (set_variable (replacement_output_parameter predicate))) ⟶ₘ ((set_variable 1) ≐ₘ (set_variable
              (replacement_output_parameter predicate))))
/-- 替换关系的像集存在条件；文献中对应替换公理的后件。 -/
def replacement_collection_core (predicate : ReplacementPredicate) :
    SetFormula :=
  ∀ₘ[SetSort.set,
    replacement_source_parameter predicate],
    ∃ₘ[SetSort.set,
      replacement_target_parameter predicate],
      ∀ₘ[SetSort.set,
        replacement_member_parameter predicate], ((set_variable (replacement_member_parameter predicate) ∈ₘ
              set_variable (replacement_target_parameter predicate)) ↔ₘ (∃ₘ[SetSort.set,
              replacement_witness_parameter predicate], ((set_variable (replacement_witness_parameter predicate) ∈ₘ
                  set_variable (replacement_source_parameter predicate)) ∧ₘ
              replacement_body_at
                predicate (set_variable (replacement_witness_parameter predicate)) (set_variable (replacement_member_parameter predicate)))))
/-- 替换公理模式的开放核心。 -/
def replacement_axiom_core (predicate : ReplacementPredicate) :
    SetFormula :=
  replacement_functionality_core predicate ⟶ₘ
    replacement_collection_core predicate
/-- 替换公理模式的闭实例。 -/
def replacement_axiom (predicate : ReplacementPredicate) :
    SetFormula :=
  Metatheory.Formula.forall_close (Formula.freeSupport (replacement_axiom_core predicate)).eraseDups (replacement_axiom_core predicate)
/-- 所有 proof-carrying 替换实例组成的理论模式。 -/
def replacement_schema : SetTheory :=
  fun formula =>
    ∃ predicate : ReplacementPredicate,
      formula = replacement_axiom predicate
/-- 在自然数算术基础上加入替换模式。 -/
def replacement_theory : SetTheory :=
  fun formula =>
    natural_arithmetic_theory formula ∨
      replacement_schema formula
/-! ## 替换模式的良构性边界 -/
private theorem equality_formula_admissible
    {left right : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Formula.Admissible (left ≐ₘ right) :=
  ⟨FormulaWellFormed.equal hLeft.1 hRight.1,
    FormulaScoped.equal hLeft.2 hRight.2⟩
theorem replacement_functionality_core_admissible (predicate : ReplacementPredicate) :
    Formula.Admissible (replacement_functionality_core predicate) := by
  have hOutput :=
    Formula.Admissible.substituteFree
      SetSort.set 1
      predicate.admissible (set_variable_admissible (replacement_output_parameter predicate))
  have hEquality :=
    equality_formula_admissible (set_variable_admissible 1) (set_variable_admissible (replacement_output_parameter predicate))
  have hBody :=
    Formula.Admissible.imp (Formula.Admissible.conj predicate.admissible hOutput)
      hEquality
  have hBody' :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set (replacement_output_parameter predicate)
      hBody
  have hBody'' :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set 1 hBody'
  have hBody''' :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set 0 hBody''
  simpa [replacement_functionality_core,
    replacement_body_at_output] using hBody'''
theorem replacement_collection_core_admissible (predicate : ReplacementPredicate) :
    Formula.Admissible (replacement_collection_core predicate) := by
  have hInputOutput :=
    Formula.Admissible.substituteFree
      SetSort.set 1
      predicate.admissible (set_variable_admissible (replacement_member_parameter predicate))
  have hInputOutput' :=
    Formula.Admissible.substituteFree
      SetSort.set 0
      hInputOutput (set_variable_admissible (replacement_witness_parameter predicate))
  have hTargetMember :=
    membership_formula_admissible (set_variable_admissible (replacement_member_parameter predicate)) (set_variable_admissible
        (replacement_target_parameter predicate))
  have hSourceMember :=
    membership_formula_admissible (set_variable_admissible (replacement_witness_parameter predicate)) (set_variable_admissible
        (replacement_source_parameter predicate))
  have hMemberSpec :=
    Formula.Admissible.conj hSourceMember hInputOutput'
  have hMemberSpec' :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set (replacement_witness_parameter predicate)
      hMemberSpec
  have hElementSpec :=
    Formula.Admissible.iff hTargetMember hMemberSpec'
  have hElementSpec' :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set (replacement_member_parameter predicate)
      hElementSpec
  have hSetSpec :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set (replacement_target_parameter predicate)
      hElementSpec'
  have hSourceSpec :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set (replacement_source_parameter predicate)
      hSetSpec
  simpa [replacement_collection_core,
    replacement_body_at,
    replacement_body_at_output] using hSourceSpec
theorem replacement_axiom_core_admissible (predicate : ReplacementPredicate) :
    Formula.Admissible (replacement_axiom_core predicate) :=
  Formula.Admissible.imp (replacement_functionality_core_admissible predicate) (replacement_collection_core_admissible predicate)
theorem replacement_axiom_sentence (predicate : ReplacementPredicate) :
    Formula.Sentence (replacement_axiom predicate) :=
  Metatheory.Formula.forall_close_eraseDups_freeSupport_sentence (replacement_axiom_core predicate) (replacement_axiom_core_admissible predicate)
theorem replacement_axiom_admissible (predicate : ReplacementPredicate) :
    Formula.Admissible (replacement_axiom predicate) := (replacement_axiom_sentence predicate).1
theorem replacement_schema_mem (predicate : ReplacementPredicate) :
    replacement_schema (replacement_axiom predicate) :=
  ⟨predicate, rfl⟩
theorem replacement_schema_admissible :
    Theory.Admissible replacement_schema := by
  intro formula hFormula
  rcases hFormula with ⟨predicate, rfl⟩
  exact replacement_axiom_admissible predicate
theorem replacement_theory_admissible :
    Theory.Admissible replacement_theory := by
  intro formula hFormula
  rcases hFormula with hFormula | hFormula
  · exact natural_arithmetic_theory_admissible formula hFormula
  · exact replacement_schema_admissible formula hFormula
@[derive_close_sentence]
theorem replacement_schema_sentence
    {formula : SetFormula} (hFormula : replacement_schema formula) :
    Formula.Sentence formula := by
  rcases hFormula with ⟨predicate, rfl⟩
  exact replacement_axiom_sentence predicate
@[derive_close_sentence]
theorem replacement_theory_sentence
    {formula : SetFormula} (hFormula : replacement_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with hFormula | hFormula
  · exact natural_arithmetic_theory_sentence hFormula
  · exact replacement_schema_sentence hFormula
theorem natural_arithmetic_theory_subset_replacement_theory
    {formula : SetFormula} (hFormula : natural_arithmetic_theory formula) :
    replacement_theory formula :=
  Or.inl hFormula
theorem replacement_schema_subset_replacement_theory
    {formula : SetFormula} (hFormula : replacement_schema formula) :
    replacement_theory formula :=
  Or.inr hFormula
/-! ## 超限递归定义契约 -/
/-- 递归步公式在指定输入、当前值和下一值处的实例。 -/
def recursive_step_body_at (step : RecursiveStep) (index current next : SetTerm) :
    SetFormula := ((step.body ⟪SetSort.set, 1 ↦ current⟫ₘ)
    ⟪SetSort.set, 2 ↦ next⟫ₘ)
    ⟪SetSort.set, 0 ↦ index⟫ₘ
/-- 递归定义契约的候选函数变量，避免捕获种子或递归步参数。 -/
def transfinite_recursion_candidate_parameter (step : RecursiveStep) (seed : SetTerm) :
    FreeVarId :=
  FreshVariable.fresh_id SetSort.set
    [step.body,
      fresh_variable_marker 0,
      fresh_variable_marker 1,
      fresh_variable_marker 2, (seed ≐ₘ seed)]
/--
以 `ω` 为定义域的递归序列规格。
该公式正是文献中 `DGSJ_φ` 右侧的现代压缩形式：候选是以 `ω` 为定义域的
函数，初值为 `seed`，后继位置满足 `step`。`DGSJ` 只保留为文献索引。
-/
def transfinite_recursion_step_condition (step : RecursiveStep) (sequence : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set, 0], ((set_variable 0 ∈ₘ ωₘ) ⟶ₘ (∀ₘ[SetSort.set, 2], (((sequence ·ₘ Sₘ(set_variable 0)) ≐ₘ
            set_variable 2) ↔ₘ
          recursive_step_body_at
            step (set_variable 0) (sequence ·ₘ set_variable 0) (set_variable 2))))
def transfinite_recursion_spec (step : RecursiveStep) (seed sequence : SetTerm) :
    SetFormula :=
  is_function_formula sequence ∧ₘ ((domₘ(sequence) ≐ₘ ωₘ) ∧ₘ (((sequence ·ₘ numₘ(0)) ≐ₘ seed) ∧ₘ
        transfinite_recursion_step_condition
          step sequence))
/--
参数化的第二类递归定义契约。
它不是额外公理，而是后续递归存在性定理要填充的接口：给定初值，候选函数
满足 `transfinite_recursion_spec`。这对应文献中的 `DGSJ_φ(seed)` 引入定义。
-/
def transfinite_recursion_definition_instance (step : RecursiveStep) (seed candidate : SetTerm) :
    SetFormula :=
  transfinite_recursion_spec step seed candidate
def transfinite_recursion_definition (step : RecursiveStep) (seed : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set,
    transfinite_recursion_candidate_parameter step seed],
    transfinite_recursion_definition_instance
      step seed (set_variable (transfinite_recursion_candidate_parameter step seed))
theorem recursive_step_body_at_admissible (step : RecursiveStep) (index current next : SetTerm) (hIndex : Term.Admissible index SetSort.set)
    (hCurrent : Term.Admissible current SetSort.set) (hNext : Term.Admissible next SetSort.set) :
    Formula.Admissible (recursive_step_body_at step index current next) := by
  have hCurrent' :=
    Formula.Admissible.substituteFree
      SetSort.set 1
      step.admissible hCurrent
  have hNext' :=
    Formula.Admissible.substituteFree
      SetSort.set 2 hCurrent' hNext
  exact Formula.Admissible.substituteFree
    SetSort.set 0 hNext' hIndex
theorem transfinite_recursion_spec_admissible (step : RecursiveStep) (seed sequence : SetTerm) (hSeed : Term.Admissible seed SetSort.set)
    (hSequence : Term.Admissible sequence SetSort.set) :
    Formula.Admissible (transfinite_recursion_spec step seed sequence) := by
  have hIndex := set_variable_admissible 0
  have hNext := set_variable_admissible 2
  have hCurrent :=
    function_application_term_admissible
      sequence (x#0) hSequence hIndex
  have hStepBody :=
    recursive_step_body_at_admissible
      step (x#0) (sequence ·ₘ x#0) (x#2)
      hIndex hCurrent hNext
  prove_admissible
theorem transfinite_recursion_definition_admissible (step : RecursiveStep) (seed : SetTerm) (hSeed : Term.Admissible seed SetSort.set) :
    Formula.Admissible (transfinite_recursion_definition step seed) := by
  have hCandidate :
      Term.Admissible (set_variable (transfinite_recursion_candidate_parameter step seed))
        SetSort.set :=
    set_variable_admissible (transfinite_recursion_candidate_parameter step seed)
  have hSpec :=
    transfinite_recursion_spec_admissible
      step seed (set_variable (transfinite_recursion_candidate_parameter step seed))
      hSeed hCandidate
  exact Formula.Admissible.exists_closeFreeAt
    SetSort.set (transfinite_recursion_candidate_parameter step seed)
    hSpec
/-! ## 理论边界 -/
/--
超限递归层不新增独立公理：它消费替换理论，定义契约由后续存在性定理填充。
-/
def hypertransfinite_recursion_theory : SetTheory :=
  replacement_theory
theorem hypertransfinite_recursion_theory_admissible :
    Theory.Admissible
      hypertransfinite_recursion_theory :=
  replacement_theory_admissible
@[derive_close_sentence]
theorem hypertransfinite_recursion_theory_sentence
    {formula : SetFormula} (hFormula : hypertransfinite_recursion_theory formula) :
    Formula.Sentence formula :=
  replacement_theory_sentence hFormula
/-!
## 后续证明留位
映像存在原理、递归函数存在性与唯一性、超限递归定理以及文献中的 `DGSJ` 具体
实例都属于后续定理层。本模块不把它们重复声明为公理，也不把文献中的公式编号
传播到公共接口。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
