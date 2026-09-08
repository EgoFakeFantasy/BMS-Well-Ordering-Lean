import YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofCode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.LanguageEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CodeDomain
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicFormulaTemplate

/-!
# ProofT 的内在有限序列编码条件

本模块只给出自然数序列编码、公式代码序列编码与末行关系。
轨迹、索引和行码见证全部由 free 上下文携带，不暴露编号参数或支持集证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

def nat_sequence_code_step_condition {bound free : SetContext}
    (sequence trace index : SetTerm bound free) : SetFormula bound free :=
  (trace ·ₘ Sₘ(index)) ≐ₘ
    Sₘ(godel_pairₘ(trace ·ₘ index, sequence ·ₘ index))

def sequence_domain_code_bound {bound free : SetContext}
    (sequence code : SetTerm bound free) : SetFormula bound free :=
  domₘ(sequence) ∈ₘ Sₘ(code)

def nat_sequence_value_code_bound {bound free : SetContext}
    (sequence code : SetTerm bound free) : SetFormula bound free :=
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let codeOne : SetTerm (SetSort.set :: bound) free :=
    code.weakenBound SetSort.set
  let index : SetTerm (SetSort.set :: bound) free := .bvar .here
  Formula.LevyBound.boundedForall ProofT.set_levy_bound
    (domₘ(sequence))
    ((sequenceOne ·ₘ index) ∈ₘ codeOne)

def sequence_trace_code_bound {bound free : SetContext}
    (trace code : SetTerm bound free) : SetFormula bound free :=
  let traceOne : SetTerm (SetSort.set :: bound) free :=
    trace.weakenBound SetSort.set
  let codeOne : SetTerm (SetSort.set :: bound) free :=
    code.weakenBound SetSort.set
  let index : SetTerm (SetSort.set :: bound) free := .bvar .here
  Formula.LevyBound.boundedForall ProofT.set_levy_bound
    (domₘ(trace))
    ((traceOne ·ₘ index) ∈ₘ Sₘ(codeOne))

def nat_sequence_code_trace_condition {bound free : SetContext}
    (sequence code trace : SetTerm (SetSort.set :: bound) free) :
    SetFormula (SetSort.set :: bound) free :=
  let sequenceTwo : SetTerm
      (SetSort.set :: SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let traceTwo : SetTerm
      (SetSort.set :: SetSort.set :: bound) free :=
    .bvar (.there .here)
  let index : SetTerm
      (SetSort.set :: SetSort.set :: bound) free := .bvar .here
  let stepBody : SetFormula
      (SetSort.set :: SetSort.set :: bound) free :=
    nat_sequence_code_step_condition sequenceTwo traceTwo index
  let stepCondition : SetFormula (SetSort.set :: bound) free :=
    Formula.LevyBound.boundedForall ProofT.set_levy_bound
      (domₘ(sequence)) stepBody
  (trace ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
    (((domₘ(trace) ≐ₘ Sₘ(domₘ(sequence))) ∧ₘ
      sequence_trace_code_bound trace code) ∧ₘ
      ((trace ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
      (stepCondition ∧ₘ (code ≐ₘ (trace ·ₘ domₘ(sequence)))))

def nat_sequence_code_condition {bound free : SetContext}
    (sequence code : SetTerm bound free) : SetFormula bound free :=
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let codeOne : SetTerm (SetSort.set :: bound) free :=
    code.weakenBound SetSort.set
  let trace : SetTerm (SetSort.set :: bound) free := .bvar .here
  let traceCondition :=
    nat_sequence_code_trace_condition sequenceOne codeOne trace
  ((((sequence ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ (code ∈ₘ ωₘ)) ∧ₘ
    sequence_domain_code_bound sequence code) ∧ₘ
    nat_sequence_value_code_bound sequence code) ∧ₘ
    traceCondition.existsE SetSort.set

/-- 自然数序列编码条件与任意类型化替换交换。 -/
@[simp] theorem nat_sequence_code_condition_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (sequence code : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (nat_sequence_code_condition sequence code) =
      nat_sequence_code_condition
        (sequence.substituteMapped boundSubstitution freeSubstitution)
        (code.substituteMapped boundSubstitution freeSubstitution) := by
  simp [nat_sequence_code_condition, sequence_domain_code_bound,
    nat_sequence_value_code_bound, sequence_trace_code_bound,
    nat_sequence_code_trace_condition, nat_sequence_code_step_condition,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped,
    Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    VariableSubstitution.liftBound,
    Term.substituteMapped_weakenBound]

/-! 顶部实例化快路：直接复用通用替换闭合性。 -/

@[simp] theorem nat_sequence_code_condition_instantiateTop
    {bound free : SetContext}
    (sequence code : SetTerm (SetSort.set :: bound) free)
    (replacement : SetTerm bound free) :
    Formula.instantiateTop replacement
        (nat_sequence_code_condition sequence code) =
      nat_sequence_code_condition
        (sequence.instantiateTop replacement)
        (code.instantiateTop replacement) := by
  change Formula.substituteMapped
      (VariableSubstitution.instantiateTop replacement)
      VariableSubstitution.freeId
      (nat_sequence_code_condition sequence code) = _
  rw [nat_sequence_code_condition_substituteMapped]
  rfl

/-- 二维证明序列递推步的四槽内在公式模板。 -/
def ProofT.proof_sequence_code_step_condition_template :
    ProofT.FormulaTemplate.Quaternary where
  body :=
    let sequence : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
      .fvar .here
    let trace : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
      .fvar (.there .here)
    let index : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
      .fvar (.there (.there .here))
    let rowCode : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
      .fvar (.there (.there (.there .here)))
    nat_sequence_code_condition (sequence ·ₘ index) rowCode ∧ₘ
      ((trace ·ₘ Sₘ(index)) ≐ₘ
        Sₘ(godel_pairₘ(trace ·ₘ index, rowCode)))

def proof_sequence_code_step_condition {bound free : SetContext}
    (sequence trace index rowCode : SetTerm bound free) : SetFormula bound free :=
  ProofT.proof_sequence_code_step_condition_template
    sequence trace index rowCode

/-- 四槽递推步直接命中规范 bound 打开快路。 -/
@[simp] theorem proof_sequence_code_step_condition_openBoundTop
    {free : SetContext}
    (sequence trace index rowCode : SetTerm [SetSort.set] free) :
    Formula.openBoundTop (σ := signature) SetSort.set
        (proof_sequence_code_step_condition
          sequence trace index rowCode) =
      proof_sequence_code_step_condition
        (Term.openBoundTop (σ := signature) SetSort.set sequence)
        (Term.openBoundTop (σ := signature) SetSort.set trace)
        (Term.openBoundTop (σ := signature) SetSort.set index)
        (Term.openBoundTop (σ := signature) SetSort.set rowCode) := by
  exact ProofT.FormulaTemplate.apply_four_openBoundTop_arguments
    ProofT.proof_sequence_code_step_condition_template
    sequence trace index rowCode

/-- 二维证明序列逐行条件的四槽内在公式模板。 -/
def ProofT.proof_sequence_code_row_condition_template :
    ProofT.FormulaTemplate.Quaternary where
  body :=
    let sequence : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
      .fvar .here
    let trace : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
      .fvar (.there .here)
    let code : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
      .fvar (.there (.there .here))
    let index : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
      .fvar (.there (.there (.there .here)))
    Formula.LevyBound.boundedExists ProofT.set_levy_bound code
      (proof_sequence_code_step_condition
        (sequence.weakenBound SetSort.set)
        (trace.weakenBound SetSort.set)
        (index.weakenBound SetSort.set)
        (.bvar .here))

def proof_sequence_code_row_condition {bound free : SetContext}
    (sequence trace code index : SetTerm bound free) : SetFormula bound free :=
  ProofT.proof_sequence_code_row_condition_template
    sequence trace code index

/-- 四槽逐行条件直接命中公式模板的顶部实例化快路。 -/
@[simp] theorem proof_sequence_code_row_condition_instantiateTop
    {bound free : SetContext}
    (sequence trace code index :
      SetTerm (SetSort.set :: bound) free)
    (replacement : SetTerm bound free) :
    Formula.instantiateTop replacement
        (proof_sequence_code_row_condition sequence trace code index) =
      proof_sequence_code_row_condition
        (sequence.instantiateTop replacement)
        (trace.instantiateTop replacement)
        (code.instantiateTop replacement)
        (index.instantiateTop replacement) := by
  exact ProofT.FormulaTemplate.apply_four_instantiateTop_arguments
    ProofT.proof_sequence_code_row_condition_template
    sequence trace code index replacement

/-! 逐行步条件以顶部见证项实例化时直接恢复四槽条件。 -/
@[simp] theorem proof_sequence_code_step_condition_instantiateTop_bvar
    {free : SetContext}
    (sequence trace index rowCode : SetOpenTerm free) :
    Formula.instantiateTop rowCode
        (proof_sequence_code_step_condition
          (sequence.weakenBound SetSort.set)
          (trace.weakenBound SetSort.set)
          (index.weakenBound SetSort.set)
          (.bvar .here)) =
      proof_sequence_code_step_condition sequence trace index rowCode := by
  change Formula.instantiateTop rowCode
      (ProofT.proof_sequence_code_step_condition_template
        (sequence.weakenBound SetSort.set)
        (trace.weakenBound SetSort.set)
        (index.weakenBound SetSort.set)
        (.bvar .here)) =
    ProofT.proof_sequence_code_step_condition_template
      sequence trace index rowCode
  rw [ProofT.FormulaTemplate.apply_four_instantiateTop_arguments]
  simp only [Term.instantiateTop_weakenBound]
  rfl

def proof_sequence_code_pointwise_condition {bound free : SetContext}
    (sequence trace code : SetTerm bound free) : SetFormula bound free :=
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let traceOne : SetTerm (SetSort.set :: bound) free :=
    trace.weakenBound SetSort.set
  let codeOne : SetTerm (SetSort.set :: bound) free :=
    code.weakenBound SetSort.set
  Formula.LevyBound.boundedForall ProofT.set_levy_bound
    (domₘ(sequence))
    (proof_sequence_code_row_condition
      sequenceOne traceOne codeOne (.bvar .here))

/-- 二维证明序列轨迹主体的三槽内在公式模板。 -/
def ProofT.proof_sequence_code_trace_body_template :
    ProofT.FormulaTemplate.Ternary where
  body :=
    let sequence : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set] :=
      .fvar .here
    let code : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set] :=
      .fvar (.there .here)
    let trace : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set] :=
      .fvar (.there (.there .here))
    ((domₘ(trace) ≐ₘ Sₘ(domₘ(sequence))) ∧ₘ
      sequence_trace_code_bound trace code) ∧ₘ
      ((trace ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
      (proof_sequence_code_pointwise_condition sequence trace code ∧ₘ
        (code ≐ₘ (trace ·ₘ domₘ(sequence))))

def proof_sequence_code_trace_body {bound free : SetContext}
    (sequence code trace : SetTerm bound free) : SetFormula bound free :=
  ProofT.proof_sequence_code_trace_body_template sequence code trace

/-- 三槽轨迹主体直接命中规范 bound 打开快路。 -/
@[simp] theorem proof_sequence_code_trace_body_openBoundTop
    {free : SetContext}
    (sequence code trace : SetTerm [SetSort.set] free) :
    Formula.openBoundTop (σ := signature) SetSort.set
        (proof_sequence_code_trace_body sequence code trace) =
      proof_sequence_code_trace_body
        (Term.openBoundTop (σ := signature) SetSort.set sequence)
        (Term.openBoundTop (σ := signature) SetSort.set code)
        (Term.openBoundTop (σ := signature) SetSort.set trace) := by
  exact ProofT.FormulaTemplate.apply_three_openBoundTop_arguments
    ProofT.proof_sequence_code_trace_body_template sequence code trace

def proof_sequence_code_trace_condition {bound free : SetContext}
    (sequence code : SetTerm bound free) : SetFormula bound free :=
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let codeOne : SetTerm (SetSort.set :: bound) free :=
    code.weakenBound SetSort.set
  Formula.LevyBound.boundedExists ProofT.set_levy_bound
    (seq_spaceₘ(ωₘ))
    (proof_sequence_code_trace_body sequenceOne codeOne (.bvar .here))

def proof_sequence_code_condition {bound free : SetContext}
    (sequence code : SetTerm bound free) : SetFormula bound free :=
  ((((sequence ∈ₘ seq_spaceₘ(syntax_formula_code_set_term)) ∧ₘ
      (code ∈ₘ ωₘ)) ∧ₘ sequence_domain_code_bound sequence code) ∧ₘ
    proof_sequence_code_trace_condition sequence code)

def proof_sequence_terminal_condition {bound free : SetContext}
    (sequence conclusion : SetTerm bound free) : SetFormula bound free :=
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let conclusionOne : SetTerm (SetSort.set :: bound) free :=
    conclusion.weakenBound SetSort.set
  let lastBody : SetFormula (SetSort.set :: bound) free :=
    (domₘ(sequenceOne) ≐ₘ Sₘ(.bvar .here)) ∧ₘ
      (conclusionOne ≐ₘ (sequenceOne ·ₘ .bvar .here))
  Formula.LevyBound.boundedExists ProofT.set_levy_bound
    (domₘ(sequence)) lastBody

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
