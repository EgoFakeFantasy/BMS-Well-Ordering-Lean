import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceCondition

/-!
# 结构码有限序列条件

本模块把证明序列的行值直接当作对象自然数参与 Gödel 配数。旧关系要求每个行值
先满足一个内层自然数序列条件；这里改为直接检查行值属于 `ωₘ`，从而可以直接
消费 Quine 结构公式码，不再为结构码伪造数字序列外壳。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-! ## 直接递推条件 -/

def object_sequence_code_step_condition {bound free : SetContext}
    (_sequence trace index element : SetTerm bound free) : SetFormula bound free :=
  (element ∈ₘ ωₘ) ∧ₘ
    ((trace ·ₘ Sₘ(index)) ≐ₘ
      Sₘ(godel_pairₘ(trace ·ₘ index, element)))

def object_sequence_code_row_condition {bound free : SetContext}
    (sequence trace code index : SetTerm bound free) : SetFormula bound free :=
  (sequence ·ₘ index ∈ₘ Sₘ(code)) ∧ₘ
    object_sequence_code_step_condition
      sequence trace index (sequence ·ₘ index)

def object_sequence_code_pointwise_condition {bound free : SetContext}
    (sequence trace code : SetTerm bound free) : SetFormula bound free :=
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let traceOne : SetTerm (SetSort.set :: bound) free :=
    trace.weakenBound SetSort.set
  let codeOne : SetTerm (SetSort.set :: bound) free :=
    code.weakenBound SetSort.set
  Formula.LevyBound.boundedForall set_levy_bound
    (domₘ(sequence))
    (object_sequence_code_row_condition
      sequenceOne traceOne codeOne (.bvar .here))

def object_sequence_code_trace_body {bound free : SetContext}
    (sequence code trace : SetTerm bound free) : SetFormula bound free :=
  ((domₘ(trace) ≐ₘ Sₘ(domₘ(sequence))) ∧ₘ
      sequence_trace_code_bound trace code) ∧ₘ
    ((trace ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
      (object_sequence_code_pointwise_condition sequence trace code ∧ₘ
        (code ≐ₘ
          godel_pairₘ(trace ·ₘ domₘ(sequence), domₘ(sequence))))

def object_sequence_code_trace_condition {bound free : SetContext}
    (sequence code : SetTerm bound free) : SetFormula bound free :=
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let codeOne : SetTerm (SetSort.set :: bound) free :=
    code.weakenBound SetSort.set
  Formula.LevyBound.boundedExists set_levy_bound
    (seq_spaceₘ(ωₘ))
    (object_sequence_code_trace_body
      sequenceOne codeOne (.bvar .here))

/-- 任意对象自然数承载集合上的直接有限序列编码条件。 -/
def object_sequence_code_condition {bound free : SetContext}
    (source sequence code : SetTerm bound free) : SetFormula bound free :=
  ((((sequence ∈ₘ seq_spaceₘ(source)) ∧ₘ
      (code ∈ₘ ωₘ)) ∧ₘ sequence_domain_code_bound sequence code) ∧ₘ
    object_sequence_code_trace_condition sequence code)

/-- 结构化公式码的直接有限序列编码条件。 -/
def structural_proof_sequence_code_condition {bound free : SetContext}
    (sequence code : SetTerm bound free) : SetFormula bound free :=
  object_sequence_code_condition syntax_formula_code_set_term sequence code

/-! ## 替换自然性 -/

@[simp] theorem object_sequence_code_row_condition_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (sequence trace code index : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (object_sequence_code_row_condition sequence trace code index) =
      object_sequence_code_row_condition
        (sequence.substituteMapped boundSubstitution freeSubstitution)
        (trace.substituteMapped boundSubstitution freeSubstitution)
        (code.substituteMapped boundSubstitution freeSubstitution)
        (index.substituteMapped boundSubstitution freeSubstitution) := by
  simp [object_sequence_code_row_condition,
    object_sequence_code_step_condition,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped]

@[simp] theorem object_sequence_code_trace_body_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (sequence code trace : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (object_sequence_code_trace_body sequence code trace) =
      object_sequence_code_trace_body
        (sequence.substituteMapped boundSubstitution freeSubstitution)
        (code.substituteMapped boundSubstitution freeSubstitution)
        (trace.substituteMapped boundSubstitution freeSubstitution) := by
  simp [object_sequence_code_trace_body,
    object_sequence_code_pointwise_condition,
    object_sequence_code_row_condition,
    object_sequence_code_step_condition, sequence_trace_code_bound,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership,
    VariableSubstitution.liftBound,
    Term.substituteMapped_weakenBound]

@[simp] theorem object_sequence_code_row_condition_instantiateTop
    {bound free : SetContext}
    (sequence trace code index :
      SetTerm (SetSort.set :: bound) free)
    (replacement : SetTerm bound free) :
    Formula.instantiateTop replacement
        (object_sequence_code_row_condition sequence trace code index) =
      object_sequence_code_row_condition
        (sequence.instantiateTop replacement)
        (trace.instantiateTop replacement)
        (code.instantiateTop replacement)
        (index.instantiateTop replacement) := by
  change Formula.substituteMapped
      (VariableSubstitution.instantiateTop replacement)
      VariableSubstitution.freeId
      (object_sequence_code_row_condition sequence trace code index) = _
  rw [object_sequence_code_row_condition_substituteMapped]
  rfl

@[simp] theorem object_sequence_code_trace_body_instantiateTop
    {bound free : SetContext}
    (sequence code trace : SetTerm (SetSort.set :: bound) free)
    (replacement : SetTerm bound free) :
    Formula.instantiateTop replacement
        (object_sequence_code_trace_body sequence code trace) =
      object_sequence_code_trace_body
        (sequence.instantiateTop replacement)
        (code.instantiateTop replacement)
        (trace.instantiateTop replacement) := by
  change Formula.substituteMapped
      (VariableSubstitution.instantiateTop replacement)
      VariableSubstitution.freeId
      (object_sequence_code_trace_body sequence code trace) = _
  rw [object_sequence_code_trace_body_substituteMapped]
  rfl

@[simp] theorem object_sequence_code_trace_body_openBoundTop
    {free : SetContext}
    (sequence code trace : SetTerm [SetSort.set] free) :
    Formula.openBoundTop (σ := signature) SetSort.set
        (object_sequence_code_trace_body sequence code trace) =
      object_sequence_code_trace_body
        (Term.openBoundTop (σ := signature) SetSort.set sequence)
        (Term.openBoundTop (σ := signature) SetSort.set code)
        (Term.openBoundTop (σ := signature) SetSort.set trace) := by
  change Formula.substituteMapped
      (VariableSubstitution.instantiateTop
        (FreshVariable.newest (σ := signature) (free := free)
          SetSort.set))
      (VariableSubstitution.of_renaming
        (VariableRenaming.weaken SetSort.set))
      (object_sequence_code_trace_body sequence code trace) = _
  rw [object_sequence_code_trace_body_substituteMapped]
  rfl

@[simp] theorem object_sequence_code_row_condition_weakenBound_instantiateTop
    {free : SetContext}
    (sequence trace code index : SetOpenTerm free) :
    Formula.instantiateTop index
        (object_sequence_code_row_condition
          (sequence.weakenBound SetSort.set)
          (trace.weakenBound SetSort.set)
          (code.weakenBound SetSort.set)
          (.bvar .here)) =
      object_sequence_code_row_condition sequence trace code index := by
  simp [object_sequence_code_row_condition,
    object_sequence_code_step_condition,
    Formula.instantiateTop, Substitution.instantiateTop,
    Formula.substitute, Formula.substituteMapped, Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.instantiateTop]

@[simp] theorem object_sequence_code_trace_body_weakenBound_instantiateTop
    {free : SetContext}
    (sequence code trace : SetOpenTerm free) :
    Formula.instantiateTop trace
        (object_sequence_code_trace_body
          (sequence.weakenBound SetSort.set)
          (code.weakenBound SetSort.set)
          (.bvar .here)) =
      object_sequence_code_trace_body sequence code trace := by
  simp [object_sequence_code_trace_body,
    object_sequence_code_pointwise_condition,
    object_sequence_code_row_condition,
    object_sequence_code_step_condition, sequence_trace_code_bound,
    Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    Formula.instantiateTop, Substitution.instantiateTop,
    Formula.substitute, Formula.substituteMapped, Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.instantiateTop, VariableSubstitution.liftBound]

@[simp] theorem object_sequence_code_condition_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (source sequence code : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (object_sequence_code_condition source sequence code) =
      object_sequence_code_condition
        (source.substituteMapped boundSubstitution freeSubstitution)
        (sequence.substituteMapped boundSubstitution freeSubstitution)
        (code.substituteMapped boundSubstitution freeSubstitution) := by
  simp [object_sequence_code_condition,
    object_sequence_code_trace_condition,
    object_sequence_code_trace_body,
    object_sequence_code_pointwise_condition,
    object_sequence_code_row_condition,
    object_sequence_code_step_condition,
    sequence_domain_code_bound, sequence_trace_code_bound,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, Formula.LevyBound.boundedExists,
    Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    VariableSubstitution.liftBound,
    Term.substituteMapped_weakenBound]

@[simp] theorem structural_proof_sequence_code_condition_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (sequence code : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (structural_proof_sequence_code_condition sequence code) =
      structural_proof_sequence_code_condition
        (sequence.substituteMapped boundSubstitution freeSubstitution)
        (code.substituteMapped boundSubstitution freeSubstitution) := by
  simp [structural_proof_sequence_code_condition]

/-! ## `Delta0` 分类 -/

theorem object_sequence_code_step_condition_delta0
    {bound free : SetContext}
    (sequence trace index element : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (object_sequence_code_step_condition
        sequence trace index element) := by
  exact Formula.IsDelta0.conj
    (Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.membership 𝒂ₘ(element, ωₘ))
    (Formula.IsDelta0.equal
      (trace ·ₘ Sₘ(index))
      (Sₘ(godel_pairₘ(trace ·ₘ index, element))))

theorem object_sequence_code_row_condition_delta0
    {bound free : SetContext}
    (sequence trace code index : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (object_sequence_code_row_condition
        sequence trace code index) := by
  exact Formula.IsDelta0.conj
    (Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.membership
      𝒂ₘ(sequence ·ₘ index, Sₘ(code)))
    (object_sequence_code_step_condition_delta0
      sequence trace index (sequence ·ₘ index))

theorem object_sequence_code_pointwise_condition_delta0
    {bound free : SetContext}
    (sequence trace code : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (object_sequence_code_pointwise_condition sequence trace code) := by
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let traceOne : SetTerm (SetSort.set :: bound) free :=
    trace.weakenBound SetSort.set
  let codeOne : SetTerm (SetSort.set :: bound) free :=
    code.weakenBound SetSort.set
  have hRow := object_sequence_code_row_condition_delta0
    sequenceOne traceOne codeOne (.bvar .here)
  simpa [object_sequence_code_pointwise_condition, sequenceOne,
    traceOne, codeOne, Formula.LevyBound.boundedForall] using
    Formula.IsDelta0.bounded_forall (domₘ(sequence)) hRow

private theorem object_sequence_trace_code_bound_delta0
    {bound free : SetContext}
    (trace code : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (sequence_trace_code_bound trace code) := by
  let traceOne : SetTerm (SetSort.set :: bound) free :=
    trace.weakenBound SetSort.set
  let codeOne : SetTerm (SetSort.set :: bound) free :=
    code.weakenBound SetSort.set
  have hBody :
      Formula.IsDelta0 set_levy_bound
        ((traceOne ·ₘ (.bvar .here)) ∈ₘ Sₘ(codeOne)) :=
    Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.membership
      𝒂ₘ(traceOne ·ₘ (.bvar .here), Sₘ(codeOne))
  simpa [sequence_trace_code_bound, traceOne, codeOne,
    Formula.LevyBound.boundedForall] using
    (Formula.IsDelta0.bounded_forall
      (domₘ(trace)) hBody)

private theorem object_sequence_domain_code_bound_delta0
    {bound free : SetContext}
    (sequence code : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (sequence_domain_code_bound sequence code) := by
  exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
    RelationSymbol.membership
    𝒂ₘ(domₘ(sequence), Sₘ(code))

theorem object_sequence_code_trace_body_delta0
    {bound free : SetContext}
    (sequence code trace : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (object_sequence_code_trace_body sequence code trace) := by
  let traceDomain : SetFormula bound free :=
    domₘ(trace) ≐ₘ Sₘ(domₘ(sequence))
  let traceBound : SetFormula bound free :=
    sequence_trace_code_bound trace code
  let traceZero : SetFormula bound free :=
    (trace ·ₘ numₘ(0)) ≐ₘ numₘ(0)
  let pointwise : SetFormula bound free :=
    object_sequence_code_pointwise_condition sequence trace code
  let traceCode : SetFormula bound free :=
    code ≐ₘ godel_pairₘ(trace ·ₘ domₘ(sequence), domₘ(sequence))
  have hDomain : Formula.IsDelta0 set_levy_bound traceDomain :=
    Formula.IsDelta0.equal (domₘ(trace)) (Sₘ(domₘ(sequence)))
  have hBound : Formula.IsDelta0 set_levy_bound traceBound :=
    object_sequence_trace_code_bound_delta0 trace code
  have hZero : Formula.IsDelta0 set_levy_bound traceZero :=
    Formula.IsDelta0.equal (trace ·ₘ numₘ(0)) (numₘ(0))
  have hPointwise : Formula.IsDelta0 set_levy_bound pointwise :=
    object_sequence_code_pointwise_condition_delta0 sequence trace code
  have hCode : Formula.IsDelta0 set_levy_bound traceCode :=
    Formula.IsDelta0.equal code
      (godel_pairₘ(trace ·ₘ domₘ(sequence), domₘ(sequence)))
  simpa [object_sequence_code_trace_body, traceDomain, traceBound,
    traceZero, pointwise, traceCode] using
    Formula.IsDelta0.conj
      (Formula.IsDelta0.conj hDomain hBound)
      (Formula.IsDelta0.conj hZero
        (Formula.IsDelta0.conj hPointwise hCode))

theorem object_sequence_code_trace_condition_delta0
    {bound free : SetContext}
    (sequence code : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (object_sequence_code_trace_condition sequence code) := by
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let codeOne : SetTerm (SetSort.set :: bound) free :=
    code.weakenBound SetSort.set
  let traceBody : SetFormula (SetSort.set :: bound) free :=
    object_sequence_code_trace_body sequenceOne codeOne (.bvar .here)
  have hBody := object_sequence_code_trace_body_delta0
    sequenceOne codeOne (.bvar .here)
  simpa [object_sequence_code_trace_condition, sequenceOne, codeOne,
    traceBody, Formula.LevyBound.boundedExists] using
    Formula.IsDelta0.bounded_exists
      (seq_spaceₘ(ωₘ)) hBody

theorem object_sequence_code_condition_delta0
    {bound free : SetContext}
    (source sequence code : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (object_sequence_code_condition source sequence code) := by
  let prefixFormula : SetFormula bound free :=
    (((sequence ∈ₘ seq_spaceₘ(source)) ∧ₘ (code ∈ₘ ωₘ)) ∧ₘ
      sequence_domain_code_bound sequence code)
  have hPrefix : Formula.IsDelta0 set_levy_bound prefixFormula :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.rel (ℬ := set_levy_bound)
          RelationSymbol.membership 𝒂ₘ(sequence, seq_spaceₘ(source)))
        (Formula.IsDelta0.rel (ℬ := set_levy_bound)
          RelationSymbol.membership 𝒂ₘ(code, ωₘ)))
      (object_sequence_domain_code_bound_delta0 sequence code)
  have hTrace := object_sequence_code_trace_condition_delta0 sequence code
  simpa [object_sequence_code_condition, prefixFormula] using
    Formula.IsDelta0.conj hPrefix hTrace

theorem structural_proof_sequence_code_condition_delta0
    {bound free : SetContext}
    (sequence code : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (structural_proof_sequence_code_condition sequence code) := by
  simpa [structural_proof_sequence_code_condition] using
    object_sequence_code_condition_delta0
      (syntax_formula_code_set_term : SetTerm bound free) sequence code

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
