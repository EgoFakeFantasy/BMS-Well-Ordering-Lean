import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.StructuralSequenceCondition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuantifier

/-!
# 结构码有限序列条件的直接反演

本模块只抽取直接结构码条件已经携带的数学分量。轨迹见证仍通过有界存在消去
暴露在规范 fresh 槽中，不回退到旧的自然数序列外壳。
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

/-! ## 条件分解 -/

/-- 直接结构码条件的四个数学组成部分。 -/
structure ObjectSequenceConditionParts
    {T : SetTheory}
    {free : SetContext}
    (Γ : Context signature free)
    (source sequence code : SetOpenTerm free) where
  sequence_space : Γ ⊢ₘ[T] sequence ∈ₘ seq_spaceₘ(source)
  code_omega : Γ ⊢ₘ[T] code ∈ₘ ωₘ
  domain_code_bound : Γ ⊢ₘ[T] sequence_domain_code_bound sequence code
  trace_condition : Γ ⊢ₘ[T] object_sequence_code_trace_condition sequence code

/-- 从直接结构码条件中抽取四个数学组成部分。 -/
theorem object_sequence_code_condition_parts
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (source sequence code : SetOpenTerm free)
    (hCondition : Γ ⊢ₘ[T]
      object_sequence_code_condition source sequence code) :
    ObjectSequenceConditionParts (T := T) Γ source sequence code where
  sequence_space := by
    exact FirstOrder.Derives.conj_elim_left <|
      FirstOrder.Derives.conj_elim_left <|
        FirstOrder.Derives.conj_elim_left hCondition
  code_omega := by
    exact FirstOrder.Derives.conj_elim_right <|
      FirstOrder.Derives.conj_elim_left <|
        FirstOrder.Derives.conj_elim_left hCondition
  domain_code_bound := by
    exact FirstOrder.Derives.conj_elim_right <|
      FirstOrder.Derives.conj_elim_left hCondition
  trace_condition := by
    exact FirstOrder.Derives.conj_elim_right hCondition

/-- 结构化公式码条件的直接分解。 -/
theorem structural_proof_sequence_code_condition_parts
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence code : SetOpenTerm free)
    (hCondition : Γ ⊢ₘ[T]
      structural_proof_sequence_code_condition sequence code) :
    ObjectSequenceConditionParts (T := T) Γ
      (syntax_formula_code_set_term : SetOpenTerm free) sequence code := by
  simpa [structural_proof_sequence_code_condition] using
    object_sequence_code_condition_parts
      (syntax_formula_code_set_term : SetOpenTerm free)
      sequence code hCondition

/-! ## 轨迹见证 -/

/-- 结构码轨迹存在式的规范见证上下文。 -/
def object_sequence_code_trace_context
    {free : SetContext}
    (Γ : Context signature free)
    (sequence code : SetOpenTerm free) :
    Context signature (SetSort.set :: free) :=
  Formula.openBoundTop (σ := signature) SetSort.set
      (bounded_exists_body (seq_spaceₘ(ωₘ))
        (object_sequence_code_trace_body
          (sequence.weakenBound SetSort.set)
          (code.weakenBound SetSort.set)
          (.bvar .here))) ::
    FreshVariable.extendContext SetSort.set Γ

/-- 结构码轨迹存在式的规范见证项。 -/
def object_sequence_code_trace_term
    {free : SetContext} : SetOpenTerm (SetSort.set :: free) :=
  FreshVariable.newest (σ := signature) (free := free) SetSort.set

/-- 规范轨迹见证携带的全部直接数学分量。 -/
structure ObjectSequenceTraceParts
    {T : SetTheory}
    {free : SetContext}
    (Γ : Context signature free)
    (sequence code : SetOpenTerm free) where
  trace_space :
    object_sequence_code_trace_context Γ sequence code ⊢ₘ[T]
      object_sequence_code_trace_term ∈ₘ seq_spaceₘ(ωₘ)
  domain_eq :
    object_sequence_code_trace_context Γ sequence code ⊢ₘ[T]
      domₘ(object_sequence_code_trace_term) ≐ₘ
        Sₘ(domₘ(sequence.weakenFree SetSort.set))
  code_bound :
    object_sequence_code_trace_context Γ sequence code ⊢ₘ[T]
      sequence_trace_code_bound object_sequence_code_trace_term
        (code.weakenFree SetSort.set)
  zero_value :
    object_sequence_code_trace_context Γ sequence code ⊢ₘ[T]
      (object_sequence_code_trace_term ·ₘ numₘ(0)) ≐ₘ numₘ(0)
  pointwise :
    object_sequence_code_trace_context Γ sequence code ⊢ₘ[T]
      object_sequence_code_pointwise_condition
        (sequence.weakenFree SetSort.set)
        object_sequence_code_trace_term
        (code.weakenFree SetSort.set)
  final_code :
    object_sequence_code_trace_context Γ sequence code ⊢ₘ[T]
      code.weakenFree SetSort.set ≐ₘ
        godel_pairₘ(
          object_sequence_code_trace_term ·ₘ
            domₘ(sequence.weakenFree SetSort.set),
          domₘ(sequence.weakenFree SetSort.set))

/-- 从轨迹存在式的规范假设中直接抽取全部数学分量。 -/
theorem object_sequence_code_trace_parts_of_assumption
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence code : SetOpenTerm free)
    (hOpened : object_sequence_code_trace_context Γ sequence code ⊢ₘ[T]
      Formula.openBoundTop (σ := signature) SetSort.set
        (bounded_exists_body (seq_spaceₘ(ωₘ))
          (object_sequence_code_trace_body
            (sequence.weakenBound SetSort.set)
            (code.weakenBound SetSort.set)
            (.bvar .here)))) :
    ObjectSequenceTraceParts (T := T) Γ sequence code := by
  rw [bounded_exists_body_openBoundTop] at hOpened
  have hSpace := FirstOrder.Derives.conj_elim_left hOpened
  have hBodyOpened := FirstOrder.Derives.conj_elim_right hOpened
  rw [object_sequence_code_trace_body_openBoundTop] at hBodyOpened
  have hBody : object_sequence_code_trace_context Γ sequence code ⊢ₘ[T]
      object_sequence_code_trace_body
        (sequence.weakenFree SetSort.set)
        (code.weakenFree SetSort.set)
        object_sequence_code_trace_term := by
    simpa [object_sequence_code_trace_term] using! hBodyOpened
  have hDomainAndBound := FirstOrder.Derives.conj_elim_left hBody
  have hZeroAndRest := FirstOrder.Derives.conj_elim_right hBody
  have hDomain := FirstOrder.Derives.conj_elim_left hDomainAndBound
  have hCodeBound := FirstOrder.Derives.conj_elim_right hDomainAndBound
  have hZero := FirstOrder.Derives.conj_elim_left hZeroAndRest
  have hPointwiseAndFinal := FirstOrder.Derives.conj_elim_right hZeroAndRest
  have hPointwise := FirstOrder.Derives.conj_elim_left hPointwiseAndFinal
  have hFinal := FirstOrder.Derives.conj_elim_right hPointwiseAndFinal
  exact {
    trace_space := by
      simpa [object_sequence_code_trace_context,
        object_sequence_code_trace_term] using hSpace
    domain_eq := by
      simpa [object_sequence_code_trace_context,
        object_sequence_code_trace_term] using hDomain
    code_bound := by
      simpa [object_sequence_code_trace_context,
        object_sequence_code_trace_term] using hCodeBound
    zero_value := by
      simpa [object_sequence_code_trace_context,
        object_sequence_code_trace_term] using hZero
    pointwise := by
      simpa [object_sequence_code_trace_context,
        object_sequence_code_trace_term] using hPointwise
    final_code := by
      simpa [object_sequence_code_trace_context,
        object_sequence_code_trace_term] using hFinal
  }

/-- 打开结构码轨迹存在式，并把见证交给后续反演。 -/
theorem object_sequence_code_trace_elim
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence code : SetOpenTerm free)
    {conclusion : SetOpenFormula free}
    (hTrace : Γ ⊢ₘ[T]
      object_sequence_code_trace_condition sequence code)
    (hCase : ObjectSequenceTraceParts (T := T) Γ sequence code →
      object_sequence_code_trace_context Γ sequence code ⊢ₘ[T]
        conclusion.weakenFree SetSort.set) :
    Γ ⊢ₘ[T] conclusion := by
  let body : SetFormula [SetSort.set] free :=
    object_sequence_code_trace_body
      (sequence.weakenBound SetSort.set)
      (code.weakenBound SetSort.set)
      (.bvar .here)
  apply bounded_exists_elim (seq_spaceₘ(ωₘ)) body conclusion
    (by simpa [body, object_sequence_code_trace_condition] using hTrace)
  have hOpened : object_sequence_code_trace_context Γ sequence code ⊢ₘ[T]
      Formula.openBoundTop (σ := signature) SetSort.set
        (bounded_exists_body (seq_spaceₘ(ωₘ)) body) :=
    FirstOrder.Derives.assumption List.mem_cons_self
  simpa [body, object_sequence_code_trace_context] using
    hCase (object_sequence_code_trace_parts_of_assumption
      sequence code hOpened)

/-! ## 逐点消去 -/

/-- 直接一步递推条件的两个数学分量。 -/
structure ObjectSequenceStepParts
    {T : SetTheory}
    {free : SetContext}
    (Γ : Context signature free)
    (trace index element : SetOpenTerm free) where
  element_omega : Γ ⊢ₘ[T] element ∈ₘ ωₘ
  step : Γ ⊢ₘ[T]
    trace ·ₘ Sₘ(index) ≐ₘ
      Sₘ(godel_pairₘ(trace ·ₘ index, element))

/-- 从直接一步递推条件中抽取元素的自然数性与递推等式。 -/
theorem object_sequence_code_step_condition_parts
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence trace index element : SetOpenTerm free)
    (hStep : Γ ⊢ₘ[T]
      object_sequence_code_step_condition sequence trace index element) :
    ObjectSequenceStepParts (T := T) Γ trace index element where
  element_omega := FirstOrder.Derives.conj_elim_left hStep
  step := FirstOrder.Derives.conj_elim_right hStep

/-- 直接逐行条件的三个数学分量。 -/
structure ObjectSequenceRowParts
    {T : SetTheory}
    {free : SetContext}
    (Γ : Context signature free)
    (sequence trace code index : SetOpenTerm free) where
  member_bound : Γ ⊢ₘ[T] sequence ·ₘ index ∈ₘ Sₘ(code)
  element_omega : Γ ⊢ₘ[T] sequence ·ₘ index ∈ₘ ωₘ
  step : Γ ⊢ₘ[T]
    trace ·ₘ Sₘ(index) ≐ₘ
      Sₘ(godel_pairₘ(trace ·ₘ index, sequence ·ₘ index))

/-- 从直接逐行条件中抽取成员界、元素自然数性与递推等式。 -/
theorem object_sequence_code_row_condition_parts
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence trace code index : SetOpenTerm free)
    (hRow : Γ ⊢ₘ[T]
      object_sequence_code_row_condition sequence trace code index) :
    ObjectSequenceRowParts (T := T) Γ sequence trace code index where
  member_bound := FirstOrder.Derives.conj_elim_left hRow
  element_omega := FirstOrder.Derives.conj_elim_left <|
    FirstOrder.Derives.conj_elim_right hRow
  step := FirstOrder.Derives.conj_elim_right <|
    FirstOrder.Derives.conj_elim_right hRow

/-- 直接结构码逐点条件可在任意定义域点实例化。 -/
theorem object_sequence_code_row_condition_at
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence trace code index : SetOpenTerm free)
    (hPointwise : Γ ⊢ₘ[T]
      object_sequence_code_pointwise_condition sequence trace code)
    (hIndex : Γ ⊢ₘ[T] index ∈ₘ domₘ(sequence)) :
    Γ ⊢ₘ[T]
      object_sequence_code_row_condition sequence trace code index := by
  have hValue := bounded_forall_elim
    (domₘ(sequence))
    (object_sequence_code_row_condition
      (sequence.weakenBound SetSort.set)
      (trace.weakenBound SetSort.set)
      (code.weakenBound SetSort.set)
      (.bvar .here))
    index hPointwise hIndex
  rw [object_sequence_code_row_condition_weakenBound_instantiateTop] at hValue
  exact hValue

/-- 直接结构码逐点条件在任意定义域点给出完整行分量。 -/
theorem object_sequence_code_row_condition_parts_at
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence trace code index : SetOpenTerm free)
    (hPointwise : Γ ⊢ₘ[T]
      object_sequence_code_pointwise_condition sequence trace code)
    (hIndex : Γ ⊢ₘ[T] index ∈ₘ domₘ(sequence)) :
    ObjectSequenceRowParts (T := T) Γ sequence trace code index :=
  object_sequence_code_row_condition_parts
    sequence trace code index
    (object_sequence_code_row_condition_at
      sequence trace code index hPointwise hIndex)

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
