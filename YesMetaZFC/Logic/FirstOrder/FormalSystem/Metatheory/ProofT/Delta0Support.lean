import YesMetaZFC.Logic.FirstOrder.FormalSystem.FiniteSequenceConcatenation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Hierarchy
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceCondition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.StructuredCertificateCondition

/-!
# `ProofT` 的内在 `Delta0` 条件

本模块只收集不依赖具体 replay 的低层句法事实。函数图谓词、有界图条件、映射条件和
有限序列条件都直接使用内在项与公式；变量作用域由上下文类型记录，不再维护
`Admissible`、`freeSupport` 或裸变量编号。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open StructuredCertificateCondition

set_option autoImplicit false

theorem function_formula_delta0
    {bound free : SetContext}
    (function : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (is_function_formula function) := by
  exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
    RelationSymbol.isFunction 𝒂ₘ(function)

/-- 有界函数图的母集项。 -/
def bounded_graph_guard {bound free : SetContext}
    (source target : SetTerm bound free) : SetTerm bound free :=
  𝒫ₘ(source ×ₘ target)

/-- 图成员的有界原子条件。 -/
def bounded_graph_condition {bound free : SetContext}
    (graph source target : SetTerm bound free) : SetFormula bound free :=
  graph ∈ₘ bounded_graph_guard source target

theorem bounded_graph_condition_delta0
    {bound free : SetContext}
    (graph source target : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (bounded_graph_condition graph source target) := by
  exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
    RelationSymbol.membership
    𝒂ₘ(graph, bounded_graph_guard source target)

/-- 有界映射条件同时保留图界与映射谓词。 -/
def bounded_mapping_condition {bound free : SetContext}
    (graph source target : SetTerm bound free) : SetFormula bound free :=
  bounded_graph_condition graph source target ∧ₘ
    is_mapping_formula graph source target

theorem bounded_mapping_condition_delta0
    {bound free : SetContext}
    (graph source target : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (bounded_mapping_condition graph source target) := by
  exact Formula.IsDelta0.conj
    (bounded_graph_condition_delta0 graph source target)
    (Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.isMapping
      𝒂ₘ(graph, source, target))

/-- 函数在一个坐标上的逐点值界。 -/
def function_value_bound_condition {bound free : SetContext}
    (graph target index : SetTerm bound free) : SetFormula bound free :=
  (index ∈ₘ domₘ(graph)) ⟶ₘ
    ((graph ·ₘ index) ∈ₘ target)

theorem function_value_bound_condition_delta0
    {bound free : SetContext}
    (graph target index : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (function_value_bound_condition graph target index) := by
  exact Formula.IsDelta0.imp
    (Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.membership
      𝒂ₘ(index, domₘ(graph)))
    (Formula.IsDelta0.rel
      (ℬ := set_levy_bound)
      RelationSymbol.membership
      𝒂ₘ(graph ·ₘ index, target))

/-- 局部有界函数条件。 -/
def bounded_function_condition {bound free : SetContext}
    (graph domainFamily target index : SetTerm bound free) : SetFormula bound free :=
  (is_function_formula graph ∧ₘ
    (domₘ(graph) ∈ₘ domainFamily)) ∧ₘ
    function_value_bound_condition graph target index

/-- 函数图对任意定义域元素的全称值界。 -/
def function_value_bound {bound free : SetContext}
    (graph target : SetTerm bound free) : SetFormula bound free :=
  Formula.LevyBound.boundedForall set_levy_bound
    (domₘ(graph))
    ((graph.weakenBound SetSort.set ·ₘ (.bvar .here)) ∈ₘ
      target.weakenBound SetSort.set)

@[simp] theorem function_value_bound_weakenFree
    {bound free : SetContext}
    (introduced : SetSort)
    (graph target : SetTerm bound free) :
    (function_value_bound graph target).weakenFree introduced =
      function_value_bound (graph.weakenFree introduced)
        (target.weakenFree introduced) := by
  have hGraph :
      (graph.weakenBound SetSort.set).renameMapped
          VariableRenaming.id (VariableRenaming.weaken introduced) =
        (graph.weakenBound SetSort.set).weakenFree introduced := by
    exact Term.renameMapped_id_weaken
      (graph.weakenBound SetSort.set)
  have hTarget :
      (target.weakenBound SetSort.set).renameMapped
          VariableRenaming.id (VariableRenaming.weaken introduced) =
        (target.weakenBound SetSort.set).weakenFree introduced := by
    exact Term.renameMapped_id_weaken
      (target.weakenBound SetSort.set)
  have hIndex :
      (Term.bvar (.here) : SetTerm (SetSort.set :: bound) free).renameMapped
          VariableRenaming.id (VariableRenaming.weaken introduced) =
        (Term.bvar (.here) :
          SetTerm (SetSort.set :: bound) (introduced :: free)) := by
    exact Term.renameMapped_id_weaken
      (Term.bvar (.here) : SetTerm (SetSort.set :: bound) free)
  rw [Formula.weakenFree_eq_renameMapped]
  simp only [function_value_bound, Formula.LevyBound.boundedForall,
    set_levy_bound, Formula.LevyBound.membership, Formula.renameMapped,
    Arguments.renameMapped]
  simp [hGraph, hTarget, hIndex, domain_term,
    function_application_term]

theorem function_value_bound_delta0
    {bound free : SetContext}
    (graph target : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (function_value_bound graph target) := by
  exact Formula.IsDelta0.bounded_forall (domₘ(graph))
    (Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.membership
      𝒂ₘ(graph.weakenBound SetSort.set ·ₘ (.bvar .here),
        target.weakenBound SetSort.set))

/-- 函数性、定义域族成员与全称值界的组合条件。 -/
def bounded_function_total_condition {bound free : SetContext}
    (graph domainFamily target : SetTerm bound free) : SetFormula bound free :=
  (is_function_formula graph ∧ₘ
    (domₘ(graph) ∈ₘ domainFamily)) ∧ₘ
    function_value_bound graph target

theorem bounded_function_condition_delta0
    {bound free : SetContext}
    (graph domainFamily target index : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (bounded_function_condition graph domainFamily target index) := by
  exact Formula.IsDelta0.conj
    (Formula.IsDelta0.conj
      (function_formula_delta0 graph)
      (Formula.IsDelta0.rel (ℬ := set_levy_bound)
        RelationSymbol.membership
        𝒂ₘ(domₘ(graph), domainFamily)))
    (function_value_bound_condition_delta0 graph target index)

theorem bounded_function_total_condition_delta0
    {bound free : SetContext}
    (graph domainFamily target : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (bounded_function_total_condition graph domainFamily target) := by
  exact Formula.IsDelta0.conj
    (Formula.IsDelta0.conj
      (function_formula_delta0 graph)
      (Formula.IsDelta0.rel (ℬ := set_levy_bound)
        RelationSymbol.membership
        𝒂ₘ(domₘ(graph), domainFamily)))
    (function_value_bound_delta0 graph target)

theorem finite_sequence_condition_delta0
    {bound free : SetContext}
    (sequence : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (finite_sequence_condition sequence) := by
  exact Formula.IsDelta0.conj
    (function_formula_delta0 sequence)
    (Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.membership
      𝒂ₘ(domₘ(sequence), ωₘ))

theorem sequence_domain_code_bound_delta0
    {bound free : SetContext}
    (sequence code : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (sequence_domain_code_bound sequence code) := by
  exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
    RelationSymbol.membership
    𝒂ₘ(domₘ(sequence), Sₘ(code))

theorem nat_sequence_value_code_bound_delta0
    {bound free : SetContext}
    (sequence code : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (nat_sequence_value_code_bound sequence code) := by
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let codeOne : SetTerm (SetSort.set :: bound) free :=
    code.weakenBound SetSort.set
  have hBody :
      Formula.IsDelta0 set_levy_bound
        ((sequenceOne ·ₘ (.bvar .here)) ∈ₘ codeOne) :=
    Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.membership
      𝒂ₘ(sequenceOne ·ₘ (.bvar .here), codeOne)
  simpa [nat_sequence_value_code_bound, sequenceOne, codeOne,
    Formula.LevyBound.boundedForall] using
    (Formula.IsDelta0.bounded_forall
      (domₘ(sequence)) hBody)

theorem sequence_trace_code_bound_delta0
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

theorem nat_sequence_code_condition_delta0
    {bound free : SetContext}
    (sequence code : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (nat_sequence_code_condition sequence code) := by
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let codeOne : SetTerm (SetSort.set :: bound) free :=
    code.weakenBound SetSort.set
  let trace : SetTerm (SetSort.set :: bound) free := .bvar .here
  let sequenceTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    (sequence.weakenBound SetSort.set).weakenBound SetSort.set
  let traceTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    .bvar (.there .here)
  let index : SetTerm (SetSort.set :: SetSort.set :: bound) free := .bvar .here
  let stepBody : SetFormula (SetSort.set :: SetSort.set :: bound) free :=
    nat_sequence_code_step_condition sequenceTwo traceTwo index
  have hStepBody :
      Formula.IsDelta0 set_levy_bound stepBody := by
    exact Formula.IsDelta0.equal
      (traceTwo ·ₘ Sₘ(index))
      (Sₘ(godel_pairₘ(
        traceTwo ·ₘ index, sequenceTwo ·ₘ index)))
  let stepCondition : SetFormula (SetSort.set :: bound) free :=
    Formula.LevyBound.boundedForall set_levy_bound
      (domₘ(sequenceOne)) stepBody
  have hStepCondition :
      Formula.IsDelta0 set_levy_bound stepCondition := by
    exact Formula.IsDelta0.bounded_forall
      (domₘ(sequenceOne)) hStepBody
  have hTraceBound := sequence_trace_code_bound_delta0 trace codeOne
  let traceDomain : SetFormula (SetSort.set :: bound) free :=
    domₘ(trace) ≐ₘ Sₘ(domₘ(sequenceOne))
  let traceZero : SetFormula (SetSort.set :: bound) free :=
    (trace ·ₘ numₘ(0)) ≐ₘ numₘ(0)
  let traceCode : SetFormula (SetSort.set :: bound) free :=
    codeOne ≐ₘ (trace ·ₘ domₘ(sequenceOne))
  let traceBody : SetFormula (SetSort.set :: bound) free :=
    (trace ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
      ((traceDomain ∧ₘ sequence_trace_code_bound trace codeOne) ∧ₘ
        (traceZero ∧ₘ (stepCondition ∧ₘ traceCode)))
  have hTraceDomain :
      Formula.IsDelta0 set_levy_bound traceDomain := by
    exact Formula.IsDelta0.equal
      (domₘ(trace)) (Sₘ(domₘ(sequenceOne)))
  have hTraceZero :
      Formula.IsDelta0 set_levy_bound traceZero := by
    exact Formula.IsDelta0.equal
      (trace ·ₘ numₘ(0)) (numₘ(0))
  have hTraceCode :
      Formula.IsDelta0 set_levy_bound traceCode := by
    exact Formula.IsDelta0.equal
      codeOne (trace ·ₘ domₘ(sequenceOne))
  have hTraceBody :
      Formula.IsDelta0 set_levy_bound
        traceBody := by
    simpa [traceBody, traceDomain, traceZero, traceCode] using
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.rel (ℬ := set_levy_bound)
          RelationSymbol.membership
          𝒂ₘ(trace, seq_spaceₘ(ωₘ)))
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.conj hTraceDomain hTraceBound)
          (Formula.IsDelta0.conj hTraceZero
            (Formula.IsDelta0.conj hStepCondition hTraceCode))))
  have hTraceGuard :
      Formula.MembershipGuard set_levy_bound
        (seq_spaceₘ(ωₘ)) traceBody := by
    exact Formula.MembershipGuard.conj_left
      Formula.MembershipGuard.membership
  have hTrace :
      Formula.IsDelta0 set_levy_bound
        (.existsE SetSort.set traceBody) :=
    Formula.IsDelta0.guarded_exists
      (seq_spaceₘ(ωₘ)) hTraceBody hTraceGuard
  have hPrefix :
      Formula.IsDelta0 set_levy_bound
        (((sequence ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
          (code ∈ₘ ωₘ)) ∧ₘ
          sequence_domain_code_bound sequence code) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.rel (ℬ := set_levy_bound)
          RelationSymbol.membership
          𝒂ₘ(sequence, seq_spaceₘ(ωₘ)))
        (Formula.IsDelta0.rel (ℬ := set_levy_bound)
          RelationSymbol.membership
          𝒂ₘ(code, ωₘ)))
      (sequence_domain_code_bound_delta0 sequence code)
  simpa [nat_sequence_code_condition, sequenceOne, codeOne, trace,
    sequenceTwo, traceTwo, index, stepBody, stepCondition,
    traceDomain, traceZero, traceCode, traceBody,
    Formula.LevyBound.boundedForall] using!
      Formula.IsDelta0.conj
        (Formula.IsDelta0.conj hPrefix
          (nat_sequence_value_code_bound_delta0 sequence code))
      hTrace

theorem proof_sequence_code_step_condition_delta0
    {bound free : SetContext}
    (sequence trace index rowCode : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (proof_sequence_code_step_condition
        sequence trace index rowCode) := by
  exact Formula.IsDelta0.conj
    (nat_sequence_code_condition_delta0
      (sequence ·ₘ index) rowCode)
    (Formula.IsDelta0.equal
      (trace ·ₘ Sₘ(index))
      (Sₘ(godel_pairₘ(trace ·ₘ index, rowCode))))

theorem proof_sequence_code_condition_delta0
    {bound free : SetContext}
    (sequence code : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (proof_sequence_code_condition sequence code) := by
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let codeOne : SetTerm (SetSort.set :: bound) free :=
    code.weakenBound SetSort.set
  let trace : SetTerm (SetSort.set :: bound) free := .bvar .here
  let sequenceTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    sequenceOne.weakenBound SetSort.set
  let codeTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    codeOne.weakenBound SetSort.set
  let sequenceThree : SetTerm
      (SetSort.set :: SetSort.set :: SetSort.set :: bound) free :=
    sequenceTwo.weakenBound SetSort.set
  let traceThree : SetTerm
      (SetSort.set :: SetSort.set :: SetSort.set :: bound) free :=
    .bvar (.there (.there .here))
  let indexThree : SetTerm
      (SetSort.set :: SetSort.set :: SetSort.set :: bound) free :=
    .bvar (.there .here)
  let rowCode : SetTerm
      (SetSort.set :: SetSort.set :: SetSort.set :: bound) free := .bvar .here
  let rowBody : SetFormula
      (SetSort.set :: SetSort.set :: SetSort.set :: bound) free :=
    proof_sequence_code_step_condition
      sequenceThree traceThree indexThree rowCode
  have hRowBody :
      Formula.IsDelta0 set_levy_bound rowBody :=
    proof_sequence_code_step_condition_delta0
      sequenceThree traceThree indexThree rowCode
  let rowWitness : SetFormula (SetSort.set :: SetSort.set :: bound) free :=
    Formula.LevyBound.boundedExists ProofT.set_levy_bound
      codeTwo rowBody
  have hRowWitness :
      Formula.IsDelta0 set_levy_bound rowWitness := by
    exact Formula.IsDelta0.bounded_exists codeTwo hRowBody
  let pointwise : SetFormula (SetSort.set :: bound) free :=
    Formula.LevyBound.boundedForall ProofT.set_levy_bound
      (domₘ(sequenceOne)) rowWitness
  have hPointwise :
      Formula.IsDelta0 set_levy_bound pointwise := by
    exact Formula.IsDelta0.bounded_forall
      (domₘ(sequenceOne)) hRowWitness
  let traceDomain : SetFormula (SetSort.set :: bound) free :=
    domₘ(trace) ≐ₘ Sₘ(domₘ(sequenceOne))
  let traceZero : SetFormula (SetSort.set :: bound) free :=
    (trace ·ₘ numₘ(0)) ≐ₘ numₘ(0)
  let traceCode : SetFormula (SetSort.set :: bound) free :=
    codeOne ≐ₘ (trace ·ₘ domₘ(sequenceOne))
  let traceBody : SetFormula (SetSort.set :: bound) free :=
    (traceDomain ∧ₘ sequence_trace_code_bound trace codeOne) ∧ₘ
      (traceZero ∧ₘ (pointwise ∧ₘ traceCode))
  have hTraceBound := sequence_trace_code_bound_delta0 trace codeOne
  have hTraceBody :
      Formula.IsDelta0 set_levy_bound traceBody := by
    have hTraceDomain :
        Formula.IsDelta0 set_levy_bound traceDomain := by
      exact Formula.IsDelta0.equal
        (domₘ(trace)) (Sₘ(domₘ(sequenceOne)))
    have hTraceZero :
        Formula.IsDelta0 set_levy_bound traceZero := by
      exact Formula.IsDelta0.equal
        (trace ·ₘ numₘ(0)) (numₘ(0))
    have hTraceCode :
        Formula.IsDelta0 set_levy_bound traceCode := by
      exact Formula.IsDelta0.equal
        codeOne (trace ·ₘ domₘ(sequenceOne))
    simpa [traceBody, traceDomain, traceZero, traceCode] using
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj hTraceDomain hTraceBound)
        (Formula.IsDelta0.conj hTraceZero
          (Formula.IsDelta0.conj hPointwise hTraceCode)))
  let traceCondition : SetFormula bound free :=
    Formula.LevyBound.boundedExists ProofT.set_levy_bound
      (seq_spaceₘ(ωₘ)) traceBody
  have hTraceCondition :
      Formula.IsDelta0 set_levy_bound traceCondition := by
    exact Formula.IsDelta0.bounded_exists
      (seq_spaceₘ(ωₘ)) hTraceBody
  have hPrefix :
      Formula.IsDelta0 set_levy_bound
        (((sequence ∈ₘ seq_spaceₘ(syntax_formula_code_set_term)) ∧ₘ
          (code ∈ₘ ωₘ)) ∧ₘ
          sequence_domain_code_bound sequence code) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.rel (ℬ := set_levy_bound)
          RelationSymbol.membership
          𝒂ₘ(sequence, seq_spaceₘ(syntax_formula_code_set_term)))
        (Formula.IsDelta0.rel (ℬ := set_levy_bound)
          RelationSymbol.membership
          𝒂ₘ(code, ωₘ)))
      (sequence_domain_code_bound_delta0 sequence code)
  simpa [proof_sequence_code_condition, sequenceOne, codeOne, trace,
    sequenceTwo, codeTwo, sequenceThree, traceThree, indexThree, rowCode,
    rowBody, rowWitness, pointwise, traceDomain, traceZero, traceCode,
    traceBody, traceCondition, Formula.LevyBound.boundedExists,
    Formula.LevyBound.boundedForall] using!
    Formula.IsDelta0.conj hPrefix hTraceCondition

theorem proof_sequence_terminal_condition_delta0
    {bound free : SetContext}
    (sequence conclusion : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (proof_sequence_terminal_condition sequence conclusion) := by
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let conclusionOne : SetTerm (SetSort.set :: bound) free :=
    conclusion.weakenBound SetSort.set
  let lastBody : SetFormula (SetSort.set :: bound) free :=
    (domₘ(sequenceOne) ≐ₘ Sₘ(.bvar .here)) ∧ₘ
      (conclusionOne ≐ₘ (sequenceOne ·ₘ .bvar .here))
  have hLastBody :
      Formula.IsDelta0 set_levy_bound lastBody := by
    exact Formula.IsDelta0.conj
      (Formula.IsDelta0.equal
        (domₘ(sequenceOne)) (Sₘ(.bvar .here)))
      (Formula.IsDelta0.equal
        conclusionOne (sequenceOne ·ₘ .bvar .here))
  simpa [proof_sequence_terminal_condition, sequenceOne, conclusionOne,
    lastBody, Formula.LevyBound.boundedExists] using
    (Formula.IsDelta0.bounded_exists
      (domₘ(sequence)) hLastBody)

/-! ## 结构化证书条件的层级分类 -/

/-- 带有显式 `Delta0` 合同的内在 checked verifier。 -/
structure Delta0CheckedVerifier
    extends StructuredCertificateCondition.CheckedVerifier where
  formula_condition_delta0 :
    Formula.IsDelta0 set_levy_bound
      (toCheckedVerifier.formula_condition.body)
  condition_delta0 :
    Formula.IsDelta0 set_levy_bound
      (toCheckedVerifier.condition.body)
  logical_condition_delta0 :
    Formula.IsDelta0 set_levy_bound
      (toCheckedVerifier.logical_condition.body)

theorem certificate_payload_bound_delta0
    {bound free : SetContext}
    (certificates index payload : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (certificate_payload_bound certificates index payload) := by
  exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
    RelationSymbol.membership
    𝒂ₘ(payload, Sₘ(certificates ·ₘ index))

theorem proof_code_component_bound_delta0
    {bound free : SetContext}
    (proofCode component : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (proof_code_component_bound proofCode component) := by
  exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
    RelationSymbol.membership
    𝒂ₘ(component, Sₘ(proofCode))

theorem modus_ponens_line_condition_delta0
    {bound free : SetContext}
    (sequence certificates index : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (modus_ponens_line_condition sequence certificates index) := by
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let certificatesOne : SetTerm (SetSort.set :: bound) free :=
    certificates.weakenBound SetSort.set
  let indexOne : SetTerm (SetSort.set :: bound) free :=
    index.weakenBound SetSort.set
  let sequenceTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    sequenceOne.weakenBound SetSort.set
  let certificatesTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    certificatesOne.weakenBound SetSort.set
  let indexTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    indexOne.weakenBound SetSort.set
  let implicationIndexOne : SetTerm (SetSort.set :: bound) free :=
    .bvar .here
  let implicationIndex : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    .bvar (.there .here)
  let premiseIndex : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    .bvar .here
  let innerBody : SetFormula (SetSort.set :: SetSort.set :: bound) free :=
    ((certificatesTwo ·ₘ indexTwo) ≐ₘ
        modus_ponens_certificate_code implicationIndex premiseIndex) ∧ₘ
      modus_ponensₘ(
        sequenceTwo ·ₘ premiseIndex,
        sequenceTwo ·ₘ implicationIndex,
        sequenceTwo ·ₘ indexTwo)
  have hInnerBody : Formula.IsDelta0 set_levy_bound innerBody := by
    exact Formula.IsDelta0.conj
      (Formula.IsDelta0.equal
        (certificatesTwo ·ₘ indexTwo)
        (modus_ponens_certificate_code implicationIndex premiseIndex))
      (Formula.IsDelta0.rel
        (ℬ := set_levy_bound)
        RelationSymbol.modusPonens
        𝒂ₘ(sequenceTwo ·ₘ premiseIndex,
          sequenceTwo ·ₘ implicationIndex,
          sequenceTwo ·ₘ indexTwo))
  have hInner :
      Formula.IsDelta0 set_levy_bound
        (Formula.LevyBound.boundedExists set_levy_bound
          implicationIndexOne innerBody) :=
    Formula.IsDelta0.bounded_exists implicationIndexOne hInnerBody
  simpa [modus_ponens_line_condition, sequenceOne, certificatesOne,
    indexOne, sequenceTwo, certificatesTwo, indexTwo,
    implicationIndexOne, implicationIndex, premiseIndex, innerBody,
    Formula.LevyBound.boundedExists] using
    (Formula.IsDelta0.bounded_exists index hInner)

theorem theory_certificate_line_condition_delta0
    (verifier : Delta0CheckedVerifier)
    {bound free : SetContext}
    (sequence certificates index : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (theory_certificate_line_condition
        verifier.toCheckedVerifier.as_object sequence certificates index) := by
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let certificatesOne : SetTerm (SetSort.set :: bound) free :=
    certificates.weakenBound SetSort.set
  let indexOne : SetTerm (SetSort.set :: bound) free :=
    index.weakenBound SetSort.set
  let certificateCode : SetTerm (SetSort.set :: bound) free :=
    .bvar .here
  let body : SetFormula (SetSort.set :: bound) free :=
    (certificatesOne ·ₘ indexOne ≐ₘ
        theory_certificate_code certificateCode) ∧ₘ
      verifier.toCheckedVerifier.as_object.condition
        (sequenceOne ·ₘ indexOne) certificateCode
  have hBody : Formula.IsDelta0 set_levy_bound body := by
    exact Formula.IsDelta0.conj
      (Formula.IsDelta0.equal
        (certificatesOne ·ₘ indexOne)
        (theory_certificate_code certificateCode))
      (FormulaTemplate.instantiate_delta0
        verifier.toCheckedVerifier.as_object.condition
        verifier.condition_delta0
        (VariableSubstitution.cons
          (sequenceOne ·ₘ indexOne)
          (VariableSubstitution.cons certificateCode
            VariableSubstitution.empty)))
  simpa [theory_certificate_line_condition, sequenceOne, certificatesOne,
    indexOne, certificateCode, body,
    Formula.LevyBound.boundedExists] using
    (Formula.IsDelta0.bounded_exists
      (Sₘ(certificates ·ₘ index)) hBody)

theorem forall_generalization_line_condition_delta0
    {bound free : SetContext}
    (sequence certificates index : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (forall_generalization_line_condition
        sequence certificates index) := by
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let certificatesOne : SetTerm (SetSort.set :: bound) free :=
    certificates.weakenBound SetSort.set
  let indexOne : SetTerm (SetSort.set :: bound) free :=
    index.weakenBound SetSort.set
  let sequenceTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    sequenceOne.weakenBound SetSort.set
  let certificatesTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    certificatesOne.weakenBound SetSort.set
  let indexTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    indexOne.weakenBound SetSort.set
  let premiseIndex : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    .bvar (.there .here)
  let bodyCode : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    .bvar .here
  let innerBody : SetFormula (SetSort.set :: SetSort.set :: bound) free :=
    ((certificatesTwo ·ₘ indexTwo) ≐ₘ
        forall_generalization_certificate_code premiseIndex bodyCode) ∧ₘ
      ((formula_code_atₘ(numₘ(1), bodyCode) ∧ₘ
        formula_abstract_free_top_condition
          (sequenceTwo ·ₘ premiseIndex) bodyCode) ∧ₘ
        ((sequenceTwo ·ₘ indexTwo) ≐ₘ all_codeₘ(bodyCode)))
  have hInnerBody : Formula.IsDelta0 set_levy_bound innerBody := by
    exact Formula.IsDelta0.conj
      (Formula.IsDelta0.equal
        (certificatesTwo ·ₘ indexTwo)
        (forall_generalization_certificate_code premiseIndex bodyCode))
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.rel (ℬ := set_levy_bound)
            RelationSymbol.isFormulaCodeAt
            𝒂ₘ(numₘ(1), bodyCode))
          (Formula.IsDelta0.rel (ℬ := set_levy_bound)
            RelationSymbol.syntaxTransform
            𝒂ₘ(
              syntax_code_kind_term .formula,
              syntax_transform_operation_term .abstractFreeTop,
              numₘ(0), numₘ(0), numₘ(0),
              sequenceTwo ·ₘ premiseIndex, bodyCode)))
        (Formula.IsDelta0.equal
          (sequenceTwo ·ₘ indexTwo) (all_codeₘ(bodyCode))))
  have hBodyWitness : Formula.IsDelta0 set_levy_bound
      (Formula.LevyBound.boundedExists set_levy_bound
        (ωₘ : SetTerm (SetSort.set :: bound) free) innerBody) :=
    Formula.IsDelta0.bounded_exists
      (ωₘ : SetTerm (SetSort.set :: bound) free) hInnerBody
  simpa [forall_generalization_line_condition, sequenceOne,
    certificatesOne, indexOne, sequenceTwo,
    certificatesTwo, indexTwo, premiseIndex, bodyCode, innerBody,
    Formula.LevyBound.boundedExists] using
    (Formula.IsDelta0.bounded_exists index hBodyWitness)

theorem line_condition_with_logical_delta0
    (verifier : Delta0CheckedVerifier)
    {bound free : SetContext}
    (sequence certificates index : SetTerm bound free)
    (logicalCondition : LogicalCondition)
    (hLogicalCondition :
      Formula.IsDelta0 set_levy_bound logicalCondition.body) :
    Formula.IsDelta0 set_levy_bound
      (line_condition_with_logical
        verifier.toCheckedVerifier.as_object
        sequence certificates index logicalCondition) := by
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let certificatesOne : SetTerm (SetSort.set :: bound) free :=
    certificates.weakenBound SetSort.set
  let indexOne : SetTerm (SetSort.set :: bound) free :=
    index.weakenBound SetSort.set
  let certificateCode : SetTerm (SetSort.set :: bound) free :=
    .bvar .here
  let logicalBody : SetFormula (SetSort.set :: bound) free :=
    (certificatesOne ·ₘ indexOne ≐ₘ
        logical_certificate_code certificateCode) ∧ₘ
      logicalCondition
        sequenceOne certificatesOne indexOne certificateCode
  have hLogicalBody : Formula.IsDelta0 set_levy_bound logicalBody := by
    exact Formula.IsDelta0.conj
      (Formula.IsDelta0.equal
        (certificatesOne ·ₘ indexOne)
        (logical_certificate_code certificateCode))
      (FormulaTemplate.instantiate_delta0
        logicalCondition hLogicalCondition
        (VariableSubstitution.cons sequenceOne
          (VariableSubstitution.cons certificatesOne
            (VariableSubstitution.cons indexOne
              (VariableSubstitution.cons certificateCode
                VariableSubstitution.empty)))))
  have hLogicalBranch :
      Formula.IsDelta0 set_levy_bound
        (Formula.LevyBound.boundedExists set_levy_bound
          (Sₘ(certificates ·ₘ index)) logicalBody) :=
    Formula.IsDelta0.bounded_exists
      (Sₘ(certificates ·ₘ index)) hLogicalBody
  have hTheoryBranch :=
    theory_certificate_line_condition_delta0 verifier
      sequence certificates index
  have hModusPonensBranch :=
    modus_ponens_line_condition_delta0 sequence certificates index
  have hForallGeneralizationBranch :=
    forall_generalization_line_condition_delta0 sequence certificates index
  simpa [line_condition_with_logical, sequenceOne, certificatesOne,
    indexOne, certificateCode, logicalBody,
    Formula.LevyBound.boundedExists] using
    Formula.IsDelta0.disj hLogicalBranch
      (Formula.IsDelta0.disj hTheoryBranch
        (Formula.IsDelta0.disj hModusPonensBranch
          hForallGeneralizationBranch))

theorem sequence_condition_delta0
    (verifier : Delta0CheckedVerifier)
    {bound free : SetContext}
    (sequence certificates : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (verifier.toCheckedVerifier.sequence_condition sequence certificates) := by
  let checked := verifier.toCheckedVerifier
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let certificatesOne : SetTerm (SetSort.set :: bound) free :=
    certificates.weakenBound SetSort.set
  let index : SetTerm (SetSort.set :: bound) free := .bvar .here
  let lineBody : SetFormula (SetSort.set :: bound) free :=
    checked.formula_condition (sequenceOne ·ₘ index) ∧ₘ
      line_condition_with_logical
        checked.as_object sequenceOne certificatesOne index
          checked.logical_condition
  have hLine :
      Formula.IsDelta0 set_levy_bound
        (line_condition_with_logical
          checked.as_object sequenceOne certificatesOne index
            checked.logical_condition) := by
    exact line_condition_with_logical_delta0 verifier
      sequenceOne certificatesOne index checked.logical_condition
      verifier.logical_condition_delta0
  have hLineBody : Formula.IsDelta0 set_levy_bound lineBody := by
    have hFormulaCondition :=
      FormulaTemplate.instantiate_delta0
        checked.formula_condition verifier.formula_condition_delta0
        (VariableSubstitution.cons
          (sequenceOne ·ₘ index) VariableSubstitution.empty)
    exact Formula.IsDelta0.conj
      hFormulaCondition hLine
  have hLineCondition :
      Formula.IsDelta0 set_levy_bound
        (Formula.LevyBound.boundedForall set_levy_bound
          (domₘ(sequence)) lineBody) :=
    Formula.IsDelta0.bounded_forall (domₘ(sequence)) hLineBody
  have hPrefix :
      Formula.IsDelta0 set_levy_bound
        ((((sequence ∈ₘ seq₊_spaceₘ(syntax_formula_code_set_term)) ∧ₘ
          (certificates ∈ₘ seq₊_spaceₘ(ωₘ))) ∧ₘ
          (domₘ(sequence) ≐ₘ domₘ(certificates))) ∧ₘ
          (numₘ(0) ∈ₘ domₘ(sequence))) := by
    exact Formula.IsDelta0.conj
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.rel (ℬ := set_levy_bound)
            RelationSymbol.membership
            𝒂ₘ(sequence, seq₊_spaceₘ(syntax_formula_code_set_term)))
          (Formula.IsDelta0.rel (ℬ := set_levy_bound)
            RelationSymbol.membership
            𝒂ₘ(certificates, seq₊_spaceₘ(ωₘ))))
        (Formula.IsDelta0.equal
          (domₘ(sequence)) (domₘ(certificates))))
      (Formula.IsDelta0.rel (ℬ := set_levy_bound)
        RelationSymbol.membership
        𝒂ₘ(numₘ(0), domₘ(sequence)))
  simpa [checked, StructuredCertificateCondition.CheckedVerifier.sequence_condition,
    StructuredCertificateCondition.sequence_condition, lineBody, sequenceOne,
    certificatesOne, index, Formula.LevyBound.boundedForall] using!
    Formula.IsDelta0.conj hPrefix hLineCondition

theorem code_condition_body_delta0
    (verifier : Delta0CheckedVerifier)
    {bound free : SetContext}
    (proofCode conclusion sequence certificates formulaCode certificateCode :
      SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (code_condition_body
        verifier.toCheckedVerifier.as_object
        proofCode conclusion sequence certificates formulaCode certificateCode
        verifier.toCheckedVerifier.logical_condition) := by
  have hSequence :
      Formula.IsDelta0 set_levy_bound
        (sequence_condition
          verifier.toCheckedVerifier.as_object
          sequence certificates verifier.toCheckedVerifier.logical_condition) := by
    simpa [StructuredCertificateCondition.CheckedVerifier.sequence_condition,
      StructuredCertificateCondition.sequence_condition] using
      sequence_condition_delta0 verifier sequence certificates
  have hProof := object_sequence_code_condition_delta0
    (syntax_formula_code_set_term : SetTerm bound free) sequence formulaCode
  have hCertificate := object_sequence_code_condition_delta0
    (ωₘ : SetTerm bound free) certificates certificateCode
  have hFormulaBound :=
    proof_code_component_bound_delta0 proofCode formulaCode
  have hCertificateBound :=
    proof_code_component_bound_delta0 proofCode certificateCode
  have hPair :
      Formula.IsDelta0 set_levy_bound
        (proofCode ≐ₘ godel_pairₘ(formulaCode, certificateCode)) :=
    Formula.IsDelta0.equal
      proofCode (godel_pairₘ(formulaCode, certificateCode))
  have hTerminal :=
    proof_sequence_terminal_condition_delta0 sequence conclusion
  simpa [code_condition_body] using
    Formula.IsDelta0.conj
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj hSequence hProof)
        hCertificate)
      (Formula.IsDelta0.conj
      (Formula.IsDelta0.conj hFormulaBound hCertificateBound)
        (Formula.IsDelta0.conj hPair hTerminal))

theorem code_condition_delta0
    (verifier : Delta0CheckedVerifier) :
    Formula.IsDelta0 set_levy_bound
      (code_condition
        verifier.toCheckedVerifier.as_object
        verifier.toCheckedVerifier.logical_condition).body := by
  let proofCode : SetOpenTerm [SetSort.set, SetSort.set] :=
    .fvar .here
  let conclusion : SetOpenTerm [SetSort.set, SetSort.set] :=
    .fvar (.there .here)
  let proofCodeOne : SetTerm [SetSort.set] [SetSort.set, SetSort.set] :=
    proofCode.weakenBound SetSort.set
  let conclusionOne : SetTerm [SetSort.set] [SetSort.set, SetSort.set] :=
    conclusion.weakenBound SetSort.set
  let proofCodeTwo : SetTerm [SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    proofCodeOne.weakenBound SetSort.set
  let conclusionTwo : SetTerm [SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    conclusionOne.weakenBound SetSort.set
  let proofCodeThree : SetTerm
      [SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    proofCodeTwo.weakenBound SetSort.set
  let conclusionThree : SetTerm
      [SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    conclusionTwo.weakenBound SetSort.set
  let proofCodeFour : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    proofCodeThree.weakenBound SetSort.set
  let conclusionFour : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    conclusionThree.weakenBound SetSort.set
  let sequence : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    .bvar (.there (.there (.there .here)))
  let certificates : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    .bvar (.there (.there .here))
  let formulaCode : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    .bvar (.there .here)
  let certificateCode : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    .bvar .here
  have hBody := code_condition_body_delta0 verifier
    proofCodeFour conclusionFour sequence certificates formulaCode certificateCode
  have hClosed := bounded_witness_closure_delta0
    (code_condition_plan proofCode) hBody
  simpa [code_condition, code_condition_plan, bounded_witness_closure,
    proofCode, conclusion,
    proofCodeOne, conclusionOne, proofCodeTwo, conclusionTwo,
    proofCodeThree, conclusionThree, proofCodeFour, conclusionFour,
    sequence, certificates, formulaCode, certificateCode,
    Formula.LevyBound.boundedExists] using! hClosed

namespace Delta0CheckedVerifier

/-- 结构化 checked verifier 直接生成 Rosser 可消费的 `Delta0` 证明图。 -/
def proof_graph
    (verifier : Delta0CheckedVerifier) : Delta0ProofGraph where
  condition := code_condition
    verifier.toCheckedVerifier.as_object
    verifier.toCheckedVerifier.logical_condition
  delta0 := by
    intro bound free proofCode conclusion
    exact FormulaTemplate.instantiate_delta0
      (code_condition
        verifier.toCheckedVerifier.as_object
        verifier.toCheckedVerifier.logical_condition)
      (code_condition_delta0 verifier)
      (VariableSubstitution.cons proofCode
        (VariableSubstitution.cons conclusion
          VariableSubstitution.empty))

end Delta0CheckedVerifier

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
