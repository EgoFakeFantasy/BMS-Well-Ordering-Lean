import YesMetaZFC.Logic.FirstOrder.FormalSystem.LanguageEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CodeDomain

/-!
# ProofT 的内在全称前缀条件

全称前缀只记录绑定层数、核心公式码和闭合公式码。轨迹方向从闭合公式码开始，
每一步剥离一个最外层全称构造，最终到达开放核心；因此不需要变量名、freshness
或旧式 token 轨迹。
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

/-! ## 轨迹局部条件 -/

def forall_prefix_formula_code_condition {bound free : SetContext}
    (depth formulaCode : SetTerm bound free) : SetFormula bound free :=
  (formulaCode ∈ₘ ωₘ ∧ₘ
      (formulaCode ∈ₘ syntax_formula_code_set_term)) ∧ₘ
    formula_code_atₘ(depth, formulaCode)

theorem forall_prefix_formula_code_condition_delta0
    {bound free : SetContext}
    (depth formulaCode : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (forall_prefix_formula_code_condition depth formulaCode) := by
  exact Formula.IsDelta0.conj
    (Formula.IsDelta0.conj
      (Formula.IsDelta0.rel (ℬ := set_levy_bound)
        RelationSymbol.membership
        𝒂ₘ(formulaCode, ωₘ))
      (Formula.IsDelta0.rel (ℬ := set_levy_bound)
        RelationSymbol.membership
        𝒂ₘ(formulaCode, syntax_formula_code_set_term)))
    (Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.isFormulaCodeAt
      𝒂ₘ(depth, formulaCode))

def forall_prefix_step_condition {bound free : SetContext}
    (trace index : SetTerm bound free) : SetFormula bound free :=
  (trace ·ₘ index) ≐ₘ all_codeₘ(trace ·ₘ Sₘ(index))

@[simp] theorem forall_prefix_formula_code_condition_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (depth formulaCode : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (forall_prefix_formula_code_condition depth formulaCode) =
      forall_prefix_formula_code_condition
        (depth.substituteMapped boundSubstitution freeSubstitution)
        (formulaCode.substituteMapped boundSubstitution freeSubstitution) := by
  simp [forall_prefix_formula_code_condition, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped]

@[simp] theorem forall_prefix_step_condition_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (trace index : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (forall_prefix_step_condition trace index) =
      forall_prefix_step_condition
        (trace.substituteMapped boundSubstitution freeSubstitution)
        (index.substituteMapped boundSubstitution freeSubstitution) := by
  simp [forall_prefix_step_condition, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped]

theorem forall_prefix_step_condition_delta0
    {bound free : SetContext}
    (trace index : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (forall_prefix_step_condition trace index) := by
  exact Formula.IsDelta0.equal
    (trace ·ₘ index)
    (all_codeₘ(trace ·ₘ Sₘ(index)))

def forall_prefix_trace_body {bound free : SetContext}
    (binderCount core code trace : SetTerm (SetSort.set :: bound) free) :
    SetFormula (SetSort.set :: bound) free :=
  let index : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    .bvar .here
  let traceTwo : SetTerm
      (SetSort.set :: SetSort.set :: bound) free :=
    trace.weakenBound SetSort.set
  let valueBody : SetFormula
      (SetSort.set :: SetSort.set :: bound) free :=
    forall_prefix_formula_code_condition
      index (traceTwo ·ₘ index)
  let stepBody : SetFormula
      (SetSort.set :: SetSort.set :: bound) free :=
    forall_prefix_step_condition traceTwo index
  let valueCondition : SetFormula
      (SetSort.set :: bound) free :=
    Formula.LevyBound.boundedForall set_levy_bound
      (domₘ(trace)) valueBody
  let stepCondition : SetFormula
      (SetSort.set :: bound) free :=
    Formula.LevyBound.boundedForall set_levy_bound
      binderCount stepBody
  (binderCount ∈ₘ ωₘ ∧ₘ
      (domₘ(trace) ≐ₘ Sₘ(binderCount))) ∧ₘ
    (((trace ·ₘ numₘ(0) ≐ₘ code) ∧ₘ
        (trace ·ₘ binderCount ≐ₘ core)) ∧ₘ
      (valueCondition ∧ₘ stepCondition))

theorem forall_prefix_trace_body_delta0
    {bound free : SetContext}
    (binderCount core code trace : SetTerm (SetSort.set :: bound) free) :
    Formula.IsDelta0 set_levy_bound
      (forall_prefix_trace_body binderCount core code trace) := by
  let index : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    .bvar .here
  let traceTwo : SetTerm
      (SetSort.set :: SetSort.set :: bound) free :=
    trace.weakenBound SetSort.set
  let valueBody : SetFormula
      (SetSort.set :: SetSort.set :: bound) free :=
    forall_prefix_formula_code_condition
      index (traceTwo ·ₘ index)
  let stepBody : SetFormula
      (SetSort.set :: SetSort.set :: bound) free :=
    forall_prefix_step_condition traceTwo index
  let valueCondition : SetFormula
      (SetSort.set :: bound) free :=
    Formula.LevyBound.boundedForall set_levy_bound
      (domₘ(trace)) valueBody
  let stepCondition : SetFormula
      (SetSort.set :: bound) free :=
    Formula.LevyBound.boundedForall set_levy_bound
      binderCount stepBody
  have hValueBody : Formula.IsDelta0 set_levy_bound valueBody := by
    exact forall_prefix_formula_code_condition_delta0
      index (traceTwo ·ₘ index)
  have hStepBody : Formula.IsDelta0 set_levy_bound stepBody := by
    exact forall_prefix_step_condition_delta0 traceTwo index
  have hValue : Formula.IsDelta0 set_levy_bound valueCondition := by
    exact Formula.IsDelta0.bounded_forall (domₘ(trace)) hValueBody
  have hStep : Formula.IsDelta0 set_levy_bound stepCondition := by
    exact Formula.IsDelta0.bounded_forall binderCount hStepBody
  have hRight : Formula.IsDelta0 set_levy_bound
      (((trace ·ₘ numₘ(0) ≐ₘ code) ∧ₘ
          (trace ·ₘ binderCount ≐ₘ core)) ∧ₘ
        (valueCondition ∧ₘ stepCondition)) := by
    exact Formula.IsDelta0.conj
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.equal
          (trace ·ₘ numₘ(0)) code)
        (Formula.IsDelta0.equal
          (trace ·ₘ binderCount) core))
      (Formula.IsDelta0.conj hValue hStep)
  simpa [forall_prefix_trace_body, valueBody, stepBody,
    valueCondition, stepCondition] using
    Formula.IsDelta0.conj
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.rel (ℬ := set_levy_bound)
          RelationSymbol.membership
          𝒂ₘ(binderCount, ωₘ))
        (Formula.IsDelta0.equal
          (domₘ(trace)) (Sₘ(binderCount))))
      hRight

def forall_prefix_code_condition {bound free : SetContext}
    (binderCount core code : SetTerm bound free) : SetFormula bound free :=
  let binderCountOne := binderCount.weakenBound SetSort.set
  let coreOne := core.weakenBound SetSort.set
  let codeOne := code.weakenBound SetSort.set
  let trace : SetTerm (SetSort.set :: bound) free := .bvar .here
  let body := forall_prefix_trace_body
    binderCountOne coreOne codeOne trace
  Formula.LevyBound.boundedExists set_levy_bound
    (seq_spaceₘ(ωₘ)) body

@[simp] theorem forall_prefix_trace_body_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (binderCount core code trace :
      SetTerm (SetSort.set :: sourceBound) sourceFree)
    (boundSubstitution :
      VariableSubstitution signature
        (SetSort.set :: sourceBound) (SetSort.set :: targetBound) targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree
        (SetSort.set :: targetBound) targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (forall_prefix_trace_body binderCount core code trace) =
      forall_prefix_trace_body
        (binderCount.substituteMapped boundSubstitution freeSubstitution)
        (core.substituteMapped boundSubstitution freeSubstitution)
        (code.substituteMapped boundSubstitution freeSubstitution)
        (trace.substituteMapped boundSubstitution freeSubstitution) := by
  simp [forall_prefix_trace_body, forall_prefix_formula_code_condition,
    forall_prefix_step_condition, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftBound,
    Term.substituteMapped_weakenBound]

@[simp] theorem forall_prefix_code_condition_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (binderCount core code : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (forall_prefix_code_condition binderCount core code) =
      forall_prefix_code_condition
        (binderCount.substituteMapped boundSubstitution freeSubstitution)
        (core.substituteMapped boundSubstitution freeSubstitution)
        (code.substituteMapped boundSubstitution freeSubstitution) := by
  simp [forall_prefix_code_condition, forall_prefix_trace_body,
    forall_prefix_formula_code_condition, forall_prefix_step_condition,
    Formula.LevyBound.boundedExists, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftBound,
    Term.substituteMapped_weakenBound]

theorem forall_prefix_code_condition_delta0
    {bound free : SetContext}
    (binderCount core code : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (forall_prefix_code_condition binderCount core code) := by
  let binderCountOne := binderCount.weakenBound SetSort.set
  let coreOne := core.weakenBound SetSort.set
  let codeOne := code.weakenBound SetSort.set
  let trace : SetTerm (SetSort.set :: bound) free := .bvar .here
  let body := forall_prefix_trace_body
    binderCountOne coreOne codeOne trace
  have hBody : Formula.IsDelta0 set_levy_bound body := by
    exact forall_prefix_trace_body_delta0
      binderCountOne coreOne codeOne trace
  simpa [forall_prefix_code_condition, binderCountOne, coreOne,
    codeOne, trace, body, Formula.LevyBound.boundedExists] using
    Formula.IsDelta0.bounded_exists
      (seq_spaceₘ(ωₘ)) hBody

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
