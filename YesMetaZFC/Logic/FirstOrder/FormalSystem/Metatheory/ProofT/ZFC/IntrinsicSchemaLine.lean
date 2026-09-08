import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicFirstOrderLogicalLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicSchemaCertificate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicTheoryLine

/-!
# ZFC schema 的内在行装配

Replacement 的七层见证沿类型化 bound 上下文一次性闭合。调用方只提供各个 Quine
载体成员、结构变换关系和最终前缀关系，不再暴露旧 token、变量名或 freshness 参数。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFC
namespace IntrinsicSchemaLine

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open StructuredCertificateCondition
open IntrinsicLogicalCertificate
open IntrinsicSchemaCertificate
open IntrinsicFirstOrderLogicalLine
open IntrinsicTheoryLine

set_option autoImplicit false
set_option maxRecDepth 10000

theorem replacement_branch_intro
    {T : SetTheory}
    {Γ : Context signature schema_free}
    (formula certificate parameter bodyCode firstOutputCode secondOutputCode
      underOneCode underTwoCode imageCode : SetOpenTerm schema_free)
    (hParameter : Γ ⊢ₘ[T] parameter ∈ₘ ωₘ)
    (hBodyCarrier : Γ ⊢ₘ[T]
      bodyCode ∈ₘ syntax_formula_code_set_term)
    (hFirstOutputCarrier : Γ ⊢ₘ[T]
      firstOutputCode ∈ₘ syntax_formula_code_set_term)
    (hSecondOutputCarrier : Γ ⊢ₘ[T]
      secondOutputCode ∈ₘ syntax_formula_code_set_term)
    (hUnderOneCarrier : Γ ⊢ₘ[T]
      underOneCode ∈ₘ syntax_formula_code_set_term)
    (hUnderTwoCarrier : Γ ⊢ₘ[T]
      underTwoCode ∈ₘ syntax_formula_code_set_term)
    (hImageCarrier : Γ ⊢ₘ[T]
      imageCode ∈ₘ syntax_formula_code_set_term)
    (hCertificate : Γ ⊢ₘ[T]
      certificate ≐ₘ schema_certificate_payload 2 parameter bodyCode)
    (hBody : Γ ⊢ₘ[T]
      formula_code_condition (Sₘ(Sₘ(parameter))) bodyCode)
    (hFirstOutput : Γ ⊢ₘ[T]
      formula_weaken_bound_condition
        (Sₘ(Sₘ(parameter))) numₘ(0) bodyCode firstOutputCode)
    (hSecondOutput : Γ ⊢ₘ[T]
      formula_weaken_bound_condition
        (Sₘ(Sₘ(parameter))) numₘ(1) bodyCode secondOutputCode)
    (hUnderOne : Γ ⊢ₘ[T]
      formula_weaken_bound_condition
        (Sₘ(Sₘ(parameter))) numₘ(2) bodyCode underOneCode)
    (hUnderTwo : Γ ⊢ₘ[T]
      formula_weaken_bound_condition
        (Sₘ(Sₘ(Sₘ(parameter)))) numₘ(2) underOneCode underTwoCode)
    (hImage : Γ ⊢ₘ[T]
      formula_swap_bound_condition
        (Sₘ(Sₘ(Sₘ(Sₘ(parameter))))) numₘ(0) underTwoCode imageCode)
    (hCore : Γ ⊢ₘ[T]
      formula_code_condition parameter
        (replacement_core_code firstOutputCode secondOutputCode imageCode))
    (hFormula : Γ ⊢ₘ[T]
      formula_code_condition numₘ(0) formula)
    (hPrefix : Γ ⊢ₘ[T]
      forall_prefix_code_condition parameter
        (replacement_core_code firstOutputCode secondOutputCode imageCode)
        formula) :
    Γ ⊢ₘ[T]
      replacement_branch.condition_closed
        formula certificate := by
  change Γ ⊢ₘ[T]
    bounded_witness_closure replacement_plan
      (replacement_condition
        (weaken_bound_context replacement_bound formula)
        (weaken_bound_context replacement_bound certificate))
  let assignment :
      BoundedWitnessAssignment T Γ
        replacement_plan
        (VariableSubstitution.empty :
          VariableSubstitution signature [] [] schema_free) := by
    refine ⟨⟨parameter, ?_⟩, ?_⟩
    · simpa [replacement_plan, BoundedWitnessAssignment] using hParameter
    refine ⟨⟨bodyCode, ?_⟩, ?_⟩
    · simpa [replacement_plan, BoundedWitnessAssignment] using hBodyCarrier
    refine ⟨⟨firstOutputCode, ?_⟩, ?_⟩
    · simpa [replacement_plan, BoundedWitnessAssignment] using hFirstOutputCarrier
    refine ⟨⟨secondOutputCode, ?_⟩, ?_⟩
    · simpa [replacement_plan, BoundedWitnessAssignment] using hSecondOutputCarrier
    refine ⟨⟨underOneCode, ?_⟩, ?_⟩
    · simpa [replacement_plan, BoundedWitnessAssignment] using hUnderOneCarrier
    refine ⟨⟨underTwoCode, ?_⟩, ?_⟩
    · simpa [replacement_plan, BoundedWitnessAssignment] using hUnderTwoCarrier
    refine ⟨⟨imageCode, ?_⟩, PUnit.unit⟩
    simpa [replacement_plan, BoundedWitnessAssignment] using hImageCarrier
  have hMatrix : Γ ⊢ₘ[T]
      (replacement_condition
        (weaken_bound_context replacement_bound formula)
        (weaken_bound_context replacement_bound certificate)).substituteMapped
          assignment.finalSubstitution VariableSubstitution.freeId := by
    have hCorePair := FirstOrder.Derives.conj_intro hCore hFormula
    have hImageRest := FirstOrder.Derives.conj_intro hImage
      (FirstOrder.Derives.conj_intro hCorePair hPrefix)
    have hUnderRest := FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hUnderOne hUnderTwo) hImageRest
    have hShiftRest := FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hFirstOutput hSecondOutput) hUnderRest
    have hBodyRest := FirstOrder.Derives.conj_intro hParameter hBody
    have hRaw := FirstOrder.Derives.conj_intro hCertificate
      (FirstOrder.Derives.conj_intro hBodyRest hShiftRest)
    change Γ ⊢ₘ[T]
      Formula.substituteMapped assignment.finalSubstitution
          VariableSubstitution.freeId
        (replacement_condition_at
          (weaken_bound_context replacement_bound formula)
          (weaken_bound_context replacement_bound certificate)
          replacement_parameter replacement_body replacement_first_output
          replacement_second_output replacement_under_one replacement_under_two
          replacement_image)
    rw [replacement_condition_at_substituteMapped]
    simpa [assignment, BoundedWitnessAssignment,
      BoundedWitnessAssignment.finalSubstitution,
      replacement_parameter, replacement_body,
      replacement_first_output, replacement_second_output,
      replacement_under_one, replacement_under_two, replacement_image,
      replacement_condition_at, replacement_plan,
      weaken_bound_context_substituteMapped,
      Term.embedBoundClosed, Arguments.embedBoundClosed,
      Formula.substituteMapped, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.cons,
      VariableSubstitution.empty, VariableSubstitution.freeId,
      VariableSubstitution.liftBound, VariableSubstitution.weakenBound,
      Term.substituteMapped_weakenBound,
      Arguments.substituteMapped_weakenBound] using! hRaw
  have hClosed :=
    bounded_witness_closure_intro_assignment assignment _ hMatrix
  simpa only [Formula.substituteMapped_empty_freeId_eq_self] using hClosed

private theorem separation_branch_condition_substituteMapped
    (formula certificate : SetOpenTerm schema_free) :
    Formula.substituteMapped
        (VariableSubstitution.empty :
          VariableSubstitution signature [] [] schema_free)
        (VariableSubstitution.cons formula
          (VariableSubstitution.cons certificate
            VariableSubstitution.empty))
        (separation_branch.condition_closed
          (IntrinsicCertificateTable.formula_slot : SetOpenTerm schema_free)
          (IntrinsicCertificateTable.certificate_slot : SetOpenTerm schema_free)) =
      separation_branch.condition_closed formula certificate := by
  let slots : VariableSubstitution signature schema_free [] schema_free :=
    VariableSubstitution.cons formula
      (VariableSubstitution.cons certificate VariableSubstitution.empty)
  have hTransport :=
    bounded_witness_closure_substituteMapped
      (plan := schema_plan)
      (body := separation_condition
        (weaken_bound_context schema_bound
          (IntrinsicCertificateTable.formula_slot : SetOpenTerm schema_free))
        (weaken_bound_context schema_bound
          (IntrinsicCertificateTable.certificate_slot : SetOpenTerm schema_free)))
      (boundSubstitution :=
        (VariableSubstitution.empty :
          VariableSubstitution signature [] [] schema_free))
      (freeSubstitution := slots)
  have hPlan :
      (BoundedWitnessPlan.transport schema_plan
        (VariableSubstitution.empty :
          VariableSubstitution signature [] [] schema_free) slots).plan =
        schema_plan := by
    rfl
  simp only [hPlan] at hTransport
  simpa [slots, BoundedBinaryBranch.condition_closed,
    separation_branch, separation_condition,
    schema_parameter, schema_body, schema_shift_one, schema_shift_two,
    schema_plan, weaken_bound_context_substituteMapped,
    separation_condition_at_substituteMapped,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons,
    VariableSubstitution.empty, VariableSubstitution.liftBound,
    VariableSubstitution.weakenBound, VariableSubstitution.freeId,
    Term.substituteMapped_weakenBound,
    Arguments.substituteMapped_weakenBound] using! hTransport

private theorem replacement_branch_condition_substituteMapped
    (formula certificate : SetOpenTerm schema_free) :
    Formula.substituteMapped
        (VariableSubstitution.empty :
          VariableSubstitution signature [] [] schema_free)
        (VariableSubstitution.cons formula
          (VariableSubstitution.cons certificate
            VariableSubstitution.empty))
        (replacement_branch.condition_closed
          (IntrinsicCertificateTable.formula_slot : SetOpenTerm schema_free)
          (IntrinsicCertificateTable.certificate_slot : SetOpenTerm schema_free)) =
      replacement_branch.condition_closed formula certificate := by
  let slots : VariableSubstitution signature schema_free [] schema_free :=
    VariableSubstitution.cons formula
      (VariableSubstitution.cons certificate VariableSubstitution.empty)
  have hTransport :=
    bounded_witness_closure_substituteMapped
      (plan := replacement_plan)
      (body := replacement_condition
        (weaken_bound_context replacement_bound
          (IntrinsicCertificateTable.formula_slot : SetOpenTerm schema_free))
        (weaken_bound_context replacement_bound
          (IntrinsicCertificateTable.certificate_slot : SetOpenTerm schema_free)))
      (boundSubstitution :=
        (VariableSubstitution.empty :
          VariableSubstitution signature [] [] schema_free))
      (freeSubstitution := slots)
  have hPlan :
      (BoundedWitnessPlan.transport replacement_plan
        (VariableSubstitution.empty :
          VariableSubstitution signature [] [] schema_free) slots).plan =
        replacement_plan := by
    rfl
  simp only [hPlan] at hTransport
  simpa [slots, BoundedBinaryBranch.condition_closed,
    replacement_branch, replacement_plan, replacement_bound,
    replacement_condition, replacement_parameter, replacement_body,
    replacement_first_output, replacement_second_output,
    replacement_under_one, replacement_under_two, replacement_image,
    replacement_first_output_condition,
    replacement_second_output_condition,
    replacement_under_one_condition, replacement_under_two_condition,
    replacement_image_condition, replacement_core_code,
    schema_conjunction_code, schema_iff_code, schema_exists_code,
    schema_certificate_payload_substituteMapped,
    formula_code_condition, formula_weaken_bound_condition,
    formula_swap_bound_condition, forall_prefix_code_condition,
    forall_prefix_trace_body, forall_prefix_formula_code_condition,
    forall_prefix_step_condition, weaken_bound_context,
    Formula.LevyBound.boundedExists, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftBound, VariableSubstitution.weakenBound,
    VariableSubstitution.freeId, Term.substituteMapped_weakenBound,
    Arguments.substituteMapped_weakenBound] using! hTransport

theorem replacement_line_intro
    {T : SetTheory}
    {Γ : Context signature schema_free}
    (sequence certificates certificate parameter bodyCode
      firstOutputCode secondOutputCode underOneCode underTwoCode imageCode :
      SetOpenTerm schema_free)
    (index : Nat)
    (hPayloadBound : Γ ⊢ₘ[T]
      certificate_payload_bound certificates (numₘ(index)) certificate)
    (hCertificateCode : Γ ⊢ₘ[T]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        theory_certificate_code certificate)
    (hParameter : Γ ⊢ₘ[T] parameter ∈ₘ ωₘ)
    (hBodyCarrier : Γ ⊢ₘ[T]
      bodyCode ∈ₘ syntax_formula_code_set_term)
    (hFirstOutputCarrier : Γ ⊢ₘ[T]
      firstOutputCode ∈ₘ syntax_formula_code_set_term)
    (hSecondOutputCarrier : Γ ⊢ₘ[T]
      secondOutputCode ∈ₘ syntax_formula_code_set_term)
    (hUnderOneCarrier : Γ ⊢ₘ[T]
      underOneCode ∈ₘ syntax_formula_code_set_term)
    (hUnderTwoCarrier : Γ ⊢ₘ[T]
      underTwoCode ∈ₘ syntax_formula_code_set_term)
    (hImageCarrier : Γ ⊢ₘ[T]
      imageCode ∈ₘ syntax_formula_code_set_term)
    (hCertificate : Γ ⊢ₘ[T]
      certificate ≐ₘ schema_certificate_payload 2 parameter bodyCode)
    (hBody : Γ ⊢ₘ[T]
      formula_code_condition (Sₘ(Sₘ(parameter))) bodyCode)
    (hFirstOutput : Γ ⊢ₘ[T]
      formula_weaken_bound_condition
        (Sₘ(Sₘ(parameter))) numₘ(0) bodyCode firstOutputCode)
    (hSecondOutput : Γ ⊢ₘ[T]
      formula_weaken_bound_condition
        (Sₘ(Sₘ(parameter))) numₘ(1) bodyCode secondOutputCode)
    (hUnderOne : Γ ⊢ₘ[T]
      formula_weaken_bound_condition
        (Sₘ(Sₘ(parameter))) numₘ(2) bodyCode underOneCode)
    (hUnderTwo : Γ ⊢ₘ[T]
      formula_weaken_bound_condition
        (Sₘ(Sₘ(Sₘ(parameter)))) numₘ(2) underOneCode underTwoCode)
    (hImage : Γ ⊢ₘ[T]
      formula_swap_bound_condition
        (Sₘ(Sₘ(Sₘ(Sₘ(parameter))))) numₘ(0) underTwoCode imageCode)
    (hCore : Γ ⊢ₘ[T]
      formula_code_condition parameter
        (replacement_core_code firstOutputCode secondOutputCode imageCode))
    (hFormula : Γ ⊢ₘ[T]
      formula_code_condition numₘ(0)
        (sequence ·ₘ numₘ(index)))
    (hPrefix : Γ ⊢ₘ[T]
      forall_prefix_code_condition parameter
        (replacement_core_code firstOutputCode secondOutputCode imageCode)
        (sequence ·ₘ numₘ(index))) :
    Γ ⊢ₘ[T]
      IntrinsicCheckedLine.line_instance
        IntrinsicVerifier.replacement_checked_verifier sequence certificates index := by
  have hBranch : Γ ⊢ₘ[T]
      replacement_branch.condition_closed
        (sequence ·ₘ numₘ(index)) certificate :=
    replacement_branch_intro
      (sequence ·ₘ numₘ(index)) certificate parameter bodyCode
      firstOutputCode secondOutputCode underOneCode underTwoCode imageCode
      hParameter hBodyCarrier hFirstOutputCarrier hSecondOutputCarrier
      hUnderOneCarrier hUnderTwoCarrier hImageCarrier hCertificate hBody
      hFirstOutput hSecondOutput hUnderOne hUnderTwo hImage hCore
      hFormula hPrefix
  have hCondition : Γ ⊢ₘ[T]
      IntrinsicVerifier.replacement_checked_verifier.condition
        (sequence ·ₘ numₘ(index)) certificate := by
    change Γ ⊢ₘ[T]
      Formula.substituteMapped
        (VariableSubstitution.empty :
          VariableSubstitution signature [] [] schema_free)
        (VariableSubstitution.cons
          (sequence ·ₘ numₘ(index))
          (VariableSubstitution.cons certificate
            VariableSubstitution.empty))
        ((fixed_table.condition
            (IntrinsicCertificateTable.formula_slot :
              SetOpenTerm IntrinsicCertificateTable.binary_free)
            (IntrinsicCertificateTable.certificate_slot :
              SetOpenTerm IntrinsicCertificateTable.binary_free)) ∨ₘ
          bounded_binary_condition_list replacement_schema_branches
            (IntrinsicCertificateTable.formula_slot :
              SetOpenTerm IntrinsicCertificateTable.binary_free)
            (IntrinsicCertificateTable.certificate_slot :
              SetOpenTerm IntrinsicCertificateTable.binary_free))
    change Γ ⊢ₘ[T]
      (Formula.substituteMapped
          (VariableSubstitution.empty :
            VariableSubstitution signature [] [] schema_free)
          (VariableSubstitution.cons
            (sequence ·ₘ numₘ(index))
            (VariableSubstitution.cons certificate
              VariableSubstitution.empty))
          (fixed_table.condition
            (IntrinsicCertificateTable.formula_slot :
              SetOpenTerm IntrinsicCertificateTable.binary_free)
            (IntrinsicCertificateTable.certificate_slot :
              SetOpenTerm IntrinsicCertificateTable.binary_free))) ∨ₘ
        Formula.substituteMapped
          (VariableSubstitution.empty :
            VariableSubstitution signature [] [] schema_free)
          (VariableSubstitution.cons
            (sequence ·ₘ numₘ(index))
            (VariableSubstitution.cons certificate
              VariableSubstitution.empty))
          (bounded_binary_condition_list replacement_schema_branches
            (IntrinsicCertificateTable.formula_slot :
              SetOpenTerm IntrinsicCertificateTable.binary_free)
          (IntrinsicCertificateTable.certificate_slot :
              SetOpenTerm IntrinsicCertificateTable.binary_free))
    apply FirstOrder.Derives.disj_intro_right
    have hSchema : Γ ⊢ₘ[T]
        bounded_binary_condition_list replacement_schema_branches
          (sequence ·ₘ numₘ(index)) certificate :=
      bounded_binary_condition_list_of_mem
        (show replacement_branch ∈ replacement_schema_branches by
          simp [replacement_schema_branches]) hBranch
    have hTransport :
        Formula.substituteMapped
            (VariableSubstitution.empty :
              VariableSubstitution signature [] [] schema_free)
            (VariableSubstitution.cons
              (sequence ·ₘ numₘ(index))
              (VariableSubstitution.cons certificate
                VariableSubstitution.empty))
            (bounded_binary_condition_list replacement_schema_branches
              (IntrinsicCertificateTable.formula_slot : SetOpenTerm schema_free)
              (IntrinsicCertificateTable.certificate_slot : SetOpenTerm schema_free)) =
          bounded_binary_condition_list replacement_schema_branches
            (sequence ·ₘ numₘ(index)) certificate := by
      simp only [replacement_schema_branches, bounded_binary_condition_list,
        Formula.substituteMapped,
        separation_branch_condition_substituteMapped,
        replacement_branch_condition_substituteMapped]
    rw [hTransport]
    exact hSchema
  exact IntrinsicTheoryLine.line_instance_intro
    IntrinsicVerifier.replacement_checked_verifier
    sequence certificates certificate index hPayloadBound hCertificateCode hCondition

end IntrinsicSchemaLine
end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
