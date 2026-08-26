import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSpecializationAxiomReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCEqAxiomReplay

/-!
# ZFC Hilbert 逻辑公理的统一对象层回放

本模块把元层 `HilbertBaseAxiom` 的十二个构造统一映射到对象层逻辑公理码，
并为全称闭包提供递归回放入口。量词体保留其真实的 binder scope，不把内部
bound variable 错误收紧为空 scope。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation

set_option autoImplicit false

/-! ## 基础 Hilbert 模式 -/

/-- 每个 ZFC 对象语言基础 Hilbert 模式都有对应的逻辑公理码回放。 -/
theorem fs_zfc_support_raw_hilbert_base_axiom_code_exists
    {formula : SetFormula}
    (hAxiom : HilbertBaseAxiom formula)
    (hFormula : Formula.Admissible formula) :
    ∃ code,
      GodelQuotation.Numbered.quote? formula = some code ∧
      Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code) := by
  have hForallBodyAt :
      ∀ {body : SetFormula},
        Formula.Admissible (Formula.forallE SetSort.set body) →
          Formula.AdmissibleAt
            (Scope.push Scope.empty SetSort.set) body := by
    intro body hBody
    rcases hBody with ⟨hWellFormed, hScoped⟩
    cases hWellFormed with
    | forallE _ hBodyWellFormed =>
        cases hScoped with
        | forallE _ hBodyScoped =>
            exact ⟨hBodyWellFormed, hBodyScoped⟩
  have hImpLeftAt :
      ∀ {left right : SetFormula},
        Formula.AdmissibleAt
            (Scope.push Scope.empty SetSort.set)
            (Formula.imp left right) →
          Formula.AdmissibleAt
            (Scope.push Scope.empty SetSort.set) left := by
    intro left right hImp
    rcases hImp with ⟨hWellFormed, hScoped⟩
    cases hWellFormed with
    | imp hLeft _ =>
        cases hScoped with
        | imp hLeftScoped _ =>
            exact ⟨hLeft, hLeftScoped⟩
  have hImpRightAt :
      ∀ {left right : SetFormula},
        Formula.AdmissibleAt
            (Scope.push Scope.empty SetSort.set)
            (Formula.imp left right) →
          Formula.AdmissibleAt
            (Scope.push Scope.empty SetSort.set) right := by
    intro left right hImp
    rcases hImp with ⟨hWellFormed, hScoped⟩
    cases hWellFormed with
    | imp _ hRight =>
        cases hScoped with
        | imp _ hRightScoped =>
            exact ⟨hRight, hRightScoped⟩
  cases hAxiom with
  | implication_distribution antecedent middle consequent =>
      have hOuterLeft := Formula.Admissible.imp_left hFormula
      have hMiddleConsequent := Formula.Admissible.imp_right hOuterLeft
      exact fs_zfc_support_raw_implication_distribution_axiom_code_exists
        (Formula.Admissible.imp_left hOuterLeft)
        (Formula.Admissible.imp_left hMiddleConsequent)
        (Formula.Admissible.imp_right hMiddleConsequent)
  | self_implication formula =>
      exact fs_zfc_support_raw_self_implication_axiom_code_exists
        (Formula.Admissible.imp_left hFormula)
  | weakening formula extra =>
      have hRight := Formula.Admissible.imp_right hFormula
      exact fs_zfc_support_raw_weakening_axiom_code_exists
        (Formula.Admissible.imp_left hFormula)
        (Formula.Admissible.imp_left hRight)
  | contradiction formula conclusion =>
      exact fs_zfc_support_raw_contradiction_axiom_code_exists
        (Formula.Admissible.imp_left hFormula)
        (Formula.Admissible.imp_right
          (Formula.Admissible.imp_right hFormula))
  | classical formula =>
      exact fs_zfc_support_raw_classical_axiom_code_exists
        (Formula.Admissible.imp_right hFormula)
  | explosion formula conclusion =>
      have hNeg := Formula.Admissible.imp_left hFormula
      exact fs_zfc_support_raw_explosion_axiom_code_exists
        (Formula.Admissible.neg_body hNeg)
        (Formula.Admissible.imp_right
          (Formula.Admissible.imp_right hFormula))
  | case_analysis formula conclusion =>
      have hPositive := Formula.Admissible.imp_left hFormula
      have hNegative := Formula.Admissible.imp_right hFormula
      exact fs_zfc_support_raw_case_analysis_axiom_code_exists
        (Formula.Admissible.imp_left hPositive)
        (Formula.Admissible.imp_right hPositive)
  | forall_specialization sort body term hTerm hClosed =>
      cases sort
      have hForall := Formula.Admissible.imp_left hFormula
      exact fs_zfc_support_raw_specialization_axiom_code_exists
        (hForallBodyAt hForall) ⟨hTerm, hClosed⟩
  | forall_distribution sort antecedent consequent =>
      cases sort
      have hForallImp :=
        Formula.Admissible.imp_left hFormula
      have hInner :=
        hForallBodyAt hForallImp
      exact fs_zfc_support_raw_quantifier_distribution_axiom_code_exists
        (hImpLeftAt hInner)
        (hImpRightAt hInner)
  | vacuous_forall sort eigen formula hFresh =>
      cases sort
      exact fs_zfc_support_raw_vacuous_quantifier_axiom_code_exists
        eigen (Formula.Admissible.imp_left hFormula) hFresh
  | equality_substitution sort leftId rightId body =>
      cases sort
      rcases fs_zfc_support_raw_equality_substitution_axiom_code_exists
          leftId rightId
          (Formula.Admissible.imp_left
            (Formula.Admissible.imp_right hFormula)) with
        ⟨code, hQuote, hLogical, _⟩
      exact ⟨code, hQuote, hLogical⟩
  | equality_reflexivity sort id =>
      cases sort
      exact fs_zfc_support_raw_equality_reflexivity_axiom_code_exists id

/-! ## 完整 Hilbert 逻辑公理 -/

/-- 每个 ZFC 对象语言 Hilbert 逻辑公理都有对应的逻辑公理码回放。 -/
theorem fs_zfc_support_raw_hilbert_logical_axiom_code_exists
    {formula : SetFormula}
    (hAxiom : HilbertLogicalAxiom formula)
    (hFormula : Formula.Admissible formula) :
    ∃ code,
      GodelQuotation.Numbered.quote? formula = some code ∧
      Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code) := by
  induction hAxiom with
  | base hBase =>
      exact fs_zfc_support_raw_hilbert_base_axiom_code_exists
        hBase hFormula
  | @forall_closure formula sort eigen hAxiom ih =>
      cases sort
      have hInnerFormula : Formula.Admissible formula := by
        have hOpened :=
          Formula.Admissible.forall_openAt
            SetSort.set hFormula
            (⟨TermWellSorted.fvar
                (σ := Nonlogical.BasicSetTheory.signature)
                SetSort.set eigen,
              TermScoped.fvar
                (σ := Nonlogical.BasicSetTheory.signature)
                (ctx := Scope.empty) SetSort.set eigen⟩)
        simpa [Formula.openAt_closeFreeAt] using hOpened
      rcases ih hInnerFormula with
        ⟨sourceCode, hSourceQuote, hSourceLogical⟩
      have hSourceBoundary :=
        GodelQuotation.Numbered.quote?_code_boundary hSourceQuote
      have hSourceMember :=
        fs_zfc_support_raw_logical_axiom_member_of_code
          sourceCode hSourceBoundary.1 hSourceLogical
      rcases
          fs_zfc_support_raw_canonical_forall_closure_condition_of_quotation
            eigen hInnerFormula with
        ⟨sourceCode', variableCode, targetCode,
          hSourceQuote', hVariableQuote, hTargetQuote, hClosure⟩
      have hSourceCodeEq : sourceCode' = sourceCode :=
        Option.some.inj (hSourceQuote'.symm.trans hSourceQuote)
      subst sourceCode'
      have hTargetCode :
          Term.Admissible targetCode SetSort.set :=
        (GodelQuotation.Numbered.quote?_code_boundary
          hTargetQuote).1
      have hTargetClosed :
          Term.freeSupport targetCode = [] := by
        exact (GodelQuotation.Numbered.quote?_code_boundary
          hTargetQuote).2
      have hSourceBoundary :=
        GodelQuotation.Numbered.quote?_code_boundary hSourceQuote
      have hVariableBoundary :=
        GodelQuotation.Numbered.quote_term_with?_code_boundary
          GodelQuotation.free_name [] hVariableQuote
      have hSourceMember :=
        fs_zfc_support_raw_logical_axiom_member_of_code
          sourceCode
          hSourceBoundary.1 hSourceLogical
      have hGeneration :
          Derives fs_zfc_support_raw_theory [] (
            logical_axiom_code_generation_condition
              LogicAxiomsₘ targetCode) := by
        let body : SetFormula :=
          ((x#454 ∈ₘ LogicAxiomsₘ) ∧ₘ
            canonical_forall_closure_code_condition
              (x#454) (x#455) targetCode)
        have hSourceSubstitute (id : FreeVarId)
            (replacement : SetTerm) :
            Term.substituteFree SetSort.set id replacement sourceCode =
              sourceCode :=
          Term.substituteFree_eq_self_of_not_mem
            SetSort.set id replacement sourceCode (by
              rw [hSourceBoundary.2]
              exact List.not_mem_nil)
        have hVariableSubstitute (id : FreeVarId)
            (replacement : SetTerm) :
            Term.substituteFree SetSort.set id replacement variableCode =
              variableCode :=
          Term.substituteFree_eq_self_of_not_mem
            SetSort.set id replacement variableCode (by
              rw [hVariableBoundary.2]
              exact List.not_mem_nil)
        have hTargetSubstitute (id : FreeVarId)
            (replacement : SetTerm) :
            Term.substituteFree SetSort.set id replacement targetCode =
              targetCode :=
          Term.substituteFree_eq_self_of_not_mem
            SetSort.set id replacement targetCode (by
              rw [hTargetClosed]
              exact List.not_mem_nil)
        have hNumeralSubstitute (id : FreeVarId)
            (replacement : SetTerm) (value : Nat) :
            Term.substituteFree SetSort.set id replacement (numₘ(value)) =
              numₘ(value) :=
          Term.substituteFree_eq_self_of_not_mem
            SetSort.set id replacement (numₘ(value)) (by
              simp [finite_numeral_term_freeSupport])
        have hSourceCloseComm
            (closedId : FreeVarId) (depth : Nat)
            (formula : SetFormula) (hDistinct : 454 ≠ closedId) :
            Formula.substituteFree SetSort.set 454 sourceCode
                (Formula.closeFreeAt SetSort.set closedId depth formula) =
              Formula.closeFreeAt SetSort.set closedId depth
                (Formula.substituteFree SetSort.set 454 sourceCode formula) :=
          (Formula.closeFreeAt_substituteFree_comm
            SetSort.set 454 closedId depth sourceCode formula
            hDistinct hSourceBoundary.1.2 (by
              rw [hSourceBoundary.2]
              exact List.not_mem_nil)).symm
        have hVariableCloseComm
            (closedId : FreeVarId) (depth : Nat)
            (formula : SetFormula) (hDistinct : 455 ≠ closedId) :
            Formula.substituteFree SetSort.set 455 variableCode
                (Formula.closeFreeAt SetSort.set closedId depth formula) =
              Formula.closeFreeAt SetSort.set closedId depth
                (Formula.substituteFree SetSort.set 455 variableCode formula) :=
          (Formula.closeFreeAt_substituteFree_comm
            SetSort.set 455 closedId depth variableCode formula
            hDistinct hVariableBoundary.1.2 (by
              rw [hVariableBoundary.2]
              exact List.not_mem_nil)).symm
        have hClosureSubstitute :
            Formula.substituteFree SetSort.set 455 variableCode
                (Formula.substituteFree SetSort.set 454 sourceCode
                  (canonical_forall_closure_code_condition
                    (x#454) (x#455) targetCode)) =
              canonical_forall_closure_code_condition
                sourceCode variableCode targetCode := by
          simp [canonical_forall_closure_code_condition,
            canonical_forall_closure_code_condition_with_ids,
            canonical_free_variable_code_condition_with_id,
            canonical_binder_shift_code_condition_with_ids,
            canonical_binder_shift_token_condition_with_ids,
            code_substitution_spec, substitution_piece_condition,
            Formula.substituteFree, Term.substituteFree, set_variable,
            hSourceCloseComm, hVariableCloseComm,
            hSourceSubstitute,
            hTargetSubstitute, hNumeralSubstitute]
        have hBody :
            Derives fs_zfc_support_raw_theory [] (
              Formula.substituteFree SetSort.set 455 variableCode
                (Formula.substituteFree SetSort.set 454 sourceCode
                  body)) := by
          simpa [body, Formula.substituteFree, Term.substituteFree,
            set_variable,
            hSourceSubstitute, hVariableSubstitute,
            hTargetSubstitute,
            hClosureSubstitute] using
            FirstOrder.Derives.conjIntro
              hSourceMember hClosure
        have hWitness :=
          fs_zfc_support_raw_exists_two_of_substituted
            body 454 455 sourceCode variableCode
            hSourceBoundary
            hVariableBoundary (by decide) hBody
        nd_apply FirstOrder.Derives.disjIntroRight
        simpa [body, logical_axiom_code_generation_condition] using
          hWitness
      exact ⟨targetCode, hTargetQuote,
        fs_zfc_support_raw_logical_axiom_code_of_generation_condition
          targetCode hTargetCode hTargetClosed hGeneration⟩

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
