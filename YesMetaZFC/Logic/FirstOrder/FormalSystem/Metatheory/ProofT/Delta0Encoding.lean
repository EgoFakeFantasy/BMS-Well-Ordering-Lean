import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Hierarchy
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta0Support
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CertifiedProofCodeEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CertifiedSequenceCodeEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaBinderCode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.RosserFinite

/-!
# `ProofT` 编码条件的 `Delta0` 支撑

本模块只处理证明码中不依赖具体 verifier 的对象层条件。所有对象量词都必须
显式带有成员界；因此这里的结论是正式的 `Formula.IsDelta0`，不是对外部可计算
检查器的注释性描述。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace Delta0Encoding

open Nonlogical.BasicSetTheory
open GodelQuotation
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-! ## 公式回放的词法条件 -/

private theorem successor_bound_free_at
    (term : SetTerm)
    (hTerm : Term.BoundFreeAt SetSort.set 0 term) :
    Term.BoundFreeAt SetSort.set 0 (Sₘ(term)) := by
  exact Term.BoundFreeAt.app FunctionSymbol.successor
    (Term.ArgsBoundFreeAt.cons hTerm Term.ArgsBoundFreeAt.nil)

private theorem application_bound_free_at
    (function argument : SetTerm)
    (hFunction : Term.BoundFreeAt SetSort.set 0 function)
    (hArgument : Term.BoundFreeAt SetSort.set 0 argument) :
    Term.BoundFreeAt SetSort.set 0 (function ·ₘ argument) := by
  exact Term.BoundFreeAt.app FunctionSymbol.application
    (Term.ArgsBoundFreeAt.cons hFunction
      (Term.ArgsBoundFreeAt.cons hArgument Term.ArgsBoundFreeAt.nil))

private theorem domain_bound_free_at
    (term : SetTerm)
    (hTerm : Term.BoundFreeAt SetSort.set 0 term) :
    Term.BoundFreeAt SetSort.set 0 (domₘ(term)) := by
  exact Term.BoundFreeAt.app FunctionSymbol.domain
    (Term.ArgsBoundFreeAt.cons hTerm Term.ArgsBoundFreeAt.nil)

private theorem application_with_free_variable_bound_free_at
    (function : SetTerm)
    (id : FreeVarId)
    (hFunction : Term.BoundFreeAt SetSort.set 0 function) :
  Term.BoundFreeAt SetSort.set 0 (function ·ₘ x#id) :=
  application_bound_free_at function (x#id)
    hFunction
      (Term.BoundFreeAt.fvar
        (σ := signature)
        (target := SetSort.set) (depth := 0)
        SetSort.set id)

theorem fs_variable_token_condition_delta0
    (token : SetTerm)
    (hToken : Term.BoundFreeAt SetSort.set 0 token) :
    Formula.IsDelta0 set_levy_bound
      (fs_variable_token_condition token) := by
  have hBound :
      Term.BoundFreeAt SetSort.set 0 (Sₘ(token)) :=
    successor_bound_free_at token hToken
  have hBody :
      Formula.IsDelta0 set_levy_bound
        ((bₛ#0 ∈ₘ Sₘ(token)) ∧ₘ
          (sym_codeₘ(token) ≐ₘ
            variable_symbol_code_term (bₛ#0))) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [bₛ#0, Sₘ(token)])
      (Formula.IsDelta0.equal
        (sym_codeₘ(token))
        (variable_symbol_code_term (bₛ#0)))
  simpa [fs_variable_token_condition] using
    Formula.IsDelta0.guarded_exists
      (Sₘ(token))
      (((bₛ#0 ∈ₘ Sₘ(token)) ∧ₘ
        (sym_codeₘ(token) ≐ₘ
          variable_symbol_code_term (bₛ#0))))
      hBound hBody
      (Formula.MembershipGuard.conj_left
        Formula.MembershipGuard.membership)

theorem fs_formula_token_condition_lifted_delta0
    (token variableToken : SetTerm)
    (hVariableToken :
      Term.BoundFreeAt SetSort.set 0 variableToken) :
    Formula.IsDelta0 set_levy_bound
      (fs_formula_token_condition_lifted token variableToken) := by
  exact Formula.IsDelta0.disj
    (Formula.IsDelta0.disj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [sym_codeₘ(token), LogicSymₘ])
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [sym_codeₘ(token), MembershipSymₘ]))
    (Formula.IsDelta0.disj
      (fs_variable_token_condition_delta0
        variableToken hVariableToken)
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [sym_codeₘ(token),
          fs_nonlogical_symbol_code_set_term]))

theorem fs_formula_token_condition_delta0
    (token : SetTerm)
    (hToken : Term.BoundFreeAt SetSort.set 0 token) :
    Formula.IsDelta0 set_levy_bound
      (fs_formula_token_condition token) := by
  simpa [fs_formula_token_condition] using
    fs_formula_token_condition_lifted_delta0 token token hToken

theorem fs_formula_signature_condition_with_id_delta0
    (code : SetTerm) (tokenIndexId : FreeVarId)
    (hCode : Term.BoundFreeAt SetSort.set 0 code)
    (hFresh :
      (SetSort.set, tokenIndexId) ∉
        Term.freeSupport (domₘ(code))) :
    Formula.IsDelta0 set_levy_bound
      (fs_formula_signature_condition_with_id
        code tokenIndexId) := by
  have hIndex :
      Term.BoundFreeAt SetSort.set 0 (x#tokenIndexId) :=
    Term.BoundFreeAt.fvar
      (σ := signature)
      (target := SetSort.set) (depth := 0)
      SetSort.set tokenIndexId
  have hDomain :
      Term.BoundFreeAt SetSort.set 0 (domₘ(code)) :=
    domain_bound_free_at code hCode
  have hValue :
      Term.BoundFreeAt SetSort.set 0
        (code ·ₘ x#tokenIndexId) :=
    application_bound_free_at code (x#tokenIndexId)
      hCode hIndex
  have hPoint :
      Formula.IsDelta0 set_levy_bound
        (fs_formula_token_condition
          (code ·ₘ x#tokenIndexId)) :=
    fs_formula_token_condition_delta0
      (code ·ₘ x#tokenIndexId) hValue
  simpa [fs_formula_signature_condition_with_id] using
    Formula.IsDelta0.bounded_forall_closeFreeAt
      tokenIndexId (domₘ(code)) hFresh hPoint

theorem fs_formula_signature_condition_delta0
    (code : SetTerm)
    (hCode : Term.BoundFreeAt SetSort.set 0 code) :
    Formula.IsDelta0 set_levy_bound
      (fs_formula_signature_condition code) := by
  have hDomain :
      Term.BoundFreeAt SetSort.set 0 (domₘ(code)) :=
    domain_bound_free_at code hCode
  have hVariableToken :
      Term.BoundFreeAt SetSort.set 0
        (code ·ₘ bₛ#1) :=
    application_bound_free_at code bₛ#1 hCode
      (Term.BoundFreeAt.bvar
        (σ := signature)
        (target := SetSort.set) (depth := 0)
        SetSort.set 1 (by simp))
  have hPoint :
      Formula.IsDelta0 set_levy_bound
        (fs_formula_token_condition_lifted
          (code ·ₘ bₛ#0)
          (code ·ₘ bₛ#1)) :=
    fs_formula_token_condition_lifted_delta0
      (code ·ₘ bₛ#0)
      (code ·ₘ bₛ#1)
      hVariableToken
  simpa [fs_formula_signature_condition] using
    Formula.IsDelta0.bounded_forall
      (domₘ(code))
      (fs_formula_token_condition_lifted
        (code ·ₘ bₛ#0)
        (code ·ₘ bₛ#1))
      hDomain hPoint

theorem fs_formula_binder_condition_lifted_delta0
    (code index nextToken : SetTerm)
    (hNextToken : Term.BoundFreeAt SetSort.set 0 nextToken) :
    Formula.IsDelta0 set_levy_bound
      (fs_formula_binder_condition_lifted
        code index nextToken) := by
  exact Formula.IsDelta0.imp
    (Formula.IsDelta0.equal
      (code ·ₘ index)
      (numₘ(Numbered.logical_token .universal)))
    (Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [Sₘ(index), domₘ(code)])
      (fs_variable_token_condition_delta0
        nextToken hNextToken))

theorem fs_formula_binder_condition_with_id_delta0
    (code : SetTerm) (tokenIndexId : FreeVarId)
    (hCode : Term.BoundFreeAt SetSort.set 0 code)
    (hFresh :
      (SetSort.set, tokenIndexId) ∉
        Term.freeSupport (domₘ(code))) :
    Formula.IsDelta0 set_levy_bound
      (fs_formula_binder_condition_with_id
        code tokenIndexId) := by
  have hIndex :
      Term.BoundFreeAt SetSort.set 0 (x#tokenIndexId) :=
    Term.BoundFreeAt.fvar
      (σ := signature)
      (target := SetSort.set) (depth := 0)
      SetSort.set tokenIndexId
  have hNext :
      Term.BoundFreeAt SetSort.set 0
        (code ·ₘ Sₘ(x#tokenIndexId)) :=
    application_bound_free_at code (Sₘ(x#tokenIndexId))
      hCode (successor_bound_free_at
        (x#tokenIndexId) hIndex)
  have hBody :
      Formula.IsDelta0 set_levy_bound
        (fs_formula_binder_condition_lifted
          code (x#tokenIndexId)
          (code ·ₘ Sₘ(x#tokenIndexId))) :=
    fs_formula_binder_condition_lifted_delta0
      code (x#tokenIndexId)
      (code ·ₘ Sₘ(x#tokenIndexId)) hNext
  simpa [fs_formula_binder_condition_with_id] using
    Formula.IsDelta0.bounded_forall_closeFreeAt
      tokenIndexId (domₘ(code)) hFresh hBody

theorem fs_formula_binder_condition_delta0
    (code : SetTerm)
    (hCode : Term.BoundFreeAt SetSort.set 0 code) :
    Formula.IsDelta0 set_levy_bound
      (fs_formula_binder_condition code) := by
  have hDomain :
      Term.BoundFreeAt SetSort.set 0 (domₘ(code)) :=
    domain_bound_free_at code hCode
  have hNext :
      Term.BoundFreeAt SetSort.set 0
        (code ·ₘ Sₘ(bₛ#1)) :=
    application_bound_free_at code (Sₘ(bₛ#1))
      hCode
      (successor_bound_free_at
        bₛ#1
        (Term.BoundFreeAt.bvar
          (σ := signature)
          (target := SetSort.set) (depth := 0)
          SetSort.set 1 (by simp)))
  have hBody :
      Formula.IsDelta0 set_levy_bound
        (fs_formula_binder_condition_lifted
          code bₛ#0
          (code ·ₘ Sₘ(bₛ#1))) :=
    fs_formula_binder_condition_lifted_delta0
      code bₛ#0
      (code ·ₘ Sₘ(bₛ#1)) hNext
  simpa [fs_formula_binder_condition] using
    Formula.IsDelta0.bounded_forall
      (domₘ(code))
      (fs_formula_binder_condition_lifted
        code bₛ#0
        (code ·ₘ Sₘ(bₛ#1)))
      hDomain hBody

theorem fs_formula_replay_condition_with_id_delta0
    (code : SetTerm) (tokenIndexId : FreeVarId)
    (hCode : Term.BoundFreeAt SetSort.set 0 code)
    (hFresh :
      (SetSort.set, tokenIndexId) ∉
        Term.freeSupport (domₘ(code))) :
    Formula.IsDelta0 set_levy_bound
      (fs_formula_replay_condition_with_id
        code tokenIndexId) := by
  exact Formula.IsDelta0.conj
    (fs_formula_signature_condition_with_id_delta0
      code tokenIndexId hCode hFresh)
    (fs_formula_binder_condition_with_id_delta0
      code tokenIndexId hCode hFresh)

theorem fs_formula_replay_condition_delta0
    (code : SetTerm)
    (hCode : Term.BoundFreeAt SetSort.set 0 code) :
    Formula.IsDelta0 set_levy_bound
      (fs_formula_replay_condition code) := by
  exact Formula.IsDelta0.conj
    (fs_formula_signature_condition_delta0 code hCode)
    (fs_formula_binder_condition_delta0 code hCode)

/-! ## 逻辑证书的有限合取与见证闭包 -/

private theorem logical_certificate_conjunction_delta0
    (formulas : List SetFormula)
    (hFormulas :
      ∀ formula, formula ∈ formulas →
        Formula.IsDelta0 set_levy_bound formula) :
    Formula.IsDelta0 set_levy_bound
      (CertifiedProof.logical_certificate_conjunction formulas) := by
  induction formulas with
  | nil =>
      simpa [CertifiedProof.logical_certificate_conjunction] using
        (Formula.IsDelta0.truth :
          Formula.IsDelta0 set_levy_bound
            (Formula.truth : SetFormula))
  | cons formula formulas ih =>
      cases formulas with
      | nil =>
          simpa [CertifiedProof.logical_certificate_conjunction] using
            hFormulas formula (by simp)
      | cons next rest =>
          simpa [CertifiedProof.logical_certificate_conjunction] using
            Formula.IsDelta0.conj
              (hFormulas formula (by simp))
              (ih (fun item hItem =>
                hFormulas item (by simp [hItem])))

theorem logical_certificate_body_with_ids_delta0
    (formulaCode certificatePayload
      certificateSequence formulaTrace lastIndex : SetTerm)
    (certificateSequenceId formulaTraceId lastIndexId lineIndexId
      codeTraceId codeIndexId : FreeVarId)
    (hPayloadCode :
      Formula.IsDelta0 set_levy_bound
        (nat_sequence_code_condition_with_ids
          certificateSequence certificatePayload
          codeTraceId codeIndexId))
    (hFormulaTraceSpace :
      Formula.IsDelta0 set_levy_bound
        (formulaTrace ∈ₘ
          seq₊_spaceₘ(FormulaCodeₘ)))
    (hEqualDomains :
      Formula.IsDelta0 set_levy_bound
        (domₘ(formulaTrace) ≐ₘ
          domₘ(certificateSequence)))
    (hNonemptyDomain :
      Formula.IsDelta0 set_levy_bound
        (domₘ(certificateSequence) ≐ₘ Sₘ(lastIndex)))
    (hInitialFormula :
      Formula.IsDelta0 set_levy_bound
        (formulaCode ≐ₘ
          (formulaTrace ·ₘ numₘ(0))))
    (hBaseCertificate :
      Formula.IsDelta0 set_levy_bound
        (CertifiedProof.logical_base_certificate_condition_with_base
          (formulaTrace ·ₘ lastIndex)
          (certificateSequence ·ₘ lastIndex)
          (CertifiedProof.logical_certificate_body_base_with_ids
            certificateSequenceId formulaTraceId lastIndexId)))
    (hLineFresh :
      (SetSort.set, lineIndexId) ∉
        Term.freeSupport lastIndex)
    (hClosureStep :
      Formula.IsDelta0 set_levy_bound
        (CertifiedProof.logical_closure_certificate_step_condition
          certificateSequence formulaTrace
          (x#lineIndexId))) :
    Formula.IsDelta0 set_levy_bound
      (CertifiedProof.logical_certificate_body_with_ids
        formulaCode certificatePayload
        certificateSequence formulaTrace lastIndex
        certificateSequenceId formulaTraceId lastIndexId lineIndexId
        codeTraceId codeIndexId) := by
  let closureCondition : SetFormula :=
    ∀ₘ[SetSort.set, lineIndexId],
      (x#lineIndexId ∈ₘ lastIndex) ⟶ₘ
        CertifiedProof.logical_closure_certificate_step_condition
          certificateSequence formulaTrace
          (x#lineIndexId)
  have hClosure :
      Formula.IsDelta0 set_levy_bound
        closureCondition := by
    simpa [closureCondition] using
      Formula.IsDelta0.bounded_forall_closeFreeAt
        lineIndexId lastIndex hLineFresh hClosureStep
  have hConjunction :
      Formula.IsDelta0 set_levy_bound
        (CertifiedProof.logical_certificate_conjunction [
          nat_sequence_code_condition_with_ids
            certificateSequence certificatePayload
            codeTraceId codeIndexId,
          formulaTrace ∈ₘ seq₊_spaceₘ(FormulaCodeₘ),
          domₘ(formulaTrace) ≐ₘ domₘ(certificateSequence),
          domₘ(certificateSequence) ≐ₘ Sₘ(lastIndex),
          formulaCode ≐ₘ (formulaTrace ·ₘ numₘ(0)),
          CertifiedProof.logical_base_certificate_condition_with_base
            (formulaTrace ·ₘ lastIndex)
            (certificateSequence ·ₘ lastIndex)
            (CertifiedProof.logical_certificate_body_base_with_ids
              certificateSequenceId formulaTraceId lastIndexId),
          closureCondition]) := by
    apply logical_certificate_conjunction_delta0
    intro formula hFormula
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hFormula
    rcases hFormula with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hPayloadCode
    · exact hFormulaTraceSpace
    · exact hEqualDomains
    · exact hNonemptyDomain
    · exact hInitialFormula
    · exact hBaseCertificate
    · exact hClosure
  simpa [CertifiedProof.logical_certificate_body_with_ids,
    closureCondition] using
    hConjunction

theorem logical_certificate_condition_with_ids_delta0_of_body
    (formulaCode certificatePayload : SetTerm)
    (certificateSequenceId formulaTraceId lastIndexId lineIndexId
      codeTraceId codeIndexId : FreeVarId)
    (hBody :
      Formula.IsDelta0 set_levy_bound
        (CertifiedProof.logical_certificate_body_with_ids
          formulaCode certificatePayload
          (x#certificateSequenceId) (x#formulaTraceId)
          (x#lastIndexId)
          certificateSequenceId formulaTraceId lastIndexId lineIndexId
          codeTraceId codeIndexId))
    (hLastFresh :
      (SetSort.set, lastIndexId) ∉
        Term.freeSupport (domₘ(x#certificateSequenceId)))
    (hTraceFresh :
      (SetSort.set, formulaTraceId) ∉
        Term.freeSupport
          (seq₊_spaceₘ(FormulaCodeₘ)))
    (hSequenceFresh :
      (SetSort.set, certificateSequenceId) ∉
        Term.freeSupport
          (seq_spaceₘ(ωₘ))) :
    Formula.IsDelta0 set_levy_bound
      (CertifiedProof.logical_certificate_condition_with_ids
        formulaCode certificatePayload
        certificateSequenceId formulaTraceId lastIndexId lineIndexId
        codeTraceId codeIndexId) := by
  have hLastBody :
      Formula.IsDelta0 set_levy_bound
        ((x#lastIndexId ∈ₘ
            domₘ(x#certificateSequenceId)) ∧ₘ
          CertifiedProof.logical_certificate_body_with_ids
            formulaCode certificatePayload
            (x#certificateSequenceId) (x#formulaTraceId)
            (x#lastIndexId)
            certificateSequenceId formulaTraceId lastIndexId lineIndexId
            codeTraceId codeIndexId) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [x#lastIndexId, domₘ(x#certificateSequenceId)])
      hBody
  have hLast :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, lastIndexId],
          (x#lastIndexId ∈ₘ
              domₘ(x#certificateSequenceId)) ∧ₘ
            CertifiedProof.logical_certificate_body_with_ids
              formulaCode certificatePayload
              (x#certificateSequenceId) (x#formulaTraceId)
              (x#lastIndexId)
              certificateSequenceId formulaTraceId lastIndexId lineIndexId
              codeTraceId codeIndexId) := by
    simpa using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        lastIndexId (domₘ(x#certificateSequenceId))
        hLastFresh hLastBody
        (Formula.FreeMembershipGuard.conj_left
          Formula.FreeMembershipGuard.membership)
  have hTraceBody :
      Formula.IsDelta0 set_levy_bound
        ((x#formulaTraceId ∈ₘ
            seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
          (∃ₘ[SetSort.set, lastIndexId],
            (x#lastIndexId ∈ₘ
                domₘ(x#certificateSequenceId)) ∧ₘ
              CertifiedProof.logical_certificate_body_with_ids
                formulaCode certificatePayload
                (x#certificateSequenceId) (x#formulaTraceId)
                (x#lastIndexId)
                certificateSequenceId formulaTraceId lastIndexId lineIndexId
                codeTraceId codeIndexId)) := by
    exact Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [x#formulaTraceId,
          seq₊_spaceₘ(FormulaCodeₘ)])
      hLast
  have hTrace :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, formulaTraceId],
          (x#formulaTraceId ∈ₘ
              seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
            (∃ₘ[SetSort.set, lastIndexId],
              (x#lastIndexId ∈ₘ
                  domₘ(x#certificateSequenceId)) ∧ₘ
                CertifiedProof.logical_certificate_body_with_ids
                  formulaCode certificatePayload
                  (x#certificateSequenceId) (x#formulaTraceId)
                  (x#lastIndexId)
                  certificateSequenceId formulaTraceId lastIndexId lineIndexId
                  codeTraceId codeIndexId)) := by
    simpa using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        formulaTraceId (seq₊_spaceₘ(FormulaCodeₘ))
        hTraceFresh hTraceBody
        (Formula.FreeMembershipGuard.conj_left
          Formula.FreeMembershipGuard.membership)
  have hSequenceBody :
      Formula.IsDelta0 set_levy_bound
        ((x#certificateSequenceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
          (∃ₘ[SetSort.set, formulaTraceId],
            (x#formulaTraceId ∈ₘ
                seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
              (∃ₘ[SetSort.set, lastIndexId],
                (x#lastIndexId ∈ₘ
                    domₘ(x#certificateSequenceId)) ∧ₘ
                  CertifiedProof.logical_certificate_body_with_ids
                    formulaCode certificatePayload
                    (x#certificateSequenceId) (x#formulaTraceId)
                    (x#lastIndexId)
                    certificateSequenceId formulaTraceId lastIndexId lineIndexId
                    codeTraceId codeIndexId))) := by
    exact Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [x#certificateSequenceId, seq_spaceₘ(ωₘ)])
      hTrace
  simpa using
    Formula.IsDelta0.guarded_exists_closeFreeAt
      certificateSequenceId (seq_spaceₘ(ωₘ))
      hSequenceFresh hSequenceBody
      (Formula.FreeMembershipGuard.conj_left
        Formula.FreeMembershipGuard.membership)

/-! ## 逐行 verifier 与序列合法性 -/

/-- MP 证书分支只使用两个有限初始段上的有界见证。 -/
theorem modus_ponens_line_condition_with_ids_delta0
    (sequence certificates index : SetTerm)
    (implicationIndex premiseIndex : FreeVarId)
    (hImplicationFresh :
      (SetSort.set, implicationIndex) ∉
        Term.freeSupport index)
    (hPremiseFresh :
      (SetSort.set, premiseIndex) ∉
        Term.freeSupport (x#implicationIndex)) :
    Formula.IsDelta0 set_levy_bound
      (CertifiedProof.modus_ponens_line_condition_with_ids
        sequence certificates index implicationIndex premiseIndex) := by
  have hPremiseBody :
      Formula.IsDelta0 set_levy_bound
        ((x#premiseIndex ∈ₘ x#implicationIndex) ∧ₘ
          (((certificates ·ₘ index) ≐ₘ
              CertifiedProof.modus_ponens_certificate_code
                (x#implicationIndex) (x#premiseIndex)) ∧ₘ
            modus_ponensₘ(
              sequence ·ₘ x#premiseIndex,
              sequence ·ₘ x#implicationIndex,
              sequence ·ₘ index))) := by
    exact Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [x#premiseIndex, x#implicationIndex])
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.equal
          (certificates ·ₘ index)
          (CertifiedProof.modus_ponens_certificate_code
            (x#implicationIndex) (x#premiseIndex)))
        (Formula.IsDelta0.rel
          RelationSymbol.modusPonens
          [sequence ·ₘ x#premiseIndex,
            sequence ·ₘ x#implicationIndex,
            sequence ·ₘ index]))
  have hPremise :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, premiseIndex],
          (x#premiseIndex ∈ₘ x#implicationIndex) ∧ₘ
            (((certificates ·ₘ index) ≐ₘ
                CertifiedProof.modus_ponens_certificate_code
                  (x#implicationIndex) (x#premiseIndex)) ∧ₘ
              modus_ponensₘ(
                sequence ·ₘ x#premiseIndex,
                sequence ·ₘ x#implicationIndex,
                sequence ·ₘ index))) := by
    simpa using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        premiseIndex (x#implicationIndex)
        hPremiseFresh hPremiseBody
        (Formula.FreeMembershipGuard.conj_left
          Formula.FreeMembershipGuard.membership)
  let implicationBody : SetFormula :=
    (x#implicationIndex ∈ₘ index) ∧ₘ
      (∃ₘ[SetSort.set, premiseIndex],
        (x#premiseIndex ∈ₘ x#implicationIndex) ∧ₘ
          (((certificates ·ₘ index) ≐ₘ
              CertifiedProof.modus_ponens_certificate_code
                (x#implicationIndex) (x#premiseIndex)) ∧ₘ
            modus_ponensₘ(
              sequence ·ₘ x#premiseIndex,
              sequence ·ₘ x#implicationIndex,
              sequence ·ₘ index)))
  have hImplicationBody :
      Formula.IsDelta0 set_levy_bound implicationBody := by
    simpa [implicationBody] using
      Formula.IsDelta0.conj
        (Formula.IsDelta0.rel
          RelationSymbol.membership
          [x#implicationIndex, index])
        hPremise
  simpa [CertifiedProof.modus_ponens_line_condition_with_ids] using
    Formula.IsDelta0.guarded_exists_closeFreeAt
      implicationIndex index
      hImplicationFresh hImplicationBody
      (Formula.FreeMembershipGuard.conj_left
        Formula.FreeMembershipGuard.membership)

/-- 理论公理证书分支的唯一见证由证书 payload 的有界性承载。 -/
theorem theory_certificate_line_condition_with_id_delta0
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm)
    (certificateCodeId : FreeVarId)
    (hCertificateFresh :
      (SetSort.set, certificateCodeId) ∉
        Term.freeSupport (Sₘ(certificates ·ₘ index)))
    (hCondition :
      Formula.IsDelta0 set_levy_bound
        (verifier.condition
          (sequence ·ₘ index) (x#certificateCodeId))) :
    Formula.IsDelta0 set_levy_bound
      (CertifiedProof.theory_certificate_line_condition_with_id
        verifier sequence certificates index certificateCodeId) := by
  have hBody :
      Formula.IsDelta0 set_levy_bound
        ((x#certificateCodeId ∈ₘ Sₘ(certificates ·ₘ index)) ∧ₘ
          (((certificates ·ₘ index) ≐ₘ
              CertifiedProof.theory_certificate_code
                (x#certificateCodeId)) ∧ₘ
            verifier.condition
              (sequence ·ₘ index) (x#certificateCodeId))) := by
    exact Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [x#certificateCodeId,
          Sₘ(certificates ·ₘ index)])
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.equal
          (certificates ·ₘ index)
          (CertifiedProof.theory_certificate_code
            (x#certificateCodeId)))
        hCondition)
  simpa [CertifiedProof.theory_certificate_line_condition_with_id,
    CertifiedProof.certificate_payload_bound] using
    Formula.IsDelta0.guarded_exists_closeFreeAt
      certificateCodeId (Sₘ(certificates ·ₘ index))
      hCertificateFresh hBody
      (Formula.FreeMembershipGuard.conj_left
        Formula.FreeMembershipGuard.membership)

/-- 三类行证书的 `Delta0` 组合器。 -/
theorem line_condition_with_ids_delta0_of_parts
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm)
    (certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex : FreeVarId)
    (hCertificateFresh :
      (SetSort.set, certificateCodeId) ∉
        Term.freeSupport (Sₘ(certificates ·ₘ index)))
    (hLogical :
      Formula.IsDelta0 set_levy_bound
        (CertifiedProof.logical_certificate_condition_with_ids
          (sequence ·ₘ index) (x#certificateCodeId)
          logicalCertificateSequenceId logicalFormulaTraceId
          logicalLastIndexId logicalLineIndexId
          logicalCodeTraceId logicalCodeIndexId))
    (hTheory :
      Formula.IsDelta0 set_levy_bound
        (verifier.condition
          (sequence ·ₘ index) (x#certificateCodeId)))
    (hImplicationFresh :
      (SetSort.set, implicationIndex) ∉
        Term.freeSupport index)
    (hPremiseFresh :
      (SetSort.set, premiseIndex) ∉
        Term.freeSupport (x#implicationIndex)) :
    Formula.IsDelta0 set_levy_bound
      (CertifiedProof.line_condition_with_ids
        verifier sequence certificates index
        certificateCodeId
        logicalCertificateSequenceId logicalFormulaTraceId
        logicalLastIndexId logicalLineIndexId
        logicalCodeTraceId logicalCodeIndexId
        implicationIndex premiseIndex) := by
  have hLogicalBody :
      Formula.IsDelta0 set_levy_bound
        ((x#certificateCodeId ∈ₘ
            Sₘ(certificates ·ₘ index)) ∧ₘ
          (((certificates ·ₘ index) ≐ₘ
              CertifiedProof.logical_certificate_code
                (x#certificateCodeId)) ∧ₘ
            CertifiedProof.logical_certificate_condition_with_ids
              (sequence ·ₘ index) (x#certificateCodeId)
              logicalCertificateSequenceId logicalFormulaTraceId
              logicalLastIndexId logicalLineIndexId
              logicalCodeTraceId logicalCodeIndexId)) := by
    exact Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [x#certificateCodeId, Sₘ(certificates ·ₘ index)])
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.equal
          (certificates ·ₘ index)
          (CertifiedProof.logical_certificate_code
            (x#certificateCodeId)))
        hLogical)
  have hLogicalLine :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, certificateCodeId],
          (x#certificateCodeId ∈ₘ
              Sₘ(certificates ·ₘ index)) ∧ₘ
            (((certificates ·ₘ index) ≐ₘ
                CertifiedProof.logical_certificate_code
                  (x#certificateCodeId)) ∧ₘ
              CertifiedProof.logical_certificate_condition_with_ids
                (sequence ·ₘ index) (x#certificateCodeId)
                logicalCertificateSequenceId logicalFormulaTraceId
                logicalLastIndexId logicalLineIndexId
                logicalCodeTraceId logicalCodeIndexId)) := by
    simpa using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        certificateCodeId (Sₘ(certificates ·ₘ index))
        hCertificateFresh hLogicalBody
        (Formula.FreeMembershipGuard.conj_left
          Formula.FreeMembershipGuard.membership)
  have hTheoryLine :=
    theory_certificate_line_condition_with_id_delta0
      verifier sequence certificates index certificateCodeId
      hCertificateFresh hTheory
  have hModusPonensLine :=
    modus_ponens_line_condition_with_ids_delta0
      sequence certificates index implicationIndex premiseIndex
      hImplicationFresh hPremiseFresh
  simpa [CertifiedProof.line_condition_with_ids] using
    Formula.IsDelta0.disj hLogicalLine
      (Formula.IsDelta0.disj hTheoryLine hModusPonensLine)

/-- 对象 verifier 的公式条件与逐行条件合成序列合法性。 -/
theorem sequence_condition_with_ids_delta0_of_parts
    (verifier : ObjectCertificateVerifier)
    (sequence certificates : SetTerm)
    (legalityIndexId certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex : FreeVarId)
    (hLegalityFresh :
      (SetSort.set, legalityIndexId) ∉
        Term.freeSupport (domₘ(sequence)))
    (hFormulaCondition :
      ∀ index,
        Formula.IsDelta0 set_levy_bound
          (verifier.formula_condition
            (sequence ·ₘ index)))
    (hLineCondition :
      ∀ index,
        Formula.IsDelta0 set_levy_bound
          (CertifiedProof.line_condition_with_ids
            verifier sequence certificates index
            certificateCodeId
            logicalCertificateSequenceId logicalFormulaTraceId
            logicalLastIndexId logicalLineIndexId
            logicalCodeTraceId logicalCodeIndexId
            implicationIndex premiseIndex)) :
    Formula.IsDelta0 set_levy_bound
      (CertifiedProof.sequence_condition_with_ids
        verifier sequence certificates
        legalityIndexId certificateCodeId
        logicalCertificateSequenceId logicalFormulaTraceId
        logicalLastIndexId logicalLineIndexId
        logicalCodeTraceId logicalCodeIndexId
        implicationIndex premiseIndex) := by
  let legalityBody : SetFormula :=
    (verifier.formula_condition
        (sequence ·ₘ x#legalityIndexId)) ∧ₘ
      CertifiedProof.line_condition_with_ids
        verifier sequence certificates (x#legalityIndexId)
        certificateCodeId
        logicalCertificateSequenceId logicalFormulaTraceId
        logicalLastIndexId logicalLineIndexId
        logicalCodeTraceId logicalCodeIndexId
        implicationIndex premiseIndex
  have hLegalityBody :
      Formula.IsDelta0 set_levy_bound legalityBody := by
    simpa [legalityBody] using
      Formula.IsDelta0.conj
        (hFormulaCondition (x#legalityIndexId))
        (hLineCondition (x#legalityIndexId))
  let legalityCondition : SetFormula :=
    ∀ₘ[SetSort.set, legalityIndexId],
      (x#legalityIndexId ∈ₘ domₘ(sequence)) ⟶ₘ legalityBody
  have hLegalityCondition :
      Formula.IsDelta0 set_levy_bound legalityCondition := by
    simpa [legalityCondition] using
      Formula.IsDelta0.bounded_forall_closeFreeAt
        legalityIndexId (domₘ(sequence))
        hLegalityFresh hLegalityBody
  have hPrefix :
      Formula.IsDelta0 set_levy_bound
        (((((sequence ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
            (certificates ∈ₘ seq₊_spaceₘ(ωₘ))) ∧ₘ
          (domₘ(sequence) ≐ₘ domₘ(certificates))) ∧ₘ
          (numₘ(0) ∈ₘ domₘ(sequence)))) := by
    exact Formula.IsDelta0.conj
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.rel
            RelationSymbol.membership
            [sequence, seq₊_spaceₘ(FormulaCodeₘ)])
          (Formula.IsDelta0.rel
            RelationSymbol.membership
            [certificates, seq₊_spaceₘ(ωₘ)]))
        (Formula.IsDelta0.equal
          (domₘ(sequence)) (domₘ(certificates))))
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [numₘ(0), domₘ(sequence)])
  simpa [CertifiedProof.sequence_condition_with_ids,
    legalityCondition, legalityBody] using
    Formula.IsDelta0.conj hPrefix hLegalityCondition

/-! ## 原子条件 -/

theorem nat_sequence_code_step_condition_delta0
    (sequence trace index : SetTerm) :
    Formula.IsDelta0 set_levy_bound
      (nat_sequence_code_step_condition
        sequence trace index) := by
  simpa [nat_sequence_code_step_condition] using
    (Formula.IsDelta0.equal
      (trace ·ₘ Sₘ(index))
      (Sₘ(godel_pairₘ(
        ⟨trace ·ₘ index, sequence ·ₘ index⟩ₘ))))

theorem sequence_domain_code_bound_delta0
    (sequence code : SetTerm) :
    Formula.IsDelta0 set_levy_bound
      (sequence_domain_code_bound sequence code) := by
  simpa [sequence_domain_code_bound] using
    (Formula.IsDelta0.rel
      RelationSymbol.membership
      [domₘ(sequence), Sₘ(code)])

theorem proof_code_component_bound_delta0
    (proofCode component : SetTerm) :
    Formula.IsDelta0 set_levy_bound
      (CertifiedProof.proof_code_component_bound
        proofCode component) := by
  simpa [CertifiedProof.proof_code_component_bound] using
    (Formula.IsDelta0.rel
      RelationSymbol.membership
      [component, Sₘ(proofCode)])

theorem nat_sequence_value_code_bound_with_id_delta0
    (sequence code : SetTerm)
    (indexId : FreeVarId)
    (hFresh :
      (SetSort.set, indexId) ∉
        Term.freeSupport (domₘ(sequence))) :
    Formula.IsDelta0 set_levy_bound
      (nat_sequence_value_code_bound_with_id
        sequence code indexId) := by
  have hBody :
      Formula.IsDelta0 set_levy_bound
        ((sequence ·ₘ x#indexId) ∈ₘ code) :=
    Formula.IsDelta0.rel
      RelationSymbol.membership
      [sequence ·ₘ x#indexId, code]
  simpa [nat_sequence_value_code_bound_with_id] using
    Formula.IsDelta0.bounded_forall_closeFreeAt
      indexId (domₘ(sequence)) hFresh hBody

theorem sequence_trace_code_bound_with_id_delta0
    (trace code : SetTerm)
    (indexId : FreeVarId)
    (hFresh :
      (SetSort.set, indexId) ∉
        Term.freeSupport (domₘ(trace))) :
    Formula.IsDelta0 set_levy_bound
      (sequence_trace_code_bound_with_id
        trace code indexId) := by
  have hBody :
      Formula.IsDelta0 set_levy_bound
        ((trace ·ₘ x#indexId) ∈ₘ Sₘ(code)) :=
    Formula.IsDelta0.rel
      RelationSymbol.membership
      [trace ·ₘ x#indexId, Sₘ(code)]
  simpa [sequence_trace_code_bound_with_id] using
    Formula.IsDelta0.bounded_forall_closeFreeAt
      indexId (domₘ(trace)) hFresh hBody

theorem nat_sequence_code_condition_with_ids_delta0
    (sequence code : SetTerm)
    (traceId indexId : FreeVarId)
    (hIndexSequence :
      (SetSort.set, indexId) ∉
        Term.freeSupport (domₘ(sequence)))
    (hIndexTrace :
      (SetSort.set, indexId) ∉
        Term.freeSupport (domₘ(x#traceId))) :
    Formula.IsDelta0 set_levy_bound
      (nat_sequence_code_condition_with_ids
        sequence code traceId indexId) := by
  have hValue :=
    nat_sequence_value_code_bound_with_id_delta0
      sequence code indexId hIndexSequence
  have hTraceBound :=
    sequence_trace_code_bound_with_id_delta0
      (x#traceId) code indexId hIndexTrace
  have hStep :
      Formula.IsDelta0 set_levy_bound
        (nat_sequence_code_step_condition
          sequence (x#traceId) (x#indexId)) :=
    nat_sequence_code_step_condition_delta0
      sequence (x#traceId) (x#indexId)
  let stepForall : SetFormula :=
    ∀ₘ[SetSort.set, indexId],
      (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
        nat_sequence_code_step_condition
          sequence (x#traceId) (x#indexId)
  have hStepForall :
      Formula.IsDelta0 set_levy_bound stepForall := by
    simpa [stepForall] using
      Formula.IsDelta0.bounded_forall_closeFreeAt
        indexId (domₘ(sequence)) hIndexSequence hStep
  let traceBody : SetFormula :=
    ((domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence))) ∧ₘ
        sequence_trace_code_bound_with_id
          (x#traceId) code indexId) ∧ₘ
      (((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
        (stepForall ∧ₘ
          (code ≐ₘ
            (x#traceId ·ₘ domₘ(sequence)))))
  have hTraceLeft :
      Formula.IsDelta0 set_levy_bound
        ((domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence))) ∧ₘ
          sequence_trace_code_bound_with_id
            (x#traceId) code indexId) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.equal
        (domₘ(x#traceId)) (Sₘ(domₘ(sequence))))
      hTraceBound
  have hTraceLast :
      Formula.IsDelta0 set_levy_bound
        ((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) :=
    Formula.IsDelta0.equal
      (x#traceId ·ₘ numₘ(0)) (numₘ(0))
  have hTraceCode :
      Formula.IsDelta0 set_levy_bound
        (code ≐ₘ (x#traceId ·ₘ domₘ(sequence))) :=
    Formula.IsDelta0.equal
      code (x#traceId ·ₘ domₘ(sequence))
  have hTraceStepCode :
      Formula.IsDelta0 set_levy_bound
        (stepForall ∧ₘ
          (code ≐ₘ (x#traceId ·ₘ domₘ(sequence))) ) :=
    Formula.IsDelta0.conj hStepForall hTraceCode
  have hTraceBody :
      Formula.IsDelta0 set_levy_bound traceBody := by
    simpa [traceBody] using
      Formula.IsDelta0.conj
        hTraceLeft
        (Formula.IsDelta0.conj
          hTraceLast hTraceStepCode)
  let traceCondition : SetFormula :=
    ∃ₘ[SetSort.set, traceId],
      (x#traceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ traceBody
  have hTraceFresh :
      (SetSort.set, traceId) ∉
        Term.freeSupport (seq_spaceₘ(ωₘ)) := by
    simp only [Term.freeSupport, Term.freeSupportList]
    exact List.not_mem_nil
  have hTrace :
      Formula.IsDelta0 set_levy_bound traceCondition := by
    simpa [traceCondition] using
      Formula.IsDelta0.bounded_exists_closeFreeAt
        traceId (seq_spaceₘ(ωₘ))
        hTraceFresh hTraceBody
  have hPrefix :
      Formula.IsDelta0 set_levy_bound
        ((((sequence ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
            (code ∈ₘ ωₘ)) ∧ₘ
          sequence_domain_code_bound sequence code) ∧ₘ
          nat_sequence_value_code_bound_with_id
            sequence code indexId) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.rel
            RelationSymbol.membership
            [sequence, seq_spaceₘ(ωₘ)])
          (Formula.IsDelta0.rel
            RelationSymbol.membership
            [code, ωₘ]))
        (sequence_domain_code_bound_delta0
          sequence code))
      hValue
  simpa [nat_sequence_code_condition_with_ids, stepForall,
    traceCondition, traceBody] using
    Formula.IsDelta0.conj hPrefix hTrace

theorem logical_formula_payload_component_condition_with_ids_delta0
    (formulaCode numericCode : SetTerm)
    (traceId indexId : FreeVarId)
    (hFormulaCode :
      Term.BoundFreeAt SetSort.set 0 formulaCode)
    (hIndexFormula :
      (SetSort.set, indexId) ∉
        Term.freeSupport (domₘ(formulaCode)))
    (hIndexTrace :
      (SetSort.set, indexId) ∉
        Term.freeSupport (domₘ(x#traceId))) :
    Formula.IsDelta0 set_levy_bound
      (CertifiedProof.logical_formula_payload_component_condition_with_ids
        formulaCode numericCode traceId indexId) := by
  have hFormulaCodeCondition :
      Formula.IsDelta0 set_levy_bound
        (formula_codeₘ(formulaCode)) :=
    Formula.IsDelta0.rel
      RelationSymbol.isFormulaCode
      [formulaCode]
  have hReplay :
      Formula.IsDelta0 set_levy_bound
        (fs_formula_replay_condition formulaCode) :=
    fs_formula_replay_condition_delta0
      formulaCode hFormulaCode
  have hSequence :
      Formula.IsDelta0 set_levy_bound
        (nat_sequence_code_condition_with_ids
          formulaCode numericCode traceId indexId) :=
    nat_sequence_code_condition_with_ids_delta0
      formulaCode numericCode traceId indexId
      hIndexFormula hIndexTrace
  have hComponent :
      Formula.IsDelta0 set_levy_bound
        ((formula_codeₘ(formulaCode) ∧ₘ
          fs_formula_replay_condition formulaCode)) :=
    Formula.IsDelta0.conj
      hFormulaCodeCondition hReplay
  simpa [CertifiedProof.logical_formula_payload_component_condition_with_ids] using
    Formula.IsDelta0.conj hComponent hSequence

theorem proof_sequence_code_step_condition_with_ids_delta0
    (sequence trace index rowCode : SetTerm)
    (rowTraceId rowIndexId : FreeVarId)
    (hNat :
      Formula.IsDelta0 set_levy_bound
        (nat_sequence_code_condition_with_ids
          (sequence ·ₘ index) rowCode
          rowTraceId rowIndexId)) :
    Formula.IsDelta0 set_levy_bound
      (proof_sequence_code_step_condition_with_ids
        sequence trace index rowCode
        rowTraceId rowIndexId) := by
  exact Formula.IsDelta0.conj
    hNat
    (Formula.IsDelta0.equal
      (trace ·ₘ Sₘ(index))
      (Sₘ(godel_pairₘ(
        ⟨trace ·ₘ index, rowCode⟩ₘ))))

theorem proof_sequence_code_condition_with_ids_delta0
    (sequence code : SetTerm)
    (traceId indexId rowCodeId rowTraceId rowIndexId : FreeVarId)
    (hCodeFresh :
      (SetSort.set, rowCodeId) ∉
        Term.freeSupport code)
    (hIndexSequence :
      (SetSort.set, indexId) ∉
        Term.freeSupport (domₘ(sequence)))
    (hTraceIndex :
      (SetSort.set, indexId) ∉
        Term.freeSupport (domₘ(x#traceId)))
    (hRowNat :
      Formula.IsDelta0 set_levy_bound
        (nat_sequence_code_condition_with_ids
          (sequence ·ₘ x#indexId) (x#rowCodeId)
          rowTraceId rowIndexId)) :
    Formula.IsDelta0 set_levy_bound
      (proof_sequence_code_condition_with_ids
        sequence code traceId indexId
        rowCodeId rowTraceId rowIndexId) := by
  have hRowStep :
      Formula.IsDelta0 set_levy_bound
        (proof_sequence_code_step_condition_with_ids
          sequence (x#traceId) (x#indexId) (x#rowCodeId)
          rowTraceId rowIndexId) :=
    proof_sequence_code_step_condition_with_ids_delta0
      sequence (x#traceId) (x#indexId) (x#rowCodeId)
      rowTraceId rowIndexId hRowNat
  let rowCondition : SetFormula :=
    ∃ₘ[SetSort.set, rowCodeId],
      (x#rowCodeId ∈ₘ code) ∧ₘ
        proof_sequence_code_step_condition_with_ids
          sequence (x#traceId) (x#indexId) (x#rowCodeId)
          rowTraceId rowIndexId
  have hRowCondition :
      Formula.IsDelta0 set_levy_bound rowCondition := by
    simpa [rowCondition] using
      Formula.IsDelta0.bounded_exists_closeFreeAt
        rowCodeId code hCodeFresh hRowStep
  let indexCondition : SetFormula :=
    ∀ₘ[SetSort.set, indexId],
      (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
        rowCondition
  have hIndexCondition :
      Formula.IsDelta0 set_levy_bound indexCondition := by
    simpa [indexCondition] using
      Formula.IsDelta0.bounded_forall_closeFreeAt
        indexId (domₘ(sequence)) hIndexSequence hRowCondition
  let traceBody : SetFormula :=
    ((domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence))) ∧ₘ
        sequence_trace_code_bound_with_id
          (x#traceId) code indexId) ∧ₘ
      (((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
        (indexCondition ∧ₘ
          (code ≐ₘ
            (x#traceId ·ₘ domₘ(sequence)))))
  have hTraceBody :
      Formula.IsDelta0 set_levy_bound traceBody := by
    have hLeft :
        Formula.IsDelta0 set_levy_bound
          ((domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence))) ∧ₘ
            sequence_trace_code_bound_with_id
              (x#traceId) code indexId) :=
      Formula.IsDelta0.conj
        (Formula.IsDelta0.equal
          (domₘ(x#traceId)) (Sₘ(domₘ(sequence))))
        (sequence_trace_code_bound_with_id_delta0
          (x#traceId) code indexId hTraceIndex)
    have hLast :
        Formula.IsDelta0 set_levy_bound
          ((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) :=
      Formula.IsDelta0.equal
        (x#traceId ·ₘ numₘ(0)) (numₘ(0))
    have hCodeEquality :
        Formula.IsDelta0 set_levy_bound
          (code ≐ₘ (x#traceId ·ₘ domₘ(sequence))) :=
      Formula.IsDelta0.equal
        code (x#traceId ·ₘ domₘ(sequence))
    simpa [traceBody] using
      Formula.IsDelta0.conj hLeft
        (Formula.IsDelta0.conj hLast
          (Formula.IsDelta0.conj
            hIndexCondition hCodeEquality))
  let traceCondition : SetFormula :=
    ∃ₘ[SetSort.set, traceId],
      (x#traceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ traceBody
  have hTraceFresh :
      (SetSort.set, traceId) ∉
        Term.freeSupport (seq_spaceₘ(ωₘ)) := by
    simp only [Term.freeSupport, Term.freeSupportList]
    exact List.not_mem_nil
  have hTrace :
      Formula.IsDelta0 set_levy_bound traceCondition := by
    simpa [traceCondition] using
      Formula.IsDelta0.bounded_exists_closeFreeAt
        traceId (seq_spaceₘ(ωₘ))
        hTraceFresh hTraceBody
  let initialCondition : SetFormula :=
    (((sequence ∈ₘ seq_spaceₘ(FormulaCodeₘ)) ∧ₘ
        (code ∈ₘ ωₘ)) ∧ₘ
      sequence_domain_code_bound sequence code)
  have hPrefix :
      Formula.IsDelta0 set_levy_bound initialCondition :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.rel
          RelationSymbol.membership
          [sequence, seq_spaceₘ(FormulaCodeₘ)])
        (Formula.IsDelta0.rel
          RelationSymbol.membership
          [code, ωₘ]))
      (sequence_domain_code_bound_delta0
        sequence code)
  simpa [proof_sequence_code_condition_with_ids,
    initialCondition, indexCondition, rowCondition,
    traceCondition, traceBody] using
    Formula.IsDelta0.conj hPrefix hTrace

theorem proof_sequence_terminal_condition_delta0
    (sequence conclusion : SetTerm)
    (hBound :
      Term.BoundFreeAt SetSort.set 0
        (domₘ(sequence))) :
    Formula.IsDelta0 set_levy_bound
      (proof_sequence_terminal_condition
        sequence conclusion) := by
  have hRest :
      Formula.IsDelta0 set_levy_bound
        ((domₘ(sequence) ≐ₘ Sₘ(bₛ#0)) ∧ₘ
          (conclusion ≐ₘ
            (sequence ·ₘ bₛ#0))) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.equal
        (domₘ(sequence)) (Sₘ(bₛ#0)))
      (Formula.IsDelta0.equal
        conclusion (sequence ·ₘ bₛ#0))
  simpa [proof_sequence_terminal_condition] using
    Formula.IsDelta0.bounded_exists
      (domₘ(sequence))
      (((domₘ(sequence) ≐ₘ Sₘ(bₛ#0)) ∧ₘ
        (conclusion ≐ₘ
          (sequence ·ₘ bₛ#0))))
      hBound
      hRest

theorem code_condition_with_ids_delta0_of_parts
    (verifier : ObjectCertificateVerifier)
    (proofCode conclusion : SetTerm)
    (sequenceId certificatesId formulaCodeId certificateCodeId
      legalityIndexId certificatePayloadId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex
      proofTraceId proofIndexId proofRowCodeId proofRowTraceId proofRowIndexId
      certificateTraceId certificateIndexId : FreeVarId)
    (hSequenceFresh :
      (SetSort.set, sequenceId) ∉
        Term.freeSupport (seq₊_spaceₘ(FormulaCodeₘ)))
    (hCertificatesFresh :
      (SetSort.set, certificatesId) ∉
        Term.freeSupport (seq₊_spaceₘ(ωₘ)))
    (hFormulaCodeFresh :
      (SetSort.set, formulaCodeId) ∉
        Term.freeSupport (Sₘ(proofCode)))
    (hCertificateCodeFresh :
      (SetSort.set, certificateCodeId) ∉
        Term.freeSupport (Sₘ(proofCode)))
    (hSequenceCondition :
      Formula.IsDelta0 set_levy_bound
        (CertifiedProof.sequence_condition_with_ids
          verifier (x#sequenceId) (x#certificatesId)
          legalityIndexId certificatePayloadId
          logicalCertificateSequenceId logicalFormulaTraceId
          logicalLastIndexId logicalLineIndexId
          logicalCodeTraceId logicalCodeIndexId
          implicationIndex premiseIndex))
    (hProofSequenceCondition :
      Formula.IsDelta0 set_levy_bound
        (proof_sequence_code_condition_with_ids
          (x#sequenceId) (x#formulaCodeId)
          proofTraceId proofIndexId proofRowCodeId
          proofRowTraceId proofRowIndexId))
    (hCertificateSequenceCondition :
      Formula.IsDelta0 set_levy_bound
        (nat_sequence_code_condition_with_ids
          (x#certificatesId) (x#certificateCodeId)
          certificateTraceId certificateIndexId))
    (hFormulaBound :
      Formula.IsDelta0 set_levy_bound
        (CertifiedProof.proof_code_component_bound
          proofCode (x#formulaCodeId)))
    (hCertificateBound :
      Formula.IsDelta0 set_levy_bound
        (CertifiedProof.proof_code_component_bound
          proofCode (x#certificateCodeId)))
    (hProofCodeEquality :
      Formula.IsDelta0 set_levy_bound
        (proofCode ≐ₘ
          godel_pairₘ(⟨x#formulaCodeId, x#certificateCodeId⟩ₘ)))
    (hTerminal :
      Formula.IsDelta0 set_levy_bound
        (proof_sequence_terminal_condition
          (x#sequenceId) conclusion)) :
    Formula.IsDelta0 set_levy_bound
      (CertifiedProof.code_condition_with_ids
        verifier proofCode conclusion
        sequenceId certificatesId formulaCodeId certificateCodeId
        legalityIndexId certificatePayloadId
        logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
        logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
        implicationIndex premiseIndex
        proofTraceId proofIndexId proofRowCodeId proofRowTraceId proofRowIndexId
        certificateTraceId certificateIndexId) := by
  let leftFormula : SetFormula :=
    (CertifiedProof.sequence_condition_with_ids
      verifier (x#sequenceId) (x#certificatesId)
      legalityIndexId certificatePayloadId
      logicalCertificateSequenceId logicalFormulaTraceId
      logicalLastIndexId logicalLineIndexId
      logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex) ∧ₘ
      proof_sequence_code_condition_with_ids
        (x#sequenceId) (x#formulaCodeId)
        proofTraceId proofIndexId proofRowCodeId
        proofRowTraceId proofRowIndexId
  let core : SetFormula :=
    (leftFormula ∧ₘ
      nat_sequence_code_condition_with_ids
        (x#certificatesId) (x#certificateCodeId)
        certificateTraceId certificateIndexId) ∧ₘ
       ((CertifiedProof.proof_code_component_bound
           proofCode (x#formulaCodeId) ∧ₘ
         CertifiedProof.proof_code_component_bound
           proofCode (x#certificateCodeId)) ∧ₘ
        ((proofCode ≐ₘ
            godel_pairₘ(⟨x#formulaCodeId, x#certificateCodeId⟩ₘ)) ∧ₘ
           proof_sequence_terminal_condition
             (x#sequenceId) conclusion))
  have hCore :
      Formula.IsDelta0 set_levy_bound core := by
    have hLeft :
        Formula.IsDelta0 set_levy_bound
          leftFormula := by
      simpa [leftFormula] using
        Formula.IsDelta0.conj
          hSequenceCondition hProofSequenceCondition
    have hCertificatePart :
        Formula.IsDelta0 set_levy_bound
          (leftFormula ∧ₘ
            nat_sequence_code_condition_with_ids
              (x#certificatesId) (x#certificateCodeId)
              certificateTraceId certificateIndexId) :=
      Formula.IsDelta0.conj hLeft hCertificateSequenceCondition
    have hBounds :
        Formula.IsDelta0 set_levy_bound
          (CertifiedProof.proof_code_component_bound
              proofCode (x#formulaCodeId) ∧ₘ
            CertifiedProof.proof_code_component_bound
              proofCode (x#certificateCodeId)) :=
      Formula.IsDelta0.conj hFormulaBound hCertificateBound
    have hTail :
        Formula.IsDelta0 set_levy_bound
          ((proofCode ≐ₘ
              godel_pairₘ(⟨x#formulaCodeId, x#certificateCodeId⟩ₘ)) ∧ₘ
            proof_sequence_terminal_condition
              (x#sequenceId) conclusion) :=
      Formula.IsDelta0.conj hProofCodeEquality hTerminal
    simpa [core, leftFormula] using
      Formula.IsDelta0.conj hCertificatePart
        (Formula.IsDelta0.conj hBounds hTail)
  let certificateBody : SetFormula :=
    (CertifiedProof.proof_code_component_bound
        proofCode (x#certificateCodeId)) ∧ₘ core
  have hCertificateBody :
      Formula.IsDelta0 set_levy_bound certificateBody := by
    simpa [certificateBody] using
      Formula.IsDelta0.conj
        hCertificateBound hCore
  have hCertificate :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, certificateCodeId], certificateBody) := by
    simpa [certificateBody] using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        certificateCodeId (Sₘ(proofCode))
        hCertificateCodeFresh hCertificateBody
        (Formula.FreeMembershipGuard.conj_left
          Formula.FreeMembershipGuard.membership)
  let formulaBody : SetFormula :=
    (CertifiedProof.proof_code_component_bound
        proofCode (x#formulaCodeId)) ∧ₘ
      (∃ₘ[SetSort.set, certificateCodeId],
        (CertifiedProof.proof_code_component_bound
            proofCode (x#certificateCodeId)) ∧ₘ core)
  have hFormulaBody :
      Formula.IsDelta0 set_levy_bound formulaBody := by
    simpa [formulaBody] using
      Formula.IsDelta0.conj hFormulaBound hCertificate
  have hFormula :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, formulaCodeId], formulaBody) := by
    simpa [formulaBody] using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        formulaCodeId (Sₘ(proofCode))
        hFormulaCodeFresh hFormulaBody
        (Formula.FreeMembershipGuard.conj_left
          Formula.FreeMembershipGuard.membership)
  let certificatesBody : SetFormula :=
    (x#certificatesId ∈ₘ seq₊_spaceₘ(ωₘ)) ∧ₘ
      (∃ₘ[SetSort.set, formulaCodeId],
        (CertifiedProof.proof_code_component_bound
            proofCode (x#formulaCodeId)) ∧ₘ
          (∃ₘ[SetSort.set, certificateCodeId],
            (CertifiedProof.proof_code_component_bound
                proofCode (x#certificateCodeId)) ∧ₘ core))
  have hCertificatesBody :
      Formula.IsDelta0 set_levy_bound certificatesBody :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [x#certificatesId, seq₊_spaceₘ(ωₘ)])
      hFormula
  have hCertificates :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, certificatesId], certificatesBody) := by
    simpa [certificatesBody] using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        certificatesId (seq₊_spaceₘ(ωₘ))
        hCertificatesFresh hCertificatesBody
        (Formula.FreeMembershipGuard.conj_left
          Formula.FreeMembershipGuard.membership)
  let sequenceBody : SetFormula :=
    (x#sequenceId ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
      (∃ₘ[SetSort.set, certificatesId],
        (x#certificatesId ∈ₘ seq₊_spaceₘ(ωₘ)) ∧ₘ
          (∃ₘ[SetSort.set, formulaCodeId],
            (CertifiedProof.proof_code_component_bound
                proofCode (x#formulaCodeId)) ∧ₘ
              (∃ₘ[SetSort.set, certificateCodeId],
                (CertifiedProof.proof_code_component_bound
                    proofCode (x#certificateCodeId)) ∧ₘ core)))
  have hSequenceBody :
      Formula.IsDelta0 set_levy_bound sequenceBody :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [x#sequenceId, seq₊_spaceₘ(FormulaCodeₘ)])
      hCertificates
  have hSequence :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, sequenceId], sequenceBody) := by
    simpa [sequenceBody] using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        sequenceId (seq₊_spaceₘ(FormulaCodeₘ))
        hSequenceFresh hSequenceBody
        (Formula.FreeMembershipGuard.conj_left
          Formula.FreeMembershipGuard.membership)
  have hPrefix :
      Formula.IsDelta0 set_levy_bound
        ((formula_codeₘ(conclusion) ∧ₘ proofCode ∈ₘ ωₘ)) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.isFormulaCode [conclusion])
      (Formula.IsDelta0.rel
        RelationSymbol.membership [proofCode, ωₘ])
  simpa [CertifiedProof.code_condition_with_ids, core,
    sequenceBody, certificatesBody, formulaBody, certificateBody] using
    Formula.IsDelta0.conj hPrefix hSequence

/-- 固定编号 Rosser 证明条件的 `Delta0` 组合接口。 -/
theorem proof_condition_delta0_of_parts
    (verifier : ObjectCertificateVerifier)
    (proofCode conclusion : SetTerm)
    (base : FreeVarId)
    (hSequenceFresh :
      (SetSort.set, base) ∉
        Term.freeSupport (seq₊_spaceₘ(FormulaCodeₘ)))
    (hCertificatesFresh :
      (SetSort.set, base + 1) ∉
        Term.freeSupport (seq₊_spaceₘ(ωₘ)))
    (hFormulaCodeFresh :
      (SetSort.set, base + 2) ∉
        Term.freeSupport (Sₘ(proofCode)))
    (hCertificateCodeFresh :
      (SetSort.set, base + 3) ∉
        Term.freeSupport (Sₘ(proofCode)))
    (hSequenceCondition :
      Formula.IsDelta0 set_levy_bound
        (CertifiedProof.sequence_condition_with_ids
          verifier (x#base) (x#(base + 1))
          (base + 20) (base + 23)
          (base + 11) (base + 12) (base + 13)
          (base + 14) (base + 15) (base + 16)
          (base + 21) (base + 22)))
    (hProofSequenceCondition :
      Formula.IsDelta0 set_levy_bound
        (proof_sequence_code_condition_with_ids
          (x#base) (x#(base + 2))
          (base + 4) (base + 5) (base + 6)
          (base + 7) (base + 8)))
    (hCertificateSequenceCondition :
      Formula.IsDelta0 set_levy_bound
        (nat_sequence_code_condition_with_ids
          (x#(base + 1)) (x#(base + 3))
          (base + 9) (base + 10)))
    (hFormulaBound :
      Formula.IsDelta0 set_levy_bound
        (CertifiedProof.proof_code_component_bound
          proofCode (x#(base + 2))))
    (hCertificateBound :
      Formula.IsDelta0 set_levy_bound
        (CertifiedProof.proof_code_component_bound
          proofCode (x#(base + 3))))
    (hProofCodeEquality :
      Formula.IsDelta0 set_levy_bound
        (proofCode ≐ₘ
          godel_pairₘ(⟨x#(base + 2), x#(base + 3)⟩ₘ)))
    (hTerminal :
      Formula.IsDelta0 set_levy_bound
        (proof_sequence_terminal_condition
          (x#base) conclusion)) :
    Formula.IsDelta0 set_levy_bound
      (Rosser.proof_condition verifier proofCode conclusion base) := by
  simpa [Rosser.proof_condition] using
    code_condition_with_ids_delta0_of_parts
      verifier proofCode conclusion
      base (base + 1) (base + 2) (base + 3)
      (base + 20) (base + 23)
      (base + 11) (base + 12) (base + 13)
      (base + 14) (base + 15) (base + 16)
      (base + 21) (base + 22)
      (base + 4) (base + 5) (base + 6)
      (base + 7) (base + 8)
      (base + 9) (base + 10)
      hSequenceFresh hCertificatesFresh
      hFormulaCodeFresh hCertificateCodeFresh
      hSequenceCondition hProofSequenceCondition
      hCertificateSequenceCondition hFormulaBound
      hCertificateBound hProofCodeEquality hTerminal

end Delta0Encoding
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
