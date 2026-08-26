import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay

/-!
# checked 逻辑证书的有限完备性

本模块只证明一个有限接口：已有的 Hilbert 逻辑公理能够递归构造出被
`CheckedReplay` 接受的自然数证书。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace Rosser

open Nonlogical.BasicSetTheory
open ProofCode
open GodelQuotation

set_option autoImplicit false

attribute [local simp] fs_logical_base_axiom_check_with

/-- 有限公式列表在任意具名自由变量基址下都能构造出 checked token payload。 -/
theorem fs_named_formula_payload_tokens_exists
    {formulas : List SetFormula}
    (hAdmissible :
      ∀ formula, formula ∈ formulas →
        Formula.Admissible formula) :
    ∃ payloadTokens : List Nat,
      (∀ freeBase,
          fs_named_formula_payload_decode freeBase
              (nat_sequence_code_value payloadTokens) =
            some (formulas.map
              (Formula.hilbertize SetSort.set))) ∧
        fs_formula_payload_decode
            (nat_sequence_code_value payloadTokens) =
          some (formulas.map
            (Formula.hilbertize SetSort.set)) := by
  induction formulas with
  | nil =>
      refine ⟨([] : List Nat), ?_, ?_⟩
      · intro freeBase
        unfold fs_named_formula_payload_decode
        rw [nat_sequence_decode_code_value]
        rfl
      · unfold fs_formula_payload_decode
        rw [nat_sequence_decode_code_value]
        rfl
  | cons head tail ih =>
      have hHead : Formula.Admissible head :=
        hAdmissible head (by simp)
      have hTail :
          ∀ formula, formula ∈ tail →
            Formula.Admissible formula := by
        intro formula hFormula
        exact hAdmissible formula (by simp [hFormula])
      rcases formula_code_witness_exists hHead with
        ⟨headWitness⟩
      rcases ih hTail with
        ⟨tailTokens, hTailNamed, hTailCanonical⟩
      refine ⟨
        nat_sequence_code_value headWitness.tokens :: tailTokens,
        ?_, ?_⟩
      · intro freeBase
        unfold fs_named_formula_payload_decode
        rw [nat_sequence_decode_code_value]
        simp only [List.mapM_cons]
        rw [fs_named_formula_token_code_decode_quote freeBase
          headWitness.h_admissible headWitness.h_tokens]
        have hTailDecode :
            List.mapM
                (fs_named_formula_token_code_decode freeBase)
                tailTokens =
              some (tail.map (Formula.hilbertize SetSort.set)) := by
          unfold fs_named_formula_payload_decode at hTailNamed
          rw [nat_sequence_decode_code_value] at hTailNamed
          exact hTailNamed freeBase
        rw [hTailDecode]
        rfl
      · unfold fs_formula_payload_decode
        rw [nat_sequence_decode_code_value]
        simp only [List.mapM_cons]
        rw [fs_formula_token_code_decode_quote
          headWitness.h_admissible headWitness.h_tokens]
        unfold fs_formula_payload_decode at hTailCanonical
        rw [nat_sequence_decode_code_value] at hTailCanonical
        rw [hTailCanonical]
        rfl

/-- 具名公式 payload 的自然数码存在。 -/
theorem fs_named_formula_payload_code_exists
    {formulas : List SetFormula}
    (hAdmissible :
      ∀ formula, formula ∈ formulas →
        Formula.Admissible formula) :
    ∃ payloadCode : Nat,
      (∀ freeBase,
          fs_named_formula_payload_decode freeBase payloadCode =
            some (formulas.map
              (Formula.hilbertize SetSort.set))) ∧
        fs_formula_payload_decode payloadCode =
          some (formulas.map
            (Formula.hilbertize SetSort.set)) := by
  rcases fs_named_formula_payload_tokens_exists
      hAdmissible with
    ⟨payloadTokens, hNamed, hCanonical⟩
  exact ⟨nat_sequence_code_value payloadTokens,
    hNamed, hCanonical⟩

/-- 公式编码相等时，其 checked 相等判定通过。 -/
theorem fs_formula_code_eq_true_of_eq
    {left right : SetFormula}
    (hEq : left = right) :
    fs_formula_code_eq left right = true := by
  subst right
  simp [fs_formula_code_eq]

/-- 单个公式 token payload 在任意具名自由变量基址下的自然数码存在。 -/
theorem fs_named_formula_token_code_exists
    {formula : SetFormula}
    (hAdmissible : Formula.Admissible formula) :
    ∃ code,
      (∀ freeBase,
          fs_named_formula_token_code_decode freeBase code =
            some (Formula.hilbertize SetSort.set formula)) ∧
        fs_formula_token_code_decode code =
          some (Formula.hilbertize SetSort.set formula) := by
  rcases formula_code_witness_exists hAdmissible with
    ⟨witness⟩
  refine ⟨nat_sequence_code_value witness.tokens, ?_, ?_⟩
  · intro freeBase
    exact fs_named_formula_token_code_decode_quote freeBase
      witness.h_admissible witness.h_tokens
  · exact fs_formula_token_code_decode_quote
      witness.h_admissible witness.h_tokens

/-- 全称 body 用具名自由变量打开后仍保有空 scope admissibility。 -/
theorem fs_set_formula_open_fvar_admissible
    {body : SetFormula} (eigen : FreeVarId)
    (hForall :
      Formula.Admissible
        (Formula.forallE SetSort.set body)) :
    Formula.Admissible
      (Formula.openAt SetSort.set 0
        (Term.var (.fvar SetSort.set eigen)) body) := by
  let fvarTerm : SetTerm :=
    Term.var (.fvar SetSort.set eigen)
  have hFvarTerm :
      Term.Admissible fvarTerm SetSort.set := by
    change
      TermWellSorted fvarTerm SetSort.set ∧
        TermScoped Scope.empty fvarTerm
    have hScopedFvar :
        TermScoped Scope.empty fvarTerm := by
      simpa [fvarTerm] using
        (TermScoped.fvar
          (σ := Nonlogical.BasicSetTheory.signature)
          (ctx := Scope.empty)
          SetSort.set eigen)
    have hSortedFvar :
        TermWellSorted fvarTerm SetSort.set := by
      simpa [fvarTerm] using
        (TermWellSorted.fvar
          (σ := Nonlogical.BasicSetTheory.signature)
          SetSort.set eigen)
    exact ⟨hSortedFvar, hScopedFvar⟩
  have hOpened :=
    Formula.Admissible.forall_openAt
      (body := body) (term := fvarTerm)
      SetSort.set hForall hFvarTerm
  simpa [fvarTerm] using hOpened

/-- 蕴含分配基础公理的 checked code 存在。 -/
theorem fs_logical_base_axiom_check_implication_distribution_exists
    {antecedent middle consequent : SetFormula}
    (hAntecedent : Formula.Admissible antecedent)
    (hMiddle : Formula.Admissible middle)
    (hConsequent : Formula.Admissible consequent) :
    ∃ code,
      (∀ freeBase,
          fs_logical_base_axiom_check
              freeBase
              (Formula.hilbertize SetSort.set
                (Formula.imp
                  (Formula.imp antecedent
                    (Formula.imp middle consequent))
                  (Formula.imp
                    (Formula.imp antecedent middle)
                    (Formula.imp antecedent consequent)))) code =
            true) ∧
        fs_logical_base_axiom_canonical_check
            (Formula.hilbertize SetSort.set
              (Formula.imp
                (Formula.imp antecedent
                  (Formula.imp middle consequent))
                (Formula.imp
                  (Formula.imp antecedent middle)
                  (Formula.imp antecedent consequent)))) code =
          true := by
  rcases fs_named_formula_payload_code_exists
      (formulas := [antecedent, middle, consequent])
      (by
        intro formula hFormula
        simp only [List.mem_cons] at hFormula
        rcases hFormula with hFormula | hFormula | hFormula | hEmpty
        · simpa [hFormula] using hAntecedent
        · simpa [hFormula] using hMiddle
        · simpa [hFormula] using hConsequent
        · cases hEmpty) with
    ⟨payloadCode, hPayloadNamed, hPayloadCanonical⟩
  refine ⟨
    fs_logical_base_certificate_code 0 payloadCode,
    ?_, ?_⟩
  · intro freeBase
    simp [fs_logical_base_axiom_check,
      fs_logical_base_certificate_code,
      godel_unpair_value_pair, hPayloadNamed freeBase,
      fs_formula_code_eq, Formula.hilbertize]
  · simp [fs_logical_base_axiom_canonical_check,
      fs_logical_base_certificate_code,
      godel_unpair_value_pair, hPayloadCanonical,
      fs_formula_code_eq, Formula.hilbertize]

/-- 每个 Hilbert 基础公理都有一个被 checked verifier 接受的 code。 -/
theorem fs_logical_base_axiom_check_exists
    {formula : SetFormula}
    (hAxiom : HilbertBaseAxiom formula)
    (hAdmissible : Formula.Admissible formula) :
    ∃ code,
      (∀ freeBase,
          fs_logical_base_axiom_check
              freeBase
              (Formula.hilbertize SetSort.set formula) code =
            true) ∧
        fs_logical_base_axiom_canonical_check
            (Formula.hilbertize SetSort.set formula) code =
          true := by
  cases hAxiom with
  | implication_distribution antecedent middle consequent =>
      have hAntecedent :
          Formula.Admissible antecedent :=
        Formula.Admissible.imp_left
          (Formula.Admissible.imp_left hAdmissible)
      have hMiddleConsequent :
          Formula.Admissible
            (Formula.imp middle consequent) :=
        Formula.Admissible.imp_right
          (Formula.Admissible.imp_left hAdmissible)
      have hMiddle :
          Formula.Admissible middle :=
        Formula.Admissible.imp_left hMiddleConsequent
      have hConsequent :
          Formula.Admissible consequent :=
        Formula.Admissible.imp_right hMiddleConsequent
      exact fs_logical_base_axiom_check_implication_distribution_exists
        hAntecedent hMiddle hConsequent
  | self_implication body =>
      have hBody :
          Formula.Admissible body :=
        Formula.Admissible.imp_left hAdmissible
      rcases fs_named_formula_payload_code_exists
          (formulas := [body])
          (by
            intro formula hFormula
            simp only [List.mem_cons] at hFormula
            rcases hFormula with hFormula | hEmpty
            · simpa [hFormula] using hBody
            · cases hEmpty) with
        ⟨payloadCode, hPayloadNamed, hPayloadCanonical⟩
      refine ⟨
        fs_logical_base_certificate_code 1 payloadCode,
        ?_, ?_⟩
      · intro freeBase
        simp [fs_logical_base_axiom_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, hPayloadNamed freeBase,
          fs_formula_code_eq, Formula.hilbertize]
      · simp [fs_logical_base_axiom_canonical_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, hPayloadCanonical,
          fs_formula_code_eq, Formula.hilbertize]
  | weakening body extra =>
      have hBody :
          Formula.Admissible body :=
        Formula.Admissible.imp_left hAdmissible
      have hExtra :
          Formula.Admissible extra :=
        Formula.Admissible.imp_left
          (Formula.Admissible.imp_right hAdmissible)
      rcases fs_named_formula_payload_code_exists
          (formulas := [body, extra])
          (by
            intro formula hFormula
            simp only [List.mem_cons] at hFormula
            rcases hFormula with hFormula | hFormula | hEmpty
            · simpa [hFormula] using hBody
            · simpa [hFormula] using hExtra
            · cases hEmpty) with
        ⟨payloadCode, hPayloadNamed, hPayloadCanonical⟩
      refine ⟨
        fs_logical_base_certificate_code 2 payloadCode,
        ?_, ?_⟩
      · intro freeBase
        simp [fs_logical_base_axiom_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, hPayloadNamed freeBase,
          fs_formula_code_eq, Formula.hilbertize]
      · simp [fs_logical_base_axiom_canonical_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, hPayloadCanonical,
          fs_formula_code_eq, Formula.hilbertize]
  | contradiction body conclusion =>
      have hBody :
          Formula.Admissible body :=
        Formula.Admissible.imp_left hAdmissible
      have hConclusion :
          Formula.Admissible conclusion :=
        Formula.Admissible.imp_right
          (Formula.Admissible.imp_right hAdmissible)
      rcases fs_named_formula_payload_code_exists
          (formulas := [body, conclusion])
          (by
            intro formula hFormula
            simp only [List.mem_cons] at hFormula
            rcases hFormula with hFormula | hFormula | hEmpty
            · simpa [hFormula] using hBody
            · simpa [hFormula] using hConclusion
            · cases hEmpty) with
        ⟨payloadCode, hPayloadNamed, hPayloadCanonical⟩
      refine ⟨
        fs_logical_base_certificate_code 3 payloadCode,
        ?_, ?_⟩
      · intro freeBase
        simp [fs_logical_base_axiom_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, hPayloadNamed freeBase,
          fs_formula_code_eq, Formula.hilbertize]
      · simp [fs_logical_base_axiom_canonical_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, hPayloadCanonical,
          fs_formula_code_eq, Formula.hilbertize]
  | classical body =>
      have hBody :
          Formula.Admissible body :=
        Formula.Admissible.imp_right hAdmissible
      rcases fs_named_formula_payload_code_exists
          (formulas := [body])
          (by
            intro formula hFormula
            simp only [List.mem_cons] at hFormula
            rcases hFormula with hFormula | hEmpty
            · simpa [hFormula] using hBody
            · cases hEmpty) with
        ⟨payloadCode, hPayloadNamed, hPayloadCanonical⟩
      refine ⟨
        fs_logical_base_certificate_code 4 payloadCode,
        ?_, ?_⟩
      · intro freeBase
        simp [fs_logical_base_axiom_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, hPayloadNamed freeBase,
          fs_formula_code_eq, Formula.hilbertize]
      · simp [fs_logical_base_axiom_canonical_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, hPayloadCanonical,
          fs_formula_code_eq, Formula.hilbertize]
  | explosion body conclusion =>
      have hBody :
          Formula.Admissible body :=
        Formula.Admissible.neg_body
          (Formula.Admissible.imp_left hAdmissible)
      have hConclusion :
          Formula.Admissible conclusion :=
        Formula.Admissible.imp_right
          (Formula.Admissible.imp_right hAdmissible)
      rcases fs_named_formula_payload_code_exists
          (formulas := [body, conclusion])
          (by
            intro formula hFormula
            simp only [List.mem_cons] at hFormula
            rcases hFormula with hFormula | hFormula | hEmpty
            · simpa [hFormula] using hBody
            · simpa [hFormula] using hConclusion
            · cases hEmpty) with
        ⟨payloadCode, hPayloadNamed, hPayloadCanonical⟩
      refine ⟨
        fs_logical_base_certificate_code 5 payloadCode,
        ?_, ?_⟩
      · intro freeBase
        simp [fs_logical_base_axiom_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, hPayloadNamed freeBase,
          fs_formula_code_eq, Formula.hilbertize]
      · simp [fs_logical_base_axiom_canonical_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, hPayloadCanonical,
          fs_formula_code_eq, Formula.hilbertize]
  | case_analysis body conclusion =>
      have hPositive :
          Formula.Admissible
            (Formula.imp body conclusion) :=
        Formula.Admissible.imp_left hAdmissible
      have hBody :
          Formula.Admissible body :=
        Formula.Admissible.imp_left hPositive
      have hConclusion :
          Formula.Admissible conclusion :=
        Formula.Admissible.imp_right hPositive
      rcases fs_named_formula_payload_code_exists
          (formulas := [body, conclusion])
          (by
            intro formula hFormula
            simp only [List.mem_cons] at hFormula
            rcases hFormula with hFormula | hFormula | hEmpty
            · simpa [hFormula] using hBody
            · simpa [hFormula] using hConclusion
            · cases hEmpty) with
        ⟨payloadCode, hPayloadNamed, hPayloadCanonical⟩
      refine ⟨
        fs_logical_base_certificate_code 6 payloadCode,
        ?_, ?_⟩
      · intro freeBase
        simp [fs_logical_base_axiom_check,
          fs_logical_base_certificate_code, godel_unpair_value_pair,
          hPayloadNamed freeBase, fs_formula_code_eq,
          Formula.hilbertize]
      · simp [fs_logical_base_axiom_canonical_check,
          fs_logical_base_certificate_code, godel_unpair_value_pair,
          hPayloadCanonical, fs_formula_code_eq,
          Formula.hilbertize]
  | forall_specialization sort body term hTerm hClosed =>
      cases sort
      have hForall :
          Formula.Admissible
            (Formula.forallE SetSort.set body) :=
        Formula.Admissible.imp_left hAdmissible
      let eigen :=
        FreshVariable.fresh_id SetSort.set [body]
      have hFresh :
          (SetSort.set, eigen) ∉ Formula.freeSupport body :=
        FreshVariable.fresh_id_not_mem_m
          (sort := SetSort.set) (formulas := [body])
          (formula := body) (by simp)
      have hOpened :
          Formula.Admissible
            (Formula.openAt SetSort.set 0
              (Term.var (.fvar SetSort.set eigen)) body) :=
        by
          let fvarTerm : SetTerm :=
            Term.var (.fvar SetSort.set eigen)
          have hFvarTerm :
              Term.Admissible fvarTerm SetSort.set :=
            by
              change
                TermWellSorted fvarTerm SetSort.set ∧
                  TermScoped Scope.empty fvarTerm
              have hScopedFvar :
                  TermScoped Scope.empty fvarTerm := by
                simpa [fvarTerm] using
                  (TermScoped.fvar
                    (σ := Nonlogical.BasicSetTheory.signature)
                    (ctx := Scope.empty)
                    SetSort.set eigen)
              have hSortedFvar :
                  TermWellSorted fvarTerm SetSort.set := by
                simpa [fvarTerm] using
                  (TermWellSorted.fvar
                    (σ := Nonlogical.BasicSetTheory.signature)
                    SetSort.set eigen)
              exact
                ⟨hSortedFvar,
                  hScopedFvar⟩
          have hOpened' :=
            Formula.Admissible.forall_openAt
              (body := body) (term := fvarTerm)
              SetSort.set hForall hFvarTerm
          simpa [fvarTerm] using hOpened'
      have hTermAdmissible :
          Term.Admissible term SetSort.set :=
        ⟨hTerm, hClosed⟩
      have hCarrier :
          Formula.Admissible (Formula.equal term term) :=
        Formula.Admissible.equal
          hTermAdmissible hTermAdmissible
      rcases formula_code_witness_exists hOpened with
        ⟨bodyWitness⟩
      rcases formula_code_witness_exists hCarrier with
        ⟨carrierWitness⟩
      let bodyCode :=
        nat_sequence_code_value bodyWitness.tokens
      let carrierCode :=
        nat_sequence_code_value carrierWitness.tokens
      let payload :=
        godel_pair_value eigen
          (godel_pair_value bodyCode carrierCode)
      have hBodyDecode :
          ∀ freeBase,
            fs_named_formula_token_code_decode freeBase bodyCode =
              some
                (Formula.hilbertize SetSort.set
                  (Formula.openAt SetSort.set 0
                    (Term.var (.fvar SetSort.set eigen)) body)) := by
        intro freeBase
        exact fs_named_formula_token_code_decode_quote freeBase
          bodyWitness.h_admissible bodyWitness.h_tokens
      have hBodyCanonical :
          fs_formula_token_code_decode bodyCode =
            some
              (Formula.hilbertize SetSort.set
                (Formula.openAt SetSort.set 0
                  (Term.var (.fvar SetSort.set eigen)) body)) :=
        fs_formula_token_code_decode_quote
          bodyWitness.h_admissible bodyWitness.h_tokens
      have hCarrierDecode :
          ∀ freeBase,
            fs_named_formula_token_code_decode freeBase carrierCode =
              some
                (Formula.hilbertize SetSort.set
                  (Formula.equal term term)) := by
        intro freeBase
        exact fs_named_formula_token_code_decode_quote freeBase
          carrierWitness.h_admissible carrierWitness.h_tokens
      have hCarrierCanonical :
          fs_formula_token_code_decode carrierCode =
            some
              (Formula.hilbertize SetSort.set
                (Formula.equal term term)) :=
        fs_formula_token_code_decode_quote
          carrierWitness.h_admissible carrierWitness.h_tokens
      have hCarrierTerm :
          fs_term_carrier_decode
              (Formula.hilbertize SetSort.set
                (Formula.equal term term)) =
            some term := by
        simp [fs_term_carrier_decode, Formula.hilbertize,
          fs_term_code_eq]
      have hFreshHilbert :
          (SetSort.set, eigen) ∉
            Formula.freeSupport
              (Formula.hilbertize SetSort.set body) := by
        intro hMember
        exact hFresh
          ((Formula.mem_freeSupport_hilbertize_iff
            SetSort.set (SetSort.set, eigen) body).mp hMember)
      have hClosedBody :
          Formula.closeFreeAt SetSort.set eigen 0
              (Formula.hilbertize SetSort.set
                (Formula.openAt SetSort.set 0
                  (Term.var (.fvar SetSort.set eigen)) body)) =
            Formula.hilbertize SetSort.set body := by
        rw [Formula.hilbertize_openAt]
        exact Formula.closeFreeAt_openAt
          SetSort.set eigen 0
            (Formula.hilbertize SetSort.set body)
          hFreshHilbert
      have hFormulaEq :
          Formula.hilbertize SetSort.set
              (Formula.imp
                (Formula.forallE SetSort.set body)
                (Formula.openAt SetSort.set 0 term body)) =
            Formula.imp
              (Formula.forallE SetSort.set
                (Formula.closeFreeAt SetSort.set eigen 0
                  (Formula.hilbertize SetSort.set
                    (Formula.openAt SetSort.set 0
                      (Term.var (.fvar SetSort.set eigen)) body))))
              (Formula.openAt SetSort.set 0 term
                (Formula.closeFreeAt SetSort.set eigen 0
                  (Formula.hilbertize SetSort.set
                    (Formula.openAt SetSort.set 0
                      (Term.var (.fvar SetSort.set eigen)) body)))) := by
        simp only [Formula.hilbertize]
        rw [Formula.hilbertize_openAt]
        rw [hClosedBody]
      have hSortedCheck :
          Term.check_wellSorted SetSort.set term = true :=
        Term.check_wellSorted_complete hTerm
      have hScopedCheck :
          Term.check_scoped Scope.empty term = true :=
        Term.check_scoped_complete hClosed
      refine ⟨
        fs_logical_base_certificate_code 7 payload,
        ?_, ?_⟩
      · intro freeBase
        simp [fs_logical_base_axiom_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, payload, bodyCode,
          carrierCode, hBodyDecode freeBase,
          hCarrierDecode freeBase,
          hCarrierTerm, hSortedCheck, hScopedCheck,
          fs_formula_code_eq_true_of_eq hFormulaEq]
      · simp [fs_logical_base_axiom_canonical_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, payload, bodyCode,
          carrierCode, hBodyCanonical, hCarrierCanonical,
          hCarrierTerm, hSortedCheck, hScopedCheck,
          fs_formula_code_eq_true_of_eq hFormulaEq]
  | forall_distribution sort antecedent consequent =>
      cases sort
      have hForallImp :
          Formula.Admissible
            (Formula.forallE SetSort.set
              (Formula.imp antecedent consequent)) :=
        Formula.Admissible.imp_left hAdmissible
      have hForallAntecedent :
          Formula.Admissible
            (Formula.forallE SetSort.set antecedent) :=
        Formula.Admissible.imp_left
          (Formula.Admissible.imp_right hAdmissible)
      have hForallConsequent :
          Formula.Admissible
            (Formula.forallE SetSort.set consequent) :=
        Formula.Admissible.imp_right
          (Formula.Admissible.imp_right hAdmissible)
      let eigen :=
        FreshVariable.fresh_id SetSort.set
          [antecedent, consequent]
      have hFreshAntecedent :
          (SetSort.set, eigen) ∉
            Formula.freeSupport antecedent :=
        FreshVariable.fresh_id_not_mem_m
          (sort := SetSort.set)
          (formulas := [antecedent, consequent])
          (formula := antecedent) (by simp)
      have hFreshConsequent :
          (SetSort.set, eigen) ∉
            Formula.freeSupport consequent :=
        FreshVariable.fresh_id_not_mem_m
          (sort := SetSort.set)
          (formulas := [antecedent, consequent])
          (formula := consequent) (by simp)
      have hOpenedAntecedent :
          Formula.Admissible
            (Formula.openAt SetSort.set 0
              (Term.var (.fvar SetSort.set eigen)) antecedent) :=
        fs_set_formula_open_fvar_admissible eigen
          hForallAntecedent
      have hOpenedConsequent :
          Formula.Admissible
            (Formula.openAt SetSort.set 0
              (Term.var (.fvar SetSort.set eigen)) consequent) :=
        fs_set_formula_open_fvar_admissible eigen
          hForallConsequent
      rcases formula_code_witness_exists hOpenedAntecedent with
        ⟨antecedentWitness⟩
      rcases formula_code_witness_exists hOpenedConsequent with
        ⟨consequentWitness⟩
      let antecedentCode :=
        nat_sequence_code_value antecedentWitness.tokens
      let consequentCode :=
        nat_sequence_code_value consequentWitness.tokens
      let payload :=
        godel_pair_value eigen
          (godel_pair_value antecedentCode consequentCode)
      have hAntecedentDecode :
          ∀ freeBase,
            fs_named_formula_token_code_decode
                freeBase antecedentCode =
              some
                (Formula.hilbertize SetSort.set
                  (Formula.openAt SetSort.set 0
                    (Term.var (.fvar SetSort.set eigen))
                    antecedent)) := by
        intro freeBase
        exact fs_named_formula_token_code_decode_quote freeBase
          antecedentWitness.h_admissible
          antecedentWitness.h_tokens
      have hAntecedentCanonical :
          fs_formula_token_code_decode antecedentCode =
            some
              (Formula.hilbertize SetSort.set
                (Formula.openAt SetSort.set 0
                  (Term.var (.fvar SetSort.set eigen))
                  antecedent)) :=
        fs_formula_token_code_decode_quote
          antecedentWitness.h_admissible
          antecedentWitness.h_tokens
      have hConsequentDecode :
          ∀ freeBase,
            fs_named_formula_token_code_decode
                freeBase consequentCode =
              some
                (Formula.hilbertize SetSort.set
                  (Formula.openAt SetSort.set 0
                    (Term.var (.fvar SetSort.set eigen))
                    consequent)) := by
        intro freeBase
        exact fs_named_formula_token_code_decode_quote freeBase
          consequentWitness.h_admissible
          consequentWitness.h_tokens
      have hConsequentCanonical :
          fs_formula_token_code_decode consequentCode =
            some
              (Formula.hilbertize SetSort.set
                (Formula.openAt SetSort.set 0
                  (Term.var (.fvar SetSort.set eigen))
                  consequent)) :=
        fs_formula_token_code_decode_quote
          consequentWitness.h_admissible
          consequentWitness.h_tokens
      have hFreshHilbertAntecedent :
          (SetSort.set, eigen) ∉
            Formula.freeSupport
              (Formula.hilbertize SetSort.set antecedent) := by
        intro hMember
        exact hFreshAntecedent
          ((Formula.mem_freeSupport_hilbertize_iff
            SetSort.set (SetSort.set, eigen) antecedent).mp hMember)
      have hFreshHilbertConsequent :
          (SetSort.set, eigen) ∉
            Formula.freeSupport
              (Formula.hilbertize SetSort.set consequent) := by
        intro hMember
        exact hFreshConsequent
          ((Formula.mem_freeSupport_hilbertize_iff
            SetSort.set (SetSort.set, eigen) consequent).mp hMember)
      have hClosedAntecedent :
          Formula.closeFreeAt SetSort.set eigen 0
              (Formula.hilbertize SetSort.set
                (Formula.openAt SetSort.set 0
                  (Term.var (.fvar SetSort.set eigen))
                  antecedent)) =
            Formula.hilbertize SetSort.set antecedent := by
        rw [Formula.hilbertize_openAt]
        exact Formula.closeFreeAt_openAt
          SetSort.set eigen 0
            (Formula.hilbertize SetSort.set antecedent)
          hFreshHilbertAntecedent
      have hClosedConsequent :
          Formula.closeFreeAt SetSort.set eigen 0
              (Formula.hilbertize SetSort.set
                (Formula.openAt SetSort.set 0
                  (Term.var (.fvar SetSort.set eigen))
                  consequent)) =
            Formula.hilbertize SetSort.set consequent := by
        rw [Formula.hilbertize_openAt]
        exact Formula.closeFreeAt_openAt
          SetSort.set eigen 0
            (Formula.hilbertize SetSort.set consequent)
          hFreshHilbertConsequent
      have hFormulaEq :
          Formula.hilbertize SetSort.set
              (Formula.imp
                (Formula.forallE SetSort.set
                  (Formula.imp antecedent consequent))
                (Formula.imp
                  (Formula.forallE SetSort.set antecedent)
                  (Formula.forallE SetSort.set consequent))) =
            Formula.imp
              (Formula.forallE SetSort.set
                (Formula.imp
                  (Formula.closeFreeAt SetSort.set eigen 0
                    (Formula.hilbertize SetSort.set
                      (Formula.openAt SetSort.set 0
                        (Term.var (.fvar SetSort.set eigen))
                        antecedent)))
                  (Formula.closeFreeAt SetSort.set eigen 0
                    (Formula.hilbertize SetSort.set
                      (Formula.openAt SetSort.set 0
                        (Term.var (.fvar SetSort.set eigen))
                        consequent)))))
              (Formula.imp
                (Formula.forallE SetSort.set
                  (Formula.closeFreeAt SetSort.set eigen 0
                    (Formula.hilbertize SetSort.set
                      (Formula.openAt SetSort.set 0
                        (Term.var (.fvar SetSort.set eigen))
                        antecedent))))
                (Formula.forallE SetSort.set
                  (Formula.closeFreeAt SetSort.set eigen 0
                    (Formula.hilbertize SetSort.set
                      (Formula.openAt SetSort.set 0
                        (Term.var (.fvar SetSort.set eigen))
                        consequent))))) := by
        simp only [Formula.hilbertize]
        rw [hClosedAntecedent, hClosedConsequent]
      refine ⟨
        fs_logical_base_certificate_code 8 payload,
        ?_, ?_⟩
      · intro freeBase
        simp [fs_logical_base_axiom_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, payload, antecedentCode,
          consequentCode, hAntecedentDecode freeBase,
          hConsequentDecode freeBase,
          fs_formula_code_eq_true_of_eq hFormulaEq]
      · simp [fs_logical_base_axiom_canonical_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, payload, antecedentCode,
          consequentCode, hAntecedentCanonical,
          hConsequentCanonical,
          fs_formula_code_eq_true_of_eq hFormulaEq]
  | vacuous_forall sort eigen body hFresh =>
      cases sort
      have hBody :
          Formula.Admissible body :=
        Formula.Admissible.imp_left hAdmissible
      rcases fs_named_formula_token_code_exists
          hBody with
        ⟨bodyCode, hBodyDecode, hBodyCanonical⟩
      have hFreshHilbert :
          (SetSort.set, eigen) ∉
            Formula.freeSupport
              (Formula.hilbertize SetSort.set body) := by
        intro hMember
        exact hFresh
          ((Formula.mem_freeSupport_hilbertize_iff
            SetSort.set (SetSort.set, eigen) body).mp hMember)
      have hFreshCheck :
          decide
              ((SetSort.set, eigen) ∉
                Formula.freeSupport
                  (Formula.hilbertize SetSort.set body)) =
            true := by
        simp [hFreshHilbert]
      have hFormulaEq :
          Formula.hilbertize SetSort.set
              (Formula.imp body
                (Formula.forallE SetSort.set
                  (Formula.closeFreeAt
                    SetSort.set eigen 0 body))) =
            Formula.imp
              (Formula.hilbertize SetSort.set body)
              (Formula.forallE SetSort.set
                (Formula.closeFreeAt
                  SetSort.set eigen 0
                  (Formula.hilbertize SetSort.set body))) := by
        simp only [Formula.hilbertize]
        rw [Formula.hilbertize_closeFreeAt]
      refine ⟨
        fs_logical_base_certificate_code 9
          (godel_pair_value eigen bodyCode),
        ?_, ?_⟩
      · intro freeBase
        simp [fs_logical_base_axiom_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, hBodyDecode freeBase,
          hFreshCheck,
          fs_formula_code_eq_true_of_eq hFormulaEq]
      · simp [fs_logical_base_axiom_canonical_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, hBodyCanonical,
          hFreshCheck,
          fs_formula_code_eq_true_of_eq hFormulaEq]
  | equality_substitution sort leftId rightId body =>
      cases sort
      have hBody :
          Formula.Admissible body :=
        Formula.Admissible.imp_left
          (Formula.Admissible.imp_right hAdmissible)
      rcases fs_named_formula_token_code_exists
          hBody with
        ⟨bodyCode, hBodyDecode, hBodyCanonical⟩
      have hFormulaEq :
          Formula.hilbertize SetSort.set
              (Formula.imp
                (Formula.equal
                  (Term.var (.fvar SetSort.set leftId))
                  (Term.var (.fvar SetSort.set rightId)))
                (Formula.imp body
                  (Formula.substituteFree SetSort.set leftId
                    (Term.var (.fvar SetSort.set rightId))
                    body))) =
            Formula.imp
              (Formula.equal
                (Term.var (.fvar SetSort.set leftId))
                (Term.var (.fvar SetSort.set rightId)))
              (Formula.imp
                (Formula.hilbertize SetSort.set body)
                (Formula.substituteFree SetSort.set leftId
                  (Term.var (.fvar SetSort.set rightId))
                  (Formula.hilbertize SetSort.set body))) := by
        simp [Formula.hilbertize,
          Formula.hilbertize_substituteFree]
      refine ⟨
        fs_logical_base_certificate_code 10
          (nat_sequence_code_value
            [leftId, rightId, bodyCode]),
        ?_, ?_⟩
      · intro freeBase
        simp [fs_logical_base_axiom_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, nat_sequence_decode_code_value,
          hBodyDecode freeBase,
          fs_formula_code_eq_true_of_eq hFormulaEq]
      · simp [fs_logical_base_axiom_canonical_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, nat_sequence_decode_code_value,
          hBodyCanonical,
          fs_formula_code_eq_true_of_eq hFormulaEq]
  | equality_reflexivity sort id =>
      cases sort
      refine ⟨
        fs_logical_base_certificate_code 11 id,
        ?_, ?_⟩
      · intro freeBase
        simp [fs_logical_base_axiom_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, fs_formula_code_eq,
          Formula.hilbertize]
      · simp [fs_logical_base_axiom_canonical_check,
          fs_logical_base_certificate_code,
          godel_unpair_value_pair, fs_formula_code_eq,
          Formula.hilbertize]

/-- 每个 Hilbert 逻辑公理都有一条被 checked verifier 接受的 code 行序列。 -/
theorem fs_logical_axiom_check_rows_exists
    {formula : SetFormula}
    (hAxiom : HilbertLogicalAxiom formula)
    (hAdmissible : Formula.Admissible formula) :
    ∃ codes,
      (∀ freeBase,
          fs_logical_axiom_check_rows freeBase codes
              (Formula.hilbertize SetSort.set formula) =
            true) ∧
        fs_logical_axiom_canonical_check_rows codes
            (Formula.hilbertize SetSort.set formula) =
          true := by
  induction hAxiom with
  | base hBase =>
      rcases fs_logical_base_axiom_check_exists
          hBase hAdmissible with
        ⟨baseCode, hBaseNamed, hBaseCanonical⟩
      exact ⟨([baseCode] : List Nat), hBaseNamed, hBaseCanonical⟩
  | @forall_closure formula sort eigen hAxiom ih =>
      cases sort
      have hInnerAdmissible :
          Formula.Admissible formula := by
        have hOpened :=
          fs_set_formula_open_fvar_admissible eigen hAdmissible
        simpa [Formula.openAt_closeFreeAt] using hOpened
      rcases ih hInnerAdmissible with
        ⟨restCodes, hRestNamed, hRestCanonical⟩
      have hFreshRaw :
          (SetSort.set, eigen) ∉
            Formula.freeSupport
              (Formula.closeFreeAt
                SetSort.set eigen 0 formula) :=
        Formula.not_mem_freeSupport_closeFreeAt
          SetSort.set eigen 0 formula
      have hFreshHilbert :
          (SetSort.set, eigen) ∉
            Formula.freeSupport
              (Formula.hilbertize SetSort.set
                (Formula.closeFreeAt
                  SetSort.set eigen 0 formula)) := by
        intro hMember
        exact hFreshRaw
          ((Formula.mem_freeSupport_hilbertize_iff
            SetSort.set (SetSort.set, eigen)
            (Formula.closeFreeAt
              SetSort.set eigen 0 formula)).mp hMember)
      have hOpenedReconstruct :
          Formula.openAt SetSort.set 0
              (Term.var (.fvar SetSort.set eigen))
              (Formula.hilbertize SetSort.set
                (Formula.closeFreeAt
                  SetSort.set eigen 0 formula)) =
            Formula.hilbertize SetSort.set formula := by
        rw [Formula.hilbertize_closeFreeAt]
        exact Formula.openAt_closeFreeAt
          SetSort.set eigen 0
            (Formula.hilbertize SetSort.set formula)
      have hFreshCheck :
          decide
              ((SetSort.set, eigen) ∉
                Formula.freeSupport
                  (Formula.hilbertize SetSort.set
                    (Formula.closeFreeAt
                      SetSort.set eigen 0 formula))) =
            true := by
        simp [hFreshHilbert]
      have hRestNonempty : restCodes ≠ [] := by
        intro hNil
        subst restCodes
        have hFalse := hRestCanonical
        simp [fs_logical_axiom_canonical_check_rows,
          fs_logical_axiom_check_rows_with] at hFalse
      refine ⟨eigen :: restCodes, ?_, ?_⟩
      · intro freeBase
        have hRestTarget :
            fs_logical_axiom_check_rows freeBase restCodes
                (Formula.openAt SetSort.set 0
                  (Term.var (.fvar SetSort.set eigen))
                  (Formula.hilbertize SetSort.set
                    (Formula.closeFreeAt
                      SetSort.set eigen 0 formula))) =
              true := by
          rw [hOpenedReconstruct]
          exact hRestNamed freeBase
        change
          fs_logical_axiom_check_rows_with
              (fs_logical_base_axiom_check freeBase)
              (eigen :: restCodes)
              (Formula.forallE SetSort.set
                (Formula.hilbertize SetSort.set
                  (Formula.closeFreeAt
                    SetSort.set eigen 0 formula))) =
            true
        rw [fs_logical_axiom_check_rows_with.eq_3
          (fs_logical_base_axiom_check freeBase)
          eigen restCodes SetSort.set
          (Formula.hilbertize SetSort.set
            (Formula.closeFreeAt SetSort.set eigen 0 formula))
          hRestNonempty]
        exact Bool.and_eq_true_iff.mpr
          ⟨hFreshCheck, hRestTarget⟩
      · have hRestTarget :
            fs_logical_axiom_canonical_check_rows restCodes
                (Formula.openAt SetSort.set 0
                  (Term.var (.fvar SetSort.set eigen))
                  (Formula.hilbertize SetSort.set
                    (Formula.closeFreeAt
                      SetSort.set eigen 0 formula))) =
              true := by
          rw [hOpenedReconstruct]
          exact hRestCanonical
        change
          fs_logical_axiom_check_rows_with
              fs_logical_base_axiom_canonical_check
              (eigen :: restCodes)
              (Formula.forallE SetSort.set
                (Formula.hilbertize SetSort.set
                  (Formula.closeFreeAt
                    SetSort.set eigen 0 formula))) =
            true
        rw [fs_logical_axiom_check_rows_with.eq_3
          fs_logical_base_axiom_canonical_check
          eigen restCodes SetSort.set
          (Formula.hilbertize SetSort.set
            (Formula.closeFreeAt SetSort.set eigen 0 formula))
          hRestNonempty]
        exact Bool.and_eq_true_iff.mpr
          ⟨hFreshCheck, hRestTarget⟩

/-- Hilbert 化理论对公式 Hilbert 化封闭。 -/
theorem fs_hilbertized_theory_closed
    {base : SetTheory} {formula : SetFormula}
    (hTheory :
      Theory.hilbertize SetSort.set base formula) :
    Theory.hilbertize SetSort.set base
      (Formula.hilbertize SetSort.set formula) := by
  rcases hTheory with ⟨source, hSource, rfl⟩
  exact ⟨source, hSource, by simp⟩

/-- 有限 Hilbert 证明中的每一行都携带可用性证明。 -/
theorem fs_hilbert_proof_admissible_of_mem
    {theory : SetTheory}
    {proof : List SetFormula}
    (hProof : HilbertProof theory proof)
    {formula : SetFormula}
    (hFormula : formula ∈ proof) :
    Formula.Admissible formula := by
  induction hProof generalizing formula with
  | nil =>
      simp at hFormula
  | @logical_axiom proof formula hProof hAxiom hAdmissible ih =>
      simp only [List.mem_append, List.mem_singleton] at hFormula
      rcases hFormula with hFormula | rfl
      · exact ih hFormula
      · exact hAdmissible
  | @theory_axiom proof formula hProof hTheory hAdmissible ih =>
      simp only [List.mem_append, List.mem_singleton] at hFormula
      rcases hFormula with hFormula | rfl
      · exact ih hFormula
      · exact hAdmissible
  | @modus_ponens proof antecedent consequent hProof hEarlier ih =>
      simp only [List.mem_append, List.mem_singleton] at hFormula
      rcases hFormula with hFormula | rfl
      · exact ih hFormula
      · have hPremises := hEarlier.mem
        exact Formula.Admissible.imp_right (ih hPremises.2)

/-- Hilbert 证明逐行提升为 checked replay 所消费的 Hilbert 化轨迹。 -/
theorem fs_checked_trace_exists_of_hilbert_proof
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    (hTheoryHilbertClosed :
      ∀ formula, theory formula →
        theory (Formula.hilbertize SetSort.set formula))
    {proof : List SetFormula}
    (hProof : HilbertProof theory proof) :
    ∃ certificates,
      (∀ freeBase,
          FSCheckedHilbertTrace enumeration
            (fs_logical_axiom_check freeBase)
            (proof.map (Formula.hilbertize SetSort.set))
            certificates) ∧
        FSCheckedHilbertTrace enumeration
          fs_logical_axiom_canonical_check
          (proof.map (Formula.hilbertize SetSort.set))
          certificates := by
  induction hProof with
  | nil =>
      exact ⟨([] : List HilbertLineCertificateCode),
        (by
          intro freeBase
          exact FSCheckedHilbertTrace.nil),
        FSCheckedHilbertTrace.nil⟩
  | @logical_axiom proof formula hProof hAxiom hAdmissible ih =>
      rcases ih with
        ⟨certificates, hTraceNamed, hTraceCanonical⟩
      rcases fs_logical_axiom_check_rows_exists
          hAxiom hAdmissible with
        ⟨rows, hRowsNamed, hRowsCanonical⟩
      let certificateCode :=
        nat_sequence_code_value rows
      let nextCertificates : List HilbertLineCertificateCode :=
        certificates ++
          [HilbertLineCertificateCode.logical certificateCode]
      refine ⟨nextCertificates, ?_, ?_⟩
      · intro freeBase
        have hCodeCheck :
            fs_logical_axiom_check freeBase certificateCode
                (Formula.hilbertize SetSort.set formula) = true := by
          unfold fs_logical_axiom_check
          dsimp [certificateCode]
          rw [nat_sequence_decode_code_value]
          exact hRowsNamed freeBase
        simpa [List.map_append] using
          (FSCheckedHilbertTrace.logical
            (hTraceNamed freeBase) certificateCode hCodeCheck
            (Formula.Admissible.hilbertize hAdmissible))
      · have hCodeCheck :
            fs_logical_axiom_canonical_check certificateCode
                (Formula.hilbertize SetSort.set formula) = true := by
          unfold fs_logical_axiom_canonical_check
          dsimp [certificateCode]
          rw [nat_sequence_decode_code_value]
          exact hRowsCanonical
        simpa [List.map_append] using
          (FSCheckedHilbertTrace.logical
            hTraceCanonical certificateCode hCodeCheck
            (Formula.Admissible.hilbertize hAdmissible))
  | @theory_axiom proof formula hProof hTheory hAdmissible ih =>
      rcases ih with
        ⟨certificates, hTraceNamed, hTraceCanonical⟩
      have hHilbertTheory :
          theory
            (Formula.hilbertize SetSort.set formula) :=
        hTheoryHilbertClosed formula hTheory
      rcases enumeration.certificate_complete
          hHilbertTheory with
        ⟨certificateCode, hCertificate⟩
      let nextCertificates : List HilbertLineCertificateCode :=
        certificates ++
          [HilbertLineCertificateCode.theory certificateCode]
      refine ⟨nextCertificates, ?_, ?_⟩
      · intro freeBase
        simpa [List.map_append] using
          (FSCheckedHilbertTrace.theory
            (hTraceNamed freeBase) certificateCode hCertificate
            (Formula.Admissible.hilbertize hAdmissible))
      · simpa [List.map_append] using
          (FSCheckedHilbertTrace.theory
            hTraceCanonical certificateCode hCertificate
            (Formula.Admissible.hilbertize hAdmissible))
  | @modus_ponens proof antecedent consequent hProof hEarlier ih =>
      rcases ih with
        ⟨certificates, hTraceNamed, hTraceCanonical⟩
      rcases hEarlier with
        ⟨initial, middle, suffix, hProofShape⟩
      let premiseIndex := initial.length
      let implicationIndex :=
        (initial ++ antecedent :: middle).length
      have hPremise :
          (proof.map (Formula.hilbertize SetSort.set))[premiseIndex]? =
            some
              (Formula.hilbertize SetSort.set antecedent) := by
        rw [hProofShape]
        simp [premiseIndex]
      have hImplication :
          (proof.map (Formula.hilbertize SetSort.set))[implicationIndex]? =
            some
              (Formula.imp
                (Formula.hilbertize SetSort.set antecedent)
                (Formula.hilbertize SetSort.set consequent)) := by
        rw [hProofShape]
        simp [implicationIndex, List.append_assoc, Formula.hilbertize]
      have hPremiseEarlier :
          premiseIndex < implicationIndex := by
        simp [premiseIndex, implicationIndex]
      let nextCertificates : List HilbertLineCertificateCode :=
        certificates ++
          [HilbertLineCertificateCode.modusPonens
            implicationIndex premiseIndex]
      refine ⟨nextCertificates, ?_, ?_⟩
      · intro freeBase
        simpa [List.map_append] using
          (FSCheckedHilbertTrace.modusPonens
            (hTraceNamed freeBase) implicationIndex premiseIndex
            hImplication hPremise hPremiseEarlier)
      · simpa [List.map_append] using
          (FSCheckedHilbertTrace.modusPonens
            hTraceCanonical implicationIndex premiseIndex
            hImplication hPremise hPremiseEarlier)

/-- 有限 Hilbert 证明的规范 proof code 必然通过 checked replay。 -/
theorem fs_replay_code_exists_of_hilbert_proof
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    (hTheoryHilbertClosed :
      ∀ formula, theory formula →
        theory (Formula.hilbertize SetSort.set formula))
    {proof : List SetFormula}
    (hProof : HilbertProof theory proof) :
    ∃ certificates state,
      fs_replay_code enumeration
          (certified_hilbert_proof_code_value
            certified_row_tokens proof certificates) =
        some state ∧
      state.proof =
        proof.map (Formula.hilbertize SetSort.set) ∧
      state.certificates = certificates := by
  rcases fs_checked_trace_exists_of_hilbert_proof
      enumeration hTheoryHilbertClosed hProof with
    ⟨certificates, hTraceNamed, hTraceCanonical⟩
  let proofCode :=
    certified_hilbert_proof_code_value
      certified_row_tokens proof certificates
  have hAdmissible :
      ∀ formula, formula ∈ proof →
        Formula.Admissible formula := by
    intro formula hFormula
    exact fs_hilbert_proof_admissible_of_mem hProof hFormula
  rcases fs_formula_rows_decode_payload_quote
      (certified_hilbert_proof_code_value
        certified_row_tokens proof certificates)
      hAdmissible with
    ⟨rows, hDecoded, hRows⟩
  rcases fs_replay_rows_of_checked_trace
      enumeration proofCode (hTraceNamed proofCode) hRows with
    ⟨state, hReplay, hProofState, hCertificateState⟩
  refine ⟨certificates, state, ?_, hProofState,
    hCertificateState⟩
  unfold fs_replay_code
  rw [fs_certified_proof_code_decode_value]
  simpa [fs_replay_raw_rows_eq_of_decode
      enumeration
      (certified_hilbert_proof_code_value
        certified_row_tokens proof certificates)
      (fs_replay_nil enumeration
        (certified_hilbert_proof_code_value
          certified_row_tokens proof certificates))
      certificates hDecoded] using hReplay

/-- 只把真实 checked replay 成功的 proof code 视为 Hilbert 化证明码。 -/
def fs_checked_hilbertized_proof_code_for
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    (proofCode : Nat)
    (formula : SetFormula) : Prop :=
  ∃ state,
    fs_replay_code enumeration proofCode = some state ∧
    Formula.hilbertize SetSort.set formula ∈ state.proof

/-- 精确把 proof code 的末行固定为目标公式的 checked replay 关系。 -/
def fs_terminal_checked_hilbertized_proof_code_for
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    (proofCode : Nat)
    (formula : SetFormula) : Prop :=
  ∃ state,
    fs_replay_code enumeration proofCode = some state ∧
    state.proof.getLast? =
      some (Formula.hilbertize SetSort.set formula)

/-- checked proof code 的可靠性只使用 replay 状态中的轨迹。 -/
theorem fs_checked_hilbertized_proof_code_for_sound
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    {proofCode : Nat}
    {formula : SetFormula}
    (hCode :
      fs_checked_hilbertized_proof_code_for
        enumeration proofCode formula) :
    HilbertDerives theory
      (Formula.hilbertize SetSort.set formula) := by
  rcases hCode with
    ⟨state, _hReplay, hFormula⟩
  exact fs_replay_code_sound enumeration hFormula

/-- 精确末行 checked replay 的可靠性。 -/
theorem fs_terminal_checked_hilbertized_proof_code_for_sound
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    {proofCode : Nat}
    {formula : SetFormula}
    (hCode :
      fs_terminal_checked_hilbertized_proof_code_for
        enumeration proofCode formula) :
    HilbertDerives theory
      (Formula.hilbertize SetSort.set formula) := by
  rcases hCode with
    ⟨state, _hReplay, hLast⟩
  rcases List.getLast?_eq_some_iff.mp hLast with
    ⟨initial, hProof⟩
  apply fs_replay_code_sound enumeration
  rw [hProof]
  simp

/-- 每个 Hilbert 可推导公式都有一个真实 checked replay proof code。 -/
theorem fs_checked_hilbertized_proof_code_for_exists_of_derives
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    (hTheoryHilbertClosed :
      ∀ formula, theory formula →
        theory (Formula.hilbertize SetSort.set formula))
    {formula : SetFormula}
    (hDerives : HilbertDerives theory formula) :
    ∃ proofCode,
      fs_checked_hilbertized_proof_code_for
        enumeration proofCode formula := by
  rcases HilbertProof.exists_finite hDerives with
    ⟨initial, hProof⟩
  rcases fs_replay_code_exists_of_hilbert_proof
      enumeration hTheoryHilbertClosed hProof with
    ⟨certificates, state, hReplay, hStateProof,
      _hStateCertificates⟩
  refine ⟨certified_hilbert_proof_code_value
      certified_row_tokens (initial ++ [formula]) certificates,
    state, hReplay, ?_⟩
  rw [hStateProof]
  simp

/-- 每个 Hilbert 可推导公式都有一个目标恰为末行的 checked proof code。 -/
theorem fs_terminal_checked_hilbertized_proof_code_for_exists_of_derives
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    (hTheoryHilbertClosed :
      ∀ formula, theory formula →
        theory (Formula.hilbertize SetSort.set formula))
    {formula : SetFormula}
    (hDerives : HilbertDerives theory formula) :
    ∃ proofCode,
      fs_terminal_checked_hilbertized_proof_code_for
        enumeration proofCode formula := by
  rcases HilbertProof.exists_finite hDerives with
    ⟨initial, hProof⟩
  rcases fs_replay_code_exists_of_hilbert_proof
      enumeration hTheoryHilbertClosed hProof with
    ⟨certificates, state, hReplay, hStateProof,
      _hStateCertificates⟩
  refine ⟨certified_hilbert_proof_code_value
      certified_row_tokens (initial ++ [formula]) certificates,
    state, hReplay, ?_⟩
  rw [hStateProof]
  simp [List.getLast?_append]

end Rosser
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
