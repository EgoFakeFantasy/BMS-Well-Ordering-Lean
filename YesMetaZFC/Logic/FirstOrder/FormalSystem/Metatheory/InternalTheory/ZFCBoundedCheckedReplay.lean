import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedLineReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectVerifierSubstitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCertifiedProofReplay

/-!
# ZFC 有界 checked replay

本模块把外部有限 checked 轨迹接到对象层证明码条件的两个边界接口：

* 证明序列的末行由具体的外部列表分解闭合；
* checked 轨迹按有限位置提供统一的逐行分类。

逻辑公理行的 specialization 与任意全称闭包回放仍由后续对象层模块提供，
这里不把它们伪装成已经完成的 verifier 结论。
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
open Rosser

set_option autoImplicit false

/-! ## 证明序列末行 -/

/-- 具体证明列表的最后一行在对象层证明码序列中可被回放。 -/
theorem ProofT.terminal_of_last
    {T : SetTheory}
    (hStandardSequence :
      ∀ {candidate : SetFormula},
        standard_sequence_semantics_theory candidate → T candidate)
    (hQuotation :
      ∀ {candidate : SetFormula},
        godel_quotation_theory candidate → T candidate)
    {proof initial : List SetFormula}
    {formula : SetFormula}
    (hProof : proof = initial ++ [formula])
    (hRows :
      ∀ row, row ∈ proof →
        Formula.Admissible row) :
    Derives T [] (
      proof_sequence_terminal_condition
        (standard_sequence
          (proof.map (fun row =>
            standard_token_sequence (certified_row_tokens row))))
        (fs_zfc_formula_code_term formula)) := by
  let elements : List SetTerm :=
    proof.map (fun row =>
      standard_token_sequence (certified_row_tokens row))
  let sequence : SetTerm :=
    standard_sequence elements
  have hFormula : Formula.Admissible formula := by
    apply hRows formula
    rw [hProof]
    simp
  have hElements :
      ∀ element, element ∈ elements →
        Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨row, hRow, rfl⟩
    exact standard_token_sequence_admissible
      (certified_row_tokens row)
  have hElementsClosed :
      ∀ element, element ∈ elements →
        Term.freeSupport element = [] := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨row, hRow, rfl⟩
    exact standard_token_sequence_freeSupport_nil
      (certified_row_tokens row)
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    simpa [sequence, elements] using
      seq_admissible_m 0 hElements
  have hSequenceClosed :
      Term.freeSupport sequence = [] := by
    simpa [sequence, elements] using
      seq_support_nil_m 0 hElementsClosed
  have hCodeClosed :
      Term.freeSupport (fs_zfc_formula_code_term formula) = [] := by
    unfold fs_zfc_formula_code_term
    cases hQuote : GodelQuotation.Numbered.quote? formula with
    | none =>
        simp [standard_token_sequence_freeSupport_nil]
    | some code =>
        exact
          (GodelQuotation.Numbered.quote?_code_boundary hQuote).2
  have hDomain :
      Derives T [] (
        domₘ(sequence) ≐ₘ numₘ(proof.length)) := by
    have hDomainStd :
        Derives standard_sequence_semantics_theory [] (
          domₘ(standard_sequence elements) ≐ₘ
            numₘ(elements.length)) :=
      standard_sequence_domain_eq_numeral_length
        hElements
        (stdseq_element_fresh_of_support_nil hElementsClosed 0)
        (stdseq_element_fresh_of_support_nil hElementsClosed 1)
    simpa [sequence, elements] using
      FirstOrder.Derives.theory_weaken
        (fun _ hCandidate => hStandardSequence hCandidate)
        hDomainStd
  have hDomainLast :
      Derives T [] (
        domₘ(sequence) ≐ₘ Sₘ(numₘ(initial.length))) := by
    simpa [hProof, sequence, elements, List.length_append,
      finite_numeral_term, successor_term] using hDomain
  have hLast :
      proof[initial.length]? = some formula := by
    rw [hProof]
    simp
  have hApplication :
      Derives T [] (
        (sequence ·ₘ numₘ(initial.length)) ≐ₘ
          standard_token_sequence (certified_row_tokens formula)) := by
    simpa [sequence, elements] using
      ProofT.ZFC.formula_sequence_apply
        hStandardSequence
        hLast
  have hFormulaCode :
      Derives T [] (
        fs_zfc_formula_code_term formula ≐ₘ
          standard_token_sequence (certified_row_tokens formula)) :=
    ProofT.ZFC.formula_code_eq_tokens
      hQuotation
      hFormula
  have hApplicationSymm :
      Derives T [] (
        standard_token_sequence (certified_row_tokens formula) ≐ₘ
          sequence ·ₘ numₘ(initial.length)) :=
    Metatheory.Derives.equality_symm
      hApplication
  have hConclusionAtLast :
      Derives T [] (
        fs_zfc_formula_code_term formula ≐ₘ
          sequence ·ₘ numₘ(initial.length)) :=
    Metatheory.Derives.equality_trans
      hFormulaCode hApplicationSymm
  have hSelfMember :
      Derives T [] (
        numₘ(initial.length) ∈ₘ
          Sₘ(numₘ(initial.length))) :=
    FirstOrder.Derives.theory_weaken
      (fun _ hCandidate => hStandardSequence hCandidate)
      (by
        simpa [finite_numeral_term, successor_term] using
          standard_sequence_finite_numeral_mem_of_lt
            initial.length (initial.length + 1)
            (Nat.lt_succ_self initial.length))
  have hLastMember :
      Derives T [] (
        numₘ(initial.length) ∈ₘ domₘ(sequence)) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(initial.length))
        (domₘ(sequence))
        (Sₘ(numₘ(initial.length)))
        (finite_numeral_term_admissible initial.length)
        (domain_term_admissible sequence hSequence)
        (successor_term_admissible
          (numₘ(initial.length))
          (finite_numeral_term_admissible initial.length))
        hDomainLast)
      hSelfMember
  let body : SetFormula :=
    (x#0 ∈ₘ domₘ(sequence)) ∧ₘ
      ((domₘ(sequence) ≐ₘ Sₘ(x#0)) ∧ₘ
        (fs_zfc_formula_code_term formula ≐ₘ
          (sequence ·ₘ x#0)))
  have hSequenceSubstitute :
      Term.substituteFree SetSort.set 0
          (numₘ(initial.length)) sequence =
        sequence :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 0 (numₘ(initial.length)) sequence (by
        rw [hSequenceClosed]
        exact List.not_mem_nil)
  have hCodeSubstitute :
      Term.substituteFree SetSort.set 0
          (numₘ(initial.length))
          (fs_zfc_formula_code_term formula) =
        fs_zfc_formula_code_term formula :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 0 (numₘ(initial.length))
        (fs_zfc_formula_code_term formula) (by
          rw [hCodeClosed]
          exact List.not_mem_nil)
  have hSequenceClose :
      Term.closeFreeAt SetSort.set 0 0 sequence =
        sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 0 0 sequence hSequence.2 (by
        rw [hSequenceClosed]
        exact List.not_mem_nil)
  have hCodeClose :
      Term.closeFreeAt SetSort.set 0 0
          (fs_zfc_formula_code_term formula) =
        fs_zfc_formula_code_term formula :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 0 0 (fs_zfc_formula_code_term formula)
      (fs_zfc_formula_code_term_admissible formula).2 (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hWitness :
      Derives T [] (
        Formula.substituteFree SetSort.set 0
          (numₘ(initial.length)) body) := by
    have hDomainWitness :
        Derives T [] (
          domₘ(sequence) ≐ₘ
            Sₘ(numₘ(initial.length))) :=
      hDomainLast
    have hConclusionWitness :
        Derives T [] (
          fs_zfc_formula_code_term formula ≐ₘ
            (sequence ·ₘ numₘ(initial.length))) :=
      hConclusionAtLast
    simpa [body, Formula.substituteFree,
      Term.substituteFree, set_variable,
      hSequenceSubstitute, hCodeSubstitute] using
      FirstOrder.Derives.conjIntro
        hLastMember
        (FirstOrder.Derives.conjIntro
          hDomainWitness hConclusionWitness)
  have hExists :
      Derives T [] (
        ∃ₘ[SetSort.set],
          (bₛ#0 ∈ₘ domₘ(sequence)) ∧ₘ
            ((domₘ(sequence) ≐ₘ Sₘ(bₛ#0)) ∧ₘ
              (fs_zfc_formula_code_term formula ≐ₘ
                (sequence ·ₘ bₛ#0)))) := by
    have hDerived :=
      FirstOrder.Derives.exists_intro_substituted
        (T := T)
        (Γ := [])
        (sort := SetSort.set)
        0 hWitness
    simpa [body, Formula.closeFreeAt,
      Term.closeFreeAt, set_variable,
      set_bound_variable, hSequenceClose,
      hCodeClose] using hDerived
  simpa [sequence, elements, proof_sequence_terminal_condition] using
    hExists

/-! ## checked trace 的有限位置分类 -/

/-- checked trace 的公式序列与证书序列始终保持同长度。 -/
theorem fs_checked_trace_certificates_length
    {theory : SetTheory}
    {enumeration : ProofCode.HilbertTheoryEnumeration theory}
    {proof : List SetFormula}
    {certificates : List HilbertLineCertificateCode}
    (hTrace :
      FSCheckedHilbertTrace enumeration
        fs_logical_axiom_canonical_check
        proof certificates) :
    certificates.length = proof.length := by
  induction hTrace with
  | nil =>
      rfl
  | @logical proof formula certificates previous certificateCode
      hCheck hAdmissible ih =>
      simp [List.length_append, ih]
  | theory previous certificateCode hCertificate hAdmissible ih =>
      simp [List.length_append, ih]
  | modusPonens previous implicationIndex premiseIndex
      hImplication hPremise hPremiseEarlier ih =>
      simp [List.length_append, ih]

/-- checked trace 中的每一行都保留公式的 admissibility。 -/
theorem fs_checked_trace_admissible_of_mem
    {theory : SetTheory}
    {enumeration : ProofCode.HilbertTheoryEnumeration theory}
    {proof : List SetFormula}
    {certificates : List HilbertLineCertificateCode}
    (hTrace :
      FSCheckedHilbertTrace enumeration
        fs_logical_axiom_canonical_check
        proof certificates)
    {formula : SetFormula}
    (hFormula : formula ∈ proof) :
    Formula.Admissible formula := by
  induction hTrace generalizing formula with
  | nil =>
      simp at hFormula
  | @logical proof formula certificates previous certificateCode
      hCheck hAdmissible ih =>
      simp only [List.mem_append, List.mem_singleton] at hFormula
      rcases hFormula with hFormula | rfl
      · exact ih hFormula
      · exact hAdmissible
  | theory previous certificateCode hCertificate hAdmissible ih =>
      simp only [List.mem_append, List.mem_singleton] at hFormula
      rcases hFormula with hFormula | rfl
      · exact ih hFormula
      · exact hAdmissible
  | modusPonens previous implicationIndex premiseIndex
      hImplication hPremise hPremiseEarlier ih =>
      simp only [List.mem_append, List.mem_singleton] at hFormula
      rcases hFormula with hFormula | rfl
      · exact ih hFormula
      · rcases List.getElem?_eq_some_iff.mp hImplication with
          ⟨hImplicationIndex, hImplicationGet⟩
        have hImplicationMem :=
          List.getElem_mem hImplicationIndex
        rw [hImplicationGet] at hImplicationMem
        exact Formula.Admissible.imp_right
          (ih hImplicationMem)

/-- checked trace 某一行的三类外部回放数据。 -/
def FSCheckedLineClassification
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    (proof : List SetFormula)
    (index : Nat)
    (formula : SetFormula)
    (certificate : HilbertLineCertificateCode) : Prop :=
  (∃ certificateCode,
      certificate = HilbertLineCertificateCode.logical certificateCode ∧
      fs_logical_axiom_canonical_check
        certificateCode formula = true ∧
      Formula.Admissible formula) ∨
    (∃ certificateCode,
      certificate = HilbertLineCertificateCode.theory certificateCode ∧
      enumeration.certificate_verifier certificateCode formula = true ∧
      Formula.Admissible formula) ∨
    (∃ implicationIndex premiseIndex antecedent consequent,
      certificate =
        HilbertLineCertificateCode.modusPonens
          implicationIndex premiseIndex ∧
      proof[implicationIndex]? =
        some (Formula.imp antecedent consequent) ∧
      proof[premiseIndex]? = some antecedent ∧
      premiseIndex < implicationIndex ∧
      implicationIndex < index ∧
      formula = consequent)

/-- 将已有的行分类沿证明列表末尾追加运输。 -/
theorem fs_checked_line_classification_append
    {theory : SetTheory}
    {enumeration : ProofCode.HilbertTheoryEnumeration theory}
    {proof : List SetFormula}
    {index : Nat}
    {formula newFormula : SetFormula}
    {certificate : HilbertLineCertificateCode}
    (hClassification :
      FSCheckedLineClassification enumeration
        proof index formula certificate) :
    FSCheckedLineClassification enumeration
      (proof ++ [newFormula]) index formula certificate := by
  rcases hClassification with hLogical | hTheory | hModus
  · exact Or.inl hLogical
  · exact Or.inr (Or.inl hTheory)
  · rcases hModus with
      ⟨implicationIndex, premiseIndex, antecedent, consequent,
        hCertificate, hImplication, hPremise,
        hPremiseEarlier, hImplicationEarlier, hFormula⟩
    have hImplicationIndex :
        implicationIndex < proof.length :=
      (List.getElem?_eq_some_iff.mp hImplication).1
    have hPremiseIndex :
        premiseIndex < proof.length :=
      (List.getElem?_eq_some_iff.mp hPremise).1
    have hImplication' :
        (proof ++ [newFormula])[implicationIndex]? =
          some (Formula.imp antecedent consequent) := by
      rw [List.getElem?_append_left hImplicationIndex]
      exact hImplication
    have hPremise' :
        (proof ++ [newFormula])[premiseIndex]? =
          some antecedent := by
      rw [List.getElem?_append_left hPremiseIndex]
      exact hPremise
    exact Or.inr (Or.inr
      ⟨implicationIndex, premiseIndex, antecedent, consequent,
        hCertificate, hImplication', hPremise',
        hPremiseEarlier, hImplicationEarlier, hFormula⟩)

/-- checked trace 在任意有限位置都能解出公式、证书及其行类型。 -/
theorem fs_checked_trace_line_classification_of_index
    {theory : SetTheory}
    {enumeration : ProofCode.HilbertTheoryEnumeration theory}
    {proof : List SetFormula}
    {certificates : List HilbertLineCertificateCode}
    (hTrace :
      FSCheckedHilbertTrace enumeration
        fs_logical_axiom_canonical_check
        proof certificates)
    (index : Nat)
    (hIndex : index < proof.length) :
    ∃ formula certificate,
      proof[index]? = some formula ∧
      certificates[index]? = some certificate ∧
      FSCheckedLineClassification enumeration
        proof index formula certificate := by
  induction hTrace generalizing index with
  | nil =>
      simp at hIndex
  | @logical proof formula certificates previous certificateCode
      hCheck hAdmissible ih =>
      have hSplit :
          index < proof.length ∨ index = proof.length := by
        simp only [List.length_append, List.length_singleton] at hIndex
        omega
      rcases hSplit with hOld | rfl
      · rcases ih index hOld with
          ⟨oldFormula, oldCertificate, hFormula, hCertificate,
            hClassification⟩
        have hFormula' :
            (proof ++ [formula])[index]? = some oldFormula := by
          rw [List.getElem?_append_left hOld]
          exact hFormula
        have hCertificateIndex :
            index < certificates.length := by
          simpa [fs_checked_trace_certificates_length previous] using hOld
        have hCertificate' :
            (certificates ++
                [HilbertLineCertificateCode.logical certificateCode])[index]? =
              some oldCertificate := by
          rw [List.getElem?_append_left hCertificateIndex]
          exact hCertificate
        exact ⟨oldFormula, oldCertificate, hFormula', hCertificate',
          fs_checked_line_classification_append hClassification⟩
      · have hFormula' :
            (proof ++ [formula])[proof.length]? =
              some formula := by
          simp
        have hCertificateLength :=
          fs_checked_trace_certificates_length previous
        have hCertificate' :
            (certificates ++
                [HilbertLineCertificateCode.logical certificateCode])[
                  proof.length]? =
              some (HilbertLineCertificateCode.logical certificateCode) := by
          rw [← hCertificateLength]
          simp
        exact ⟨formula,
          HilbertLineCertificateCode.logical certificateCode,
          hFormula', hCertificate',
          Or.inl ⟨certificateCode, rfl, hCheck, hAdmissible⟩⟩
  | @theory proof formula certificates previous certificateCode
      hCertificate hAdmissible ih =>
      have hSplit :
          index < proof.length ∨ index = proof.length := by
        simp only [List.length_append, List.length_singleton] at hIndex
        omega
      rcases hSplit with hOld | rfl
      · rcases ih index hOld with
          ⟨oldFormula, oldCertificate, hFormula, hCertificate',
            hClassification⟩
        have hFormula' :
            (proof ++ [formula])[index]? = some oldFormula := by
          rw [List.getElem?_append_left hOld]
          exact hFormula
        have hCertificateIndex :
            index < certificates.length := by
          simpa [fs_checked_trace_certificates_length previous] using hOld
        have hCertificate'' :
            (certificates ++
                [HilbertLineCertificateCode.theory certificateCode])[index]? =
              some oldCertificate := by
          rw [List.getElem?_append_left hCertificateIndex]
          exact hCertificate'
        exact ⟨oldFormula, oldCertificate, hFormula', hCertificate'',
          fs_checked_line_classification_append hClassification⟩
      · have hFormula' :
            (proof ++ [formula])[proof.length]? =
              some formula := by
          simp
        have hCertificateLength :=
          fs_checked_trace_certificates_length previous
        have hCertificate' :
            (certificates ++
                [HilbertLineCertificateCode.theory certificateCode])[
                  proof.length]? =
              some (HilbertLineCertificateCode.theory certificateCode) := by
          rw [← hCertificateLength]
          simp
        exact ⟨formula,
          HilbertLineCertificateCode.theory certificateCode,
          hFormula', hCertificate',
          Or.inr (Or.inl
            ⟨certificateCode, rfl, hCertificate, hAdmissible⟩)⟩
  | @modusPonens proof antecedent consequent certificates previous
      implicationIndex premiseIndex
      hImplication hPremise hPremiseEarlier ih =>
      have hSplit :
          index < proof.length ∨ index = proof.length := by
        simp only [List.length_append, List.length_singleton] at hIndex
        omega
      rcases hSplit with hOld | rfl
      · rcases ih index hOld with
          ⟨formula, certificate, hFormula, hCertificate, hClassification⟩
        have hFormula' :
            (proof ++ [consequent])[index]? = some formula := by
          rw [List.getElem?_append_left hOld]
          exact hFormula
        have hCertificateIndex :
            index < certificates.length := by
          simpa [fs_checked_trace_certificates_length previous] using hOld
        have hCertificate' :
            (certificates ++
                [HilbertLineCertificateCode.modusPonens
                  implicationIndex premiseIndex])[index]? =
              some certificate := by
          rw [List.getElem?_append_left hCertificateIndex]
          exact hCertificate
        exact ⟨formula, certificate, hFormula', hCertificate',
          fs_checked_line_classification_append hClassification⟩
      · have hFormula' :
            (proof ++ [consequent])[proof.length]? =
              some consequent := by
          simp
        have hCertificateLength :=
          fs_checked_trace_certificates_length previous
        have hCertificate' :
            (certificates ++
                [HilbertLineCertificateCode.modusPonens
                  implicationIndex premiseIndex])[proof.length]? =
              some
                (HilbertLineCertificateCode.modusPonens
                  implicationIndex premiseIndex) := by
          rw [← hCertificateLength]
          simp
        have hImplicationIndex :
            implicationIndex < proof.length :=
          (List.getElem?_eq_some_iff.mp hImplication).1
        have hPremiseIndex :
            premiseIndex < proof.length :=
          (List.getElem?_eq_some_iff.mp hPremise).1
        have hImplication' :
            (proof ++ [consequent])[implicationIndex]? =
              some (Formula.imp antecedent consequent) := by
          rw [List.getElem?_append_left hImplicationIndex]
          exact hImplication
        have hPremise' :
            (proof ++ [consequent])[premiseIndex]? =
              some antecedent := by
          rw [List.getElem?_append_left hPremiseIndex]
          exact hPremise
        exact ⟨consequent,
          HilbertLineCertificateCode.modusPonens
            implicationIndex premiseIndex,
          hFormula', hCertificate',
          Or.inr (Or.inr
            ⟨implicationIndex, premiseIndex, antecedent, consequent,
              rfl, hImplication', hPremise',
              hPremiseEarlier, hImplicationIndex, rfl⟩)⟩

/-! ## 对象证书条件的闭码运输 -/

/--
对象证书条件沿闭公式码等式运输。

内部用保留变量 `443` 表示待运输的公式码；schema 的内部编号从 `904`
开始，因此闭项替换不会捕获内部见证。
-/
theorem ProofT.certificate_condition_of_code_eq
    {T : SetTheory}
    (verifier : ObjectCertificateVerifier)
    (hContract : ProofT.VerifierTransport verifier)
    (left right certificate : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hLeftClosed : Term.freeSupport left = [])
    (hRightClosed : Term.freeSupport right = [])
    (hCertificateClosed : Term.freeSupport certificate = [])
    (hEquality :
      Derives T [] (left ≐ₘ right))
    (hRightCondition :
      Derives T [] (
        verifier.condition right certificate)) :
    Derives T [] (
      verifier.condition left certificate) := by
  let body : SetFormula :=
    verifier.condition (x#443) certificate
  have hSubstitute (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement) :
      Formula.substituteFree SetSort.set 443 replacement body =
        verifier.condition replacement certificate := by
    have hCertificateSubstitution :
        Term.substituteFree SetSort.set 443
            replacement certificate =
          certificate :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set 443 replacement certificate (by
          rw [hCertificateClosed]
          exact List.not_mem_nil)
    apply hContract.substitute_closed
        (x#443) certificate replacement replacement certificate 443
        (by decide) hReplacement
        (by simp [Term.substituteFree, set_variable])
        hCertificateSubstitution
    · simp [ProofT.schema_base, FreshVariable.fresh_id,
        FreshVariable.formulas_bound, FreshVariable.formula_bound,
        FreshVariable.support_bound, Formula.freeSupport,
        Term.freeSupport,
        hCertificateClosed]
    · simp [ProofT.schema_base, FreshVariable.fresh_id,
        FreshVariable.formulas_bound, FreshVariable.formula_bound,
        FreshVariable.support_bound, Formula.freeSupport,
        hReplacement.2, hCertificateClosed]
  have hRightInstance :
      Derives T [] (
        Formula.substituteFree SetSort.set 443 right body) := by
    rw [hSubstitute right ⟨hRight, hRightClosed⟩]
    exact hRightCondition
  have hSymmetric :
      Derives T [] (right ≐ₘ left) :=
    Metatheory.Derives.equality_symm
      hEquality
  have hTransport :
      Derives T [] (
        Formula.substituteFree SetSort.set 443 left body) :=
    FirstOrder.Derives.eq_subst_m
      (T := T) (Γ := [])
      (sort := SetSort.set) (eigen := 443)
      (left := right) (right := left) (body := body)
      hSymmetric hRightInstance
  rw [hSubstitute left ⟨hLeft, hLeftClosed⟩] at hTransport
  exact hTransport

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
