import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedCertificateRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProofTerminal
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.FormulaConstruction

/-!
# ZFC checked modus ponens 的对象层拒绝

本模块把宿主层已经确认的 token 形状不匹配翻译为对象层
`modus_ponensₘ` 的否定。核心接口不依赖具体 proof code 或 replay 状态，只要求三项
分别对齐到标准 token 序列，因此可被 checked proof、外部证书和后续证明器共用。
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

/--
若前件、蕴含式和结论分别等于三个标准 token 序列，而蕴含式 token 串不是由另外
两串构造出的规范蕴含串，则对象层 modus ponens 不成立。
-/
theorem ProofT.modus_ponens_neg_of_shape
    {T : SetTheory}
    (R : ProofT.ObjectReplay T)
    (premise implication conclusion : SetTerm)
    (premiseTokens implicationTokens conclusionTokens : List Nat)
    (hPremise : Term.Admissible premise SetSort.set)
    (hImplication : Term.Admissible implication SetSort.set)
    (hConclusion : Term.Admissible conclusion SetSort.set)
    (hPremiseEquality :
      Derives T [] (
        premise ≐ₘ standard_token_sequence premiseTokens))
    (hImplicationEquality :
      Derives T [] (
        implication ≐ₘ standard_token_sequence implicationTokens))
    (hConclusionEquality :
      Derives T [] (
        conclusion ≐ₘ standard_token_sequence conclusionTokens))
    (hShape :
      implicationTokens ≠
        Numbered.implication_tokens
          premiseTokens conclusionTokens) :
    Derives T [] (
      ¬ₘ modus_ponensₘ(premise, implication, conclusion)) := by
  let premiseStandard : SetTerm :=
    standard_token_sequence premiseTokens
  let conclusionStandard : SetTerm :=
    standard_token_sequence conclusionTokens
  let expectedTokens : List Nat :=
    Numbered.implication_tokens
      premiseTokens conclusionTokens
  have hPremiseStandard :
      Term.Admissible premiseStandard SetSort.set := by
    simpa [premiseStandard] using
      standard_token_sequence_admissible premiseTokens
  have hConclusionStandard :
      Term.Admissible conclusionStandard SetSort.set := by
    simpa [conclusionStandard] using
      standard_token_sequence_admissible conclusionTokens
  have hConstructorCongruence :
      Derives T [] (
        imp_codeₘ(premise, conclusion) ≐ₘ
          imp_codeₘ(premiseStandard, conclusionStandard)) :=
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      (fun left right => imp_codeₘ(left, right))
      (fun left right hLeft hRight =>
        implication_formula_code_term_admissible
          left right hLeft hRight)
      (by
        intro parameter replacement left right
        simp [Term.substituteFree])
      premise premiseStandard conclusion conclusionStandard
      hPremise hPremiseStandard
      hConclusion hConclusionStandard
      (by simpa [premiseStandard] using hPremiseEquality)
      (by simpa [conclusionStandard] using hConclusionEquality)
  have hPremiseReflexive :
      Derives godel_quotation_theory [] (
        premiseStandard ≐ₘ
          standard_token_sequence premiseTokens) := by
    simpa [premiseStandard] using
      FirstOrder.Derives.eq_refl_m premiseStandard
  have hConclusionReflexive :
      Derives godel_quotation_theory [] (
        conclusionStandard ≐ₘ
          standard_token_sequence conclusionTokens) := by
    simpa [conclusionStandard] using
      FirstOrder.Derives.eq_refl_m conclusionStandard
  have hStandardConstructor :
      Derives T [] (
        imp_codeₘ(premiseStandard, conclusionStandard) ≐ₘ
          standard_token_sequence expectedTokens) := by
    simpa [expectedTokens] using
      FirstOrder.Derives.theory_weaken
        (fun _ hFormula => R.godel_quotation hFormula) <|
        implication_formula_code_eq_standard_token_sequence
          premiseTokens conclusionTokens
          premiseStandard conclusionStandard
          hPremiseReflexive hConclusionReflexive
  have hExpected :
      Derives T [] (
        imp_codeₘ(premise, conclusion) ≐ₘ
          standard_token_sequence expectedTokens) :=
    Metatheory.Derives.equality_trans
      hConstructorCongruence hStandardConstructor
  have hModusPonensAdmissible :
      Formula.Admissible
        (modus_ponensₘ(premise, implication, conclusion)) :=
    modus_ponens_formula_admissible
      premise implication conclusion
      hPremise hImplication hConclusion
  nd_apply FirstOrder.Derives.negIntro
    (T := T)
    (Γ := ([] : Context signature))
    (body := modus_ponensₘ(premise, implication, conclusion))
    (hBodyCheck :=
      Formula.check_admissible_complete hModusPonensAdmissible)
  let Γ : Context signature :=
    [modus_ponensₘ(premise, implication, conclusion)]
  have hModusPonens :
      Γ ⊢ₘ[T]
        modus_ponensₘ(premise, implication, conclusion) :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hIff :
      Γ ⊢ₘ[T]
        modus_ponensₘ(premise, implication, conclusion) ↔ₘ
          modus_ponens_condition
            premise implication conclusion := by
    exact FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <|
        FirstOrder.Derives.theory_weaken
          (fun _ hFormula => R.logical_rules hFormula)
          (modus_ponens_iff_condition
            premise implication conclusion
            hPremise hImplication hConclusion)
  have hCondition :
      Γ ⊢ₘ[T]
        modus_ponens_condition
          premise implication conclusion :=
    FirstOrder.Derives.iffElimRight hIff hModusPonens
  have hCodeEquality :
      Γ ⊢ₘ[T]
        implication ≐ₘ imp_codeₘ(premise, conclusion) := by
    simpa [modus_ponens_condition] using
      FirstOrder.Derives.conjElimRight hCondition
  have hImplicationStandard :
      Γ ⊢ₘ[T]
        standard_token_sequence implicationTokens ≐ₘ
          implication :=
    Metatheory.Derives.equality_symm <|
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ])
        hImplicationEquality
  have hExpectedAt :
      Γ ⊢ₘ[T]
        imp_codeₘ(premise, conclusion) ≐ₘ
          standard_token_sequence expectedTokens :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) hExpected
  have hStandardEquality :
      Γ ⊢ₘ[T]
        standard_token_sequence implicationTokens ≐ₘ
          standard_token_sequence expectedTokens :=
    Metatheory.Derives.equality_trans hImplicationStandard <|
      Metatheory.Derives.equality_trans
        hCodeEquality hExpectedAt
  have hStandardNe :
      Γ ⊢ₘ[T]
        ¬ₘ (standard_token_sequence implicationTokens ≐ₘ
          standard_token_sequence expectedTokens) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <|
        FirstOrder.Derives.theory_weaken
          (fun _ hFormula => R.standard_sequence hFormula) <|
          standard_token_sequence_ne <| by
            simpa [expectedTokens] using hShape
  exact FirstOrder.Derives.negElim
    hStandardEquality hStandardNe

/--
规范二维 token 行序列中的三项若不满足蕴含串构造等式，则对应三个标准位置
不能满足对象层 modus ponens。
-/
theorem ProofT.row_modus_ponens_neg
    {T : SetTheory}
    (R : ProofT.ObjectReplay T)
    (rows : List (List Nat))
    (index implicationIndex premiseIndex : Nat)
    (hIndex : index < rows.length)
    (hImplicationIndex : implicationIndex < rows.length)
    (hPremiseIndex : premiseIndex < rows.length)
    (hShape :
      rows[implicationIndex] ≠
        Numbered.implication_tokens
          rows[premiseIndex] rows[index]) :
    Derives T [] (
      ¬ₘ modus_ponensₘ(
        standard_sequence
            (rows.map standard_token_sequence) ·ₘ
          numₘ(premiseIndex),
        standard_sequence
            (rows.map standard_token_sequence) ·ₘ
          numₘ(implicationIndex),
        standard_sequence
            (rows.map standard_token_sequence) ·ₘ
          numₘ(index))) := by
  let sequence : SetTerm :=
    standard_sequence
      (rows.map standard_token_sequence)
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    dsimp [sequence]
    apply seq_admissible_m 0
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨tokens, _, rfl⟩
    exact standard_token_sequence_admissible tokens
  have hPremise :
      Term.Admissible
        (sequence ·ₘ numₘ(premiseIndex)) SetSort.set :=
    function_application_term_admissible
      sequence (numₘ(premiseIndex))
      hSequence (finite_numeral_term_admissible premiseIndex)
  have hImplication :
      Term.Admissible
        (sequence ·ₘ numₘ(implicationIndex)) SetSort.set :=
    function_application_term_admissible
      sequence (numₘ(implicationIndex))
      hSequence (finite_numeral_term_admissible implicationIndex)
  have hConclusion :
      Term.Admissible
        (sequence ·ₘ numₘ(index)) SetSort.set :=
    function_application_term_admissible
      sequence (numₘ(index))
      hSequence (finite_numeral_term_admissible index)
  have hPremiseEquality :
      Derives T [] (
        sequence ·ₘ numₘ(premiseIndex) ≐ₘ
          standard_token_sequence rows[premiseIndex]) := by
    simpa [sequence] using
      ProofT.row_apply
        R
        rows premiseIndex hPremiseIndex
  have hImplicationEquality :
      Derives T [] (
        sequence ·ₘ numₘ(implicationIndex) ≐ₘ
          standard_token_sequence rows[implicationIndex]) := by
    simpa [sequence] using
      ProofT.row_apply
        R
        rows implicationIndex hImplicationIndex
  have hConclusionEquality :
      Derives T [] (
        sequence ·ₘ numₘ(index) ≐ₘ
          standard_token_sequence rows[index]) := by
    simpa [sequence] using
      ProofT.row_apply
        R
        rows index hIndex
  simpa [sequence] using
    ProofT.modus_ponens_neg_of_shape
      R
      (sequence ·ₘ numₘ(premiseIndex))
      (sequence ·ₘ numₘ(implicationIndex))
      (sequence ·ₘ numₘ(index))
      rows[premiseIndex]
      rows[implicationIndex]
      rows[index]
      hPremise hImplication hConclusion
      hPremiseEquality hImplicationEquality hConclusionEquality
      hShape

/-! ## 具体 MP 失败的完整 checked 行拒绝 -/

/--
MP 证书码锁定到两个具体索引，且对应的对象层 MP 已被否定时，完整 checked
行条件被拒绝。外层标签 `2` 同时排除逻辑与理论证书分支。
-/
theorem
    ProofT.ZFC.line_neg_of_modus_ponens_ground
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (sequence certificates : SetTerm)
    (index implicationIndex premiseIndex : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hCertificateAt :
      Derives T [] (
        certificates ·ₘ numₘ(index) ≐ₘ
          numₘ(godel_pair_value 2
            (godel_pair_value implicationIndex premiseIndex))))
    (hGroundNeg :
      Derives T [] (
        ¬ₘ modus_ponensₘ(
          sequence ·ₘ numₘ(premiseIndex),
          sequence ·ₘ numₘ(implicationIndex),
          sequence ·ₘ numₘ(index)))) :
    Derives T [] (
      ¬ₘ ProofT.ZFC.line_condition
        sequence certificates (numₘ(index))) := by
  let logicalCondition : SetFormula :=
    CertifiedProof.logical_certificate_condition_with_ids
      (sequence ·ₘ numₘ(index))
      (x#ProofT.certificate_code_id)
      ProofT.lc_sequence_id
      ProofT.lc_formula_trace_id
      ProofT.lc_last_index_id
      ProofT.lc_line_index_id
      ProofT.lc_code_trace_id
      ProofT.lc_code_index_id
  let theoryCondition : SetFormula :=
    fs_zfc_object_certificate_verifier.condition
      (sequence ·ₘ numₘ(index))
      (x#ProofT.certificate_code_id)
  have hLogicalNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_logical_line_branch
          sequence certificates (numₘ(index))) := by
    have hBody :
        Formula.Admissible
          (ProofT.tagged_line_body
            certificates (numₘ(index)) 0 logicalCondition) := by
      simpa [logicalCondition, ProofT.tagged_line_body,
        fs_zfc_checked_logical_line_body,
        CertifiedProof.logical_certificate_code] using
        fs_zfc_checked_logical_line_body_admissible
          sequence certificates (numₘ(index))
          hSequence hCertificates
          (finite_numeral_term_admissible index)
    have hInvalid :
        ∀ value,
          godel_pair_value 2
              (godel_pair_value implicationIndex premiseIndex) ≠
            godel_pair_value 0 value := by
      intro value hCode
      have hTag := (godel_pair_value_eq_iff.mp hCode).1
      omega
    simpa [fs_zfc_checked_logical_line_branch,
      fs_zfc_checked_logical_line_body,
      ProofT.tagged_line_body,
      logicalCondition,
      CertifiedProof.logical_certificate_code] using
      ProofT.tagged_branch_neg
        C
        certificates (numₘ(index)) 0
        (godel_pair_value 2
          (godel_pair_value implicationIndex premiseIndex))
        logicalCondition hCertificates
        (finite_numeral_term_admissible index)
        hBody hCertificateAt hInvalid
  have hTheoryNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_theory_line_branch
          sequence certificates (numₘ(index))) := by
    have hBody :
        Formula.Admissible
          (ProofT.tagged_line_body
            certificates (numₘ(index)) 1 theoryCondition) := by
      simpa [theoryCondition, ProofT.tagged_line_body,
        fs_zfc_checked_theory_line_body,
        CertifiedProof.theory_certificate_code] using
        fs_zfc_checked_theory_line_body_admissible
          sequence certificates (numₘ(index))
          hSequence hCertificates
          (finite_numeral_term_admissible index)
    have hInvalid :
        ∀ value,
          godel_pair_value 2
              (godel_pair_value implicationIndex premiseIndex) ≠
            godel_pair_value 1 value := by
      intro value hCode
      have hTag := (godel_pair_value_eq_iff.mp hCode).1
      omega
    simpa [fs_zfc_checked_theory_line_branch,
      fs_zfc_checked_theory_line_body,
      ProofT.tagged_line_body,
      theoryCondition,
      CertifiedProof.theory_certificate_code] using
      ProofT.tagged_branch_neg
        C
        certificates (numₘ(index)) 1
        (godel_pair_value 2
          (godel_pair_value implicationIndex premiseIndex))
        theoryCondition hCertificates
        (finite_numeral_term_admissible index)
        hBody hCertificateAt hInvalid
  have hModusPonensNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_modus_ponens_line_branch
          sequence certificates (numₘ(index))) :=
    ProofT.modus_ponens_branch_neg_of_ground
      C
      sequence certificates index implicationIndex premiseIndex
      hSequence hCertificates hSequenceClosed
      hCertificateAt hGroundNeg
  exact
    ProofT.ZFC.line_neg_of_branches
      sequence certificates (numₘ(index))
      hSequence hCertificates
      (finite_numeral_term_admissible index)
      hLogicalNeg hTheoryNeg hModusPonensNeg

/--
具体 MP 失败否定证明序列条件中使用的 numeral checked 行实例。
-/
theorem
    ProofT.ZFC.line_instance_neg_of_modus_ponens_ground
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (sequence certificates : SetTerm)
    (index implicationIndex premiseIndex : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hCertificatesClosed : Term.freeSupport certificates = [])
    (hCertificateAt :
      Derives T [] (
        certificates ·ₘ numₘ(index) ≐ₘ
          numₘ(godel_pair_value 2
            (godel_pair_value implicationIndex premiseIndex))))
    (hGroundNeg :
      Derives T [] (
        ¬ₘ modus_ponensₘ(
          sequence ·ₘ numₘ(premiseIndex),
          sequence ·ₘ numₘ(implicationIndex),
          sequence ·ₘ numₘ(index)))) :
    Derives T [] (
      ¬ₘ ProofT.ZFC.line_instance
        sequence certificates index) := by
  have hLineNeg :=
    ProofT.ZFC.line_neg_of_modus_ponens_ground
      C
      sequence certificates index implicationIndex premiseIndex
      hSequence hCertificates hSequenceClosed
      hCertificateAt hGroundNeg
  unfold ProofT.ZFC.line_instance ProofT.line_instance
  rw [ProofT.line_condition_substitute_numeral
    fs_zfc_object_certificate_verifier
    ProofT.ZFC.verifier_transport
    sequence certificates index
    hSequenceClosed hCertificatesClosed]
  exact hLineNeg

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
