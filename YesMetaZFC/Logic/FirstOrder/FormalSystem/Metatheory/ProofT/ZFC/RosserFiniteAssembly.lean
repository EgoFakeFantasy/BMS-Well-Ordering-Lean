import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCRosser
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.Core

/-!
# `ProofT` 的 ZFC Rosser 有限装配

本模块只处理 Rosser 论证中的有限句法拼装：

* 固定编号的证明码条件沿外层证明码变量作闭项替换；
* 每个标准较小码的闭否定可装配成对象层“无更小证明码”全称式。

这里不判断证明码是否有效；负向 checked replay 只需向第二个接口逐项提供结果。
标准码比较通过 `ProofT.Core` 注入，不再直接调用 ZFC 分离构造。
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

namespace ProofT
namespace ZFC

/--
当前 ZFC realization 的固定编号证明码条件沿保留编号以下的变量作闭项替换。

证明码与结论码的替换结果由调用方分别给出；内部四个见证及 checked replay
编号均位于保留边界以上，故不会捕获替换项。
-/
theorem condition_substitute
    (sourceId : FreeVarId)
    (replacement proofCode conclusion
      proofCodeResult conclusionResult : SetTerm)
    (hSource :
      sourceId < ProofT.condition_base)
    (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement)
    (hProofCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement proofCode =
        proofCodeResult)
    (hConclusionSubstitution :
      Term.substituteFree SetSort.set sourceId replacement conclusion =
        conclusionResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (proof_condition
          fs_zfc_object_certificate_verifier
          proofCode conclusion
          ProofT.condition_base) =
      proof_condition
        fs_zfc_object_certificate_verifier
        proofCodeResult conclusionResult
        ProofT.condition_base := by
  have hSourceNe
      (id : FreeVarId)
      (hId : ProofT.condition_base ≤ id) :
      sourceId ≠ id :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le hSource hId)
  have hReplacementFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport replacement := by
    rw [hReplacement.2]
    exact List.not_mem_nil
  have hVariableFixed
      (id : FreeVarId)
      (hId : ProofT.condition_base ≤ id) :
      Term.substituteFree SetSort.set sourceId replacement
          (x#id) =
        x#id := by
    simp [Term.substituteFree, set_variable,
      Ne.symm (hSourceNe id hId)]
  have hVariableVerifierBase :
      ProofT.schema_base
          [(x#880) ·ₘ (x#900), (x#903)] =
        904 := by
    simp [ProofT.schema_base,
      FreshVariable.fresh_id,
      FreshVariable.formulas_bound,
      FreshVariable.formula_bound,
      FreshVariable.support_bound,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList]
  have hSequenceCondition :
      Formula.substituteFree SetSort.set sourceId replacement
          (CertifiedProof.sequence_condition_with_ids
            fs_zfc_object_certificate_verifier
            (x#880) (x#881)
            900 903 891 892 893 894 895 896 901 902) =
        CertifiedProof.sequence_condition_with_ids
          fs_zfc_object_certificate_verifier
          (x#880) (x#881)
          900 903 891 892 893 894 895 896 901 902 := by
    simpa [ProofT.ZFC.sequence_condition] using
      ProofT.ZFC.sequence_condition_substitute
        (x#880) (x#881) replacement
        (x#880) (x#881) sourceId
        (Nat.lt_trans hSource (by native_decide))
        hReplacement
        (hVariableFixed 880 (by native_decide))
        (hVariableFixed 881 (by native_decide))
        hVariableVerifierBase hVariableVerifierBase
  have hProofSequence :
      Formula.substituteFree SetSort.set sourceId replacement
          (proof_sequence_code_condition_with_ids
            (x#880) (x#882)
            884 885 886 887 888) =
        proof_sequence_code_condition_with_ids
          (x#880) (x#882)
          884 885 886 887 888 := by
    exact
      proof_sequence_code_condition_with_ids_substitute_closed
        (x#880) (x#882) replacement
        (x#880) (x#882)
        sourceId 884 885 886 887 888
        (hSourceNe 884 (by native_decide))
        (hSourceNe 885 (by native_decide))
        (hSourceNe 886 (by native_decide))
        (hSourceNe 887 (by native_decide))
        (hSourceNe 888 (by native_decide))
        hReplacement.1.2
        (hReplacementFresh 884)
        (hReplacementFresh 885)
        (hReplacementFresh 886)
        (hReplacementFresh 887)
        (hReplacementFresh 888)
        (hVariableFixed 880 (by native_decide))
        (hVariableFixed 882 (by native_decide))
  have hCertificateSequence :
      Formula.substituteFree SetSort.set sourceId replacement
          (nat_sequence_code_condition_with_ids
            (x#881) (x#883) 889 890) =
        nat_sequence_code_condition_with_ids
          (x#881) (x#883) 889 890 := by
    exact
      nat_sequence_code_condition_with_ids_substitute_closed
        (x#881) (x#883) replacement
        (x#881) (x#883)
        sourceId 889 890
        (hSourceNe 889 (by native_decide))
        (hSourceNe 890 (by native_decide))
        hReplacement.1.2
        (hReplacementFresh 889)
        (hReplacementFresh 890)
        (hVariableFixed 881 (by native_decide))
        (hVariableFixed 883 (by native_decide))
  have hTerminal :
      Formula.substituteFree SetSort.set sourceId replacement
          (proof_sequence_terminal_condition
            (x#880) conclusion) =
        proof_sequence_terminal_condition
          (x#880) conclusionResult := by
    exact proof_sequence_terminal_condition_substitute
      (x#880) conclusion replacement
      (x#880) conclusionResult sourceId
      (hVariableFixed 880 (by native_decide))
      hConclusionSubstitution
  let sourceBody : SetFormula :=
    proof_witness
      fs_zfc_object_certificate_verifier
      proofCode conclusion
      (x#880) (x#881) (x#882) (x#883)
      ProofT.condition_base
  let targetBody : SetFormula :=
    proof_witness
      fs_zfc_object_certificate_verifier
      proofCodeResult conclusionResult
      (x#880) (x#881) (x#882) (x#883)
      ProofT.condition_base
  have hBody :
      Formula.substituteFree SetSort.set sourceId replacement
          sourceBody =
        targetBody := by
    simp [sourceBody, targetBody,
      proof_witness,
      ProofT.condition_base,
      CertifiedProof.proof_code_component_bound,
      Formula.substituteFree, Term.substituteFree,
      hSequenceCondition, hProofSequence,
      hCertificateSequence, hTerminal,
      hProofCodeSubstitution,
      hVariableFixed 882 (by native_decide),
      hVariableFixed 883 (by native_decide)]
  let sourceCertificateBody : SetFormula :=
    CertifiedProof.proof_code_component_bound
        proofCode (x#883) ∧ₘ
      sourceBody
  let targetCertificateBody : SetFormula :=
    CertifiedProof.proof_code_component_bound
        proofCodeResult (x#883) ∧ₘ
      targetBody
  have hCertificateBody :
      Formula.substituteFree SetSort.set sourceId replacement
          sourceCertificateBody =
        targetCertificateBody := by
    simp [sourceCertificateBody, targetCertificateBody,
      Formula.substituteFree, Term.substituteFree,
      CertifiedProof.proof_code_component_bound,
      hProofCodeSubstitution,
      hVariableFixed 883 (by native_decide),
      hBody]
  have hExists3 :
      Formula.substituteFree SetSort.set sourceId replacement
          (∃ₘ[SetSort.set, 883], sourceCertificateBody) =
        (∃ₘ[SetSort.set, 883], targetCertificateBody) :=
    fs_zfc_substitute_free_exists_closed
      sourceId 883 replacement
      sourceCertificateBody targetCertificateBody
      (hSourceNe 883 (by native_decide))
      hReplacement.1.2
      (hReplacementFresh 883)
      hCertificateBody
  let sourceFormulaBody : SetFormula :=
    CertifiedProof.proof_code_component_bound
        proofCode (x#882) ∧ₘ
      (∃ₘ[SetSort.set, 883], sourceCertificateBody)
  let targetFormulaBody : SetFormula :=
    CertifiedProof.proof_code_component_bound
        proofCodeResult (x#882) ∧ₘ
      (∃ₘ[SetSort.set, 883], targetCertificateBody)
  have hFormulaBody :
      Formula.substituteFree SetSort.set sourceId replacement
          sourceFormulaBody =
        targetFormulaBody := by
    have hGuard :
        Formula.substituteFree SetSort.set sourceId replacement
            (CertifiedProof.proof_code_component_bound
              proofCode (x#882)) =
          CertifiedProof.proof_code_component_bound
            proofCodeResult (x#882) := by
      simp [Formula.substituteFree, Term.substituteFree,
        CertifiedProof.proof_code_component_bound,
        hProofCodeSubstitution,
        hVariableFixed 882 (by native_decide)]
    simp only [sourceFormulaBody, targetFormulaBody,
      Formula.substituteFree] at hGuard ⊢
    have hRight := hExists3
    simp only [Formula.substituteFree] at hRight
    rw [hGuard, hRight]
  have hExists2 :
      Formula.substituteFree SetSort.set sourceId replacement
          (∃ₘ[SetSort.set, 882], sourceFormulaBody) =
        (∃ₘ[SetSort.set, 882], targetFormulaBody) :=
    fs_zfc_substitute_free_exists_closed
      sourceId 882 replacement
      sourceFormulaBody targetFormulaBody
      (hSourceNe 882 (by native_decide))
      hReplacement.1.2
      (hReplacementFresh 882)
      hFormulaBody
  let sourceCertificatesBody : SetFormula :=
    (x#881 ∈ₘ seq₊_spaceₘ(ωₘ)) ∧ₘ
      (∃ₘ[SetSort.set, 882], sourceFormulaBody)
  let targetCertificatesBody : SetFormula :=
    (x#881 ∈ₘ seq₊_spaceₘ(ωₘ)) ∧ₘ
      (∃ₘ[SetSort.set, 882], targetFormulaBody)
  have hCertificatesBody :
      Formula.substituteFree SetSort.set sourceId replacement
          sourceCertificatesBody =
        targetCertificatesBody := by
    have hGuard :
        Formula.substituteFree SetSort.set sourceId replacement
            (x#881 ∈ₘ seq₊_spaceₘ(ωₘ)) =
          (x#881 ∈ₘ seq₊_spaceₘ(ωₘ)) := by
      simp [Formula.substituteFree, Term.substituteFree,
        hVariableFixed 881 (by native_decide)]
    simp only [sourceCertificatesBody, targetCertificatesBody,
      Formula.substituteFree] at hGuard ⊢
    have hRight := hExists2
    simp only [Formula.substituteFree] at hRight
    rw [hGuard, hRight]
  have hExists1 :
      Formula.substituteFree SetSort.set sourceId replacement
          (∃ₘ[SetSort.set, 881], sourceCertificatesBody) =
        (∃ₘ[SetSort.set, 881], targetCertificatesBody) :=
    fs_zfc_substitute_free_exists_closed
      sourceId 881 replacement
      sourceCertificatesBody targetCertificatesBody
      (hSourceNe 881 (by native_decide))
      hReplacement.1.2
      (hReplacementFresh 881)
      hCertificatesBody
  let sourceSequenceBody : SetFormula :=
    (x#880 ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
      (∃ₘ[SetSort.set, 881], sourceCertificatesBody)
  let targetSequenceBody : SetFormula :=
    (x#880 ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
      (∃ₘ[SetSort.set, 881], targetCertificatesBody)
  have hSequenceBody :
      Formula.substituteFree SetSort.set sourceId replacement
          sourceSequenceBody =
        targetSequenceBody := by
    have hGuard :
        Formula.substituteFree SetSort.set sourceId replacement
            (x#880 ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) =
          (x#880 ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) := by
      simp [Formula.substituteFree, Term.substituteFree,
        hVariableFixed 880 (by native_decide)]
    simp only [sourceSequenceBody, targetSequenceBody,
      Formula.substituteFree] at hGuard ⊢
    have hRight := hExists1
    simp only [Formula.substituteFree] at hRight
    rw [hGuard, hRight]
  have hExists0 :
      Formula.substituteFree SetSort.set sourceId replacement
          (∃ₘ[SetSort.set, 880], sourceSequenceBody) =
        (∃ₘ[SetSort.set, 880], targetSequenceBody) :=
    fs_zfc_substitute_free_exists_closed
      sourceId 880 replacement
      sourceSequenceBody targetSequenceBody
      (hSourceNe 880 (by native_decide))
      hReplacement.1.2
      (hReplacementFresh 880)
      hSequenceBody
  rw [proof_condition_eq_witness,
    proof_condition_eq_witness]
  let sourceExists : SetFormula :=
    ∃ₘ[SetSort.set, 880], sourceSequenceBody
  let targetExists : SetFormula :=
    ∃ₘ[SetSort.set, 880], targetSequenceBody
  have hExists :
      Formula.substituteFree SetSort.set sourceId replacement
          sourceExists =
        targetExists := by
    simpa [sourceExists, targetExists] using hExists0
  have hHeader :
      Formula.substituteFree SetSort.set sourceId replacement
          (formula_codeₘ(conclusion) ∧ₘ
            proofCode ∈ₘ ωₘ) =
        (formula_codeₘ(conclusionResult) ∧ₘ
          proofCodeResult ∈ₘ ωₘ) := by
    simp [Formula.substituteFree, Term.substituteFree,
      hConclusionSubstitution,
      hProofCodeSubstitution]
  change
    Formula.conj
        (Formula.substituteFree SetSort.set sourceId replacement
          (formula_codeₘ(conclusion) ∧ₘ
            proofCode ∈ₘ ωₘ))
        (Formula.substituteFree SetSort.set sourceId replacement
          sourceExists) =
      Formula.conj
        (formula_codeₘ(conclusionResult) ∧ₘ
          proofCodeResult ∈ₘ ωₘ)
        targetExists
  rw [hHeader, hExists]

/--
证明码坐标替换的常用闭结论码特例。
-/
theorem condition_substitute_code
    (sourceId : FreeVarId)
    (replacement conclusion : SetTerm)
    (hSource :
      sourceId < ProofT.condition_base)
    (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion) :
    Formula.substituteFree SetSort.set sourceId replacement
        (proof_condition
          fs_zfc_object_certificate_verifier
          (x#sourceId) conclusion
          ProofT.condition_base) =
      proof_condition
        fs_zfc_object_certificate_verifier
        replacement conclusion
        ProofT.condition_base := by
  apply condition_substitute
    sourceId replacement (x#sourceId) conclusion
      replacement conclusion hSource hReplacement
  · simp [Term.substituteFree, set_variable]
  · exact GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hConclusion sourceId replacement

/--
“无更小证明码”的上界与结论码可同时沿保留编号以下的变量作闭项替换。

全称绑定的候选码与外层替换变量必须不同；闭见证保证替换可穿过该绑定。
-/
theorem no_smaller_substitute
    (sourceId smallerCodeId : FreeVarId)
    (replacement bound conclusion
      boundResult conclusionResult : SetTerm)
    (hDistinct : sourceId ≠ smallerCodeId)
    (hSource :
      sourceId < ProofT.condition_base)
    (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement)
    (hBoundSubstitution :
      Term.substituteFree SetSort.set sourceId replacement bound =
        boundResult)
    (hConclusionSubstitution :
      Term.substituteFree SetSort.set sourceId replacement conclusion =
        conclusionResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (no_smaller_condition
          fs_zfc_object_certificate_verifier
          bound conclusion
          smallerCodeId ProofT.condition_base) =
      no_smaller_condition
        fs_zfc_object_certificate_verifier
        boundResult conclusionResult
        smallerCodeId ProofT.condition_base := by
  let sourceCondition : SetFormula :=
    proof_condition
      fs_zfc_object_certificate_verifier
      (x#smallerCodeId) conclusion
      ProofT.condition_base
  let targetCondition : SetFormula :=
    proof_condition
      fs_zfc_object_certificate_verifier
      (x#smallerCodeId) conclusionResult
      ProofT.condition_base
  let sourceBody : SetFormula :=
    (x#smallerCodeId ∈ₘ bound) ⟶ₘ
      ¬ₘ sourceCondition
  let targetBody : SetFormula :=
    (x#smallerCodeId ∈ₘ boundResult) ⟶ₘ
      ¬ₘ targetCondition
  have hProofCondition :
      Formula.substituteFree SetSort.set sourceId replacement
          sourceCondition =
        targetCondition := by
    apply condition_substitute
      sourceId replacement (x#smallerCodeId) conclusion
        (x#smallerCodeId) conclusionResult
        hSource hReplacement
    · simp [Term.substituteFree, set_variable,
        Ne.symm hDistinct]
    · exact hConclusionSubstitution
  have hBody :
      Formula.substituteFree SetSort.set sourceId replacement
          sourceBody =
        targetBody := by
    simp [sourceBody, targetBody,
      sourceCondition, targetCondition,
      Formula.substituteFree, Term.substituteFree,
      set_variable, Ne.symm hDistinct,
      hBoundSubstitution, hProofCondition]
  have hReplacementFresh :
      (SetSort.set, smallerCodeId) ∉
        Term.freeSupport replacement := by
    rw [hReplacement.2]
    exact List.not_mem_nil
  unfold no_smaller_condition
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set sourceId smallerCodeId 0 replacement
    sourceBody hDistinct hReplacement.1.2
    hReplacementFresh]
  have hClosed :=
    congrArg
      (Formula.closeFreeAt SetSort.set smallerCodeId 0)
      hBody
  exact congrArg (Formula.forallE SetSort.set) <| by
    simpa [targetBody] using hClosed

/--
“无更小证明码”沿其上界变量作闭项替换的闭结论码特例。
-/
theorem no_smaller_substitute_bound
    (sourceId smallerCodeId : FreeVarId)
    (replacement conclusion : SetTerm)
    (hDistinct : sourceId ≠ smallerCodeId)
    (hSource :
      sourceId < ProofT.condition_base)
    (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion) :
    Formula.substituteFree SetSort.set sourceId replacement
        (no_smaller_condition
          fs_zfc_object_certificate_verifier
          (x#sourceId) conclusion
          smallerCodeId ProofT.condition_base) =
      no_smaller_condition
        fs_zfc_object_certificate_verifier
        replacement conclusion
        smallerCodeId ProofT.condition_base := by
  apply no_smaller_substitute
    sourceId smallerCodeId replacement
      (x#sourceId) conclusion replacement conclusion
      hDistinct hSource hReplacement
  · simp [Term.substituteFree, set_variable]
  · exact GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hConclusion sourceId replacement

/--
Rosser 比较公式沿外部公式码变量作闭项替换。
-/
theorem comparison_substitute
    (sourceId proofCodeId smallerCodeId : FreeVarId)
    (replacement left right leftResult rightResult : SetTerm)
    (hProofDistinct : sourceId ≠ proofCodeId)
    (hSmallerDistinct : sourceId ≠ smallerCodeId)
    (hSource :
      sourceId < ProofT.condition_base)
    (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement)
    (hLeft :
      Term.substituteFree SetSort.set sourceId replacement left =
        leftResult)
    (hRight :
      Term.substituteFree SetSort.set sourceId replacement right =
        rightResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (comparison_condition
          fs_zfc_object_certificate_verifier
          left right proofCodeId smallerCodeId
          ProofT.condition_base) =
      comparison_condition
        fs_zfc_object_certificate_verifier
        leftResult rightResult proofCodeId smallerCodeId
        ProofT.condition_base := by
  let sourceBody : SetFormula :=
    proof_condition
        fs_zfc_object_certificate_verifier
        (x#proofCodeId) left ProofT.condition_base ∧ₘ
      no_smaller_condition
        fs_zfc_object_certificate_verifier
        (x#proofCodeId) right smallerCodeId
        ProofT.condition_base
  let targetBody : SetFormula :=
    proof_condition
        fs_zfc_object_certificate_verifier
        (x#proofCodeId) leftResult ProofT.condition_base ∧ₘ
      no_smaller_condition
        fs_zfc_object_certificate_verifier
        (x#proofCodeId) rightResult smallerCodeId
        ProofT.condition_base
  have hPositive :
      Formula.substituteFree SetSort.set sourceId replacement
          (proof_condition
            fs_zfc_object_certificate_verifier
            (x#proofCodeId) left ProofT.condition_base) =
        proof_condition
          fs_zfc_object_certificate_verifier
          (x#proofCodeId) leftResult
          ProofT.condition_base := by
    apply condition_substitute
      sourceId replacement (x#proofCodeId) left
        (x#proofCodeId) leftResult hSource hReplacement
    · simp [Term.substituteFree, set_variable,
        Ne.symm hProofDistinct]
    · exact hLeft
  have hNegative :
      Formula.substituteFree SetSort.set sourceId replacement
          (no_smaller_condition
            fs_zfc_object_certificate_verifier
            (x#proofCodeId) right smallerCodeId
            ProofT.condition_base) =
        no_smaller_condition
          fs_zfc_object_certificate_verifier
          (x#proofCodeId) rightResult smallerCodeId
          ProofT.condition_base := by
    apply no_smaller_substitute
      sourceId smallerCodeId replacement
        (x#proofCodeId) right (x#proofCodeId) rightResult
        hSmallerDistinct hSource hReplacement
    · simp [Term.substituteFree, set_variable,
        Ne.symm hProofDistinct]
    · exact hRight
  have hBody :
      Formula.substituteFree SetSort.set sourceId replacement
          sourceBody =
        targetBody := by
    simp [sourceBody, targetBody,
      Formula.substituteFree, hPositive, hNegative]
  unfold comparison_condition
  apply fs_zfc_substitute_free_exists_closed
    sourceId proofCodeId replacement sourceBody targetBody
      hProofDistinct hReplacement.1.2
  · rw [hReplacement.2]
    exact List.not_mem_nil
  · exact hBody

/--
ZFC Rosser 谓词实例就是在给定公式码及其否定码上的证书比较。
-/
theorem predicate_at_eq_comparison
    (formulaCode : SetTerm)
    (hCode :
      GodelQuotation.Numbered.CodeBoundary formulaCode) :
    fs_zfc_rosser_predicate_at formulaCode =
      comparison_condition
        fs_zfc_object_certificate_verifier
        formulaCode (neg_codeₘ(formulaCode))
        fs_zfc_rosser_proof_code_id
        fs_zfc_rosser_smaller_code_id
        ProofT.condition_base := by
  unfold fs_zfc_rosser_predicate_at
  unfold ProofT.rosser_predicate_at
  rw [ProofT.rosser_predicate,
    provability_body]
  apply comparison_substitute
    fs_zfc_rosser_code_id
    fs_zfc_rosser_proof_code_id
    fs_zfc_rosser_smaller_code_id
    formulaCode (x#fs_zfc_rosser_code_id)
    (neg_codeₘ(x#fs_zfc_rosser_code_id))
    formulaCode (neg_codeₘ(formulaCode))
    (by native_decide) (by native_decide)
    (by native_decide) hCode
  · simp [Term.substituteFree, set_variable]
  · simp [negation_formula_code_term,
      Term.substituteFree, set_variable]

/--
每个标准较小码的闭否定可装配成对象层“无更小证明码”。

有限性只来自标准自然数 `bound`；调用方只需给出对应的有限逐点分支。
-/
theorem no_smaller_of_numerals
    (bound : Nat)
    (conclusion : SetTerm)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (hBranch :
      ∀ code, code < bound →
        Derives fs_zfc_support_raw_theory [] (
          ¬ₘ proof_condition
            fs_zfc_object_certificate_verifier
            (numₘ(code)) conclusion
            ProofT.condition_base)) :
    Derives fs_zfc_support_raw_theory [] (
      no_smaller_condition
        fs_zfc_object_certificate_verifier
        (numₘ(bound)) conclusion
        fs_zfc_rosser_smaller_code_id
        ProofT.condition_base) := by
  let point : SetTerm := x#fs_zfc_rosser_smaller_code_id
  let target : SetFormula :=
    ¬ₘ proof_condition
      fs_zfc_object_certificate_verifier
      point conclusion
      ProofT.condition_base
  have hTarget :
      Formula.Admissible target := by
    exact Formula.Admissible.neg <|
      proof_condition_admissible
        fs_zfc_object_certificate_verifier
        point conclusion
        ProofT.condition_base
        (set_variable_admissible
          fs_zfc_rosser_smaller_code_id)
        hConclusion.1
  have hFinite :
      Derives fs_zfc_support_raw_theory [] (
        stdseq_numeral_member_condition bound point ⟶ₘ
          target) := by
    apply stdseq_numeral_member_condition_elim_of_theory
      (hPointCheck :=
        Term.check_admissible_complete
          (set_variable_admissible
            fs_zfc_rosser_smaller_code_id))
      (hConclusionCheck :=
        Formula.check_admissible_complete hTarget)
    intro code hCode
    let equality : SetFormula := point ≐ₘ numₘ(code)
    let Γ : Context signature := [equality]
    nd_apply FirstOrder.Derives.impIntro
    have hEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          point ≐ₘ numₘ(code) :=
      FirstOrder.Derives.assumption (by simp [Γ, equality])
    have hSymmetric :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(code) ≐ₘ point :=
      Metatheory.Derives.equality_symm hEquality
    have hAtNumeral :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          Formula.substituteFree SetSort.set
            fs_zfc_rosser_smaller_code_id
            (numₘ(code)) target := by
      have hSubstitution :=
        condition_substitute_code
          fs_zfc_rosser_smaller_code_id
          (numₘ(code)) conclusion
          (by native_decide)
          ⟨finite_numeral_term_admissible code,
            finite_numeral_term_freeSupport code⟩
          hConclusion
      have hNeg :=
        FirstOrder.Derives.context_weaken
          (Γ := [])
          (Δ := Γ)
          (by simp [Γ])
          (hBranch code hCode)
      have hConditionSubstitution :
          Formula.substituteFree SetSort.set
              fs_zfc_rosser_smaller_code_id
              (numₘ(code))
              (proof_condition
                fs_zfc_object_certificate_verifier
                point conclusion
                ProofT.condition_base) =
            proof_condition
              fs_zfc_object_certificate_verifier
              (numₘ(code)) conclusion
              ProofT.condition_base := by
        simpa [point] using hSubstitution
      change
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          ¬ₘ Formula.substituteFree SetSort.set
            fs_zfc_rosser_smaller_code_id
            (numₘ(code))
            (proof_condition
              fs_zfc_object_certificate_verifier
              point conclusion
              ProofT.condition_base)
      rw [hConditionSubstitution]
      exact hNeg
    have hTransport :=
      FirstOrder.Derives.eq_subst_m
        (T := fs_zfc_support_raw_theory)
        (Γ := Γ)
        (sort := SetSort.set)
        (eigen := fs_zfc_rosser_smaller_code_id)
        (left := numₘ(code))
        (right := point)
        (body := target)
        hSymmetric hAtNumeral
    simpa [point, target,
      ProofT.formula_substitute_self] using
      hTransport
  have hMembershipIff :
      Derives fs_zfc_support_raw_theory [] (
        (point ∈ₘ numₘ(bound)) ↔ₘ
          stdseq_numeral_member_condition bound point) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (stdseq_numeral_member_iff
        bound point
        (set_variable_admissible
          fs_zfc_rosser_smaller_code_id))
  have hOpen :
      Derives fs_zfc_support_raw_theory [] (
        (point ∈ₘ numₘ(bound)) ⟶ₘ target) := by
    exact Metatheory.Derives.imp_trans
      (by
        nd_apply FirstOrder.Derives.impIntro
        exact FirstOrder.Derives.iffElimRight
          (FirstOrder.Derives.context_weaken_cons
            hMembershipIff)
          (FirstOrder.Derives.assumption (by simp)))
      hFinite
  have hTheoryFresh :
      ∀ formula, fs_zfc_support_raw_theory formula →
        (SetSort.set, fs_zfc_rosser_smaller_code_id) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  have hGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := fs_zfc_support_raw_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := fs_zfc_rosser_smaller_code_id)
      hTheoryFresh
      (by simp)
      hOpen
  simpa [no_smaller_condition,
    point, target] using hGeneralized

/--
一个标准证明码及其右侧有限排除可封装成 Rosser 证明码比较。
-/
theorem comparison_of_numeral
    (proofCode : Nat)
    (left right : SetTerm)
    (hLeft :
      GodelQuotation.Numbered.CodeBoundary left)
    (hRight :
      GodelQuotation.Numbered.CodeBoundary right)
    (hPositive :
      Derives fs_zfc_support_raw_theory [] (
        proof_condition
          fs_zfc_object_certificate_verifier
          (numₘ(proofCode)) left
          ProofT.condition_base))
    (hNoSmaller :
      Derives fs_zfc_support_raw_theory [] (
        no_smaller_condition
          fs_zfc_object_certificate_verifier
          (numₘ(proofCode)) right
          fs_zfc_rosser_smaller_code_id
          ProofT.condition_base)) :
    Derives fs_zfc_support_raw_theory [] (
      comparison_condition
        fs_zfc_object_certificate_verifier
        left right
        fs_zfc_rosser_proof_code_id
        fs_zfc_rosser_smaller_code_id
        ProofT.condition_base) := by
  let body : SetFormula :=
    proof_condition
        fs_zfc_object_certificate_verifier
        (x#fs_zfc_rosser_proof_code_id) left
        ProofT.condition_base ∧ₘ
      no_smaller_condition
        fs_zfc_object_certificate_verifier
        (x#fs_zfc_rosser_proof_code_id) right
        fs_zfc_rosser_smaller_code_id
        ProofT.condition_base
  have hNumeral :
      GodelQuotation.Numbered.CodeBoundary
        (numₘ(proofCode)) :=
    ⟨finite_numeral_term_admissible proofCode,
      finite_numeral_term_freeSupport proofCode⟩
  have hPositiveSubstitution :=
    condition_substitute_code
      fs_zfc_rosser_proof_code_id
      (numₘ(proofCode)) left
      (by native_decide)
      hNumeral hLeft
  have hNoSmallerSubstitution :=
    no_smaller_substitute_bound
      fs_zfc_rosser_proof_code_id
      fs_zfc_rosser_smaller_code_id
      (numₘ(proofCode)) right
      (by native_decide)
      (by native_decide)
      hNumeral hRight
  have hInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set
          fs_zfc_rosser_proof_code_id
          (numₘ(proofCode)) body) := by
    simpa [body, Formula.substituteFree,
      hPositiveSubstitution,
      hNoSmallerSubstitution] using
      FirstOrder.Derives.conjIntro
        hPositive hNoSmaller
  unfold comparison_condition
  exact FirstOrder.Derives.exists_intro_substituted
    fs_zfc_rosser_proof_code_id hInstance

/--
有限逐码排除版本的 Rosser 比较装配接口。

调用方只需给出一个正证明码，以及所有严格较小标准码的右侧否证。
-/
theorem comparison_of_numeral_branches
    (proofCode : Nat)
    (left right : SetTerm)
    (hLeft :
      GodelQuotation.Numbered.CodeBoundary left)
    (hRight :
      GodelQuotation.Numbered.CodeBoundary right)
    (hPositive :
      Derives fs_zfc_support_raw_theory [] (
        proof_condition
          fs_zfc_object_certificate_verifier
          (numₘ(proofCode)) left
          ProofT.condition_base))
    (hBranch :
      ∀ code, code < proofCode →
        Derives fs_zfc_support_raw_theory [] (
          ¬ₘ proof_condition
            fs_zfc_object_certificate_verifier
            (numₘ(code)) right
            ProofT.condition_base)) :
    Derives fs_zfc_support_raw_theory [] (
      comparison_condition
        fs_zfc_object_certificate_verifier
        left right
        fs_zfc_rosser_proof_code_id
        fs_zfc_rosser_smaller_code_id
        ProofT.condition_base) := by
  apply comparison_of_numeral
    proofCode left right hLeft hRight hPositive
  exact
    no_smaller_of_numerals
      proofCode right hRight hBranch

/--
标准右证明码及其以下所有左证明码的逐点否定，共同否定 Rosser 比较。

证明只在对象理论内切分候选证明码与标准码的次序；较小分支有限枚举，较大分支
直接违反 `no_smaller`。
-/
theorem comparison_neg_of_right_numeral
    (C : ProofT.Core fs_zfc_support_raw_theory)
    (proofCode : Nat)
    (left right : SetTerm)
    (hLeft :
      GodelQuotation.Numbered.CodeBoundary left)
    (hRight :
      GodelQuotation.Numbered.CodeBoundary right)
    (hRightCode :
      Derives fs_zfc_support_raw_theory [] (
        proof_condition
          fs_zfc_object_certificate_verifier
          (numₘ(proofCode)) right
          ProofT.condition_base))
    (hLeftBranch :
      ∀ code, code ≤ proofCode →
        Derives fs_zfc_support_raw_theory [] (
          ¬ₘ proof_condition
            fs_zfc_object_certificate_verifier
            (numₘ(code)) left
            ProofT.condition_base)) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ comparison_condition
        fs_zfc_object_certificate_verifier
        left right
        fs_zfc_rosser_proof_code_id
        fs_zfc_rosser_smaller_code_id
        ProofT.condition_base) := by
  let point : SetTerm :=
    x#fs_zfc_rosser_proof_code_id
  let positive : SetFormula :=
    proof_condition
      fs_zfc_object_certificate_verifier
      point left ProofT.condition_base
  let noSmaller : SetFormula :=
    no_smaller_condition
      fs_zfc_object_certificate_verifier
      point right fs_zfc_rosser_smaller_code_id
      ProofT.condition_base
  let body : SetFormula :=
    positive ∧ₘ noSmaller
  let comparison : SetFormula :=
    comparison_condition
      fs_zfc_object_certificate_verifier
      left right
      fs_zfc_rosser_proof_code_id
      fs_zfc_rosser_smaller_code_id
      ProofT.condition_base
  have hBodyAdmissible :
      Formula.Admissible body := by
    exact Formula.Admissible.conj
      (proof_condition_admissible
        fs_zfc_object_certificate_verifier
        point left ProofT.condition_base
        (set_variable_admissible
          fs_zfc_rosser_proof_code_id)
        hLeft.1)
      (no_smaller_condition_admissible
        fs_zfc_object_certificate_verifier
        point right fs_zfc_rosser_smaller_code_id
        ProofT.condition_base
        (set_variable_admissible
          fs_zfc_rosser_proof_code_id)
        hRight.1)
  have hComparisonAdmissible :
      Formula.Admissible comparison := by
    simpa [comparison] using
      comparison_condition_admissible
        fs_zfc_object_certificate_verifier
        left right
        fs_zfc_rosser_proof_code_id
        fs_zfc_rosser_smaller_code_id
        ProofT.condition_base
        hLeft.1 hRight.1
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete
        hComparisonAdmissible)
  let Γ : Context signature := [comparison]
  have hComparison :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] comparison :=
    FirstOrder.Derives.assumption (by simp [Γ])
  apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := fs_zfc_rosser_proof_code_id)
    (body := body)
    (conclusion := Formula.falsum)
    (hBodyCheck :=
      Formula.check_admissible_complete hBodyAdmissible)
  · intro formula hFormula
    rw [(C.theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simpa [comparison, body,
      comparison_condition] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set fs_zfc_rosser_proof_code_id 0 body
  · exact List.not_mem_nil
  · simpa [comparison, body,
      comparison_condition] using hComparison
  · let Δ : Context signature := body :: Γ
    have hBody :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hPositive :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] positive :=
      FirstOrder.Derives.conjElimLeft hBody
    have hNoSmaller :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] noSmaller :=
      FirstOrder.Derives.conjElimRight hBody
    have hPointInOmega :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          point ∈ₘ ωₘ := by
      dsimp only [positive] at hPositive
      rw [proof_condition_eq_witness]
        at hPositive
      exact FirstOrder.Derives.conjElimRight
        (FirstOrder.Derives.conjElimLeft hPositive)
    apply C.cut_elim
      proofCode point Formula.falsum
      (set_variable_admissible
        fs_zfc_rosser_proof_code_id)
      Formula.Admissible.falsum
      hPointInOmega
    · intro code hCode
      let Ε : Context signature :=
        (point ≐ₘ numₘ(code)) :: Δ
      have hEquality :
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            point ≐ₘ numₘ(code) :=
        FirstOrder.Derives.assumption (by simp [Ε])
      have hPositiveAt :
          Ε ⊢ₘ[fs_zfc_support_raw_theory] positive :=
        FirstOrder.Derives.context_weaken_cons hPositive
      have hTransport :=
        FirstOrder.Derives.eq_subst_m
          (T := fs_zfc_support_raw_theory)
          (Γ := Ε)
          (sort := SetSort.set)
          (eigen := fs_zfc_rosser_proof_code_id)
          (left := point)
          (right := numₘ(code))
          (body := positive)
          hEquality
          (by
            simpa [point, positive,
              ProofT.formula_substitute_self] using
              hPositiveAt)
      have hSubstitution :=
        condition_substitute_code
          fs_zfc_rosser_proof_code_id
          (numₘ(code)) left
          (by native_decide)
          ⟨finite_numeral_term_admissible code,
            finite_numeral_term_freeSupport code⟩
          hLeft
      have hPositiveNumeral :
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            proof_condition
              fs_zfc_object_certificate_verifier
              (numₘ(code)) left
              ProofT.condition_base := by
        simpa [positive, point, hSubstitution] using
          hTransport
      have hNegativeNumeral :
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            ¬ₘ proof_condition
              fs_zfc_object_certificate_verifier
              (numₘ(code)) left
              ProofT.condition_base :=
        FirstOrder.Derives.context_weaken
          (Γ := [])
          (Δ := Ε)
          (by simp)
          (hLeftBranch code hCode)
      exact FirstOrder.Derives.negElim
        hPositiveNumeral hNegativeNumeral
    · let Ε : Context signature :=
        (numₘ(proofCode) ∈ₘ point) :: Δ
      have hMember :
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            numₘ(proofCode) ∈ₘ point :=
        FirstOrder.Derives.assumption (by simp [Ε])
      have hNoSmallerAt :
          Ε ⊢ₘ[fs_zfc_support_raw_theory] noSmaller :=
        FirstOrder.Derives.context_weaken_cons hNoSmaller
      have hInstantiated :=
        FirstOrder.Derives.forall_elim
          (term := numₘ(proofCode)) hNoSmallerAt
      have hSubstitution :=
        condition_substitute_code
          fs_zfc_rosser_smaller_code_id
          (numₘ(proofCode)) right
          (by native_decide)
          ⟨finite_numeral_term_admissible proofCode,
            finite_numeral_term_freeSupport proofCode⟩
          hRight
      have hImp :
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            (numₘ(proofCode) ∈ₘ point) ⟶ₘ
              ¬ₘ proof_condition
                fs_zfc_object_certificate_verifier
                (numₘ(proofCode)) right
                ProofT.condition_base := by
        simpa [noSmaller, point,
          no_smaller_condition,
          Formula.openAt_closeFreeAt_eq_substituteFree,
          Formula.substituteFree, Term.substituteFree,
          set_variable, hSubstitution,
          (by native_decide :
            fs_zfc_rosser_smaller_code_id ≠
              fs_zfc_rosser_proof_code_id)] using
            hInstantiated
      have hNegative :=
        FirstOrder.Derives.impElim hImp hMember
      exact FirstOrder.Derives.negElim
        (FirstOrder.Derives.context_weaken
          (Γ := [])
          (Δ := Ε)
          (by simp)
          hRightCode)
        hNegative

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
