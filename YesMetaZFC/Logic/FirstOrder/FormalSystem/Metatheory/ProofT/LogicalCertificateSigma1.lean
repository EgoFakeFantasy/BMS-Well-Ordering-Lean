import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Sigma1Encoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CanonicalDelta0

/-!
# 逻辑基础证书的 `Sigma1` 组合器

逻辑证书的 payload、序列和公式码检查都可以分别交付层级证明；本模块只负责把
这些字段装配成有限证书合取，再关闭基础证书中的无界存在见证。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace LogicalCertificateSigma1

open Nonlogical.BasicSetTheory
open GodelQuotation
open Rosser
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-! ## 量词出现性的 `Sigma1` 分类 -/

theorem universal_binder_at_condition_delta0
    (boundVariable formula body start : SetTerm)
    (hSegmentFresh :
      (SetSort.set, 320) ∉
        Term.freeSupport
          (forall_codeₘ(boundVariable, body))) :
    Formula.IsDelta0 set_levy_bound
      (universal_binder_at_condition
        boundVariable formula body start) := by
  have hPrefix :
      Formula.IsDelta0 set_levy_bound
        (((boundVariable ∈ₘ VarSymₘ) ∧ₘ
            (formula_codeₘ(body) ∧ₘ
              (body ∈ₘ CodeStrₘ)))) := by
    exact Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [boundVariable, VarSymₘ])
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.rel
          RelationSymbol.isFormulaCode [body])
        (Formula.IsDelta0.rel
          RelationSymbol.membership [body, CodeStrₘ]))
  have hSubstring :
      Formula.IsDelta0 set_levy_bound
        (code_substring_at_condition
          formula (forall_codeₘ(boundVariable, body)) start) :=
    code_substring_at_delta0
      formula (forall_codeₘ(boundVariable, body)) start
      hSegmentFresh
  simpa [universal_binder_at_condition] using
    Formula.IsDelta0.conj hPrefix hSubstring

theorem quantifier_occurs_condition_sigma1
    (boundVariable formula : SetTerm) :
    (SetSort.set, 320) ∉
      Term.freeSupport
        (forall_codeₘ(boundVariable, x#321)) →
    Formula.IsSigma1 set_levy_bound
      (quantifier_occurs_condition boundVariable formula) := by
  intro hSegmentFresh
  have hUniversal :
      Formula.IsDelta0 set_levy_bound
        (universal_binder_at_condition
          boundVariable formula (x#321) (x#322)) :=
      universal_binder_at_condition_delta0
      boundVariable formula (x#321) (x#322)
      hSegmentFresh
  simpa [quantifier_occurs_condition] using
    Formula.IsSigma1.exists_closeFreeAt
      SetSort.set 321 <|
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set 322 hUniversal.to_sigma1

/-- 有限逻辑证书字段合取保持 `Sigma1`。 -/
theorem certificate_conjunction_sigma1
    (formulas : List SetFormula)
    (hFormulas :
      ∀ formula, formula ∈ formulas →
        Formula.IsSigma1 set_levy_bound formula) :
    Formula.IsSigma1 set_levy_bound
      (CertifiedProof.logical_certificate_conjunction formulas) := by
  induction formulas with
  | nil =>
      simpa [CertifiedProof.logical_certificate_conjunction] using
        (Formula.IsSigma1.delta0
          (Formula.IsDelta0.truth :
            Formula.IsDelta0 set_levy_bound
              (Formula.truth : SetFormula)))
  | cons formula formulas ih =>
      cases formulas with
      | nil =>
          simpa [CertifiedProof.logical_certificate_conjunction] using
            hFormulas formula (by simp)
      | cons next rest =>
          simpa [CertifiedProof.logical_certificate_conjunction] using
            Formula.IsSigma1.conj
              (hFormulas formula (by simp))
              (ih (fun item hItem =>
                hFormulas item (by simp [hItem])))

/-- 一元基础证书的 `Sigma1` 字段装配器。 -/
theorem unary_base_certificate_condition_with_ids_sigma1
    (tag : Nat)
    (constructor : SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId componentId traceId indexId : FreeVarId)
    (hSequence :
      Formula.IsSigma1 set_levy_bound
        (nat_sequence_code_condition_with_ids
          (x#sequenceId) (x#payloadId) traceId indexId))
    (hComponent :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_formula_payload_component_condition_with_ids
          (x#componentId) (x#sequenceId ·ₘ numₘ(0))
          traceId indexId)) :
    Formula.IsSigma1 set_levy_bound
      (CertifiedProof.logical_unary_base_certificate_condition_with_ids
        tag constructor formulaCode certificate
        payloadId sequenceId componentId traceId indexId) := by
  let body : SetFormula :=
    CertifiedProof.logical_certificate_conjunction [
      certificate ≐ₘ
        godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
      nat_sequence_code_condition_with_ids
        (x#sequenceId) (x#payloadId) traceId indexId,
      domₘ(x#sequenceId) ≐ₘ numₘ(1),
      CertifiedProof.logical_formula_payload_component_condition_with_ids
        (x#componentId) (x#sequenceId ·ₘ numₘ(0))
        traceId indexId,
      formulaCode ≐ₘ constructor (x#componentId)]
  have hBody :
      Formula.IsSigma1 set_levy_bound body := by
    apply certificate_conjunction_sigma1
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with
      rfl | rfl | rfl | rfl | rfl
    · exact
        Formula.IsSigma1.delta0
          (Formula.IsDelta0.equal
            certificate
            (godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ)))
    · exact hSequence
    · exact
        Formula.IsSigma1.delta0
          (Formula.IsDelta0.equal
            (domₘ(x#sequenceId)) (numₘ(1)))
    · exact hComponent
    · exact
        Formula.IsSigma1.delta0
          (Formula.IsDelta0.equal
            formulaCode (constructor (x#componentId)))
  simpa [CertifiedProof.logical_unary_base_certificate_condition_with_ids,
    body] using
    Formula.IsSigma1.exists_closeFreeAt
      SetSort.set payloadId <|
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set sequenceId <|
        Formula.IsSigma1.exists_closeFreeAt
          SetSort.set componentId hBody

/-- 二元基础证书的 `Sigma1` 字段装配器。 -/
theorem binary_base_certificate_condition_with_ids_sigma1
    (tag : Nat)
    (constructor : SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId leftId rightId traceId indexId : FreeVarId)
    (hSequence :
      Formula.IsSigma1 set_levy_bound
        (nat_sequence_code_condition_with_ids
          (x#sequenceId) (x#payloadId) traceId indexId))
    (hLeft :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_formula_payload_component_condition_with_ids
          (x#leftId) (x#sequenceId ·ₘ numₘ(0))
          traceId indexId))
    (hRight :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_formula_payload_component_condition_with_ids
          (x#rightId) (x#sequenceId ·ₘ numₘ(1))
          traceId indexId)) :
    Formula.IsSigma1 set_levy_bound
      (CertifiedProof.logical_binary_base_certificate_condition_with_ids
        tag constructor formulaCode certificate
        payloadId sequenceId leftId rightId traceId indexId) := by
  let body : SetFormula :=
    CertifiedProof.logical_certificate_conjunction [
      certificate ≐ₘ
        godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
      nat_sequence_code_condition_with_ids
        (x#sequenceId) (x#payloadId) traceId indexId,
      domₘ(x#sequenceId) ≐ₘ numₘ(2),
      CertifiedProof.logical_formula_payload_component_condition_with_ids
        (x#leftId) (x#sequenceId ·ₘ numₘ(0))
        traceId indexId,
      CertifiedProof.logical_formula_payload_component_condition_with_ids
        (x#rightId) (x#sequenceId ·ₘ numₘ(1))
        traceId indexId,
      formulaCode ≐ₘ
        constructor (x#leftId) (x#rightId)]
  have hBody :
      Formula.IsSigma1 set_levy_bound body := by
    apply certificate_conjunction_sigma1
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact
        Formula.IsSigma1.delta0
          (Formula.IsDelta0.equal
            certificate
            (godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ)))
    · exact hSequence
    · exact
        Formula.IsSigma1.delta0
          (Formula.IsDelta0.equal
            (domₘ(x#sequenceId)) (numₘ(2)))
    · exact hLeft
    · exact hRight
    · exact
        Formula.IsSigma1.delta0
          (Formula.IsDelta0.equal
            formulaCode
            (constructor (x#leftId) (x#rightId)))
  simpa [CertifiedProof.logical_binary_base_certificate_condition_with_ids,
    body] using
    Formula.IsSigma1.exists_closeFreeAt
      SetSort.set payloadId <|
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set sequenceId <|
        Formula.IsSigma1.exists_closeFreeAt
          SetSort.set leftId <|
          Formula.IsSigma1.exists_closeFreeAt
            SetSort.set rightId hBody

/-- 三元基础证书的 `Sigma1` 字段装配器。 -/
theorem ternary_base_certificate_condition_with_ids_sigma1
    (tag : Nat)
    (constructor : SetTerm → SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId firstId secondId thirdId traceId indexId : FreeVarId)
    (hSequence :
      Formula.IsSigma1 set_levy_bound
        (nat_sequence_code_condition_with_ids
          (x#sequenceId) (x#payloadId) traceId indexId))
    (hFirst :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_formula_payload_component_condition_with_ids
          (x#firstId) (x#sequenceId ·ₘ numₘ(0))
          traceId indexId))
    (hSecond :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_formula_payload_component_condition_with_ids
          (x#secondId) (x#sequenceId ·ₘ numₘ(1))
          traceId indexId))
    (hThird :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_formula_payload_component_condition_with_ids
          (x#thirdId) (x#sequenceId ·ₘ numₘ(2))
          traceId indexId)) :
    Formula.IsSigma1 set_levy_bound
      (CertifiedProof.logical_ternary_base_certificate_condition_with_ids
        tag constructor formulaCode certificate
        payloadId sequenceId firstId secondId thirdId traceId indexId) := by
  let body : SetFormula :=
    CertifiedProof.logical_certificate_conjunction [
      certificate ≐ₘ
        godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
      nat_sequence_code_condition_with_ids
        (x#sequenceId) (x#payloadId) traceId indexId,
      domₘ(x#sequenceId) ≐ₘ numₘ(3),
      CertifiedProof.logical_formula_payload_component_condition_with_ids
        (x#firstId) (x#sequenceId ·ₘ numₘ(0))
        traceId indexId,
      CertifiedProof.logical_formula_payload_component_condition_with_ids
        (x#secondId) (x#sequenceId ·ₘ numₘ(1))
        traceId indexId,
      CertifiedProof.logical_formula_payload_component_condition_with_ids
        (x#thirdId) (x#sequenceId ·ₘ numₘ(2))
        traceId indexId,
      formulaCode ≐ₘ
        constructor (x#firstId) (x#secondId) (x#thirdId)]
  have hBody :
      Formula.IsSigma1 set_levy_bound body := by
    apply certificate_conjunction_sigma1
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact
        Formula.IsSigma1.delta0
          (Formula.IsDelta0.equal
            certificate
            (godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ)))
    · exact hSequence
    · exact
        Formula.IsSigma1.delta0
          (Formula.IsDelta0.equal
            (domₘ(x#sequenceId)) (numₘ(3)))
    · exact hFirst
    · exact hSecond
    · exact hThird
    · exact
        Formula.IsSigma1.delta0
          (Formula.IsDelta0.equal
            formulaCode
            (constructor (x#firstId) (x#secondId) (x#thirdId)))
  simpa [CertifiedProof.logical_ternary_base_certificate_condition_with_ids,
    body] using
    Formula.IsSigma1.exists_closeFreeAt
      SetSort.set payloadId <|
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set sequenceId <|
        Formula.IsSigma1.exists_closeFreeAt
          SetSort.set firstId <|
          Formula.IsSigma1.exists_closeFreeAt
            SetSort.set secondId <|
            Formula.IsSigma1.exists_closeFreeAt
              SetSort.set thirdId hBody

/-! ## 十二类基础逻辑公理的析取装配 -/

theorem base_certificate_condition_with_base_sigma1_of_parts
    (formulaCode certificate : SetTerm)
    (base : FreeVarId)
    (h0 :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_ternary_base_certificate_condition_with_ids
          0 implication_distribution_axiom_code_term
          formulaCode certificate
          base (base + 1) (base + 2) (base + 3)
          (base + 4) (base + 40) (base + 41)))
    (h1 :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_unary_base_certificate_condition_with_ids
          1 self_implication_axiom_code_term
          formulaCode certificate
          (base + 5) (base + 6) (base + 7)
          (base + 40) (base + 41)))
    (h2 :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_binary_base_certificate_condition_with_ids
          2 weakening_axiom_code_term
          formulaCode certificate
          (base + 8) (base + 9) (base + 10) (base + 11)
          (base + 40) (base + 41)))
    (h3 :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_binary_base_certificate_condition_with_ids
          3 contradiction_axiom_code_term
          formulaCode certificate
          (base + 12) (base + 13) (base + 14) (base + 15)
          (base + 40) (base + 41)))
    (h4 :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_unary_base_certificate_condition_with_ids
          4 classical_axiom_code_term
          formulaCode certificate
          (base + 16) (base + 17) (base + 18)
          (base + 40) (base + 41)))
    (h5 :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_binary_base_certificate_condition_with_ids
          5 explosion_axiom_code_term
          formulaCode certificate
          (base + 19) (base + 20) (base + 21) (base + 22)
          (base + 40) (base + 41)))
    (h6 :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_binary_base_certificate_condition_with_ids
          6 case_analysis_axiom_code_term
          formulaCode certificate
          (base + 23) (base + 24) (base + 25) (base + 26)
          (base + 40) (base + 41)))
    (h7 :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_specialization_certificate_condition_with_ids
          formulaCode certificate
          (base + 27) (base + 28) (base + 29) (base + 30)
          (base + 31) (base + 32) (base + 33) (base + 34)
          (base + 35) (base + 36) (base + 40) (base + 41)))
    (h8 :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_forall_distribution_certificate_condition_with_ids
          formulaCode certificate
          (base + 42) (base + 43) (base + 44) (base + 45)
          (base + 46) (base + 47) (base + 48) (base + 49)
          (base + 50) (base + 51) (base + 40) (base + 41)))
    (h9 :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_vacuous_forall_certificate_condition_with_ids
          formulaCode certificate
          (base + 52) (base + 53) (base + 54) (base + 55)
          (base + 56) (base + 57) (base + 40) (base + 41)))
    (h10 :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_equality_substitution_certificate_condition_with_ids
          formulaCode certificate
          (base + 58) (base + 59) (base + 60) (base + 61)
          (base + 40) (base + 41)))
    (h11 :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_equality_reflexivity_certificate_condition_with_id
          formulaCode certificate (base + 62))) :
    Formula.IsSigma1 set_levy_bound
      (CertifiedProof.logical_base_certificate_condition_with_base
        formulaCode certificate base) := by
  simpa [CertifiedProof.logical_base_certificate_condition_with_base] using
    Formula.IsSigma1.disj h0 <|
      Formula.IsSigma1.disj h1 <|
        Formula.IsSigma1.disj h2 <|
          Formula.IsSigma1.disj h3 <|
            Formula.IsSigma1.disj h4 <|
              Formula.IsSigma1.disj h5 <|
                Formula.IsSigma1.disj h6 <|
                  Formula.IsSigma1.disj h7 <|
                    Formula.IsSigma1.disj h8 <|
                      Formula.IsSigma1.disj h9 <|
                        Formula.IsSigma1.disj h10 h11

end LogicalCertificateSigma1
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
