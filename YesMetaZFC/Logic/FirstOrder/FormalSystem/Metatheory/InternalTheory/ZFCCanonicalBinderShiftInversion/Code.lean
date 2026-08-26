import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCanonicalBinderShiftInversion.Assemble
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.Opening

/-!
# 规范 binder-shift 的代码层函数性

本模块把单 token 唯一性提升到有限标准序列代码。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open GodelQuotation

set_option autoImplicit false

/-- 将代码条件的逐点全称式实例化到标准下标。 -/
private theorem fs_zfc_support_raw_canonical_binder_shift_point_at
    {Γ : Context signature}
    (index : Nat)
    (sourceCode targetCode : SetTerm)
    (indexId : FreeVarId)
    (hSourceFresh :
      (SetSort.set, indexId) ∉
        Term.freeSupport sourceCode)
    (hTargetFresh :
      (SetSort.set, indexId) ∉
        Term.freeSupport targetCode)
    (hPointwise :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∀ₘ[SetSort.set, indexId],
          (x#indexId ∈ₘ domₘ(sourceCode)) ⟶ₘ
            canonical_binder_shift_token_condition_with_ids
              (sourceCode ·ₘ x#indexId)
              (targetCode ·ₘ x#indexId)
              (indexId + 1) (indexId + 2)
              (indexId + 3) (indexId + 4)
              (indexId + 5) (indexId + 6)
              (indexId + 7)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (numₘ(index) ∈ₘ domₘ(sourceCode)) ⟶ₘ
        canonical_binder_shift_token_condition_with_ids
          (sourceCode ·ₘ numₘ(index))
          (targetCode ·ₘ numₘ(index))
          (indexId + 1) (indexId + 2)
          (indexId + 3) (indexId + 4)
          (indexId + 5) (indexId + 6)
          (indexId + 7) := by
  have hSourceSubstitute :
      Term.substituteFree SetSort.set indexId
          (numₘ(index)) sourceCode =
        sourceCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set indexId (numₘ(index)) sourceCode
      hSourceFresh
  have hTargetSubstitute :
      Term.substituteFree SetSort.set indexId
          (numₘ(index)) targetCode =
        targetCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set indexId (numₘ(index)) targetCode
      hTargetFresh
  have hCloseCommute
      (closedId : FreeVarId)
      (depth : Nat)
      (formula : SetFormula)
      (hDistinct : indexId ≠ closedId) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set
            closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) formula) := by
    exact (Formula.closeFreeAt_substituteFree_comm
      SetSort.set indexId closedId depth
      (numₘ(index)) formula hDistinct
      (finite_numeral_term_admissible index).2
      (by simp [finite_numeral_term_freeSupport])).symm
  have hClose₁ (depth : Nat) (formula : SetFormula) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set
            (indexId + 1) depth formula) =
        Formula.closeFreeAt SetSort.set (indexId + 1) depth
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) formula) :=
    hCloseCommute (indexId + 1) depth formula (by simp)
  have hClose₂ (depth : Nat) (formula : SetFormula) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set
            (indexId + 2) depth formula) =
        Formula.closeFreeAt SetSort.set (indexId + 2) depth
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) formula) :=
    hCloseCommute (indexId + 2) depth formula (by simp)
  have hClose₃ (depth : Nat) (formula : SetFormula) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set
            (indexId + 3) depth formula) =
        Formula.closeFreeAt SetSort.set (indexId + 3) depth
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) formula) :=
    hCloseCommute (indexId + 3) depth formula (by simp)
  have hClose₄ (depth : Nat) (formula : SetFormula) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set
            (indexId + 4) depth formula) =
        Formula.closeFreeAt SetSort.set (indexId + 4) depth
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) formula) :=
    hCloseCommute (indexId + 4) depth formula (by simp)
  have hClose₅ (depth : Nat) (formula : SetFormula) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set
            (indexId + 5) depth formula) =
        Formula.closeFreeAt SetSort.set (indexId + 5) depth
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) formula) :=
    hCloseCommute (indexId + 5) depth formula (by simp)
  have hClose₆ (depth : Nat) (formula : SetFormula) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set
            (indexId + 6) depth formula) =
        Formula.closeFreeAt SetSort.set (indexId + 6) depth
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) formula) :=
    hCloseCommute (indexId + 6) depth formula (by simp)
  have hClose₇ (depth : Nat) (formula : SetFormula) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set
            (indexId + 7) depth formula) =
        Formula.closeFreeAt SetSort.set (indexId + 7) depth
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) formula) :=
    hCloseCommute (indexId + 7) depth formula (by simp)
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := numₘ(index)) hPointwise
  simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
    canonical_binder_shift_token_condition_with_ids,
    canonical_binder_shift_fixed_token_condition_substituteFree,
    Formula.substituteFree, Formula.next_depth,
    Term.substituteFree, set_variable,
    hSourceSubstitute, hTargetSubstitute,
    hClose₁, hClose₂, hClose₃, hClose₄,
    hClose₅, hClose₆, hClose₇,
    GodelQuotation.gq_binder_shift_numeral_substitute] using
    hAtRaw

/--
标准源 token 串和逐点 binder-shift 关系唯一决定目标代码。

证明只使用公式码的有限序列后果、定义域外延和单 token 函数性，不反演公式树。
-/
theorem fs_zfc_support_raw_canonical_binder_shift_code_unique
    {Γ : Context signature}
    {sourceTokens targetTokens : List Nat}
    (relation :
      CanonicalBinderShiftTokens sourceTokens targetTokens)
    (sourceCode targetCode : SetTerm)
    (indexId : FreeVarId)
    (hSourceCode :
      Term.CheckCertificate sourceCode SetSort.set)
    (hTargetCode :
      Term.CheckCertificate targetCode SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceCode ≐ₘ
          GodelQuotation.standard_token_sequence sourceTokens)
    (hSourceFresh :
      ∀ id, indexId ≤ id → id ≤ indexId + 7 →
        (SetSort.set, id) ∉ Term.freeSupport sourceCode)
    (hTargetFresh :
      ∀ id, indexId ≤ id → id ≤ indexId + 7 →
        (SetSort.set, id) ∉ Term.freeSupport targetCode)
    (hContextFresh :
      ∀ formula, formula ∈ Γ →
        ∀ id, indexId ≤ id → id ≤ indexId + 7 →
          (SetSort.set, id) ∉
            Formula.freeSupport formula)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_shift_code_condition_with_ids
          sourceCode targetCode
          indexId (indexId + 1) (indexId + 2)
          (indexId + 3) (indexId + 4)
          (indexId + 5) (indexId + 6)
          (indexId + 7)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      targetCode ≐ₘ
        GodelQuotation.standard_token_sequence targetTokens := by
  rw [canonical_binder_shift_code_condition_with_ids]
    at hCondition
  have hData :=
    FirstOrder.Derives.conjElimLeft hCondition
  have hPointwise :=
    FirstOrder.Derives.conjElimRight hCondition
  have hFormulaData :=
    FirstOrder.Derives.conjElimLeft hData
  have hTargetFormula :=
    FirstOrder.Derives.conjElimRight hFormulaData
  have hDomainEquality :=
    FirstOrder.Derives.conjElimRight hData
  have hTargetMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetCode ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          FirstOrder.Derives.theory_weaken
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_godel_quotation
                hFormula)
            (GodelQuotation.gq_formula_code_definition_instance
              targetCode hTargetCode.admissible))
      hTargetFormula
  have hTargetFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition targetCode := by
    have hCodeString :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          targetCode ∈ₘ CodeStrₘ :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            fs_zfc_support_raw_derives_of_godel_quotation
              (GodelQuotation.gq_formula_code_member_implies_code_string
                targetCode hTargetCode.admissible))
        hTargetMember
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_standard_sequence
            (GodelQuotation.code_string_member_implies_finite_sequence_at
              targetCode hTargetCode.admissible))
      hCodeString
  have hTargetFunction :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        is_function_formula targetCode := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimLeft hTargetFinite
  have hSourceDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sourceCode) ≐ₘ
          numₘ(sourceTokens.length) :=
    GodelQuotation.gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      sourceCode sourceTokens hSourceEquality hSourceCode
  have hTargetDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(targetCode) ≐ₘ
          numₘ(targetTokens.length) := by
    have hTargetSource :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          domₘ(targetCode) ≐ₘ domₘ(sourceCode) :=
      Metatheory.Derives.equality_symm hDomainEquality
    simpa [relation.length_eq] using
      Metatheory.Derives.equality_trans
        hTargetSource hSourceDomain
  apply
    GodelQuotation.gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_standard_sequence_semantics
          hFormula)
      (fun _ hFormula =>
        fs_zfc_support_raw_theory_sentence hFormula)
      targetCode targetTokens
      hTargetFunction hTargetDomain
      (hSource := hTargetCode)
  intro index targetToken hTargetGet
  rcases relation.getElem?_source_relation hTargetGet with
    ⟨sourceToken, hSourceGet, tokenRelation⟩
  have hReferencePointGq :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        ((numₘ(index) ∈ₘ
            domₘ(GodelQuotation.standard_token_sequence
              sourceTokens)) ∧ₘ
          ((GodelQuotation.standard_token_sequence
              sourceTokens ·ₘ numₘ(index)) ≐ₘ
            numₘ(sourceToken))) :=
    GodelQuotation.gq_standard_token_sequence_point_inversion
      (GodelQuotation.standard_token_sequence sourceTokens)
      sourceTokens
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set)
        (GodelQuotation.standard_token_sequence sourceTokens))
      hSourceGet
  have hReferencePoint :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ((numₘ(index) ∈ₘ
            domₘ(GodelQuotation.standard_token_sequence
              sourceTokens)) ∧ₘ
          ((GodelQuotation.standard_token_sequence
              sourceTokens ·ₘ numₘ(index)) ≐ₘ
            numₘ(sourceToken))) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_godel_quotation hFormula)
          hReferencePointGq
  have hSourcePoint :=
    GodelQuotation.gq_point_inversion_of_equality_of_theory
      sourceCode
      (GodelQuotation.standard_token_sequence sourceTokens)
      (numₘ(index)) (numₘ(sourceToken))
      hSourceEquality hReferencePoint
      (hLeft := hSourceCode)
  have hAt :=
    fs_zfc_support_raw_canonical_binder_shift_point_at
      index sourceCode targetCode indexId
      (hSourceFresh indexId (Nat.le_refl indexId)
        (Nat.le_add_right indexId 7))
      (hTargetFresh indexId (Nat.le_refl indexId)
        (Nat.le_add_right indexId 7))
      hPointwise
  have hTokenCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_shift_token_condition_with_ids
          (sourceCode ·ₘ numₘ(index))
          (targetCode ·ₘ numₘ(index))
          (indexId + 1) (indexId + 2)
          (indexId + 3) (indexId + 4)
          (indexId + 5) (indexId + 6)
          (indexId + 7) :=
    FirstOrder.Derives.impElim hAt
      (FirstOrder.Derives.conjElimLeft hSourcePoint)
  have hSourceAt :
      Term.Admissible
        (sourceCode ·ₘ numₘ(index)) SetSort.set :=
    function_application_term_admissible
      sourceCode (numₘ(index))
      hSourceCode.admissible
      (finite_numeral_term_admissible index)
  have hTargetAt :
      Term.Admissible
        (targetCode ·ₘ numₘ(index)) SetSort.set :=
    function_application_term_admissible
      targetCode (numₘ(index))
      hTargetCode.admissible
      (finite_numeral_term_admissible index)
  have hSourceAtFresh :
      ∀ id, indexId + 1 ≤ id →
        id ≤ indexId + 7 →
        (SetSort.set, id) ∉
          Term.freeSupport
            (sourceCode ·ₘ numₘ(index)) := by
    intro id hLower hUpper
    simpa [Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport] using
      hSourceFresh id
        (Nat.le_trans (Nat.le_add_right indexId 1) hLower)
        hUpper
  have hTargetAtFresh :
      ∀ id, indexId + 1 ≤ id →
        id ≤ indexId + 7 →
        (SetSort.set, id) ∉
          Term.freeSupport
            (targetCode ·ₘ numₘ(index)) := by
    intro id hLower hUpper
    simpa [Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport] using
      hTargetFresh id
        (Nat.le_trans (Nat.le_add_right indexId 1) hLower)
        hUpper
  exact
    fs_zfc_support_raw_canonical_binder_shift_token_unique
      tokenRelation
      (sourceCode ·ₘ numₘ(index))
      (targetCode ·ₘ numₘ(index))
      (indexId + 1)
      hSourceAt hTargetAt
      (FirstOrder.Derives.conjElimRight hSourcePoint)
      hSourceAtFresh hTargetAtFresh
      (by
        intro formula hFormula id hLower hUpper
        exact hContextFresh formula hFormula id
          (Nat.le_trans
            (Nat.le_add_right indexId 1) hLower)
          hUpper)
      hTokenCondition

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
