import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalPayloadFailureInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCanonicalBinderShiftInversion.Code
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Support.Base
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Substitution.Transport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.FormulaConstruction
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoderShift
/-! # 一阶逻辑基础证书的有限失败适配：只组合既有反演，不公开 trace。 -/
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
namespace CertifiedProof
/-- 对象变量项只含自身这一自由变量。 -/
theorem fs_zfc_fo_failure_set_variable_fresh
    (source target : FreeVarId)
    (hNe : source ≠ target) :
    (SetSort.set, source) ∉ Term.freeSupport (x#target) := by
  intro hMember
  exact hNe <| congrArg Prod.snd <|
    List.mem_singleton.mp hMember
/-- 对象变量作用于闭 numeral 后仍保持同样的自由变量支持。 -/
theorem fs_zfc_fo_failure_application_numeral_fresh
    (source target : FreeVarId)
    (value : Nat)
    (hNe : source ≠ target) :
    (SetSort.set, source) ∉
      Term.freeSupport (x#target ·ₘ numₘ(value)) := by
  intro hMember
  simp [Term.freeSupport, Term.freeSupportList,
    finite_numeral_term_freeSupport] at hMember
  exact fs_zfc_fo_failure_set_variable_fresh
    source target hNe hMember
/-- 不同于全部局部 binder 的自由变量在整层存在闭包中仍出现。 -/
theorem fs_zfc_fo_failure_mem_exists_assignments
    (assignments : List (FreeVarId × SetTerm))
    (body : SetFormula)
    (freeVariable : SetSort × FreeVarId)
    (hFresh :
      ∀ assignment, assignment ∈ assignments →
        freeVariable ≠ (SetSort.set, assignment.1))
    (hMember :
      freeVariable ∈ Formula.freeSupport body) :
    freeVariable ∈
      Formula.freeSupport
        (Formula.existsFreeAssignments
          SetSort.set assignments body) := by
  induction assignments with
  | nil =>
      simpa [Formula.existsFreeAssignments] using hMember
  | cons assignment assignments ih =>
      rcases assignment with ⟨id, witness⟩
      have hTail :
          freeVariable ∈
            Formula.freeSupport
              (Formula.existsFreeAssignments
                SetSort.set assignments body) :=
        ih
          (fun assignment hAssignment =>
            hFresh assignment (by simp [hAssignment]))
      simp only [Formula.existsFreeAssignments, Formula.freeSupport]
      exact
        (Formula.mem_freeSupport_closeFreeAt_iff
          freeVariable SetSort.set id 0
          (Formula.existsFreeAssignments
            SetSort.set assignments body)).2
          ⟨hTail, hFresh (id, witness) (by simp)⟩
/-- 两个标准子公式码的对象等式直接拼成标准蕴含码。 -/
theorem fs_zfc_support_raw_implication_code_eq_standard
    {Γ : Context signature}
    (leftTokens rightTokens : List Nat)
    (left right : SetTerm)
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set)
    (hLeftEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        left ≐ₘ standard_token_sequence leftTokens)
    (hRightEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        right ≐ₘ standard_token_sequence rightTokens) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      imp_codeₘ(left, right) ≐ₘ
        standard_token_sequence
          (Numbered.implication_tokens
            leftTokens rightTokens) := by
  have hCongruence :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        imp_codeₘ(left, right) ≐ₘ
          imp_codeₘ(
            standard_token_sequence leftTokens,
            standard_token_sequence rightTokens) :=
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      (fun left right => imp_codeₘ(left, right))
      (fun left right hLeft hRight =>
        implication_formula_code_term_admissible
          left right hLeft hRight)
      (by intros; simp [Term.substituteFree])
      left (standard_token_sequence leftTokens)
      right (standard_token_sequence rightTokens)
      hLeft.admissible
      (standard_token_sequence_admissible leftTokens)
      hRight.admissible
      (standard_token_sequence_admissible rightTokens)
      hLeftEquality hRightEquality
  have hStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        imp_codeₘ(
            standard_token_sequence leftTokens,
            standard_token_sequence rightTokens) ≐ₘ
          standard_token_sequence
            (Numbered.implication_tokens
              leftTokens rightTokens) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <|
          implication_formula_code_eq_standard_token_sequence
            leftTokens rightTokens
            (standard_token_sequence leftTokens)
            (standard_token_sequence rightTokens)
            (FirstOrder.Derives.eq_refl_m
              (standard_token_sequence leftTokens))
            (FirstOrder.Derives.eq_refl_m
              (standard_token_sequence rightTokens))
  exact Metatheory.Derives.equality_trans
    hCongruence hStandard
/-- 从右结合的有限字段合取中按成员关系取出指定字段。 -/
theorem fs_zfc_fo_failure_conjunction_elim
    {Γ : Context signature}
    (fields : List SetFormula)
    (field : SetFormula)
    (hField : field ∈ fields)
    (hFields :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_certificate_conjunction fields) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] field := by
  induction fields generalizing field with
  | nil =>
      simp at hField
  | cons head tail ih =>
      cases tail with
      | nil =>
          have hEqual : field = head := by
            simpa using hField
          subst field
          simpa [logical_certificate_conjunction] using hFields
      | cons next rest =>
          rcases List.mem_cons.mp hField with rfl | hField
          · simpa [logical_certificate_conjunction] using
              FirstOrder.Derives.conjElimLeft hFields
          · exact ih field hField <| by
              simpa [logical_certificate_conjunction] using
                FirstOrder.Derives.conjElimRight hFields

/-! ## tag 7 的项载体反演 -/

/--
对象项码在 ZFC 支持理论中仍给出有限序列。证明只把既有 GQ 反演沿理论包含
提升；它是 specialization 载体反演的局部适配，不引入新的 replay 层。
-/
theorem fs_zfc_support_raw_term_code_implies_finite_sequence
    {Γ : Context signature}
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hPredicate :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] term_codeₘ(code)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      finite_sequence_condition code := by
  let premise : SetFormula := term_codeₘ(code)
  have hPremise :
      Formula.Admissible premise := by
    simpa [premise] using Formula.Admissible.rel
      (by simpa [signature] using
        (ArgsAdmissible.cons hCode ArgsAdmissible.nil))
  have hGQ :
      [premise] ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition code :=
    gq_term_code_implies_finite_sequence
      code hCode
      (FirstOrder.Derives.assumption
        (by simp [premise])
        (Formula.check_admissible_complete hPremise))
  have hGQRaw :
      [premise] ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition code :=
    FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      hGQ
  exact FirstOrder.Derives.cut hPredicate <|
    FirstOrder.Derives.context_weaken
      (Γ := [premise]) (Δ := premise :: Γ)
      (by intro formula hFormula; simp_all)
      hGQRaw

/--
括号三段码的第一项定义域属于整个码定义域。该包装把 GQ 的纯序列事实提升到
raw theory，供 tag 7 的反身等式载体长度消去直接调用。
-/
theorem fs_zfc_support_raw_bracketed_first_domain_mem
    {Γ : Context signature}
    (first middle last : SetTerm)
    (hFirst : Term.CheckCertificate first SetSort.set)
    (hMiddle : Term.CheckCertificate middle SetSort.set)
    (hLast : Term.CheckCertificate last SetSort.set)
    (hFirstFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition first)
    (hMiddleFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition middle)
    (hLastFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition last) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      domₘ(first) ∈ₘ
        domₘ(binary_atomic_formula_code_term middle first last) := by
  let premises : Context signature := [
    finite_sequence_condition first,
    finite_sequence_condition middle,
    finite_sequence_condition last]
  have hGQ :
      premises ⊢ₘ[godel_quotation_theory]
        domₘ(first) ∈ₘ
          domₘ(binary_atomic_formula_code_term middle first last) :=
    gq_bracketed_three_part_first_domain_mem_code_domain
      first middle last
      (FirstOrder.Derives.assumption (by simp [premises]))
      (FirstOrder.Derives.assumption (by simp [premises]))
      (FirstOrder.Derives.assumption (by simp [premises]))
      (hFirstCheck := hFirst)
      (hMiddleCheck := hMiddle)
      (hLastCheck := hLast)
  apply FirstOrder.Derives.multi_cut
    (premises := premises)
  · intro formula hFormula
    simp only [premises, List.mem_cons, List.not_mem_nil,
      or_false] at hFormula
    rcases hFormula with rfl | rfl | rfl
    · exact hFirstFinite
    · exact hMiddleFinite
    · exact hLastFinite
  · exact
      (FirstOrder.Derives.theory_weaken
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_godel_quotation hFormula)
        hGQ).context_weaken_append

/-- 在 raw theory 中按标准父串长度消去子项定义域长度。 -/
theorem fs_zfc_support_raw_domain_length_elim
    {Γ : Context signature}
    (child parent : SetTerm)
    (tokens : List Nat)
    (conclusion : SetFormula)
    (hChild : Term.Admissible child SetSort.set)
    (hParent : Term.CheckCertificate parent SetSort.set)
    (hConclusion : Formula.Admissible conclusion)
    (hMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(child) ∈ₘ domₘ(parent))
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ parent)
    (hBranch :
      ∀ length, length < tokens.length →
        (domₘ(child) ≐ₘ numₘ(length)) :: Γ
          ⊢ₘ[fs_zfc_support_raw_theory] conclusion) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] conclusion := by
  have hParentDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(parent) ≐ₘ numₘ(tokens.length) :=
    GodelQuotation.gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      parent tokens
      (Metatheory.Derives.equality_symm hEquality)
      (hCode := hParent)
  have hLengthMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(child) ∈ₘ numₘ(tokens.length) :=
    FirstOrder.Derives.iffElimRight
      (membership_right_iff_of_equality
        (domₘ(child)) (domₘ(parent))
        (numₘ(tokens.length))
        (domain_term_admissible child hChild)
        (domain_term_admissible parent hParent.admissible)
        (finite_numeral_term_admissible tokens.length)
        hParentDomain)
      hMember
  exact fs_zfc_support_raw_finite_numeral_member_elim_context
    tokens.length (domₘ(child)) conclusion
    (domain_term_admissible child hChild)
    hConclusion hLengthMember hBranch
/-! ## 嵌套 payload 的地面坐标组合 -/
/-- 两层对象 Gödel 配对等式唯一恢复三个自然数坐标。 -/
theorem fs_zfc_support_raw_nested_pair_coordinates
    {Γ : Context signature}
    (raw tag : Nat)
    (payload eigen left right : SetTerm)
    (hPayload : Term.Admissible payload SetSort.set)
    (hEigen : Term.Admissible eigen SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEigenNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] eigen ∈ₘ ωₘ)
    (hLeftNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] left ∈ₘ ωₘ)
    (hRightNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] right ∈ₘ ωₘ)
    (hCertificatePair :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(raw) ≐ₘ
          godel_pairₘ(⟨numₘ(tag), payload⟩ₘ))
    (hPayloadPair :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        payload ≐ₘ
          godel_pairₘ(⟨eigen,
            godel_pairₘ(⟨left, right⟩ₘ)⟩ₘ)) :
    (Γ ⊢ₘ[fs_zfc_support_raw_theory]
      eigen ≐ₘ
        numₘ((godel_unpair_value
          (godel_unpair_value raw).2).1)) ∧
    (Γ ⊢ₘ[fs_zfc_support_raw_theory]
      left ≐ₘ
        numₘ((godel_unpair_value
          (godel_unpair_value
            (godel_unpair_value raw).2).2).1)) ∧
    (Γ ⊢ₘ[fs_zfc_support_raw_theory]
      right ≐ₘ
        numₘ((godel_unpair_value
          (godel_unpair_value
            (godel_unpair_value raw).2).2).2)) := by
  let payloadCode := (godel_unpair_value raw).2
  let payloadPair := godel_unpair_value payloadCode
  let nestedCode := payloadPair.2
  let formulaCodes := godel_unpair_value nestedCode
  let inner := godel_pairₘ(⟨left, right⟩ₘ)
  have hInnerNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] inner ∈ₘ ωₘ := by
    simpa [inner] using
      fs_zfc_support_raw_godel_pairing_mem_omega
        left right hLeft hRight hLeftNatural hRightNatural
  have hPayloadNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] payload ∈ₘ ωₘ :=
    fs_zfc_support_raw_godel_pairing_mem_omega_of_equality
      payload eigen inner hPayload hEigen
      (godel_pairing_term_admissible _ <|
        ordered_pair_term_admissible left right hLeft hRight)
      hEigenNatural hInnerNatural
      (by simpa [inner] using hPayloadPair)
  have hPayloadEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        payload ≐ₘ numₘ(payloadCode) := by
    simpa [payloadCode] using
      ProofT.pair_right_unique
        ProofT.ZFC.pairing_core
        raw tag payload hPayload hPayloadNatural hCertificatePair
  have hPayloadGround :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(payloadCode) ≐ₘ
          godel_pairₘ(⟨eigen, inner⟩ₘ) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hPayloadEquality)
      (by simpa [inner] using hPayloadPair)
  have hEigenEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        eigen ≐ₘ numₘ(payloadPair.1) := by
    simpa [payloadPair] using
      ProofT.pair_left_unique
        ProofT.ZFC.pairing_core
        payloadCode eigen inner hEigen
        (godel_pairing_term_admissible _ <|
          ordered_pair_term_admissible left right hLeft hRight)
        hEigenNatural hInnerNatural hPayloadGround
  have hPayloadGround' :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(payloadCode) ≐ₘ
          godel_pairₘ(⟨numₘ(payloadPair.1), inner⟩ₘ) :=
    Metatheory.Derives.equality_trans hPayloadGround <|
      godel_pairing_term_congr_of_equalities
        eigen (numₘ(payloadPair.1)) inner inner
        hEigen (finite_numeral_term_admissible payloadPair.1)
        (godel_pairing_term_admissible _ <|
          ordered_pair_term_admissible left right hLeft hRight)
        (godel_pairing_term_admissible _ <|
          ordered_pair_term_admissible left right hLeft hRight)
        hEigenEquality (FirstOrder.Derives.eq_refl_m inner)
  have hInnerEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        inner ≐ₘ numₘ(nestedCode) := by
    simpa [nestedCode, payloadPair] using
      ProofT.pair_right_unique
        ProofT.ZFC.pairing_core
        payloadCode payloadPair.1 inner
        (godel_pairing_term_admissible _ <|
          ordered_pair_term_admissible left right hLeft hRight)
        hInnerNatural hPayloadGround'
  have hNestedGround :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(nestedCode) ≐ₘ
          godel_pairₘ(⟨left, right⟩ₘ) := by
    simpa [inner] using
      Metatheory.Derives.equality_symm hInnerEquality
  have hLeftEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        left ≐ₘ numₘ(formulaCodes.1) := by
    simpa [formulaCodes] using
      ProofT.pair_left_unique
        ProofT.ZFC.pairing_core
        nestedCode left right hLeft hRight
        hLeftNatural hRightNatural hNestedGround
  have hNestedGround' :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(nestedCode) ≐ₘ
          godel_pairₘ(⟨numₘ(formulaCodes.1), right⟩ₘ) :=
    Metatheory.Derives.equality_trans hNestedGround <|
      godel_pairing_term_congr_of_equalities
        left (numₘ(formulaCodes.1)) right right
        hLeft (finite_numeral_term_admissible formulaCodes.1)
        hRight hRight hLeftEquality
        (FirstOrder.Derives.eq_refl_m right)
  have hRightEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        right ≐ₘ numₘ(formulaCodes.2) := by
    simpa [formulaCodes] using
      ProofT.pair_right_unique
        ProofT.ZFC.pairing_core
        nestedCode formulaCodes.1 right hRight
        hRightNatural hNestedGround'
  exact ⟨by simpa [payloadCode, payloadPair] using hEigenEquality,
    by simpa [payloadCode, payloadPair, nestedCode, formulaCodes] using
      hLeftEquality,
    by simpa [payloadCode, payloadPair, nestedCode, formulaCodes] using
      hRightEquality⟩
/-! ## canonical 闭包的函数性消费 -/
/-- 标准源码与逐 token `binder-shift` 关系唯一决定对象条件中的目标码。 -/
private theorem fs_zfc_support_raw_canonical_binder_shift_unique_imp
    (sourceTokens shiftedTokens : List Nat)
    (relation : CanonicalBinderShiftTokens sourceTokens shiftedTokens)
    (sourceCode shiftedCode : SetTerm)
    (hSource : Term.CheckCertificate sourceCode SetSort.set)
    (hShifted : Term.CheckCertificate shiftedCode SetSort.set)
    (hSourceFresh :
      ∀ id, 462 ≤ id → id ≤ 469 →
        (SetSort.set, id) ∉ Term.freeSupport sourceCode)
    (hShiftedFresh :
      ∀ id, 462 ≤ id → id ≤ 469 →
        (SetSort.set, id) ∉ Term.freeSupport shiftedCode) :
    Derives fs_zfc_support_raw_theory [] (
      sourceCode ≐ₘ standard_token_sequence sourceTokens ⟶ₘ
        canonical_binder_shift_code_condition_with_ids
            sourceCode shiftedCode
            462 463 464 465 466 467 468 469 ⟶ₘ
          shiftedCode ≐ₘ standard_token_sequence shiftedTokens) := by
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck := by prove_nd_formula_check)
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck := by prove_nd_formula_check)
  let shiftCondition : SetFormula :=
    canonical_binder_shift_code_condition_with_ids
      sourceCode shiftedCode 462 463 464 465 466 467 468 469
  let sourceEquality : SetFormula :=
    sourceCode ≐ₘ standard_token_sequence sourceTokens
  let Γ : Context signature := [shiftCondition, sourceEquality]
  apply fs_zfc_support_raw_canonical_binder_shift_code_unique
    relation sourceCode shiftedCode 462 hSource hShifted
  · exact FirstOrder.Derives.assumption (by simp)
  · exact hSourceFresh
  · exact hShiftedFresh
  · intro formula hFormula id hLower hUpper
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hFormula
    rcases hFormula with rfl | rfl
    · intro hMember
      rcases
          canonical_binder_shift_code_condition_with_ids_freeSupport_subset
            sourceCode shiftedCode 462 463 464 465 466 467 468 469
            (SetSort.set, id) hMember with hMember | hMember
      · exact hSourceFresh id hLower hUpper hMember
      · exact hShiftedFresh id hLower hUpper hMember
    · simpa [sourceEquality, Formula.freeSupport,
        Term.freeSupport, Term.freeSupportList,
        standard_token_sequence_freeSupport_nil] using
        hSourceFresh id hLower hUpper
  · exact FirstOrder.Derives.assumption (by simp)
/-- 同输入的标准 token 代换规格与对象规格唯一决定候选体码。 -/
theorem fs_zfc_support_raw_code_substitution_unique_imp
    (shiftedTokens : List Nat)
    (eigen : Nat)
    (shiftedCode variableCode bodyCode : SetTerm)
    (hShifted : Term.CheckCertificate shiftedCode SetSort.set)
    (hVariable : Term.CheckCertificate variableCode SetSort.set)
    (hBody : Term.CheckCertificate bodyCode SetSort.set)
    (hFresh :
      ReservedIdsFresh [310, 311]
        [shiftedCode, variableCode,
          canonical_outer_binder_variable_code_term, bodyCode]) :
    Derives fs_zfc_support_raw_theory [] (
      formula_codeₘ(shiftedCode) ⟶ₘ
        shiftedCode ≐ₘ standard_token_sequence shiftedTokens ⟶ₘ
          variableCode ≐ₘ standard_token_sequence
              [Numbered.variable_token (free_name eigen)] ⟶ₘ
            code_substitution_spec shiftedCode variableCode
                canonical_outer_binder_variable_code_term bodyCode ⟶ₘ
              bodyCode ≐ₘ standard_token_sequence
                (substitute_tokens shiftedTokens
                  (Numbered.variable_token (free_name eigen))
                  [Numbered.variable_token (bound_name 0)])) := by
  repeat'
    apply FirstOrder.Derives.impIntro
      (hAntecedentCheck := by prove_nd_formula_check)
  let bodyTokens :=
    substitute_tokens shiftedTokens
      (Numbered.variable_token (free_name eigen))
      [Numbered.variable_token (bound_name 0)]
  let shiftedFormula : SetFormula := formula_codeₘ(shiftedCode)
  let shiftedEquality : SetFormula :=
    shiftedCode ≐ₘ standard_token_sequence shiftedTokens
  let variableEquality : SetFormula :=
    variableCode ≐ₘ standard_token_sequence
      [Numbered.variable_token (free_name eigen)]
  let specification : SetFormula :=
    code_substitution_spec shiftedCode variableCode
      canonical_outer_binder_variable_code_term bodyCode
  let Γ : Context signature :=
    [specification, variableEquality, shiftedEquality, shiftedFormula]
  have hShiftedFormula :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] shiftedFormula :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hShiftedEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] shiftedEquality :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hVariableEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] variableEquality :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hSpecification :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] specification :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hShiftedMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] shiftedCode ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation <|
            gq_formula_code_definition_instance
              shiftedCode hShifted.admissible)
      hShiftedFormula
  have hShiftedUnion :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        shiftedCode ∈ₘ (TermCodeₘ ∪ₘ FormulaCodeₘ) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation <|
            gq_weaken_relation_plane <|
              mem_binary_union_right TermCodeₘ FormulaCodeₘ shiftedCode
                term_code_set_term_admissible
                formula_code_set_term_admissible
                hShifted.admissible)
      hShiftedMember
  have hNamedMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence
            [Numbered.variable_token (free_name eigen)] ∈ₘ VarSymₘ := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
    apply fs_zfc_support_raw_derives_of_godel_quotation
    exact FirstOrder.Derives.iffElimRight
      (membership_left_iff_of_equality
        (Numbered.named_variable_code (free_name eigen))
        (standard_token_sequence
          [Numbered.variable_token (free_name eigen)])
        VarSymₘ
        (variable_code_term_admissible _
          (finite_numeral_term_admissible _))
        (standard_token_sequence_admissible _)
        variable_symbol_set_term_admissible
        (named_variable_code_eq_standard_token_sequence
          (free_name eigen)))
      (named_variable_code_mem_variable_symbols (free_name eigen))
  have hVariableMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] variableCode ∈ₘ VarSymₘ :=
    FirstOrder.Derives.iffElimLeft
      (membership_left_iff_of_equality
        variableCode
        (standard_token_sequence
          [Numbered.variable_token (free_name eigen)])
        VarSymₘ hVariable.admissible
        (standard_token_sequence_admissible _)
        variable_symbol_set_term_admissible
        hVariableEquality)
      hNamedMember
  have hOuterTerm :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        term_codeₘ(canonical_outer_binder_variable_code_term) := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
    apply fs_zfc_support_raw_derives_of_godel_quotation
    exact gq_term_code_of_variable_symbol
      canonical_outer_binder_variable_code_term
      (variable_code_term_admissible _
        (finite_numeral_term_admissible 1))
      (by
        simpa [canonical_outer_binder_variable_code_term] using
          named_variable_code_mem_variable_symbols 1)
  have hPrecondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_precondition shiftedCode variableCode
          canonical_outer_binder_variable_code_term := by
    exact FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro hShiftedUnion hVariableMember)
      hOuterTerm
  let standardShifted := standard_token_sequence shiftedTokens
  let standardVariable :=
    standard_token_sequence [Numbered.variable_token (free_name eigen)]
  let standardBody := standard_token_sequence bodyTokens
  have hStandardMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standardShifted ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (membership_left_iff_of_equality
        shiftedCode standardShifted FormulaCodeₘ
        hShifted.admissible
        (standard_token_sequence_admissible shiftedTokens)
        formula_code_set_term_admissible
        hShiftedEquality)
      hShiftedMember
  have hStandardUnion :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standardShifted ∈ₘ (TermCodeₘ ∪ₘ FormulaCodeₘ) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation <|
            gq_weaken_relation_plane <|
              mem_binary_union_right TermCodeₘ FormulaCodeₘ standardShifted
                term_code_set_term_admissible
                formula_code_set_term_admissible
                (standard_token_sequence_admissible shiftedTokens))
      hStandardMember
  have hStandardPrecondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_precondition standardShifted standardVariable
          canonical_outer_binder_variable_code_term := by
    exact FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro hStandardUnion hNamedMember)
      hOuterTerm
  have hStandardSpec :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_spec standardShifted standardVariable
          canonical_outer_binder_variable_code_term
          standardBody := by
    let standardOuter :=
      standard_token_sequence [Numbered.variable_token (bound_name 0)]
    have hRaw :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          code_substitution_spec standardShifted standardVariable
            standardOuter standardBody := by
      simpa [standardShifted, standardVariable, standardOuter,
        standardBody, bodyTokens] using
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            fs_zfc_support_raw_derives_of_godel_quotation <|
              gq_weaken_standard_sequence <|
                standard_token_sequence_code_substitution_spec
                  shiftedTokens
                  (Numbered.variable_token (free_name eigen))
                  [Numbered.variable_token (bound_name 0)])
    apply GodelQuotation.code_substitution_spec_congr_of_code_equalities
      standardShifted standardShifted
      standardVariable standardVariable
      standardOuter canonical_outer_binder_variable_code_term
      standardBody standardBody
    · exact ⟨standard_token_sequence_admissible _,
        standard_token_sequence_freeSupport_nil _⟩
    · exact ⟨standard_token_sequence_admissible _,
        standard_token_sequence_freeSupport_nil _⟩
    · exact ⟨standard_token_sequence_admissible _,
        standard_token_sequence_freeSupport_nil _⟩
    · exact ⟨standard_token_sequence_admissible _,
        standard_token_sequence_freeSupport_nil _⟩
    · exact ⟨standard_token_sequence_admissible _,
        standard_token_sequence_freeSupport_nil _⟩
    · exact ⟨variable_code_term_admissible _
        (finite_numeral_term_admissible 1), by
          simp [Term.freeSupport, Term.freeSupportList,
            finite_numeral_term_freeSupport]⟩
    · exact ⟨standard_token_sequence_admissible _,
        standard_token_sequence_freeSupport_nil _⟩
    · exact ⟨standard_token_sequence_admissible _,
        standard_token_sequence_freeSupport_nil _⟩
    · exact FirstOrder.Derives.eq_refl_m standardShifted
    · exact FirstOrder.Derives.eq_refl_m standardVariable
    · simpa [standardOuter, canonical_outer_binder_variable_code_term,
        bound_name] using
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            fs_zfc_support_raw_derives_of_godel_quotation <|
              Metatheory.Derives.equality_symm <|
                named_variable_code_eq_standard_token_sequence 1)
    · exact FirstOrder.Derives.eq_refl_m standardBody
    · exact hRaw
  have hStandardFresh :
      ReservedIdsFresh [310, 311]
        [standardShifted, standardVariable,
          canonical_outer_binder_variable_code_term, standardBody] := by
    repeat' apply reserved_ids_fresh_cons_closed
    · exact standard_token_sequence_freeSupport_nil _
    · exact standard_token_sequence_freeSupport_nil _
    · simp [
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
    · exact standard_token_sequence_freeSupport_nil _
    · exact reserved_ids_fresh_nil _
  have hObjectEq :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        bodyCode ≐ₘ
          subst_codeₘ(shiftedCode, variableCode,
            canonical_outer_binder_variable_code_term) := by
    have hFunctional :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation <|
            gq_weaken_substitution_variable <|
              code_substitution_spec_implies_eq_term
                shiftedCode variableCode
                canonical_outer_binder_variable_code_term bodyCode
                hShifted hVariable
                (Term.check_admissible_complete <|
                  variable_code_term_admissible _
                    (finite_numeral_term_admissible 1))
                hBody hFresh
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim hFunctional hPrecondition)
      hSpecification
  have hStandardEq :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standardBody ≐ₘ
          subst_codeₘ(standardShifted, standardVariable,
            canonical_outer_binder_variable_code_term) := by
    have hFunctional :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation <|
            gq_weaken_substitution_variable <|
              code_substitution_spec_implies_eq_term
                standardShifted standardVariable
                canonical_outer_binder_variable_code_term standardBody
                (Term.check_admissible_complete <|
                  standard_token_sequence_admissible shiftedTokens)
                (Term.check_admissible_complete <|
                  standard_token_sequence_admissible _)
                (Term.check_admissible_complete <|
                  variable_code_term_admissible _
                    (finite_numeral_term_admissible 1))
                (Term.check_admissible_complete <|
                  standard_token_sequence_admissible bodyTokens)
                hStandardFresh
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim hFunctional hStandardPrecondition)
      hStandardSpec
  have hInputCongruence :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        subst_codeₘ(shiftedCode, variableCode,
            canonical_outer_binder_variable_code_term) ≐ₘ
          subst_codeₘ(standardShifted, standardVariable,
            canonical_outer_binder_variable_code_term) :=
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      (fun source boundVariable =>
        subst_codeₘ(source, boundVariable,
          canonical_outer_binder_variable_code_term))
      (fun source boundVariable hSource hBoundVariable =>
        code_substitution_term_admissible source boundVariable
          canonical_outer_binder_variable_code_term
          hSource hBoundVariable
          (variable_code_term_admissible _
            (finite_numeral_term_admissible 1)))
      (by
        intro parameter replacement source boundVariable
        have hOne :
            Term.substituteFree SetSort.set parameter replacement (numₘ(1)) =
              numₘ(1) := by
          apply Term.substituteFree_eq_self_of_not_mem
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil
        simp [Term.substituteFree, hOne])
      shiftedCode standardShifted variableCode standardVariable
      hShifted.admissible
      (standard_token_sequence_admissible shiftedTokens)
      hVariable.admissible
      (standard_token_sequence_admissible _)
      hShiftedEquality
      hVariableEquality
  simpa [standardBody, bodyTokens] using
    Metatheory.Derives.equality_trans hObjectEq <|
      Metatheory.Derives.equality_trans hInputCongruence
        (Metatheory.Derives.equality_symm hStandardEq)

/-- 规范源码、变量码与 canonical closure 条件唯一决定全称闭包 token 串。 -/
theorem fs_zfc_support_raw_canonical_forall_closure_unique_imp
    (sourceTokens shiftedTokens : List Nat)
    (eigen : Nat)
    (relation : CanonicalBinderShiftTokens sourceTokens shiftedTokens)
    (sourceCode variableCode targetCode : SetTerm)
    (hSource : Term.CheckCertificate sourceCode SetSort.set)
    (hVariable : Term.CheckCertificate variableCode SetSort.set)
    (hTarget : Term.CheckCertificate targetCode SetSort.set)
    (hSourceShiftFresh :
      ∀ id, 462 ≤ id → id ≤ 469 →
        (SetSort.set, id) ∉ Term.freeSupport sourceCode)
    (hVariableShiftFresh :
      ∀ id, 462 ≤ id → id ≤ 469 →
        (SetSort.set, id) ∉ Term.freeSupport variableCode)
    (hSourceWitnessFresh :
      ∀ id, id = 460 ∨ id = 461 →
        (SetSort.set, id) ∉ Term.freeSupport sourceCode)
    (hVariableWitnessFresh :
      ∀ id, id = 460 ∨ id = 461 →
        (SetSort.set, id) ∉ Term.freeSupport variableCode)
    (hTargetWitnessFresh :
      ∀ id, id = 460 ∨ id = 461 →
        (SetSort.set, id) ∉ Term.freeSupport targetCode)
    (hVariableSubstitutionFresh :
      ∀ id, id = 310 ∨ id = 311 →
        (SetSort.set, id) ∉ Term.freeSupport variableCode) :
    Derives fs_zfc_support_raw_theory [] (
      sourceCode ≐ₘ standard_token_sequence sourceTokens ⟶ₘ
        variableCode ≐ₘ standard_token_sequence
            [Numbered.variable_token (free_name eigen)] ⟶ₘ
          canonical_forall_closure_code_condition
              sourceCode variableCode targetCode ⟶ₘ
            targetCode ≐ₘ standard_token_sequence
              (Numbered.universal_tokens 1
                (substitute_tokens shiftedTokens
                  (Numbered.variable_token (free_name eigen))
                  [Numbered.variable_token (bound_name 0)]))) := by
  let bodyTokens :=
    substitute_tokens shiftedTokens
      (Numbered.variable_token (free_name eigen))
      [Numbered.variable_token (bound_name 0)]
  let conclusion : SetFormula :=
    targetCode ≐ₘ standard_token_sequence
      (Numbered.universal_tokens 1 bodyTokens)
  let sourceEquality : SetFormula :=
    sourceCode ≐ₘ standard_token_sequence sourceTokens
  let variableEquality : SetFormula :=
    variableCode ≐ₘ standard_token_sequence
      [Numbered.variable_token (free_name eigen)]
  let closure : SetFormula :=
    canonical_forall_closure_code_condition
      sourceCode variableCode targetCode
  let closureBody : SetFormula :=
    (((canonical_free_variable_code_condition_with_id
          variableCode 470 ∧ₘ
        canonical_binder_shift_code_condition_with_ids
          sourceCode (x#460)
          462 463 464 465 466 467 468 469) ∧ₘ
      (code_substitution_spec
          (x#460) variableCode
          canonical_outer_binder_variable_code_term
          (x#461) ∧ₘ
        formula_codeₘ(x#461))) ∧ₘ
      (targetCode ≐ₘ
        forall_codeₘ(
          canonical_outer_binder_variable_code_term,
          x#461)))
  let bodyExists : SetFormula :=
    ∃ₘ[SetSort.set, 461], closureBody
  let Γ : Context signature :=
    [closure, variableEquality, sourceEquality]
  have hSourceEqualityAdmissible :
      Formula.Admissible sourceEquality := by
    exact Formula.Admissible.equal hSource.admissible
      (standard_token_sequence_admissible sourceTokens)
  have hVariableEqualityAdmissible :
      Formula.Admissible variableEquality := by
    exact Formula.Admissible.equal hVariable.admissible
      (standard_token_sequence_admissible _)
  have hClosureAdmissible : Formula.Admissible closure := by
    simpa [closure] using
      canonical_forall_closure_code_condition_admissible
        sourceCode variableCode targetCode
        hSource.admissible hVariable.admissible hTarget.admissible
  change Derives fs_zfc_support_raw_theory [] (
    sourceEquality ⟶ₘ variableEquality ⟶ₘ closure ⟶ₘ conclusion)
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck :=
      Formula.check_admissible_complete hSourceEqualityAdmissible)
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck :=
      Formula.check_admissible_complete hVariableEqualityAdmissible)
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck :=
      Formula.check_admissible_complete hClosureAdmissible)
  have hBodyExistsAdmissible : Formula.Admissible bodyExists := by
    have hOpened :=
      Formula.Admissible.exists_openAt
        (term := (x#460 : SetTerm))
        SetSort.set hClosureAdmissible
        (set_variable_admissible 460)
    simpa [bodyExists, closureBody, closure,
      canonical_forall_closure_code_condition,
      canonical_forall_closure_code_condition_with_ids,
      Formula.openAt_closeFreeAt] using hOpened
  have hClosureBodyAdmissible : Formula.Admissible closureBody := by
    have hOpened :=
      Formula.Admissible.exists_openAt
        (term := (x#461 : SetTerm))
        SetSort.set hBodyExistsAdmissible
        (set_variable_admissible 461)
    simpa [bodyExists, closureBody,
      Formula.openAt_closeFreeAt] using hOpened
  have hClosureAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] closure :=
    FirstOrder.Derives.assumption (by simp [Γ])
  nd_apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 460)
    (body := bodyExists)
    (conclusion := conclusion)
    (hBodyCheck :=
      Formula.check_admissible_complete hBodyExistsAdmissible)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    simp only [Γ, List.mem_cons, List.not_mem_nil,
      or_false] at hFormula
    rcases hFormula with rfl | rfl | rfl
    · exact
        not_mem_freeSupport_canonical_forall_closure_code_condition
          (SetSort.set, 460) sourceCode variableCode targetCode
          (hSourceWitnessFresh 460 (Or.inl rfl))
          (hVariableWitnessFresh 460 (Or.inl rfl))
          (hTargetWitnessFresh 460 (Or.inl rfl))
    · simpa [variableEquality, Formula.freeSupport,
        Term.freeSupport, Term.freeSupportList,
        standard_token_sequence_freeSupport_nil] using
        hVariableWitnessFresh 460 (Or.inl rfl)
    · simpa [sourceEquality, Formula.freeSupport,
        Term.freeSupport, Term.freeSupportList,
        standard_token_sequence_freeSupport_nil] using
        hSourceWitnessFresh 460 (Or.inl rfl)
  · simpa [conclusion, Formula.freeSupport,
      Term.freeSupport, Term.freeSupportList,
      standard_token_sequence_freeSupport_nil] using
      hTargetWitnessFresh 460 (Or.inl rfl)
  · simpa [closure, bodyExists, closureBody,
      canonical_forall_closure_code_condition,
      canonical_forall_closure_code_condition_with_ids] using hClosureAt
  · let Δ₁ : Context signature := bodyExists :: Γ
    have hBodyExistsAt :
        Δ₁ ⊢ₘ[fs_zfc_support_raw_theory] bodyExists :=
      FirstOrder.Derives.assumption (by simp [Δ₁])
    nd_apply FirstOrder.Derives.exists_elim
      (T := fs_zfc_support_raw_theory)
      (Γ := Δ₁)
      (sort := SetSort.set)
      (eigen := 461)
      (body := closureBody)
      (conclusion := conclusion)
      (hBodyCheck :=
        Formula.check_admissible_complete hClosureBodyAdmissible)
    · intro formula hFormula
      rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      simp only [Δ₁, List.mem_cons] at hFormula
      rcases hFormula with rfl | hFormula
      · simpa [bodyExists] using
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set 461 0 closureBody
      · simp only [Γ, List.mem_cons, List.not_mem_nil,
          or_false] at hFormula
        rcases hFormula with rfl | rfl | rfl
        · exact
            not_mem_freeSupport_canonical_forall_closure_code_condition
              (SetSort.set, 461) sourceCode variableCode targetCode
              (hSourceWitnessFresh 461 (Or.inr rfl))
              (hVariableWitnessFresh 461 (Or.inr rfl))
              (hTargetWitnessFresh 461 (Or.inr rfl))
        · simpa [variableEquality, Formula.freeSupport,
            Term.freeSupport, Term.freeSupportList,
            standard_token_sequence_freeSupport_nil] using
            hVariableWitnessFresh 461 (Or.inr rfl)
        · simpa [sourceEquality, Formula.freeSupport,
            Term.freeSupport, Term.freeSupportList,
            standard_token_sequence_freeSupport_nil] using
            hSourceWitnessFresh 461 (Or.inr rfl)
    · simpa [conclusion, Formula.freeSupport,
        Term.freeSupport, Term.freeSupportList,
        standard_token_sequence_freeSupport_nil] using
        hTargetWitnessFresh 461 (Or.inr rfl)
    · simpa [bodyExists, closureBody] using hBodyExistsAt
    · let Δ₂ : Context signature := closureBody :: Δ₁
      have hAt :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory] closureBody :=
        FirstOrder.Derives.assumption (by simp [Δ₂])
      have hShift :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            canonical_binder_shift_code_condition_with_ids
              sourceCode (x#460)
              462 463 464 465 466 467 468 469 := by
        simpa [closureBody] using
          FirstOrder.Derives.conjElimRight <|
            FirstOrder.Derives.conjElimLeft <|
              FirstOrder.Derives.conjElimLeft hAt
      have hSpecification :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            code_substitution_spec
              (x#460) variableCode
              canonical_outer_binder_variable_code_term
              (x#461) := by
        simpa [closureBody] using
          FirstOrder.Derives.conjElimLeft <|
            FirstOrder.Derives.conjElimRight <|
              FirstOrder.Derives.conjElimLeft hAt
      have hShiftedFormula :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            formula_codeₘ(x#460) := by
        simpa [canonical_binder_shift_code_condition_with_ids] using
          FirstOrder.Derives.conjElimRight <|
            FirstOrder.Derives.conjElimLeft <|
              FirstOrder.Derives.conjElimLeft hShift
      have hSourceEquality :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory] sourceEquality :=
        FirstOrder.Derives.context_weaken
          (Γ := Γ) (Δ := Δ₂)
          (by intro formula hFormula; simp [Δ₂, Δ₁, hFormula]) <|
            FirstOrder.Derives.assumption (by simp [Γ])
      have hVariableEquality :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory] variableEquality :=
        FirstOrder.Derives.context_weaken
          (Γ := Γ) (Δ := Δ₂)
          (by intro formula hFormula; simp [Δ₂, Δ₁, hFormula]) <|
            FirstOrder.Derives.assumption (by simp [Γ])
      have hShiftedEquality :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            x#460 ≐ₘ standard_token_sequence shiftedTokens := by
        have hFunctional :=
          FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Δ₂) (by simp) <|
              fs_zfc_support_raw_canonical_binder_shift_unique_imp
                sourceTokens shiftedTokens relation sourceCode (x#460)
                hSource (Term.check_certificate_of_admissible <|
                  set_variable_admissible 460)
                hSourceShiftFresh
                (by
                  intro id hLower hUpper
                  exact fs_zfc_fo_failure_set_variable_fresh id 460 <|
                    Nat.ne_of_gt <|
                      Nat.lt_of_lt_of_le
                        (by decide : 460 < 462) hLower)
        exact FirstOrder.Derives.impElim
          (FirstOrder.Derives.impElim hFunctional
            (by simpa [sourceEquality] using hSourceEquality))
          hShift
      have hFresh :
          ReservedIdsFresh [310, 311]
            [(x#460), variableCode,
              canonical_outer_binder_variable_code_term, (x#461)] := by
        intro term hTerm id hId
        simp only [List.mem_cons, List.not_mem_nil,
          or_false] at hTerm hId
        rcases hTerm with rfl | rfl | rfl | rfl
        · exact fs_zfc_fo_failure_set_variable_fresh id 460 <| by
            rcases hId with rfl | rfl <;> decide
        · exact hVariableSubstitutionFresh id hId
        · simp only [Term.freeSupport, Term.freeSupportList,
            finite_numeral_term_freeSupport, List.nil_append]
          intro h
          cases h
        · exact fs_zfc_fo_failure_set_variable_fresh id 461 <| by
            rcases hId with rfl | rfl <;> decide
      have hBodyEquality :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            x#461 ≐ₘ standard_token_sequence bodyTokens := by
        have hFunctional :=
          FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Δ₂) (by simp) <|
              fs_zfc_support_raw_code_substitution_unique_imp
                shiftedTokens eigen (x#460) variableCode (x#461)
                (Term.check_certificate_of_admissible <|
                  set_variable_admissible 460)
                hVariable
                (Term.check_certificate_of_admissible <|
                  set_variable_admissible 461)
                hFresh
        exact FirstOrder.Derives.impElim
          (FirstOrder.Derives.impElim
            (FirstOrder.Derives.impElim
              (FirstOrder.Derives.impElim hFunctional hShiftedFormula)
              hShiftedEquality)
            (by simpa [variableEquality] using hVariableEquality))
          hSpecification
      have hTargetEquality :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            targetCode ≐ₘ
              forall_codeₘ(
                canonical_outer_binder_variable_code_term,
                x#461) := by
        simpa [closureBody] using
          FirstOrder.Derives.conjElimRight hAt
      have hUniversalCongruence :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            forall_codeₘ(
                canonical_outer_binder_variable_code_term,
                x#461) ≐ₘ
              forall_codeₘ(
                canonical_outer_binder_variable_code_term,
                standard_token_sequence bodyTokens) := by
        exact Metatheory.Derives.unary_term_constructor_congr_of_equality
          (fun body =>
            forall_codeₘ(
              canonical_outer_binder_variable_code_term, body))
          (fun body hBody =>
            universal_formula_code_term_admissible
              canonical_outer_binder_variable_code_term body
              (variable_code_term_admissible _
                (finite_numeral_term_admissible 1))
              hBody)
          (by
            intro parameter replacement body
            have hOuter :
                Term.substituteFree SetSort.set parameter replacement
                    canonical_outer_binder_variable_code_term =
                  canonical_outer_binder_variable_code_term := by
              apply Term.substituteFree_eq_self_of_not_mem
              simp [
                Term.freeSupport, Term.freeSupportList,
                finite_numeral_term_freeSupport]
            simp [Term.substituteFree, hOuter])
          (x#461) (standard_token_sequence bodyTokens)
          (set_variable_admissible 461)
          (standard_token_sequence_admissible bodyTokens)
          hBodyEquality
      have hStandardUniversal :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            forall_codeₘ(
                canonical_outer_binder_variable_code_term,
                standard_token_sequence bodyTokens) ≐ₘ
              standard_token_sequence
                (Numbered.universal_tokens 1 bodyTokens) := by
        exact FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ₂) (by simp) <|
            fs_zfc_support_raw_derives_of_godel_quotation <| by
              simpa [canonical_outer_binder_variable_code_term,
                GodelQuotation.Numbered.named_variable_code] using
                universal_formula_code_eq_standard_token_sequence
                  1 bodyTokens
                  (standard_token_sequence bodyTokens)
                  (FirstOrder.Derives.eq_refl_m
                    (standard_token_sequence bodyTokens))
      simpa [conclusion, bodyTokens] using
        Metatheory.Derives.equality_trans hTargetEquality <|
          Metatheory.Derives.equality_trans hUniversalCongruence
            hStandardUniversal

/-- tag 8 的两个公式字段失败或最终公式错配均否定全称分配分支。 -/
theorem fs_zfc_support_raw_logical_forall_distribution_neg_of_check_false
    (raw freeBase : Nat)
    (row : List Nat)
    (decoded : FSDecodedFormula)
    (base : FreeVarId)
    (hBaseLower : 700 ≤ base)
    (hRawBound : raw < freeBase)
    (hTag : (godel_unpair_value raw).1 = 8)
    (hDecode : fs_formula_row_decode freeBase row = some decoded)
    (hCheck :
      fs_logical_base_axiom_check
        freeBase decoded.formula raw = false) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_forall_distribution_certificate_condition_with_ids
        (standard_token_sequence row) (numₘ(raw))
        (base + 42) (base + 43) (base + 44) (base + 45)
        (base + 46) (base + 47) (base + 48) (base + 49)
        (base + 50) (base + 51) (base + 40) (base + 41)) := by
  let payloadId := base + 42
  let eigenId := base + 43
  let leftNumericId := base + 44
  let rightNumericId := base + 45
  let leftId := base + 46
  let rightId := base + 47
  let variableId := base + 48
  let closedImplicationId := base + 49
  let closedLeftId := base + 50
  let closedRightId := base + 51
  let traceId := base + 40
  let indexId := base + 41
  let payloadCode := (godel_unpair_value raw).2
  let payloadPair := godel_unpair_value payloadCode
  let nestedCode := payloadPair.2
  let formulaCodes := godel_unpair_value nestedCode
  let eigen := payloadPair.1
  let leftCode := formulaCodes.1
  let rightCode := formulaCodes.2
  let leftTokens := nat_sequence_decode leftCode
  let rightTokens := nat_sequence_decode rightCode
  let fields : List SetFormula := [
    numₘ(raw) ≐ₘ godel_pairₘ(⟨numₘ(8), x#payloadId⟩ₘ),
    x#payloadId ≐ₘ
      godel_pairₘ(⟨x#eigenId,
        godel_pairₘ(⟨x#leftNumericId, x#rightNumericId⟩ₘ)⟩ₘ),
    x#eigenId ∈ₘ ωₘ,
    logical_formula_payload_component_condition_with_ids
      (x#leftId) (x#leftNumericId) traceId indexId,
    logical_formula_payload_component_condition_with_ids
      (x#rightId) (x#rightNumericId) traceId indexId,
    x#variableId ≐ₘ var_codeₘ(numₘ(2) *ₘ x#eigenId),
    ¬ₘ quantifier_occurs_condition (x#variableId) (x#leftId),
    ¬ₘ quantifier_occurs_condition (x#variableId) (x#rightId),
    canonical_forall_closure_code_condition
      (imp_codeₘ(x#leftId, x#rightId))
      (x#variableId) (x#closedImplicationId),
    canonical_forall_closure_code_condition
      (x#leftId) (x#variableId) (x#closedLeftId),
    canonical_forall_closure_code_condition
      (x#rightId) (x#variableId) (x#closedRightId),
    standard_token_sequence row ≐ₘ
      imp_codeₘ(x#closedImplicationId,
        imp_codeₘ(x#closedLeftId, x#closedRightId))]
  let body := logical_certificate_conjunction fields
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, x#payloadId), (eigenId, x#eigenId),
    (leftNumericId, x#leftNumericId),
    (rightNumericId, x#rightNumericId),
    (leftId, x#leftId), (rightId, x#rightId),
    (variableId, x#variableId),
    (closedImplicationId, x#closedImplicationId),
    (closedLeftId, x#closedLeftId),
    (closedRightId, x#closedRightId)]
  have hCondition :=
    logical_forall_distribution_certificate_condition_with_ids_admissible
      (standard_token_sequence row) (numₘ(raw))
      payloadId eigenId leftNumericId rightNumericId
      leftId rightId variableId closedImplicationId
      closedLeftId closedRightId traceId indexId
      (standard_token_sequence_admissible row)
      (finite_numeral_term_admissible raw)
  have hBody : Formula.Admissible body :=
    fs_zfc_admissible_body_of_exists_assignments assignments body <| by
      simpa [assignments, body, fields, payloadId, eigenId,
        leftNumericId, rightNumericId, leftId, rightId, variableId,
        closedImplicationId, closedLeftId, closedRightId, traceId,
        indexId,
        logical_forall_distribution_certificate_condition_with_ids,
        Formula.existsFreeAssignments] using hCondition
  have hEigenBound : eigen < freeBase := by
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans
        (godel_unpair_value_left_le payloadCode)
        (godel_unpair_value_right_le raw))
      hRawBound
  have hTraceIndex : traceId ≠ indexId := by
    simp [traceId, indexId]
  have hTraceFreshBody :
      (SetSort.set, traceId) ∉ Formula.freeSupport body := by
    intro hMember
    have hConditionMember :
        (SetSort.set, traceId) ∈
          Formula.freeSupport
            (Formula.existsFreeAssignments
              SetSort.set assignments body) :=
      fs_zfc_fo_failure_mem_exists_assignments
        assignments body (SetSort.set, traceId)
        (by
          intro assignment hAssignment
          simp only [assignments, List.mem_cons,
            List.not_mem_nil, or_false] at hAssignment
          rcases hAssignment with
            rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl
          all_goals
            simp [traceId, payloadId, eigenId, leftNumericId,
              rightNumericId, leftId, rightId, variableId,
              closedImplicationId, closedLeftId, closedRightId])
        hMember
    have hSupport :=
      logical_forall_distribution_certificate_condition_with_ids_freeSupport_subset
        (standard_token_sequence row) (numₘ(raw))
        payloadId eigenId leftNumericId rightNumericId
        leftId rightId variableId closedImplicationId
        closedLeftId closedRightId traceId indexId
        (SetSort.set, traceId)
        (by
          simpa [assignments, body, fields,
            logical_forall_distribution_certificate_condition_with_ids,
            Formula.existsFreeAssignments] using hConditionMember)
    rcases hSupport with hSupport | hSupport
    · simp at hSupport
    · simp [finite_numeral_term_freeSupport] at hSupport
  apply fs_zfc_support_raw_exists_assignments_neg assignments body
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck := Formula.check_admissible_complete hBody)
  let Γ : Context signature := [body]
  have hAt : Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hBody)
  have hField :
      ∀ field, field ∈ fields →
        Γ ⊢ₘ[fs_zfc_support_raw_theory] field := by
    intro field hMember
    exact fs_zfc_fo_failure_conjunction_elim
      fields field hMember (by simpa [Γ, body] using hAt)
  have hPair :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(raw) ≐ₘ
          godel_pairₘ(⟨numₘ(8), x#payloadId⟩ₘ) :=
    hField _ (by simp [fields])
  have hPayloadPair :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#payloadId ≐ₘ
          godel_pairₘ(⟨x#eigenId,
            godel_pairₘ(⟨x#leftNumericId, x#rightNumericId⟩ₘ)⟩ₘ) :=
    hField _ (by simp [fields])
  have hEigenNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] x#eigenId ∈ₘ ωₘ :=
    hField _ (by simp [fields])
  have hLeftComponent :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_formula_payload_component_condition_with_ids
          (x#leftId) (x#leftNumericId) traceId indexId :=
    hField _ (by simp [fields])
  have hRightComponent :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_formula_payload_component_condition_with_ids
          (x#rightId) (x#rightNumericId) traceId indexId :=
    hField _ (by simp [fields])
  have hVariableField :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#variableId ≐ₘ var_codeₘ(numₘ(2) *ₘ x#eigenId) :=
    hField _ (by simp [fields])
  have hClosedImplication :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_forall_closure_code_condition
          (imp_codeₘ(x#leftId, x#rightId))
          (x#variableId) (x#closedImplicationId) :=
    hField _ (by simp [fields])
  have hClosedLeft :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_forall_closure_code_condition
          (x#leftId) (x#variableId) (x#closedLeftId) :=
    hField _ (by simp [fields])
  have hClosedRight :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_forall_closure_code_condition
          (x#rightId) (x#variableId) (x#closedRightId) :=
    hField _ (by simp [fields])
  have hFormulaField :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence row ≐ₘ
          imp_codeₘ(x#closedImplicationId,
            imp_codeₘ(x#closedLeftId, x#closedRightId)) :=
    hField _ (by simp [fields])
  have hLeftNatural :=
    (fs_zfc_support_raw_nat_sequence_code_condition_parts
      (x#leftId) (x#leftNumericId) traceId indexId
      (FirstOrder.Derives.conjElimRight hLeftComponent)).2.1
  have hRightNatural :=
    (fs_zfc_support_raw_nat_sequence_code_condition_parts
      (x#rightId) (x#rightNumericId) traceId indexId
      (FirstOrder.Derives.conjElimRight hRightComponent)).2.1
  rcases
      fs_zfc_support_raw_nested_pair_coordinates
        raw 8 (x#payloadId) (x#eigenId)
        (x#leftNumericId) (x#rightNumericId)
        (set_variable_admissible payloadId)
        (set_variable_admissible eigenId)
        (set_variable_admissible leftNumericId)
        (set_variable_admissible rightNumericId)
        hEigenNatural hLeftNatural hRightNatural
        (by simpa [fields] using hPair)
        (by simpa [fields] using hPayloadPair) with
    ⟨hEigenEquality, hLeftNumericEquality, hRightNumericEquality⟩
  have hTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, traceId) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    simp only [Γ, List.mem_singleton] at hFormula
    subst formula
    exact hTraceFreshBody
  cases hLeftDecode :
      fs_named_formula_token_code_decode freeBase leftCode with
  | none =>
      exact
        fs_zfc_support_raw_logical_formula_payload_component_falsum_of_named_decode_none
          (x#leftId) (x#leftNumericId) freeBase leftCode
          traceId indexId hTraceIndex
          (set_variable_admissible leftId)
          (set_variable_admissible leftNumericId)
          (fs_zfc_fo_failure_set_variable_fresh traceId leftId <| by
            simp [traceId, leftId])
          (fs_zfc_fo_failure_set_variable_fresh indexId leftId <| by
            simp [indexId, leftId])
          (fs_zfc_fo_failure_set_variable_fresh indexId leftNumericId <| by
            simp [indexId, leftNumericId])
          hTraceFreshContext hLeftComponent
          (by
            simpa [payloadCode, payloadPair, nestedCode,
              formulaCodes, leftCode] using hLeftNumericEquality)
          (by
            simpa [fs_named_formula_token_code_decode,
              leftTokens] using hLeftDecode)
  | some antecedent =>
      cases hRightDecode :
          fs_named_formula_token_code_decode freeBase rightCode with
      | none =>
          exact
            fs_zfc_support_raw_logical_formula_payload_component_falsum_of_named_decode_none
              (x#rightId) (x#rightNumericId) freeBase rightCode
              traceId indexId hTraceIndex
              (set_variable_admissible rightId)
              (set_variable_admissible rightNumericId)
              (fs_zfc_fo_failure_set_variable_fresh traceId rightId <| by
                simp [traceId, rightId])
              (fs_zfc_fo_failure_set_variable_fresh indexId rightId <| by
                simp [indexId, rightId])
              (fs_zfc_fo_failure_set_variable_fresh indexId rightNumericId <| by
                simp [indexId, rightNumericId])
              hTraceFreshContext hRightComponent
              (by
                simpa [payloadCode, payloadPair, nestedCode,
                  formulaCodes, rightCode] using hRightNumericEquality)
              (by
                simpa [fs_named_formula_token_code_decode,
                  rightTokens] using hRightDecode)
      | some consequent =>
          have hLeftEquality :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                x#leftId ≐ₘ standard_token_sequence leftTokens :=
            fs_zfc_support_raw_logical_formula_payload_component_code_eq_standard
              (x#leftId) (x#leftNumericId) leftCode
              traceId indexId hTraceIndex
              (set_variable_admissible leftId)
              (set_variable_admissible leftNumericId)
              (fs_zfc_fo_failure_set_variable_fresh traceId leftId <| by
                simp [traceId, leftId])
              (fs_zfc_fo_failure_set_variable_fresh indexId leftId <| by
                simp [indexId, leftId])
              (fs_zfc_fo_failure_set_variable_fresh indexId leftNumericId <| by
                simp [indexId, leftNumericId])
              hTraceFreshContext hLeftComponent
              (by
                simpa [payloadCode, payloadPair, nestedCode,
                  formulaCodes, leftCode] using hLeftNumericEquality)
          have hRightEquality :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                x#rightId ≐ₘ standard_token_sequence rightTokens :=
            fs_zfc_support_raw_logical_formula_payload_component_code_eq_standard
              (x#rightId) (x#rightNumericId) rightCode
              traceId indexId hTraceIndex
              (set_variable_admissible rightId)
              (set_variable_admissible rightNumericId)
              (fs_zfc_fo_failure_set_variable_fresh traceId rightId <| by
                simp [traceId, rightId])
              (fs_zfc_fo_failure_set_variable_fresh indexId rightId <| by
                simp [indexId, rightId])
              (fs_zfc_fo_failure_set_variable_fresh indexId rightNumericId <| by
                simp [indexId, rightNumericId])
              hTraceFreshContext hRightComponent
              (by
                simpa [payloadCode, payloadPair, nestedCode,
                  formulaCodes, rightCode] using hRightNumericEquality)
          have hVariableCongruence :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                var_codeₘ(numₘ(2) *ₘ x#eigenId) ≐ₘ
                  var_codeₘ(numₘ(2) *ₘ numₘ(eigen)) :=
            Metatheory.Derives.unary_term_constructor_congr_of_equality
              (fun term => var_codeₘ(numₘ(2) *ₘ term))
              (fun term hTerm =>
                variable_code_term_admissible _ <|
                  natural_multiplication_term_admissible
                    (numₘ(2)) term
                    (finite_numeral_term_admissible 2) hTerm)
              (by
                intros
                simp [Term.substituteFree,
                  Term.substituteFree_eq_self_of_not_mem,
                  finite_numeral_term_freeSupport])
              (x#eigenId) (numₘ(eigen))
              (set_variable_admissible eigenId)
              (finite_numeral_term_admissible eigen)
              (by
                simpa [payloadCode, payloadPair, eigen] using
                  hEigenEquality)
          have hVariableArithmetic :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                var_codeₘ(numₘ(2) *ₘ numₘ(eigen)) ≐ₘ
                  var_codeₘ(numₘ(2 * eigen)) :=
            FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Γ) (by simp) <|
                Metatheory.Derives.equality_symm
                  (fs_zfc_support_raw_variable_code_term_numeral_mul eigen)
          have hVariableStandard :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                x#variableId ≐ₘ standard_token_sequence
                  [Numbered.variable_token (free_name eigen)] := by
            exact Metatheory.Derives.equality_trans hVariableField <|
              Metatheory.Derives.equality_trans hVariableCongruence <|
                Metatheory.Derives.equality_trans hVariableArithmetic <|
                  FirstOrder.Derives.context_weaken
                    (Γ := []) (Δ := Γ) (by simp) <| by
                      apply FirstOrder.Derives.theory_weaken
                        (fun _ hFormula =>
                          fs_zfc_support_raw_contains_godel_quotation
                            hFormula)
                      simpa [GodelQuotation.Numbered.named_variable_code,
                        free_name] using
                        named_variable_code_eq_standard_token_sequence
                          (free_name eigen)
          have hLeftNamed :
              fs_named_hilbert_tokens_decode_with_env
                  freeBase [] leftTokens =
                some antecedent := by
            simpa [fs_named_formula_token_code_decode,
              leftTokens] using hLeftDecode
          have hRightNamed :
              fs_named_hilbert_tokens_decode_with_env
                  freeBase [] rightTokens =
                some consequent := by
            simpa [fs_named_formula_token_code_decode,
              rightTokens] using hRightDecode
          rcases
              fs_named_hilbert_tokens_decode_with_env_binder_close
                freeBase eigen [] leftTokens antecedent
                hEigenBound hLeftNamed with
            ⟨leftShifted, hLeftShift, hLeftBodyDecode⟩
          rcases
              fs_named_hilbert_tokens_decode_with_env_binder_close
                freeBase eigen [] rightTokens consequent
                hEigenBound hRightNamed with
            ⟨rightShifted, hRightShift, hRightBodyDecode⟩
          let closeTokens := fun shifted =>
            Numbered.universal_tokens 1
              (substitute_tokens shifted
                (Numbered.variable_token (free_name eigen))
                [Numbered.variable_token (bound_name 0)])
          let leftClosedTokens := closeTokens leftShifted
          let rightClosedTokens := closeTokens rightShifted
          let implicationShifted :=
            Numbered.implication_tokens leftShifted rightShifted
          let implicationClosedTokens := closeTokens implicationShifted
          have hLeftClosedDecode :
              fs_named_hilbert_tokens_decode_with_env
                  freeBase [] leftClosedTokens =
                some (Formula.forallE SetSort.set
                  (Formula.closeFreeAt SetSort.set eigen 0 antecedent)) := by
            apply fs_named_hilbert_tokens_decode_with_env_universal
            simpa [leftClosedTokens, closeTokens, bound_name] using
              hLeftBodyDecode
          have hRightClosedDecode :
              fs_named_hilbert_tokens_decode_with_env
                  freeBase [] rightClosedTokens =
                some (Formula.forallE SetSort.set
                  (Formula.closeFreeAt SetSort.set eigen 0 consequent)) := by
            apply fs_named_hilbert_tokens_decode_with_env_universal
            simpa [rightClosedTokens, closeTokens, bound_name] using
              hRightBodyDecode
          have hImplicationBodyDecode :
              fs_named_hilbert_tokens_decode_with_env
                  freeBase [bound_name 0]
                  (substitute_tokens implicationShifted
                    (Numbered.variable_token (free_name eigen))
                    [Numbered.variable_token (bound_name 0)]) =
                some (Formula.imp
                  (Formula.closeFreeAt SetSort.set eigen 0 antecedent)
                  (Formula.closeFreeAt SetSort.set eigen 0 consequent)) := by
            simpa [implicationShifted,
              substitute_tokens_implication_tokens] using
              fs_named_hilbert_tokens_decode_with_env_implication
                freeBase [bound_name 0]
                hLeftBodyDecode hRightBodyDecode
          have hImplicationClosedDecode :
              fs_named_hilbert_tokens_decode_with_env
                  freeBase [] implicationClosedTokens =
                some (Formula.forallE SetSort.set
                  (Formula.imp
                    (Formula.closeFreeAt SetSort.set eigen 0 antecedent)
                    (Formula.closeFreeAt SetSort.set eigen 0 consequent))) := by
            apply fs_named_hilbert_tokens_decode_with_env_universal
            simpa [implicationClosedTokens, closeTokens, bound_name] using
              hImplicationBodyDecode
          let candidate : SetFormula :=
            Formula.imp
              (Formula.forallE SetSort.set
                (Formula.imp
                  (Formula.closeFreeAt SetSort.set eigen 0 antecedent)
                  (Formula.closeFreeAt SetSort.set eigen 0 consequent)))
              (Formula.imp
                (Formula.forallE SetSort.set
                  (Formula.closeFreeAt SetSort.set eigen 0 antecedent))
                (Formula.forallE SetSort.set
                  (Formula.closeFreeAt SetSort.set eigen 0 consequent)))
          let expectedTokens :=
            Numbered.implication_tokens implicationClosedTokens
              (Numbered.implication_tokens
                leftClosedTokens rightClosedTokens)
          have hExpectedDecode :
              fs_named_hilbert_tokens_decode_with_env
                  freeBase [] expectedTokens =
                some candidate := by
            exact fs_named_hilbert_tokens_decode_with_env_implication
              freeBase [] hImplicationClosedDecode <|
                fs_named_hilbert_tokens_decode_with_env_implication
                  freeBase [] hLeftClosedDecode hRightClosedDecode
          have hFormulaCheck :
              fs_formula_code_eq decoded.formula candidate = false := by
            simpa [fs_logical_base_axiom_check,
              fs_logical_base_axiom_check_with, hTag,
              payloadCode, payloadPair, nestedCode, formulaCodes,
              eigen, leftCode, rightCode, hLeftDecode, hRightDecode,
              candidate] using hCheck
          have hCandidateDifferent : candidate ≠ decoded.formula :=
            Ne.symm (fs_formula_code_eq_ne_of_false hFormulaCheck)
          have hRowNe : row ≠ expectedTokens := by
            intro hEqual
            have hNamed := fs_formula_row_decode_named_of_some hDecode
            rw [hEqual] at hNamed
            exact hCandidateDifferent <|
              Option.some.inj (hExpectedDecode.symm.trans hNamed)
          have hFreshVariable
              (id offset : Nat) (hUpper : id ≤ 470) :
              (SetSort.set, id) ∉
                Term.freeSupport (x#(base + offset)) :=
            fs_zfc_fo_failure_set_variable_fresh id (base + offset) <| by
              apply Nat.ne_of_lt
              exact Nat.lt_of_le_of_lt hUpper <|
                Nat.lt_of_lt_of_le (by decide : 470 < 700) <|
                  Nat.le_trans hBaseLower
                    (Nat.le_add_right base offset)
          have hImplicationEquality :=
            fs_zfc_support_raw_implication_code_eq_standard
              leftTokens rightTokens (x#leftId) (x#rightId)
              (Term.check_certificate_of_admissible <|
                set_variable_admissible leftId)
              (Term.check_certificate_of_admissible <|
                set_variable_admissible rightId)
              hLeftEquality hRightEquality
          have hClose
              (sourceTokens shiftedTokens : List Nat)
              (relation : CanonicalBinderShiftTokens
                sourceTokens shiftedTokens)
              (source target : SetTerm)
              (hSourceCheck : Term.CheckCertificate source SetSort.set)
              (hTargetCheck : Term.CheckCertificate target SetSort.set)
              (hSource :
                Γ ⊢ₘ[fs_zfc_support_raw_theory]
                  source ≐ₘ standard_token_sequence sourceTokens)
              (hClosure :
                Γ ⊢ₘ[fs_zfc_support_raw_theory]
                  canonical_forall_closure_code_condition
                    source (x#variableId) target)
              (hSourceSupport :
                ∀ id, id ≤ 470 →
                  (SetSort.set, id) ∉ Term.freeSupport source)
              (hTargetSupport :
                ∀ id, id ≤ 470 →
                  (SetSort.set, id) ∉ Term.freeSupport target) :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                target ≐ₘ
                  standard_token_sequence (closeTokens shiftedTokens) := by
            have hFunctional :=
              FirstOrder.Derives.context_weaken
                (Γ := []) (Δ := Γ) (by simp) <|
                  fs_zfc_support_raw_canonical_forall_closure_unique_imp
                    sourceTokens shiftedTokens eigen relation
                    source (x#variableId) target
                    hSourceCheck
                    (Term.check_certificate_of_admissible <|
                      set_variable_admissible variableId)
                    hTargetCheck
                    (by
                      intro id _ hUpper
                      exact hSourceSupport id (Nat.le_trans hUpper (by decide)))
                    (by
                      intro id _ hUpper
                      exact hFreshVariable id 48
                        (Nat.le_trans hUpper (by decide)))
                    (by
                      intro id hId
                      exact hSourceSupport id <| by
                        rcases hId with rfl | rfl <;> decide)
                    (by
                      intro id hId
                      exact hFreshVariable id 48 <| by
                        rcases hId with rfl | rfl <;> decide)
                    (by
                      intro id hId
                      exact hTargetSupport id <| by
                        rcases hId with rfl | rfl <;> decide)
                    (by
                      intro id hId
                      exact hFreshVariable id 48 <| by
                        rcases hId with rfl | rfl <;> decide)
            simpa [closeTokens] using
              FirstOrder.Derives.impElim
                (FirstOrder.Derives.impElim
                  (FirstOrder.Derives.impElim hFunctional hSource)
                  hVariableStandard)
                hClosure
          have hClosedLeftEquality :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                x#closedLeftId ≐ₘ
                  standard_token_sequence leftClosedTokens := by
            simpa [leftClosedTokens] using
              hClose leftTokens leftShifted hLeftShift
                (x#leftId) (x#closedLeftId)
                (Term.check_certificate_of_admissible <|
                  set_variable_admissible leftId)
                (Term.check_certificate_of_admissible <|
                  set_variable_admissible closedLeftId)
                hLeftEquality hClosedLeft
                (by
                  intro id hUpper
                  exact hFreshVariable id 46 hUpper)
                (by
                  intro id hUpper
                  exact hFreshVariable id 50 hUpper)
          have hClosedRightEquality :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                x#closedRightId ≐ₘ
                  standard_token_sequence rightClosedTokens := by
            simpa [rightClosedTokens] using
              hClose rightTokens rightShifted hRightShift
                (x#rightId) (x#closedRightId)
                (Term.check_certificate_of_admissible <|
                  set_variable_admissible rightId)
                (Term.check_certificate_of_admissible <|
                  set_variable_admissible closedRightId)
                hRightEquality hClosedRight
                (by
                  intro id hUpper
                  exact hFreshVariable id 47 hUpper)
                (by
                  intro id hUpper
                  exact hFreshVariable id 51 hUpper)
          have hClosedImplicationEquality :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                x#closedImplicationId ≐ₘ
                  standard_token_sequence implicationClosedTokens := by
            have hSourceSupport :
                  ∀ freshId, freshId ≤ 470 →
                  (SetSort.set, freshId) ∉
                    Term.freeSupport
                      (imp_codeₘ(x#leftId, x#rightId)) := by
              intro freshId hUpper
              have hLeftNe : freshId ≠ leftId := by
                apply Nat.ne_of_lt
                exact Nat.lt_of_le_of_lt hUpper <|
                  Nat.lt_of_lt_of_le (by decide : 470 < 700) <|
                    Nat.le_trans hBaseLower <| by
                      simp [leftId]
              have hRightNe : freshId ≠ rightId := by
                apply Nat.ne_of_lt
                exact Nat.lt_of_le_of_lt hUpper <|
                  Nat.lt_of_lt_of_le (by decide : 470 < 700) <|
                    Nat.le_trans hBaseLower <| by
                      simp [rightId]
              simp only [Term.freeSupport, Term.freeSupportList]
              intro hMember
              rcases List.mem_cons.mp hMember with hLeft | hRight
              · exact hLeftNe (congrArg Prod.snd hLeft)
              · exact hRightNe <| congrArg Prod.snd <|
                  List.mem_singleton.mp hRight
            have hTargetSupport :
                ∀ freshId, freshId ≤ 470 →
                  (SetSort.set, freshId) ∉
                    Term.freeSupport (x#closedImplicationId) := by
              intro freshId hUpper
              exact hFreshVariable freshId 49 hUpper
            simpa [implicationClosedTokens] using
              hClose
                (sourceTokens :=
                  Numbered.implication_tokens leftTokens rightTokens)
                (shiftedTokens := implicationShifted)
                (relation := CanonicalBinderShiftTokens.implication
                  hLeftShift hRightShift)
                (source := imp_codeₘ(x#leftId, x#rightId))
                (target := x#closedImplicationId)
                (Term.check_certificate_of_admissible <|
                  implication_formula_code_term_admissible
                    (x#leftId) (x#rightId)
                    (set_variable_admissible leftId)
                    (set_variable_admissible rightId))
                (Term.check_certificate_of_admissible <|
                  set_variable_admissible closedImplicationId)
                hImplicationEquality hClosedImplication
                hSourceSupport hTargetSupport
          have hTailEquality :=
            fs_zfc_support_raw_implication_code_eq_standard
              leftClosedTokens rightClosedTokens
              (x#closedLeftId) (x#closedRightId)
              (Term.check_certificate_of_admissible <|
                set_variable_admissible closedLeftId)
              (Term.check_certificate_of_admissible <|
                set_variable_admissible closedRightId)
              hClosedLeftEquality hClosedRightEquality
          have hWholeEquality :=
            fs_zfc_support_raw_implication_code_eq_standard
              implicationClosedTokens
              (Numbered.implication_tokens
                leftClosedTokens rightClosedTokens)
              (x#closedImplicationId)
              (imp_codeₘ(x#closedLeftId, x#closedRightId))
              (Term.check_certificate_of_admissible <|
                set_variable_admissible closedImplicationId)
              (Term.check_certificate_of_admissible <|
                implication_formula_code_term_admissible
                  (x#closedLeftId) (x#closedRightId)
                  (set_variable_admissible closedLeftId)
                  (set_variable_admissible closedRightId))
              hClosedImplicationEquality hTailEquality
          have hRowEquality :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                standard_token_sequence row ≐ₘ
                  standard_token_sequence expectedTokens := by
            simpa [fields, expectedTokens] using
              Metatheory.Derives.equality_trans hFormulaField hWholeEquality
          exact FirstOrder.Derives.negElim hRowEquality <|
            FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Γ) (by simp) <|
                fs_zfc_support_raw_derives_of_standard_sequence <|
                  standard_token_sequence_ne hRowNe

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
