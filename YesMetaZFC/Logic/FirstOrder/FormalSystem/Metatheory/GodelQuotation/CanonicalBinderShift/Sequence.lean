import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.CanonicalBinderShift.Core
/-!
# 规范 binder 深度平移的序列与代码层

本模块把基础层的单 token 对象条件提升到整条标准 token 序列，并进一步完成
quotation 代码与标准序列代码之间的等词运输。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false
universe u v w
/-! ## 标准 token 序列的整条对象表示 -/
/--
同步 token 串在一个具体下标等式分支上满足对象层逐点条件。
外层指标占用 `indexId`，七类 token 见证从 `indexId + 1` 连续分配；因此逐点值只
依赖更小的外层指标，不会被内部存在量词捕获。
-/
private theorem canonical_binder_shift_at_index_equality
    {sourceTokens targetTokens : List Nat} (relation :
      CanonicalBinderShiftTokens sourceTokens targetTokens) (indexId : FreeVarId) (index : Nat) (hIndex : index < sourceTokens.length) :
    ⊢ₘ[godel_quotation_theory] ((x#indexId) ≐ₘ numₘ(index)) ⟶ₘ
        canonical_binder_shift_token_condition_with_ids (standard_token_sequence sourceTokens ·ₘ x#indexId) (standard_token_sequence targetTokens ·ₘ x#indexId)
          (indexId + 1) (indexId + 2) (indexId + 3) (indexId + 4) (indexId + 5) (indexId + 6) (indexId + 7) := by
  let sourceSequence :=
    standard_token_sequence sourceTokens
  let targetSequence :=
    standard_token_sequence targetTokens
  let point : SetTerm := x#indexId
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  let sourceToken := sourceTokens[index]
  have hSourceGet :
      sourceTokens[index]? = some sourceToken := by
    simp [sourceToken, List.getElem?_eq_getElem hIndex]
  rcases relation.getElem?_relation hSourceGet with
    ⟨targetToken, hTargetGet, tokenRelation⟩
  have hSource :
      Term.Admissible sourceSequence SetSort.set :=
    standard_token_sequence_admissible sourceTokens
  have hTarget :
      Term.Admissible targetSequence SetSort.set :=
    standard_token_sequence_admissible targetTokens
  have hPoint :
      Term.Admissible point SetSort.set := by
    simpa [point] using set_variable_admissible indexId
  have hNumeral :
      Term.Admissible (numₘ(index)) SetSort.set :=
    finite_numeral_term_admissible index
  have hSourcePoint :
      Term.Admissible (sourceSequence ·ₘ point) SetSort.set :=
    function_application_term_admissible
      sourceSequence point hSource hPoint
  have hTargetPoint :
      Term.Admissible (targetSequence ·ₘ point) SetSort.set :=
    function_application_term_admissible
      targetSequence point hTarget hPoint
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        point ≐ₘ numₘ(index) := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := godel_quotation_theory)
        (Γ := Γ)
        (φ := equality)
        (by simp [Γ]))
  have hSourceArgument :
      Γ ⊢ₘ[godel_quotation_theory] (sourceSequence ·ₘ point) ≐ₘ (sourceSequence ·ₘ numₘ(index)) :=
    function_application_term_congr_argument_of_equality
      sourceSequence point (numₘ(index))
      hSource hPoint hNumeral hEquality
  have hTargetArgument :
      Γ ⊢ₘ[godel_quotation_theory] (targetSequence ·ₘ point) ≐ₘ (targetSequence ·ₘ numₘ(index)) :=
    function_application_term_congr_argument_of_equality
      targetSequence point (numₘ(index))
      hTarget hPoint hNumeral hEquality
  have hSourceAtNumeral :
      Γ ⊢ₘ[godel_quotation_theory] (sourceSequence ·ₘ numₘ(index)) ≐ₘ
          numₘ(sourceToken) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
        simpa [sourceSequence] using
          gq_weaken_standard_sequence (standard_token_sequence_apply_getElem?
              sourceTokens hSourceGet)
  have hTargetAtNumeral :
      Γ ⊢ₘ[godel_quotation_theory] (targetSequence ·ₘ numₘ(index)) ≐ₘ
          numₘ(targetToken) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
        simpa [targetSequence] using
          gq_weaken_standard_sequence (standard_token_sequence_apply_getElem?
              targetTokens hTargetGet)
  have hSourceEquality :
      Γ ⊢ₘ[godel_quotation_theory] (sourceSequence ·ₘ point) ≐ₘ
          numₘ(sourceToken) :=
    Metatheory.Derives.equality_trans
      hSourceArgument hSourceAtNumeral
  have hTargetEquality :
      Γ ⊢ₘ[godel_quotation_theory] (targetSequence ·ₘ point) ≐ₘ
          numₘ(targetToken) :=
    Metatheory.Derives.equality_trans
      hTargetArgument hTargetAtNumeral
  have hSourcePointSupport :
      Term.freeSupport (sourceSequence ·ₘ point) =
        [(SetSort.set, indexId)] := by
    simp [sourceSequence, point,
      Term.freeSupport, Term.freeSupportList,
      standard_token_sequence_freeSupport_nil] <;>
      rfl
  have hTargetPointSupport :
      Term.freeSupport (targetSequence ·ₘ point) =
        [(SetSort.set, indexId)] := by
    simp [targetSequence, point,
      Term.freeSupport, Term.freeSupportList,
      standard_token_sequence_freeSupport_nil] <;>
      rfl
  have hSourceFreshFrom :
      ∀ id, indexId + 1 ≤ id → (SetSort.set, id) ∉
          Term.freeSupport (sourceSequence ·ₘ point) := by
    intro id hLower hMember
    rw [hSourcePointSupport] at hMember
    have hPair : (SetSort.set, id) = (SetSort.set, indexId) :=
      List.mem_singleton.mp hMember
    have hId : id = indexId :=
      congrArg Prod.snd hPair
    have hStrict : indexId < id :=
      Nat.lt_of_succ_le hLower
    rw [hId] at hStrict
    exact (Nat.lt_irrefl indexId) hStrict
  have hTargetFreshFrom :
      ∀ id, indexId + 1 ≤ id → (SetSort.set, id) ∉
          Term.freeSupport (targetSequence ·ₘ point) := by
    intro id hLower hMember
    rw [hTargetPointSupport] at hMember
    have hPair : (SetSort.set, id) = (SetSort.set, indexId) :=
      List.mem_singleton.mp hMember
    have hId : id = indexId :=
      congrArg Prod.snd hPair
    have hStrict : indexId < id :=
      Nat.lt_of_succ_le hLower
    rw [hId] at hStrict
    exact (Nat.lt_irrefl indexId) hStrict
  have hCondition :=
    canonical_binder_shift_token_condition_with_ids_of_values
      tokenRelation (indexId + 1) (sourceSequence ·ₘ point) (targetSequence ·ₘ point)
      hSourcePoint hTargetPoint
      hSourceFreshFrom hTargetFreshFrom
      hSourceEquality hTargetEquality
  simpa [Γ, equality, sourceSequence, targetSequence, point,
    Nat.add_assoc] using hCondition
/-- 同步 token 串在其整个标准定义域上逐点满足对象层平移关系。 -/
theorem canonical_binder_shift_standard_sequences_pointwise
    {sourceTokens targetTokens : List Nat} (relation :
      CanonicalBinderShiftTokens sourceTokens targetTokens) (indexId : FreeVarId) :
    ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, indexId], ((x#indexId ∈ₘ
            domₘ(standard_token_sequence sourceTokens)) ⟶ₘ
          canonical_binder_shift_token_condition_with_ids (standard_token_sequence sourceTokens ·ₘ x#indexId)
            (standard_token_sequence targetTokens ·ₘ x#indexId) (indexId + 1) (indexId + 2) (indexId + 3) (indexId + 4) (indexId + 5)
            (indexId + 6) (indexId + 7)) := by
  let sourceSequence :=
    standard_token_sequence sourceTokens
  let targetSequence :=
    standard_token_sequence targetTokens
  let point : SetTerm := x#indexId
  let conclusion : SetFormula :=
    canonical_binder_shift_token_condition_with_ids (sourceSequence ·ₘ point) (targetSequence ·ₘ point) (indexId + 1) (indexId + 2) (indexId + 3)
      (indexId + 4) (indexId + 5) (indexId + 6) (indexId + 7)
  have hPoint :
      Term.Admissible point SetSort.set := by
    simpa [point] using set_variable_admissible indexId
  have hSource :
      Term.Admissible sourceSequence SetSort.set :=
    standard_token_sequence_admissible sourceTokens
  have hTarget :
      Term.Admissible targetSequence SetSort.set :=
    standard_token_sequence_admissible targetTokens
  have hSourcePoint :
      Term.Admissible (sourceSequence ·ₘ point) SetSort.set :=
    function_application_term_admissible
      sourceSequence point hSource hPoint
  have hTargetPoint :
      Term.Admissible (targetSequence ·ₘ point) SetSort.set :=
    function_application_term_admissible
      targetSequence point hTarget hPoint
  have hConclusion :
      Formula.Admissible conclusion := by
    simpa [conclusion] using
      canonical_binder_shift_token_condition_with_ids_admissible (sourceSequence ·ₘ point) (targetSequence ·ₘ point) (indexId + 1) (indexId + 2) (indexId + 3)
        (indexId + 4) (indexId + 5) (indexId + 6) (indexId + 7)
        hSourcePoint hTargetPoint
  have hCases :
      ⊢ₘ[godel_quotation_theory]
        stdseq_numeral_member_condition
            sourceTokens.length point ⟶ₘ
          conclusion :=
    stdseq_numeral_member_condition_elim_of_theory
      sourceTokens.length point conclusion
      (fun index hIndex => by
        simpa [conclusion, sourceSequence,
          targetSequence, point] using
          canonical_binder_shift_at_index_equality
            relation indexId index hIndex)
  have hDomain :
      Term.Admissible (domₘ(sourceSequence)) SetSort.set :=
    domain_term_admissible sourceSequence hSource
  have hNumeral :
      Term.Admissible (numₘ(sourceTokens.length)) SetSort.set :=
    finite_numeral_term_admissible sourceTokens.length
  have hDomainEq :
      ⊢ₘ[godel_quotation_theory]
        domₘ(sourceSequence) ≐ₘ
          numₘ(sourceTokens.length) := by
    simpa [sourceSequence] using
      gq_weaken_standard_sequence (standard_token_sequence_domain_eq_length
          sourceTokens)
  have hDomainIff :=
    membership_right_iff_of_equality
      point (domₘ(sourceSequence)) (numₘ(sourceTokens.length))
      hPoint hDomain hNumeral hDomainEq
  have hNumeralIff :
      ⊢ₘ[godel_quotation_theory] (point ∈ₘ numₘ(sourceTokens.length)) ↔ₘ
          stdseq_numeral_member_condition
            sourceTokens.length point :=
    gq_weaken_standard_sequence (stdseq_numeral_member_iff
        sourceTokens.length point hPoint)
  have hOpen :
      ⊢ₘ[godel_quotation_theory] (point ∈ₘ domₘ(sourceSequence)) ⟶ₘ
          conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    have hMembership :
        [point ∈ₘ domₘ(sourceSequence)]
          ⊢ₘ[godel_quotation_theory]
            point ∈ₘ domₘ(sourceSequence) :=
      FirstOrder.Derives.assumption (by simp)
    have hNumeralMembership :=
      FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons
          hDomainIff)
        hMembership
    have hCondition :=
      FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons
          hNumeralIff)
        hNumeralMembership
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hCases)
      hCondition
  have hTheoryFresh :
      ∀ formula, godel_quotation_theory formula → (SetSort.set, indexId) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    rw [(godel_quotation_theory_sentence hFormula).2]
    exact List.not_mem_nil
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := godel_quotation_theory) (Γ := []) (sort := SetSort.set) (eigen := indexId)
      hTheoryFresh (by simp) hOpen
  simpa [sourceSequence, targetSequence,
    point, conclusion] using hGeneralized
/--
同步 token 串的两条标准序列满足完整对象层代码关系。
`formula_codeₘ` 前提由 quotation 正确性层提供；本定理负责定义域一致与整条逐点关系，
从而不把“任意 token 串都是公式”这类错误前提混入同步内核。
-/
theorem canonical_binder_shift_standard_sequences_code_condition_with_ids
    {sourceTokens targetTokens : List Nat} (relation :
      CanonicalBinderShiftTokens sourceTokens targetTokens) (hSourceFormula :
      ⊢ₘ[godel_quotation_theory]
        formula_codeₘ(
          standard_token_sequence sourceTokens)) (hTargetFormula :
      ⊢ₘ[godel_quotation_theory]
        formula_codeₘ(
          standard_token_sequence targetTokens)) (indexId : FreeVarId) :
    ⊢ₘ[godel_quotation_theory]
      canonical_binder_shift_code_condition_with_ids (standard_token_sequence sourceTokens) (standard_token_sequence targetTokens)
        indexId (indexId + 1) (indexId + 2) (indexId + 3) (indexId + 4) (indexId + 5) (indexId + 6) (indexId + 7) := by
  let sourceSequence :=
    standard_token_sequence sourceTokens
  let targetSequence :=
    standard_token_sequence targetTokens
  have hSource :
      Term.Admissible sourceSequence SetSort.set :=
    standard_token_sequence_admissible sourceTokens
  have hTarget :
      Term.Admissible targetSequence SetSort.set :=
    standard_token_sequence_admissible targetTokens
  have hSourceDomain :
      ⊢ₘ[godel_quotation_theory]
        domₘ(sourceSequence) ≐ₘ
          numₘ(sourceTokens.length) := by
    simpa [sourceSequence] using
      gq_weaken_standard_sequence (standard_token_sequence_domain_eq_length
          sourceTokens)
  have hTargetDomain :
      ⊢ₘ[godel_quotation_theory]
        domₘ(targetSequence) ≐ₘ
          numₘ(sourceTokens.length) := by
    simpa [targetSequence, relation.length_eq] using
      gq_weaken_standard_sequence (standard_token_sequence_domain_eq_length
          targetTokens)
  have hTargetDomainSymm :
      ⊢ₘ[godel_quotation_theory]
        numₘ(sourceTokens.length) ≐ₘ
          domₘ(targetSequence) :=
    Metatheory.Derives.equality_symm hTargetDomain
  have hDomainEquality :
      ⊢ₘ[godel_quotation_theory]
        domₘ(sourceSequence) ≐ₘ
          domₘ(targetSequence) :=
    Metatheory.Derives.equality_trans hSourceDomain hTargetDomainSymm
  have hPointwise :=
    canonical_binder_shift_standard_sequences_pointwise
      relation indexId
  rw [canonical_binder_shift_code_condition_with_ids]
  exact FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro (by simpa [sourceSequence] using hSourceFormula)
        (by simpa [targetSequence] using hTargetFormula)) (by simpa [sourceSequence, targetSequence] using
        hDomainEquality))
    hPointwise
/--
两组闭代码等式把显式编号的整条 binder-shift 条件从参考代码运输回实际代码。
内部八个见证占用 `indexId` 到 `indexId + 7`；两次 Leibniz 运输分别使用后续两个
编号，因此不会与关系自身的量词闭包相互捕获。该层是 quotation 原始码与标准
token 序列之间的统一桥。
-/
theorem canonical_binder_shift_code_condition_with_ids_of_equalities
    {Γ : Context signature} (indexId : FreeVarId) (sourceCode targetCode sourceReference targetReference : SetTerm)
    (hSourceCode : Numbered.CodeBoundary sourceCode) (hTargetCode : Numbered.CodeBoundary targetCode) (hSourceReference : Numbered.CodeBoundary sourceReference)
    (hTargetReference : Numbered.CodeBoundary targetReference) (hSourceEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        sourceCode ≐ₘ sourceReference) (hTargetEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        targetCode ≐ₘ targetReference) (hReferenceCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        canonical_binder_shift_code_condition_with_ids
          sourceReference targetReference
          indexId (indexId + 1) (indexId + 2) (indexId + 3) (indexId + 4) (indexId + 5) (indexId + 6) (indexId + 7)) :
    Γ ⊢ₘ[godel_quotation_theory]
      canonical_binder_shift_code_condition_with_ids
        sourceCode targetCode
        indexId (indexId + 1) (indexId + 2) (indexId + 3) (indexId + 4) (indexId + 5) (indexId + 6) (indexId + 7) := by
  let sourceParameter := indexId + 8
  let targetParameter := indexId + 9
  have hFixed (parameter : FreeVarId) (replacement fixed : SetTerm) (hFixed : Numbered.CodeBoundary fixed) :
      Term.substituteFree SetSort.set parameter replacement fixed =
        fixed :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter replacement fixed (by
        rw [hFixed.2]
        exact List.not_mem_nil)
  have hCloseCommute (parameter closedId : FreeVarId) (depth : Nat) (replacement : SetTerm) (hReplacement : Numbered.CodeBoundary replacement)
      (formula : SetFormula) (hDistinct : parameter ≠ closedId) :
      Formula.substituteFree SetSort.set parameter replacement (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth (Formula.substituteFree SetSort.set parameter
            replacement formula) := by
    exact (Formula.closeFreeAt_substituteFree_comm
        SetSort.set parameter closedId depth replacement formula
        hDistinct hReplacement.1.2 (by
          rw [hReplacement.2]
          exact List.not_mem_nil)).symm
  have hSourceCodeClose (closedId : FreeVarId) (depth : Nat) (formula : SetFormula) (hDistinct : sourceParameter ≠ closedId) :
      Formula.substituteFree SetSort.set sourceParameter sourceCode (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth (Formula.substituteFree SetSort.set sourceParameter
            sourceCode formula) :=
    hCloseCommute sourceParameter closedId depth
      sourceCode hSourceCode formula hDistinct
  have hSourceReferenceClose (closedId : FreeVarId) (depth : Nat) (formula : SetFormula) (hDistinct : sourceParameter ≠ closedId) :
      Formula.substituteFree SetSort.set sourceParameter
          sourceReference (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth (Formula.substituteFree SetSort.set sourceParameter
            sourceReference formula) :=
    hCloseCommute sourceParameter closedId depth
      sourceReference hSourceReference formula hDistinct
  have hTargetCodeClose (closedId : FreeVarId) (depth : Nat) (formula : SetFormula) (hDistinct : targetParameter ≠ closedId) :
      Formula.substituteFree SetSort.set targetParameter targetCode (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth (Formula.substituteFree SetSort.set targetParameter
            targetCode formula) :=
    hCloseCommute targetParameter closedId depth
      targetCode hTargetCode formula hDistinct
  have hTargetReferenceClose (closedId : FreeVarId) (depth : Nat) (formula : SetFormula) (hDistinct : targetParameter ≠ closedId) :
      Formula.substituteFree SetSort.set targetParameter
          targetReference (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth (Formula.substituteFree SetSort.set targetParameter
            targetReference formula) :=
    hCloseCommute targetParameter closedId depth
      targetReference hTargetReference formula hDistinct
  have hTargetReferenceFixedBySourceCode :
      Term.substituteFree SetSort.set sourceParameter
          sourceCode targetReference =
        targetReference :=
    hFixed sourceParameter sourceCode targetReference
      hTargetReference
  have hTargetReferenceFixedBySourceReference :
      Term.substituteFree SetSort.set sourceParameter
          sourceReference targetReference =
        targetReference :=
    hFixed sourceParameter sourceReference targetReference
      hTargetReference
  have hSourceCodeFixedByTargetCode :
      Term.substituteFree SetSort.set targetParameter
          targetCode sourceCode =
        sourceCode :=
    hFixed targetParameter targetCode sourceCode hSourceCode
  have hSourceCodeFixedByTargetReference :
      Term.substituteFree SetSort.set targetParameter
          targetReference sourceCode =
        sourceCode :=
    hFixed targetParameter targetReference sourceCode hSourceCode
  let sourceBody : SetFormula :=
    canonical_binder_shift_code_condition_with_ids (x#sourceParameter) targetReference
      indexId (indexId + 1) (indexId + 2) (indexId + 3) (indexId + 4) (indexId + 5) (indexId + 6) (indexId + 7)
  have hSourceIffRaw :=
    Metatheory.Derives.equality_iff_of_equality (T := godel_quotation_theory) (Γ := Γ) (sort := SetSort.set) (eigen := sourceParameter)
      (left := sourceCode) (right := sourceReference) (body := sourceBody)
      hSourceEquality
  have hSourceIff :
      Γ ⊢ₘ[godel_quotation_theory]
        canonical_binder_shift_code_condition_with_ids
            sourceCode targetReference
            indexId (indexId + 1) (indexId + 2) (indexId + 3) (indexId + 4) (indexId + 5) (indexId + 6) (indexId + 7) ↔ₘ
          canonical_binder_shift_code_condition_with_ids
            sourceReference targetReference
            indexId (indexId + 1) (indexId + 2) (indexId + 3) (indexId + 4) (indexId + 5) (indexId + 6) (indexId + 7) := by
    simpa [sourceBody, sourceParameter,
      canonical_binder_shift_code_condition_with_ids,
      canonical_binder_shift_token_condition_with_ids,
      Formula.substituteFree, Formula.next_depth,
      Term.substituteFree, set_variable,
      hTargetReferenceFixedBySourceCode,
      hTargetReferenceFixedBySourceReference,
      hSourceCodeClose, hSourceReferenceClose,
      gq_binder_shift_numeral_substitute] using hSourceIffRaw
  have hAtSource :
      Γ ⊢ₘ[godel_quotation_theory]
        canonical_binder_shift_code_condition_with_ids
          sourceCode targetReference
          indexId (indexId + 1) (indexId + 2) (indexId + 3) (indexId + 4) (indexId + 5) (indexId + 6) (indexId + 7) :=
    FirstOrder.Derives.iffElimLeft
      hSourceIff hReferenceCondition
  let targetBody : SetFormula :=
    canonical_binder_shift_code_condition_with_ids
      sourceCode (x#targetParameter)
      indexId (indexId + 1) (indexId + 2) (indexId + 3) (indexId + 4) (indexId + 5) (indexId + 6) (indexId + 7)
  have hTargetIffRaw :=
    Metatheory.Derives.equality_iff_of_equality (T := godel_quotation_theory) (Γ := Γ) (sort := SetSort.set) (eigen := targetParameter)
      (left := targetCode) (right := targetReference) (body := targetBody)
      hTargetEquality
  have hTargetIff :
      Γ ⊢ₘ[godel_quotation_theory]
        canonical_binder_shift_code_condition_with_ids
            sourceCode targetCode
            indexId (indexId + 1) (indexId + 2) (indexId + 3) (indexId + 4) (indexId + 5) (indexId + 6) (indexId + 7) ↔ₘ
          canonical_binder_shift_code_condition_with_ids
            sourceCode targetReference
            indexId (indexId + 1) (indexId + 2) (indexId + 3) (indexId + 4) (indexId + 5) (indexId + 6) (indexId + 7) := by
    simpa [targetBody, targetParameter,
      canonical_binder_shift_code_condition_with_ids,
      canonical_binder_shift_token_condition_with_ids,
      Formula.substituteFree, Formula.next_depth,
      Term.substituteFree, set_variable,
      hSourceCodeFixedByTargetCode,
      hSourceCodeFixedByTargetReference,
      hTargetCodeClose, hTargetReferenceClose,
      gq_binder_shift_numeral_substitute] using hTargetIffRaw
  exact FirstOrder.Derives.iffElimLeft
    hTargetIff hAtSource
/--
同一 Hilbert 核公式在相邻入口深度的两次 quotation，直接满足对象层 binder-shift
代码关系。
证明先把两次可计算 quotation 分别运输到同步 token 串的标准序列，再复用整条序列
关系；因此调用方不必重复装配 `FormulaCodeₘ` 成员关系、闭项边界或 quotation 值等式。
-/
theorem quote_hilbert_with?_canonical_binder_shift_code_condition_with_ids
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (formula : Formula σ)
    {sourceNames targetNames : List Nat} (environment :
      CanonicalBinderShiftEnvironment sourceNames targetNames) (depth : Nat)
    {sourceTokens targetTokens : List Nat}
    {sourceCode targetCode : SetTerm} (hSourceTokens :
      Numbered.quote_hilbert_tokens_with?
          free_name bound_name sourceNames depth formula =
        some sourceTokens) (hTargetTokens :
      Numbered.quote_hilbert_tokens_with?
          free_name bound_name targetNames (depth + 1) formula =
        some targetTokens) (hSourceCode :
      Numbered.quote_hilbert_with?
          free_name bound_name sourceNames depth formula =
        some sourceCode) (hTargetCode :
      Numbered.quote_hilbert_with?
          free_name bound_name targetNames (depth + 1) formula =
        some targetCode) (indexId : FreeVarId) :
    ⊢ₘ[godel_quotation_theory]
      canonical_binder_shift_code_condition_with_ids
        sourceCode targetCode
        indexId (indexId + 1) (indexId + 2) (indexId + 3) (indexId + 4) (indexId + 5) (indexId + 6) (indexId + 7) := by
  have hRelation :
      CanonicalBinderShiftTokens sourceTokens targetTokens :=
    quote_hilbert_tokens_with?_canonical_binder_shift
      formula environment depth hSourceTokens hTargetTokens
  have hSourceBoundary : Numbered.CodeBoundary sourceCode :=
    Numbered.quote_hilbert_with?_code_boundary
      free_name bound_name hSourceCode
  have hTargetBoundary : Numbered.CodeBoundary targetCode :=
    Numbered.quote_hilbert_with?_code_boundary
      free_name bound_name hTargetCode
  have hSourceReferenceBoundary :
      Numbered.CodeBoundary (standard_token_sequence sourceTokens) :=
    ⟨standard_token_sequence_admissible sourceTokens,
      standard_token_sequence_freeSupport_nil sourceTokens⟩
  have hTargetReferenceBoundary :
      Numbered.CodeBoundary (standard_token_sequence targetTokens) :=
    ⟨standard_token_sequence_admissible targetTokens,
      standard_token_sequence_freeSupport_nil targetTokens⟩
  have hSourceEquality :
      ⊢ₘ[godel_quotation_theory]
        sourceCode ≐ₘ standard_token_sequence sourceTokens :=
    quote_hilbert_with?_eq_standard_token_sequence
      free_name bound_name hSourceTokens hSourceCode
  have hTargetEquality :
      ⊢ₘ[godel_quotation_theory]
        targetCode ≐ₘ standard_token_sequence targetTokens :=
    quote_hilbert_with?_eq_standard_token_sequence
      free_name bound_name hTargetTokens hTargetCode
  have hSourceReferenceMember :
      ⊢ₘ[godel_quotation_theory]
        standard_token_sequence sourceTokens ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.iffElimRight (membership_left_iff_of_equality
        sourceCode (standard_token_sequence sourceTokens)
        FormulaCodeₘ hSourceBoundary.1
        hSourceReferenceBoundary.1
        formula_code_set_term_admissible
        hSourceEquality) (Numbered.quote_hilbert_with?_formula_code_mem
        free_name bound_name hSourceCode)
  have hTargetReferenceMember :
      ⊢ₘ[godel_quotation_theory]
        standard_token_sequence targetTokens ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.iffElimRight (membership_left_iff_of_equality
        targetCode (standard_token_sequence targetTokens)
        FormulaCodeₘ hTargetBoundary.1
        hTargetReferenceBoundary.1
        formula_code_set_term_admissible
        hTargetEquality) (Numbered.quote_hilbert_with?_formula_code_mem
        free_name bound_name hTargetCode)
  have hReferenceCondition :=
    canonical_binder_shift_standard_sequences_code_condition_with_ids
      hRelation (gq_is_formula_code_of_mem (standard_token_sequence sourceTokens)
        hSourceReferenceBoundary.1 hSourceReferenceMember) (gq_is_formula_code_of_mem (standard_token_sequence targetTokens)
        hTargetReferenceBoundary.1 hTargetReferenceMember)
      indexId
  exact canonical_binder_shift_code_condition_with_ids_of_equalities
    indexId sourceCode targetCode (standard_token_sequence sourceTokens) (standard_token_sequence targetTokens)
    hSourceBoundary hTargetBoundary
    hSourceReferenceBoundary hTargetReferenceBoundary
    hSourceEquality hTargetEquality hReferenceCondition
/-- 自动新鲜编号封装下的整条标准序列代码关系。 -/
theorem canonical_binder_shift_standard_sequences_code_condition
    {sourceTokens targetTokens : List Nat} (relation :
      CanonicalBinderShiftTokens sourceTokens targetTokens) (hSourceFormula :
      ⊢ₘ[godel_quotation_theory]
        formula_codeₘ(
          standard_token_sequence sourceTokens)) (hTargetFormula :
      ⊢ₘ[godel_quotation_theory]
        formula_codeₘ(
          standard_token_sequence targetTokens)) :
    ⊢ₘ[godel_quotation_theory]
      canonical_binder_shift_code_condition (standard_token_sequence sourceTokens) (standard_token_sequence targetTokens) := by
  rw [canonical_binder_shift_code_condition]
  exact
    canonical_binder_shift_standard_sequences_code_condition_with_ids
      relation hSourceFormula hTargetFormula _
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
