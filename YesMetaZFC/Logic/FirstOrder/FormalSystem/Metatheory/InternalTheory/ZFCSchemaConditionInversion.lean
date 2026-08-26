import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSequenceConditionRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTraceLegality.ForallPrefix

/-!
# ZFC schema 条件的对象层反演

本模块收集 separation/collection 共同依赖的函数性内核。所有证明都在
`fs_zfc_support_raw_theory` 中进行有限语法消去，不使用模型、标准性或元层真值传输。
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

/-! ## 规范深度平移的函数性 -/

/--
在标准 cutoff 与源深度上，规范深度平移条件唯一决定目标深度。

证明只区分宿主层的 `sourceDepth < cutoff`；对象层错误分支分别由有限
numeral 的成员关系或等式互异性排除。
-/
theorem fs_zfc_support_raw_canonical_shifted_depth_condition_unique
    {Γ : Context signature}
    (cutoff sourceDepth : Nat)
    (targetDepth : SetTerm)
    (hTargetDepth : Term.Admissible targetDepth SetSort.set)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_shifted_depth_condition
          (numₘ(cutoff)) (numₘ(sourceDepth)) targetDepth) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      targetDepth ≐ₘ
        numₘ(canonical_project_shift_depth cutoff sourceDepth) := by
  let leftBranch : SetFormula :=
    (numₘ(sourceDepth) ∈ₘ numₘ(cutoff)) ∧ₘ
      (targetDepth ≐ₘ numₘ(sourceDepth))
  let rightOrder : SetFormula :=
    (numₘ(sourceDepth) ≐ₘ numₘ(cutoff)) ∨ₘ
      (numₘ(cutoff) ∈ₘ numₘ(sourceDepth))
  let rightBranch : SetFormula :=
    rightOrder ∧ₘ
      (targetDepth ≐ₘ Sₘ(numₘ(sourceDepth)))
  have hConclusion :
      Formula.Admissible
        (targetDepth ≐ₘ
          numₘ(canonical_project_shift_depth
            cutoff sourceDepth)) :=
    Formula.Admissible.equal hTargetDepth
      (finite_numeral_term_admissible
        (canonical_project_shift_depth cutoff sourceDepth))
  have hDisjunction :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        leftBranch ∨ₘ rightBranch := by
    simpa [leftBranch, rightOrder, rightBranch,
      canonical_shifted_depth_condition] using hCondition
  apply FirstOrder.Derives.disjElim hDisjunction
  · let Δ : Context signature := leftBranch :: Γ
    have hLeft :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] leftBranch :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hMember :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(sourceDepth) ∈ₘ numₘ(cutoff) := by
      simpa [leftBranch] using
        FirstOrder.Derives.conjElimLeft hLeft
    have hTarget :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          targetDepth ≐ₘ numₘ(sourceDepth) := by
      simpa [leftBranch] using
        FirstOrder.Derives.conjElimRight hLeft
    by_cases hBelow : sourceDepth < cutoff
    · simpa [canonical_project_shift_depth_of_lt hBelow] using
        hTarget
    · exact FirstOrder.Derives.falsumElim
        (φ := targetDepth ≐ₘ
          numₘ(canonical_project_shift_depth
            cutoff sourceDepth))
        (FirstOrder.Derives.negElim hMember <|
          FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Δ) (by simp)
            (fs_zfc_support_raw_derives_of_standard_sequence <|
              standard_sequence_finite_numeral_not_mem_of_not_lt
                sourceDepth cutoff hBelow))
  · let Δ : Context signature := rightBranch :: Γ
    have hRight :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] rightBranch :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hOrder :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] rightOrder := by
      simpa [rightBranch] using
        FirstOrder.Derives.conjElimLeft hRight
    have hTarget :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          targetDepth ≐ₘ Sₘ(numₘ(sourceDepth)) := by
      simpa [rightBranch] using
        FirstOrder.Derives.conjElimRight hRight
    by_cases hBelow : sourceDepth < cutoff
    · apply FirstOrder.Derives.disjElim hOrder
      · let Ε : Context signature :=
          (numₘ(sourceDepth) ≐ₘ numₘ(cutoff)) :: Δ
        have hEquality :
            Ε ⊢ₘ[fs_zfc_support_raw_theory]
              numₘ(sourceDepth) ≐ₘ numₘ(cutoff) :=
          FirstOrder.Derives.assumption (by simp [Ε])
        exact FirstOrder.Derives.falsumElim
          (φ := targetDepth ≐ₘ
            numₘ(canonical_project_shift_depth
              cutoff sourceDepth))
          (fs_zfc_support_raw_falsum_of_numeral_equality
            (by omega) hEquality)
      · let Ε : Context signature :=
          (numₘ(cutoff) ∈ₘ numₘ(sourceDepth)) :: Δ
        have hMember :
            Ε ⊢ₘ[fs_zfc_support_raw_theory]
              numₘ(cutoff) ∈ₘ numₘ(sourceDepth) :=
          FirstOrder.Derives.assumption (by simp [Ε])
        exact FirstOrder.Derives.falsumElim
          (φ := targetDepth ≐ₘ
            numₘ(canonical_project_shift_depth
              cutoff sourceDepth))
          (FirstOrder.Derives.negElim hMember <|
            FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Ε) (by simp)
              (fs_zfc_support_raw_derives_of_standard_sequence <|
                standard_sequence_finite_numeral_not_mem_of_not_lt
                  cutoff sourceDepth (by omega)))
    · have hCutoffLe : cutoff ≤ sourceDepth := by omega
      simpa [canonical_project_shift_depth_of_le hCutoffLe,
        finite_numeral_term] using hTarget

/--
在标准 cutoff 与源深度上，目标变量条件唯一决定右侧规范变量码。
-/
theorem fs_zfc_support_raw_canonical_shifted_variable_target_condition_unique
    {Γ : Context signature}
    (cutoff sourceDepth : Nat)
    (rightVariable targetDepth : SetTerm)
    (hTargetDepth : Term.Admissible targetDepth SetSort.set)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_shifted_variable_target_condition
          (numₘ(cutoff)) (numₘ(sourceDepth))
          rightVariable targetDepth) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      rightVariable ≐ₘ
        canonical_binder_variable_code_term
          (numₘ(canonical_project_shift_depth
            cutoff sourceDepth)) := by
  have hDepthCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_shifted_depth_condition
          (numₘ(cutoff)) (numₘ(sourceDepth))
          targetDepth := by
    simpa [canonical_shifted_variable_target_condition] using
      FirstOrder.Derives.conjElimLeft hCondition
  have hRightCode :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        rightVariable ≐ₘ
          canonical_binder_variable_code_term targetDepth := by
    simpa [canonical_shifted_variable_target_condition] using
      FirstOrder.Derives.conjElimRight hCondition
  have hDepth :=
    fs_zfc_support_raw_canonical_shifted_depth_condition_unique
      cutoff sourceDepth targetDepth hTargetDepth hDepthCondition
  have hCode :=
    canonical_binder_variable_code_term_congr_of_equality
      targetDepth
      (numₘ(canonical_project_shift_depth
        cutoff sourceDepth))
      hTargetDepth
      (finite_numeral_term_admissible
        (canonical_project_shift_depth cutoff sourceDepth))
      hDepth
  exact Metatheory.Derives.equality_trans hRightCode hCode

/-- 不同标准深度的规范 binder 变量码等式在对象层导出矛盾。 -/
theorem fs_zfc_support_raw_canonical_binder_variable_code_falsum
    {Γ : Context signature}
    (leftDepth rightDepth : Nat)
    (hNe : leftDepth ≠ rightDepth)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_variable_code_term
            (numₘ(leftDepth)) ≐ₘ
          canonical_binder_variable_code_term
            (numₘ(rightDepth))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  let leftTokens : List Nat :=
    [GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name leftDepth)]
  let rightTokens : List Nat :=
    [GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name rightDepth)]
  have hLeftStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_variable_code_term
            (numₘ(leftDepth)) ≐ₘ
          standard_token_sequence leftTokens := by
    exact FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      (fs_zfc_support_raw_derives_of_godel_quotation <| by
        simpa [leftTokens] using
          canonical_binder_variable_code_numeral_eq_standard_token_sequence
            leftDepth)
  have hRightStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_variable_code_term
            (numₘ(rightDepth)) ≐ₘ
          standard_token_sequence rightTokens := by
    exact FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      (fs_zfc_support_raw_derives_of_godel_quotation <| by
        simpa [rightTokens] using
          canonical_binder_variable_code_numeral_eq_standard_token_sequence
            rightDepth)
  have hStandardEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence leftTokens ≐ₘ
          standard_token_sequence rightTokens :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hLeftStandard)
      (Metatheory.Derives.equality_trans
        hEquality hRightStandard)
  have hTokensNe : leftTokens ≠ rightTokens := by
    intro hTokens
    have hToken :
        GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name leftDepth) =
          GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name rightDepth) := by
      simpa [leftTokens, rightTokens] using
        congrArg List.head? hTokens
    exact hNe <|
      GodelQuotation.bound_name_injective <|
        GodelQuotation.variable_token_injective hToken
  exact FirstOrder.Derives.negElim hStandardEquality <|
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      (fs_zfc_support_raw_derives_of_standard_sequence <|
        standard_token_sequence_ne hTokensNe)

/-- 将变量目标条件沿源深度等式运输到一个标准 numeral。 -/
private theorem fs_zfc_support_raw_canonical_shifted_variable_target_of_source_equality
    {Γ : Context signature}
    (cutoff sourceDepth : Nat)
    (sourceDepthId : FreeVarId)
    (rightVariable targetDepth : SetTerm)
    (hRightVariable : Term.Admissible rightVariable SetSort.set)
    (hTargetDepth : Term.Admissible targetDepth SetSort.set)
    (hSourceFreshRight :
      (SetSort.set, sourceDepthId) ∉
        Term.freeSupport rightVariable)
    (hSourceFreshTarget :
      (SetSort.set, sourceDepthId) ∉
        Term.freeSupport targetDepth)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (x#sourceDepthId) ≐ₘ numₘ(sourceDepth))
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_shifted_variable_target_condition
          (numₘ(cutoff)) (x#sourceDepthId)
          rightVariable targetDepth) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      canonical_shifted_variable_target_condition
        (numₘ(cutoff)) (numₘ(sourceDepth))
        rightVariable targetDepth := by
  let body : SetFormula :=
    canonical_shifted_variable_target_condition
      (numₘ(cutoff)) (x#sourceDepthId)
      rightVariable targetDepth
  have hBody : Formula.Admissible body := by
    simpa [body] using
      canonical_shifted_variable_target_condition_admissible
        (numₘ(cutoff)) (x#sourceDepthId)
        rightVariable targetDepth
        (finite_numeral_term_admissible cutoff)
        (set_variable_admissible sourceDepthId)
        hRightVariable hTargetDepth
  have hTransport :=
    Metatheory.Derives.equality_iff_of_equality
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (sort := SetSort.set)
      (eigen := sourceDepthId)
      (left := x#sourceDepthId)
      (right := numₘ(sourceDepth))
      (body := body)
      hSourceEquality
  have hCutoffFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceDepthId
          replacement (numₘ(cutoff)) =
        numₘ(cutoff) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hTwoFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceDepthId
          replacement (numₘ(2)) =
        numₘ(2) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hRightFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceDepthId
          replacement rightVariable =
        rightVariable :=
    Term.substituteFree_eq_self_of_not_mem
      _ _ _ _ hSourceFreshRight
  have hTargetFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceDepthId
          replacement targetDepth =
        targetDepth :=
    Term.substituteFree_eq_self_of_not_mem
      _ _ _ _ hSourceFreshTarget
  change
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (Formula.substituteFree SetSort.set sourceDepthId
          (x#sourceDepthId) body ↔ₘ
        Formula.substituteFree SetSort.set sourceDepthId
          (numₘ(sourceDepth)) body)
    at hTransport
  have hLeftSubstitution :
      Formula.substituteFree SetSort.set sourceDepthId
          (x#sourceDepthId) body =
        canonical_shifted_variable_target_condition
          (numₘ(cutoff)) (x#sourceDepthId)
          rightVariable targetDepth := by
    simp [body,
      canonical_shifted_variable_target_condition,
      canonical_shifted_depth_condition,
      canonical_binder_variable_code_term,
      canonical_binder_name_term,
      Formula.substituteFree, Term.substituteFree,
      set_variable, hCutoffFixed, hRightFixed,
      hTargetFixed, hTwoFixed]
  have hRightSubstitution :
      Formula.substituteFree SetSort.set sourceDepthId
          (numₘ(sourceDepth)) body =
        canonical_shifted_variable_target_condition
          (numₘ(cutoff)) (numₘ(sourceDepth))
          rightVariable targetDepth := by
    simp [body,
      canonical_shifted_variable_target_condition,
      canonical_shifted_depth_condition,
      canonical_binder_variable_code_term,
      canonical_binder_name_term,
      Formula.substituteFree, Term.substituteFree,
      set_variable, hCutoffFixed, hRightFixed,
      hTargetFixed, hTwoFixed]
  exact FirstOrder.Derives.iffElimRight
    (by
      simpa [hLeftSubstitution, hRightSubstitution] using
        hTransport)
    hCondition

/--
标准入口深度中的一个已知规范变量，其显式 cutoff-shift 条件唯一决定右侧变量码。

外层深度见证由有限 numeral 成员消去；错误深度分支由规范 binder 变量码互异性
排除，正确分支再消去目标深度见证。
-/
theorem fs_zfc_support_raw_canonical_shifted_variable_code_condition_unique
    {Γ : Context signature}
    (cutoff entryDepth sourceDepth : Nat)
    (leftVariable rightVariable : SetTerm)
    (variableDepthId : FreeVarId)
    (hLeftVariable : Term.Admissible leftVariable SetSort.set)
    (hRightVariable : Term.Admissible rightVariable SetSort.set)
    (hLeftEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        leftVariable ≐ₘ
          canonical_binder_variable_code_term
            (numₘ(sourceDepth)))
    (hDepthFreshRight :
      (SetSort.set, variableDepthId) ∉
        Term.freeSupport rightVariable)
    (hTargetDepthFreshLeft :
      (SetSort.set, variableDepthId + 1) ∉
        Term.freeSupport leftVariable)
    (hTargetDepthFreshRight :
      (SetSort.set, variableDepthId + 1) ∉
        Term.freeSupport rightVariable)
    (hDepthFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, variableDepthId) ∉
          Formula.freeSupport formula)
    (hTargetDepthFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, variableDepthId + 1) ∉
          Formula.freeSupport formula)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_shifted_variable_code_condition_with_id
          (numₘ(cutoff)) (numₘ(entryDepth))
          leftVariable
          rightVariable variableDepthId) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      rightVariable ≐ₘ
        canonical_binder_variable_code_term
          (numₘ(canonical_project_shift_depth
            cutoff sourceDepth)) := by
  let targetBody : SetFormula :=
    canonical_shifted_variable_target_condition
      (numₘ(cutoff)) (x#variableDepthId)
      rightVariable (x#(variableDepthId + 1))
  let outerBody : SetFormula :=
    (((x#variableDepthId ∈ₘ numₘ(entryDepth)) ∧ₘ
        (leftVariable ≐ₘ
          canonical_binder_variable_code_term
            (x#variableDepthId))) ∧ₘ
      (∃ₘ[SetSort.set, variableDepthId + 1], targetBody))
  have hTargetBody : Formula.Admissible targetBody := by
    simpa [targetBody] using
      canonical_shifted_variable_target_condition_admissible
        (numₘ(cutoff)) (x#variableDepthId)
        rightVariable (x#(variableDepthId + 1))
        (finite_numeral_term_admissible cutoff)
        (set_variable_admissible variableDepthId)
        hRightVariable
        (set_variable_admissible (variableDepthId + 1))
  have hExistsAdmissible :
      Formula.Admissible
        (canonical_shifted_variable_code_condition_with_id
          (numₘ(cutoff)) (numₘ(entryDepth))
          leftVariable
          rightVariable variableDepthId) :=
    canonical_shifted_variable_code_condition_with_id_admissible
      (numₘ(cutoff)) (numₘ(entryDepth))
      leftVariable
      rightVariable variableDepthId
      (finite_numeral_term_admissible cutoff)
      (finite_numeral_term_admissible entryDepth)
      hLeftVariable hRightVariable
  have hOuterBody : Formula.Admissible outerBody := by
    have hOpened :=
      Formula.Admissible.exists_openAt
        (term := (x#variableDepthId : SetTerm))
        SetSort.set hExistsAdmissible
        (set_variable_admissible variableDepthId)
    simpa [outerBody, targetBody,
      canonical_shifted_variable_code_condition_with_id,
      Formula.openAt_closeFreeAt] using hOpened
  have hExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, variableDepthId], outerBody := by
    simpa [outerBody, targetBody,
      canonical_shifted_variable_code_condition_with_id] using
      hCondition
  have hConclusion :
      Formula.Admissible
        (rightVariable ≐ₘ
          canonical_binder_variable_code_term
            (numₘ(canonical_project_shift_depth
              cutoff sourceDepth))) :=
    Formula.Admissible.equal hRightVariable
      (canonical_binder_variable_code_term_admissible
        (numₘ(canonical_project_shift_depth
          cutoff sourceDepth))
        (finite_numeral_term_admissible
          (canonical_project_shift_depth cutoff sourceDepth)))
  have hTargetDepthFreshOuterBody :
      (SetSort.set, variableDepthId + 1) ∉
        Formula.freeSupport outerBody := by
    have hClosedTarget :=
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set (variableDepthId + 1) 0
        targetBody
    have hIdNe :
        variableDepthId + 1 ≠ variableDepthId := by
      exact Nat.ne_of_gt (Nat.lt_succ_self variableDepthId)
    simp only [outerBody, Formula.freeSupport,
      Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport,
      List.append_nil]
    intro hMember
    rcases List.mem_cons.mp hMember with hFirst | hRest
    · exact hIdNe (congrArg Prod.snd hFirst)
    · rcases List.mem_append.mp hRest with hPrefix | hClosed
      · rcases List.mem_append.mp hPrefix with hEmpty | hPrefix
        · cases hEmpty
        · rcases List.mem_append.mp hPrefix with hLeft | hSecond
          · exact hTargetDepthFreshLeft hLeft
          · rcases List.mem_append.mp hSecond with hEmpty | hSecond
            · cases hEmpty
            · have hEquality :=
                List.mem_singleton.mp hSecond
              exact hIdNe (congrArg Prod.snd hEquality)
      · exact hClosedTarget hClosed
  nd_apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := variableDepthId)
    (body := outerBody)
    (conclusion :=
      rightVariable ≐ₘ
        canonical_binder_variable_code_term
          (numₘ(canonical_project_shift_depth
            cutoff sourceDepth)))
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · exact hDepthFreshContext
  · simpa [Formula.freeSupport,
      canonical_binder_variable_code_term,
      canonical_binder_name_term,
      Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport] using
      hDepthFreshRight
  · exact hExists
  · let Δ : Context signature := outerBody :: Γ
    change Δ ⊢ₘ[fs_zfc_support_raw_theory]
      rightVariable ≐ₘ
        canonical_binder_variable_code_term
          (numₘ(canonical_project_shift_depth
            cutoff sourceDepth))
    have hBody :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] outerBody :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hSourceData :=
      FirstOrder.Derives.conjElimLeft hBody
    have hSourceMember :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          (x#variableDepthId) ∈ₘ numₘ(entryDepth) := by
      simpa [outerBody] using
        FirstOrder.Derives.conjElimLeft hSourceData
    have hLeftCode :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          leftVariable ≐ₘ
            canonical_binder_variable_code_term
              (x#variableDepthId) := by
      simpa [outerBody] using
        FirstOrder.Derives.conjElimRight hSourceData
    have hTargetExists :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          ∃ₘ[SetSort.set, variableDepthId + 1],
            targetBody := by
      simpa [outerBody] using
        FirstOrder.Derives.conjElimRight hBody
    apply
      fs_zfc_support_raw_finite_numeral_member_elim_context
        entryDepth (x#variableDepthId)
        (rightVariable ≐ₘ
          canonical_binder_variable_code_term
            (numₘ(canonical_project_shift_depth
              cutoff sourceDepth)))
        (set_variable_admissible variableDepthId)
        hConclusion hSourceMember
    intro index hIndex
    let sourceEquality : SetFormula :=
      (x#variableDepthId) ≐ₘ numₘ(index)
    let Ε : Context signature := sourceEquality :: Δ
    change Ε ⊢ₘ[fs_zfc_support_raw_theory]
      rightVariable ≐ₘ
        canonical_binder_variable_code_term
          (numₘ(canonical_project_shift_depth
            cutoff sourceDepth))
    have hSourceEquality :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          (x#variableDepthId) ≐ₘ numₘ(index) := by
      simpa [Ε, sourceEquality] using
        (FirstOrder.Derives.assumption
          (T := fs_zfc_support_raw_theory)
          (Γ := Ε) (φ := sourceEquality) (by simp [Ε]))
    have hLeftCodeAt :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          leftVariable ≐ₘ
            canonical_binder_variable_code_term
              (x#variableDepthId) :=
      FirstOrder.Derives.context_weaken_cons hLeftCode
    have hKnownLeft :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_binder_variable_code_term
              (numₘ(sourceDepth)) ≐ₘ
            leftVariable :=
      Metatheory.Derives.equality_symm <|
        FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons
            hLeftEquality
    have hDepthCode :=
      canonical_binder_variable_code_term_congr_of_equality
        (x#variableDepthId) (numₘ(index))
        (set_variable_admissible variableDepthId)
        (finite_numeral_term_admissible index)
        hSourceEquality
    have hKnownCode :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_binder_variable_code_term
              (numₘ(sourceDepth)) ≐ₘ
            canonical_binder_variable_code_term
              (numₘ(index)) :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_trans
          hKnownLeft hLeftCodeAt)
        hDepthCode
    by_cases hDepth : index = sourceDepth
    · subst index
      have hTargetExistsAt :
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            ∃ₘ[SetSort.set, variableDepthId + 1],
              targetBody :=
        FirstOrder.Derives.context_weaken_cons hTargetExists
      nd_apply FirstOrder.Derives.exists_elim
        (T := fs_zfc_support_raw_theory)
        (Γ := Ε)
        (sort := SetSort.set)
        (eigen := variableDepthId + 1)
        (body := targetBody)
        (conclusion :=
          rightVariable ≐ₘ
            canonical_binder_variable_code_term
              (numₘ(canonical_project_shift_depth
                cutoff sourceDepth)))
        (hBodyCheck :=
          Formula.check_admissible_complete hTargetBody)
      · intro formula hFormula
        rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
        exact List.not_mem_nil
      · intro formula hFormula
        simp only [Ε, Δ, List.mem_cons] at hFormula
        rcases hFormula with rfl | rfl | hFormula
        · simp [sourceEquality, Formula.freeSupport,
            Term.freeSupport,
            finite_numeral_term_freeSupport]
        · exact hTargetDepthFreshOuterBody
        · exact hTargetDepthFreshContext formula hFormula
      · simpa [Formula.freeSupport,
          canonical_binder_variable_code_term,
          canonical_binder_name_term,
          Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport] using
          hTargetDepthFreshRight
      · exact hTargetExistsAt
      · let Ζ : Context signature := targetBody :: Ε
        change Ζ ⊢ₘ[fs_zfc_support_raw_theory]
          rightVariable ≐ₘ
            canonical_binder_variable_code_term
              (numₘ(canonical_project_shift_depth
                cutoff sourceDepth))
        have hTarget :
            Ζ ⊢ₘ[fs_zfc_support_raw_theory] targetBody :=
          FirstOrder.Derives.assumption
            (by simp [Ζ])
            (Formula.check_admissible_complete hTargetBody)
        have hSourceEqualityAt :
            Ζ ⊢ₘ[fs_zfc_support_raw_theory]
              (x#variableDepthId) ≐ₘ
                numₘ(sourceDepth) :=
          FirstOrder.Derives.context_weaken_cons
            hSourceEquality
        have hSourceFreshTarget :
            (SetSort.set, variableDepthId) ∉
              Term.freeSupport (x#(variableDepthId + 1)) := by
          intro hMember
          have hEquality :
              (SetSort.set, variableDepthId) =
                (SetSort.set, variableDepthId + 1) :=
            List.mem_singleton.mp hMember
          have hIdEquality :
              variableDepthId = variableDepthId + 1 :=
            congrArg Prod.snd hEquality
          exact
            (Nat.ne_of_lt (Nat.lt_succ_self variableDepthId)) <| by
              simp at hIdEquality
        have hTargetTransported :=
          fs_zfc_support_raw_canonical_shifted_variable_target_of_source_equality
            cutoff sourceDepth variableDepthId
            rightVariable (x#(variableDepthId + 1))
            hRightVariable
            (set_variable_admissible (variableDepthId + 1))
            hDepthFreshRight hSourceFreshTarget
            hSourceEqualityAt
            (by simpa [targetBody] using hTarget)
        exact
          fs_zfc_support_raw_canonical_shifted_variable_target_condition_unique
            cutoff sourceDepth rightVariable
            (x#(variableDepthId + 1))
            (set_variable_admissible (variableDepthId + 1))
            hTargetTransported
    · exact FirstOrder.Derives.falsumElim
        (φ := rightVariable ≐ₘ
          canonical_binder_variable_code_term
            (numₘ(canonical_project_shift_depth
              cutoff sourceDepth)))
        (fs_zfc_support_raw_canonical_binder_variable_code_falsum
          sourceDepth index (Ne.symm hDepth) hKnownCode)

/-! ## 规范全称前缀的函数性 -/

/-- 规范全称前缀构造只要求核心项 admissible。 -/
theorem canonical_forall_prefix_code_from_admissible
    (start count : Nat)
    (core : SetTerm)
    (hCore : Term.Admissible core SetSort.set) :
    Term.Admissible
      (canonical_forall_prefix_code_from start count core)
        SetSort.set := by
  induction count generalizing start with
  | zero =>
      simpa [canonical_forall_prefix_code_from] using hCore
  | succ count ih =>
      exact universal_formula_code_term_admissible _ _
        (canonical_binder_variable_code_term_admissible
          (numₘ(start))
          (finite_numeral_term_admissible start))
        (ih (start + 1))

/-- 规范全称前缀码对核心项等式保持。 -/
theorem canonical_forall_prefix_code_from_congr_of_equality
    {T : SetTheory}
    {Γ : Context signature}
    (start count : Nat)
    (leftCore rightCore : SetTerm)
    (hLeftCore : Term.Admissible leftCore SetSort.set)
    (hRightCore : Term.Admissible rightCore SetSort.set)
    (hCoreEquality : Γ ⊢ₘ[T] leftCore ≐ₘ rightCore) :
    Γ ⊢ₘ[T]
      canonical_forall_prefix_code_from start count leftCore ≐ₘ
        canonical_forall_prefix_code_from start count rightCore := by
  induction count generalizing start with
  | zero =>
      simpa [canonical_forall_prefix_code_from] using hCoreEquality
  | succ count ih =>
      have hLeftBody :
          Term.Admissible
            (canonical_forall_prefix_code_from
              (start + 1) count leftCore)
            SetSort.set :=
        canonical_forall_prefix_code_from_admissible
          (start + 1) count leftCore hLeftCore
      have hRightBody :
          Term.Admissible
            (canonical_forall_prefix_code_from
              (start + 1) count rightCore)
            SetSort.set :=
        canonical_forall_prefix_code_from_admissible
          (start + 1) count rightCore hRightCore
      have hBinder :
          Γ ⊢ₘ[T]
            canonical_binder_variable_code_term
                (numₘ(start)) ≐ₘ
              canonical_binder_variable_code_term
                (numₘ(start)) :=
        FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (canonical_binder_variable_code_term
            (numₘ(start)))
      have hUniversal :=
        canonical_universal_code_term_congr_of_equalities
          (canonical_binder_variable_code_term
            (numₘ(start)))
          (canonical_binder_variable_code_term
            (numₘ(start)))
          (canonical_forall_prefix_code_from
            (start + 1) count leftCore)
          (canonical_forall_prefix_code_from
            (start + 1) count rightCore)
          (canonical_binder_variable_code_term_admissible
            (numₘ(start))
            (finite_numeral_term_admissible start))
          (canonical_binder_variable_code_term_admissible
            (numₘ(start))
            (finite_numeral_term_admissible start))
          hLeftBody hRightBody hBinder
          (ih (start + 1))
      simpa [canonical_forall_prefix_code_from] using hUniversal

/-- 规范全称前缀不引入新的自由变量。 -/
private theorem canonical_forall_prefix_code_from_freeSupport
    (start count : Nat)
    (core : SetTerm) :
    Term.freeSupport
        (canonical_forall_prefix_code_from start count core) =
      Term.freeSupport core := by
  induction count generalizing start with
  | zero =>
      simp [canonical_forall_prefix_code_from]
  | succ count ih =>
      simp [canonical_forall_prefix_code_from,
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport, ih (start + 1)]

/-- 将前缀轨迹的逐点全称式实例化到一个具体有效位置。 -/
private theorem fs_zfc_support_raw_canonical_forall_prefix_step_at
    {Γ : Context signature}
    (trace : SetTerm)
    (indexId : FreeVarId)
    (count index : Nat)
    (hTrace : Term.Admissible trace SetSort.set)
    (hIndexFreshTrace :
      (SetSort.set, indexId) ∉ Term.freeSupport trace)
    (hSteps :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∀ₘ[SetSort.set, indexId],
          (x#indexId ∈ₘ numₘ(count)) ⟶ₘ
            canonical_forall_prefix_step_condition
              trace (x#indexId))
    (hIndex : index < count) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      canonical_forall_prefix_step_condition
        trace (numₘ(index)) := by
  have hTraceClose :
      Term.closeFreeAt SetSort.set indexId 0 trace =
        trace :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 trace
      hTrace.2 hIndexFreshTrace
  have hTraceOpen :
      Term.openAt SetSort.set 0 (numₘ(index)) trace =
        trace :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (numₘ(index)) trace hTrace.2
  have hCountClose :
      Term.closeFreeAt SetSort.set indexId 0 (numₘ(count)) =
        numₘ(count) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 (numₘ(count))
      (finite_numeral_term_admissible count).2 (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hCountOpen :
      Term.openAt SetSort.set 0 (numₘ(index)) (numₘ(count)) =
        numₘ(count) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (numₘ(index)) (numₘ(count))
      (finite_numeral_term_admissible count).2
  have hTwoClose :
      Term.closeFreeAt SetSort.set indexId 0 (numₘ(2)) =
        numₘ(2) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 (numₘ(2))
      (finite_numeral_term_admissible 2).2 (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hTwoOpen :
      Term.openAt SetSort.set 0 (numₘ(index)) (numₘ(2)) =
        numₘ(2) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (numₘ(index)) (numₘ(2))
      (finite_numeral_term_admissible 2).2
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := numₘ(index)) hSteps
  have hAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (numₘ(index) ∈ₘ numₘ(count)) ⟶ₘ
          canonical_forall_prefix_step_condition
            trace (numₘ(index)) := by
    simpa [canonical_forall_prefix_step_condition,
      canonical_binder_variable_code_term,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Term.openAt, Term.closeFreeAt,
      set_variable, hTraceClose, hTraceOpen,
      hCountClose, hCountOpen, hTwoClose, hTwoOpen] using hAtRaw
  exact FirstOrder.Derives.impElim hAt <|
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      (fs_zfc_support_raw_derives_of_standard_sequence
        (standard_sequence_finite_numeral_mem_of_lt
          index count hIndex))

/--
从末项向首项有限回放规范全称前缀。

`count = start + remaining` 明示当前回放区间；递归只发生在宿主自然数
`remaining` 上，对象层仅实例化有限多个 numeral 位置。
-/
private theorem fs_zfc_support_raw_canonical_forall_prefix_trace_replay
    {Γ : Context signature}
    (trace core : SetTerm)
    (indexId : FreeVarId)
    (count start remaining : Nat)
    (hTrace : Term.Admissible trace SetSort.set)
    (hCore : Term.Admissible core SetSort.set)
    (hIndexFreshTrace :
      (SetSort.set, indexId) ∉ Term.freeSupport trace)
    (hCount : count = start + remaining)
    (hSteps :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∀ₘ[SetSort.set, indexId],
          (x#indexId ∈ₘ numₘ(count)) ⟶ₘ
            canonical_forall_prefix_step_condition
              trace (x#indexId))
    (hLast :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (trace ·ₘ numₘ(count)) ≐ₘ core) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (trace ·ₘ numₘ(start)) ≐ₘ
        canonical_forall_prefix_code_from
          start remaining core := by
  induction remaining generalizing start with
  | zero =>
      simpa [hCount, canonical_forall_prefix_code_from] using
        hLast
  | succ remaining ih =>
      have hStart : start < count := by
        omega
      have hStep :=
        fs_zfc_support_raw_canonical_forall_prefix_step_at
          trace indexId count start
          hTrace hIndexFreshTrace hSteps hStart
      have hTail :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            (trace ·ₘ numₘ(start + 1)) ≐ₘ
              canonical_forall_prefix_code_from
                (start + 1) remaining core :=
        ih (start + 1) (by omega)
      have hTailAtSuccessor :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            (trace ·ₘ Sₘ(numₘ(start))) ≐ₘ
              canonical_forall_prefix_code_from
                (start + 1) remaining core := by
        simpa [finite_numeral_term] using hTail
      have hBinder :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            canonical_binder_variable_code_term
                (numₘ(start)) ≐ₘ
              canonical_binder_variable_code_term
                (numₘ(start)) :=
        FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (canonical_binder_variable_code_term
            (numₘ(start)))
      have hUniversal :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            forall_codeₘ(
                canonical_binder_variable_code_term
                  (numₘ(start)),
                trace ·ₘ Sₘ(numₘ(start))) ≐ₘ
              forall_codeₘ(
                canonical_binder_variable_code_term
                  (numₘ(start)),
                canonical_forall_prefix_code_from
                  (start + 1) remaining core) :=
        canonical_universal_code_term_congr_of_equalities
          (canonical_binder_variable_code_term
            (numₘ(start)))
          (canonical_binder_variable_code_term
            (numₘ(start)))
          (trace ·ₘ Sₘ(numₘ(start)))
          (canonical_forall_prefix_code_from
            (start + 1) remaining core)
          (canonical_binder_variable_code_term_admissible
            (numₘ(start))
            (finite_numeral_term_admissible start))
          (canonical_binder_variable_code_term_admissible
            (numₘ(start))
            (finite_numeral_term_admissible start))
          (function_application_term_admissible
            trace (Sₘ(numₘ(start))) hTrace
            (successor_term_admissible
              (numₘ(start))
              (finite_numeral_term_admissible start)))
          (canonical_forall_prefix_code_from_admissible
            (start + 1) remaining core hCore)
          hBinder hTailAtSuccessor
      exact Metatheory.Derives.equality_trans
        (by
          simpa [canonical_forall_prefix_step_condition] using
            hStep)
        (by
          simpa [canonical_forall_prefix_code_from] using
            hUniversal)

/--
显式编号的规范全称前缀条件唯一决定最终公式码。

上下文与两个输入项上的新鲜性只是对象存在消去所需的捕获规避条件；
结论不要求核心码闭合，也不要求任何语义解释。
-/
theorem fs_zfc_support_raw_canonical_forall_prefix_code_condition_unique
    {Γ : Context signature}
    (core code : SetTerm)
    (count : Nat)
    (traceId indexId : FreeVarId)
    (hCore : Term.Admissible core SetSort.set)
    (hCode : Term.Admissible code SetSort.set)
    (hTraceNeIndex : traceId ≠ indexId)
    (hTraceFreshCore :
      (SetSort.set, traceId) ∉ Term.freeSupport core)
    (hTraceFreshCode :
      (SetSort.set, traceId) ∉ Term.freeSupport code)
    (hTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, traceId) ∉ Formula.freeSupport formula)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_forall_prefix_code_condition_with_ids
          (numₘ(count)) core code traceId indexId) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      code ≐ₘ canonical_forall_prefix_code count core := by
  let traceBody : SetFormula :=
    canonical_forall_prefix_trace_condition
      (numₘ(count)) core code (x#traceId) indexId
  have hTraceBody :
      Formula.Admissible traceBody := by
    simpa [traceBody] using
      canonical_forall_prefix_trace_condition_admissible
        (numₘ(count)) core code (x#traceId) indexId
        (finite_numeral_term_admissible count)
        hCore hCode (set_variable_admissible traceId)
  have hTraceExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, traceId], traceBody := by
    simpa [traceBody,
      canonical_forall_prefix_code_condition_with_ids] using
      FirstOrder.Derives.conjElimRight hCondition
  have hConclusion :
      Formula.Admissible
        (code ≐ₘ canonical_forall_prefix_code count core) :=
    Formula.Admissible.equal hCode
      (canonical_forall_prefix_code_from_admissible
        0 count core hCore)
  nd_apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := traceId)
    (body := traceBody)
    (conclusion :=
      code ≐ₘ canonical_forall_prefix_code count core)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · exact hTraceFreshContext
  · simpa [Formula.freeSupport,
      canonical_forall_prefix_code,
      canonical_forall_prefix_code_from_freeSupport
        0 count core] using
      And.intro hTraceFreshCode hTraceFreshCore
  · exact hTraceExists
  · let Δ : Context signature := traceBody :: Γ
    change Δ ⊢ₘ[fs_zfc_support_raw_theory]
      code ≐ₘ canonical_forall_prefix_code count core
    have hBodyAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] traceBody :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hTraceData :=
      FirstOrder.Derives.conjElimRight hBodyAt
    have hHead :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          (x#traceId ·ₘ numₘ(0)) ≐ₘ code := by
      simpa [traceBody,
        canonical_forall_prefix_trace_condition] using
        FirstOrder.Derives.conjElimLeft hTraceData
    have hStepsLast :=
      FirstOrder.Derives.conjElimRight hTraceData
    have hSteps :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          ∀ₘ[SetSort.set, indexId],
            (x#indexId ∈ₘ numₘ(count)) ⟶ₘ
              canonical_forall_prefix_step_condition
                (x#traceId) (x#indexId) := by
      simpa [traceBody,
        canonical_forall_prefix_trace_condition] using
        FirstOrder.Derives.conjElimLeft hStepsLast
    have hLast :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          (x#traceId ·ₘ numₘ(count)) ≐ₘ core := by
      simpa [traceBody,
        canonical_forall_prefix_trace_condition] using
        FirstOrder.Derives.conjElimRight hStepsLast
    have hIndexFreshTrace :
        (SetSort.set, indexId) ∉
          Term.freeSupport (x#traceId) := by
      intro hMember
      have hEquality :
          (SetSort.set, indexId) =
            (SetSort.set, traceId) :=
        List.mem_singleton.mp hMember
      exact hTraceNeIndex
        (congrArg Prod.snd hEquality).symm
    have hReplay :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          (x#traceId ·ₘ numₘ(0)) ≐ₘ
            canonical_forall_prefix_code count core :=
      fs_zfc_support_raw_canonical_forall_prefix_trace_replay
        (x#traceId) core indexId count 0 count
        (set_variable_admissible traceId) hCore
        hIndexFreshTrace (by omega) hSteps hLast
    exact Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hHead)
      hReplay

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
