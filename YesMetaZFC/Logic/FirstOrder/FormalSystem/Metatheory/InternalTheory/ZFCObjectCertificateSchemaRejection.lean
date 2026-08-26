import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCollectionCertificateContentRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTraceLegality.AtomQuotation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaCodeDecodeRejection

/-!
# ZFC schema 证书的动态内容拒绝

这里把显式 schema 反演接回动态对象 verifier。输入只保留生成器成功、
公式码不匹配与两个真实 schema 标签；内部仍使用 binary certificate code，
不引入整 trace 或更强的反向实例假设。
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
把一个规范 scope 变量条件消去为有限个地面深度分支。

调用方只需在原上下文中给出每个 `index < entryDepth` 的条件蕴含；本定理负责
消去内部深度见证，并把变量码等式运输到对应的规范 binder 码。
-/
theorem fs_zfc_support_raw_canonical_scoped_variable_code_condition_with_id_elim
    {Γ : Context signature}
    (entryDepth : Nat)
    (variableCode : SetTerm)
    (variableDepthId : FreeVarId)
    (conclusion : SetFormula)
    (hVariableCode :
      Term.Admissible variableCode SetSort.set)
    (hConclusion :
      Formula.Admissible conclusion)
    (hDepthFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, variableDepthId) ∉
          Formula.freeSupport formula)
    (hDepthFreshConclusion :
      (SetSort.set, variableDepthId) ∉
        Formula.freeSupport conclusion)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_scoped_variable_code_condition_with_id
          (numₘ(entryDepth)) variableCode
          variableDepthId)
    (hBranch :
      ∀ index, index < entryDepth →
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          (variableCode ≐ₘ
              canonical_binder_variable_code_term
                (numₘ(index))) ⟶ₘ
            conclusion) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      conclusion := by
  let body : SetFormula :=
    (x#variableDepthId ∈ₘ numₘ(entryDepth)) ∧ₘ
      (variableCode ≐ₘ
        canonical_binder_variable_code_term
          (x#variableDepthId))
  have hConditionAdmissible :
      Formula.Admissible
        (canonical_scoped_variable_code_condition_with_id
          (numₘ(entryDepth)) variableCode
          variableDepthId) :=
    canonical_scoped_variable_code_condition_with_id_admissible
      (numₘ(entryDepth)) variableCode variableDepthId
      (finite_numeral_term_admissible entryDepth)
      hVariableCode
  have hBodyAdmissible :
      Formula.Admissible body := by
    have hOpened :=
      Formula.Admissible.exists_openAt
        (term := (x#variableDepthId : SetTerm))
        SetSort.set hConditionAdmissible
        (set_variable_admissible variableDepthId)
    simpa [body,
      canonical_scoped_variable_code_condition_with_id,
      Formula.openAt_closeFreeAt] using hOpened
  have hExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, variableDepthId], body := by
    simpa [body,
      canonical_scoped_variable_code_condition_with_id] using
      hCondition
  nd_apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := variableDepthId)
    (body := body)
    (conclusion := conclusion)
    (hBodyCheck :=
      Formula.check_admissible_complete hBodyAdmissible)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · exact hDepthFreshContext
  · exact hDepthFreshConclusion
  · exact hExists
  · let Δ : Context signature := body :: Γ
    change Δ ⊢ₘ[fs_zfc_support_raw_theory]
      conclusion
    have hBody :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
        (Formula.check_admissible_complete
          hBodyAdmissible)
    have hMember :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#variableDepthId ∈ₘ numₘ(entryDepth) := by
      simpa [body] using
        FirstOrder.Derives.conjElimLeft hBody
    have hVariableCodeAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          variableCode ≐ₘ
            canonical_binder_variable_code_term
              (x#variableDepthId) := by
      simpa [body] using
        FirstOrder.Derives.conjElimRight hBody
    apply
      fs_zfc_support_raw_finite_numeral_member_elim_context
        entryDepth (x#variableDepthId)
        conclusion
        (set_variable_admissible variableDepthId)
        hConclusion hMember
    intro index hIndex
    let depthEquality : SetFormula :=
      (x#variableDepthId) ≐ₘ numₘ(index)
    let Ε : Context signature := depthEquality :: Δ
    change Ε ⊢ₘ[fs_zfc_support_raw_theory]
      conclusion
    have hDepthEquality :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          (x#variableDepthId) ≐ₘ numₘ(index) :=
      FirstOrder.Derives.assumption
        (by simp [Ε, depthEquality])
        (by prove_nd_formula_check)
    have hVariableCodeAt' :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          variableCode ≐ₘ
            canonical_binder_variable_code_term
              (x#variableDepthId) :=
      FirstOrder.Derives.context_weaken_cons
        hVariableCodeAt
    have hDepthCode :=
      canonical_binder_variable_code_term_congr_of_equality
        (x#variableDepthId) (numₘ(index))
        (set_variable_admissible variableDepthId)
        (finite_numeral_term_admissible index)
        hDepthEquality
    have hGroundCode :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          variableCode ≐ₘ
            canonical_binder_variable_code_term
              (numₘ(index)) :=
      Metatheory.Derives.equality_trans
        hVariableCodeAt' hDepthCode
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := Γ) (Δ := Ε)
        (by
          intro formula hFormula
          simp [Ε, Δ, hFormula])
        (hBranch index hIndex))
      hGroundCode


/--
标准 token 串若不等于当前有限 scope 内的任何规范项目原子，则对象原子分类条件
不可成立。两个变量深度都由上面的有限 scope 消去器处理。
-/
theorem fs_zfc_support_raw_canonical_project_atomic_code_condition_with_ids_neg_of_no_match
    (entryDepth : Nat)
    (tokens : List Nat)
    (base : FreeVarId)
    (hNoMatch :
      ∀ kind leftDepth rightDepth,
        leftDepth < entryDepth →
        rightDepth < entryDepth →
        tokens ≠
          CanonicalProjectTrace.canonical_project_atom_tokens
            kind leftDepth rightDepth) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ canonical_project_atomic_code_condition_with_ids
        (numₘ(entryDepth))
        (standard_token_sequence tokens)
        base (base + 1) (base + 2) (base + 3)) := by
  let leftCode : SetTerm := x#base
  let rightCode : SetTerm := x#(base + 1)
  let leftScope : SetFormula :=
    canonical_scoped_variable_code_condition_with_id
      (numₘ(entryDepth)) leftCode (base + 2)
  let rightScope : SetFormula :=
    canonical_scoped_variable_code_condition_with_id
      (numₘ(entryDepth)) rightCode (base + 3)
  let equalityShape : SetFormula :=
    standard_token_sequence tokens ≐ₘ
      eq_codeₘ(leftCode, rightCode)
  let membershipShape : SetFormula :=
    standard_token_sequence tokens ≐ₘ
      membership_atomic_formula_code_term
        leftCode rightCode
  let subsetShape : SetFormula :=
    standard_token_sequence tokens ≐ₘ
      project_subset_atomic_code_term
        leftCode rightCode
  let shapeCases : SetFormula :=
    equalityShape ∨ₘ
      (membershipShape ∨ₘ subsetShape)
  let body : SetFormula :=
    (leftScope ∧ₘ rightScope) ∧ₘ shapeCases
  let rightBody : SetFormula :=
    (rightCode ∈ₘ TermCodeₘ) ∧ₘ body
  let rightExists : SetFormula :=
    ∃ₘ[SetSort.set, base + 1], rightBody
  let leftBody : SetFormula :=
    (leftCode ∈ₘ TermCodeₘ) ∧ₘ rightExists
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, base], leftBody
  have hLeftCode :
      Term.Admissible leftCode SetSort.set :=
    set_variable_admissible base
  have hRightCode :
      Term.Admissible rightCode SetSort.set :=
    set_variable_admissible (base + 1)
  have hLeftScope :
      Formula.Admissible leftScope := by
    simpa [leftScope] using
      canonical_scoped_variable_code_condition_with_id_admissible
        (numₘ(entryDepth)) leftCode (base + 2)
        (finite_numeral_term_admissible entryDepth)
        hLeftCode
  have hRightScope :
      Formula.Admissible rightScope := by
    simpa [rightScope] using
      canonical_scoped_variable_code_condition_with_id_admissible
        (numₘ(entryDepth)) rightCode (base + 3)
        (finite_numeral_term_admissible entryDepth)
        hRightCode
  have hEqualityShape :
      Formula.Admissible equalityShape := by
    dsimp only [equalityShape]
    exact Formula.Admissible.equal
      (standard_token_sequence_admissible tokens)
      (equality_formula_code_term_admissible
        leftCode rightCode hLeftCode hRightCode)
  have hMembershipShape :
      Formula.Admissible membershipShape := by
    dsimp only [membershipShape]
    exact Formula.Admissible.equal
      (standard_token_sequence_admissible tokens)
      (binary_atomic_formula_code_term_admissible
        membership_symbol_code_term
        leftCode rightCode
        membership_symbol_code_term_admissible
        hLeftCode hRightCode)
  have hSubsetShape :
      Formula.Admissible subsetShape := by
    dsimp only [subsetShape]
    exact Formula.Admissible.equal
      (standard_token_sequence_admissible tokens)
      (canonical_project_subset_atomic_code_term_admissible
        leftCode rightCode hLeftCode hRightCode)
  have hBody :
      Formula.Admissible body := by
    dsimp only [body, shapeCases]
    exact Formula.Admissible.conj
      (Formula.Admissible.conj hLeftScope hRightScope)
          (Formula.Admissible.disj hEqualityShape
            (Formula.Admissible.disj
              hMembershipShape hSubsetShape))
  have hRightBody :
      Formula.Admissible rightBody := by
    dsimp only [rightBody]
    exact Formula.Admissible.conj
      (membership_formula_admissible
        hRightCode term_code_set_term_admissible)
      hBody
  have hRightExists :
      Formula.Admissible rightExists := by
    dsimp only [rightExists]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set (base + 1) hRightBody
  have hLeftBody :
      Formula.Admissible leftBody := by
    dsimp only [leftBody]
    exact Formula.Admissible.conj
      (membership_formula_admissible
        hLeftCode term_code_set_term_admissible)
      hRightExists
  have hCondition :
      Formula.Admissible condition := by
    dsimp only [condition]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set base hLeftBody
  have hConditionShape :
      condition =
        canonical_project_atomic_code_condition_with_ids
          (numₘ(entryDepth))
          (standard_token_sequence tokens)
          base (base + 1) (base + 2) (base + 3) := by
    rfl
  rw [← hConditionShape]
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete hCondition)
  let Γ : Context signature := [condition]
  have hConditionAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hCondition)
  have hLeftFreshCondition :
      (SetSort.set, base) ∉
        Formula.freeSupport condition := by
    simpa [condition] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set base 0 leftBody
  nd_apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := base)
    (body := leftBody)
    (conclusion := Formula.falsum)
    (hBodyCheck :=
      Formula.check_admissible_complete hLeftBody)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    exact hLeftFreshCondition
  · exact List.not_mem_nil
  · exact hConditionAt
  · let Δ : Context signature := leftBody :: Γ
    have hLeftBodyAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          leftBody :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
        (Formula.check_admissible_complete hLeftBody)
    have hRightExistsAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          rightExists :=
      FirstOrder.Derives.conjElimRight hLeftBodyAt
    have hRightFreshRightExists :
        (SetSort.set, base + 1) ∉
          Formula.freeSupport rightExists := by
      simpa [rightExists] using
        Formula.not_mem_freeSupport_closeFreeAt
          SetSort.set (base + 1) 0 rightBody
    have hLeftBodyFresh :
        (SetSort.set, base + 1) ∉
          Formula.freeSupport leftBody := by
      have hLeftGuardFresh :
          (SetSort.set, base + 1) ∉
            Formula.freeSupport
              (leftCode ∈ₘ TermCodeₘ) := by
        simp only [leftCode, Formula.freeSupport, Term.freeSupport,
          Term.freeSupportList]
        intro hMember
        have hId : base + 1 = base :=
          congrArg Prod.snd (List.mem_singleton.mp hMember)
        exact (Nat.ne_of_lt (by
          exact Nat.lt_add_of_pos_right (n := base)
            (by decide : 0 < 1))) hId.symm
      simp only [leftBody, Formula.freeSupport]
      intro hMember
      rcases List.mem_append.mp hMember with hLeft | hRight
      · exact hLeftGuardFresh hLeft
      · exact hRightFreshRightExists hRight
    have hRightFreshCondition :
        (SetSort.set, base + 1) ∉
          Formula.freeSupport condition := by
      simpa [condition] using
        Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
          (SetSort.set, base + 1)
          SetSort.set base 0 leftBody
          hLeftBodyFresh
    nd_apply FirstOrder.Derives.exists_elim
      (T := fs_zfc_support_raw_theory)
      (Γ := Δ)
      (sort := SetSort.set)
      (eigen := base + 1)
      (body := rightBody)
      (conclusion := Formula.falsum)
      (hBodyCheck :=
        Formula.check_admissible_complete hRightBody)
    · intro formula hFormula
      rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      simp only [Δ, Γ, List.mem_cons,
        List.not_mem_nil,
        or_false] at hFormula
      rcases hFormula with rfl | rfl
      · exact hLeftBodyFresh
      · exact hRightFreshCondition
    · exact List.not_mem_nil
    · exact hRightExistsAt
    · let Θ : Context signature := rightBody :: Δ
      change Θ ⊢ₘ[fs_zfc_support_raw_theory]
        Formula.falsum
      have hRightBodyAt :
          Θ ⊢ₘ[fs_zfc_support_raw_theory]
            rightBody :=
        FirstOrder.Derives.assumption
          (by simp [Θ])
          (Formula.check_admissible_complete hRightBody)
      have hBodyAt :
          Θ ⊢ₘ[fs_zfc_support_raw_theory]
            body :=
        FirstOrder.Derives.conjElimRight hRightBodyAt
      have hScopesAt :
          Θ ⊢ₘ[fs_zfc_support_raw_theory]
            leftScope ∧ₘ rightScope := by
        simpa [body] using
          FirstOrder.Derives.conjElimLeft hBodyAt
      have hLeftScopeAt :
          Θ ⊢ₘ[fs_zfc_support_raw_theory]
            leftScope :=
        FirstOrder.Derives.conjElimLeft hScopesAt
      have hRightScopeAt :
          Θ ⊢ₘ[fs_zfc_support_raw_theory]
            rightScope :=
        FirstOrder.Derives.conjElimRight hScopesAt
      have hShapeCasesAt :
          Θ ⊢ₘ[fs_zfc_support_raw_theory]
            shapeCases := by
        simpa [body] using
          FirstOrder.Derives.conjElimRight hBodyAt
      have hShapeSupport :
          Formula.freeSupport shapeCases =
            [(SetSort.set, base), (SetSort.set, base + 1),
              (SetSort.set, base), (SetSort.set, base + 1),
              (SetSort.set, base), (SetSort.set, base + 1)] := by
        simp [shapeCases, equalityShape, membershipShape,
          subsetShape, Formula.freeSupport, Term.freeSupport,
          Term.freeSupportList, finite_numeral_term_freeSupport,
          standard_token_sequence_freeSupport_nil,
          Numbered.argument_sequence, standard_sequence_from,
          leftCode, rightCode] <;>
          rfl
      have hShapeFresh (id : FreeVarId)
          (hBase : id ≠ base)
          (hRight : id ≠ base + 1) :
          (SetSort.set, id) ∉
            Formula.freeSupport shapeCases := by
        rw [hShapeSupport]
        intro hMember
        rcases List.mem_cons.mp hMember with h | hMember
        · exact hBase (congrArg Prod.snd h)
        rcases List.mem_cons.mp hMember with h | hMember
        · exact hRight (congrArg Prod.snd h)
        rcases List.mem_cons.mp hMember with h | hMember
        · exact hBase (congrArg Prod.snd h)
        rcases List.mem_cons.mp hMember with h | hMember
        · exact hRight (congrArg Prod.snd h)
        rcases List.mem_cons.mp hMember with h | hMember
        · exact hBase (congrArg Prod.snd h)
        rcases List.mem_cons.mp hMember with h | hMember
        · exact hRight (congrArg Prod.snd h)
        · exact List.not_mem_nil hMember
      have hScopeBodySupport
          (codeId depthId : FreeVarId) :
          Formula.freeSupport
              ((x#depthId ∈ₘ numₘ(entryDepth)) ∧ₘ
                (x#codeId ≐ₘ
                  canonical_binder_variable_code_term
                    (x#depthId))) =
            [(SetSort.set, depthId), (SetSort.set, codeId),
              (SetSort.set, depthId)] := by
        simp [Formula.freeSupport, Term.freeSupport,
          Term.freeSupportList,
          finite_numeral_term_freeSupport] <;>
          rfl
      have hScopeBodyFresh
          (targetId codeId depthId : FreeVarId)
          (hDepth : targetId ≠ depthId)
          (hCode : targetId ≠ codeId) :
          (SetSort.set, targetId) ∉
            Formula.freeSupport
              ((x#depthId ∈ₘ numₘ(entryDepth)) ∧ₘ
                (x#codeId ≐ₘ
                  canonical_binder_variable_code_term
                    (x#depthId))) := by
        rw [hScopeBodySupport codeId depthId]
        intro hMember
        rcases List.mem_cons.mp hMember with h | hMember
        · exact hDepth (congrArg Prod.snd h)
        rcases List.mem_cons.mp hMember with h | hMember
        · exact hCode (congrArg Prod.snd h)
        rcases List.mem_cons.mp hMember with h | hMember
        · exact hDepth (congrArg Prod.snd h)
        · exact List.not_mem_nil hMember
      have hLeftDepthFreshLeftScope :
          (SetSort.set, base + 2) ∉
            Formula.freeSupport leftScope := by
        simpa [leftScope,
          canonical_scoped_variable_code_condition_with_id,
          Formula.freeSupport] using
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set (base + 2) 0
            ((x#(base + 2) ∈ₘ numₘ(entryDepth)) ∧ₘ
              (leftCode ≐ₘ
                canonical_binder_variable_code_term
                  (x#(base + 2))))
      have hLeftDepthFreshRightScope :
          (SetSort.set, base + 2) ∉
            Formula.freeSupport rightScope := by
        simpa [rightScope,
          canonical_scoped_variable_code_condition_with_id,
          Formula.freeSupport, rightCode] using
          Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            (SetSort.set, base + 2)
            SetSort.set (base + 3) 0
            ((x#(base + 3) ∈ₘ numₘ(entryDepth)) ∧ₘ
              (x#(base + 1) ≐ₘ
                canonical_binder_variable_code_term
                  (x#(base + 3))))
            (hScopeBodyFresh
              (base + 2) (base + 1) (base + 3)
              (Nat.ne_of_lt <|
                Nat.add_lt_add_left
                  (by decide : 2 < 3) base)
              (Nat.ne_of_gt <|
                Nat.add_lt_add_left
                  (by decide : 1 < 2) base))
      have hLeftDepthFreshBody :
          (SetSort.set, base + 2) ∉
            Formula.freeSupport body := by
        intro hMember
        have hMember' :
            (SetSort.set, base + 2) ∈
              (Formula.freeSupport leftScope ++
                Formula.freeSupport rightScope) ++
                Formula.freeSupport shapeCases := by
          simpa only [body, Formula.freeSupport] using hMember
        rcases List.mem_append.mp hMember' with
          hScopes | hShape
        · rcases List.mem_append.mp hScopes with
            hLeft | hRight
          · exact hLeftDepthFreshLeftScope hLeft
          · exact hLeftDepthFreshRightScope hRight
        · exact
            (hShapeFresh (base + 2)
              (Nat.ne_of_gt <|
                Nat.lt_add_of_pos_right (n := base)
                  (by decide : 0 < 2))
              (Nat.ne_of_gt <|
                Nat.add_lt_add_left
                  (by decide : 1 < 2) base)) hShape
      have hLeftDepthFreshRightBody :
          (SetSort.set, base + 2) ∉
            Formula.freeSupport rightBody := by
        have hRightGuardFresh :
            (SetSort.set, base + 2) ∉
              Formula.freeSupport
                      (rightCode ∈ₘ TermCodeₘ) := by
          simp only [rightCode, Formula.freeSupport, Term.freeSupport,
            Term.freeSupportList]
          intro hMember
          have hId : base + 2 = base + 1 :=
            congrArg Prod.snd (List.mem_singleton.mp hMember)
          exact (Nat.ne_of_lt (Nat.add_lt_add_left
            (by decide : 1 < 2) base)) hId.symm
        simp only [rightBody, Formula.freeSupport]
        intro hMember
        rcases List.mem_append.mp hMember with hGuard | hBody
        · exact hRightGuardFresh hGuard
        · exact hLeftDepthFreshBody hBody
      have hLeftDepthFreshRightExists :
          (SetSort.set, base + 2) ∉
            Formula.freeSupport rightExists := by
        simpa [rightExists] using
          Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            (SetSort.set, base + 2)
            SetSort.set (base + 1) 0 rightBody
            hLeftDepthFreshRightBody
      have hLeftDepthFreshLeftBody :
          (SetSort.set, base + 2) ∉
            Formula.freeSupport leftBody := by
        have hLeftGuardFresh :
            (SetSort.set, base + 2) ∉
              Formula.freeSupport
                (leftCode ∈ₘ TermCodeₘ) := by
          simp only [leftCode, Formula.freeSupport, Term.freeSupport,
            Term.freeSupportList]
          intro hMember
          have hId : base + 2 = base :=
            congrArg Prod.snd (List.mem_singleton.mp hMember)
          exact (Nat.ne_of_lt (Nat.lt_add_of_pos_right
            (n := base) (by decide : 0 < 2))) hId.symm
        simp only [leftBody, Formula.freeSupport]
        intro hMember
        rcases List.mem_append.mp hMember with hLeft | hRight
        · exact hLeftGuardFresh hLeft
        · exact hLeftDepthFreshRightExists hRight
      have hLeftDepthFreshCondition :
          (SetSort.set, base + 2) ∉
            Formula.freeSupport condition := by
        simpa [condition] using
          Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            (SetSort.set, base + 2)
            SetSort.set base 0 leftBody
            hLeftDepthFreshLeftBody
      apply
        fs_zfc_support_raw_canonical_scoped_variable_code_condition_with_id_elim
          entryDepth leftCode (base + 2)
          Formula.falsum hLeftCode
          Formula.Admissible.falsum
      · intro formula hFormula
        simp only [Θ, Δ, Γ, List.mem_cons,
          List.not_mem_nil,
          or_false] at hFormula
        rcases hFormula with rfl | rfl | rfl
        · exact hLeftDepthFreshRightBody
        · exact hLeftDepthFreshLeftBody
        · exact hLeftDepthFreshCondition
      · exact List.not_mem_nil
      · simpa [leftScope] using hLeftScopeAt
      · intro leftDepth hLeftDepth
        apply FirstOrder.Derives.impIntro
          (hAntecedentCheck := by prove_nd_formula_check)
        let leftEquality : SetFormula :=
          leftCode ≐ₘ
            canonical_binder_variable_code_term
              (numₘ(leftDepth))
        let Λ : Context signature := leftEquality :: Θ
        have hLeftEquality :
            Λ ⊢ₘ[fs_zfc_support_raw_theory]
              leftCode ≐ₘ
                canonical_binder_variable_code_term
                  (numₘ(leftDepth)) :=
          FirstOrder.Derives.assumption
            (by simp [Λ, leftEquality])
            (by prove_nd_formula_check)
        have hRightScopeAt' :
            Λ ⊢ₘ[fs_zfc_support_raw_theory]
              rightScope :=
          FirstOrder.Derives.context_weaken_cons
            hRightScopeAt
        have hRightDepthFreshLeftScope :
            (SetSort.set, base + 3) ∉
              Formula.freeSupport leftScope := by
          simpa [leftScope,
            canonical_scoped_variable_code_condition_with_id,
            Formula.freeSupport, leftCode] using
            Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
              (SetSort.set, base + 3)
              SetSort.set (base + 2) 0
              ((x#(base + 2) ∈ₘ numₘ(entryDepth)) ∧ₘ
                (x#base ≐ₘ
                  canonical_binder_variable_code_term
                    (x#(base + 2))))
              (hScopeBodyFresh
                (base + 3) base (base + 2)
                (Nat.ne_of_gt <|
                  Nat.add_lt_add_left
                    (by decide : 2 < 3) base)
                (Nat.ne_of_gt <|
                  Nat.lt_add_of_pos_right (n := base)
                    (by decide : 0 < 3)))
        have hRightDepthFreshRightScope :
            (SetSort.set, base + 3) ∉
              Formula.freeSupport rightScope := by
          simpa [rightScope,
            canonical_scoped_variable_code_condition_with_id,
            Formula.freeSupport] using
            Formula.not_mem_freeSupport_closeFreeAt
              SetSort.set (base + 3) 0
              ((x#(base + 3) ∈ₘ numₘ(entryDepth)) ∧ₘ
                (rightCode ≐ₘ
                  canonical_binder_variable_code_term
                    (x#(base + 3))))
        have hRightDepthFreshBody :
            (SetSort.set, base + 3) ∉
              Formula.freeSupport body := by
          intro hMember
          have hMember' :
              (SetSort.set, base + 3) ∈
                (Formula.freeSupport leftScope ++
                  Formula.freeSupport rightScope) ++
                  Formula.freeSupport shapeCases := by
            simpa only [body, Formula.freeSupport] using hMember
          rcases List.mem_append.mp hMember' with
            hScopes | hShape
          · rcases List.mem_append.mp hScopes with
              hLeft | hRight
            · exact hRightDepthFreshLeftScope hLeft
            · exact hRightDepthFreshRightScope hRight
          · exact
              (hShapeFresh (base + 3)
                (Nat.ne_of_gt <|
                  Nat.lt_add_of_pos_right (n := base)
                    (by decide : 0 < 3))
                (Nat.ne_of_gt <|
                  Nat.add_lt_add_left
                    (by decide : 1 < 3) base)) hShape
        have hRightDepthFreshRightBody :
            (SetSort.set, base + 3) ∉
              Formula.freeSupport rightBody := by
          have hRightGuardFresh :
              (SetSort.set, base + 3) ∉
                Formula.freeSupport
                  (rightCode ∈ₘ TermCodeₘ) := by
            simp only [rightCode, Formula.freeSupport, Term.freeSupport,
              Term.freeSupportList]
            intro hMember
            have hId : base + 3 = base + 1 :=
              congrArg Prod.snd (List.mem_singleton.mp hMember)
            exact (Nat.ne_of_lt (Nat.add_lt_add_left
              (by decide : 1 < 3) base)) hId.symm
          simp only [rightBody, Formula.freeSupport]
          intro hMember
          rcases List.mem_append.mp hMember with hGuard | hBody
          · exact hRightGuardFresh hGuard
          · exact hRightDepthFreshBody hBody
        have hRightDepthFreshRightExists :
            (SetSort.set, base + 3) ∉
              Formula.freeSupport rightExists := by
          simpa [rightExists] using
            Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
              (SetSort.set, base + 3)
              SetSort.set (base + 1) 0 rightBody
              hRightDepthFreshRightBody
        have hRightDepthFreshLeftBody :
            (SetSort.set, base + 3) ∉
              Formula.freeSupport leftBody := by
          have hLeftGuardFresh :
              (SetSort.set, base + 3) ∉
                Formula.freeSupport
                  (leftCode ∈ₘ TermCodeₘ) := by
            simp only [leftCode, Formula.freeSupport, Term.freeSupport,
              Term.freeSupportList]
            intro hMember
            have hId : base + 3 = base :=
              congrArg Prod.snd (List.mem_singleton.mp hMember)
            exact (Nat.ne_of_lt (Nat.lt_add_of_pos_right
              (n := base) (by decide : 0 < 3))) hId.symm
          simp only [leftBody, Formula.freeSupport]
          intro hMember
          rcases List.mem_append.mp hMember with hLeft | hRight
          · exact hLeftGuardFresh hLeft
          · exact hRightDepthFreshRightExists hRight
        have hRightDepthFreshCondition :
            (SetSort.set, base + 3) ∉
              Formula.freeSupport condition := by
          simpa [condition] using
            Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
              (SetSort.set, base + 3)
              SetSort.set base 0 leftBody
              hRightDepthFreshLeftBody
        have hRightDepthFreshLeftEquality :
            (SetSort.set, base + 3) ∉
              Formula.freeSupport leftEquality := by
          intro hMember
          have hMember' :
              (SetSort.set, base + 3) ∈
                [(SetSort.set, base)] := by
            simpa only [leftEquality, leftCode,
              Formula.freeSupport, Term.freeSupport,
              Term.freeSupportList,
              finite_numeral_term_freeSupport] using
              hMember
          have hPair :=
            List.mem_singleton.mp hMember'
          exact
            (Nat.ne_of_gt <|
              Nat.lt_add_of_pos_right (n := base)
                (by decide : 0 < 3))
              (congrArg Prod.snd hPair)
        apply
          fs_zfc_support_raw_canonical_scoped_variable_code_condition_with_id_elim
            entryDepth rightCode (base + 3)
            Formula.falsum hRightCode
            Formula.Admissible.falsum
        · intro formula hFormula
          simp only [Θ, Δ, Γ, List.mem_cons,
            List.not_mem_nil,
            or_false] at hFormula
          rcases hFormula with rfl | rfl | rfl | rfl
          · exact hRightDepthFreshLeftEquality
          · exact hRightDepthFreshRightBody
          · exact hRightDepthFreshLeftBody
          · exact hRightDepthFreshCondition
        · exact List.not_mem_nil
        · simpa [rightScope] using hRightScopeAt'
        · intro rightDepth hRightDepth
          apply FirstOrder.Derives.impIntro
            (hAntecedentCheck := by prove_nd_formula_check)
          let rightEquality : SetFormula :=
            rightCode ≐ₘ
              canonical_binder_variable_code_term
                (numₘ(rightDepth))
          let Μ : Context signature := rightEquality :: Λ
          have hRightEquality :
              Μ ⊢ₘ[fs_zfc_support_raw_theory]
                rightCode ≐ₘ
                  canonical_binder_variable_code_term
                    (numₘ(rightDepth)) :=
            FirstOrder.Derives.assumption
              (by simp [Μ, rightEquality])
              (by prove_nd_formula_check)
          have hLeftEquality' :
              Μ ⊢ₘ[fs_zfc_support_raw_theory]
                leftCode ≐ₘ
                  canonical_binder_variable_code_term
                    (numₘ(leftDepth)) :=
            FirstOrder.Derives.context_weaken_cons
              hLeftEquality
          have hLeftNamedCode :
              Term.Admissible
                (GodelQuotation.Numbered.named_variable_code
                  (GodelQuotation.bound_name leftDepth))
                SetSort.set :=
            variable_code_term_admissible _
              (finite_numeral_term_admissible
                (GodelQuotation.bound_name leftDepth))
          have hRightNamedCode :
              Term.Admissible
                (GodelQuotation.Numbered.named_variable_code
                  (GodelQuotation.bound_name rightDepth))
                SetSort.set :=
            variable_code_term_admissible _
              (finite_numeral_term_admissible
                (GodelQuotation.bound_name rightDepth))
          have hLeftNamed :
              Μ ⊢ₘ[fs_zfc_support_raw_theory]
                leftCode ≐ₘ
                  GodelQuotation.Numbered.named_variable_code
                    (GodelQuotation.bound_name leftDepth) :=
            Metatheory.Derives.equality_trans
              hLeftEquality' <|
              Metatheory.Derives.equality_symm <|
                FirstOrder.Derives.context_weaken
                  (Γ := []) (Δ := Μ) (by simp) <|
                    fs_zfc_support_raw_derives_of_godel_quotation <|
                      canonical_binder_variable_code_numeral_derives
                        leftDepth
          have hRightNamed :
              Μ ⊢ₘ[fs_zfc_support_raw_theory]
                rightCode ≐ₘ
                  GodelQuotation.Numbered.named_variable_code
                    (GodelQuotation.bound_name rightDepth) :=
            Metatheory.Derives.equality_trans
              hRightEquality <|
              Metatheory.Derives.equality_symm <|
                FirstOrder.Derives.context_weaken
                  (Γ := []) (Δ := Μ) (by simp) <|
                    fs_zfc_support_raw_derives_of_godel_quotation <|
                      canonical_binder_variable_code_numeral_derives
                        rightDepth
          have hShapeCasesAt' :
              Μ ⊢ₘ[fs_zfc_support_raw_theory]
                shapeCases :=
            FirstOrder.Derives.context_weaken_cons <|
              FirstOrder.Derives.context_weaken_cons
                hShapeCasesAt
          apply FirstOrder.Derives.disjElim hShapeCasesAt'
          · let Ν : Context signature := equalityShape :: Μ
            have hShape :
                Ν ⊢ₘ[fs_zfc_support_raw_theory]
                  standard_token_sequence tokens ≐ₘ
                    eq_codeₘ(leftCode, rightCode) :=
              FirstOrder.Derives.assumption
                (by simp [Ν, equalityShape])
                (Formula.check_admissible_complete
                  hEqualityShape)
            have hConstructor :=
              canonical_equality_code_term_congr_of_equalities
                leftCode
                (GodelQuotation.Numbered.named_variable_code
                  (GodelQuotation.bound_name leftDepth))
                rightCode
                (GodelQuotation.Numbered.named_variable_code
                  (GodelQuotation.bound_name rightDepth))
                hLeftCode
                hLeftNamedCode
                hRightCode
                hRightNamedCode
                (FirstOrder.Derives.context_weaken_cons
                  (assumption := equalityShape)
                  hLeftNamed)
                (FirstOrder.Derives.context_weaken_cons
                  (assumption := equalityShape)
                  hRightNamed)
            have hCode :
                Ν ⊢ₘ[fs_zfc_support_raw_theory]
                  standard_token_sequence tokens ≐ₘ
                    CanonicalProjectTrace.canonical_project_atom_code
                      .equality leftDepth rightDepth := by
              simpa [CanonicalProjectTrace.canonical_project_atom_code] using
                Metatheory.Derives.equality_trans
                  hShape hConstructor
            have hStandard :
                Ν ⊢ₘ[fs_zfc_support_raw_theory]
                  standard_token_sequence tokens ≐ₘ
                    standard_token_sequence
                      (CanonicalProjectTrace.canonical_project_atom_tokens
                        .equality leftDepth rightDepth) :=
              Metatheory.Derives.equality_trans hCode <|
                FirstOrder.Derives.context_weaken
                  (Γ := []) (Δ := Ν) (by simp) <|
                    fs_zfc_support_raw_derives_of_godel_quotation <|
                      CanonicalProjectTrace.canonical_project_atom_code_eq_standard_token_sequence
                        .equality leftDepth rightDepth
            exact FirstOrder.Derives.negElim
              hStandard <|
                FirstOrder.Derives.context_weaken
                  (Γ := []) (Δ := Ν) (by simp) <|
                    fs_zfc_support_raw_derives_of_standard_sequence <|
                      standard_token_sequence_ne
                        (hNoMatch .equality
                          leftDepth rightDepth
                          hLeftDepth hRightDepth)
          · let tailShapes : SetFormula :=
              membershipShape ∨ₘ subsetShape
            let Ν : Context signature := tailShapes :: Μ
            have hTail :
                Ν ⊢ₘ[fs_zfc_support_raw_theory]
                  membershipShape ∨ₘ subsetShape :=
              FirstOrder.Derives.assumption
                (by simp [Ν, tailShapes])
                (by prove_nd_formula_check)
            apply FirstOrder.Derives.disjElim hTail
            · let Ξ : Context signature := membershipShape :: Ν
              have hShape :
                  Ξ ⊢ₘ[fs_zfc_support_raw_theory]
                    standard_token_sequence tokens ≐ₘ
                      membership_atomic_formula_code_term
                        leftCode rightCode :=
                FirstOrder.Derives.assumption
                  (by simp [Ξ, membershipShape])
                  (Formula.check_admissible_complete
                    hMembershipShape)
              have hConstructor :=
                canonical_membership_atomic_code_term_congr_of_equalities
                  leftCode
                  (GodelQuotation.Numbered.named_variable_code
                    (GodelQuotation.bound_name leftDepth))
                  rightCode
                  (GodelQuotation.Numbered.named_variable_code
                    (GodelQuotation.bound_name rightDepth))
                  hLeftCode
                  hLeftNamedCode
                  hRightCode
                  hRightNamedCode
                  (FirstOrder.Derives.context_weaken_cons
                    (assumption := membershipShape) <|
                    FirstOrder.Derives.context_weaken_cons
                      (assumption := tailShapes)
                      hLeftNamed)
                  (FirstOrder.Derives.context_weaken_cons
                    (assumption := membershipShape) <|
                    FirstOrder.Derives.context_weaken_cons
                      (assumption := tailShapes)
                      hRightNamed)
              have hCode :
                  Ξ ⊢ₘ[fs_zfc_support_raw_theory]
                    standard_token_sequence tokens ≐ₘ
                      CanonicalProjectTrace.canonical_project_atom_code
                        .membership leftDepth rightDepth := by
                simpa [CanonicalProjectTrace.canonical_project_atom_code] using
                  Metatheory.Derives.equality_trans
                    hShape hConstructor
              have hStandard :
                  Ξ ⊢ₘ[fs_zfc_support_raw_theory]
                    standard_token_sequence tokens ≐ₘ
                      standard_token_sequence
                        (CanonicalProjectTrace.canonical_project_atom_tokens
                          .membership leftDepth rightDepth) :=
                Metatheory.Derives.equality_trans hCode <|
                  FirstOrder.Derives.context_weaken
                    (Γ := []) (Δ := Ξ) (by simp) <|
                      fs_zfc_support_raw_derives_of_godel_quotation <|
                        CanonicalProjectTrace.canonical_project_atom_code_eq_standard_token_sequence
                          .membership leftDepth rightDepth
              exact FirstOrder.Derives.negElim
                hStandard <|
                  FirstOrder.Derives.context_weaken
                    (Γ := []) (Δ := Ξ) (by simp) <|
                      fs_zfc_support_raw_derives_of_standard_sequence <|
                        standard_token_sequence_ne
                          (hNoMatch .membership
                            leftDepth rightDepth
                            hLeftDepth hRightDepth)
            · let Ξ : Context signature := subsetShape :: Ν
              have hShape :
                  Ξ ⊢ₘ[fs_zfc_support_raw_theory]
                    standard_token_sequence tokens ≐ₘ
                      project_subset_atomic_code_term
                        leftCode rightCode :=
                FirstOrder.Derives.assumption
                  (by simp [Ξ, subsetShape])
                  (Formula.check_admissible_complete
                    hSubsetShape)
              have hConstructor :=
                canonical_project_subset_atomic_code_term_congr_of_equalities
                  leftCode
                  (GodelQuotation.Numbered.named_variable_code
                    (GodelQuotation.bound_name leftDepth))
                  rightCode
                  (GodelQuotation.Numbered.named_variable_code
                    (GodelQuotation.bound_name rightDepth))
                  hLeftCode
                  hLeftNamedCode
                  hRightCode
                  hRightNamedCode
                  (FirstOrder.Derives.context_weaken_cons
                    (assumption := subsetShape) <|
                    FirstOrder.Derives.context_weaken_cons
                      (assumption := tailShapes)
                      hLeftNamed)
                  (FirstOrder.Derives.context_weaken_cons
                    (assumption := subsetShape) <|
                    FirstOrder.Derives.context_weaken_cons
                      (assumption := tailShapes)
                      hRightNamed)
              have hCode :
                  Ξ ⊢ₘ[fs_zfc_support_raw_theory]
                    standard_token_sequence tokens ≐ₘ
                      CanonicalProjectTrace.canonical_project_atom_code
                        .subset leftDepth rightDepth := by
                simpa [CanonicalProjectTrace.canonical_project_atom_code] using
                  Metatheory.Derives.equality_trans
                    hShape hConstructor
              have hStandard :
                  Ξ ⊢ₘ[fs_zfc_support_raw_theory]
                    standard_token_sequence tokens ≐ₘ
                      standard_token_sequence
                        (CanonicalProjectTrace.canonical_project_atom_tokens
                          .subset leftDepth rightDepth) :=
                Metatheory.Derives.equality_trans hCode <|
                  FirstOrder.Derives.context_weaken
                    (Γ := []) (Δ := Ξ) (by simp) <|
                      fs_zfc_support_raw_derives_of_godel_quotation <|
                        CanonicalProjectTrace.canonical_project_atom_code_eq_standard_token_sequence
                          .subset leftDepth rightDepth
              exact FirstOrder.Derives.negElim
                hStandard <|
                  FirstOrder.Derives.context_weaken
                    (Γ := []) (Δ := Ξ) (by simp) <|
                      fs_zfc_support_raw_derives_of_standard_sequence <|
                        standard_token_sequence_ne
                          (hNoMatch .subset
                            leftDepth rightDepth
                            hLeftDepth hRightDepth)


theorem fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_separation_generate
    (formula : SetTerm)
    (certificate : Nat)
    (candidate : SetFormula)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_support_generate certificate = some candidate)
    (hFormulaNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (formula ≐ₘ fs_zfc_formula_code_term candidate)))
    (hOuter :
      (godel_unpair_value certificate).1 = 1)
    (hSeparation :
      (godel_unpair_value
        (godel_unpair_value certificate).2).1 = 0) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition_with_base
        formula (numₘ(certificate)) base) := by
  let payload : Nat := (godel_unpair_value certificate).2
  let schemaPayload : Nat := (godel_unpair_value payload).2
  have hPayload :
      payload = godel_pair_value 0 schemaPayload := by
    calc
      payload =
          godel_pair_value
            (godel_unpair_value payload).1
            (godel_unpair_value payload).2 := by
        exact (godel_unpair_value_spec payload).symm
      _ = godel_pair_value 0 schemaPayload := by
        simp [payload, schemaPayload, hSeparation]
  have hRaw :
      certificate =
        godel_pair_value 1
          (godel_pair_value 0 schemaPayload) := by
    calc
      certificate =
          godel_pair_value
            (godel_unpair_value certificate).1
            (godel_unpair_value certificate).2 := by
        exact (godel_unpair_value_spec certificate).symm
      _ = godel_pair_value 1 payload := by
        simp [payload, hOuter]
      _ = godel_pair_value 1
          (godel_pair_value 0 schemaPayload) := by
        rw [hPayload]
  rw [hRaw] at hGenerate
  have hSchemaGenerate :
      (fs_zfc_separation_generate schemaPayload).map
        (fun sentence =>
          Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence)) =
        some candidate := by
    simpa [fs_zfc_support_generate,
      fs_zfc_embedded_hilbert_generator,
      fs_zfc_axiom_generate,
      godel_unpair_value_pair] using hGenerate
  unfold fs_zfc_separation_generate at hSchemaGenerate
  dsimp only at hSchemaGenerate
  cases hDecode :
      fs_project_unary_schema_hilbert_decode
        (godel_unpair_value schemaPayload).1
        (godel_unpair_value schemaPayload).2 with
  | none =>
      simp only [hDecode, Option.map_none] at hSchemaGenerate
      cases hSchemaGenerate
  | some schema =>
      simp only [hDecode, Option.map_some,
        Option.some.injEq] at hSchemaGenerate
      have hGenerate := hSchemaGenerate
      subst candidate
      have hBodyDecode :=
        fs_project_unary_schema_hilbert_decode_body hDecode
      have hBodyCode :
          (godel_unpair_value schemaPayload).2 =
            nat_sequence_code_value
              (fs_project_hilbert_token_tree schema.body).tokens :=
        fs_project_hilbert_code_decode_code_eq hBodyDecode
      have hSchemaPayload :
          schemaPayload =
            fs_zfc_schema_certificate
              (godel_unpair_value schemaPayload).1
              (nat_sequence_code_value
                (fs_project_hilbert_token_tree schema.body).tokens) := by
        calc
          schemaPayload =
              godel_pair_value
                (godel_unpair_value schemaPayload).1
                (godel_unpair_value schemaPayload).2 := by
            exact (godel_unpair_value_spec schemaPayload).symm
          _ =
              fs_zfc_schema_certificate
                (godel_unpair_value schemaPayload).1
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens) := by
            simp [fs_zfc_schema_certificate, hBodyCode]
      have hCertificate :
          certificate =
            godel_pair_value 1
              (godel_pair_value 0
                (fs_zfc_schema_certificate
                  (godel_unpair_value schemaPayload).1
                  (nat_sequence_code_value
                    (fs_project_hilbert_token_tree schema.body).tokens))) := by
        exact hRaw.trans <|
          congrArg
            (fun value => godel_pair_value 1
              (godel_pair_value 0 value))
            hSchemaPayload
      apply
        fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_branch_negs
          formula (numₘ(certificate)) base
          hFormula (finite_numeral_term_admissible certificate)
      · rw [hCertificate]
        exact
          fs_zfc_support_raw_fixed_table_condition_neg_of_schema_code
            formula
            (godel_pair_value 0
              (fs_zfc_schema_certificate
                (godel_unpair_value schemaPayload).1
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens)))
            hFormula
      · exact
          fs_zfc_schema_plugins_elim
            (by
              rw [hCertificate]
              exact
                fs_zfc_support_raw_separation_condition_with_base_neg_of_schema_formula_ne
                  schema formula base hFormula hFormulaClosed hFormulaNe)
            (by
              apply
                fs_zfc_support_raw_collection_condition_with_base_neg_of_code_ne
                  formula certificate base hFormula
              intro parameterValue bodyTokenValue hEquality
              rw [hCertificate] at hEquality
              exact Nat.zero_ne_one <|
                (godel_pair_value_eq_iff.mp <|
                  (godel_pair_value_eq_iff.mp hEquality).2).1)

/-- 收集生成分支的公式内容不匹配会否定完整显式-base 对象 verifier。 -/
theorem fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_collection_generate
    (formula : SetTerm)
    (certificate : Nat)
    (candidate : SetFormula)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_support_generate certificate = some candidate)
    (hFormulaNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (formula ≐ₘ fs_zfc_formula_code_term candidate)))
    (hOuter :
      (godel_unpair_value certificate).1 = 1)
    (hCollection :
      (godel_unpair_value
        (godel_unpair_value certificate).2).1 = 1) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition_with_base
        formula (numₘ(certificate)) base) := by
  let payload : Nat := (godel_unpair_value certificate).2
  let schemaPayload : Nat := (godel_unpair_value payload).2
  have hPayload :
      payload = godel_pair_value 1 schemaPayload := by
    calc
      payload =
          godel_pair_value
            (godel_unpair_value payload).1
            (godel_unpair_value payload).2 := by
        exact (godel_unpair_value_spec payload).symm
      _ = godel_pair_value 1 schemaPayload := by
        simp [payload, schemaPayload, hCollection]
  have hRaw :
      certificate =
        godel_pair_value 1
          (godel_pair_value 1 schemaPayload) := by
    calc
      certificate =
          godel_pair_value
            (godel_unpair_value certificate).1
            (godel_unpair_value certificate).2 := by
        exact (godel_unpair_value_spec certificate).symm
      _ = godel_pair_value 1 payload := by
        simp [payload, hOuter]
      _ = godel_pair_value 1
          (godel_pair_value 1 schemaPayload) := by
        rw [hPayload]
  rw [hRaw] at hGenerate
  have hSchemaGenerate :
      (fs_zfc_collection_generate schemaPayload).map
        (fun sentence =>
          Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence)) =
        some candidate := by
    simpa [fs_zfc_support_generate,
      fs_zfc_embedded_hilbert_generator,
      fs_zfc_axiom_generate,
      godel_unpair_value_pair] using hGenerate
  unfold fs_zfc_collection_generate at hSchemaGenerate
  dsimp only at hSchemaGenerate
  cases hDecode :
      fs_project_binary_schema_hilbert_decode
        (godel_unpair_value schemaPayload).1
        (godel_unpair_value schemaPayload).2 with
  | none =>
      simp only [hDecode, Option.map_none] at hSchemaGenerate
      cases hSchemaGenerate
  | some schema =>
      simp only [hDecode, Option.map_some,
        Option.some.injEq] at hSchemaGenerate
      have hGenerate := hSchemaGenerate
      subst candidate
      have hBodyDecode :=
        fs_project_binary_schema_hilbert_decode_body hDecode
      have hBodyCode :
          (godel_unpair_value schemaPayload).2 =
            nat_sequence_code_value
              (fs_project_hilbert_token_tree schema.body).tokens :=
        fs_project_hilbert_code_decode_code_eq hBodyDecode
      have hSchemaPayload :
          schemaPayload =
            fs_zfc_schema_certificate
              (godel_unpair_value schemaPayload).1
              (nat_sequence_code_value
                (fs_project_hilbert_token_tree schema.body).tokens) := by
        calc
          schemaPayload =
              godel_pair_value
                (godel_unpair_value schemaPayload).1
                (godel_unpair_value schemaPayload).2 := by
            exact (godel_unpair_value_spec schemaPayload).symm
          _ =
              fs_zfc_schema_certificate
                (godel_unpair_value schemaPayload).1
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens) := by
            simp [fs_zfc_schema_certificate, hBodyCode]
      have hCertificate :
          certificate =
            godel_pair_value 1
              (godel_pair_value 1
                (fs_zfc_schema_certificate
                  (godel_unpair_value schemaPayload).1
                  (nat_sequence_code_value
                    (fs_project_hilbert_token_tree schema.body).tokens))) := by
        exact hRaw.trans <|
          congrArg
            (fun value => godel_pair_value 1
              (godel_pair_value 1 value))
            hSchemaPayload
      apply
        fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_branch_negs
          formula (numₘ(certificate)) base
          hFormula (finite_numeral_term_admissible certificate)
      · rw [hCertificate]
        exact
          fs_zfc_support_raw_fixed_table_condition_neg_of_schema_code
            formula
            (godel_pair_value 1
              (fs_zfc_schema_certificate
                (godel_unpair_value schemaPayload).1
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens)))
            hFormula
      · exact
          fs_zfc_schema_plugins_elim
            (by
              apply
                fs_zfc_support_raw_separation_condition_with_base_neg_of_code_ne
                  formula certificate base hFormula
              intro parameterValue bodyTokenValue hEquality
              rw [hCertificate] at hEquality
              exact Nat.one_ne_zero <|
                (godel_pair_value_eq_iff.mp <|
                  (godel_pair_value_eq_iff.mp hEquality).2).1)
            (by
              rw [hCertificate]
              exact
                fs_zfc_support_raw_collection_condition_with_base_neg_of_schema_formula_ne
                  schema formula base hFormula hFormulaClosed hFormulaNe)

/-- 分离生成分支的动态 fresh-base 包装。 -/
theorem fs_zfc_support_raw_object_certificate_condition_neg_of_separation_generate
    (formula : SetTerm)
    (certificate : Nat)
    (candidate : SetFormula)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_support_generate certificate = some candidate)
    (hFormulaNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (formula ≐ₘ fs_zfc_formula_code_term candidate)))
    (hOuter :
      (godel_unpair_value certificate).1 = 1)
    (hSeparation :
      (godel_unpair_value
        (godel_unpair_value certificate).2).1 = 0) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition
        formula (numₘ(certificate))) := by
  exact
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_separation_generate
      formula certificate candidate
      (ProofT.schema_base [formula, numₘ(certificate)])
      hFormula hFormulaClosed hGenerate hFormulaNe hOuter hSeparation

/-- 收集生成分支的动态 fresh-base 包装。 -/
theorem fs_zfc_support_raw_object_certificate_condition_neg_of_collection_generate
    (formula : SetTerm)
    (certificate : Nat)
    (candidate : SetFormula)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_support_generate certificate = some candidate)
    (hFormulaNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (formula ≐ₘ fs_zfc_formula_code_term candidate)))
    (hOuter :
      (godel_unpair_value certificate).1 = 1)
    (hCollection :
      (godel_unpair_value
        (godel_unpair_value certificate).2).1 = 1) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition
        formula (numₘ(certificate))) := by
  exact
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_collection_generate
      formula certificate candidate
      (ProofT.schema_base [formula, numₘ(certificate)])
      hFormula hFormulaClosed hGenerate hFormulaNe hOuter hCollection

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
