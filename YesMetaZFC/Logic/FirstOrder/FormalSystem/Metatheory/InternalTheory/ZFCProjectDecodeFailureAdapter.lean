import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectCertificateSchemaRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalFirstOrderFailureAdapter
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaCompositeConstructorDisjointness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaFormulaShiftLineInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCProjectDecodeHostClosure
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCProjectDecodeObjectClosure

/-!
# Project 公式分类器的解码失败适配

本模块只把宿主 Project decoder 的失败视图转换为对象分类条件的否定。
成功反演仍由既有公式码与有限序列设施承担；decoder 构造闭包不进入公开接口。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.SetTheory.Definitional.Project
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation

set_option autoImplicit false

/-! ## 递归适配所需的 fresh 存在消去 -/

theorem fs_zfc_support_raw_exists_elim_fresh
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (reserved : List FreeVarId)
    (binderId : FreeVarId)
    (body conclusion : SetFormula)
    (hExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, binderId],
          body)
    (hCase :
      ∀ eigen,
        (∀ id, id ∈ reserved →
          (Nonlogical.BasicSetTheory.SetSort.set, id) ∉
            Term.freeSupport
              (x#eigen :
                Nonlogical.BasicSetTheory.SetTerm)) →
          Formula.CheckCertificate
            (Formula.substituteFree
              Nonlogical.BasicSetTheory.SetSort.set
              binderId (x#eigen) body) →
          Formula.substituteFree
              Nonlogical.BasicSetTheory.SetSort.set
              binderId (x#eigen) body :: Γ
            ⊢ₘ[fs_zfc_support_raw_theory] conclusion) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] conclusion := by
  let closed :=
    Formula.closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      binderId 0 body
  let guards : List SetFormula :=
    reserved.map fun id =>
      (x#id : SetTerm) ≐ₘ x#id
  let basis := guards ++ closed :: conclusion :: Γ
  let eigen :=
    FreshVariable.fresh_id
      Nonlogical.BasicSetTheory.SetSort.set basis
  let opened :=
    Formula.openAt
      Nonlogical.BasicSetTheory.SetSort.set
      0 (x#eigen) closed
  have hBodyFresh :
      (Nonlogical.BasicSetTheory.SetSort.set, eigen) ∉
        Formula.freeSupport closed := by
    dsimp [eigen, basis]
    exact FreshVariable.fresh_id_not_mem_m
      (formula := closed) (by simp)
  have hConclusionFresh :
      (Nonlogical.BasicSetTheory.SetSort.set, eigen) ∉
        Formula.freeSupport conclusion := by
    dsimp [eigen, basis]
    exact FreshVariable.fresh_id_not_mem_m
      (formula := conclusion) (by simp)
  have hOpened :
      Formula.Admissible opened := by
    dsimp [opened]
    exact Formula.Admissible.exists_openAt
      (body := closed)
      (term :=
        (x#eigen :
          Nonlogical.BasicSetTheory.SetTerm))
      Nonlogical.BasicSetTheory.SetSort.set
      hExists.admissible
      (set_variable_admissible eigen)
  have hReservedFresh :
      ∀ id, id ∈ reserved →
        (Nonlogical.BasicSetTheory.SetSort.set, id) ∉
          Term.freeSupport
            (x#eigen :
              Nonlogical.BasicSetTheory.SetTerm) := by
    intro id hId
    apply
      CertifiedProof.fs_zfc_fo_failure_set_variable_fresh
    intro hEqual
    have hGuardFresh :
        (Nonlogical.BasicSetTheory.SetSort.set, eigen) ∉
          Formula.freeSupport
            ((x#id :
              Nonlogical.BasicSetTheory.SetTerm) ≐ₘ x#id) := by
      dsimp [eigen, basis]
      apply FreshVariable.fresh_id_not_mem_m
      simp [guards, hId]
    apply hGuardFresh
    change
      (Nonlogical.BasicSetTheory.SetSort.set, eigen) ∈ [
        (Nonlogical.BasicSetTheory.SetSort.set, id),
        (Nonlogical.BasicSetTheory.SetSort.set, id)]
    simp [hEqual]
  apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := Nonlogical.BasicSetTheory.SetSort.set)
    (eigen := eigen)
    (body := opened)
    (conclusion := conclusion)
    (hBodyCheck :=
      Formula.check_admissible_complete hOpened)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    dsimp [eigen, basis]
    apply FreshVariable.fresh_id_not_mem_m
    simp [hFormula]
  · exact hConclusionFresh
  · simpa [opened,
      Formula.closeFreeAt_openAt
        Nonlogical.BasicSetTheory.SetSort.set
        eigen 0 closed hBodyFresh, closed] using hExists
  · have hOpenedCheck :
        Formula.CheckCertificate opened :=
      Formula.check_admissible_complete hOpened
    simpa [opened, closed,
      Formula.openAt_closeFreeAt_eq_substituteFree] using
      hCase eigen hReservedFresh (by
        simpa [opened, closed,
          Formula.openAt_closeFreeAt_eq_substituteFree] using
          hOpenedCheck)

theorem fs_zfc_support_raw_exists₂_elim_fresh
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (reserved : List FreeVarId)
    (firstId secondId : FreeVarId)
    (body conclusion : SetFormula)
    (hIds : firstId ≠ secondId)
    (hSecondReserved : secondId ∈ reserved)
    (hExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, firstId],
          ∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, secondId],
            body)
    (hCase :
      ∀ firstEigen secondEigen,
        (∀ id, id ∈ reserved →
          (Nonlogical.BasicSetTheory.SetSort.set, id) ∉
            Term.freeSupport (x#firstEigen : SetTerm)) →
        (∀ id, id ∈ reserved →
          (Nonlogical.BasicSetTheory.SetSort.set, id) ∉
            Term.freeSupport (x#secondEigen : SetTerm)) →
        Formula.CheckCertificate
          (Formula.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set secondId
            (x#secondEigen)
            (Formula.substituteFree
              Nonlogical.BasicSetTheory.SetSort.set firstId
              (x#firstEigen) body)) →
        Formula.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set secondId
            (x#secondEigen)
            (Formula.substituteFree
              Nonlogical.BasicSetTheory.SetSort.set firstId
              (x#firstEigen) body) ::
          Formula.substituteFree
              Nonlogical.BasicSetTheory.SetSort.set firstId
              (x#firstEigen)
              (∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, secondId],
                body) :: Γ
          ⊢ₘ[fs_zfc_support_raw_theory] conclusion) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] conclusion := by
  apply fs_zfc_support_raw_exists_elim_fresh
    reserved firstId
    (∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, secondId], body)
    conclusion hExists
  intro firstEigen hFirstFresh hOuterCheck
  let first : SetTerm := x#firstEigen
  let outer : SetFormula :=
    Formula.substituteFree
      Nonlogical.BasicSetTheory.SetSort.set firstId first
      (∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, secondId], body)
  let Δ : Context Nonlogical.BasicSetTheory.signature :=
    outer :: Γ
  have hOuter :
      Δ ⊢ₘ[fs_zfc_support_raw_theory] outer :=
    FirstOrder.Derives.assumption (by simp [Δ]) hOuterCheck
  have hComm :
      Formula.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set firstId first
          (Formula.closeFreeAt
            Nonlogical.BasicSetTheory.SetSort.set secondId 0 body) =
        Formula.closeFreeAt
          Nonlogical.BasicSetTheory.SetSort.set secondId 0
          (Formula.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set firstId first body) :=
    (Formula.closeFreeAt_substituteFree_comm
      Nonlogical.BasicSetTheory.SetSort.set
      firstId secondId 0 first body hIds
      (set_variable_admissible firstEigen).2
      (by
        intro hEqual
        apply hFirstFresh secondId hSecondReserved
        change
          (Nonlogical.BasicSetTheory.SetSort.set, secondId) ∈
            [(Nonlogical.BasicSetTheory.SetSort.set, firstEigen)]
        change
          (Nonlogical.BasicSetTheory.SetSort.set, secondId) ∈
            [(Nonlogical.BasicSetTheory.SetSort.set, firstEigen)]
          at hEqual
        exact hEqual)).symm
  have hSecondExists :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, secondId],
          Formula.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set
            firstId first body := by
    simpa [outer, first, Formula.substituteFree, hComm] using
      hOuter
  apply fs_zfc_support_raw_exists_elim_fresh
    reserved secondId
    (Formula.substituteFree
      Nonlogical.BasicSetTheory.SetSort.set firstId first body)
    conclusion hSecondExists
  intro secondEigen hSecondFresh hInnerCheck
  simpa [first, outer, Δ] using
    hCase firstEigen secondEigen
      hFirstFresh hSecondFresh hInnerCheck

private theorem fs_zfc_support_raw_project_line_of_all
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (codes depths point : SetTerm)
    (indexId firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId :
      FreeVarId)
    (hPoint :
      Term.CheckCertificate point
        Nonlogical.BasicSetTheory.SetSort.set)
    (hCodesFresh :
      (Nonlogical.BasicSetTheory.SetSort.set,
        indexId) ∉
        Term.freeSupport codes)
    (hDepthsFresh :
      (Nonlogical.BasicSetTheory.SetSort.set,
        indexId) ∉
        Term.freeSupport depths)
    (hIndexFresh :
      ∀ id,
        id ∈ [
          firstPremiseId, secondPremiseId,
          leftVariableCodeId, rightVariableCodeId,
          leftVariableDepthId, rightVariableDepthId] →
        indexId ≠ id)
    (hPointFresh :
      ∀ id,
        id ∈ [
          firstPremiseId, secondPremiseId,
          leftVariableCodeId, rightVariableCodeId,
          leftVariableDepthId, rightVariableDepthId] →
        (Nonlogical.BasicSetTheory.SetSort.set,
          id) ∉
          Term.freeSupport point)
    (hAll :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∀ₘ[Nonlogical.BasicSetTheory.SetSort.set,
          indexId],
          (x#indexId ∈ₘ domₘ(codes)) ⟶ₘ
            canonical_project_formula_line_condition_with_ids
              codes depths (x#indexId)
              firstPremiseId secondPremiseId
              leftVariableCodeId rightVariableCodeId
              leftVariableDepthId rightVariableDepthId)
    (hDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        point ∈ₘ domₘ(codes)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      canonical_project_formula_line_condition_with_ids
        codes depths point
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId := by
  have hCodesFixed :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          indexId
          point codes =
        codes :=
    Term.substituteFree_eq_self_of_not_mem
      Nonlogical.BasicSetTheory.SetSort.set
      indexId point codes hCodesFresh
  have hDepthsFixed :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          indexId
          point depths =
        depths :=
    Term.substituteFree_eq_self_of_not_mem
      Nonlogical.BasicSetTheory.SetSort.set
      indexId point depths hDepthsFresh
  have hNumeralFixed (number : Nat) :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          indexId point (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hComm
      (binderId : FreeVarId)
      (hNe : indexId ≠ binderId)
      (hFresh :
        (Nonlogical.BasicSetTheory.SetSort.set,
          binderId) ∉
          Term.freeSupport point)
      (formula : SetFormula) :
      Formula.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          indexId point
          (Formula.closeFreeAt
            Nonlogical.BasicSetTheory.SetSort.set
            binderId 0 formula) =
        Formula.closeFreeAt
          Nonlogical.BasicSetTheory.SetSort.set
          binderId 0
          (Formula.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set
            indexId point formula) :=
    (Formula.closeFreeAt_substituteFree_comm
      Nonlogical.BasicSetTheory.SetSort.set
      indexId binderId 0 point formula
      hNe hPoint.admissible.2 hFresh).symm
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := point) hAll
      (hTermCheck := hPoint)
  rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    at hAt
  have hAt' :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (point ∈ₘ domₘ(codes)) ⟶ₘ
          canonical_project_formula_line_condition_with_ids
            codes depths point
            firstPremiseId secondPremiseId
            leftVariableCodeId rightVariableCodeId
            leftVariableDepthId rightVariableDepthId := by
    simpa [
      canonical_project_formula_line_condition_with_ids,
      canonical_project_atomic_code_condition_with_ids,
      canonical_scoped_variable_code_condition_with_id,
      Formula.substituteFree, Term.substituteFree,
      GodelQuotation.Numbered.argument_sequence,
      GodelQuotation.standard_sequence_from,
      set_variable, hCodesFixed, hDepthsFixed,
      hNumeralFixed,
      hComm firstPremiseId
        (hIndexFresh firstPremiseId (by simp))
        (hPointFresh firstPremiseId (by simp)),
      hComm secondPremiseId
        (hIndexFresh secondPremiseId (by simp))
        (hPointFresh secondPremiseId (by simp)),
      hComm leftVariableCodeId
        (hIndexFresh leftVariableCodeId (by simp))
        (hPointFresh leftVariableCodeId (by simp)),
      hComm rightVariableCodeId
        (hIndexFresh rightVariableCodeId (by simp))
        (hPointFresh rightVariableCodeId (by simp)),
      hComm leftVariableDepthId
        (hIndexFresh leftVariableDepthId (by simp))
        (hPointFresh leftVariableDepthId (by simp)),
      hComm rightVariableDepthId
        (hIndexFresh rightVariableDepthId (by simp))
        (hPointFresh rightVariableDepthId (by simp)),
      Ne.symm
        (hIndexFresh firstPremiseId (by simp)),
      Ne.symm
        (hIndexFresh secondPremiseId (by simp)),
      Ne.symm
        (hIndexFresh leftVariableCodeId (by simp)),
      Ne.symm
        (hIndexFresh rightVariableCodeId (by simp)),
      Ne.symm
        (hIndexFresh leftVariableDepthId (by simp)),
      Ne.symm
        (hIndexFresh rightVariableDepthId (by simp))
    ] using hAt
  exact FirstOrder.Derives.impElim hAt' hDomain

/-! ## Project decoder 失败的逐行递归适配 -/

theorem fs_zfc_support_raw_project_line_falsum_of_decode_none
    (depth : Nat) (tokens : List Nat)
    (base : FreeVarId)
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (codes depths point : SetTerm)
    (hCodes :
      Term.CheckCertificate codes
        Nonlogical.BasicSetTheory.SetSort.set)
    (hDepths :
      Term.CheckCertificate depths
        Nonlogical.BasicSetTheory.SetSort.set)
    (hPoint :
      Term.CheckCertificate point
        Nonlogical.BasicSetTheory.SetSort.set)
    (hCodesFresh :
      ∀ id, id ∈ [
        base + 3, base + 4, base + 5,
        base + 6, base + 7, base + 8,
        base + 9, base + 10, base + 11] →
        (Nonlogical.BasicSetTheory.SetSort.set, id) ∉
          Term.freeSupport codes)
    (hDepthsFresh :
      ∀ id, id ∈ [
        base + 3, base + 4, base + 5,
        base + 6, base + 7, base + 8,
        base + 9, base + 10, base + 11] →
        (Nonlogical.BasicSetTheory.SetSort.set, id) ∉
          Term.freeSupport depths)
    (hPointFresh :
      ∀ id, id ∈ [
        base + 3, base + 4, base + 5,
        base + 6, base + 7, base + 8,
        base + 9, base + 10, base + 11] →
        (Nonlogical.BasicSetTheory.SetSort.set, id) ∉
          Term.freeSupport point)
    (hPositive :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        codes ∈ₘ seq₊_spaceₘ(FormulaCodeₘ))
    (hAll :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∀ₘ[Nonlogical.BasicSetTheory.SetSort.set, base + 3],
          (x#(base + 3) ∈ₘ domₘ(codes)) ⟶ₘ
            canonical_project_formula_line_condition_with_ids
              codes depths (x#(base + 3))
              (base + 4) (base + 5)
              (base + 6) (base + 7)
              (base + 8) (base + 9))
    (hDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        point ∈ₘ domₘ(codes))
    (hCode :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (codes ·ₘ point) ≐ₘ
          standard_token_sequence tokens)
    (hDepth :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (depths ·ₘ point) ≐ₘ numₘ(depth))
    (hDecode :
      fs_project_hilbert_tokens_decode depth tokens = none) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  let firstPremiseId := base + 4
  let secondPremiseId := base + 5
  let leftVariableCodeId := base + 6
  let rightVariableCodeId := base + 7
  let leftVariableDepthId := base + 8
  let rightVariableDepthId := base + 9
  let firstPremise : SetTerm := x#firstPremiseId
  let secondPremise : SetTerm := x#secondPremiseId
  let atomic : SetFormula :=
    canonical_project_atomic_code_condition_with_ids
      (depths ·ₘ point) (codes ·ₘ point)
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId
  let negationBody : SetFormula :=
    (firstPremise ∈ₘ point) ∧ₘ
      (((firstPremise ∈ₘ domₘ(codes)) ∧ₘ
          ((depths ·ₘ firstPremise) ≐ₘ
            (depths ·ₘ point))) ∧ₘ
        ((codes ·ₘ point) ≐ₘ
          neg_codeₘ(codes ·ₘ firstPremise)))
  let negation : SetFormula :=
    ∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, firstPremiseId],
      negationBody
  let implicationCore : SetFormula :=
    (((firstPremise ∈ₘ domₘ(codes)) ∧ₘ
          (secondPremise ∈ₘ domₘ(codes))) ∧ₘ
        (((depths ·ₘ firstPremise) ≐ₘ
            (depths ·ₘ point)) ∧ₘ
          ((depths ·ₘ secondPremise) ≐ₘ
            (depths ·ₘ point)))) ∧ₘ
      ((codes ·ₘ point) ≐ₘ
        imp_codeₘ(
          codes ·ₘ firstPremise,
          codes ·ₘ secondPremise))
  let implicationBody : SetFormula :=
    (secondPremise ∈ₘ point) ∧ₘ implicationCore
  let implicationInner : SetFormula :=
    ∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, secondPremiseId],
      implicationBody
  let implicationOuterBody : SetFormula :=
    (firstPremise ∈ₘ point) ∧ₘ implicationInner
  let implication : SetFormula :=
    ∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, firstPremiseId],
      implicationOuterBody
  let universalBody : SetFormula :=
    (firstPremise ∈ₘ point) ∧ₘ
      (((firstPremise ∈ₘ domₘ(codes)) ∧ₘ
          ((depths ·ₘ firstPremise) ≐ₘ
            Sₘ(depths ·ₘ point))) ∧ₘ
        ((codes ·ₘ point) ≐ₘ
          forall_codeₘ(
            canonical_binder_variable_code_term
              (depths ·ₘ point),
            codes ·ₘ firstPremise)))
  let universal : SetFormula :=
    ∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, firstPremiseId],
      universalBody
  let rest : SetFormula := implication ∨ₘ universal
  let tail : SetFormula := negation ∨ₘ rest
  have hCodeApplicationFresh
      (id : FreeVarId)
      (hId : id ∈ [
        base + 3, base + 4, base + 5,
        base + 6, base + 7, base + 8,
        base + 9, base + 10, base + 11]) :
      (Nonlogical.BasicSetTheory.SetSort.set, id) ∉
        Term.freeSupport (codes ·ₘ point) := by
    simp only [Term.freeSupport, Term.freeSupportList,
      List.append_nil]
    exact List.not_mem_append
        (hCodesFresh id hId)
        (hPointFresh id hId)
  have hDepthApplicationFresh
      (id : FreeVarId)
      (hId : id ∈ [
        base + 3, base + 4, base + 5,
        base + 6, base + 7, base + 8,
        base + 9, base + 10, base + 11]) :
      (Nonlogical.BasicSetTheory.SetSort.set, id) ∉
        Term.freeSupport (depths ·ₘ point) := by
    simp only [Term.freeSupport, Term.freeSupportList,
      List.append_nil]
    exact List.not_mem_append
        (hDepthsFresh id hId)
        (hPointFresh id hId)
  have hLine :=
    fs_zfc_support_raw_project_line_of_all
      codes depths point
      (base + 3) firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId
      hPoint
      (hCodesFresh (base + 3) (by simp))
      (hDepthsFresh (base + 3) (by simp))
      (by
        intro id hId
        simp only [List.mem_cons, List.not_mem_nil,
          or_false] at hId
        rcases hId with rfl | rfl | rfl | rfl | rfl | rfl <;>
          dsimp [firstPremiseId, secondPremiseId,
            leftVariableCodeId, rightVariableCodeId,
            leftVariableDepthId, rightVariableDepthId] <;>
          exact Nat.ne_of_lt (by omega))
      (by
        intro id hId
        apply hPointFresh id
        simp only [List.mem_cons, List.not_mem_nil,
          or_false] at hId ⊢
        rcases hId with rfl | rfl | rfl | rfl | rfl | rfl <;>
          dsimp [firstPremiseId, secondPremiseId,
            leftVariableCodeId, rightVariableCodeId,
            leftVariableDepthId, rightVariableDepthId] <;>
          simp)
      hAll hDomain
  have hCases :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        atomic ∨ₘ tail := by
    simpa [atomic, tail, rest, negation, universal,
      implication, negationBody, implicationBody,
      universalBody, firstPremise, secondPremise,
      firstPremiseId, secondPremiseId,
      leftVariableCodeId, rightVariableCodeId,
      leftVariableDepthId, rightVariableDepthId,
      implicationCore, implicationInner, implicationOuterBody,
      canonical_project_formula_line_condition_with_ids] using
      hLine
  apply FirstOrder.Derives.disjElim hCases
  · let Δ : Context Nonlogical.BasicSetTheory.signature :=
      atomic :: Γ
    have hAtomic :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] atomic :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hNoMatch :
        ∀ kind leftDepth rightDepth,
          leftDepth < depth →
          rightDepth < depth →
          tokens ≠
            CanonicalProjectTrace.canonical_project_atom_tokens
              kind leftDepth rightDepth := by
      intro kind leftDepth rightDepth
        hLeftDepth hRightDepth hEqual
      rcases
          fs_project_hilbert_tokens_decode_canonical_atom_some
            depth kind leftDepth rightDepth
            hLeftDepth hRightDepth with
        ⟨formula, hSome⟩
      rw [hEqual, hSome] at hDecode
      cases hDecode
    let depthParameter : FreeVarId := base + 10
    let codeParameter : FreeVarId := base + 11
    let currentDepth : SetTerm := depths ·ₘ point
    let currentCode : SetTerm := codes ·ₘ point
    let depthBody : SetFormula :=
      canonical_project_atomic_code_condition_with_ids
        (x#depthParameter) currentCode
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId
    let depthGround : SetFormula :=
      canonical_project_atomic_code_condition_with_ids
        (numₘ(depth)) currentCode
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId
    have hCurrentDepth :
        Term.CheckCertificate currentDepth
          Nonlogical.BasicSetTheory.SetSort.set := by
      dsimp [currentDepth]
      exact Term.check_admissible_complete <|
        function_application_term_admissible
          depths point hDepths.admissible hPoint.admissible
    have hCurrentCode :
        Term.CheckCertificate currentCode
          Nonlogical.BasicSetTheory.SetSort.set := by
      dsimp [currentCode]
      exact Term.check_admissible_complete <|
        function_application_term_admissible
          codes point hCodes.admissible hPoint.admissible
    have hDepthBody :
        Formula.CheckCertificate depthBody := by
      apply Formula.check_admissible_complete
      simpa [depthBody] using
        canonical_project_atomic_code_condition_with_ids_admissible
          (x#depthParameter) currentCode
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId
          (set_variable_admissible depthParameter)
          hCurrentCode.admissible
    have hCurrentCodeDepthFixed (replacement : SetTerm) :
        Term.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set
            depthParameter replacement currentCode =
          currentCode :=
      Term.substituteFree_eq_self_of_not_mem
        Nonlogical.BasicSetTheory.SetSort.set
        depthParameter replacement currentCode <| by
          simpa [depthParameter, currentCode] using
            hCodeApplicationFresh (base + 10) (by simp)
    have hDepthLeft :
        Formula.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set
            depthParameter currentDepth depthBody =
          atomic := by
      simpa [depthBody, atomic, currentDepth, currentCode,
        depthParameter] using
        canonical_project_atomic_code_condition_with_ids_substitute_free
          (x#(base + 10)) (codes ·ₘ point)
          (depths ·ₘ point) (depths ·ₘ point)
          (codes ·ₘ point)
          (base + 10) leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId
          (by
            dsimp [leftVariableCodeId]
            exact Nat.ne_of_gt (by omega))
          (by
            dsimp [rightVariableCodeId]
            exact Nat.ne_of_gt (by omega))
          (by
            dsimp [leftVariableDepthId]
            exact Nat.ne_of_gt (by omega))
          (by
            dsimp [rightVariableDepthId]
            exact Nat.ne_of_gt (by omega))
          hCurrentDepth.admissible
          (by
            simpa [leftVariableCodeId] using
              hDepthApplicationFresh (base + 6) (by simp))
          (by
            simpa [rightVariableCodeId] using
              hDepthApplicationFresh (base + 7) (by simp))
          (by
            simpa [leftVariableDepthId] using
              hDepthApplicationFresh (base + 8) (by simp))
          (by
            simpa [rightVariableDepthId] using
              hDepthApplicationFresh (base + 9) (by simp))
          (by simp [Term.substituteFree, set_variable])
          (by
            simpa [depthParameter, currentCode] using
              hCurrentCodeDepthFixed (depths ·ₘ point))
    have hDepthRight :
        Formula.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set
            depthParameter (numₘ(depth)) depthBody =
          depthGround := by
      simpa [depthBody, depthGround, currentCode,
        depthParameter] using
        canonical_project_atomic_code_condition_with_ids_substitute_free
          (x#(base + 10)) (codes ·ₘ point)
          (numₘ(depth)) (numₘ(depth))
          (codes ·ₘ point)
          (base + 10) leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId
          (by
            dsimp [leftVariableCodeId]
            exact Nat.ne_of_gt (by omega))
          (by
            dsimp [rightVariableCodeId]
            exact Nat.ne_of_gt (by omega))
          (by
            dsimp [leftVariableDepthId]
            exact Nat.ne_of_gt (by omega))
          (by
            dsimp [rightVariableDepthId]
            exact Nat.ne_of_gt (by omega))
          (finite_numeral_term_admissible depth)
          (by
            rw [finite_numeral_term_freeSupport]
            exact List.not_mem_nil)
          (by
            rw [finite_numeral_term_freeSupport]
            exact List.not_mem_nil)
          (by
            rw [finite_numeral_term_freeSupport]
            exact List.not_mem_nil)
          (by
            rw [finite_numeral_term_freeSupport]
            exact List.not_mem_nil)
          (by simp [Term.substituteFree, set_variable])
          (by
            simpa [depthParameter, currentCode] using
              hCurrentCodeDepthFixed (numₘ(depth)))
    have hDepthTransportRaw :=
      Metatheory.Derives.equality_iff_of_equality
        (T := fs_zfc_support_raw_theory)
        (Γ := Δ)
        (sort := Nonlogical.BasicSetTheory.SetSort.set)
        (eigen := depthParameter)
        (left := currentDepth)
        (right := numₘ(depth))
        (body := depthBody)
        (FirstOrder.Derives.context_weaken_cons hDepth)
        (hLeftCheck := hCurrentDepth)
        (hRightCheck :=
          Term.check_admissible_complete
            (finite_numeral_term_admissible depth))
        (hBodyCheck := hDepthBody)
    have hDepthGround :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] depthGround :=
      FirstOrder.Derives.iffElimRight
        (by
          simpa only [hDepthLeft, hDepthRight] using
            hDepthTransportRaw)
        hAtomic
    let codeBody : SetFormula :=
      canonical_project_atomic_code_condition_with_ids
        (numₘ(depth)) (x#codeParameter)
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId
    let atomicGround : SetFormula :=
      canonical_project_atomic_code_condition_with_ids
        (numₘ(depth)) (standard_token_sequence tokens)
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId
    have hCodeBody :
        Formula.CheckCertificate codeBody := by
      apply Formula.check_admissible_complete
      simpa [codeBody] using
        canonical_project_atomic_code_condition_with_ids_admissible
          (numₘ(depth)) (x#codeParameter)
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId
          (finite_numeral_term_admissible depth)
          (set_variable_admissible codeParameter)
    have hNumeralCodeFixed (replacement : SetTerm) :
        Term.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set
            codeParameter replacement (numₘ(depth)) =
          numₘ(depth) := by
      apply Term.substituteFree_eq_self_of_not_mem
      rw [finite_numeral_term_freeSupport]
      exact List.not_mem_nil
    have hCodeLeft :
        Formula.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set
            codeParameter currentCode codeBody =
          depthGround := by
      simpa [codeBody, depthGround, currentCode,
        codeParameter] using
        canonical_project_atomic_code_condition_with_ids_substitute_free
          (numₘ(depth)) (x#(base + 11))
          (codes ·ₘ point) (numₘ(depth))
          (codes ·ₘ point)
          (base + 11) leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId
          (by
            dsimp [leftVariableCodeId]
            exact Nat.ne_of_gt (by omega))
          (by
            dsimp [rightVariableCodeId]
            exact Nat.ne_of_gt (by omega))
          (by
            dsimp [leftVariableDepthId]
            exact Nat.ne_of_gt (by omega))
          (by
            dsimp [rightVariableDepthId]
            exact Nat.ne_of_gt (by omega))
          hCurrentCode.admissible
          (by
            simpa [leftVariableCodeId] using
              hCodeApplicationFresh (base + 6) (by simp))
          (by
            simpa [rightVariableCodeId] using
              hCodeApplicationFresh (base + 7) (by simp))
          (by
            simpa [leftVariableDepthId] using
              hCodeApplicationFresh (base + 8) (by simp))
          (by
            simpa [rightVariableDepthId] using
              hCodeApplicationFresh (base + 9) (by simp))
          (by
            simpa [codeParameter] using
              hNumeralCodeFixed (codes ·ₘ point))
          (by simp [Term.substituteFree, set_variable])
    have hCodeRight :
        Formula.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set
            codeParameter
            (standard_token_sequence tokens) codeBody =
          atomicGround := by
      simpa [codeBody, atomicGround, codeParameter] using
        canonical_project_atomic_code_condition_with_ids_substitute_free
          (numₘ(depth)) (x#(base + 11))
          (standard_token_sequence tokens)
          (numₘ(depth)) (standard_token_sequence tokens)
          (base + 11) leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId
          (by
            dsimp [leftVariableCodeId]
            exact Nat.ne_of_gt (by omega))
          (by
            dsimp [rightVariableCodeId]
            exact Nat.ne_of_gt (by omega))
          (by
            dsimp [leftVariableDepthId]
            exact Nat.ne_of_gt (by omega))
          (by
            dsimp [rightVariableDepthId]
            exact Nat.ne_of_gt (by omega))
          (standard_token_sequence_admissible tokens)
          (by
            rw [standard_token_sequence_freeSupport_nil]
            exact List.not_mem_nil)
          (by
            rw [standard_token_sequence_freeSupport_nil]
            exact List.not_mem_nil)
          (by
            rw [standard_token_sequence_freeSupport_nil]
            exact List.not_mem_nil)
          (by
            rw [standard_token_sequence_freeSupport_nil]
            exact List.not_mem_nil)
          (by
            simpa [codeParameter] using
              hNumeralCodeFixed
                (standard_token_sequence tokens))
          (by simp [Term.substituteFree, set_variable])
    have hCodeTransportRaw :=
      Metatheory.Derives.equality_iff_of_equality
        (T := fs_zfc_support_raw_theory)
        (Γ := Δ)
        (sort := Nonlogical.BasicSetTheory.SetSort.set)
        (eigen := codeParameter)
        (left := currentCode)
        (right := standard_token_sequence tokens)
        (body := codeBody)
        (FirstOrder.Derives.context_weaken_cons hCode)
        (hLeftCheck := hCurrentCode)
        (hRightCheck :=
          Term.check_admissible_complete
            (standard_token_sequence_admissible tokens))
        (hBodyCheck := hCodeBody)
    have hAtomicGround :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] atomicGround :=
      FirstOrder.Derives.iffElimRight
        (by
          simpa only [hCodeLeft, hCodeRight] using
            hCodeTransportRaw)
        hDepthGround
    have hAtomicNot :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          ¬ₘ atomicGround :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp [Δ]) <| by
          simpa [atomicGround, leftVariableCodeId,
            rightVariableCodeId,
            leftVariableDepthId,
            rightVariableDepthId,
            Nat.add_assoc] using
            fs_zfc_support_raw_canonical_project_atomic_code_condition_with_ids_neg_of_no_match
              depth tokens (base + 6) hNoMatch
    exact FirstOrder.Derives.negElim
      hAtomicGround hAtomicNot
  · let Δ : Context Nonlogical.BasicSetTheory.signature :=
      tail :: Γ
    have hTail :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] tail :=
      FirstOrder.Derives.assumption (by simp [Δ])
    exact FirstOrder.Derives.disjElim hTail
      (by
        let Ε : Context Nonlogical.BasicSetTheory.signature :=
          negation :: Δ
        have hNegation :
            Ε ⊢ₘ[fs_zfc_support_raw_theory] negation :=
          FirstOrder.Derives.assumption (by simp [Ε])
        apply fs_zfc_support_raw_exists_elim_fresh
          [
            base + 3, base + 4, base + 5,
            base + 6, base + 7, base + 8,
            base + 9, base + 10, base + 11]
          firstPremiseId negationBody Formula.falsum
        · simpa [negation] using hNegation
        · intro eigen hEigenFresh hOpenedCheck
          let child : SetTerm := x#eigen
          let opened : SetFormula :=
            Formula.substituteFree
              Nonlogical.BasicSetTheory.SetSort.set
              firstPremiseId child negationBody
          let childBody : SetFormula :=
            (child ∈ₘ point) ∧ₘ
              (((child ∈ₘ domₘ(codes)) ∧ₘ
                  ((depths ·ₘ child) ≐ₘ
                    (depths ·ₘ point))) ∧ₘ
                ((codes ·ₘ point) ≐ₘ
                  neg_codeₘ(codes ·ₘ child)))
          let Ζ : Context Nonlogical.BasicSetTheory.signature :=
            opened :: Ε
          have hOpened :
              Ζ ⊢ₘ[fs_zfc_support_raw_theory] opened :=
            FirstOrder.Derives.assumption
              (by simp [Ζ]) hOpenedCheck
          have hCodesFixed :
              Term.substituteFree
                  Nonlogical.BasicSetTheory.SetSort.set
                  firstPremiseId child codes =
                codes :=
            Term.substituteFree_eq_self_of_not_mem
              Nonlogical.BasicSetTheory.SetSort.set
              firstPremiseId child codes <| by
                simpa [firstPremiseId] using
                  hCodesFresh (base + 4) (by simp)
          have hDepthsFixed :
              Term.substituteFree
                  Nonlogical.BasicSetTheory.SetSort.set
                  firstPremiseId child depths =
                depths :=
            Term.substituteFree_eq_self_of_not_mem
              Nonlogical.BasicSetTheory.SetSort.set
              firstPremiseId child depths <| by
                simpa [firstPremiseId] using
                  hDepthsFresh (base + 4) (by simp)
          have hPointFixed :
              Term.substituteFree
                  Nonlogical.BasicSetTheory.SetSort.set
                  firstPremiseId child point =
                point :=
            Term.substituteFree_eq_self_of_not_mem
              Nonlogical.BasicSetTheory.SetSort.set
              firstPremiseId child point <| by
                simpa [firstPremiseId] using
                  hPointFresh (base + 4) (by simp)
          have hBody :
              Ζ ⊢ₘ[fs_zfc_support_raw_theory] childBody := by
            simpa [opened, childBody, negationBody,
              firstPremise, child, Formula.substituteFree,
              Term.substituteFree, set_variable,
              hCodesFixed, hDepthsFixed, hPointFixed] using
              hOpened
          have hΓSub :
              ∀ formula, formula ∈ Γ → formula ∈ Ζ := by
            intro formula hFormula
            simp only [Ζ, Ε, Δ, List.mem_cons]
            exact Or.inr <| Or.inr <| Or.inr hFormula
          have hPositiveAt :
              Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                codes ∈ₘ seq₊_spaceₘ(FormulaCodeₘ) :=
            FirstOrder.Derives.context_weaken
              (Γ := Γ) (Δ := Ζ)
              hΓSub hPositive
          have hAllAt :
              Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                ∀ₘ[Nonlogical.BasicSetTheory.SetSort.set,
                  base + 3],
                  (x#(base + 3) ∈ₘ domₘ(codes)) ⟶ₘ
                    canonical_project_formula_line_condition_with_ids
                      codes depths (x#(base + 3))
                      (base + 4) (base + 5)
                      (base + 6) (base + 7)
                      (base + 8) (base + 9) :=
            FirstOrder.Derives.context_weaken
              (Γ := Γ) (Δ := Ζ)
              hΓSub hAll
          have hCodeAt :=
            FirstOrder.Derives.context_weaken
              (Γ := Γ) (Δ := Ζ)
              hΓSub hCode
          have hDepthAt :=
            FirstOrder.Derives.context_weaken
              (Γ := Γ) (Δ := Ζ)
              hΓSub hDepth
          have hChildDomain :
              Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                child ∈ₘ domₘ(codes) := by
            simpa [childBody] using
              FirstOrder.Derives.conjElimLeft <|
                FirstOrder.Derives.conjElimLeft <|
                  FirstOrder.Derives.conjElimRight hBody
          have hFormulaCodeNonempty :
              Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                FormulaCodeₘ ≠ₘ ∅ₘ :=
            FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Ζ) (by simp [Ζ, Ε, Δ]) <|
                fs_zfc_support_raw_derives_of_godel_quotation
                  GodelQuotation.formula_code_set_nonempty_derives
          have hChildMember :
              Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                (codes ·ₘ child) ∈ₘ FormulaCodeₘ :=
            fs_zfc_support_raw_positive_sequence_application_mem
              FormulaCodeₘ codes child
              formula_code_set_term_admissible
              hCodes.admissible
              (set_variable_admissible eigen)
              hFormulaCodeNonempty hPositiveAt hChildDomain
          have hChildDepth :
              Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                (depths ·ₘ child) ≐ₘ numₘ(depth) :=
            Metatheory.Derives.equality_trans
              (by
                simpa [childBody] using
                  FirstOrder.Derives.conjElimRight <|
                    FirstOrder.Derives.conjElimLeft <|
                      FirstOrder.Derives.conjElimRight hBody)
              hDepthAt
          have hParentEquality :
              Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                standard_token_sequence tokens ≐ₘ
                  neg_codeₘ(codes ·ₘ child) :=
            Metatheory.Derives.equality_trans
              (Metatheory.Derives.equality_symm hCodeAt)
              (by
                simpa [childBody] using
                  FirstOrder.Derives.conjElimRight <|
                    FirstOrder.Derives.conjElimRight hBody)
          let bodyTokens : List Nat :=
            (tokens.drop 2).take (tokens.length - 3)
          by_cases hShape :
              tokens =
                Numbered.negation_tokens bodyTokens
          · have hChildEquality :
                Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                  (codes ·ₘ child) ≐ₘ
                    standard_token_sequence bodyTokens :=
              fs_zfc_support_raw_negation_body_eq_standard
                (codes ·ₘ child) bodyTokens
                (Term.check_admissible_complete <|
                  function_application_term_admissible
                    codes child hCodes.admissible
                    (set_variable_admissible eigen))
                hChildMember
                (by simpa [hShape] using hParentEquality)
            have hBodyLength :
                bodyTokens.length < tokens.length := by
              rw [hShape]
              simp [Numbered.negation_tokens]
              omega
            cases hProject :
                fs_project_hilbert_tokens_decode
                  depth bodyTokens with
            | none =>
                exact
                  fs_zfc_support_raw_project_line_falsum_of_decode_none
                    depth bodyTokens base
                    codes depths child hCodes hDepths
                    (Term.check_admissible_complete <|
                      set_variable_admissible eigen)
                    hCodesFresh hDepthsFresh
                    (by
                      intro id hId
                      simpa [child] using
                        hEigenFresh id hId)
                    hPositiveAt hAllAt hChildDomain
                    hChildEquality hChildDepth hProject
            | some body =>
                have hOuter :=
                  fs_project_hilbert_tokens_decode_negation
                    depth bodyTokens hProject
                rw [hShape, hOuter] at hDecode
                cases hDecode
          · exact
              fs_zfc_support_raw_negation_falsum_of_not_shape
                (codes ·ₘ child) tokens
                (Term.check_admissible_complete <|
                  function_application_term_admissible
                    codes child hCodes.admissible
                    (set_variable_admissible eigen))
                hChildMember hParentEquality
                (by simpa [bodyTokens] using hShape))
      (by
        let Ε : Context Nonlogical.BasicSetTheory.signature :=
          rest :: Δ
        have hRest :
            Ε ⊢ₘ[fs_zfc_support_raw_theory] rest :=
          FirstOrder.Derives.assumption (by simp [Ε])
        exact FirstOrder.Derives.disjElim hRest
          (by
            let Ζ : Context Nonlogical.BasicSetTheory.signature :=
              implication :: Ε
            have hImplication :
                Ζ ⊢ₘ[fs_zfc_support_raw_theory] implication :=
              FirstOrder.Derives.assumption (by simp [Ζ])
            apply fs_zfc_support_raw_exists_elim_fresh
              [
                base + 3, base + 4, base + 5,
                base + 6, base + 7, base + 8,
                base + 9, base + 10, base + 11]
              firstPremiseId implicationOuterBody
              Formula.falsum
              (by simpa [implication] using hImplication)
            intro leftEigen hLeftFresh hOuterCheck
            let leftPoint : SetTerm := x#leftEigen
            let outerOpened : SetFormula :=
              Formula.substituteFree
                Nonlogical.BasicSetTheory.SetSort.set
                firstPremiseId leftPoint
                implicationOuterBody
            let Ω : Context Nonlogical.BasicSetTheory.signature :=
              outerOpened :: Ζ
            have hOuterOpened :
                Ω ⊢ₘ[fs_zfc_support_raw_theory] outerOpened :=
              FirstOrder.Derives.assumption
                (by simp [Ω]) hOuterCheck
            have hIds :
                firstPremiseId ≠ secondPremiseId := by
              dsimp [firstPremiseId, secondPremiseId]
              exact Nat.ne_of_lt (by omega)
            have hComm :
                Formula.substituteFree
                    Nonlogical.BasicSetTheory.SetSort.set
                    firstPremiseId leftPoint
                    (Formula.closeFreeAt
                      Nonlogical.BasicSetTheory.SetSort.set
                      secondPremiseId 0 implicationBody) =
                  Formula.closeFreeAt
                    Nonlogical.BasicSetTheory.SetSort.set
                    secondPremiseId 0
                    (Formula.substituteFree
                      Nonlogical.BasicSetTheory.SetSort.set
                      firstPremiseId leftPoint implicationBody) :=
              (Formula.closeFreeAt_substituteFree_comm
                Nonlogical.BasicSetTheory.SetSort.set
                firstPremiseId secondPremiseId 0
                leftPoint implicationBody hIds
                (set_variable_admissible leftEigen).2
                (by
                  intro hEqual
                  apply hLeftFresh secondPremiseId
                    (by simp [secondPremiseId])
                  change
                    (Nonlogical.BasicSetTheory.SetSort.set,
                      secondPremiseId) ∈
                      [(Nonlogical.BasicSetTheory.SetSort.set,
                        leftEigen)]
                  change
                    (Nonlogical.BasicSetTheory.SetSort.set,
                      secondPremiseId) ∈
                      [(Nonlogical.BasicSetTheory.SetSort.set,
                        leftEigen)]
                    at hEqual
                  exact hEqual)).symm
            have hSecondExists :
                Ω ⊢ₘ[fs_zfc_support_raw_theory]
                  ∃ₘ[Nonlogical.BasicSetTheory.SetSort.set,
                    secondPremiseId],
                    Formula.substituteFree
                      Nonlogical.BasicSetTheory.SetSort.set
                      firstPremiseId leftPoint implicationBody := by
              simpa [outerOpened, implicationOuterBody,
                implicationInner, Formula.substituteFree,
                hComm] using
                FirstOrder.Derives.conjElimRight hOuterOpened
            apply fs_zfc_support_raw_exists_elim_fresh
              [
                base + 3, base + 4, base + 5,
                base + 6, base + 7, base + 8,
                base + 9, base + 10, base + 11]
              secondPremiseId
              (Formula.substituteFree
                Nonlogical.BasicSetTheory.SetSort.set
                firstPremiseId leftPoint implicationBody)
              Formula.falsum hSecondExists
            intro rightEigen hRightFresh hOpenedCheck
            let rightPoint : SetTerm := x#rightEigen
            let opened : SetFormula :=
              Formula.substituteFree
                Nonlogical.BasicSetTheory.SetSort.set
                secondPremiseId rightPoint
                (Formula.substituteFree
                  Nonlogical.BasicSetTheory.SetSort.set
                  firstPremiseId leftPoint implicationBody)
            let branchCore : SetFormula :=
              (((leftPoint ∈ₘ domₘ(codes)) ∧ₘ
                  (rightPoint ∈ₘ domₘ(codes))) ∧ₘ
                (((depths ·ₘ leftPoint) ≐ₘ
                    (depths ·ₘ point)) ∧ₘ
                  ((depths ·ₘ rightPoint) ≐ₘ
                    (depths ·ₘ point)))) ∧ₘ
                ((codes ·ₘ point) ≐ₘ
                  imp_codeₘ(
                    codes ·ₘ leftPoint,
                    codes ·ₘ rightPoint))
            let branchBody : SetFormula :=
              (rightPoint ∈ₘ point) ∧ₘ branchCore
            let Θ : Context Nonlogical.BasicSetTheory.signature :=
              opened :: Ω
            have hOpened :
                Θ ⊢ₘ[fs_zfc_support_raw_theory] opened :=
              FirstOrder.Derives.assumption
                (by simp [Θ]) hOpenedCheck
            have hCodesFirst :
                Term.substituteFree
                    Nonlogical.BasicSetTheory.SetSort.set
                    firstPremiseId leftPoint codes =
                  codes :=
              Term.substituteFree_eq_self_of_not_mem
                Nonlogical.BasicSetTheory.SetSort.set
                firstPremiseId leftPoint codes <| by
                  simpa [firstPremiseId] using
                    hCodesFresh (base + 4) (by simp)
            have hCodesSecond :
                Term.substituteFree
                    Nonlogical.BasicSetTheory.SetSort.set
                    secondPremiseId rightPoint codes =
                  codes :=
              Term.substituteFree_eq_self_of_not_mem
                Nonlogical.BasicSetTheory.SetSort.set
                secondPremiseId rightPoint codes <| by
                  simpa [secondPremiseId] using
                    hCodesFresh (base + 5) (by simp)
            have hDepthsFirst :
                Term.substituteFree
                    Nonlogical.BasicSetTheory.SetSort.set
                    firstPremiseId leftPoint depths =
                  depths :=
              Term.substituteFree_eq_self_of_not_mem
                Nonlogical.BasicSetTheory.SetSort.set
                firstPremiseId leftPoint depths <| by
                  simpa [firstPremiseId] using
                    hDepthsFresh (base + 4) (by simp)
            have hDepthsSecond :
                Term.substituteFree
                    Nonlogical.BasicSetTheory.SetSort.set
                    secondPremiseId rightPoint depths =
                  depths :=
              Term.substituteFree_eq_self_of_not_mem
                Nonlogical.BasicSetTheory.SetSort.set
                secondPremiseId rightPoint depths <| by
                  simpa [secondPremiseId] using
                    hDepthsFresh (base + 5) (by simp)
            have hPointFirst :
                Term.substituteFree
                    Nonlogical.BasicSetTheory.SetSort.set
                    firstPremiseId leftPoint point =
                  point :=
              Term.substituteFree_eq_self_of_not_mem
                Nonlogical.BasicSetTheory.SetSort.set
                firstPremiseId leftPoint point <| by
                  simpa [firstPremiseId] using
                    hPointFresh (base + 4) (by simp)
            have hPointSecond :
                Term.substituteFree
                    Nonlogical.BasicSetTheory.SetSort.set
                    secondPremiseId rightPoint point =
                  point :=
              Term.substituteFree_eq_self_of_not_mem
                Nonlogical.BasicSetTheory.SetSort.set
                secondPremiseId rightPoint point <| by
                  simpa [secondPremiseId] using
                    hPointFresh (base + 5) (by simp)
            have hLeftPointFixed :
                Term.substituteFree
                    Nonlogical.BasicSetTheory.SetSort.set
                    secondPremiseId rightPoint leftPoint =
                  leftPoint :=
              Term.substituteFree_eq_self_of_not_mem
                Nonlogical.BasicSetTheory.SetSort.set
                secondPremiseId rightPoint leftPoint <| by
                  intro hEqual
                  apply hLeftFresh (base + 5) (by simp)
                  change
                    (Nonlogical.BasicSetTheory.SetSort.set,
                      base + 5) ∈
                      [(Nonlogical.BasicSetTheory.SetSort.set,
                        leftEigen)]
                  change
                    (Nonlogical.BasicSetTheory.SetSort.set,
                      base + 5) ∈
                      [(Nonlogical.BasicSetTheory.SetSort.set,
                        leftEigen)]
                    at hEqual
                  exact hEqual
            have hBody :
                Θ ⊢ₘ[fs_zfc_support_raw_theory] branchBody := by
              simpa [opened, branchBody, branchCore,
                implicationBody, implicationCore,
                firstPremise, secondPremise,
                leftPoint, rightPoint,
                Formula.substituteFree, Term.substituteFree,
                set_variable, hCodesFirst, hCodesSecond,
                hDepthsFirst, hDepthsSecond,
                hPointFirst, hPointSecond,
                hLeftPointFixed, firstPremiseId,
                secondPremiseId] using hOpened
            have hΓSub :
                ∀ formula, formula ∈ Γ → formula ∈ Θ := by
              intro formula hFormula
              simp only [Θ, Ω, Ζ, Ε, Δ, List.mem_cons]
              exact Or.inr <| Or.inr <| Or.inr <|
                Or.inr <| Or.inr hFormula
            have hPositiveAt :=
              FirstOrder.Derives.context_weaken
                (Γ := Γ) (Δ := Θ) hΓSub hPositive
            have hAllAt :=
              FirstOrder.Derives.context_weaken
                (Γ := Γ) (Δ := Θ) hΓSub hAll
            have hCodeAt :=
              FirstOrder.Derives.context_weaken
                (Γ := Γ) (Δ := Θ) hΓSub hCode
            have hDepthAt :=
              FirstOrder.Derives.context_weaken
                (Γ := Γ) (Δ := Θ) hΓSub hDepth
            have hNonempty :
                Θ ⊢ₘ[fs_zfc_support_raw_theory]
                  FormulaCodeₘ ≠ₘ ∅ₘ :=
              FirstOrder.Derives.context_weaken
                (Γ := []) (Δ := Θ) (by simp) <|
                  fs_zfc_support_raw_derives_of_godel_quotation
                    GodelQuotation.formula_code_set_nonempty_derives
            have hLeftDomain :
                Θ ⊢ₘ[fs_zfc_support_raw_theory]
                  leftPoint ∈ₘ domₘ(codes) := by
              simpa [branchBody, branchCore] using
                FirstOrder.Derives.conjElimLeft <|
                  FirstOrder.Derives.conjElimLeft <|
                    FirstOrder.Derives.conjElimLeft <|
                      FirstOrder.Derives.conjElimRight hBody
            have hRightDomain :
                Θ ⊢ₘ[fs_zfc_support_raw_theory]
                  rightPoint ∈ₘ domₘ(codes) := by
              simpa [branchBody, branchCore] using
                FirstOrder.Derives.conjElimRight <|
                  FirstOrder.Derives.conjElimLeft <|
                    FirstOrder.Derives.conjElimLeft <|
                      FirstOrder.Derives.conjElimRight hBody
            let leftCode : SetTerm := codes ·ₘ leftPoint
            let rightCode : SetTerm := codes ·ₘ rightPoint
            have hLeftCheck :
                Term.CheckCertificate leftCode SetSort.set :=
              Term.check_admissible_complete <| by
                simpa [leftCode] using
                  function_application_term_admissible
                    codes leftPoint hCodes.admissible
                    (set_variable_admissible leftEigen)
            have hRightCheck :
                Term.CheckCertificate rightCode SetSort.set :=
              Term.check_admissible_complete <| by
                simpa [rightCode] using
                  function_application_term_admissible
                    codes rightPoint hCodes.admissible
                    (set_variable_admissible rightEigen)
            have hLeftMember :
                Θ ⊢ₘ[fs_zfc_support_raw_theory]
                  leftCode ∈ₘ FormulaCodeₘ := by
              simpa [leftCode] using
                fs_zfc_support_raw_positive_sequence_application_mem
                  FormulaCodeₘ codes leftPoint
                  formula_code_set_term_admissible
                  hCodes.admissible
                  (set_variable_admissible leftEigen)
                  hNonempty hPositiveAt hLeftDomain
            have hRightMember :
                Θ ⊢ₘ[fs_zfc_support_raw_theory]
                  rightCode ∈ₘ FormulaCodeₘ := by
              simpa [rightCode] using
                fs_zfc_support_raw_positive_sequence_application_mem
                  FormulaCodeₘ codes rightPoint
                  formula_code_set_term_admissible
                  hCodes.admissible
                  (set_variable_admissible rightEigen)
                  hNonempty hPositiveAt hRightDomain
            have hLeftDepth :
                Θ ⊢ₘ[fs_zfc_support_raw_theory]
                  (depths ·ₘ leftPoint) ≐ₘ numₘ(depth) :=
              Metatheory.Derives.equality_trans
                (by
                  simpa [branchBody, branchCore] using
                    FirstOrder.Derives.conjElimLeft <|
                      FirstOrder.Derives.conjElimRight <|
                        FirstOrder.Derives.conjElimLeft <|
                          FirstOrder.Derives.conjElimRight hBody)
                hDepthAt
            have hRightDepth :
                Θ ⊢ₘ[fs_zfc_support_raw_theory]
                  (depths ·ₘ rightPoint) ≐ₘ numₘ(depth) :=
              Metatheory.Derives.equality_trans
                (by
                  simpa [branchBody, branchCore] using
                    FirstOrder.Derives.conjElimRight <|
                      FirstOrder.Derives.conjElimRight <|
                        FirstOrder.Derives.conjElimLeft <|
                          FirstOrder.Derives.conjElimRight hBody)
                hDepthAt
            have hParentEquality :
                Θ ⊢ₘ[fs_zfc_support_raw_theory]
                  standard_token_sequence tokens ≐ₘ
                    imp_codeₘ(leftCode, rightCode) :=
              Metatheory.Derives.equality_trans
                (Metatheory.Derives.equality_symm hCodeAt)
                (by
                  simpa [branchBody, branchCore,
                    leftCode, rightCode] using
                    FirstOrder.Derives.conjElimRight <|
                      FirstOrder.Derives.conjElimRight hBody)
            have hLeftDomainMember :=
              fs_zfc_support_raw_implication_left_domain_mem
                leftCode rightCode hLeftCheck hRightCheck
                hLeftMember hRightMember
            refine CertifiedProof.fs_zfc_support_raw_domain_length_elim
              (child := leftCode)
              (parent := imp_codeₘ(leftCode, rightCode))
              (tokens := tokens)
              (conclusion := Formula.falsum)
              (hChild := hLeftCheck.admissible)
              (hParent := by prove_term_check)
              (hConclusion := Formula.Admissible.falsum)
              hLeftDomainMember hParentEquality ?_
            intro leftLength hLeftLength
            let Λ : Context Nonlogical.BasicSetTheory.signature :=
              (domₘ(leftCode) ≐ₘ numₘ(leftLength)) :: Θ
            have hLeftDomainLength :
                Λ ⊢ₘ[fs_zfc_support_raw_theory]
                  domₘ(leftCode) ≐ₘ numₘ(leftLength) :=
              FirstOrder.Derives.assumption (by simp [Λ])
            have hRightDomainMember :=
              fs_zfc_support_raw_implication_right_domain_mem
                leftCode rightCode leftLength
                hLeftCheck hRightCheck
                (FirstOrder.Derives.context_weaken_cons
                  hLeftMember)
                (FirstOrder.Derives.context_weaken_cons
                  hRightMember)
                hLeftDomainLength
            refine CertifiedProof.fs_zfc_support_raw_domain_length_elim
              (child := rightCode)
              (parent := imp_codeₘ(leftCode, rightCode))
              (tokens := tokens)
              (conclusion := Formula.falsum)
              (hChild := hRightCheck.admissible)
              (hParent := by prove_term_check)
              (hConclusion := Formula.Admissible.falsum)
              hRightDomainMember
              (FirstOrder.Derives.context_weaken_cons
                hParentEquality) ?_
            intro rightLength hRightLength
            let Μ : Context Nonlogical.BasicSetTheory.signature :=
              (domₘ(rightCode) ≐ₘ numₘ(rightLength)) :: Λ
            have hRightDomainLength :
                Μ ⊢ₘ[fs_zfc_support_raw_theory]
                  domₘ(rightCode) ≐ₘ numₘ(rightLength) :=
              FirstOrder.Derives.assumption (by simp [Μ])
            have hLeftDomainLengthAt :
                Μ ⊢ₘ[fs_zfc_support_raw_theory]
                  domₘ(leftCode) ≐ₘ numₘ(leftLength) :=
              FirstOrder.Derives.context_weaken_cons
                hLeftDomainLength
            let leftTokens :=
              (tokens.drop 1).take leftLength
            let rightTokens :=
              (tokens.drop (leftLength + 2)).take rightLength
            have hLeftMemberAt :
                Μ ⊢ₘ[fs_zfc_support_raw_theory]
                  leftCode ∈ₘ FormulaCodeₘ :=
              FirstOrder.Derives.context_weaken_cons <|
                FirstOrder.Derives.context_weaken_cons hLeftMember
            have hRightMemberAt :
                Μ ⊢ₘ[fs_zfc_support_raw_theory]
                  rightCode ∈ₘ FormulaCodeₘ :=
              FirstOrder.Derives.context_weaken_cons <|
                FirstOrder.Derives.context_weaken_cons hRightMember
            have hParentEqualityAt :
                Μ ⊢ₘ[fs_zfc_support_raw_theory]
                  standard_token_sequence tokens ≐ₘ
                    imp_codeₘ(leftCode, rightCode) :=
              FirstOrder.Derives.context_weaken_cons <|
                FirstOrder.Derives.context_weaken_cons hParentEquality
            have hPositiveAt' :
                Μ ⊢ₘ[fs_zfc_support_raw_theory]
                  codes ∈ₘ seq₊_spaceₘ(FormulaCodeₘ) :=
              FirstOrder.Derives.context_weaken_cons <|
                FirstOrder.Derives.context_weaken_cons hPositiveAt
            have hAllAt' :
                Μ ⊢ₘ[fs_zfc_support_raw_theory]
                  ∀ₘ[Nonlogical.BasicSetTheory.SetSort.set,
                    base + 3],
                    (x#(base + 3) ∈ₘ domₘ(codes)) ⟶ₘ
                      canonical_project_formula_line_condition_with_ids
                        codes depths (x#(base + 3))
                        (base + 4) (base + 5)
                        (base + 6) (base + 7)
                        (base + 8) (base + 9) :=
              FirstOrder.Derives.context_weaken_cons <|
                FirstOrder.Derives.context_weaken_cons hAllAt
            have hLeftDomain' :
                Μ ⊢ₘ[fs_zfc_support_raw_theory]
                  leftPoint ∈ₘ domₘ(codes) :=
              FirstOrder.Derives.context_weaken_cons <|
                FirstOrder.Derives.context_weaken_cons hLeftDomain
            have hRightDomain' :
                Μ ⊢ₘ[fs_zfc_support_raw_theory]
                  rightPoint ∈ₘ domₘ(codes) :=
              FirstOrder.Derives.context_weaken_cons <|
                FirstOrder.Derives.context_weaken_cons hRightDomain
            have hLeftDepth' :
                Μ ⊢ₘ[fs_zfc_support_raw_theory]
                  (depths ·ₘ leftPoint) ≐ₘ numₘ(depth) :=
              FirstOrder.Derives.context_weaken_cons <|
                FirstOrder.Derives.context_weaken_cons hLeftDepth
            have hRightDepth' :
                Μ ⊢ₘ[fs_zfc_support_raw_theory]
                  (depths ·ₘ rightPoint) ≐ₘ numₘ(depth) :=
              FirstOrder.Derives.context_weaken_cons <|
                FirstOrder.Derives.context_weaken_cons hRightDepth
            by_cases hShape :
                tokens =
                  Numbered.implication_tokens
                    leftTokens rightTokens
            · have hBodies :
                  Μ ⊢ₘ[fs_zfc_support_raw_theory]
                    (leftCode ≐ₘ
                        standard_token_sequence leftTokens) ∧ₘ
                      (rightCode ≐ₘ
                        standard_token_sequence rightTokens) := by
                simpa [leftTokens, rightTokens] using
                  fs_zfc_support_raw_implication_bodies_eq_standard
                    leftCode rightCode tokens
                    leftLength rightLength
                    hLeftCheck hRightCheck
                    hLeftMemberAt hRightMemberAt
                    hLeftDomainLengthAt hRightDomainLength
                    hParentEqualityAt
              cases hLeftProject :
                  fs_project_hilbert_tokens_decode
                    depth leftTokens with
              | none =>
                  exact
                    fs_zfc_support_raw_project_line_falsum_of_decode_none
                      depth leftTokens base
                      codes depths leftPoint hCodes hDepths
                      (Term.check_admissible_complete <|
                        set_variable_admissible leftEigen)
                      hCodesFresh hDepthsFresh
                      (by
                        intro id hId
                        simpa [leftPoint] using
                          hLeftFresh id hId)
                      hPositiveAt' hAllAt' hLeftDomain'
                      (FirstOrder.Derives.conjElimLeft hBodies)
                      hLeftDepth' hLeftProject
              | some leftFormulaProject =>
                  cases hRightProject :
                      fs_project_hilbert_tokens_decode
                        depth rightTokens with
                  | none =>
                      exact
                        fs_zfc_support_raw_project_line_falsum_of_decode_none
                          depth rightTokens base
                          codes depths rightPoint hCodes hDepths
                          (Term.check_admissible_complete <|
                            set_variable_admissible rightEigen)
                          hCodesFresh hDepthsFresh
                          (by
                            intro id hId
                            simpa [rightPoint] using
                              hRightFresh id hId)
                          hPositiveAt' hAllAt' hRightDomain'
                          (FirstOrder.Derives.conjElimRight hBodies)
                          hRightDepth' hRightProject
                  | some rightFormulaProject =>
                      have hOuter :=
                        fs_project_hilbert_tokens_decode_implication
                          depth leftTokens rightTokens
                          hLeftProject hRightProject
                      rw [hShape, hOuter] at hDecode
                      cases hDecode
            · exact
                fs_zfc_support_raw_implication_falsum_of_not_shape
                  leftCode rightCode tokens
                  leftLength rightLength
                  hLeftCheck hRightCheck
                  hLeftMemberAt hRightMemberAt
                  hLeftDomainLengthAt hRightDomainLength
                  hParentEqualityAt
                  (by simpa [leftTokens, rightTokens] using hShape))
          (by
            let Ζ : Context Nonlogical.BasicSetTheory.signature :=
              universal :: Ε
            have hUniversal :
                Ζ ⊢ₘ[fs_zfc_support_raw_theory] universal :=
              FirstOrder.Derives.assumption (by simp [Ζ])
            apply fs_zfc_support_raw_exists_elim_fresh
              [
                base + 3, base + 4, base + 5,
                base + 6, base + 7, base + 8,
                base + 9, base + 10, base + 11]
              firstPremiseId universalBody Formula.falsum
            · simpa [universal] using hUniversal
            · intro eigen hEigenFresh hOpenedCheck
              let child : SetTerm := x#eigen
              let opened : SetFormula :=
                Formula.substituteFree
                  Nonlogical.BasicSetTheory.SetSort.set
                  firstPremiseId child universalBody
              let branchBody : SetFormula :=
                (child ∈ₘ point) ∧ₘ
                  (((child ∈ₘ domₘ(codes)) ∧ₘ
                      ((depths ·ₘ child) ≐ₘ
                        Sₘ(depths ·ₘ point))) ∧ₘ
                    ((codes ·ₘ point) ≐ₘ
                      forall_codeₘ(
                        canonical_binder_variable_code_term
                          (depths ·ₘ point),
                        codes ·ₘ child)))
              let Θ : Context Nonlogical.BasicSetTheory.signature :=
                opened :: Ζ
              have hOpened :
                  Θ ⊢ₘ[fs_zfc_support_raw_theory] opened :=
                FirstOrder.Derives.assumption
                  (by simp [Θ]) hOpenedCheck
              have hCodesFixed :
                  Term.substituteFree
                      Nonlogical.BasicSetTheory.SetSort.set
                      firstPremiseId child codes =
                    codes :=
                Term.substituteFree_eq_self_of_not_mem
                  Nonlogical.BasicSetTheory.SetSort.set
                  firstPremiseId child codes <| by
                    simpa [firstPremiseId] using
                      hCodesFresh (base + 4) (by simp)
              have hDepthsFixed :
                  Term.substituteFree
                      Nonlogical.BasicSetTheory.SetSort.set
                      firstPremiseId child depths =
                    depths :=
                Term.substituteFree_eq_self_of_not_mem
                  Nonlogical.BasicSetTheory.SetSort.set
                  firstPremiseId child depths <| by
                    simpa [firstPremiseId] using
                      hDepthsFresh (base + 4) (by simp)
              have hPointFixed :
                  Term.substituteFree
                      Nonlogical.BasicSetTheory.SetSort.set
                      firstPremiseId child point =
                    point :=
                Term.substituteFree_eq_self_of_not_mem
                  Nonlogical.BasicSetTheory.SetSort.set
                  firstPremiseId child point <| by
                    simpa [firstPremiseId] using
                      hPointFresh (base + 4) (by simp)
              have hTwoFixed :
                  Term.substituteFree
                      Nonlogical.BasicSetTheory.SetSort.set
                      firstPremiseId child (numₘ(2)) =
                    numₘ(2) := by
                apply Term.substituteFree_eq_self_of_not_mem
                rw [finite_numeral_term_freeSupport]
                exact List.not_mem_nil
              have hBody :
                  Θ ⊢ₘ[fs_zfc_support_raw_theory] branchBody := by
                simpa [opened, branchBody, universalBody,
                  firstPremise, child,
                  Formula.substituteFree, Term.substituteFree,
                  set_variable, hCodesFixed, hDepthsFixed,
                  hPointFixed, hTwoFixed] using hOpened
              have hΓSub :
                  ∀ formula, formula ∈ Γ → formula ∈ Θ := by
                intro formula hFormula
                simp only [Θ, Ζ, Ε, Δ, List.mem_cons]
                exact Or.inr <| Or.inr <| Or.inr <|
                  Or.inr hFormula
              have hPositiveAt :=
                FirstOrder.Derives.context_weaken
                  (Γ := Γ) (Δ := Θ) hΓSub hPositive
              have hAllAt :=
                FirstOrder.Derives.context_weaken
                  (Γ := Γ) (Δ := Θ) hΓSub hAll
              have hCodeAt :=
                FirstOrder.Derives.context_weaken
                  (Γ := Γ) (Δ := Θ) hΓSub hCode
              have hDepthAt :=
                FirstOrder.Derives.context_weaken
                  (Γ := Γ) (Δ := Θ) hΓSub hDepth
              have hChildDomain :
                  Θ ⊢ₘ[fs_zfc_support_raw_theory]
                    child ∈ₘ domₘ(codes) := by
                simpa [branchBody] using
                  FirstOrder.Derives.conjElimLeft <|
                    FirstOrder.Derives.conjElimLeft <|
                      FirstOrder.Derives.conjElimRight hBody
              have hFormulaCodeNonempty :
                  Θ ⊢ₘ[fs_zfc_support_raw_theory]
                    FormulaCodeₘ ≠ₘ ∅ₘ :=
                FirstOrder.Derives.context_weaken
                  (Γ := []) (Δ := Θ)
                  (by simp [Θ, Ζ, Ε, Δ]) <|
                    fs_zfc_support_raw_derives_of_godel_quotation
                      GodelQuotation.formula_code_set_nonempty_derives
              let childCode : SetTerm := codes ·ₘ child
              have hChildCheck :
                  Term.CheckCertificate childCode
                    Nonlogical.BasicSetTheory.SetSort.set := by
                dsimp [childCode]
                exact Term.check_admissible_complete <|
                  function_application_term_admissible
                    codes child hCodes.admissible
                    (set_variable_admissible eigen)
              have hChildMember :
                  Θ ⊢ₘ[fs_zfc_support_raw_theory]
                    childCode ∈ₘ FormulaCodeₘ :=
                fs_zfc_support_raw_positive_sequence_application_mem
                  FormulaCodeₘ codes child
                  formula_code_set_term_admissible
                  hCodes.admissible
                  (set_variable_admissible eigen)
                  hFormulaCodeNonempty hPositiveAt hChildDomain
              have hCurrentDepthCheck :
                  Term.CheckCertificate (depths ·ₘ point)
                    Nonlogical.BasicSetTheory.SetSort.set :=
                Term.check_admissible_complete <|
                  function_application_term_admissible
                    depths point hDepths.admissible hPoint.admissible
              have hChildDepth :
                  Θ ⊢ₘ[fs_zfc_support_raw_theory]
                    (depths ·ₘ child) ≐ₘ numₘ(depth + 1) := by
                have hSuccessor :=
                  successor_term_congr_of_equality
                    (depths ·ₘ point) (numₘ(depth))
                    hCurrentDepthCheck.admissible
                    (finite_numeral_term_admissible depth)
                    hDepthAt
                simpa [finite_numeral_term] using
                  Metatheory.Derives.equality_trans
                    (by
                      simpa [branchBody] using
                        FirstOrder.Derives.conjElimRight <|
                          FirstOrder.Derives.conjElimLeft <|
                            FirstOrder.Derives.conjElimRight hBody)
                    hSuccessor
              have hParentCanonical :
                  Θ ⊢ₘ[fs_zfc_support_raw_theory]
                    standard_token_sequence tokens ≐ₘ
                      forall_codeₘ(
                        canonical_binder_variable_code_term
                          (depths ·ₘ point),
                        childCode) :=
                Metatheory.Derives.equality_trans
                  (Metatheory.Derives.equality_symm hCodeAt)
                  (by
                    simpa [branchBody, childCode] using
                      FirstOrder.Derives.conjElimRight <|
                        FirstOrder.Derives.conjElimRight hBody)
              let name := GodelQuotation.bound_name depth
              let namedCode : SetTerm :=
                Numbered.named_variable_code name
              let binderCode : SetTerm :=
                canonical_binder_variable_code_term
                  (depths ·ₘ point)
              have hNamedCheck :
                  Term.CheckCertificate namedCode
                    Nonlogical.BasicSetTheory.SetSort.set := by
                dsimp [namedCode, name]
                prove_term_check
              have hBinderCheck :
                  Term.CheckCertificate binderCode
                    Nonlogical.BasicSetTheory.SetSort.set := by
                dsimp [binderCode]
                prove_term_check
              have hBinderNumeral :
                  Θ ⊢ₘ[fs_zfc_support_raw_theory]
                    namedCode ≐ₘ
                      canonical_binder_variable_code_term
                        (numₘ(depth)) := by
                dsimp [namedCode, name]
                exact FirstOrder.Derives.context_weaken
                  (Γ := []) (Δ := Θ) (by simp) <|
                    fs_zfc_support_raw_derives_of_godel_quotation
                      (canonical_binder_variable_code_numeral_derives
                        depth)
              have hBinderToCurrent :
                  Θ ⊢ₘ[fs_zfc_support_raw_theory]
                    canonical_binder_variable_code_term
                        (numₘ(depth)) ≐ₘ
                      binderCode := by
                dsimp [binderCode]
                exact
                  canonical_binder_variable_code_term_congr_of_equality
                    (numₘ(depth)) (depths ·ₘ point)
                    (finite_numeral_term_admissible depth)
                    hCurrentDepthCheck.admissible
                    (Metatheory.Derives.equality_symm hDepthAt)
              have hNamedToBinder :
                  Θ ⊢ₘ[fs_zfc_support_raw_theory]
                    namedCode ≐ₘ binderCode :=
                Metatheory.Derives.equality_trans
                  hBinderNumeral hBinderToCurrent
              have hBinderCongruence :
                  Θ ⊢ₘ[fs_zfc_support_raw_theory]
                    forall_codeₘ(binderCode, childCode) ≐ₘ
                      forall_codeₘ(namedCode, childCode) :=
                canonical_universal_code_term_congr_of_equalities
                  binderCode namedCode childCode childCode
                  hBinderCheck.admissible hNamedCheck.admissible
                  hChildCheck.admissible hChildCheck.admissible
                  (Metatheory.Derives.equality_symm
                    hNamedToBinder)
                  (Metatheory.Derives.equality_refl
                    childCode
                    (hTermCheck := hChildCheck))
              have hParentEquality :
                  Θ ⊢ₘ[fs_zfc_support_raw_theory]
                    standard_token_sequence tokens ≐ₘ
                      forall_codeₘ(namedCode, childCode) :=
                Metatheory.Derives.equality_trans
                  (by
                    simpa [binderCode] using hParentCanonical)
                  hBinderCongruence
              have hBodyDomainMember :
                  Θ ⊢ₘ[fs_zfc_support_raw_theory]
                    domₘ(childCode) ∈ₘ
                      domₘ(forall_codeₘ(namedCode, childCode)) := by
                simpa [namedCode] using
                  fs_zfc_support_raw_universal_body_domain_mem
                    name childCode hChildCheck hChildMember
              refine CertifiedProof.fs_zfc_support_raw_domain_length_elim
                (child := childCode)
                (parent := forall_codeₘ(namedCode, childCode))
                (tokens := tokens)
                (conclusion := Formula.falsum)
                (hChild := hChildCheck.admissible)
                (hParent := by prove_term_check)
                (hConclusion := Formula.Admissible.falsum)
                hBodyDomainMember hParentEquality ?_
              intro bodyLength hBodyLength
              let Λ : Context Nonlogical.BasicSetTheory.signature :=
                (domₘ(childCode) ≐ₘ numₘ(bodyLength)) :: Θ
              have hBodyDomainLength :
                  Λ ⊢ₘ[fs_zfc_support_raw_theory]
                    domₘ(childCode) ≐ₘ numₘ(bodyLength) :=
                FirstOrder.Derives.assumption (by simp [Λ])
              let bodyTokens :=
                (tokens.drop 3).take bodyLength
              have hChildMemberAt :
                  Λ ⊢ₘ[fs_zfc_support_raw_theory]
                    childCode ∈ₘ FormulaCodeₘ := by
                simpa [Λ] using
                  FirstOrder.Derives.context_weaken_cons
                    (assumption :=
                      domₘ(childCode) ≐ₘ numₘ(bodyLength))
                    hChildMember
              have hParentEqualityAt :
                  Λ ⊢ₘ[fs_zfc_support_raw_theory]
                    standard_token_sequence tokens ≐ₘ
                      forall_codeₘ(namedCode, childCode) := by
                simpa [Λ] using
                  FirstOrder.Derives.context_weaken_cons
                    (assumption :=
                      domₘ(childCode) ≐ₘ numₘ(bodyLength))
                    hParentEquality
              by_cases hShape :
                  tokens =
                    Numbered.universal_tokens name bodyTokens
              · have hChildEquality :
                    Λ ⊢ₘ[fs_zfc_support_raw_theory]
                      childCode ≐ₘ
                        standard_token_sequence bodyTokens :=
                  fs_zfc_support_raw_universal_body_eq_standard
                    name childCode bodyTokens hChildCheck
                    hChildMemberAt
                    (by simpa [hShape] using hParentEqualityAt)
                have hStrict :
                    bodyTokens.length < tokens.length := by
                  rw [hShape]
                  simp [Numbered.universal_tokens]
                  omega
                cases hProject :
                    fs_project_hilbert_tokens_decode
                      (depth + 1) bodyTokens with
                | none =>
                    exact
                      fs_zfc_support_raw_project_line_falsum_of_decode_none
                        (depth + 1) bodyTokens base
                        codes depths child hCodes hDepths
                        (Term.check_admissible_complete <|
                          set_variable_admissible eigen)
                        hCodesFresh hDepthsFresh
                        (by
                          intro id hId
                          simpa [child] using
                            hEigenFresh id hId)
                        (FirstOrder.Derives.context_weaken_cons
                          hPositiveAt)
                        (FirstOrder.Derives.context_weaken_cons
                          hAllAt)
                        (FirstOrder.Derives.context_weaken_cons
                          hChildDomain)
                        hChildEquality
                        (FirstOrder.Derives.context_weaken_cons
                          hChildDepth)
                        hProject
                | some body =>
                    have hOuter :=
                      fs_project_hilbert_tokens_decode_universal
                        depth name bodyTokens (by rfl) hProject
                    rw [hShape, hOuter] at hDecode
                    cases hDecode
              · exact
                  fs_zfc_support_raw_universal_falsum_of_not_shape
                    name childCode tokens bodyLength
                    hChildCheck hChildMemberAt hBodyDomainLength
                    (by simpa [namedCode] using hParentEqualityAt)
                    (by simpa [bodyTokens] using hShape)))
termination_by tokens.length

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
