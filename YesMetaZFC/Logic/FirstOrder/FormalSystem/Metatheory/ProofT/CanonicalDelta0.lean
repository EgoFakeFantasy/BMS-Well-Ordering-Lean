import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaClassifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalProjectTokenShift.Core
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Hierarchy

/-!
# 规范公式与 cutoff-shift 的 `Delta0` 证书

本模块只承载已经显式有界化的规范见证。`TermCodeₘ` 约束原子中的两个项码见证，
`ωₘ` 约束 shift 中的目标深度见证；其余证明只使用布尔联结词和成员有界量词。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-! ## 规范变量 -/

theorem canonical_scoped_variable_code_condition_delta0
    (depth variableCode : SetTerm)
    (variableDepthId : FreeVarId)
    (hDepthFresh :
      (SetSort.set, variableDepthId) ∉
        Term.freeSupport depth) :
    Formula.IsDelta0 set_levy_bound
      (canonical_scoped_variable_code_condition_with_id
        depth variableCode variableDepthId) := by
  have hBody :
      Formula.IsDelta0 set_levy_bound
        ((x#variableDepthId ∈ₘ depth) ∧ₘ
          (variableCode ≐ₘ
            canonical_binder_variable_code_term
              (x#variableDepthId))) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [x#variableDepthId, depth])
      (Formula.IsDelta0.equal
        variableCode
        (canonical_binder_variable_code_term
          (x#variableDepthId)))
  simpa [canonical_scoped_variable_code_condition_with_id] using
    Formula.IsDelta0.guarded_exists_closeFreeAt
      variableDepthId depth hDepthFresh hBody
      (Formula.FreeMembershipGuard.conj_left
        Formula.FreeMembershipGuard.membership)

/-! ## 原子分类器 -/

theorem canonical_project_atomic_code_condition_with_ids_delta0
    (depth code : SetTerm)
    (leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId)
    (hDepthLeftFresh :
      (SetSort.set, leftVariableDepthId) ∉
        Term.freeSupport depth)
    (hDepthRightFresh :
      (SetSort.set, rightVariableDepthId) ∉
        Term.freeSupport depth)
    :
    Formula.IsDelta0 set_levy_bound
      (canonical_project_atomic_code_condition_with_ids
        depth code
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId) := by
  let leftVariable := x#leftVariableCodeId
  let rightVariable := x#rightVariableCodeId
  have hLeftScope :
      Formula.IsDelta0 set_levy_bound
        (canonical_scoped_variable_code_condition_with_id
          depth leftVariable leftVariableDepthId) :=
    canonical_scoped_variable_code_condition_delta0
      depth leftVariable leftVariableDepthId
      hDepthLeftFresh
  have hRightScope :
      Formula.IsDelta0 set_levy_bound
        (canonical_scoped_variable_code_condition_with_id
          depth rightVariable rightVariableDepthId) :=
    canonical_scoped_variable_code_condition_delta0
      depth rightVariable rightVariableDepthId
      hDepthRightFresh
  have hLeftGuard :
      Formula.IsDelta0 set_levy_bound
        (leftVariable ∈ₘ TermCodeₘ) :=
    Formula.IsDelta0.rel
      RelationSymbol.membership
      [leftVariable, TermCodeₘ]
  have hRightGuard :
      Formula.IsDelta0 set_levy_bound
        (rightVariable ∈ₘ TermCodeₘ) :=
    Formula.IsDelta0.rel
      RelationSymbol.membership
      [rightVariable, TermCodeₘ]
  have hShape :
      Formula.IsDelta0 set_levy_bound
        ((code ≐ₘ eq_codeₘ(leftVariable, rightVariable)) ∨ₘ
          ((code ≐ₘ
              membership_atomic_formula_code_term
                leftVariable rightVariable) ∨ₘ
            (code ≐ₘ
              project_subset_atomic_code_term
                leftVariable rightVariable))) :=
    Formula.IsDelta0.disj
      (Formula.IsDelta0.equal
        code (eq_codeₘ(leftVariable, rightVariable)))
      (Formula.IsDelta0.disj
        (Formula.IsDelta0.equal
          code
          (membership_atomic_formula_code_term
            leftVariable rightVariable))
        (Formula.IsDelta0.equal
          code
          (project_subset_atomic_code_term
            leftVariable rightVariable)))
  have hRightBody :
      Formula.IsDelta0 set_levy_bound
        ((canonical_scoped_variable_code_condition_with_id
            depth leftVariable leftVariableDepthId ∧ₘ
          canonical_scoped_variable_code_condition_with_id
            depth rightVariable rightVariableDepthId) ∧ₘ
          ((code ≐ₘ eq_codeₘ(leftVariable, rightVariable)) ∨ₘ
            ((code ≐ₘ
                membership_atomic_formula_code_term
                  leftVariable rightVariable) ∨ₘ
              (code ≐ₘ
                project_subset_atomic_code_term
                  leftVariable rightVariable)))) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.conj hLeftScope hRightScope)
      hShape
  have hRight :=
    Formula.IsDelta0.bounded_exists_closeFreeAt
      rightVariableCodeId TermCodeₘ
      (by simp [Term.freeSupport, Term.freeSupportList])
      hRightBody
  simpa [canonical_project_atomic_code_condition_with_ids,
    leftVariable, rightVariable] using
    Formula.IsDelta0.bounded_exists_closeFreeAt
      leftVariableCodeId TermCodeₘ
      (by simp [Term.freeSupport, Term.freeSupportList])
      hRight

/-! ## 规范公式轨迹的逐行分类 -/

theorem canonical_project_formula_line_condition_with_ids_delta0
    (codes depths index : SetTerm)
    (firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId)
    (hFirstPremiseFresh :
      (SetSort.set, firstPremiseId) ∉
        Term.freeSupport index)
    (hSecondPremiseFresh :
      (SetSort.set, secondPremiseId) ∉
        Term.freeSupport index)
    (hLeftDepthFresh :
      (SetSort.set, leftVariableDepthId) ∉
        Term.freeSupport (depths ·ₘ index))
    (hRightDepthFresh :
      (SetSort.set, rightVariableDepthId) ∉
        Term.freeSupport (depths ·ₘ index)) :
    Formula.IsDelta0 set_levy_bound
      (canonical_project_formula_line_condition_with_ids
        codes depths index
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId) := by
  let firstPremise := x#firstPremiseId
  let secondPremise := x#secondPremiseId
  have hAtomic :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_atomic_code_condition_with_ids
          (depths ·ₘ index) (codes ·ₘ index)
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId) :=
    canonical_project_atomic_code_condition_with_ids_delta0
      (depths ·ₘ index) (codes ·ₘ index)
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId
      hLeftDepthFresh hRightDepthFresh
  have hNegBody :
      Formula.IsDelta0 set_levy_bound
        ((firstPremise ∈ₘ index) ∧ₘ
          (((firstPremise ∈ₘ domₘ(codes)) ∧ₘ
              ((depths ·ₘ firstPremise) ≐ₘ
                (depths ·ₘ index))) ∧ₘ
            ((codes ·ₘ index) ≐ₘ
              neg_codeₘ(codes ·ₘ firstPremise)))) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [firstPremise, index])
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.rel
            RelationSymbol.membership
            [firstPremise, domₘ(codes)])
          (Formula.IsDelta0.equal
            (depths ·ₘ firstPremise)
            (depths ·ₘ index)))
        (Formula.IsDelta0.equal
          (codes ·ₘ index)
          (neg_codeₘ(codes ·ₘ firstPremise))))
  have hNeg :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, firstPremiseId],
          (x#firstPremiseId ∈ₘ index) ∧ₘ
            (((x#firstPremiseId ∈ₘ domₘ(codes)) ∧ₘ
                ((depths ·ₘ x#firstPremiseId) ≐ₘ
                  (depths ·ₘ index))) ∧ₘ
              ((codes ·ₘ index) ≐ₘ
                neg_codeₘ(codes ·ₘ x#firstPremiseId)))) := by
    simpa [firstPremise] using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        firstPremiseId index
        hFirstPremiseFresh hNegBody
        (Formula.FreeMembershipGuard.conj_left
          Formula.FreeMembershipGuard.membership)
  have hImpBody :
      Formula.IsDelta0 set_levy_bound
        ((secondPremise ∈ₘ index) ∧ₘ
          ((((firstPremise ∈ₘ domₘ(codes)) ∧ₘ
              (secondPremise ∈ₘ domₘ(codes))) ∧ₘ
              (((depths ·ₘ firstPremise) ≐ₘ
                  (depths ·ₘ index)) ∧ₘ
                ((depths ·ₘ secondPremise) ≐ₘ
                  (depths ·ₘ index)))) ∧ₘ
            ((codes ·ₘ index) ≐ₘ
              imp_codeₘ(
                codes ·ₘ firstPremise,
                codes ·ₘ secondPremise)))) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [secondPremise, index])
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.conj
            (Formula.IsDelta0.rel
              RelationSymbol.membership
              [firstPremise, domₘ(codes)])
            (Formula.IsDelta0.rel
              RelationSymbol.membership
              [secondPremise, domₘ(codes)]))
          (Formula.IsDelta0.conj
            (Formula.IsDelta0.equal
              (depths ·ₘ firstPremise)
              (depths ·ₘ index))
            (Formula.IsDelta0.equal
              (depths ·ₘ secondPremise)
              (depths ·ₘ index))))
        (Formula.IsDelta0.equal
          (codes ·ₘ index)
          (imp_codeₘ(
            codes ·ₘ firstPremise,
            codes ·ₘ secondPremise))))
  have hImpInner :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, secondPremiseId],
          (x#secondPremiseId ∈ₘ index) ∧ₘ
            ((((x#firstPremiseId ∈ₘ domₘ(codes)) ∧ₘ
                (x#secondPremiseId ∈ₘ domₘ(codes))) ∧ₘ
                (((depths ·ₘ x#firstPremiseId) ≐ₘ
                    (depths ·ₘ index)) ∧ₘ
                  ((depths ·ₘ x#secondPremiseId) ≐ₘ
                    (depths ·ₘ index)))) ∧ₘ
              ((codes ·ₘ index) ≐ₘ
                imp_codeₘ(
                  codes ·ₘ x#firstPremiseId,
                  codes ·ₘ x#secondPremiseId)))) := by
    simpa [firstPremise, secondPremise] using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        secondPremiseId index
        hSecondPremiseFresh hImpBody
        (Formula.FreeMembershipGuard.conj_left
          Formula.FreeMembershipGuard.membership)
  have hImpOuterBody :
      Formula.IsDelta0 set_levy_bound
        ((firstPremise ∈ₘ index) ∧ₘ
          (∃ₘ[SetSort.set, secondPremiseId],
            (x#secondPremiseId ∈ₘ index) ∧ₘ
              ((((x#firstPremiseId ∈ₘ domₘ(codes)) ∧ₘ
                  (x#secondPremiseId ∈ₘ domₘ(codes))) ∧ₘ
                  (((depths ·ₘ x#firstPremiseId) ≐ₘ
                      (depths ·ₘ index)) ∧ₘ
                    ((depths ·ₘ x#secondPremiseId) ≐ₘ
                      (depths ·ₘ index)))) ∧ₘ
                ((codes ·ₘ index) ≐ₘ
                  imp_codeₘ(
                    codes ·ₘ x#firstPremiseId,
                    codes ·ₘ x#secondPremiseId))))) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [firstPremise, index])
      hImpInner
  have hImp :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, firstPremiseId],
          (x#firstPremiseId ∈ₘ index) ∧ₘ
            (∃ₘ[SetSort.set, secondPremiseId],
              (x#secondPremiseId ∈ₘ index) ∧ₘ
                ((((x#firstPremiseId ∈ₘ domₘ(codes)) ∧ₘ
                    (x#secondPremiseId ∈ₘ domₘ(codes))) ∧ₘ
                    (((depths ·ₘ x#firstPremiseId) ≐ₘ
                        (depths ·ₘ index)) ∧ₘ
                      ((depths ·ₘ x#secondPremiseId) ≐ₘ
                        (depths ·ₘ index)))) ∧ₘ
                  ((codes ·ₘ index) ≐ₘ
                    imp_codeₘ(
                      codes ·ₘ x#firstPremiseId,
                      codes ·ₘ x#secondPremiseId))))) := by
    simpa [firstPremise] using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        firstPremiseId index
        hFirstPremiseFresh hImpOuterBody
        (Formula.FreeMembershipGuard.conj_left
          Formula.FreeMembershipGuard.membership)
  have hUniversalBody :
      Formula.IsDelta0 set_levy_bound
        ((firstPremise ∈ₘ index) ∧ₘ
          (((firstPremise ∈ₘ domₘ(codes)) ∧ₘ
              ((depths ·ₘ firstPremise) ≐ₘ
                Sₘ(depths ·ₘ index))) ∧ₘ
            ((codes ·ₘ index) ≐ₘ
              forall_codeₘ(
                canonical_binder_variable_code_term
                  (depths ·ₘ index),
                codes ·ₘ firstPremise)))) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [firstPremise, index])
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.rel
            RelationSymbol.membership
            [firstPremise, domₘ(codes)])
          (Formula.IsDelta0.equal
            (depths ·ₘ firstPremise)
            (Sₘ(depths ·ₘ index))))
        (Formula.IsDelta0.equal
          (codes ·ₘ index)
          (forall_codeₘ(
            canonical_binder_variable_code_term
              (depths ·ₘ index),
            codes ·ₘ firstPremise))))
  have hUniversal :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, firstPremiseId],
          (x#firstPremiseId ∈ₘ index) ∧ₘ
            (((x#firstPremiseId ∈ₘ domₘ(codes)) ∧ₘ
                ((depths ·ₘ x#firstPremiseId) ≐ₘ
                  Sₘ(depths ·ₘ index))) ∧ₘ
              ((codes ·ₘ index) ≐ₘ
                forall_codeₘ(
                  canonical_binder_variable_code_term
                    (depths ·ₘ index),
                  codes ·ₘ x#firstPremiseId)))) := by
    simpa [firstPremise] using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        firstPremiseId index
        hFirstPremiseFresh hUniversalBody
        (Formula.FreeMembershipGuard.conj_left
          Formula.FreeMembershipGuard.membership)
  simpa [canonical_project_formula_line_condition_with_ids,
    firstPremise, secondPremise] using
    Formula.IsDelta0.disj hAtomic
      (Formula.IsDelta0.disj hNeg
        (Formula.IsDelta0.disj hImp hUniversal))

/-! ## 规范公式轨迹 -/

theorem canonical_project_formula_trace_condition_with_ids_delta0
    (entryDepth code codes depths : SetTerm)
    (lastIndexId indexId
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId)
    (hCodesFresh :
      (SetSort.set, indexId) ∉
        Term.freeSupport (domₘ(codes)))
    (hFirstPremiseFresh :
      (SetSort.set, firstPremiseId) ∉
        Term.freeSupport (x#indexId))
    (hSecondPremiseFresh :
      (SetSort.set, secondPremiseId) ∉
        Term.freeSupport (x#indexId))
    (hLeftDepthFresh :
      (SetSort.set, leftVariableDepthId) ∉
        Term.freeSupport (depths ·ₘ x#indexId))
    (hRightDepthFresh :
      (SetSort.set, rightVariableDepthId) ∉
        Term.freeSupport (depths ·ₘ x#indexId))
    (hLastFresh :
      (SetSort.set, lastIndexId) ∉
        Term.freeSupport (domₘ(codes))) :
    Formula.IsDelta0 set_levy_bound
      (canonical_project_formula_trace_condition_with_ids
        entryDepth code codes depths
        lastIndexId indexId
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId) := by
  have hCodesSpace :
      Formula.IsDelta0 set_levy_bound
        (codes ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) :=
    Formula.IsDelta0.rel
      RelationSymbol.membership
      [codes, seq₊_spaceₘ(FormulaCodeₘ)]
  have hDepthsSpace :
      Formula.IsDelta0 set_levy_bound
        (depths ∈ₘ seq₊_spaceₘ(ωₘ)) :=
    Formula.IsDelta0.rel
      RelationSymbol.membership
      [depths, seq₊_spaceₘ(ωₘ)]
  have hDomain :
      Formula.IsDelta0 set_levy_bound
        (domₘ(codes) ≐ₘ domₘ(depths)) :=
    Formula.IsDelta0.equal
      (domₘ(codes)) (domₘ(depths))
  have hZero :
      Formula.IsDelta0 set_levy_bound
        (numₘ(0) ∈ₘ domₘ(codes)) :=
    Formula.IsDelta0.rel
      RelationSymbol.membership
      [numₘ(0), domₘ(codes)]
  have hLine :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_formula_line_condition_with_ids
          codes depths (x#indexId)
          firstPremiseId secondPremiseId
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId) :=
    canonical_project_formula_line_condition_with_ids_delta0
      codes depths (x#indexId)
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId
      hFirstPremiseFresh hSecondPremiseFresh
      hLeftDepthFresh hRightDepthFresh
  have hLineForall :
      Formula.IsDelta0 set_levy_bound
        (∀ₘ[SetSort.set, indexId],
          (x#indexId ∈ₘ domₘ(codes)) ⟶ₘ
            canonical_project_formula_line_condition_with_ids
              codes depths (x#indexId)
              firstPremiseId secondPremiseId
              leftVariableCodeId rightVariableCodeId
              leftVariableDepthId rightVariableDepthId) := by
    simpa using
      Formula.IsDelta0.bounded_forall_closeFreeAt
        indexId (domₘ(codes))
        hCodesFresh hLine
  have hTerminalBody :
      Formula.IsDelta0 set_levy_bound
        (((x#lastIndexId ∈ₘ domₘ(codes)) ∧ₘ
            (domₘ(codes) ≐ₘ Sₘ(x#lastIndexId))) ∧ₘ
          ((code ≐ₘ (codes ·ₘ x#lastIndexId)) ∧ₘ
            (entryDepth ≐ₘ (depths ·ₘ x#lastIndexId)))) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.rel
          RelationSymbol.membership
          [x#lastIndexId, domₘ(codes)])
        (Formula.IsDelta0.equal
          (domₘ(codes)) (Sₘ(x#lastIndexId))))
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.equal
          code (codes ·ₘ x#lastIndexId))
        (Formula.IsDelta0.equal
          entryDepth (depths ·ₘ x#lastIndexId)))
  have hTerminal :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, lastIndexId],
          (((x#lastIndexId ∈ₘ domₘ(codes)) ∧ₘ
              (domₘ(codes) ≐ₘ Sₘ(x#lastIndexId))) ∧ₘ
            ((code ≐ₘ (codes ·ₘ x#lastIndexId)) ∧ₘ
              (entryDepth ≐ₘ (depths ·ₘ x#lastIndexId))))) := by
    simpa using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        lastIndexId (domₘ(codes))
        hLastFresh hTerminalBody
        (Formula.FreeMembershipGuard.conj_left
          (Formula.FreeMembershipGuard.conj_left
            Formula.FreeMembershipGuard.membership))
  have hPrefix :
      Formula.IsDelta0 set_levy_bound
        (((((codes ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
            (depths ∈ₘ seq₊_spaceₘ(ωₘ))) ∧ₘ
          (domₘ(codes) ≐ₘ domₘ(depths))) ∧ₘ
          (numₘ(0) ∈ₘ domₘ(codes)))) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj hCodesSpace hDepthsSpace)
        hDomain)
      hZero
  simpa [canonical_project_formula_trace_condition_with_ids] using
    Formula.IsDelta0.conj hPrefix
      (Formula.IsDelta0.conj hLineForall hTerminal)

/-! ## 规范公式码分类条件 -/

theorem canonical_project_formula_code_condition_with_ids_delta0
    (entryDepth code : SetTerm)
    (codesId depthsId lastIndexId indexId
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId)
    (hIndexFresh :
      (SetSort.set, indexId) ∉
        Term.freeSupport (domₘ(x#codesId)))
    (hFirstPremiseFresh :
      (SetSort.set, firstPremiseId) ∉
        Term.freeSupport (x#indexId))
    (hSecondPremiseFresh :
      (SetSort.set, secondPremiseId) ∉
        Term.freeSupport (x#indexId))
    (hLeftDepthFresh :
      (SetSort.set, leftVariableDepthId) ∉
        Term.freeSupport (x#depthsId ·ₘ x#indexId))
    (hRightDepthFresh :
      (SetSort.set, rightVariableDepthId) ∉
        Term.freeSupport (x#depthsId ·ₘ x#indexId))
    (hLastFresh :
      (SetSort.set, lastIndexId) ∉
        Term.freeSupport (domₘ(x#codesId))) :
    Formula.IsDelta0 set_levy_bound
      (canonical_project_formula_code_condition_with_ids
        entryDepth code
        codesId depthsId lastIndexId indexId
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId) := by
  let codes := x#codesId
  let depths := x#depthsId
  have hTrace :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_formula_trace_condition_with_ids
          entryDepth code codes depths
          lastIndexId indexId
          firstPremiseId secondPremiseId
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId) :=
    canonical_project_formula_trace_condition_with_ids_delta0
      entryDepth code codes depths
      lastIndexId indexId
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId
      hIndexFresh hFirstPremiseFresh hSecondPremiseFresh
      hLeftDepthFresh hRightDepthFresh hLastFresh
  have hDepths :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, depthsId],
          canonical_project_formula_trace_condition_with_ids
            entryDepth code codes depths
            lastIndexId indexId
            firstPremiseId secondPremiseId
            leftVariableCodeId rightVariableCodeId
            leftVariableDepthId rightVariableDepthId) := by
    simpa [depths] using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        depthsId (seq₊_spaceₘ(ωₘ))
        (by simp [Term.freeSupport, Term.freeSupportList])
        hTrace
        (Formula.FreeMembershipGuard.conj_left
          (Formula.FreeMembershipGuard.conj_left
            (Formula.FreeMembershipGuard.conj_left
              (Formula.FreeMembershipGuard.conj_right
                Formula.FreeMembershipGuard.membership))))
  have hCodesBody :
      Formula.IsDelta0 set_levy_bound
        ((codes ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
          (∃ₘ[SetSort.set, depthsId],
            canonical_project_formula_trace_condition_with_ids
              entryDepth code codes depths
              lastIndexId indexId
              firstPremiseId secondPremiseId
              leftVariableCodeId rightVariableCodeId
              leftVariableDepthId rightVariableDepthId)) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [codes, seq₊_spaceₘ(FormulaCodeₘ)])
      hDepths
  have hCodes :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, codesId],
          (x#codesId ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
            (∃ₘ[SetSort.set, depthsId],
              canonical_project_formula_trace_condition_with_ids
                entryDepth code (x#codesId) (x#depthsId)
                lastIndexId indexId
                firstPremiseId secondPremiseId
                leftVariableCodeId rightVariableCodeId
                leftVariableDepthId rightVariableDepthId)) := by
    simpa [codes, depths] using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        codesId (seq₊_spaceₘ(FormulaCodeₘ))
        (by simp [Term.freeSupport, Term.freeSupportList])
        hCodesBody
        (Formula.FreeMembershipGuard.conj_left
          Formula.FreeMembershipGuard.membership)
  have hPrefix :
      Formula.IsDelta0 set_levy_bound
        ((entryDepth ∈ₘ ωₘ) ∧ₘ formula_codeₘ(code)) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [entryDepth, ωₘ])
      (Formula.IsDelta0.rel
        RelationSymbol.isFormulaCode
        [code])
  simpa [canonical_project_formula_code_condition_with_ids,
    codes, depths] using
    Formula.IsDelta0.conj hPrefix hCodes

/-! ## cutoff-shift token 图 -/

theorem canonical_project_shift_token_condition_with_ids_delta0
    (cutoff sourceValue targetValue : SetTerm)
    (sourceDepthId targetDepthId : FreeVarId)
    (hSourceDepthFresh :
      (SetSort.set, sourceDepthId) ∉
        Term.freeSupport (Sₘ(sourceValue))) :
    Formula.IsDelta0 set_levy_bound
      (canonical_project_shift_token_condition_with_ids
        cutoff sourceValue targetValue
        sourceDepthId targetDepthId) := by
  let sourceDepth := x#sourceDepthId
  let targetDepth := x#targetDepthId
  have hSourceDepth :
      Formula.IsDelta0 set_levy_bound
        (sourceDepth ∈ₘ Sₘ(sourceValue)) :=
    Formula.IsDelta0.rel
      RelationSymbol.membership
      [sourceDepth, Sₘ(sourceValue)]
  have hTargetDepth :
      Formula.IsDelta0 set_levy_bound
        (targetDepth ∈ₘ ωₘ) :=
    Formula.IsDelta0.rel
      RelationSymbol.membership
      [targetDepth, ωₘ]
  have hSourceValue :
      Formula.IsDelta0 set_levy_bound
        (sourceValue ≐ₘ
          variable_symbol_number_term
            (Sₘ(numₘ(2) *ₘ sourceDepth))) :=
    Formula.IsDelta0.equal
      sourceValue
      (variable_symbol_number_term
        (Sₘ(numₘ(2) *ₘ sourceDepth)))
  have hTargetValue :
      Formula.IsDelta0 set_levy_bound
        (targetValue ≐ₘ
          variable_symbol_number_term
            (Sₘ(numₘ(2) *ₘ targetDepth))) :=
    Formula.IsDelta0.equal
      targetValue
      (variable_symbol_number_term
        (Sₘ(numₘ(2) *ₘ targetDepth)))
  have hShift :
      Formula.IsDelta0 set_levy_bound
        (canonical_shifted_depth_condition
          cutoff sourceDepth targetDepth) :=
    canonical_shifted_depth_condition_delta0
      cutoff sourceDepth targetDepth
  have hTargetBody :
      Formula.IsDelta0 set_levy_bound
        ((sourceValue ≐ₘ
            variable_symbol_number_term
              (Sₘ(numₘ(2) *ₘ sourceDepth))) ∧ₘ
          (canonical_shifted_depth_condition
              cutoff sourceDepth targetDepth ∧ₘ
            (targetValue ≐ₘ
              variable_symbol_number_term
                (Sₘ(numₘ(2) *ₘ targetDepth))))) :=
    Formula.IsDelta0.conj hSourceValue
      (Formula.IsDelta0.conj hShift hTargetValue)
  have hTarget :=
    Formula.IsDelta0.bounded_exists_closeFreeAt
      targetDepthId ωₘ
      (by simp [Term.freeSupport, Term.freeSupportList])
      hTargetBody
  have hVariable :=
    Formula.IsDelta0.bounded_exists_closeFreeAt
      sourceDepthId (Sₘ(sourceValue))
      hSourceDepthFresh hTarget
  have hFixed :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_shift_fixed_token_condition sourceValue ∧ₘ
          (targetValue ≐ₘ sourceValue)) :=
    Formula.IsDelta0.conj
      (by
        have hFixedBase :
            Formula.IsDelta0 set_levy_bound
              (canonical_binder_shift_fixed_token_condition sourceValue) := by
          simpa [canonical_binder_shift_fixed_token_condition] using
            (Formula.IsDelta0.disj
              (Formula.IsDelta0.equal
                sourceValue (logical_symbol_number_term .equality))
              (Formula.IsDelta0.disj
                (Formula.IsDelta0.equal
                  sourceValue (logical_symbol_number_term .negation))
                (Formula.IsDelta0.disj
                  (Formula.IsDelta0.equal
                    sourceValue (logical_symbol_number_term .implication))
                  (Formula.IsDelta0.disj
                    (Formula.IsDelta0.equal
                      sourceValue (logical_symbol_number_term .universal))
                    (Formula.IsDelta0.disj
                      (Formula.IsDelta0.equal
                        sourceValue (logical_symbol_number_term .leftParenthesis))
                      (Formula.IsDelta0.disj
                        (Formula.IsDelta0.equal
                          sourceValue (logical_symbol_number_term .rightParenthesis))
                        (Formula.IsDelta0.disj
                          (Formula.IsDelta0.equal
                            sourceValue (logical_symbol_number_term .existential))
                          (Formula.IsDelta0.disj
                            (Formula.IsDelta0.equal
                              sourceValue (logical_symbol_number_term .conjunction))
                            (Formula.IsDelta0.disj
                              (Formula.IsDelta0.equal
                                sourceValue membership_symbol_number_term)
                              Formula.IsDelta0.falsum)))))))))
        simpa [canonical_project_shift_fixed_token_condition] using
          Formula.IsDelta0.disj
            hFixedBase
            (Formula.IsDelta0.equal
              sourceValue
              (coded_predicate_symbol_number_term
                (numₘ(1))
                (numₘ(RelationSymbol.subset.ctorIdx)))))
      (Formula.IsDelta0.equal targetValue sourceValue)
  simpa [canonical_project_shift_token_condition_with_ids] using
    Formula.IsDelta0.disj hFixed hVariable

/-! ## cutoff-shift 序列图与全称前缀图 -/

/-- 两条有限 token 序列逐点实现 cutoff-shift 的 `Delta0` 证书。 -/
theorem canonical_project_shift_code_condition_with_ids_delta0
    (cutoff sourceCode targetCode : SetTerm)
    (indexId sourceDepthId targetDepthId : FreeVarId)
    (hIndexFresh :
      (SetSort.set, indexId) ∉
        Term.freeSupport (domₘ(sourceCode)))
    (hSourceDepthFresh :
      (SetSort.set, sourceDepthId) ∉
        Term.freeSupport
          (Sₘ(sourceCode ·ₘ x#indexId))) :
    Formula.IsDelta0 set_levy_bound
      (canonical_project_shift_code_condition_with_ids
        cutoff sourceCode targetCode
        indexId sourceDepthId targetDepthId) := by
  let prefixFormula : SetFormula :=
    (((cutoff ∈ₘ ωₘ) ∧ₘ
      finite_sequence_condition sourceCode) ∧ₘ
      finite_sequence_condition targetCode) ∧ₘ
      (domₘ(sourceCode) ≐ₘ domₘ(targetCode))
  have hPrefix :
      Formula.IsDelta0 set_levy_bound prefixFormula := by
    have hLeft :
        Formula.IsDelta0 set_levy_bound
          (((cutoff ∈ₘ ωₘ) ∧ₘ
            finite_sequence_condition sourceCode) ∧ₘ
            finite_sequence_condition targetCode) :=
      Formula.IsDelta0.conj
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.rel
            RelationSymbol.membership [cutoff, ωₘ])
          (finite_sequence_condition_delta0 sourceCode))
        (finite_sequence_condition_delta0 targetCode)
    exact Formula.IsDelta0.conj
      hLeft
      (Formula.IsDelta0.equal
        (domₘ(sourceCode)) (domₘ(targetCode)))
  let point : SetFormula :=
    canonical_project_shift_token_condition_with_ids
      cutoff
      (sourceCode ·ₘ x#indexId)
      (targetCode ·ₘ x#indexId)
      sourceDepthId targetDepthId
  have hPoint :
      Formula.IsDelta0 set_levy_bound
        point := by
    exact
      (canonical_project_shift_token_condition_with_ids_delta0
        cutoff
        (sourceCode ·ₘ x#indexId)
        (targetCode ·ₘ x#indexId)
        sourceDepthId targetDepthId
        hSourceDepthFresh)
  let pointwise : SetFormula :=
    ∀ₘ[SetSort.set, indexId],
      (x#indexId ∈ₘ domₘ(sourceCode)) ⟶ₘ
        point
  have hPointwise :
      Formula.IsDelta0 set_levy_bound
        pointwise := by
    simpa using
      Formula.IsDelta0.bounded_forall_closeFreeAt
        indexId (domₘ(sourceCode))
        hIndexFresh hPoint
  simpa [canonical_project_shift_code_condition_with_ids] using
    (show Formula.IsDelta0 set_levy_bound
      (prefixFormula ∧ₘ pointwise) from
      Formula.IsDelta0.conj hPrefix hPointwise)

 /-- 规范全称前缀轨迹去掉首个序列成员 guard 后的公式体。 -/
def canonical_forall_prefix_trace_body
    (binderCount core code trace : SetTerm)
    (indexId : FreeVarId) : SetFormula :=
  (domₘ(trace) ≐ₘ Sₘ(binderCount)) ∧ₘ
    (((trace ·ₘ numₘ(0)) ≐ₘ code) ∧ₘ
      ((∀ₘ[SetSort.set, indexId],
          (x#indexId ∈ₘ binderCount) ⟶ₘ
            canonical_forall_prefix_step_condition
              trace (x#indexId)) ∧ₘ
        ((trace ·ₘ binderCount) ≐ₘ core)))

/-- 规范全称前缀轨迹去掉首个序列成员 guard 后的 `Delta0` 证书。 -/
theorem canonical_forall_prefix_trace_body_delta0
    (binderCount core code trace : SetTerm)
    (indexId : FreeVarId)
    (hIndexFresh :
      (SetSort.set, indexId) ∉
        Term.freeSupport binderCount) :
    Formula.IsDelta0 set_levy_bound
      (canonical_forall_prefix_trace_body
        binderCount core code trace indexId) := by
  have hDomain :
      Formula.IsDelta0 set_levy_bound
        (domₘ(trace) ≐ₘ Sₘ(binderCount)) :=
    Formula.IsDelta0.equal
      (domₘ(trace)) (Sₘ(binderCount))
  have hHead :
      Formula.IsDelta0 set_levy_bound
        ((trace ·ₘ numₘ(0)) ≐ₘ code) :=
    Formula.IsDelta0.equal
      (trace ·ₘ numₘ(0)) code
  let steps : SetFormula :=
    ∀ₘ[SetSort.set, indexId],
      (x#indexId ∈ₘ binderCount) ⟶ₘ
        canonical_forall_prefix_step_condition
          trace (x#indexId)
  have hSteps :
      Formula.IsDelta0 set_levy_bound steps := by
    simpa [steps] using
      Formula.IsDelta0.bounded_forall_closeFreeAt
        indexId binderCount hIndexFresh
        (canonical_forall_prefix_step_condition_delta0
          trace (x#indexId))
  have hTail :
      Formula.IsDelta0 set_levy_bound
        (steps ∧ₘ
          ((trace ·ₘ binderCount) ≐ₘ core)) :=
    Formula.IsDelta0.conj hSteps
      (Formula.IsDelta0.equal
        (trace ·ₘ binderCount) core)
  have hRight :
      Formula.IsDelta0 set_levy_bound
        (((trace ·ₘ numₘ(0)) ≐ₘ code) ∧ₘ
          (steps ∧ₘ
            ((trace ·ₘ binderCount) ≐ₘ core))) :=
    Formula.IsDelta0.conj hHead hTail
  simpa [canonical_forall_prefix_trace_body, steps] using
    Formula.IsDelta0.conj hDomain hRight

/-- 规范全称前缀轨迹条件的 `Delta0` 证书。 -/
theorem canonical_forall_prefix_trace_condition_delta0
    (binderCount core code trace : SetTerm)
    (indexId : FreeVarId)
    (hIndexFresh :
      (SetSort.set, indexId) ∉
        Term.freeSupport binderCount) :
    Formula.IsDelta0 set_levy_bound
      (canonical_forall_prefix_trace_condition
        binderCount core code trace indexId) := by
  have hTraceSpace :
      Formula.IsDelta0 set_levy_bound
        (trace ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) :=
    Formula.IsDelta0.rel
      RelationSymbol.membership
      [trace, seq₊_spaceₘ(FormulaCodeₘ)]
  have hDomain :
      Formula.IsDelta0 set_levy_bound
        (domₘ(trace) ≐ₘ Sₘ(binderCount)) :=
    Formula.IsDelta0.equal
      (domₘ(trace)) (Sₘ(binderCount))
  have hHead :
      Formula.IsDelta0 set_levy_bound
        ((trace ·ₘ numₘ(0)) ≐ₘ code) :=
    Formula.IsDelta0.equal
      (trace ·ₘ numₘ(0)) code
  let steps : SetFormula :=
    ∀ₘ[SetSort.set, indexId],
      (x#indexId ∈ₘ binderCount) ⟶ₘ
        canonical_forall_prefix_step_condition
          trace (x#indexId)
  have hSteps :
      Formula.IsDelta0 set_levy_bound steps := by
    simpa [steps] using
      Formula.IsDelta0.bounded_forall_closeFreeAt
        indexId binderCount hIndexFresh
        (canonical_forall_prefix_step_condition_delta0
          trace (x#indexId))
  have hTail :
      Formula.IsDelta0 set_levy_bound
        (steps ∧ₘ
          ((trace ·ₘ binderCount) ≐ₘ core)) :=
    Formula.IsDelta0.conj hSteps
      (Formula.IsDelta0.equal
        (trace ·ₘ binderCount) core)
  have hRight :
      Formula.IsDelta0 set_levy_bound
        (((trace ·ₘ numₘ(0)) ≐ₘ code) ∧ₘ
          (steps ∧ₘ
            ((trace ·ₘ binderCount) ≐ₘ core))) :=
    Formula.IsDelta0.conj hHead hTail
  simpa [canonical_forall_prefix_trace_condition] using
    Formula.IsDelta0.conj
      (Formula.IsDelta0.conj hTraceSpace
        hDomain)
      hRight

/-- 规范全称前缀码条件的 `Delta0` 证书。 -/
theorem canonical_forall_prefix_code_condition_with_ids_delta0
    (binderCount core code : SetTerm)
    (traceId indexId : FreeVarId)
    (hIndexFresh :
      (SetSort.set, indexId) ∉
        Term.freeSupport binderCount) :
    Formula.IsDelta0 set_levy_bound
      (canonical_forall_prefix_code_condition_with_ids
        binderCount core code traceId indexId) := by
  have hTrace :
      Formula.IsDelta0 set_levy_bound
        (canonical_forall_prefix_trace_condition
          binderCount core code (x#traceId) indexId) :=
    canonical_forall_prefix_trace_condition_delta0
      binderCount core code (x#traceId) indexId hIndexFresh
  have hBody :
      Formula.IsDelta0 set_levy_bound
        (canonical_forall_prefix_trace_body
          binderCount core code (x#traceId) indexId) :=
    canonical_forall_prefix_trace_body_delta0
      binderCount core code (x#traceId) indexId hIndexFresh
  have hWitness :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, traceId],
          canonical_forall_prefix_trace_condition
            binderCount core code (x#traceId) indexId) := by
    simpa [canonical_forall_prefix_trace_condition,
      canonical_forall_prefix_trace_body] using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        traceId (seq₊_spaceₘ(FormulaCodeₘ))
        (by simp [Term.freeSupport, Term.freeSupportList])
        hTrace
        (Formula.FreeMembershipGuard.conj_left
          (Formula.FreeMembershipGuard.conj_left
            Formula.FreeMembershipGuard.membership))
  have hPrefix :
      Formula.IsDelta0 set_levy_bound
        (((binderCount ∈ₘ ωₘ) ∧ₘ
          formula_codeₘ(core)) ∧ₘ
          formula_codeₘ(code)) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.rel
          RelationSymbol.membership [binderCount, ωₘ])
        (Formula.IsDelta0.rel
          RelationSymbol.isFormulaCode [core]))
      (Formula.IsDelta0.rel
        RelationSymbol.isFormulaCode [code])
  simpa [canonical_forall_prefix_code_condition_with_ids] using
    Formula.IsDelta0.conj hPrefix hWitness

/-! ## 编码级替换规格 -/

theorem substitution_piece_condition_delta0
    (source boundVariable replacement pieces index : SetTerm) :
    Formula.IsDelta0 set_levy_bound
      (substitution_piece_condition
        source boundVariable replacement pieces index) := by
  have hIndex :
      Formula.IsDelta0 set_levy_bound
        (index ∈ₘ domₘ(source)) :=
    Formula.IsDelta0.rel
      RelationSymbol.membership [index, domₘ(source)]
  have hMatch :
      Formula.IsDelta0 set_levy_bound
        (((source ·ₘ index) ≐ₘ
            (boundVariable ·ₘ numₘ(0))) ∧ₘ
          ((pieces ·ₘ index) ≐ₘ replacement)) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.equal
        (source ·ₘ index)
        (boundVariable ·ₘ numₘ(0)))
      (Formula.IsDelta0.equal
        (pieces ·ₘ index) replacement)
  have hOther :
      Formula.IsDelta0 set_levy_bound
        (((source ·ₘ index) ≠ₘ
            (boundVariable ·ₘ numₘ(0))) ∧ₘ
          ((pieces ·ₘ index) ≐ₘ
            sym_codeₘ(source ·ₘ index))) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.neg
        (Formula.IsDelta0.equal
          (source ·ₘ index)
          (boundVariable ·ₘ numₘ(0))))
      (Formula.IsDelta0.equal
        (pieces ·ₘ index)
        (sym_codeₘ(source ·ₘ index)))
  simpa [substitution_piece_condition] using
    Formula.IsDelta0.imp hIndex
      (Formula.IsDelta0.disj hMatch hOther)

theorem code_substitution_spec_delta0
    (source boundVariable replacement candidate : SetTerm)
    (hIndexFresh :
      (SetSort.set, 311) ∉
        Term.freeSupport (domₘ(source))) :
    Formula.IsDelta0 set_levy_bound
      (code_substitution_spec
        source boundVariable replacement candidate) := by
  have hPointBody :
      Formula.IsDelta0 set_levy_bound
        (((source ·ₘ x#311) ≐ₘ
            (boundVariable ·ₘ numₘ(0))) ∧ₘ
          ((x#310 ·ₘ x#311) ≐ₘ replacement) ∨ₘ
          (((source ·ₘ x#311) ≠ₘ
              (boundVariable ·ₘ numₘ(0))) ∧ₘ
            ((x#310 ·ₘ x#311) ≐ₘ
              sym_codeₘ(source ·ₘ x#311)))) :=
    Formula.IsDelta0.disj
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.equal
          (source ·ₘ x#311)
          (boundVariable ·ₘ numₘ(0)))
        (Formula.IsDelta0.equal
          (x#310 ·ₘ x#311) replacement))
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.neg
          (Formula.IsDelta0.equal
            (source ·ₘ x#311)
            (boundVariable ·ₘ numₘ(0))))
        (Formula.IsDelta0.equal
          (x#310 ·ₘ x#311)
          (sym_codeₘ(source ·ₘ x#311))))
  let indexForall : SetFormula :=
    ∀ₘ[SetSort.set, 311],
      substitution_piece_condition
        source boundVariable replacement
        (x#310) (x#311)
  have hIndexForall :
      Formula.IsDelta0 set_levy_bound
        indexForall := by
    simpa [indexForall, substitution_piece_condition] using
      Formula.IsDelta0.bounded_forall_closeFreeAt
        311 (domₘ(source)) hIndexFresh hPointBody
  have hPiecesSpace :
      Formula.IsDelta0 set_levy_bound
        (x#310 ∈ₘ seq_spaceₘ(CodeStrₘ)) :=
    Formula.IsDelta0.rel
      RelationSymbol.membership
      [x#310, seq_spaceₘ(CodeStrₘ)]
  have hPiecesDomain :
      Formula.IsDelta0 set_levy_bound
        (domₘ(x#310) ≐ₘ domₘ(source)) :=
    Formula.IsDelta0.equal
      (domₘ(x#310)) (domₘ(source))
  have hFlatten :
      Formula.IsDelta0 set_levy_bound
        (candidate ≐ₘ flattenₘ(x#310)) :=
    Formula.IsDelta0.equal
      candidate (flattenₘ(x#310))
  let piecesBody : SetFormula :=
    (((x#310 ∈ₘ seq_spaceₘ(CodeStrₘ)) ∧ₘ
        (domₘ(x#310) ≐ₘ domₘ(source))) ∧ₘ
      (indexForall ∧ₘ
        (candidate ≐ₘ flattenₘ(x#310))))
  have hPiecesBody :
      Formula.IsDelta0 set_levy_bound
        piecesBody := by
    simpa [piecesBody] using
      Formula.IsDelta0.conj
        (Formula.IsDelta0.conj hPiecesSpace hPiecesDomain)
        (Formula.IsDelta0.conj hIndexForall hFlatten)
  have hPieces :
      Formula.IsDelta0 set_levy_bound
        (∃ₘ[SetSort.set, 310],
          piecesBody) := by
    simpa using
      Formula.IsDelta0.guarded_exists_closeFreeAt
        310 (seq_spaceₘ(CodeStrₘ))
        (by simp [Term.freeSupport, Term.freeSupportList])
        hPiecesBody
        (Formula.FreeMembershipGuard.conj_left
          (Formula.FreeMembershipGuard.conj_left
            Formula.FreeMembershipGuard.membership))
  have hCandidate :
      Formula.IsDelta0 set_levy_bound
        (candidate ∈ₘ CodeStrₘ) :=
    Formula.IsDelta0.rel
      RelationSymbol.membership [candidate, CodeStrₘ]
  simpa [code_substitution_spec, piecesBody, indexForall] using
    Formula.IsDelta0.conj hCandidate hPieces

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
