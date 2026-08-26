import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCanonicalBinderShiftInversion.Unique

/-!
# 规范 binder-shift 单 token 条件的最终组装

本模块只展开对象条件的六个分支，并调用已经闭合的分支唯一性定理。
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

theorem fs_zfc_support_raw_canonical_binder_shift_token_unique
    {Γ : Context signature}
    {sourceToken targetToken : Nat}
    (relation :
      CanonicalBinderShiftToken sourceToken targetToken)
    (sourceValue targetValue : SetTerm)
    (freshBase : FreeVarId)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hTargetValue :
      Term.Admissible targetValue SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hSourceFresh :
      ∀ id, freshBase ≤ id → id ≤ freshBase + 6 →
        (SetSort.set, id) ∉
          Term.freeSupport sourceValue)
    (hTargetFresh :
      ∀ id, freshBase ≤ id → id ≤ freshBase + 6 →
        (SetSort.set, id) ∉
          Term.freeSupport targetValue)
    (hContextFresh :
      ∀ formula, formula ∈ Γ → ∀ id,
        freshBase ≤ id → id ≤ freshBase + 6 →
        (SetSort.set, id) ∉
          Formula.freeSupport formula)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_shift_token_condition_with_ids
          sourceValue targetValue
          freshBase (freshBase + 1) (freshBase + 2)
          (freshBase + 3) (freshBase + 4)
          (freshBase + 5) (freshBase + 6)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ numₘ(targetToken) := by
  let freeId := freshBase
  let boundId := freshBase + 1
  let constantId := freshBase + 2
  let functionArityId := freshBase + 3
  let functionIndexId := freshBase + 4
  let predicateArityId := freshBase + 5
  let predicateIndexId := freshBase + 6
  let freeBody : SetFormula :=
    ((((x#freeId ∈ₘ ωₘ) ∧ₘ
          (x#freeId ∈ₘ Sₘ(sourceValue))) ∧ₘ
        (sourceValue ≐ₘ
          variable_symbol_number_term
            (numₘ(2) *ₘ x#freeId))) ∧ₘ
      (targetValue ≐ₘ sourceValue))
  let freeCase : SetFormula :=
    ∃ₘ[SetSort.set, freeId], freeBody
  let boundBody : SetFormula :=
    ((((x#boundId ∈ₘ ωₘ) ∧ₘ
          (x#boundId ∈ₘ Sₘ(sourceValue))) ∧ₘ
        (sourceValue ≐ₘ
          variable_symbol_number_term
            (Sₘ(numₘ(2) *ₘ x#boundId)))) ∧ₘ
      (targetValue ≐ₘ
        variable_symbol_number_term
          (Sₘ(Sₘ(Sₘ(
            numₘ(2) *ₘ x#boundId))))))
  let boundCase : SetFormula :=
    ∃ₘ[SetSort.set, boundId], boundBody
  let constantBody : SetFormula :=
    (((x#constantId ∈ₘ ωₘ) ∧ₘ
        (sourceValue ≐ₘ
          constant_symbol_number_term
            (x#constantId))) ∧ₘ
      (targetValue ≐ₘ sourceValue))
  let constantCase : SetFormula :=
    ∃ₘ[SetSort.set, constantId], constantBody
  let functionBody : SetFormula :=
    ((((x#functionArityId ∈ₘ ωₘ) ∧ₘ
          (x#functionIndexId ∈ₘ ωₘ)) ∧ₘ
        (sourceValue ≐ₘ
          coded_function_symbol_number_term
            (x#functionArityId)
            (x#functionIndexId))) ∧ₘ
      (targetValue ≐ₘ sourceValue))
  let functionInner : SetFormula :=
    ∃ₘ[SetSort.set, functionIndexId], functionBody
  let functionCase : SetFormula :=
    ∃ₘ[SetSort.set, functionArityId], functionInner
  let predicateBody : SetFormula :=
    ((((x#predicateArityId ∈ₘ ωₘ) ∧ₘ
          (x#predicateIndexId ∈ₘ ωₘ)) ∧ₘ
        (sourceValue ≐ₘ
          coded_predicate_symbol_number_term
            (x#predicateArityId)
            (x#predicateIndexId))) ∧ₘ
      (targetValue ≐ₘ sourceValue))
  let predicateInner : SetFormula :=
    ∃ₘ[SetSort.set, predicateIndexId], predicateBody
  let predicateCase : SetFormula :=
    ∃ₘ[SetSort.set, predicateArityId], predicateInner
  let fixedCase : SetFormula :=
    canonical_binder_shift_fixed_token_condition
        sourceValue ∧ₘ
      (targetValue ≐ₘ sourceValue)
  have hCases :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        fixedCase ∨ₘ
          (freeCase ∨ₘ
            (boundCase ∨ₘ
              (constantCase ∨ₘ
                (functionCase ∨ₘ predicateCase)))) := by
    simpa [fixedCase, freeCase, freeBody,
      boundCase, boundBody, constantCase, constantBody,
      functionCase, functionInner, functionBody,
      predicateCase, predicateInner, predicateBody,
      freeId, boundId, constantId,
      functionArityId, functionIndexId,
      predicateArityId, predicateIndexId,
      canonical_binder_shift_token_condition_with_ids] using
      hCondition
  have hConsFresh
      (branch : SetFormula)
      (id : FreeVarId)
      (hBranch :
        (SetSort.set, id) ∉
          Formula.freeSupport branch)
      (hLower : freshBase ≤ id)
      (hUpper : id ≤ freshBase + 6) :
      ∀ formula, formula ∈ branch :: Γ →
        (SetSort.set, id) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    simp only [List.mem_cons] at hFormula
    rcases hFormula with rfl | hFormula
    · exact hBranch
    · exact hContextFresh formula hFormula id hLower hUpper
  have hFixedProof :
      fixedCase :: Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ numₘ(targetToken) := by
    apply fs_zfc_support_raw_canonical_binder_fixed_case_unique
      relation sourceValue targetValue
      hSourceValue hTargetValue
      (FirstOrder.Derives.context_weaken_cons
        hSourceEquality)
    simpa [fixedCase] using
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := fixedCase :: Γ)
        (φ := fixedCase)
        (by simp))
  have hFreeOwnFresh :
      (SetSort.set, freeId) ∉
        Formula.freeSupport freeCase := by
    simpa [freeCase] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set freeId 0 freeBody
  have hFreeProof :
      freeCase :: Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ numₘ(targetToken) := by
    apply fs_zfc_support_raw_canonical_binder_free_case_unique
      relation sourceValue targetValue freeId
      hSourceValue hTargetValue
      (FirstOrder.Derives.context_weaken_cons
        hSourceEquality)
      (hSourceFresh freeId (by simp [freeId])
        (by simp [freeId]))
      (hTargetFresh freeId (by simp [freeId])
        (by simp [freeId]))
      (hConsFresh freeCase freeId hFreeOwnFresh
        (by simp [freeId]) (by simp [freeId]))
    simpa [freeCase, freeBody] using
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := freeCase :: Γ)
        (φ := freeCase)
        (by simp))
  have hBoundOwnFresh :
      (SetSort.set, boundId) ∉
        Formula.freeSupport boundCase := by
    simpa [boundCase] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set boundId 0 boundBody
  have hBoundProof :
      boundCase :: Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ numₘ(targetToken) := by
    apply fs_zfc_support_raw_canonical_binder_bound_case_unique
      relation sourceValue targetValue boundId
      hSourceValue hTargetValue
      (FirstOrder.Derives.context_weaken_cons
        hSourceEquality)
      (hTargetFresh boundId (by simp [boundId])
        (by simp [boundId]))
      (hConsFresh boundCase boundId hBoundOwnFresh
        (by simp [boundId]) (by simp [boundId]))
    simpa [boundCase, boundBody,
      canonical_binder_bound_name_term,
      canonical_binder_shifted_bound_name_term] using
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := boundCase :: Γ)
        (φ := boundCase)
        (by simp))
  have hConstantOwnFresh :
      (SetSort.set, constantId) ∉
        Formula.freeSupport constantCase := by
    simpa [constantCase] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set constantId 0 constantBody
  have hConstantProof :
      constantCase :: Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ numₘ(targetToken) := by
    apply fs_zfc_support_raw_canonical_binder_constant_case_unique
      relation sourceValue targetValue constantId
      hSourceValue hTargetValue
      (FirstOrder.Derives.context_weaken_cons
        hSourceEquality)
      (hSourceFresh constantId (by simp [constantId])
        (by simp [constantId]))
      (hTargetFresh constantId (by simp [constantId])
        (by simp [constantId]))
      (hConsFresh constantCase constantId
        hConstantOwnFresh (by simp [constantId])
        (by simp [constantId]))
    simpa [constantCase, constantBody] using
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := constantCase :: Γ)
        (φ := constantCase)
        (by simp))
  have hFunctionArityOwnFresh :
      (SetSort.set, functionArityId) ∉
        Formula.freeSupport functionCase := by
    simpa [functionCase] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set functionArityId 0 functionInner
  have hFunctionIndexInnerFresh :
      (SetSort.set, functionIndexId) ∉
        Formula.freeSupport functionInner := by
    simpa [functionInner] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set functionIndexId 0 functionBody
  have hFunctionIndexOwnFresh :
      (SetSort.set, functionIndexId) ∉
        Formula.freeSupport functionCase := by
    simpa [functionCase] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, functionIndexId)
        SetSort.set functionArityId 0
        functionInner hFunctionIndexInnerFresh
  have hFunctionProof :
      functionCase :: Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ numₘ(targetToken) := by
    apply fs_zfc_support_raw_canonical_binder_function_case_unique
      relation sourceValue targetValue
      functionArityId functionIndexId
      hSourceValue hTargetValue
      (FirstOrder.Derives.context_weaken_cons
        hSourceEquality)
      (hSourceFresh functionArityId
        (by simp [functionArityId])
        (by simp [functionArityId]))
      (hTargetFresh functionArityId
        (by simp [functionArityId])
        (by simp [functionArityId]))
      (hSourceFresh functionIndexId
        (by simp [functionIndexId])
        (by simp [functionIndexId]))
      (hTargetFresh functionIndexId
        (by simp [functionIndexId])
        (by simp [functionIndexId]))
      (hConsFresh functionCase functionArityId
        hFunctionArityOwnFresh
        (by simp [functionArityId])
        (by simp [functionArityId]))
      (hConsFresh functionCase functionIndexId
        hFunctionIndexOwnFresh
        (by simp [functionIndexId])
        (by simp [functionIndexId]))
    simpa [functionCase, functionInner, functionBody] using
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := functionCase :: Γ)
        (φ := functionCase)
        (by simp))
  have hPredicateArityOwnFresh :
      (SetSort.set, predicateArityId) ∉
        Formula.freeSupport predicateCase := by
    simpa [predicateCase] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set predicateArityId 0 predicateInner
  have hPredicateIndexInnerFresh :
      (SetSort.set, predicateIndexId) ∉
        Formula.freeSupport predicateInner := by
    simpa [predicateInner] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set predicateIndexId 0 predicateBody
  have hPredicateIndexOwnFresh :
      (SetSort.set, predicateIndexId) ∉
        Formula.freeSupport predicateCase := by
    simpa [predicateCase] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, predicateIndexId)
        SetSort.set predicateArityId 0
        predicateInner hPredicateIndexInnerFresh
  have hPredicateProof :
      predicateCase :: Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ numₘ(targetToken) := by
    apply fs_zfc_support_raw_canonical_binder_predicate_case_unique
      relation sourceValue targetValue
      predicateArityId predicateIndexId
      hSourceValue hTargetValue
      (FirstOrder.Derives.context_weaken_cons
        hSourceEquality)
      (hSourceFresh predicateArityId
        (by simp [predicateArityId])
        (by simp [predicateArityId]))
      (hTargetFresh predicateArityId
        (by simp [predicateArityId])
        (by simp [predicateArityId]))
      (hSourceFresh predicateIndexId
        (by simp [predicateIndexId])
        (by simp [predicateIndexId]))
      (hTargetFresh predicateIndexId
        (by simp [predicateIndexId])
        (by simp [predicateIndexId]))
      (hConsFresh predicateCase predicateArityId
        hPredicateArityOwnFresh
        (by simp [predicateArityId])
        (by simp [predicateArityId]))
      (hConsFresh predicateCase predicateIndexId
        hPredicateIndexOwnFresh
        (by simp [predicateIndexId])
        (by simp [predicateIndexId]))
    simpa [predicateCase, predicateInner, predicateBody] using
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := predicateCase :: Γ)
        (φ := predicateCase)
        (by simp))
  have hInsertTails
      (branch : SetFormula)
      (tails : Context signature)
      (hBranch :
        branch :: Γ ⊢ₘ[fs_zfc_support_raw_theory]
          targetValue ≐ₘ numₘ(targetToken)) :
      branch :: tails ++ Γ
        ⊢ₘ[fs_zfc_support_raw_theory]
          targetValue ≐ₘ numₘ(targetToken) := by
    apply FirstOrder.Derives.context_weaken
      (Γ := branch :: Γ)
      (Δ := branch :: tails ++ Γ)
    · intro formula hFormula
      simp only [List.mem_cons] at hFormula
      rcases hFormula with rfl | hFormula
      · simp
      · simp [hFormula]
    · exact hBranch
  let tail₅ : SetFormula :=
    functionCase ∨ₘ predicateCase
  let tail₄ : SetFormula :=
    constantCase ∨ₘ tail₅
  let tail₃ : SetFormula :=
    boundCase ∨ₘ tail₄
  let tail₂ : SetFormula :=
    freeCase ∨ₘ tail₃
  apply FirstOrder.Derives.disjElim hCases
  · exact hFixedProof
  · have hTail₂ :
        tail₂ :: Γ ⊢ₘ[fs_zfc_support_raw_theory]
          tail₂ :=
      FirstOrder.Derives.assumption (by simp)
    apply FirstOrder.Derives.disjElim hTail₂
    · simpa [tail₂] using
        hInsertTails freeCase [tail₂] hFreeProof
    · have hTail₃ :
          tail₃ :: tail₂ :: Γ
            ⊢ₘ[fs_zfc_support_raw_theory]
              tail₃ :=
        FirstOrder.Derives.assumption (by simp)
      apply FirstOrder.Derives.disjElim hTail₃
      · simpa [tail₂, tail₃] using
          hInsertTails boundCase [tail₃, tail₂]
            hBoundProof
      · have hTail₄ :
            tail₄ :: tail₃ :: tail₂ :: Γ
              ⊢ₘ[fs_zfc_support_raw_theory]
                tail₄ :=
          FirstOrder.Derives.assumption (by simp)
        apply FirstOrder.Derives.disjElim hTail₄
        · simpa [tail₂, tail₃, tail₄] using
            hInsertTails constantCase
              [tail₄, tail₃, tail₂] hConstantProof
        · have hTail₅ :
              tail₅ :: tail₄ :: tail₃ :: tail₂ :: Γ
                ⊢ₘ[fs_zfc_support_raw_theory]
                  tail₅ :=
            FirstOrder.Derives.assumption (by simp)
          apply FirstOrder.Derives.disjElim hTail₅
          · simpa [tail₂, tail₃, tail₄, tail₅] using
              hInsertTails functionCase
                [tail₅, tail₄, tail₃, tail₂]
                hFunctionProof
          · simpa [tail₂, tail₃, tail₄, tail₅] using
              hInsertTails predicateCase
                [tail₅, tail₄, tail₃, tail₂]
                hPredicateProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
