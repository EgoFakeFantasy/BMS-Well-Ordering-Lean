import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalAxiomReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCBaseLogicalReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Occurrence

/-!
# ZFC 恒等律逻辑公理的对象层回放

本模块只补齐恒等律 `x = x` 的基础模式回放。它复用公共 Gödel quotation
边界和逻辑公理码生成入口，不引入新的 proof predicate 或额外对象层假设。
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

theorem fs_zfc_support_raw_variable_symbol_occurs_iff_of_code_equality
    (boundVariable left right : SetTerm)
    (hBoundVariable : Term.Admissible boundVariable SetSort.set)
    (hLeft : GodelQuotation.Numbered.CodeBoundary left)
    (hRight : GodelQuotation.Numbered.CodeBoundary right)
    (hBoundFresh312 :
      (SetSort.set, 312) ∉ Term.freeSupport boundVariable)
    (hBoundFresh490 :
      (SetSort.set, 490) ∉ Term.freeSupport boundVariable)
    (hEquality :
      Derives fs_zfc_support_raw_theory [] (left ≐ₘ right)) :
    Derives fs_zfc_support_raw_theory [] (
      variable_symbol_occurs_condition boundVariable left ↔ₘ
        variable_symbol_occurs_condition boundVariable right) := by
  let body : SetFormula :=
    variable_symbol_occurs_condition boundVariable (x#490)
  have hBodyAdmissible :
      Formula.Admissible body := by
    simpa [body] using
      variable_symbol_occurs_condition_admissible
        boundVariable (x#490)
        hBoundVariable (set_variable_admissible 490)
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality
      (T := fs_zfc_support_raw_theory) (Γ := [])
      (sort := SetSort.set) (eigen := 490)
      (left := left) (right := right) (body := body)
      hEquality
  have hBoundVariableFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set 490 replacement boundVariable =
        boundVariable :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 490 replacement boundVariable hBoundFresh490
  have hBoundVariableClose :
      Term.closeFreeAt SetSort.set 312 0 boundVariable =
        boundVariable :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 312 0 boundVariable
      hBoundVariable.2 hBoundFresh312
  have hLeftClose :
      Term.closeFreeAt SetSort.set 312 0 left = left :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 312 0 left hLeft.1.2 (by
        rw [hLeft.2]
        exact List.not_mem_nil)
  have hRightClose :
      Term.closeFreeAt SetSort.set 312 0 right = right :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 312 0 right hRight.1.2 (by
        rw [hRight.2]
        exact List.not_mem_nil)
  have hNumeralClose :
      Term.closeFreeAt SetSort.set 312 0 (numₘ(0)) =
        numₘ(0) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 312 0 (numₘ(0))
      (finite_numeral_term_admissible 0).2 (by
        simp [finite_numeral_term_freeSupport])
  have hNumeralSubstitute (replacement : SetTerm) :
      Term.substituteFree SetSort.set 490 replacement (numₘ(0)) =
        numₘ(0) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 490 replacement (numₘ(0)) (by
        simp [finite_numeral_term_freeSupport])
  have hVariableFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set 490 replacement (x#490) =
        replacement := by
    simp [Term.substituteFree, set_variable]
  simpa [body, variable_symbol_occurs_condition,
    Formula.substituteFree,
    Formula.closeFreeAt, Formula.next_depth,
    Term.substituteFree, set_variable,
    Term.closeFreeAt,
    hBoundVariableFixed, hVariableFixed,
    hBoundVariableClose, hLeftClose, hRightClose,
    hNumeralClose, hNumeralSubstitute] using hCongruence

theorem fs_zfc_support_raw_quantifier_body_iff_of_code_equality
    (boundVariable left right position : SetTerm)
    (hBoundVariable : Term.Admissible boundVariable SetSort.set)
    (hLeft : GodelQuotation.Numbered.CodeBoundary left)
    (hRight : GodelQuotation.Numbered.CodeBoundary right)
    (hPosition : Term.Admissible position SetSort.set)
    (hBoundFresh320 :
      (SetSort.set, 320) ∉ Term.freeSupport boundVariable)
    (hBoundFresh325 :
      (SetSort.set, 325) ∉ Term.freeSupport boundVariable)
    (hBoundFresh326 :
      (SetSort.set, 326) ∉ Term.freeSupport boundVariable)
    (hBoundFresh327 :
      (SetSort.set, 327) ∉ Term.freeSupport boundVariable)
    (hPositionFresh320 :
      (SetSort.set, 320) ∉ Term.freeSupport position)
    (hPositionFresh325 :
      (SetSort.set, 325) ∉ Term.freeSupport position)
    (hPositionFresh326 :
      (SetSort.set, 326) ∉ Term.freeSupport position)
    (hPositionFresh327 :
      (SetSort.set, 327) ∉ Term.freeSupport position)
    (hBoundFresh491 :
      (SetSort.set, 491) ∉ Term.freeSupport boundVariable)
    (hPositionFresh491 :
      (SetSort.set, 491) ∉ Term.freeSupport position)
    (hEquality :
      Derives fs_zfc_support_raw_theory [] (left ≐ₘ right)) :
    Derives fs_zfc_support_raw_theory [] (
      quantifier_body_position_condition boundVariable left position ↔ₘ
        quantifier_body_position_condition boundVariable right position) := by
  let body : SetFormula :=
    quantifier_body_position_condition boundVariable (x#491) position
  have hBodyAdmissible :
      Formula.Admissible body := by
    simpa [body] using
      quantifier_body_position_condition_admissible
        boundVariable (x#491) position
        hBoundVariable (set_variable_admissible 491) hPosition
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality
      (T := fs_zfc_support_raw_theory) (Γ := [])
      (sort := SetSort.set) (eigen := 491)
      (left := left) (right := right) (body := body)
      hEquality
  have hBoundFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set 491 replacement boundVariable =
        boundVariable :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 491 replacement boundVariable hBoundFresh491
  have hPositionFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set 491 replacement position =
        position :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 491 replacement position hPositionFresh491
  have hVariableFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set 491 replacement (x#491) =
        replacement := by
    simp [Term.substituteFree, set_variable]
  have hBoundClose320 (depth : Nat) :
      Term.closeFreeAt SetSort.set 320 depth boundVariable =
        boundVariable :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 320 depth boundVariable
      hBoundVariable.2 hBoundFresh320
  have hBoundClose325 (depth : Nat) :
      Term.closeFreeAt SetSort.set 325 depth boundVariable =
        boundVariable :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 325 depth boundVariable
      hBoundVariable.2 hBoundFresh325
  have hBoundClose326 (depth : Nat) :
      Term.closeFreeAt SetSort.set 326 depth boundVariable =
        boundVariable :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 326 depth boundVariable
      hBoundVariable.2 hBoundFresh326
  have hBoundClose327 (depth : Nat) :
      Term.closeFreeAt SetSort.set 327 depth boundVariable =
        boundVariable :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 327 depth boundVariable
      hBoundVariable.2 hBoundFresh327
  have hPositionClose320 (depth : Nat) :
      Term.closeFreeAt SetSort.set 320 depth position =
        position :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 320 depth position
      hPosition.2 hPositionFresh320
  have hPositionClose325 (depth : Nat) :
      Term.closeFreeAt SetSort.set 325 depth position =
        position :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 325 depth position
      hPosition.2 hPositionFresh325
  have hPositionClose326 (depth : Nat) :
      Term.closeFreeAt SetSort.set 326 depth position =
        position :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 326 depth position
      hPosition.2 hPositionFresh326
  have hPositionClose327 (depth : Nat) :
      Term.closeFreeAt SetSort.set 327 depth position =
        position :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 327 depth position
      hPosition.2 hPositionFresh327
  have hLeftClose (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth left = left :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth left hLeft.1.2 (by
        rw [hLeft.2]
        exact List.not_mem_nil)
  have hRightClose (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth right = right :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth right hRight.1.2 (by
        rw [hRight.2]
        exact List.not_mem_nil)
  have hNumeralSubstitute (replacement : SetTerm) (value : Nat) :
      Term.substituteFree SetSort.set 491 replacement (numₘ(value)) =
        numₘ(value) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 491 replacement (numₘ(value)) (by
        simp [finite_numeral_term_freeSupport])
  have hNumeralClose (id depth value : Nat) :
      Term.closeFreeAt SetSort.set id depth (numₘ(value)) =
        numₘ(value) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth (numₘ(value))
      (finite_numeral_term_admissible value).2 (by
        simp [finite_numeral_term_freeSupport])
  simpa [body, quantifier_body_position_condition,
    universal_binder_at_condition, code_substring_at_condition,
    Formula.substituteFree, Formula.closeFreeAt,
    Formula.next_depth, Term.substituteFree,
    Term.closeFreeAt, set_variable, set_bound_variable,
    hBoundFixed, hPositionFixed, hVariableFixed,
    hBoundClose320, hBoundClose325, hBoundClose326, hBoundClose327,
    hPositionClose320, hPositionClose325, hPositionClose326,
    hPositionClose327,
    hLeftClose, hRightClose,
    hNumeralSubstitute,
    hNumeralClose,
    finite_numeral_term_freeSupport] using hCongruence

theorem fs_zfc_support_raw_no_capture_of_separation
    (boundVariable leftFormula rightFormula leftReplacement rightReplacement position : SetTerm)
    (hBoundVariable : Term.Admissible boundVariable SetSort.set)
    (hLeftFormula : GodelQuotation.Numbered.CodeBoundary leftFormula)
    (hRightFormula : GodelQuotation.Numbered.CodeBoundary rightFormula)
    (hLeftReplacement : GodelQuotation.Numbered.CodeBoundary leftReplacement)
    (hRightReplacement : GodelQuotation.Numbered.CodeBoundary rightReplacement)
    (hPosition : Term.Admissible position SetSort.set)
    (hBoundFresh325 :
      (SetSort.set, 325) ∉ Term.freeSupport boundVariable)
    (hBoundFresh326 :
      (SetSort.set, 326) ∉ Term.freeSupport boundVariable)
    (hBoundFresh327 :
      (SetSort.set, 327) ∉ Term.freeSupport boundVariable)
    (hOccurrenceEquality :
      Derives fs_zfc_support_raw_theory [] (
        variable_symbol_occurs_condition boundVariable leftReplacement ↔ₘ
          variable_symbol_occurs_condition boundVariable rightReplacement))
    (hQuantifierBodyEquality :
      Derives fs_zfc_support_raw_theory [] (
        quantifier_body_position_condition boundVariable leftFormula position ↔ₘ
          quantifier_body_position_condition boundVariable rightFormula position))
    (hSeparation :
      Derives fs_zfc_support_raw_theory [] (
        universal_binder_at_condition boundVariable rightFormula
            (x#325) (x#326) ⟶ₘ
          ¬ₘ variable_symbol_occurs_condition
            boundVariable rightReplacement)) :
    Derives fs_zfc_support_raw_theory [] (
      variable_symbol_occurs_condition boundVariable leftReplacement ⟶ₘ
        ¬ₘ quantifier_body_position_condition
          boundVariable leftFormula position) := by
  let occurrenceLeft : SetFormula :=
    variable_symbol_occurs_condition boundVariable leftReplacement
  let occurrenceRight : SetFormula :=
    variable_symbol_occurs_condition boundVariable rightReplacement
  let bodyLeft : SetFormula :=
    quantifier_body_position_condition boundVariable leftFormula position
  let bodyRight : SetFormula :=
    quantifier_body_position_condition boundVariable rightFormula position
  have hOccurrenceLeftAdmissible :
      Formula.Admissible occurrenceLeft := by
    simpa [occurrenceLeft] using
      variable_symbol_occurs_condition_admissible
        boundVariable leftReplacement
        hBoundVariable hLeftReplacement.1
  have hOccurrenceRightAdmissible :
      Formula.Admissible occurrenceRight := by
    simpa [occurrenceRight] using
      variable_symbol_occurs_condition_admissible
        boundVariable rightReplacement
        hBoundVariable hRightReplacement.1
  have hBodyLeftAdmissible :
      Formula.Admissible bodyLeft := by
    simpa [bodyLeft] using
      quantifier_body_position_condition_admissible
        boundVariable leftFormula position
        hBoundVariable hLeftFormula.1 hPosition
  have hBodyRightAdmissible :
      Formula.Admissible bodyRight := by
    simpa [bodyRight] using
      quantifier_body_position_condition_admissible
        boundVariable rightFormula position
        hBoundVariable hRightFormula.1 hPosition
  let body₃ : SetFormula :=
    ((universal_binder_at_condition boundVariable rightFormula
        (x#325) (x#326) ∧ₘ
      ((x#327) ∈ₘ domₘ(x#325))) ∧ₘ
      (position ≐ₘ ((x#327) +ₘ (numₘ(3) +ₘ (x#326)))))
  let body₂ : SetFormula :=
    ∃ₘ[SetSort.set, 327], body₃
  let body₁ : SetFormula :=
    ∃ₘ[SetSort.set, 326], body₂
  have hBodyBinder :
      Formula.Admissible
        (universal_binder_at_condition boundVariable rightFormula
          (x#325) (x#326)) :=
    universal_binder_at_condition_admissible
      boundVariable rightFormula (x#325) (x#326)
      hBoundVariable hRightFormula.1
      (set_variable_admissible 325)
      (set_variable_admissible 326)
  have hBodyMember :
      Formula.Admissible
        ((x#327) ∈ₘ domₘ(x#325)) :=
    membership_formula_admissible
      (set_variable_admissible 327)
      (domain_term_admissible (x#325)
        (set_variable_admissible 325))
  have hBodyOffset :
      Term.Admissible
        (numₘ(3) +ₘ (x#326)) SetSort.set :=
    natural_addition_term_admissible
      (numₘ(3)) (x#326)
      (finite_numeral_term_admissible 3)
      (set_variable_admissible 326)
  have hBodyPosition :
      Term.Admissible
        ((x#327) +ₘ (numₘ(3) +ₘ (x#326))) SetSort.set :=
    natural_addition_term_admissible
      (x#327) (numₘ(3) +ₘ (x#326))
      (set_variable_admissible 327) hBodyOffset
  have hBodyEquality :
      Formula.Admissible body₃ := by
    simpa [body₃] using
      Formula.Admissible.conj
        (Formula.Admissible.conj hBodyBinder hBodyMember)
        (Formula.Admissible.equal hPosition hBodyPosition)
  have hBody₂Admissible :
      Formula.Admissible body₂ := by
    simpa [body₂] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set 327 hBodyEquality
  have hBody₁Admissible :
      Formula.Admissible body₁ := by
    simpa [body₁] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set 326 hBody₂Admissible
  let leftBody₃ : SetFormula :=
    ((universal_binder_at_condition boundVariable leftFormula
        (x#325) (x#326) ∧ₘ
      ((x#327) ∈ₘ domₘ(x#325))) ∧ₘ
      (position ≐ₘ ((x#327) +ₘ (numₘ(3) +ₘ (x#326)))))
  let leftBody₂ : SetFormula :=
    ∃ₘ[SetSort.set, 327], leftBody₃
  let leftBody₁ : SetFormula :=
    ∃ₘ[SetSort.set, 326], leftBody₂
  have hOccurrenceFresh (id : FreeVarId)
      (hId312 : id ≠ 312)
      (hBoundFresh :
        (SetSort.set, id) ∉ Term.freeSupport boundVariable) :
      (SetSort.set, id) ∉ Formula.freeSupport occurrenceLeft := by
    have hInnerFresh :
        (SetSort.set, id) ∉
          Formula.freeSupport
            (((x#312 ∈ₘ domₘ(leftReplacement)) ∧ₘ
              ((leftReplacement ·ₘ x#312) ≐ₘ
                (boundVariable ·ₘ numₘ(0))))) := by
      simp only [Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList, hLeftReplacement.2,
        finite_numeral_term_freeSupport]
      intro hMember
      have hMember' := List.mem_cons.mp hMember
      rcases hMember' with hMember | hMember
      · exact hId312 (by simpa using congrArg Prod.snd hMember)
      · have hMember'' := List.mem_cons.mp hMember
        rcases hMember'' with hMember | hMember
        · exact hId312 (by simpa using congrArg Prod.snd hMember)
        · exact hBoundFresh (by simpa [List.mem_append] using hMember)
    have hClosedFresh :=
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (σ := signature) (SetSort.set, id) SetSort.set 312 0
        (((x#312 ∈ₘ domₘ(leftReplacement)) ∧ₘ
          ((leftReplacement ·ₘ x#312) ≐ₘ
            (boundVariable ·ₘ numₘ(0))))) hInnerFresh
    simp only [occurrenceLeft, variable_symbol_occurs_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList]
    intro hMember
    have hMember' := List.mem_append.mp hMember
    rcases hMember' with hMember | hMember
    · exact hBoundFresh (by simpa [List.mem_append] using hMember)
    · exact hClosedFresh (by simpa [List.mem_append] using hMember)
  have hBodyLeftFresh (id : FreeVarId)
      (hId : id = 325 ∨ id = 326 ∨ id = 327) :
      (SetSort.set, id) ∉ Formula.freeSupport bodyLeft := by
    rcases hId with rfl | rfl | rfl
    · simpa [bodyLeft, quantifier_body_position_condition,
        leftBody₁, leftBody₂, leftBody₃] using
        (Formula.not_mem_freeSupport_closeFreeAt
          (σ := signature) SetSort.set 325 0 leftBody₁)
    · have hInner :
          (SetSort.set, 326) ∉ Formula.freeSupport leftBody₁ := by
        simpa [leftBody₁] using
          (Formula.not_mem_freeSupport_closeFreeAt
            (σ := signature) SetSort.set 326 0 leftBody₂)
      simpa [bodyLeft, quantifier_body_position_condition,
        leftBody₁, leftBody₂, leftBody₃] using
        Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
          (σ := signature) (SetSort.set, 326) SetSort.set 325 0
          leftBody₁ hInner
    · have hInner₃ :
          (SetSort.set, 327) ∉ Formula.freeSupport leftBody₂ := by
        simpa [leftBody₂] using
          (Formula.not_mem_freeSupport_closeFreeAt
            (σ := signature) SetSort.set 327 0 leftBody₃)
      have hInner₂ :
          (SetSort.set, 327) ∉ Formula.freeSupport leftBody₁ :=
        Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
          (σ := signature) (SetSort.set, 327) SetSort.set 326 0
          leftBody₂ hInner₃
      simpa [bodyLeft, quantifier_body_position_condition,
        leftBody₁, leftBody₂, leftBody₃] using
        Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
          (σ := signature) (SetSort.set, 327) SetSort.set 325 0
          leftBody₁ hInner₂
  let Γ : Context signature := [bodyLeft, occurrenceLeft]
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.negIntro
  have hOccurrenceLeft :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] occurrenceLeft :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hBodyLeft :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] bodyLeft :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hOccurrenceRight :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] occurrenceRight :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ])
        hOccurrenceEquality)
      hOccurrenceLeft
  have hBodyRight :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] bodyRight :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ])
        hQuantifierBodyEquality)
      hBodyLeft
  have hExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, 325], body₁ := by
    simpa [bodyRight, quantifier_body_position_condition,
      body₁, body₂, body₃] using hBodyRight
  nd_apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory) (Γ := Γ)
    (sort := SetSort.set) (eigen := 325)
    (body := body₁) (conclusion := Formula.falsum)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    simp only [Γ, List.mem_cons, List.not_mem_nil,
      or_false] at hFormula
    rcases hFormula with rfl | rfl
    · simpa [bodyLeft, quantifier_body_position_condition] using
        (Formula.not_mem_freeSupport_closeFreeAt
          (σ := signature) SetSort.set 325 0
          (∃ₘ[SetSort.set, 326],
            ∃ₘ[SetSort.set, 327],
              ((universal_binder_at_condition boundVariable leftFormula
                  (x#325) (x#326) ∧ₘ
                ((x#327) ∈ₘ domₘ(x#325))) ∧ₘ
                (position ≐ₘ
                  ((x#327) +ₘ (numₘ(3) +ₘ (x#326)))))))
    · exact hOccurrenceFresh 325 (by decide) hBoundFresh325
  · exact List.not_mem_nil
  · exact hExists
  · let Γ₁ : Context signature := body₁ :: Γ
    have hBody₁ :
        Γ₁ ⊢ₘ[fs_zfc_support_raw_theory] body₁ :=
      FirstOrder.Derives.assumption (by simp [Γ₁])
    have hExists₂ :
        Γ₁ ⊢ₘ[fs_zfc_support_raw_theory]
          ∃ₘ[SetSort.set, 326], body₂ := by
      simpa [body₁] using hBody₁
    nd_apply FirstOrder.Derives.exists_elim
      (T := fs_zfc_support_raw_theory) (Γ := Γ₁)
      (sort := SetSort.set) (eigen := 326)
      (body := body₂) (conclusion := Formula.falsum)
    · intro formula hFormula
      rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      simp only [Γ₁, Γ, List.mem_cons,
        List.not_mem_nil, or_false] at hFormula
      rcases hFormula with rfl | rfl | rfl
      · simpa [body₁] using
          (Formula.not_mem_freeSupport_closeFreeAt
            (σ := signature) SetSort.set 326 0
            body₂)
      · exact hBodyLeftFresh 326 (by simp)
      · exact hOccurrenceFresh 326 (by decide) hBoundFresh326
    · exact List.not_mem_nil
    · exact hExists₂
    · let Γ₂ : Context signature := body₂ :: Γ₁
      have hBody₂ :
          Γ₂ ⊢ₘ[fs_zfc_support_raw_theory] body₂ :=
        FirstOrder.Derives.assumption (by simp [Γ₂])
      have hExists₃ :
          Γ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            ∃ₘ[SetSort.set, 327], body₃ := by
        simpa [body₂] using hBody₂
      nd_apply FirstOrder.Derives.exists_elim
        (T := fs_zfc_support_raw_theory) (Γ := Γ₂)
        (sort := SetSort.set) (eigen := 327)
        (body := body₃) (conclusion := Formula.falsum)
      · intro formula hFormula
        rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
        exact List.not_mem_nil
      · intro formula hFormula
        simp only [Γ₂, Γ₁, Γ, List.mem_cons,
          List.not_mem_nil, or_false] at hFormula
        rcases hFormula with rfl | rfl | rfl | rfl
        · simpa [body₂] using
            (Formula.not_mem_freeSupport_closeFreeAt
              (σ := signature) SetSort.set 327 0
              body₃)
        · have hInner :
              (SetSort.set, 327) ∉ Formula.freeSupport body₂ := by
            simpa [body₂] using
              (Formula.not_mem_freeSupport_closeFreeAt
                (σ := signature) SetSort.set 327 0
                body₃)
          simpa [body₁] using
            Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
              (σ := signature) (SetSort.set, 327) SetSort.set 326 0
              body₂ hInner
        · exact hBodyLeftFresh 327 (by simp)
        · exact hOccurrenceFresh 327 (by decide) hBoundFresh327
      · exact List.not_mem_nil
      · exact hExists₃
      · let Γ₃ : Context signature := body₃ :: Γ₂
        have hBody₃ :
            Γ₃ ⊢ₘ[fs_zfc_support_raw_theory] body₃ :=
          FirstOrder.Derives.assumption (by simp [Γ₃])
        have hBinder :
            Γ₃ ⊢ₘ[fs_zfc_support_raw_theory]
              universal_binder_at_condition boundVariable
                rightFormula (x#325) (x#326) :=
          FirstOrder.Derives.conjElimLeft <|
            FirstOrder.Derives.conjElimLeft hBody₃
        have hNotOccurrenceRight :
            Γ₃ ⊢ₘ[fs_zfc_support_raw_theory]
              ¬ₘ variable_symbol_occurs_condition
                boundVariable rightReplacement :=
          FirstOrder.Derives.impElim
            (FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Γ₃) (by simp [Γ₃, Γ₂, Γ₁, Γ])
              hSeparation)
            hBinder
        have hOccurrenceRight₃ :
            Γ₃ ⊢ₘ[fs_zfc_support_raw_theory] occurrenceRight :=
          FirstOrder.Derives.context_weaken
            (Γ := Γ) (Δ := Γ₃) (by
              intro formula hFormula
              change formula ∈ body₃ :: body₂ :: body₁ :: Γ
              exact List.mem_cons_of_mem body₃ <|
                List.mem_cons_of_mem body₂ <|
                  List.mem_cons_of_mem body₁ hFormula)
            hOccurrenceRight
        exact FirstOrder.Derives.negElim
          hOccurrenceRight₃ hNotOccurrenceRight

theorem fs_zfc_support_raw_substitutable_no_capture_of_implications
    (boundVariable replacement formula : SetTerm)
    (hBoundVariable : Term.Admissible boundVariable SetSort.set)
    (hReplacement : Term.Admissible replacement SetSort.set)
    (hFormula : Term.Admissible formula SetSort.set)
    (hReplacementFresh421 :
      (SetSort.set, 421) ∉ Term.freeSupport replacement)
    (hVariableCollection :
      Derives fs_zfc_support_raw_theory [] (
        ((x#420 ∈ₘ varsₘ(replacement)) ⟶ₘ
          ((x#420 ∈ₘ VarSymₘ) ∧ₘ
            variable_symbol_occurs_condition
              (x#420) replacement))))
    (hNoCapture :
      Derives fs_zfc_support_raw_theory [] (
        variable_symbol_occurs_condition
            (x#420) replacement ⟶ₘ
          ¬ₘ quantifier_body_position_condition
            (x#420) formula (x#421))) :
    Derives fs_zfc_support_raw_theory [] (
      ∀ₘ[SetSort.set, 420],
        ((x#420 ∈ₘ varsₘ(replacement)) ⟶ₘ
          (∀ₘ[SetSort.set, 421],
            (free_occurrence_position_condition
                boundVariable formula (x#421) ⟶ₘ
              ¬ₘ quantifier_body_position_condition
                (x#420) formula (x#421))))) := by
  let variableMember : SetFormula :=
    x#420 ∈ₘ varsₘ(replacement)
  let freePosition : SetFormula :=
    free_occurrence_position_condition
      boundVariable formula (x#421)
  let noCapture : SetFormula :=
    ¬ₘ quantifier_body_position_condition
      (x#420) formula (x#421)
  let positionImplication : SetFormula :=
    freePosition ⟶ₘ noCapture
  let allPositions : SetFormula :=
    ∀ₘ[SetSort.set, 421], positionImplication
  let variableImplication : SetFormula :=
    variableMember ⟶ₘ allPositions
  have hVariableMemberAdmissible :
      Formula.Admissible variableMember := by
    simpa [variableMember] using
      membership_formula_admissible
        (set_variable_admissible 420)
        (variable_collection_term_admissible
          replacement hReplacement)
  have hFreePositionAdmissible :
      Formula.Admissible freePosition := by
    simpa [freePosition] using
      free_occurrence_position_condition_admissible
        boundVariable formula (x#421)
        hBoundVariable hFormula
        (set_variable_admissible 421)
  have hNoCaptureAdmissible :
      Formula.Admissible noCapture := by
    simpa [noCapture] using
      Formula.Admissible.neg <|
        quantifier_body_position_condition_admissible
          (x#420) formula (x#421)
          (set_variable_admissible 420)
          hFormula (set_variable_admissible 421)
  have hPositionImplicationAdmissible :
      Formula.Admissible positionImplication := by
    simpa [positionImplication] using
      Formula.Admissible.imp
        hFreePositionAdmissible hNoCaptureAdmissible
  have hAllPositionsAdmissible :
      Formula.Admissible allPositions := by
    simpa [allPositions] using
      Formula.Admissible.forall_closeFreeAt
        SetSort.set 421 hPositionImplicationAdmissible
  have hVariableImplicationAdmissible :
      Formula.Admissible variableImplication := by
    simpa [variableImplication] using
      Formula.Admissible.imp
        hVariableMemberAdmissible hAllPositionsAdmissible
  have hTheoryFresh (eigen : FreeVarId) :
      ∀ formula, fs_zfc_support_raw_theory formula →
        (SetSort.set, eigen) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  let variableContext : Context signature := [variableMember]
  have hPositionBody :
      variableContext ⊢ₘ[fs_zfc_support_raw_theory]
        positionImplication := by
    nd_apply FirstOrder.Derives.impIntro
    let context : Context signature :=
      [freePosition, variableMember]
    have hFreePosition :
        context ⊢ₘ[fs_zfc_support_raw_theory] freePosition :=
      FirstOrder.Derives.assumption (by simp [context])
    have hVariableMember :
        context ⊢ₘ[fs_zfc_support_raw_theory] variableMember :=
      FirstOrder.Derives.assumption (by simp [context])
    have hVariableCollection' :
        context ⊢ₘ[fs_zfc_support_raw_theory]
          (x#420 ∈ₘ VarSymₘ) ∧ₘ
            variable_symbol_occurs_condition
              (x#420) replacement :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := context) (by simp [context])
          hVariableCollection)
        hVariableMember
    have hOccurrence :
        context ⊢ₘ[fs_zfc_support_raw_theory]
          variable_symbol_occurs_condition
            (x#420) replacement :=
      FirstOrder.Derives.conjElimRight hVariableCollection'
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := context) (by simp [context])
        hNoCapture)
      hOccurrence
  have hAllPositions :
      variableContext ⊢ₘ[fs_zfc_support_raw_theory] allPositions := by
    apply FirstOrder.Derives.forall_intro
      (hTheoryFresh 421)
    · intro formula hFormula
      simp only [variableContext, List.mem_cons,
        List.not_mem_nil, or_false] at hFormula
      rcases hFormula with rfl
      simpa [variableMember, Formula.freeSupport,
        Term.freeSupport, Term.freeSupportList,
        Term.freeSupportList_append, List.mem_append,
        hReplacementFresh421]
    · simpa [allPositions] using hPositionBody
  have hVariableImplication :
      [] ⊢ₘ[fs_zfc_support_raw_theory] variableImplication := by
    nd_apply FirstOrder.Derives.impIntro
    simpa [variableContext, variableImplication] using
      hAllPositions
  simpa [variableImplication, variableMember, allPositions,
    positionImplication, freePosition, noCapture] using
    FirstOrder.Derives.forall_intro
      (T := fs_zfc_support_raw_theory) (Γ := [])
      (sort := SetSort.set) (eigen := 420)
      (hTheoryFresh 420) (by simp) hVariableImplication

/--
可代入性关系与其对象定义体在三个闭代码处等价。
三个代码项只需闭合 quotation 边界；不额外要求任何语义或模型前提。
-/
theorem fs_zfc_support_raw_substitutable_iff_condition
    (boundCode replacementCode bodyCode : SetTerm)
    (hBoundBoundary :
      GodelQuotation.Numbered.CodeBoundary boundCode)
    (hReplacementBoundary :
      GodelQuotation.Numbered.CodeBoundary replacementCode)
    (hBodyBoundary :
      GodelQuotation.Numbered.CodeBoundary bodyCode) :
    Derives fs_zfc_support_raw_theory [] (
      substitutableₘ(boundCode, replacementCode, bodyCode) ↔ₘ
        substitutable_condition boundCode replacementCode bodyCode) := by
  have hCloseCode (code : SetTerm)
      (hCode : GodelQuotation.Numbered.CodeBoundary code)
      (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth code = code :=
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq hCode id depth
  have hOpenCode (code : SetTerm)
      (hCode : GodelQuotation.Numbered.CodeBoundary code)
      (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement code = code :=
    GodelQuotation.Numbered.CodeBoundary.openAt_eq hCode depth replacement
  have hSubstituteCode (code : SetTerm)
      (hCode : GodelQuotation.Numbered.CodeBoundary code)
      (id : Nat) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement code = code :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq hCode id replacement
  have hNumeralBoundary (value : Nat) :
      GodelQuotation.Numbered.CodeBoundary (numₘ(value)) :=
    ⟨finite_numeral_term_admissible value,
      finite_numeral_term_freeSupport value⟩
  have hCloseCommute (sourceId closedId : FreeVarId) (depth : Nat)
      (replacement : SetTerm)
      (hReplacement : GodelQuotation.Numbered.CodeBoundary replacement)
      (formula : SetFormula) (hDistinct : sourceId ≠ closedId) :
      Formula.substituteFree SetSort.set sourceId replacement
          (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set sourceId replacement formula) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId closedId depth replacement formula
      hDistinct hReplacement.1.2 (by
        rw [hReplacement.2]
        exact List.not_mem_nil)).symm
  have hSubstitutableCondition0 :
      Formula.substituteFree SetSort.set 0 boundCode
          (substitutable_condition (x#0) (x#1) (x#2)) =
        substitutable_condition boundCode (x#1) (x#2) := by
    simp [substitutable_condition, Formula.substituteFree,
      free_occurrence_position_condition,
      bound_occurrence_position_condition,
      variable_occurs_at_position_condition,
      binder_declaration_position_condition,
      quantifier_body_position_condition,
      universal_binder_at_condition,
      code_substring_at_condition,
      Formula.closeFreeAt, Formula.next_depth,
      Term.substituteFree, Term.closeFreeAt, set_variable,
      hCloseCode boundCode hBoundBoundary,
      hCloseCode (numₘ(0)) (hNumeralBoundary 0),
      hCloseCode (numₘ(2)) (hNumeralBoundary 2),
      hCloseCode (numₘ(3)) (hNumeralBoundary 3),
      hSubstituteCode (numₘ(0)) (hNumeralBoundary 0),
      hSubstituteCode (numₘ(2)) (hNumeralBoundary 2),
      hSubstituteCode (numₘ(3)) (hNumeralBoundary 3)]
  have hSubstitutableCondition0Closed :
      Formula.substituteFree SetSort.set 0 boundCode
          (Formula.closeFreeAt SetSort.set 1 1
            (Formula.closeFreeAt SetSort.set 2 0
              (substitutable_condition (x#0) (x#1) (x#2)))) =
        Formula.closeFreeAt SetSort.set 1 1
          (Formula.closeFreeAt SetSort.set 2 0
            (substitutable_condition boundCode (x#1) (x#2))) := by
    rw [hCloseCommute 0 1 1 boundCode hBoundBoundary _ (by decide)]
    rw [hCloseCommute 0 2 0 boundCode hBoundBoundary _ (by decide)]
    exact congrArg
      (Formula.closeFreeAt SetSort.set 1 1 ∘
        Formula.closeFreeAt SetSort.set 2 0)
      hSubstitutableCondition0
  have hSubstitutableCondition1 :
      Formula.substituteFree SetSort.set 1 replacementCode
          (substitutable_condition boundCode (x#1) (x#2)) =
        substitutable_condition boundCode replacementCode (x#2) := by
    simp [substitutable_condition, Formula.substituteFree,
      free_occurrence_position_condition,
      bound_occurrence_position_condition,
      variable_occurs_at_position_condition,
      binder_declaration_position_condition,
      quantifier_body_position_condition,
      universal_binder_at_condition,
      code_substring_at_condition,
      Formula.closeFreeAt, Formula.next_depth,
      Term.substituteFree, Term.closeFreeAt, set_variable,
      hCloseCode boundCode hBoundBoundary,
      hCloseCode replacementCode hReplacementBoundary,
      hCloseCode (numₘ(0)) (hNumeralBoundary 0),
      hCloseCode (numₘ(2)) (hNumeralBoundary 2),
      hCloseCode (numₘ(3)) (hNumeralBoundary 3),
      hSubstituteCode boundCode hBoundBoundary,
      hSubstituteCode (numₘ(0)) (hNumeralBoundary 0),
      hSubstituteCode (numₘ(2)) (hNumeralBoundary 2),
      hSubstituteCode (numₘ(3)) (hNumeralBoundary 3)]
  have hSubstitutableCondition2 :
      Formula.substituteFree SetSort.set 2 bodyCode
          (substitutable_condition boundCode replacementCode (x#2)) =
        substitutable_condition boundCode replacementCode bodyCode := by
    simp [substitutable_condition, Formula.substituteFree,
      free_occurrence_position_condition,
      bound_occurrence_position_condition,
      variable_occurs_at_position_condition,
      binder_declaration_position_condition,
      quantifier_body_position_condition,
      universal_binder_at_condition,
      code_substring_at_condition,
      Formula.closeFreeAt, Formula.next_depth,
      Term.substituteFree, Term.closeFreeAt, set_variable,
      hCloseCode boundCode hBoundBoundary,
      hCloseCode replacementCode hReplacementBoundary,
      hCloseCode bodyCode hBodyBoundary,
      hCloseCode (numₘ(0)) (hNumeralBoundary 0),
      hCloseCode (numₘ(2)) (hNumeralBoundary 2),
      hCloseCode (numₘ(3)) (hNumeralBoundary 3),
      hSubstituteCode boundCode hBoundBoundary,
      hSubstituteCode replacementCode hReplacementBoundary,
      hSubstituteCode (numₘ(0)) (hNumeralBoundary 0),
      hSubstituteCode (numₘ(2)) (hNumeralBoundary 2),
      hSubstituteCode (numₘ(3)) (hNumeralBoundary 3)]
  have hSubstitutableCondition1Closed :
      Formula.substituteFree SetSort.set 1 replacementCode
          (Formula.closeFreeAt SetSort.set 2 0
            (substitutable_condition boundCode (x#1) (x#2))) =
        Formula.closeFreeAt SetSort.set 2 0
          (substitutable_condition boundCode replacementCode (x#2)) := by
    rw [hCloseCommute 1 2 0 replacementCode hReplacementBoundary _ (by decide)]
    exact congrArg
      (Formula.closeFreeAt SetSort.set 2 0)
      hSubstitutableCondition1
  have hDefinition :
      Derives fs_zfc_support_raw_theory [] substitutable_definition_axiom := by
    apply fs_zfc_support_raw_derives_of_logical_rules
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hAt0 :
      Derives fs_zfc_support_raw_theory [] (
        ∀ₘ[SetSort.set, 1],
          ∀ₘ[SetSort.set, 2],
            (substitutableₘ(boundCode, (x#1), (x#2)) ↔ₘ
              substitutable_condition boundCode (x#1) (x#2))) := by
    simpa [substitutable_definition_axiom,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable, set_bound_variable,
      GodelQuotation.Numbered.CodeBoundary.openAt_eq hBoundBoundary,
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hBoundBoundary,
      GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
        hBoundBoundary,
      hCloseCode boundCode hBoundBoundary,
      hSubstitutableCondition0Closed] using
      (FirstOrder.Derives.forall_elim
        (term := boundCode) hDefinition)
  have hAt1 :
      Derives fs_zfc_support_raw_theory [] (
        ∀ₘ[SetSort.set, 2],
          (substitutableₘ(boundCode, replacementCode, (x#2)) ↔ₘ
            substitutable_condition boundCode replacementCode (x#2))) := by
    simpa [
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable, set_bound_variable,
      hCloseCode boundCode hBoundBoundary,
      hOpenCode boundCode hBoundBoundary,
      GodelQuotation.Numbered.CodeBoundary.openAt_eq
        hReplacementBoundary,
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hReplacementBoundary,
      GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
        hReplacementBoundary,
      hSubstitutableCondition1Closed] using
      (FirstOrder.Derives.forall_elim
        (term := replacementCode) hAt0)
  have hAt2 :
      Derives fs_zfc_support_raw_theory [] (
        substitutableₘ(boundCode, replacementCode, bodyCode) ↔ₘ
          substitutable_condition boundCode replacementCode bodyCode) := by
    simpa [
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable, set_bound_variable,
      hCloseCode boundCode hBoundBoundary,
      hCloseCode replacementCode hReplacementBoundary,
      hOpenCode boundCode hBoundBoundary,
      hOpenCode replacementCode hReplacementBoundary,
      hOpenCode bodyCode hBodyBoundary,
      GodelQuotation.Numbered.CodeBoundary.openAt_eq hBodyBoundary,
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hBodyBoundary,
      GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
        hBodyBoundary,
      hSubstitutableCondition2] using
      (FirstOrder.Derives.forall_elim
        (term := bodyCode) hAt1)
  exact hAt2

/--
把可代入性定义体的对象层证明提升为公开关系事实。
-/
theorem fs_zfc_support_raw_substitutable_of_condition
    (boundCode replacementCode bodyCode : SetTerm)
    (hBoundBoundary :
      GodelQuotation.Numbered.CodeBoundary boundCode)
    (hReplacementBoundary :
      GodelQuotation.Numbered.CodeBoundary replacementCode)
    (hBodyBoundary :
      GodelQuotation.Numbered.CodeBoundary bodyCode)
    (hCondition :
      Derives fs_zfc_support_raw_theory [] (
        substitutable_condition boundCode replacementCode bodyCode)) :
    Derives fs_zfc_support_raw_theory [] (
      substitutableₘ(boundCode, replacementCode, bodyCode)) :=
  FirstOrder.Derives.iffElimLeft
    (fs_zfc_support_raw_substitutable_iff_condition
      boundCode replacementCode bodyCode
      hBoundBoundary hReplacementBoundary hBodyBoundary)
    hCondition

/--
公开可代入性关系可消去为其对象定义体。
-/
theorem fs_zfc_support_raw_substitutable_condition_of
    (boundCode replacementCode bodyCode : SetTerm)
    (hBoundBoundary :
      GodelQuotation.Numbered.CodeBoundary boundCode)
    (hReplacementBoundary :
      GodelQuotation.Numbered.CodeBoundary replacementCode)
    (hBodyBoundary :
      GodelQuotation.Numbered.CodeBoundary bodyCode)
    (hSubstitutable :
      Derives fs_zfc_support_raw_theory [] (
        substitutableₘ(boundCode, replacementCode, bodyCode))) :
    Derives fs_zfc_support_raw_theory [] (
      substitutable_condition boundCode replacementCode bodyCode) :=
  FirstOrder.Derives.iffElimRight
    (fs_zfc_support_raw_substitutable_iff_condition
      boundCode replacementCode bodyCode
      hBoundBoundary hReplacementBoundary hBodyBoundary)
    hSubstitutable

/--
可代入性原子逐三个代码参数穿过对象等式。
这只是 Leibniz 换元，不展开可代入性定义体。
-/
theorem fs_substitutable_of_equalities
    {T : Theory signature} {Γ : Context signature}
    (leftBound rightBound leftReplacement rightReplacement
      leftFormula rightFormula : SetTerm)
    (hLeftBound : Term.Admissible leftBound SetSort.set)
    (hRightBound : Term.Admissible rightBound SetSort.set)
    (hLeftReplacement : Term.Admissible leftReplacement SetSort.set)
    (hRightReplacement : Term.Admissible rightReplacement SetSort.set)
    (hLeftFormula : Term.Admissible leftFormula SetSort.set)
    (hRightFormula : Term.Admissible rightFormula SetSort.set)
    (hFresh :
      ReservedIdsFresh [467, 468, 469]
        [leftBound, rightBound, leftReplacement, rightReplacement,
          leftFormula, rightFormula])
    (hBoundEquality :
      Γ ⊢ₘ[T] leftBound ≐ₘ rightBound)
    (hReplacementEquality :
      Γ ⊢ₘ[T] leftReplacement ≐ₘ rightReplacement)
    (hFormulaEquality :
      Γ ⊢ₘ[T] leftFormula ≐ₘ rightFormula)
    (hRight :
      Γ ⊢ₘ[T]
        substitutableₘ(
          rightBound, rightReplacement, rightFormula)) :
    Γ ⊢ₘ[T]
      substitutableₘ(
        leftBound, leftReplacement, leftFormula) := by
  have hFixed (term : SetTerm)
      (hTerm :
        term ∈
          [leftBound, rightBound, leftReplacement, rightReplacement,
            leftFormula, rightFormula])
      (id : FreeVarId) (hId : id ∈ [467, 468, 469])
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement term = term :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement term
        (hFresh term hTerm id hId)
  have hFormulaIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := 469)
      (left := leftFormula) (right := rightFormula)
      (body :=
        substitutableₘ(
          rightBound, rightReplacement, x#469))
      hFormulaEquality
      (hLeftCheck := Term.check_admissible_complete hLeftFormula)
      (hRightCheck := Term.check_admissible_complete hRightFormula)
      (hBodyCheck := Formula.check_admissible_complete <| by
        exact is_substitutable_formula_admissible
          hRightBound hRightReplacement
            (set_variable_admissible 469))
  have hFormulaIff :
      Γ ⊢ₘ[T]
        substitutableₘ(
            rightBound, rightReplacement, leftFormula) ↔ₘ
          substitutableₘ(
            rightBound, rightReplacement, rightFormula) := by
    simpa [Formula.substituteFree, Term.substituteFree, set_variable,
      hFixed rightBound (by simp) 469 (by simp),
      hFixed rightReplacement (by simp) 469 (by simp)] using
        hFormulaIffRaw
  have hAtFormula :
      Γ ⊢ₘ[T]
        substitutableₘ(
          rightBound, rightReplacement, leftFormula) :=
    FirstOrder.Derives.iffElimLeft hFormulaIff hRight
  have hReplacementIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := 468)
      (left := leftReplacement) (right := rightReplacement)
      (body :=
        substitutableₘ(
          rightBound, x#468, leftFormula))
      hReplacementEquality
      (hLeftCheck := Term.check_admissible_complete hLeftReplacement)
      (hRightCheck := Term.check_admissible_complete hRightReplacement)
      (hBodyCheck := Formula.check_admissible_complete <| by
        exact is_substitutable_formula_admissible
          hRightBound (set_variable_admissible 468) hLeftFormula)
  have hReplacementIff :
      Γ ⊢ₘ[T]
        substitutableₘ(
            rightBound, leftReplacement, leftFormula) ↔ₘ
          substitutableₘ(
            rightBound, rightReplacement, leftFormula) := by
    simpa [Formula.substituteFree, Term.substituteFree, set_variable,
      hFixed rightBound (by simp) 468 (by simp),
      hFixed leftFormula (by simp) 468 (by simp)] using
        hReplacementIffRaw
  have hAtReplacement :
      Γ ⊢ₘ[T]
        substitutableₘ(
          rightBound, leftReplacement, leftFormula) :=
    FirstOrder.Derives.iffElimLeft hReplacementIff hAtFormula
  have hBoundIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := 467)
      (left := leftBound) (right := rightBound)
      (body :=
        substitutableₘ(
          x#467, leftReplacement, leftFormula))
      hBoundEquality
      (hLeftCheck := Term.check_admissible_complete hLeftBound)
      (hRightCheck := Term.check_admissible_complete hRightBound)
      (hBodyCheck := Formula.check_admissible_complete <| by
        exact is_substitutable_formula_admissible
          (set_variable_admissible 467)
          hLeftReplacement hLeftFormula)
  have hBoundIff :
      Γ ⊢ₘ[T]
        substitutableₘ(
            leftBound, leftReplacement, leftFormula) ↔ₘ
          substitutableₘ(
            rightBound, leftReplacement, leftFormula) := by
    simpa [Formula.substituteFree, Term.substituteFree, set_variable,
      hFixed leftReplacement (by simp) 467 (by simp),
      hFixed leftFormula (by simp) 467 (by simp)] using
        hBoundIffRaw
  exact FirstOrder.Derives.iffElimLeft
    hBoundIff hAtReplacement

theorem fs_zfc_support_raw_equality_substitution_axiom_code_exists
    {body : SetFormula}
    (leftId rightId : FreeVarId)
    (hBody : Formula.Admissible body) :
    ∃ code,
      GodelQuotation.Numbered.quote?
          (Formula.imp
            (Formula.equal
              (Term.var (.fvar SetSort.set leftId))
              (Term.var (.fvar SetSort.set rightId)))
            (Formula.imp body
              (Formula.substituteFree SetSort.set leftId
                (Term.var (.fvar SetSort.set rightId)) body))) =
        some code ∧
      Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code) ∧
      Derives fs_zfc_support_raw_theory [] (
        substitutableₘ(
          var_codeₘ(numₘ(2 * leftId)),
          var_codeₘ(numₘ(2 * rightId)),
          fs_zfc_formula_code_term body)) := by
  let leftTerm : SetTerm :=
    Term.var (.fvar SetSort.set leftId)
  let rightTerm : SetTerm :=
    Term.var (.fvar SetSort.set rightId)
  let target : SetFormula :=
    Formula.substituteFree SetSort.set leftId rightTerm body
  have hLeftTerm : Term.Admissible leftTerm SetSort.set := by
    simpa [leftTerm] using
      (show Term.Admissible
          (Term.var (.fvar SetSort.set leftId) : SetTerm) SetSort.set from
        ⟨TermWellSorted.fvar (σ := signature) SetSort.set leftId,
          TermScoped.fvar (σ := signature)
            (ctx := (Scope.empty : Scope signature))
            SetSort.set leftId⟩)
  have hRightTerm : Term.Admissible rightTerm SetSort.set := by
    simpa [rightTerm] using
      (show Term.Admissible
          (Term.var (.fvar SetSort.set rightId) : SetTerm) SetSort.set from
        ⟨TermWellSorted.fvar (σ := signature) SetSort.set rightId,
          TermScoped.fvar (σ := signature)
            (ctx := (Scope.empty : Scope signature))
            SetSort.set rightId⟩)
  have hTarget : Formula.Admissible target := by
    simpa [target] using
      Formula.Admissible.substituteFree
        SetSort.set leftId hBody hRightTerm
  have hWholeFormula :
      Formula.Admissible
        (Formula.imp
          (Formula.equal leftTerm rightTerm)
          (Formula.imp body target)) := by
    exact Formula.Admissible.imp
      (Formula.Admissible.equal hLeftTerm hRightTerm)
      (Formula.Admissible.imp hBody hTarget)
  rcases GodelQuotation.Numbered.quote?_exists hBody with
    ⟨bodyCode, hBodyQuote⟩
  rcases GodelQuotation.quote_term_tokens?_exists
      (term := rightTerm) hRightTerm with
    ⟨replacementTokens, hReplacementTokens⟩
  rcases GodelQuotation.Numbered.quote?_exists hTarget with
    ⟨targetCode, hTargetQuote⟩
  let replacementCode : SetTerm :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.free_name rightId)
  have hReplacementQuote :
      GodelQuotation.Numbered.quote_term_with?
          GodelQuotation.free_name [] rightTerm =
        some replacementCode := by
    simp [replacementCode, rightTerm,
      GodelQuotation.Numbered.quote_term_with?]
  let boundCode : SetTerm :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.free_name leftId)
  have hBoundTermQuote :
      GodelQuotation.Numbered.quote_term_with?
          GodelQuotation.free_name [] leftTerm =
        some boundCode := by
    simp [boundCode, leftTerm,
      GodelQuotation.Numbered.quote_term_with?]
  have hBoundBoundary :
      GodelQuotation.Numbered.CodeBoundary boundCode := by
    exact
      ⟨variable_code_term_admissible
          (numₘ(GodelQuotation.free_name leftId))
          (finite_numeral_term_admissible
            (GodelQuotation.free_name leftId)),
        named_variable_code_freeSupport
          (GodelQuotation.free_name leftId)⟩
  have hBodyBoundary :
      GodelQuotation.Numbered.CodeBoundary bodyCode :=
    GodelQuotation.Numbered.quote?_code_boundary hBodyQuote
  have hReplacementBoundary :
      GodelQuotation.Numbered.CodeBoundary replacementCode :=
    GodelQuotation.Numbered.quote_term_with?_code_boundary
      GodelQuotation.free_name [] hReplacementQuote
  have hTargetBoundary :
      GodelQuotation.Numbered.CodeBoundary targetCode :=
    GodelQuotation.Numbered.quote?_code_boundary hTargetQuote
  have hBodyFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(bodyCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code hBodyQuote)
  have hReplacementTermCode :
      Derives fs_zfc_support_raw_theory [] term_codeₘ(replacementCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote_term_with?_is_term_code
        GodelQuotation.free_name [] hReplacementQuote)
  have hBoundMember :
      Derives fs_zfc_support_raw_theory [] (boundCode ∈ₘ VarSymₘ) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.named_variable_code_mem_variable_symbols
        (GodelQuotation.free_name leftId))
  have hReplacementMember :
      Derives fs_zfc_support_raw_theory [] (replacementCode ∈ₘ VarSymₘ) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.named_variable_code_mem_variable_symbols
        (GodelQuotation.free_name rightId))
  have hBodyTokensExists :
      ∃ bodyTokens, GodelQuotation.Numbered.quote_tokens? body =
        some bodyTokens :=
    GodelQuotation.Numbered.quote_tokens?_exists hBody
  rcases hBodyTokensExists with
    ⟨bodyTokens, hBodyTokens⟩
  have hReplacementTokens' :
      GodelQuotation.quote_term_tokens? rightTerm =
        some replacementTokens :=
    hReplacementTokens
  have hBodyEquality :
      Derives fs_zfc_support_raw_theory [] (
        bodyCode ≐ₘ
          GodelQuotation.standard_token_sequence bodyTokens) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.quote?_eq_standard_token_sequence
        hBodyTokens hBodyQuote)
  have hReplacementEquality :
      Derives fs_zfc_support_raw_theory [] (
        replacementCode ≐ₘ
          GodelQuotation.standard_token_sequence replacementTokens) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (by
        simpa [replacementCode] using
          GodelQuotation.quote_term_with?_eq_standard_token_sequence
            GodelQuotation.free_name [] hReplacementTokens'
            hReplacementQuote)
  have hSubstitutionSpec :
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          bodyCode boundCode replacementCode targetCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.quote?_substitution_result_spec_derives
        leftId hBodyTokens hBodyQuote
        hReplacementTokens' hReplacementQuote hTargetQuote)
  have hSubstitutionEquality :
      Derives fs_zfc_support_raw_theory [] (
        targetCode ≐ₘ
          subst_codeₘ(bodyCode, boundCode, replacementCode)) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.quote?_substitution_result_eq_derives
        leftId hBodyTokens hBodyQuote
        hReplacementTokens' hReplacementQuote hTargetQuote)
  let standardBodyCode : SetTerm :=
    GodelQuotation.standard_token_sequence bodyTokens
  let standardReplacementCode : SetTerm :=
    GodelQuotation.standard_token_sequence replacementTokens
  have hStandardBodyBoundary :
      GodelQuotation.Numbered.CodeBoundary standardBodyCode := by
    exact ⟨by
      simpa [standardBodyCode] using
        GodelQuotation.standard_token_sequence_admissible bodyTokens,
      by
        simp [standardBodyCode]⟩
  have hStandardReplacementBoundary :
      GodelQuotation.Numbered.CodeBoundary standardReplacementCode := by
    exact ⟨by
      simpa [standardReplacementCode] using
        GodelQuotation.standard_token_sequence_admissible replacementTokens,
      by
        simp [standardReplacementCode]⟩
  have hOccurrenceEquality :
      Derives fs_zfc_support_raw_theory [] (
        variable_symbol_occurs_condition (x#420) replacementCode ↔ₘ
          variable_symbol_occurs_condition
            (x#420) standardReplacementCode) :=
    fs_zfc_support_raw_variable_symbol_occurs_iff_of_code_equality
      (x#420) replacementCode standardReplacementCode
      (set_variable_admissible 420)
      hReplacementBoundary hStandardReplacementBoundary
      (by native_decide) (by native_decide)
      hReplacementEquality
  have hQuantifierBodyEquality :
      Derives fs_zfc_support_raw_theory [] (
        quantifier_body_position_condition
            (x#420) bodyCode (x#421) ↔ₘ
          quantifier_body_position_condition
            (x#420) standardBodyCode (x#421)) :=
    fs_zfc_support_raw_quantifier_body_iff_of_code_equality
      (x#420) bodyCode standardBodyCode (x#421)
      (set_variable_admissible 420)
      hBodyBoundary hStandardBodyBoundary
      (set_variable_admissible 421)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      hBodyEquality
  have hFollower :
      GodelQuotation.gq_universal_follower_condition
        (fun token => token ∉ replacementTokens) bodyTokens :=
    GodelQuotation.quote_tokens?_universal_followers_avoid_term
      hBodyTokens hReplacementTokens'
  have hSeparation :
      Derives fs_zfc_support_raw_theory [] (
        universal_binder_at_condition
            (x#420) standardBodyCode (x#325) (x#326) ⟶ₘ
          ¬ₘ variable_symbol_occurs_condition
            (x#420) standardReplacementCode) := by
    have hSeparation' :=
      GodelQuotation.standard_token_sequences_universal_binder_separation
        bodyTokens replacementTokens hFollower
        (x#420) (x#325) (x#326)
        (by
          apply reserved_ids_fresh_cons_variable 420
          · intro id hId
            simp only [List.mem_cons, List.not_mem_nil,
              or_false] at hId
            rcases hId with rfl | rfl | rfl <;> decide
          · apply reserved_ids_fresh_cons_variable 325
            · intro id hId
              simp only [List.mem_cons, List.not_mem_nil,
                or_false] at hId
              rcases hId with rfl | rfl | rfl <;> decide
            · apply reserved_ids_fresh_cons_variable 326
              · intro id hId
                simp only [List.mem_cons, List.not_mem_nil,
                  or_false] at hId
                rcases hId with rfl | rfl | rfl <;> decide
              · exact reserved_ids_fresh_nil _)
    exact FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_quotation_occurrence hFormula)
      (by simpa [standardBodyCode, standardReplacementCode] using hSeparation')
  have hNoCapture :
      Derives fs_zfc_support_raw_theory [] (
        variable_symbol_occurs_condition
            (x#420) replacementCode ⟶ₘ
          ¬ₘ quantifier_body_position_condition
            (x#420) bodyCode (x#421)) :=
    fs_zfc_support_raw_no_capture_of_separation
      (x#420) bodyCode standardBodyCode
      replacementCode standardReplacementCode (x#421)
      (set_variable_admissible 420)
      hBodyBoundary hStandardBodyBoundary
      hReplacementBoundary hStandardReplacementBoundary
      (set_variable_admissible 421)
      (by native_decide) (by native_decide) (by native_decide)
      hOccurrenceEquality hQuantifierBodyEquality hSeparation
  have hVariableCollection :
      Derives fs_zfc_support_raw_theory [] (
        (x#420 ∈ₘ varsₘ(replacementCode)) ⟶ₘ
          ((x#420 ∈ₘ VarSymₘ) ∧ₘ
            variable_symbol_occurs_condition
              (x#420) replacementCode)) := by
    have hReplacementUnion :
        Derives GodelQuotation.godel_quotation_theory [] (
          replacementCode ∈ₘ (TermCodeₘ ∪ₘ FormulaCodeₘ)) :=
      GodelQuotation.gq_mem_binary_union_left
        TermCodeₘ FormulaCodeₘ replacementCode
        term_code_set_term_admissible formula_code_set_term_admissible
        hReplacementBoundary.1
        (FirstOrder.Derives.iffElimRight
          (by
            simpa [is_term_code_definition_instance] using
              GodelQuotation.gq_term_code_definition_instance
                replacementCode hReplacementBoundary.1)
          (GodelQuotation.Numbered.quote_term_with?_is_term_code
            GodelQuotation.free_name [] hReplacementQuote))
    have hInversion :=
      GodelQuotation.gq_variable_collection_member_inversion
        replacementCode hReplacementBoundary
        hReplacementUnion
    have hInversionRaw :=
      fs_zfc_support_raw_derives_of_godel_quotation hInversion
    have hAt := FirstOrder.Derives.forall_elim
      (term := x#420) hInversionRaw
    have hNumeralClose (id depth : Nat) :
        Term.closeFreeAt SetSort.set id depth (numₘ(0)) =
          numₘ(0) :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set id depth (numₘ(0))
        (finite_numeral_term_admissible 0).2 (by
          simp [finite_numeral_term_freeSupport])
    have hNumeralOpen (depth : Nat) (term : SetTerm) :
        Term.openAt SetSort.set depth term (numₘ(0)) =
          numₘ(0) :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set depth term (numₘ(0))
        (finite_numeral_term_admissible 0).2
    simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable,
      variable_symbol_occurs_condition,
      hNumeralClose, hNumeralOpen,
      GodelQuotation.Numbered.CodeBoundary.openAt_eq hReplacementBoundary,
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hReplacementBoundary,
      GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
        hReplacementBoundary] using hAt
  have hReplacementFresh421 :
      (SetSort.set, 421) ∉ Term.freeSupport replacementCode := by
    rw [hReplacementBoundary.2]
    exact List.not_mem_nil
  have hAllVariables :=
    fs_zfc_support_raw_substitutable_no_capture_of_implications
      boundCode replacementCode bodyCode
      hBoundBoundary.1
      hReplacementBoundary.1 hBodyBoundary.1
      hReplacementFresh421
      hVariableCollection hNoCapture
  have hBasic :
      Derives fs_zfc_support_raw_theory [] (
        ((boundCode ∈ₘ VarSymₘ) ∧ₘ
          (term_codeₘ(replacementCode) ∧ₘ formula_codeₘ(bodyCode)))) := by
    exact FirstOrder.Derives.conjIntro hBoundMember
      (FirstOrder.Derives.conjIntro
        hReplacementTermCode hBodyFormulaCode)
  have hCondition :
      Derives fs_zfc_support_raw_theory [] (
        substitutable_condition boundCode replacementCode bodyCode) := by
    simpa [substitutable_condition] using
      (FirstOrder.Derives.conjIntro hBasic hAllVariables)
  have hSubstitable :
      Derives fs_zfc_support_raw_theory [] (
        substitutableₘ(boundCode, replacementCode, bodyCode)) :=
    fs_zfc_support_raw_substitutable_of_condition
      boundCode replacementCode bodyCode
      hBoundBoundary hReplacementBoundary hBodyBoundary hCondition
  have hCloseCode (code : SetTerm)
      (hCode : GodelQuotation.Numbered.CodeBoundary code)
      (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth code = code :=
    GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq hCode id depth
  have hOpenCode (code : SetTerm)
      (hCode : GodelQuotation.Numbered.CodeBoundary code)
      (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement code = code :=
    GodelQuotation.Numbered.CodeBoundary.openAt_eq hCode depth replacement
  have hSubstituteCode (code : SetTerm)
      (hCode : GodelQuotation.Numbered.CodeBoundary code)
      (id : Nat) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement code = code :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq hCode id replacement
  let code : SetTerm :=
    imp_codeₘ(
      eq_codeₘ(boundCode, replacementCode),
      imp_codeₘ(bodyCode, targetCode))
  have hSubstitutionTargetAdmissible :
      Term.Admissible
        (subst_codeₘ(bodyCode, boundCode, replacementCode)) SetSort.set :=
    code_substitution_term_admissible
      bodyCode boundCode replacementCode
      hBodyBoundary.1 hBoundBoundary.1 hReplacementBoundary.1
  have hEqualityCode :
      Term.Admissible (eq_codeₘ(boundCode, replacementCode)) SetSort.set :=
    equality_formula_code_term_admissible
      boundCode replacementCode hBoundBoundary.1 hReplacementBoundary.1
  have hInnerTargetCode :
      Term.Admissible (imp_codeₘ(bodyCode, targetCode)) SetSort.set :=
    implication_formula_code_term_admissible
      bodyCode targetCode hBodyBoundary.1 hTargetBoundary.1
  have hInnerSubstitutionCode :
      Term.Admissible
        (imp_codeₘ(bodyCode, subst_codeₘ(bodyCode, boundCode, replacementCode)))
        SetSort.set :=
    implication_formula_code_term_admissible
      bodyCode (subst_codeₘ(bodyCode, boundCode, replacementCode))
      hBodyBoundary.1 hSubstitutionTargetAdmissible
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      implication_formula_code_term_admissible
        (eq_codeₘ(boundCode, replacementCode))
        (imp_codeₘ(bodyCode, targetCode))
        hEqualityCode hInnerTargetCode
  have hCodeClosed :
      Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hBoundBoundary.2, hReplacementBoundary.2,
      hBodyBoundary.2, hTargetBoundary.2]
  have hInnerEquality :
      Derives fs_zfc_support_raw_theory [] (
        imp_codeₘ(bodyCode, targetCode) ≐ₘ
          imp_codeₘ(bodyCode,
            subst_codeₘ(bodyCode, boundCode, replacementCode))) :=
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      (fun left right => imp_codeₘ(left, right))
      (fun left right hLeft hRight =>
        implication_formula_code_term_admissible left right hLeft hRight)
      (by intros; simp [Term.substituteFree])
      bodyCode bodyCode targetCode
        (subst_codeₘ(bodyCode, boundCode, replacementCode))
      hBodyBoundary.1 hBodyBoundary.1
      hTargetBoundary.1 hSubstitutionTargetAdmissible
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) bodyCode)
      hSubstitutionEquality
  have hSchemaEquality :
      Derives fs_zfc_support_raw_theory [] (
        code ≐ₘ
          equality_substitution_axiom_code_term
            boundCode replacementCode bodyCode) :=
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      (fun left right => imp_codeₘ(left, right))
      (fun left right hLeft hRight =>
        implication_formula_code_term_admissible left right hLeft hRight)
      (by intros; simp [Term.substituteFree])
      (eq_codeₘ(boundCode, replacementCode))
        (eq_codeₘ(boundCode, replacementCode))
        (imp_codeₘ(bodyCode, targetCode))
        (imp_codeₘ(bodyCode,
          subst_codeₘ(bodyCode, boundCode, replacementCode)))
      hEqualityCode hEqualityCode
      hInnerTargetCode hInnerSubstitutionCode
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set)
        (eq_codeₘ(boundCode, replacementCode)))
      hInnerEquality
  have hEqualityDefinition :
      Derives fs_zfc_support_raw_theory [] (
        equality_axiom_schema_definition_axiom) := by
    apply fs_zfc_support_raw_derives_of_logical_rules
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inr (Or.inr (Or.inl rfl))
  have hEqualitySubstitutionDefinition :=
    FirstOrder.Derives.conjElimLeft hEqualityDefinition
  have hEqualitySubstitutionInstance :=
    FirstOrder.Derives.forall_elim
      (term := code) hEqualitySubstitutionDefinition
  have hEqualityIff :
      Derives fs_zfc_support_raw_theory [] (
        (code ∈ₘ EqualitySubstAxiomsₘ) ↔ₘ
          equality_substitution_axiom_condition code) := by
    simpa [code, equality_substitution_axiom_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable, set_bound_variable,
      hOpenCode code ⟨hCode, hCodeClosed⟩,
      hCloseCode code ⟨hCode, hCodeClosed⟩] using
      hEqualitySubstitutionInstance
  let conditionBody : SetFormula :=
    (((((x#440 ∈ₘ VarSymₘ) ∧ₘ (x#441 ∈ₘ VarSymₘ)) ∧ₘ
        formula_codeₘ(x#442)) ∧ₘ
      substitutableₘ(x#440, x#441, x#442)) ∧ₘ
      (code ≐ₘ
        equality_substitution_axiom_code_term
          (x#440) (x#441) (x#442)))
  have hConditionBodyActual :
      Derives fs_zfc_support_raw_theory [] (
        (((((boundCode ∈ₘ VarSymₘ) ∧ₘ
              (replacementCode ∈ₘ VarSymₘ)) ∧ₘ
            formula_codeₘ(bodyCode)) ∧ₘ
          substitutableₘ(boundCode, replacementCode, bodyCode)) ∧ₘ
          (code ≐ₘ
            equality_substitution_axiom_code_term
              boundCode replacementCode bodyCode))) := by
    exact FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjIntro
          (FirstOrder.Derives.conjIntro
            hBoundMember hReplacementMember)
          hBodyFormulaCode)
        hSubstitable)
      hSchemaEquality
  have hConditionBodySubstitute :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 442 bodyCode
          (Formula.substituteFree SetSort.set 441 replacementCode
            (Formula.substituteFree SetSort.set 440 boundCode
              conditionBody))) := by
    simpa [conditionBody, code, Formula.substituteFree,
      Term.substituteFree, set_variable, set_bound_variable,
      hCodeClosed, hSubstituteCode boundCode hBoundBoundary,
      hSubstituteCode replacementCode hReplacementBoundary,
      hSubstituteCode bodyCode hBodyBoundary,
      hSubstituteCode code ⟨hCode, hCodeClosed⟩] using
      hConditionBodyActual
  have hConditionBody :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, 440],
          ∃ₘ[SetSort.set, 441],
            ∃ₘ[SetSort.set, 442], conditionBody) :=
    fs_zfc_support_raw_exists_three_of_substituted
      conditionBody 440 441 442
      boundCode replacementCode bodyCode
      hBoundBoundary hReplacementBoundary hBodyBoundary
      (by decide) (by decide) (by decide)
      hConditionBodySubstitute
  have hCondition :
      Derives fs_zfc_support_raw_theory [] (
        equality_substitution_axiom_condition code) := by
    simpa [equality_substitution_axiom_condition, conditionBody] using
      hConditionBody
  have hMember :
      Derives fs_zfc_support_raw_theory [] (
        code ∈ₘ EqualitySubstAxiomsₘ) :=
    FirstOrder.Derives.iffElimLeft hEqualityIff hCondition
  have hBase :
      Derives fs_zfc_support_raw_theory [] (
        base_logical_axiom_condition code) :=
    fs_zfc_support_raw_base_logical_condition_of_member
      code hCode (by
        simp [fs_zfc_support_raw_base_logical_axiom_branches]) hMember
  have hLogical :=
    fs_zfc_support_raw_logical_axiom_code_of_base_condition
      code hCode hCodeClosed hBase
  have hBodyHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize
            SetSort.set body) =
        some bodyCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using hBodyQuote
  have hTargetHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize
            SetSort.set target) =
        some targetCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using hTargetQuote
  have hWholeQuote :
      GodelQuotation.Numbered.quote?
          ((Formula.imp
            (Formula.equal leftTerm rightTerm)
            (Formula.imp body target)) : SetFormula) =
        some code := by
    change
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize SetSort.set
            (Formula.imp
              (Formula.equal leftTerm rightTerm)
              (Formula.imp body target))) =
        some code
    simp [code,
      GodelQuotation.Numbered.quote_hilbert_with?,
      Formula.hilbertize, hBoundTermQuote, hReplacementQuote,
      hBodyHilbertQuote, hTargetHilbertQuote]
  have hCanonicalSubstitutable :
      Derives fs_zfc_support_raw_theory [] (
        substitutableₘ(
          var_codeₘ(numₘ(2 * leftId)),
          var_codeₘ(numₘ(2 * rightId)),
          fs_zfc_formula_code_term body)) := by
    simpa [boundCode, replacementCode,
      GodelQuotation.free_name, fs_zfc_formula_code_term,
      hBodyQuote] using hSubstitable
  exact ⟨code, hWholeQuote, hLogical, hCanonicalSubstitutable⟩

/-- 恒等律的 quotation 直接落在对象层恒等律公理码上。 -/
theorem fs_zfc_support_raw_equality_reflexivity_axiom_code_exists
    (id : FreeVarId) :
    ∃ code,
      GodelQuotation.Numbered.quote?
          ((Formula.equal
            (Term.var (.fvar SetSort.set id))
            (Term.var (.fvar SetSort.set id))) : SetFormula) =
        some code ∧
      Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code) := by
  let termCode : SetTerm :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.free_name id)
  have hTermQuote :
      GodelQuotation.Numbered.quote_term_with?
          GodelQuotation.free_name []
            (Term.var (.fvar SetSort.set id) : SetTerm) =
        some termCode := by
    simp [termCode, GodelQuotation.Numbered.quote_term_with?]
  have hTermBoundary :=
    GodelQuotation.Numbered.quote_term_with?_code_boundary
      GodelQuotation.free_name [] hTermQuote
  let code : SetTerm :=
    equality_reflexivity_axiom_code_term termCode
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      equality_reflexivity_axiom_code_term_admissible
        termCode hTermBoundary.1
  have hTermCodeClosed :
      Term.freeSupport termCode = [] := by
    simp [termCode, GodelQuotation.Numbered.named_variable_code]
  have hCodeClosed :
      Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hTermCodeClosed]
  have hTermCloseAt (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth termCode =
        termCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth termCode hTermBoundary.1.2 (by
        rw [hTermBoundary.2]
        exact List.not_mem_nil)
  have hTermSubstitute :
      Term.substituteFree SetSort.set 443 termCode termCode =
        termCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 443 termCode termCode (by
        rw [hTermBoundary.2]
        exact List.not_mem_nil)
  have hCodeSubstitute :
      Term.substituteFree SetSort.set 443 termCode code =
        code :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 443 termCode code (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hDefinition :
      Derives fs_zfc_support_raw_theory [] (
        equality_axiom_schema_definition_axiom) := by
    apply fs_zfc_support_raw_derives_of_logical_rules
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inr (Or.inr (Or.inl rfl))
  have hReflexivityDefinition :=
    FirstOrder.Derives.conjElimRight hDefinition
  have hReflexivityInstance :=
    FirstOrder.Derives.forall_elim
      (term := code) hReflexivityDefinition
  have hReflexivityIff :
      Derives fs_zfc_support_raw_theory [] (
        (code ∈ₘ EqualityReflAxiomsₘ) ↔ₘ
          equality_reflexivity_axiom_condition code) := by
    simpa [code, equality_reflexivity_axiom_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable,
      GodelQuotation.Numbered.named_variable_code,
      hTermCloseAt] using
      hReflexivityInstance
  have hTermMember :
      Derives fs_zfc_support_raw_theory [] (
        termCode ∈ₘ VarSymₘ) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.named_variable_code_mem_variable_symbols
        (GodelQuotation.free_name id))
  let body : SetFormula :=
    (x#443 ∈ₘ VarSymₘ) ∧ₘ
      (code ≐ₘ equality_reflexivity_axiom_code_term (x#443))
  have hBody :
      Derives fs_zfc_support_raw_theory [] (
        (termCode ∈ₘ VarSymₘ) ∧ₘ
          (code ≐ₘ equality_reflexivity_axiom_code_term termCode)) := by
    apply FirstOrder.Derives.conjIntro
    · exact hTermMember
    · exact FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) code
  have hBodySubstitute :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 443 termCode body) := by
    simpa [body, Formula.substituteFree,
      Term.substituteFree, set_variable, code,
      hTermSubstitute, hCodeSubstitute,
      GodelQuotation.Numbered.named_variable_code,
      hTermCloseAt] using
      hBody
  have hConditionBody :=
    fs_zfc_support_raw_exists_one_of_substituted
      body 443 termCode hTermBoundary hBodySubstitute
  have hCondition :
      Derives fs_zfc_support_raw_theory [] (
        equality_reflexivity_axiom_condition code) := by
    simpa [equality_reflexivity_axiom_condition, body, code,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable,
      GodelQuotation.Numbered.named_variable_code,
      hTermCloseAt] using
      hConditionBody
  have hMember :
      Derives fs_zfc_support_raw_theory [] (
        code ∈ₘ EqualityReflAxiomsₘ) :=
    FirstOrder.Derives.iffElimLeft hReflexivityIff hCondition
  have hBaseAdmissible :
      Formula.Admissible (base_logical_axiom_condition code) :=
    base_logical_axiom_condition_admissible code hCode
  let tail11 : SetFormula :=
    (code ∈ₘ EqualitySubstAxiomsₘ) ∨ₘ
      (code ∈ₘ EqualityReflAxiomsₘ)
  let tail10 : SetFormula :=
    (code ∈ₘ VacuousForallAxiomsₘ) ∨ₘ tail11
  let tail9 : SetFormula :=
    (code ∈ₘ ForallDistribAxiomsₘ) ∨ₘ tail10
  let tail8 : SetFormula :=
    (code ∈ₘ SpecializationAxiomsₘ) ∨ₘ tail9
  let tail7 : SetFormula :=
    (code ∈ₘ CaseAnalysisAxiomsₘ) ∨ₘ tail8
  let tail6 : SetFormula :=
    (code ∈ₘ ExplosionAxiomsₘ) ∨ₘ tail7
  let tail5 : SetFormula :=
    (code ∈ₘ ClassicalAxiomsₘ) ∨ₘ tail6
  let tail4 : SetFormula :=
    (code ∈ₘ ContradictionAxiomsₘ) ∨ₘ tail5
  let tail3 : SetFormula :=
    (code ∈ₘ WeakeningAxiomsₘ) ∨ₘ tail4
  let tail2 : SetFormula :=
    (code ∈ₘ SelfImpAxiomsₘ) ∨ₘ tail3
  let tail1 : SetFormula :=
    (code ∈ₘ ImpDistribAxiomsₘ) ∨ₘ tail2
  have hRight1 := Formula.Admissible.disj_right hBaseAdmissible
  have hRight2 := Formula.Admissible.disj_right hRight1
  have hRight3 := Formula.Admissible.disj_right hRight2
  have hRight4 := Formula.Admissible.disj_right hRight3
  have hRight5 := Formula.Admissible.disj_right hRight4
  have hRight6 := Formula.Admissible.disj_right hRight5
  have hRight7 := Formula.Admissible.disj_right hRight6
  have hRight8 := Formula.Admissible.disj_right hRight7
  have hRight9 := Formula.Admissible.disj_right hRight8
  have hRight10 := Formula.Admissible.disj_right hRight9
  have hTail11 :
      Derives fs_zfc_support_raw_theory [] tail11 := by
    dsimp [tail11]
    exact FirstOrder.Derives.disjIntroRight hMember
  have hTail10 :
      Derives fs_zfc_support_raw_theory [] tail10 := by
    dsimp [tail10]
    exact FirstOrder.Derives.disjIntroRight hTail11
  have hTail9 :
      Derives fs_zfc_support_raw_theory [] tail9 := by
    dsimp [tail9]
    exact FirstOrder.Derives.disjIntroRight hTail10
  have hTail8 :
      Derives fs_zfc_support_raw_theory [] tail8 := by
    dsimp [tail8]
    exact FirstOrder.Derives.disjIntroRight hTail9
  have hTail7 :
      Derives fs_zfc_support_raw_theory [] tail7 := by
    dsimp [tail7]
    exact FirstOrder.Derives.disjIntroRight hTail8
  have hTail6 :
      Derives fs_zfc_support_raw_theory [] tail6 := by
    dsimp [tail6]
    exact FirstOrder.Derives.disjIntroRight hTail7
  have hTail5 :
      Derives fs_zfc_support_raw_theory [] tail5 := by
    dsimp [tail5]
    exact FirstOrder.Derives.disjIntroRight hTail6
  have hTail4 :
      Derives fs_zfc_support_raw_theory [] tail4 := by
    dsimp [tail4]
    exact FirstOrder.Derives.disjIntroRight hTail5
  have hTail3 :
      Derives fs_zfc_support_raw_theory [] tail3 := by
    dsimp [tail3]
    exact FirstOrder.Derives.disjIntroRight hTail4
  have hTail2 :
      Derives fs_zfc_support_raw_theory [] tail2 := by
    dsimp [tail2]
    exact FirstOrder.Derives.disjIntroRight hTail3
  have hTail1 :
      Derives fs_zfc_support_raw_theory [] tail1 := by
    dsimp [tail1]
    exact FirstOrder.Derives.disjIntroRight hTail2
  have hBase :
      Derives fs_zfc_support_raw_theory [] (
        base_logical_axiom_condition code) := by
    simpa [base_logical_axiom_condition, tail1, tail2, tail3,
      tail4, tail5, tail6, tail7, tail8, tail9, tail10, tail11] using
      hTail1
  have hLogical :=
    fs_zfc_support_raw_logical_axiom_code_of_base_condition
      code hCode hCodeClosed hBase
  have hWholeQuote :
      GodelQuotation.Numbered.quote?
          ((Formula.equal
            (Term.var (.fvar SetSort.set id))
            (Term.var (.fvar SetSort.set id))) : SetFormula) =
        some code := by
    simp [code, termCode,
      GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?,
      GodelQuotation.Numbered.quote_hilbert_with?,
      Formula.hilbertize, hTermQuote,
      GodelQuotation.Numbered.named_variable_code]
  exact ⟨code, hWholeQuote, hLogical⟩

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
