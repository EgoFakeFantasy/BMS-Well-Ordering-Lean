import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.Core

/-!
# 有限序列空间的对象层消去

本模块把有限序列空间定义中的映射见证消去为公共的有限序列条件。
目标集只在展开 `seq_spaceₘ` 定义时需要非空；从映射见证恢复函数性与有限定义域
本身不依赖目标集的其他性质。
-/

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/--
有限序列成员条件中的映射见证给出函数性和自然数定义域。
这是从任意值域上的有限映射恢复 `finite_sequence_condition` 的核心消去接口。
-/
theorem finite_sequence_member_condition_implies_finite_sequence
    (target sequence : SetTerm)
    (hTarget : Term.Admissible target SetSort.set)
    (hSequence : Term.Admissible sequence SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory]
      finite_sequence_member_condition target sequence ⟶ₘ
        finite_sequence_condition sequence := by
  let conclusion : SetFormula :=
    finite_sequence_condition sequence
  let freshnessBasis : List SetFormula :=
    [conclusion, target ≐ₘ target, sequence ≐ₘ sequence]
  let witnessId : FreeVarId :=
    FreshVariable.fresh_id SetSort.set freshnessBasis
  let witness : SetTerm := x#witnessId
  let witnessCondition : SetFormula :=
    (witness ∈ₘ ωₘ) ∧ₘ
      is_mapping_formula sequence witness target
  have hWitness :
      Term.Admissible witness SetSort.set := by
    simpa [witness] using
      set_variable_admissible witnessId
  have hWitnessFreshTarget :
      (SetSort.set, witnessId) ∉
        Term.freeSupport target := by
    dsimp [witnessId, freshnessBasis]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m
        (sort := SetSort.set)
        (formulas := [
          conclusion, target ≐ₘ target,
          sequence ≐ₘ sequence])
        (formula := target ≐ₘ target)
        (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hWitnessFreshSequence :
      (SetSort.set, witnessId) ∉
        Term.freeSupport sequence := by
    dsimp [witnessId, freshnessBasis]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m
        (sort := SetSort.set)
        (formulas := [
          conclusion, target ≐ₘ target,
          sequence ≐ₘ sequence])
        (formula := sequence ≐ₘ sequence)
        (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hWitnessFreshConclusion :
      (SetSort.set, witnessId) ∉
        Formula.freeSupport conclusion := by
    dsimp [witnessId, freshnessBasis]
    exact
      FreshVariable.fresh_id_not_mem_m
        (sort := SetSort.set)
        (formulas := [
          conclusion, target ≐ₘ target,
          sequence ≐ₘ sequence])
        (formula := conclusion)
        (by simp)
  have hWitnessCloseTarget :
      Term.closeFreeAt SetSort.set witnessId 0 target =
        target :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set witnessId 0 target
      hTarget.2 hWitnessFreshTarget
  have hWitnessCloseSequence :
      Term.closeFreeAt SetSort.set witnessId 0 sequence =
        sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set witnessId 0 sequence
      hSequence.2 hWitnessFreshSequence
  have hPoint :
      ⊢ₘ[standard_sequence_semantics_theory]
        witnessCondition ⟶ₘ conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature := [witnessCondition]
    have hWitnessCondition :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          witnessCondition :=
      FirstOrder.Derives.assumption (by simp [Γ])
    have hWitnessOmega :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          witness ∈ₘ ωₘ :=
      FirstOrder.Derives.conjElimLeft hWitnessCondition
    have hMapping :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          is_mapping_formula sequence witness target :=
      FirstOrder.Derives.conjElimRight hWitnessCondition
    have hMappingCondition :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          is_mapping_condition sequence witness target :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp [Γ]) <|
            stdseq_weaken_mapping_predicate <|
              is_mapping_implies_condition
                sequence witness target
                hSequence hWitness hTarget)
        hMapping
    have hFunction :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          is_function_formula sequence :=
      FirstOrder.Derives.conjElimLeft hMappingCondition
    have hDomainEquality :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          witness ≐ₘ domₘ(sequence) :=
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight
          hMappingCondition
    have hDomainOmega :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          domₘ(sequence) ∈ₘ ωₘ :=
      FirstOrder.Derives.iffElimRight
        (membership_left_iff_of_equality
          witness (domₘ(sequence)) ωₘ
          hWitness
          (domain_term_admissible sequence hSequence)
          omega_term_admissible
          hDomainEquality)
        hWitnessOmega
    simpa [conclusion, finite_sequence_condition] using
      FirstOrder.Derives.conjIntro
        hFunction hDomainOmega
  have hTheoryFresh :
      ∀ formula, standard_sequence_semantics_theory formula →
        (SetSort.set, witnessId) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    rw [(standard_sequence_semantics_theory_sentence
      hFormula).2]
    exact List.not_mem_nil
  have hLift :=
    Metatheory.Derives.exists_imp_of_imp
      (T := standard_sequence_semantics_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := witnessId)
      hTheoryFresh
      (by
        intro formula hFormula
        cases hFormula)
      hWitnessFreshConclusion
      hPoint
  simpa [finite_sequence_member_condition,
    witnessCondition, witness, conclusion,
    Formula.closeFreeAt, Term.closeFreeAt,
    set_variable, set_bound_variable,
    hWitnessCloseTarget, hWitnessCloseSequence] using hLift

/--
非空目标集上的序列空间成员满足其有限映射成员条件。
该定理只展开 `seq_spaceₘ` 的对象层定义合同，不提前投影见证的任何分量。
-/
theorem sequence_space_member_implies_member_condition
    (target sequence : SetTerm)
    (hTarget : Term.Admissible target SetSort.set)
    (hSequence : Term.Admissible sequence SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory]
      (target ≠ₘ ∅ₘ) ⟶ₘ
        ((sequence ∈ₘ seq_spaceₘ(target)) ⟶ₘ
          finite_sequence_member_condition target sequence) := by
  let sequenceSpace : SetTerm := seq_spaceₘ(target)
  let nonempty : SetFormula := target ≠ₘ ∅ₘ
  let membership : SetFormula :=
    sequence ∈ₘ sequenceSpace
  have hSequenceSpace :
      Term.Admissible sequenceSpace SetSort.set := by
    simpa [sequenceSpace] using
      finite_sequence_space_term_admissible
        target hTarget
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [membership, nonempty]
  have hNonempty :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        target ≠ₘ ∅ₘ := by
    simpa [nonempty] using
      (FirstOrder.Derives.assumption
        (T := standard_sequence_semantics_theory)
        (Γ := Γ) (φ := nonempty) (by simp [Γ]))
  have hMembership :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        sequence ∈ₘ sequenceSpace := by
    simpa [membership] using
      (FirstOrder.Derives.assumption
        (T := standard_sequence_semantics_theory)
        (Γ := Γ) (φ := membership) (by simp [Γ]))
  have hContract :=
    stdseq_weaken_finite_sequence_space <|
      finite_sequence_space_definition_instance_derives
        target sequenceSpace hTarget hSequenceSpace
  have hSpaceIff :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        (sequenceSpace ≐ₘ seq_spaceₘ(target)) ↔ₘ
          finite_sequence_space_spec
            target sequenceSpace :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
          simpa [sequenceSpace] using hContract)
      hNonempty
  have hSpaceSpec :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        finite_sequence_space_spec
          target sequenceSpace :=
    FirstOrder.Derives.iffElimRight
      hSpaceIff <|
        FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) sequenceSpace
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := sequence) hSpaceSpec
  have hTargetOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term target =
        target :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term target hTarget.2
  have hSequenceSpaceOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term sequenceSpace =
        sequenceSpace :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term sequenceSpace
      hSequenceSpace.2
  have hAt :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        (sequence ∈ₘ sequenceSpace) ↔ₘ
          finite_sequence_member_condition
            target sequence := by
    simpa [finite_sequence_space_spec,
      finite_sequence_member_condition,
      Formula.openAt, Formula.next_depth,
      Term.openAt, hTargetOpen,
      hSequenceSpaceOpen] using hAtRaw
  exact FirstOrder.Derives.iffElimRight
    hAt hMembership

/--
非空目标集上的任意有限序列空间成员都是有限序列。
非空性只用于启用空间定义合同，结论不携带额外的值域强度。
-/
theorem sequence_space_member_implies_finite_sequence
    (target sequence : SetTerm)
    (hTarget : Term.Admissible target SetSort.set)
    (hSequence : Term.Admissible sequence SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory]
      (target ≠ₘ ∅ₘ) ⟶ₘ
        ((sequence ∈ₘ seq_spaceₘ(target)) ⟶ₘ
          finite_sequence_condition sequence) := by
  have hMember :=
    sequence_space_member_implies_member_condition
      target sequence hTarget hSequence
  have hFinite :=
    finite_sequence_member_condition_implies_finite_sequence
      target sequence hTarget hSequence
  derive_prop

end YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation
