import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceDomainSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceMappingSemantics
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure

/-!
# 内在有限序列空间语义

本模块把普通有限序列空间与非空有限序列空间的定义公理接到内在项接口。所有实例化
都通过 typed substitution 完成；后续成员消去只消费这里的最小理论合同。
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

/-- 有限序列空间语义所需的最小对象理论合同。 -/
structure FiniteSequenceSpaceSupport (T : SetTheory)
    extends FiniteSequenceEvaluationSupport T where
  contains_finite_sequence_space :
    ∀ {sentence}, finite_sequence_space_theory sentence → T sentence
  contains_nonempty_finite_sequence_space :
    ∀ {sentence}, nonempty_finite_sequence_space_theory sentence → T sentence

namespace FiniteSequenceSpaceSupport

/-- 有限序列空间支撑沿理论包含直接提升。 -/
theorem theory_weaken
    {T U : SetTheory}
    (S : FiniteSequenceSpaceSupport T)
    (hTU : Theory.Extends U T) :
    FiniteSequenceSpaceSupport U where
  toFiniteSequenceEvaluationSupport :=
    S.toFiniteSequenceEvaluationSupport.theory_weaken hTU
  contains_finite_sequence_space := fun hSentence =>
    hTU (S.contains_finite_sequence_space hSentence)
  contains_nonempty_finite_sequence_space := fun hSentence =>
    hTU (S.contains_nonempty_finite_sequence_space hSentence)

theorem weaken_finite_sequence_space
    {T : SetTheory} (S : FiniteSequenceSpaceSupport T)
    {sentence : SetSentence}
    (hSentence : finite_sequence_space_theory sentence) :
    T sentence :=
  S.contains_finite_sequence_space hSentence

theorem weaken_nonempty_finite_sequence_space
    {T : SetTheory} (S : FiniteSequenceSpaceSupport T)
    {sentence : SetSentence}
    (hSentence : nonempty_finite_sequence_space_theory sentence) :
    T sentence :=
  S.contains_nonempty_finite_sequence_space hSentence

end FiniteSequenceSpaceSupport

/-- 普通有限序列空间定义公理在任意内在开放项上直接实例化。 -/
theorem intrinsic_finite_sequence_space_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (source candidate : SetOpenTerm free) :
    Γ ⊢ₘ[finite_sequence_space_theory]
      finite_sequence_space_definition_instance source candidate := by
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    finite_sequence_space_definition_instance
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons candidate
      (VariableSubstitution.cons source VariableSubstitution.empty)
  have hClosed :
      ([] : Context signature []) ⊢ₘ[finite_sequence_space_theory]
        Formula.fromSentence (Metatheory.Formula.forall_close body) := by
    have hAxiom :
        ([] : Context signature []) ⊢ₘ[finite_sequence_space_theory]
          Formula.fromSentence finite_sequence_space_definition_axiom :=
      FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
    simpa [finite_sequence_space_definition_axiom, body] using hAxiom
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, finite_sequence_space_definition_instance,
    finite_sequence_space_spec, finite_sequence_member_condition,
    membership_specification,
    set_variable, set_bound_variable,
    finite_numeral_term, Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons,
    VariableSubstitution.empty, VariableSubstitution.freeId,
    VariableSubstitution.boundId, VariableSubstitution.weakenBound,
    VariableSubstitution.liftFree, Context.substituteFree,
    FreshVariable.extendContext] using hInstance

/-- 非空有限序列空间定义公理在任意内在开放项上直接实例化。 -/
theorem intrinsic_nonempty_finite_sequence_space_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (source candidate : SetOpenTerm free) :
    Γ ⊢ₘ[nonempty_finite_sequence_space_theory]
      nonempty_finite_sequence_space_definition_instance source candidate := by
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    nonempty_finite_sequence_space_definition_instance
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons candidate
      (VariableSubstitution.cons source VariableSubstitution.empty)
  have hClosed :
      ([] : Context signature []) ⊢ₘ[nonempty_finite_sequence_space_theory]
        Formula.fromSentence (Metatheory.Formula.forall_close body) := by
    have hAxiom :
        ([] : Context signature []) ⊢ₘ[nonempty_finite_sequence_space_theory]
          Formula.fromSentence nonempty_finite_sequence_space_definition_axiom :=
      FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
    simpa [nonempty_finite_sequence_space_definition_axiom, body] using hAxiom
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, nonempty_finite_sequence_space_definition_instance,
    nonempty_finite_sequence_space_spec,
    nonempty_finite_sequence_member_condition,
    membership_specification,
    set_variable, set_bound_variable,
    finite_numeral_term, Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons,
    VariableSubstitution.empty, VariableSubstitution.freeId,
    VariableSubstitution.boundId, VariableSubstitution.weakenBound,
    VariableSubstitution.liftFree, Context.substituteFree,
    FreshVariable.extendContext] using hInstance

/-- 普通有限序列空间成员与有限映射成员条件之间的规范等价。 -/
theorem sequence_space_member_iff_member_condition
    {T : SetTheory} (S : FiniteSequenceSpaceSupport T)
    {free : SetContext} {Γ : Context signature free}
    (source sequence : SetOpenTerm free)
    (hNonempty : Γ ⊢ₘ[T] source ≠ₘ ∅ₘ) :
    Γ ⊢ₘ[T]
      (sequence ∈ₘ seq_spaceₘ(source)) ↔ₘ
        finite_sequence_member_condition source sequence := by
  have hContract : Γ ⊢ₘ[T]
      finite_sequence_space_definition_instance
        source (seq_spaceₘ(source)) :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_finite_sequence_space hSentence)
      (intrinsic_finite_sequence_space_definition_instance_derives
        (Γ := Γ) source (seq_spaceₘ(source)))
  have hSpaceIff : Γ ⊢ₘ[T]
      (seq_spaceₘ(source) ≐ₘ seq_spaceₘ(source)) ↔ₘ
        finite_sequence_space_spec source (seq_spaceₘ(source)) :=
    FirstOrder.Derives.imp_elim hContract hNonempty
  have hSpaceSpec : Γ ⊢ₘ[T]
      finite_sequence_space_spec source (seq_spaceₘ(source)) :=
    FirstOrder.Derives.iff_elim_left hSpaceIff
      (Metatheory.Derives.equality_refl
        (T := T) (Γ := Γ) (seq_spaceₘ(source)))
  have hAtRaw := FirstOrder.Derives.forall_elim
    (term := sequence) hSpaceSpec
  simpa [finite_sequence_space_spec, finite_sequence_member_condition,
    membership_specification, Formula.instantiateFreeTop,
    Substitution.instantiateFreeTop, Formula.substitute,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.liftFree, VariableSubstitution.weakenBound,
    VariableSubstitution.boundId, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_instantiateFreeTop,
    Arguments.substituteMapped_weakenFree_instantiateFreeTop] using hAtRaw

/-- 普通有限序列空间成员反演为有限映射成员条件。 -/
theorem sequence_space_member_implies_member_condition
    {T : SetTheory} (S : FiniteSequenceSpaceSupport T)
    {free : SetContext} {Γ : Context signature free}
    (source sequence : SetOpenTerm free)
    (hNonempty : Γ ⊢ₘ[T] source ≠ₘ ∅ₘ)
    (hMembership : Γ ⊢ₘ[T] sequence ∈ₘ seq_spaceₘ(source)) :
    Γ ⊢ₘ[T] finite_sequence_member_condition source sequence :=
  FirstOrder.Derives.iff_elim_left
    (sequence_space_member_iff_member_condition
      S source sequence hNonempty)
    hMembership

/-- 标准有限图由长度的 `ω` 证书和值域逐项证书直接满足有限序列成员条件。 -/
theorem standard_sequence_member_condition_intro
    {T : SetTheory} (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (elements : List (SetOpenTerm free))
    (target : SetOpenTerm free)
    (hLengthOmega : Γ ⊢ₘ[T] numₘ(elements.length) ∈ₘ ωₘ)
    (hTargetMember : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ target) :
    Γ ⊢ₘ[T]
      finite_sequence_member_condition target
        (standard_sequence elements) := by
  let sequence : SetOpenTerm free := standard_sequence elements
  let length : SetOpenTerm free := numₘ(elements.length)
  have hDomain : Γ ⊢ₘ[T]
      length ≐ₘ domₘ(sequence) :=
    Metatheory.Derives.equality_symm <| by
      simpa [sequence, length] using
        standard_sequence_domain_eq
          (Γ := Γ) S.toFiniteSequenceGraphSupport
          (elements := elements)
  have hMapping : Γ ⊢ₘ[T]
      is_mapping_formula sequence length target := by
    simpa [sequence, length] using
      standard_sequence_from_is_mapping
        (Γ := Γ) S 0 (elements := elements)
        length target hDomain hTargetMember
  apply FirstOrder.Derives.exists_intro length
  rw [Formula.instantiateTop_abstractFreeTop,
    Formula.instantiateFreeTop_conj,
    Formula.instantiateFreeTop_rel,
    Formula.instantiateFreeTop_rel]
  repeat
    first
    | rw [Arguments.instantiateFreeTop_cons]
    | rw [Arguments.instantiateFreeTop_nil]
    | rw [Term.instantiateFreeTop_fvar_here]
    | rw [Term.instantiateFreeTop_app]
    | rw [Term.instantiateFreeTop_weakenFree]
  exact FirstOrder.Derives.conj_intro hLengthOmega hMapping

/-- 标准有限图直接进入普通有限序列空间。 -/
theorem standard_sequence_mem_sequence_space
    {T : SetTheory} (S : FiniteSequenceSpaceSupport T)
    {free : SetContext} {Γ : Context signature free}
    (elements : List (SetOpenTerm free))
    (target : SetOpenTerm free)
    (hLengthOmega : Γ ⊢ₘ[T] numₘ(elements.length) ∈ₘ ωₘ)
    (hTargetNonempty : Γ ⊢ₘ[T] target ≠ₘ ∅ₘ)
    (hTargetMember : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ target) :
    Γ ⊢ₘ[T]
      standard_sequence elements ∈ₘ seq_spaceₘ(target) :=
  FirstOrder.Derives.iff_elim_right
    (sequence_space_member_iff_member_condition
      S target (standard_sequence elements) hTargetNonempty)
    (standard_sequence_member_condition_intro
      S.toFiniteSequenceEvaluationSupport elements target
      hLengthOmega hTargetMember)

/-- 有限映射成员条件反演为有限序列条件。 -/
theorem finite_sequence_member_condition_implies_finite_sequence
    {T : SetTheory} (S : FiniteSequenceSpaceSupport T)
    {free : SetContext} {Γ : Context signature free}
    (source sequence : SetOpenTerm free)
    (hCondition : Γ ⊢ₘ[T]
      finite_sequence_member_condition source sequence) :
    Γ ⊢ₘ[T] finite_sequence_condition sequence := by
  let length : SetOpenTerm (SetSort.set :: free) := .fvar .here
  let body : SetOpenFormula (SetSort.set :: free) :=
    (length ∈ₘ ωₘ) ∧ₘ
      is_mapping_formula
        (sequence.weakenFree SetSort.set)
        length (source.weakenFree SetSort.set)
  have hImp : FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T]
      body ⟶ₘ (finite_sequence_condition sequence).weakenFree SetSort.set := by
    apply FirstOrder.Derives.imp_intro
    let Δ : Context signature (SetSort.set :: free) :=
      body :: FreshVariable.extendContext SetSort.set Γ
    have hBody : Δ ⊢ₘ[T] body :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hLength : Δ ⊢ₘ[T] length ∈ₘ ωₘ :=
      FirstOrder.Derives.conj_elim_left hBody
    have hMapping : Δ ⊢ₘ[T]
        is_mapping_formula
          (sequence.weakenFree SetSort.set)
          length (source.weakenFree SetSort.set) :=
      FirstOrder.Derives.conj_elim_right hBody
    have hMappingCondition : Δ ⊢ₘ[T]
        is_mapping_condition
          (sequence.weakenFree SetSort.set)
          length (source.weakenFree SetSort.set) :=
      FirstOrder.Derives.imp_elim
        (FirstOrder.Derives.context_weaken
          (Γ := ([] : Context signature (SetSort.set :: free)))
          (Δ := Δ) (by simp [Δ])
          (FirstOrder.Derives.theory_weaken
            (fun hSentence => S.contains_function_application
              (mapping_predicate_theory_subset_function_application_theory
                hSentence))
            (is_mapping_implies_condition
              (Γ := ([] : Context signature (SetSort.set :: free)))
              (sequence.weakenFree SetSort.set)
              length (source.weakenFree SetSort.set))))
        hMapping
    have hFunction : Δ ⊢ₘ[T]
        is_function_formula (sequence.weakenFree SetSort.set) :=
      FirstOrder.Derives.conj_elim_left hMappingCondition
    have hLengthDomain : Δ ⊢ₘ[T]
        length ≐ₘ domₘ(sequence.weakenFree SetSort.set) :=
      FirstOrder.Derives.conj_elim_left
        (FirstOrder.Derives.conj_elim_right hMappingCondition)
    have hDomainOmega : Δ ⊢ₘ[T]
        domₘ(sequence.weakenFree SetSort.set) ∈ₘ ωₘ :=
      FirstOrder.Derives.iff_elim_left
        (membership_left_iff_of_equality
          length (domₘ(sequence.weakenFree SetSort.set)) ωₘ hLengthDomain)
        hLength
    have hResult : Δ ⊢ₘ[T]
        is_function_formula (sequence.weakenFree SetSort.set) ∧ₘ
          (domₘ(sequence.weakenFree SetSort.set) ∈ₘ ωₘ) :=
      FirstOrder.Derives.conj_intro hFunction hDomainOmega
    simpa [body, finite_sequence_condition] using hResult
  have hLift := Metatheory.Derives.exists_imp_of_imp
    (T := T) (Γ := Γ) (sort := SetSort.set) hImp
  exact FirstOrder.Derives.imp_elim
    (by simpa [body, finite_sequence_member_condition, length] using hLift)
    hCondition

/-- 非空有限序列空间成员与普通空间成员及零点定义域条件的规范等价。 -/
theorem nonempty_sequence_space_member_iff_condition
    {T : SetTheory} (S : FiniteSequenceSpaceSupport T)
    {free : SetContext} {Γ : Context signature free}
    (source sequence : SetOpenTerm free)
    (hNonempty : Γ ⊢ₘ[T] source ≠ₘ ∅ₘ) :
    Γ ⊢ₘ[T]
      (sequence ∈ₘ seq₊_spaceₘ(source)) ↔ₘ
        ((sequence ∈ₘ seq_spaceₘ(source)) ∧ₘ
          (numₘ(0) ∈ₘ domₘ(sequence))) := by
  have hContract : Γ ⊢ₘ[T]
      nonempty_finite_sequence_space_definition_instance
        source (seq₊_spaceₘ(source)) :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_nonempty_finite_sequence_space hSentence)
      (intrinsic_nonempty_finite_sequence_space_definition_instance_derives
        (Γ := Γ) source (seq₊_spaceₘ(source)))
  have hSpaceIff : Γ ⊢ₘ[T]
      (seq₊_spaceₘ(source) ≐ₘ seq₊_spaceₘ(source)) ↔ₘ
        nonempty_finite_sequence_space_spec source
          (seq₊_spaceₘ(source)) :=
    FirstOrder.Derives.imp_elim hContract hNonempty
  have hSpaceSpec : Γ ⊢ₘ[T]
      nonempty_finite_sequence_space_spec source
        (seq₊_spaceₘ(source)) :=
    FirstOrder.Derives.iff_elim_left hSpaceIff
      (Metatheory.Derives.equality_refl
        (T := T) (Γ := Γ) (seq₊_spaceₘ(source)))
  have hAtRaw := FirstOrder.Derives.forall_elim
    (term := sequence) hSpaceSpec
  simpa [nonempty_finite_sequence_space_spec,
    nonempty_finite_sequence_member_condition, membership_specification,
    Formula.instantiateFreeTop, Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.liftFree, VariableSubstitution.weakenBound,
    VariableSubstitution.boundId, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_instantiateFreeTop,
    Arguments.substituteMapped_weakenFree_instantiateFreeTop] using hAtRaw

/-- 非空有限序列空间成员反演为普通有限序列空间成员。 -/
theorem nonempty_sequence_space_member_implies_sequence_space
    {T : SetTheory} (S : FiniteSequenceSpaceSupport T)
    {free : SetContext} {Γ : Context signature free}
    (source sequence : SetOpenTerm free)
    (hNonempty : Γ ⊢ₘ[T] source ≠ₘ ∅ₘ)
    (hMembership : Γ ⊢ₘ[T] sequence ∈ₘ seq₊_spaceₘ(source)) :
    Γ ⊢ₘ[T] sequence ∈ₘ seq_spaceₘ(source) :=
  FirstOrder.Derives.conj_elim_left
    (FirstOrder.Derives.iff_elim_left
      (nonempty_sequence_space_member_iff_condition
        S source sequence hNonempty)
      hMembership)

/-- 非空外部列表生成的标准有限图直接进入非空有限序列空间。 -/
theorem standard_sequence_mem_nonempty_sequence_space
    {T : SetTheory} (S : FiniteSequenceSpaceSupport T)
    {free : SetContext} {Γ : Context signature free}
    (elements : List (SetOpenTerm free))
    (target : SetOpenTerm free)
    (hLengthOmega : Γ ⊢ₘ[T] numₘ(elements.length) ∈ₘ ωₘ)
    (hTargetNonempty : Γ ⊢ₘ[T] target ≠ₘ ∅ₘ)
    (hTargetMember : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ target)
    (hElementsNonempty : elements ≠ []) :
    Γ ⊢ₘ[T]
      standard_sequence elements ∈ₘ seq₊_spaceₘ(target) := by
  have hSpace : Γ ⊢ₘ[T]
      standard_sequence elements ∈ₘ seq_spaceₘ(target) :=
    standard_sequence_mem_sequence_space
      S elements target hLengthOmega hTargetNonempty hTargetMember
  have hZeroDomain : Γ ⊢ₘ[T]
      numₘ(0) ∈ₘ domₘ(standard_sequence elements) := by
    have hLengthPositive : 0 < elements.length := by
      cases elements with
      | nil => exact (hElementsNonempty rfl).elim
      | cons head tail => simp
    simpa [standard_sequence] using
      standard_sequence_from_index_domain_mem_of_lt
        (Γ := Γ) S.toFiniteSequenceGraphSupport 0
        (elements := elements) 0
        hLengthPositive
  exact FirstOrder.Derives.iff_elim_right
    (nonempty_sequence_space_member_iff_condition
      S target (standard_sequence elements) hTargetNonempty)
    (FirstOrder.Derives.conj_intro hSpace hZeroDomain)

/-- 普通有限序列空间在定义域内的函数值落入源集合。 -/
theorem sequence_space_member_application_mem
    {T : SetTheory} (S : FiniteSequenceSpaceSupport T)
    {free : SetContext} {Γ : Context signature free}
    (source sequence index : SetOpenTerm free)
    (hNonempty : Γ ⊢ₘ[T] source ≠ₘ ∅ₘ)
    (hMembership : Γ ⊢ₘ[T] sequence ∈ₘ seq_spaceₘ(source))
    (hIndex : Γ ⊢ₘ[T] index ∈ₘ domₘ(sequence)) :
    Γ ⊢ₘ[T] (sequence ·ₘ index) ∈ₘ source := by
  let length : SetOpenTerm (SetSort.set :: free) := .fvar .here
  let body : SetOpenFormula (SetSort.set :: free) :=
    (length ∈ₘ ωₘ) ∧ₘ
      is_mapping_formula
        (sequence.weakenFree SetSort.set)
        length (source.weakenFree SetSort.set)
  have hCondition := sequence_space_member_implies_member_condition
    S source sequence hNonempty hMembership
  have hExist : Γ ⊢ₘ[T] body.existsFreeTop SetSort.set := by
    simpa [body, length, finite_sequence_member_condition] using hCondition
  apply FirstOrder.Derives.exists_elim hExist
  let Δ : Context signature (SetSort.set :: free) :=
    body :: FreshVariable.extendContext SetSort.set Γ
  have hBody : Δ ⊢ₘ[T] body :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hMapping : Δ ⊢ₘ[T]
      is_mapping_formula
        (sequence.weakenFree SetSort.set)
        length (source.weakenFree SetSort.set) :=
    FirstOrder.Derives.conj_elim_right hBody
  have hMappingApplication : Δ ⊢ₘ[T]
      is_mapping_formula
        (sequence.weakenFree SetSort.set)
        length (source.weakenFree SetSort.set) ⟶ₘ
        ((index.weakenFree SetSort.set ∈ₘ
            domₘ(sequence.weakenFree SetSort.set)) ⟶ₘ
          ((sequence.weakenFree SetSort.set ·ₘ
              index.weakenFree SetSort.set) ∈ₘ
            source.weakenFree SetSort.set)) :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_function_application hSentence)
      (is_mapping_application_mem_target
        (Γ := Δ)
        (sequence.weakenFree SetSort.set)
        length (source.weakenFree SetSort.set)
        (index.weakenFree SetSort.set))
  have hIndexWeak : FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T]
      index.weakenFree SetSort.set ∈ₘ
        domₘ(sequence.weakenFree SetSort.set) := by
    have hRenamed := FirstOrder.Derives.free_renaming
      (T := T) (VariableRenaming.weaken SetSort.set) hIndex
    simpa only [FreshVariable.extendContext, Formula.weakenFree,
      Formula.renameFree, Renaming.weakenFree] using! hRenamed
  have hIndexCase : Δ ⊢ₘ[T]
      index.weakenFree SetSort.set ∈ₘ
        domₘ(sequence.weakenFree SetSort.set) :=
    FirstOrder.Derives.context_weaken_cons hIndexWeak
  have hValue := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim hMappingApplication hMapping)
    hIndexCase
  simpa [body, length, Formula.weakenFree] using! hValue

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
