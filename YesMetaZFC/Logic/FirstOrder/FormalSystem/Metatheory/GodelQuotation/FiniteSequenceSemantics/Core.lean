import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.DefinitionContracts
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequence
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalArithmeticBound
/-!
# 标准有限序列的对象语义
本模块证明 `standard_sequence_from` 的递归成员刻画、定义域、单值性、函数求值、
值域上界与有限序列空间成员关系。所有结论均从显式联合理论中的现有定义合同推出；
内部机械化引理统一使用 `stdseq_` 前缀，公共接口保留 `standard_sequence_*` 命名。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false
def standard_sequence_semantics_theory : SetTheory :=
  Theory.union membership_irreflexive_theory (Theory.union finite_sequence_flatten_theory (Theory.union finite_sequence_space_theory
        (Theory.union infinity_theory (Theory.union empty_set_symbol_theory (Theory.union successor_operator_theory (Theory.union binary_union_operator_theory
                (Theory.union singleton_operator_theory (Theory.union ordered_pair_operator_theory (Theory.union function_application_theory
                      natural_addition_bound_theory)))))))))
theorem stdseq_empty_set_symbol_sentence
    {formula : SetFormula} (hFormula : empty_set_symbol_theory formula) :
    Formula.Sentence formula := by
  rw [empty_set_symbol_theory] at hFormula
  rcases hFormula with rfl | hFormula
  · exact ⟨empty_set_definition_axiom_admissible, by native_decide⟩
  · rw [empty_set_theory, SetPredicate.separation_theory] at hFormula
    rcases hFormula with rfl | hFormula
    · exact ⟨SetPredicate.separation_axiom_admissible empty_predicate, by native_decide⟩
    · exact extensionality_theory_sentence hFormula
@[derive_close_sentence]
theorem standard_sequence_semantics_theory_sentence
    {formula : SetFormula} (hFormula : standard_sequence_semantics_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with hFormula | hFormula
  · exact membership_irreflexive_theory_sentence hFormula
  · rcases hFormula with hFormula | hFormula
    · exact finite_sequence_flatten_theory_sentence hFormula
    · rcases hFormula with hFormula | hFormula
      · exact finite_sequence_space_theory_sentence hFormula
      · rcases hFormula with hFormula | hFormula
        · exact infinity_theory_sentence hFormula
        · rcases hFormula with hFormula | hFormula
          · exact stdseq_empty_set_symbol_sentence hFormula
          · rcases hFormula with hFormula | hFormula
            · exact successor_operator_theory_sentence hFormula
            · rcases hFormula with hFormula | hFormula
              · exact binary_union_operator_theory_sentence hFormula
              · rcases hFormula with hFormula | hFormula
                · exact singleton_operator_theory_sentence hFormula
                · rcases hFormula with hFormula | hFormula
                  · exact ordered_pair_operator_theory_sentence hFormula
                  · rcases hFormula with hFormula | hFormula
                    · exact function_application_theory_sentence hFormula
                    · exact natural_addition_bound_theory_sentence hFormula
theorem stdseq_weaken_membership_irreflexive
    {φ : SetFormula} (h : ⊢ₘ[membership_irreflexive_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  exact FirstOrder.Derives.theory_weaken (fun _ hf => Or.inl hf) h
theorem stdseq_empty (t : SetTerm) (ht : Term.Admissible t SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] ¬ₘ t ∈ₘ ∅ₘ := by
  have h := empty_set_term_has_no_members t ht
  exact FirstOrder.Derives.theory_weaken (fun _ hf => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hf))))) h
private theorem stdseq_weaken_infinity {φ : SetFormula} (h : ⊢ₘ[infinity_theory] φ) : ⊢ₘ[standard_sequence_semantics_theory] φ := by
  exact FirstOrder.Derives.theory_weaken (fun _ hf => Or.inr (Or.inr (Or.inr (Or.inl hf)))) h
theorem stdseq_weaken_finite_sequence_space {φ : SetFormula} (h : ⊢ₘ[finite_sequence_space_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  exact FirstOrder.Derives.theory_weaken (fun _ hf => Or.inr (Or.inr (Or.inl hf))) h
theorem stdseq_weaken_finite_sequence_flatten {φ : SetFormula} (h : ⊢ₘ[finite_sequence_flatten_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  exact FirstOrder.Derives.theory_weaken (fun _ hf => Or.inr (Or.inl hf)) h
theorem stdseq_weaken_nonempty_sequence_space
    {φ : SetFormula} (h : ⊢ₘ[nonempty_finite_sequence_space_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  apply stdseq_weaken_finite_sequence_flatten
  exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
      nonempty_sequence_space_theory_subset_finite_sequence_flatten_theory
        hFormula)
    h
private theorem stdseq_weaken_binary {φ : SetFormula} (h : ⊢ₘ[binary_union_operator_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  exact FirstOrder.Derives.theory_weaken (fun _ hf => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hf))))))) h
theorem stdseq_weaken_successor {φ : SetFormula} (h : ⊢ₘ[successor_operator_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  exact FirstOrder.Derives.theory_weaken (fun _ hf => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hf)))))) h
/-- 后继算子理论嵌入标准序列语义理论的公开接口。 -/
theorem standard_sequence_weaken_successor
    {φ : SetFormula} (h : ⊢ₘ[successor_operator_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ :=
  stdseq_weaken_successor h
private theorem stdseq_weaken_singleton {φ : SetFormula} (h : ⊢ₘ[singleton_operator_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  exact FirstOrder.Derives.theory_weaken (fun _ hf => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hf)))))))) h
theorem stdseq_weaken_ordered {φ : SetFormula} (h : ⊢ₘ[ordered_pair_operator_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  exact FirstOrder.Derives.theory_weaken (fun _ hf => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hf))))))))) h
theorem stdseq_weaken_function_application {φ : SetFormula} (h : ⊢ₘ[function_application_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  exact FirstOrder.Derives.theory_weaken (fun _ hf => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hf)))))))))) h
/-- 函数求值理论嵌入标准序列语义理论的公开接口。 -/
theorem standard_sequence_weaken_function_application
    {φ : SetFormula} (h : ⊢ₘ[function_application_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ :=
  stdseq_weaken_function_application h
/-- 加法上界扩展嵌入标准序列语义理论。 -/
theorem standard_sequence_weaken_natural_addition_bound
    {Γ : Context signature}
    {φ : SetFormula}
    (h : Γ ⊢ₘ[natural_addition_bound_theory] φ) :
    Γ ⊢ₘ[standard_sequence_semantics_theory] φ := by
  exact FirstOrder.Derives.theory_weaken
    (fun _ hf =>
      Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr hf)))))))))) h

/-- 自然幂索引上界扩展嵌入标准序列语义理论。 -/
theorem standard_sequence_weaken_natural_exponentiation_bound
    {Γ : Context signature}
    {φ : SetFormula}
    (h : Γ ⊢ₘ[natural_exponentiation_bound_theory] φ) :
    Γ ⊢ₘ[standard_sequence_semantics_theory] φ :=
  standard_sequence_weaken_natural_addition_bound <|
    FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        natural_exponentiation_bound_theory_subset_addition_bound_theory
          hFormula)
      h

/-- 自然数幂定义层嵌入标准序列语义理论。 -/
theorem standard_sequence_weaken_natural_exponentiation
    {Γ : Context signature}
    {φ : SetFormula}
    (h : Γ ⊢ₘ[natural_exponentiation_theory] φ) :
    Γ ⊢ₘ[standard_sequence_semantics_theory] φ :=
  standard_sequence_weaken_natural_exponentiation_bound <|
    FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        natural_exponentiation_theory_subset_bound_theory hFormula)
      h
private theorem stdseq_weaken_relation_predicate {φ : SetFormula} (h : ⊢ₘ[relation_predicate_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  apply stdseq_weaken_function_application
  exact FirstOrder.Derives.theory_weaken (fun _ hf => relation_plane_theory_subset_function_application_theory
      (relation_predicate_theory_subset_relation_plane_theory hf)) h
private theorem stdseq_weaken_relation_function {φ : SetFormula} (h : ⊢ₘ[relation_function_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  apply stdseq_weaken_function_application
  exact FirstOrder.Derives.theory_weaken (fun _ hf => relation_plane_theory_subset_function_application_theory
      (relation_function_theory_subset_relation_plane_theory hf)) h
theorem stdseq_weaken_relation_plane {φ : SetFormula} (h : ⊢ₘ[relation_plane_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  apply stdseq_weaken_function_application
  exact FirstOrder.Derives.theory_weaken (fun _ hf => relation_plane_theory_subset_function_application_theory hf) h
private theorem stdseq_weaken_relation_domain {φ : SetFormula} (h : ⊢ₘ[relation_domain_operator_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  apply stdseq_weaken_function_application
  exact FirstOrder.Derives.theory_weaken (fun _ hf => relation_domain_operator_theory_subset_function_application_theory hf) h
theorem stdseq_weaken_relation_range {φ : SetFormula} (h : ⊢ₘ[relation_range_operator_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  apply stdseq_weaken_relation_plane
  exact FirstOrder.Derives.theory_weaken (fun _ hf =>
      relation_range_operator_theory_subset_relation_plane_theory hf) h
theorem stdseq_weaken_subset {φ : SetFormula} (h : ⊢ₘ[subset_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  apply stdseq_weaken_relation_plane
  exact FirstOrder.Derives.theory_weaken (fun _ hf => subset_theory_subset_relation_plane_theory hf) h
theorem stdseq_weaken_mapping_predicate {φ : SetFormula} (h : ⊢ₘ[mapping_predicate_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  apply stdseq_weaken_function_application
  exact FirstOrder.Derives.theory_weaken (fun _ hf => mapping_predicate_theory_subset_function_application_theory hf) h
theorem stdseq_weaken_function_predicate {φ : SetFormula} (h : ⊢ₘ[function_predicate_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  apply stdseq_weaken_function_application
  exact FirstOrder.Derives.theory_weaken (fun _ hf => function_predicate_theory_subset_function_application_theory hf) h
theorem stdseq_weaken_extensionality {φ : SetFormula} (h : ⊢ₘ[extensionality_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  apply stdseq_weaken_function_application
  exact FirstOrder.Derives.theory_weaken (fun _ hf => extensionality_theory_subset_function_application_theory hf) h
theorem stdseq_disj_congr
    {left₁ right₁ left₂ right₂ : SetFormula} (hLeft : ⊢ₘ[standard_sequence_semantics_theory] left₁ ↔ₘ left₂)
    (hRight : ⊢ₘ[standard_sequence_semantics_theory] right₁ ↔ₘ right₂) :
    ⊢ₘ[standard_sequence_semantics_theory] (left₁ ∨ₘ right₁) ↔ₘ (left₂ ∨ₘ right₂) := by
  have hLeftOne :
      Formula.Admissible left₁ :=
    Formula.Admissible.iff_left hLeft.admissible
  have hLeftTwo :
      Formula.Admissible left₂ :=
    Formula.Admissible.iff_right hLeft.admissible
  have hRightOne :
      Formula.Admissible right₁ :=
    Formula.Admissible.iff_left hRight.admissible
  have hRightTwo :
      Formula.Admissible right₂ :=
    Formula.Admissible.iff_right hRight.admissible
  have hSourceOne :
      Formula.Admissible (left₁ ∨ₘ right₁) :=
    Formula.Admissible.disj hLeftOne hRightOne
  have hSourceTwo :
      Formula.Admissible (left₂ ∨ₘ right₂) :=
    Formula.Admissible.disj hLeftTwo hRightTwo
  apply FirstOrder.Derives.iffIntro
  · apply FirstOrder.Derives.disjElim
      (left := left₁) (right := right₁)
      (conclusion := left₂ ∨ₘ right₂)
      (.assumption (φ := left₁ ∨ₘ right₁) (by simp))
    · exact FirstOrder.Derives.disjIntroLeft (right := right₂)
        (FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken (Γ := []) (Δ := [left₁, left₁ ∨ₘ right₁]) (by simp) hLeft)
          (.assumption (φ := left₁) (by simp)))
    · exact FirstOrder.Derives.disjIntroRight (left := left₂)
        (FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken (Γ := []) (Δ := [right₁, left₁ ∨ₘ right₁]) (by simp) hRight)
          (.assumption (φ := right₁) (by simp)))
  · apply FirstOrder.Derives.disjElim
      (left := left₂) (right := right₂)
      (conclusion := left₁ ∨ₘ right₁)
      (.assumption (φ := left₂ ∨ₘ right₂) (by simp))
    · exact FirstOrder.Derives.disjIntroLeft (right := right₁)
        (FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken (Γ := []) (Δ := [left₂, left₂ ∨ₘ right₂]) (by simp) hLeft)
          (.assumption (φ := left₂) (by simp)))
    · exact FirstOrder.Derives.disjIntroRight (left := left₁)
        (FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken (Γ := []) (Δ := [right₂, left₂ ∨ₘ right₂]) (by simp) hRight)
          (.assumption (φ := right₂) (by simp)))
theorem standard_sequence_finite_numeral_mem_omega (number : Nat) :
    ⊢ₘ[standard_sequence_semantics_theory] numₘ(number) ∈ₘ ωₘ := by
  exact stdseq_weaken_infinity (infinity_finite_numeral_mem_omega number)
/-- `ωₘ` 含有零，因而在标准序列语义理论中不是空集。 -/
theorem standard_sequence_omega_ne_empty :
    ⊢ₘ[standard_sequence_semantics_theory] ωₘ ≠ₘ ∅ₘ := by
  let equality : SetFormula := ωₘ ≐ₘ ∅ₘ
  let Γ : Context signature := [equality]
  nd_apply FirstOrder.Derives.negIntro
  have hEquality : Γ ⊢ₘ[standard_sequence_semantics_theory] equality :=
    .assumption (by simp [Γ])
  have hZero :
      Γ ⊢ₘ[standard_sequence_semantics_theory] numₘ(0) ∈ₘ ωₘ :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) (standard_sequence_finite_numeral_mem_omega 0)
  have hTransport := membership_right_iff_of_equality (numₘ(0)) ωₘ ∅ₘ (finite_numeral_term_admissible 0)
    omega_term_admissible
    empty_set_term_admissible
    hEquality
  have hEmptyMember :
      Γ ⊢ₘ[standard_sequence_semantics_theory] numₘ(0) ∈ₘ ∅ₘ :=
    FirstOrder.Derives.iffElimRight hTransport hZero
  exact FirstOrder.Derives.negElim hEmptyMember (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ])
      (stdseq_empty (numₘ(0)) (finite_numeral_term_admissible 0)))
/--
代码字符串空间中的每个对象都是有限序列。
该结论把 `CodeStrₘ = seq_spaceₘ(ωₘ)` 的空间成员规格消去为后续拼接语义直接需要的
`finite_sequence_condition`，并保留成对象层全称定理。
-/
theorem code_string_member_implies_finite_sequence :
    ⊢ₘ[standard_sequence_semantics_theory]
      ∀ₘ[SetSort.set, 470], ((x#470 ∈ₘ CodeStrₘ) ⟶ₘ
          finite_sequence_condition (x#470)) := by
  let sequence : SetTerm := x#470
  let sequenceSpace : SetTerm := CodeStrₘ
  let member : SetFormula := sequence ∈ₘ sequenceSpace
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    simpa [sequence] using set_variable_admissible 470
  have hSequenceSpace :
      Term.Admissible sequenceSpace SetSort.set := by
    simpa [sequenceSpace, code_string_space_term] using
      finite_sequence_space_term_admissible
        ωₘ omega_term_admissible
  have hContract :=
    stdseq_weaken_finite_sequence_space <|
      finite_sequence_space_definition_instance_derives
        ωₘ sequenceSpace omega_term_admissible hSequenceSpace
  have hSpaceSpec :
      ⊢ₘ[standard_sequence_semantics_theory]
        finite_sequence_space_spec ωₘ sequenceSpace := by
    have hIff :=
      FirstOrder.Derives.impElim
        hContract standard_sequence_omega_ne_empty
    exact FirstOrder.Derives.iffElimRight hIff <| by
      simpa [sequenceSpace, code_string_space_term] using (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) sequenceSpace)
  have hAtSequence :=
    FirstOrder.Derives.forall_elim
      (term := sequence) hSpaceSpec
  have hOmegaOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term ωₘ = ωₘ :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term ωₘ omega_term_admissible.2
  have hSpaceOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term sequenceSpace =
        sequenceSpace :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term sequenceSpace hSequenceSpace.2
  have hMemberIff :
      ⊢ₘ[standard_sequence_semantics_theory]
        member ↔ₘ
          finite_sequence_member_condition ωₘ sequence := by
    simpa [member, sequence,
      finite_sequence_space_spec,
      finite_sequence_member_condition,
      Formula.openAt, Formula.next_depth,
      Term.openAt, hOmegaOpen, hSpaceOpen] using
      hAtSequence
  have hOpen :
      ⊢ₘ[standard_sequence_semantics_theory]
        member ⟶ₘ finite_sequence_condition sequence := by
    let Γ : Context signature := [member]
    nd_apply FirstOrder.Derives.impIntro
    have hMember :
        Γ ⊢ₘ[standard_sequence_semantics_theory] member :=
      FirstOrder.Derives.assumption (by simp [Γ])
    have hExists :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          finite_sequence_member_condition ωₘ sequence :=
      FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hMemberIff)
        hMember
    let witness : SetTerm := x#471
    let witnessCondition : SetFormula := (witness ∈ₘ ωₘ) ∧ₘ
        is_mapping_formula sequence witness ωₘ
    have hExists' :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          ∃ₘ[SetSort.set, 471], witnessCondition := by
      simpa [finite_sequence_member_condition,
        witnessCondition, witness, sequence,
        Formula.closeFreeAt, Term.closeFreeAt,
        set_variable, set_bound_variable] using hExists
    apply FirstOrder.Derives.exists_elim
      (T := standard_sequence_semantics_theory) (Γ := Γ)
      (sort := SetSort.set) (eigen := 471)
      (body := witnessCondition)
        (conclusion := finite_sequence_condition sequence)
    · intro formula hFormula
      rw [(standard_sequence_semantics_theory_sentence
        hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      rcases List.mem_singleton.mp hFormula with rfl
      simp [member, sequence, sequenceSpace,
        Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList]
    · simp [sequence, finite_sequence_condition,
        Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList]
    · exact hExists'
    · let Δ : Context signature := [witnessCondition, member]
      have hWitnessCondition :
          Δ ⊢ₘ[standard_sequence_semantics_theory]
            witnessCondition :=
        FirstOrder.Derives.assumption (by simp [Δ])
      have hWitnessOmega :
          Δ ⊢ₘ[standard_sequence_semantics_theory]
            witness ∈ₘ ωₘ :=
        FirstOrder.Derives.conjElimLeft hWitnessCondition
      have hMapping :
          Δ ⊢ₘ[standard_sequence_semantics_theory]
            is_mapping_formula sequence witness ωₘ :=
        FirstOrder.Derives.conjElimRight hWitnessCondition
      have hMappingCondition :
          Δ ⊢ₘ[standard_sequence_semantics_theory]
            is_mapping_condition sequence witness ωₘ :=
        FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp [Δ]) <|
            stdseq_weaken_mapping_predicate <|
              is_mapping_implies_condition
                sequence witness ωₘ
                hSequence (by simpa [witness] using
                  set_variable_admissible 471)
                omega_term_admissible)
          hMapping
      have hFunction :
          Δ ⊢ₘ[standard_sequence_semantics_theory]
            is_function_formula sequence :=
        FirstOrder.Derives.conjElimLeft hMappingCondition
      have hDomainEquality :
          Δ ⊢ₘ[standard_sequence_semantics_theory]
            witness ≐ₘ domₘ(sequence) :=
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight
            hMappingCondition
      have hDomainOmega :
          Δ ⊢ₘ[standard_sequence_semantics_theory]
            domₘ(sequence) ∈ₘ ωₘ :=
        FirstOrder.Derives.iffElimRight
          (membership_left_iff_of_equality
            witness (domₘ(sequence)) ωₘ
            (by simpa [witness] using
              set_variable_admissible 471)
            (domain_term_admissible sequence hSequence)
            omega_term_admissible
            hDomainEquality)
          hWitnessOmega
      exact FirstOrder.Derives.conjIntro
        hFunction hDomainOmega
  have hTheoryFresh :
      ∀ formula, standard_sequence_semantics_theory formula → (SetSort.set, 470) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    rw [(standard_sequence_semantics_theory_sentence hFormula).2]
    exact List.not_mem_nil
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := 470)
      hTheoryFresh (by simp) hOpen
  simpa [sequence, sequenceSpace, member] using hGeneralized
/-- 代码字符串有限性的全称结论在任意 admissible 项处的直接实例。 -/
theorem code_string_member_implies_finite_sequence_at (sequence : SetTerm) (hSequence : Term.Admissible sequence SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] (sequence ∈ₘ CodeStrₘ) ⟶ₘ
        finite_sequence_condition sequence := by
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := sequence)
      code_string_member_implies_finite_sequence
  simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.substituteFree, Term.substituteFree,
    set_variable, finite_sequence_condition,
    is_function_formula, domain_term] using hAt
/--
有限序列空间中的映射在其定义域内逐点落入目标集。
该定理直接消费 `seq_spaceₘ(target)` 的映射见证，并通过函数层公开的
`is_mapping_application_mem_target` 合同得到值域结论。它是任意目标集上的通用接口；
目标非空只用于启用有限序列空间的定义公理。
-/
theorem sequence_space_member_application_mem (target sequence index : SetTerm) (hTarget : Term.Admissible target SetSort.set)
    (hSequence : Term.Admissible sequence SetSort.set) (hIndex : Term.Admissible index SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] (target ≠ₘ ∅ₘ) ⟶ₘ ((sequence ∈ₘ seq_spaceₘ(target)) ⟶ₘ ((index ∈ₘ domₘ(sequence)) ⟶ₘ
            ((sequence ·ₘ index) ∈ₘ target))) := by
  let sequenceSpace : SetTerm := seq_spaceₘ(target)
  let nonempty : SetFormula := target ≠ₘ ∅ₘ
  let membership : SetFormula := sequence ∈ₘ sequenceSpace
  let domainMembership : SetFormula :=
    index ∈ₘ domₘ(sequence)
  let value : SetTerm := sequence ·ₘ index
  let conclusion : SetFormula :=
    domainMembership ⟶ₘ (value ∈ₘ target)
  let freshnessBasis : List SetFormula :=
    [conclusion, target ≐ₘ target,
      sequence ≐ₘ sequence, index ≐ₘ index]
  let witnessId : FreeVarId :=
    FreshVariable.fresh_id SetSort.set freshnessBasis
  let witness : SetTerm := x#witnessId
  let witnessCondition : SetFormula := (witness ∈ₘ ωₘ) ∧ₘ
      is_mapping_formula sequence witness target
  have hSequenceSpace :
      Term.Admissible sequenceSpace SetSort.set := by
    simpa [sequenceSpace] using
      finite_sequence_space_term_admissible
        target hTarget
  have hValue :
      Term.Admissible value SetSort.set := by
    simpa [value] using
      function_application_term_admissible
        sequence index hSequence hIndex
  have hNonempty :
      Formula.Admissible nonempty := by
    simpa [nonempty] using
      Formula.Admissible.neg <|
        Formula.Admissible.equal
          hTarget empty_set_term_admissible
  have hMembership :
      Formula.Admissible membership := by
    simpa [membership] using
      membership_formula_admissible
        hSequence hSequenceSpace
  have hDomainMembership :
      Formula.Admissible domainMembership := by
    simpa [domainMembership] using
      membership_formula_admissible hIndex (domain_term_admissible sequence hSequence)
  have hConclusion :
      Formula.Admissible conclusion := by
    simpa [conclusion, domainMembership, value] using
      Formula.Admissible.imp hDomainMembership (membership_formula_admissible hValue hTarget)
  have hWitness :
      Term.Admissible witness SetSort.set := by
    simpa [witness] using
      set_variable_admissible witnessId
  have hWitnessCondition :
      Formula.Admissible witnessCondition := by
    simpa [witnessCondition] using
      Formula.Admissible.conj (membership_formula_admissible
          hWitness omega_term_admissible) (is_mapping_formula_admissible
          hSequence hWitness hTarget)
  have hWitnessFreshTarget : (SetSort.set, witnessId) ∉
        Term.freeSupport target := by
    dsimp [witnessId, freshnessBasis]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas := [
          conclusion, target ≐ₘ target,
          sequence ≐ₘ sequence, index ≐ₘ index]) (formula := target ≐ₘ target) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hWitnessFreshSequence : (SetSort.set, witnessId) ∉
        Term.freeSupport sequence := by
    dsimp [witnessId, freshnessBasis]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas := [
          conclusion, target ≐ₘ target,
          sequence ≐ₘ sequence, index ≐ₘ index]) (formula := sequence ≐ₘ sequence) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hWitnessFreshIndex : (SetSort.set, witnessId) ∉
        Term.freeSupport index := by
    dsimp [witnessId, freshnessBasis]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas := [
          conclusion, target ≐ₘ target,
          sequence ≐ₘ sequence, index ≐ₘ index]) (formula := index ≐ₘ index) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hWitnessFreshConclusion : (SetSort.set, witnessId) ∉
        Formula.freeSupport conclusion := by
    dsimp [witnessId, freshnessBasis]
    exact FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas := [
        conclusion, target ≐ₘ target,
        sequence ≐ₘ sequence, index ≐ₘ index]) (formula := conclusion) (by simp)
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
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature :=
      [domainMembership, witnessCondition]
    have hWitnessConditionProof :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          witnessCondition :=
      FirstOrder.Derives.assumption (by simp [Γ])
    have hMapping :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          is_mapping_formula sequence witness target := by
      simpa [witnessCondition] using (FirstOrder.Derives.conjElimRight
          hWitnessConditionProof)
    have hDomain :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          index ∈ₘ domₘ(sequence) := by
      simpa [domainMembership] using (FirstOrder.Derives.assumption (T := standard_sequence_semantics_theory) (Γ := Γ) (φ := domainMembership)
          (by simp [Γ]))
    have hMappingCondition :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          is_mapping_condition sequence witness target :=
      FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          stdseq_weaken_mapping_predicate <|
            is_mapping_implies_condition
              sequence witness target
              hSequence hWitness hTarget)
        hMapping
    have hDomainEquality :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          witness ≐ₘ domₘ(sequence) :=
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight
          hMappingCondition
    have hWitnessDomain :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          index ∈ₘ witness :=
      FirstOrder.Derives.iffElimLeft (membership_right_iff_of_equality
          index witness (domₘ(sequence))
          hIndex hWitness (domain_term_admissible sequence hSequence)
          hDomainEquality)
        hDomain
    have hApplication :=
      stdseq_weaken_function_application <|
        is_mapping_application_mem_target
          sequence witness target index
          hSequence hWitness hTarget hIndex
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ])
          (by simpa [value] using hApplication))
        hMapping)
      hWitnessDomain
  have hTheoryFresh :
      ∀ formula, standard_sequence_semantics_theory formula → (SetSort.set, witnessId) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    rw [(standard_sequence_semantics_theory_sentence
      hFormula).2]
    exact List.not_mem_nil
  have hLiftRaw :=
    Metatheory.Derives.exists_imp_of_imp (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := witnessId)
      hTheoryFresh (by
        intro formula hFormula
        cases hFormula)
      hWitnessFreshConclusion hPoint
  have hFiniteToConclusion :
      ⊢ₘ[standard_sequence_semantics_theory]
        finite_sequence_member_condition target sequence ⟶ₘ
          conclusion := by
    simpa [finite_sequence_member_condition,
      witnessCondition, witness, conclusion,
      Formula.closeFreeAt, Term.closeFreeAt,
      set_variable, set_bound_variable,
      hWitnessCloseTarget, hWitnessCloseSequence] using hLiftRaw
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [domainMembership, membership, nonempty]
  have hNonemptyProof :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        target ≠ₘ ∅ₘ := by
    simpa [nonempty] using
      (FirstOrder.Derives.assumption
        (T := standard_sequence_semantics_theory)
        (Γ := Γ) (φ := nonempty) (by simp [Γ]))
  have hMembershipProof :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        sequence ∈ₘ sequenceSpace := by
    simpa [membership] using
      (FirstOrder.Derives.assumption
        (T := standard_sequence_semantics_theory)
        (Γ := Γ) (φ := membership) (by simp [Γ]))
  have hDomainProof :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        domainMembership :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hContract :=
    stdseq_weaken_finite_sequence_space <|
      finite_sequence_space_definition_instance_derives
        target sequenceSpace hTarget hSequenceSpace
  have hSpaceIff :
      Γ ⊢ₘ[standard_sequence_semantics_theory] (sequenceSpace ≐ₘ seq_spaceₘ(target)) ↔ₘ
          finite_sequence_space_spec
            target sequenceSpace :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) (by simpa [sequenceSpace] using hContract))
      hNonemptyProof
  have hSpaceSpec :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        finite_sequence_space_spec
          target sequenceSpace :=
    FirstOrder.Derives.iffElimRight
      hSpaceIff (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) sequenceSpace)
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := sequence) hSpaceSpec
  have hTargetOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term target = target :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term target hTarget.2
  have hSequenceSpaceOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term sequenceSpace =
        sequenceSpace :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term sequenceSpace
      hSequenceSpace.2
  have hAt :
      Γ ⊢ₘ[standard_sequence_semantics_theory] (sequence ∈ₘ sequenceSpace) ↔ₘ
          finite_sequence_member_condition
            target sequence := by
    simpa [finite_sequence_space_spec,
      finite_sequence_member_condition,
      Formula.openAt, Formula.next_depth,
      Term.openAt, hTargetOpen,
      hSequenceSpaceOpen] using hAtRaw
  have hFinite :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        finite_sequence_member_condition
          target sequence :=
    FirstOrder.Derives.iffElimRight
      hAt hMembershipProof
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ])
        hFiniteToConclusion)
      hFinite)
    hDomainProof
/--
非空有限序列空间的成员自动属于对应的普通有限序列空间。
该接口只消去 `seq₊_spaceₘ` 定义中的附加“零号位置存在”分量，供轨迹分类器读取
任意已知定义域位置上的值。
-/
theorem nonempty_sequence_space_member_implies_sequence_space (target sequence : SetTerm) (hTarget : Term.Admissible target SetSort.set)
    (hSequence : Term.Admissible sequence SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] (target ≠ₘ ∅ₘ) ⟶ₘ ((sequence ∈ₘ seq₊_spaceₘ(target)) ⟶ₘ (sequence ∈ₘ seq_spaceₘ(target))) := by
  let positiveSpace := seq₊_spaceₘ(target)
  let nonempty : SetFormula := target ≠ₘ ∅ₘ
  let membership : SetFormula := sequence ∈ₘ positiveSpace
  have hPositiveSpace :
      Term.Admissible positiveSpace SetSort.set := by
    simpa [positiveSpace] using
      nonempty_finite_sequence_space_term_admissible
        target hTarget
  have hNonempty :
      Formula.Admissible nonempty := by
    simpa [nonempty] using
      Formula.Admissible.neg <|
        Formula.Admissible.equal hTarget empty_set_term_admissible
  have hMembership :
      Formula.Admissible membership := by
    simpa [membership] using
      membership_formula_admissible
        hSequence hPositiveSpace
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [membership, nonempty]
  have hNonemptyProof :
      Γ ⊢ₘ[standard_sequence_semantics_theory] nonempty :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hMembershipProof :
      Γ ⊢ₘ[standard_sequence_semantics_theory] membership :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hContract :
      Γ ⊢ₘ[standard_sequence_semantics_theory] (positiveSpace ≐ₘ seq₊_spaceₘ(target)) ↔ₘ
          nonempty_finite_sequence_space_spec
            target positiveSpace := by
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
          simpa [positiveSpace] using
            stdseq_weaken_nonempty_sequence_space <|
              nonempty_finite_sequence_space_definition_instance_derives
                target positiveSpace hTarget hPositiveSpace)
      hNonemptyProof
  have hSpec :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        nonempty_finite_sequence_space_spec
          target positiveSpace :=
    FirstOrder.Derives.iffElimRight hContract <|
      FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) positiveSpace
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := sequence) hSpec
  have hTargetOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term target = target :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term target hTarget.2
  have hPositiveSpaceOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term positiveSpace =
        positiveSpace :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term positiveSpace hPositiveSpace.2
  have hZeroOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term (numₘ(0)) =
        numₘ(0) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term (numₘ(0)) (finite_numeral_term_admissible 0).2
  have hAt :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        membership ↔ₘ
          nonempty_finite_sequence_member_condition
            target sequence := by
    simpa [membership, positiveSpace,
      nonempty_finite_sequence_space_spec,
      nonempty_finite_sequence_member_condition,
      Formula.openAt, Formula.next_depth, Term.openAt,
      hTargetOpen, hPositiveSpaceOpen, hZeroOpen] using hAtRaw
  have hCondition :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        nonempty_finite_sequence_member_condition
          target sequence :=
    FirstOrder.Derives.iffElimRight hAt hMembershipProof
  simpa [nonempty_finite_sequence_member_condition] using
    FirstOrder.Derives.conjElimLeft hCondition
def standard_sequence_member_condition (start : Nat) : List SetTerm → SetTerm → SetFormula
  | ([] : List SetTerm), _ => Formula.falsum
  | element :: rest, member =>
      (member ≐ₘ ⟨numₘ(start), element⟩ₘ) ∨ₘ
        standard_sequence_member_condition (start + 1) rest member
/-- 标准序列成员条件按外部列表递归保持 admissibility。 -/
theorem standard_sequence_member_condition_admissible (start : Nat) (elements : List SetTerm) (member : SetTerm) (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hMember : Term.Admissible member SetSort.set) :
    Formula.Admissible (standard_sequence_member_condition
        start elements member) := by
  induction elements generalizing start with
  | nil =>
      exact Formula.Admissible.falsum
  | cons head tail ih =>
      have hHead := hElements head (by simp)
      have hTail :
          ∀ element, element ∈ tail →
            Term.Admissible element SetSort.set := by
        intro element hElement
        exact hElements element (by simp [hElement])
      exact Formula.Admissible.disj (Formula.Admissible.equal
          hMember (ordered_pair_term_admissible (numₘ(start)) head (finite_numeral_term_admissible start)
            hHead)) (ih (start + 1) hTail)
/-- 标准序列成员条件的可计算证书扩展。 -/
@[formula_check]
theorem standard_sequence_member_condition_check
    (start : Nat) (elements : List SetTerm) (member : SetTerm)
    (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set)
    (hMember : Term.Admissible member SetSort.set) :
    Formula.CheckCertificate
      (standard_sequence_member_condition start elements member) :=
  Formula.check_admissible_complete
    (standard_sequence_member_condition_admissible
      start elements member hElements hMember)
theorem standard_sequence_from_member_iff (start : Nat) {elements : List SetTerm} (member : SetTerm) (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hMember : Term.Admissible member SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] (member ∈ₘ standard_sequence_from start elements) ↔ₘ
        standard_sequence_member_condition start elements member := by
  induction elements generalizing start with
  | nil =>
      have hEmpty := stdseq_empty member hMember
      derive_prop
  | cons head tail ih =>
      have hHead := hElements head (by simp)
      have hTail : ∀ element, element ∈ tail →
          Term.Admissible element SetSort.set := by
        intro element hElement
        exact hElements element (by simp [hElement])
      have hPair : Term.Admissible (⟨numₘ(start), head⟩ₘ) SetSort.set :=
        ordered_pair_term_admissible (numₘ(start)) head (finite_numeral_term_admissible start) hHead
      have hSingleton : Term.Admissible ({⟨numₘ(start), head⟩ₘ}ₘ) SetSort.set :=
        singleton_term_admissible _ hPair
      have hRest : Term.Admissible (standard_sequence_from (start + 1) tail) SetSort.set :=
        seq_admissible_m (start + 1) hTail
      have hUnion := binary_union_term_spec_derives ({⟨numₘ(start), head⟩ₘ}ₘ) (standard_sequence_from (start + 1) tail)
        hSingleton hRest
      have hUnion' :
          ⊢ₘ[standard_sequence_semantics_theory]
            binary_union_spec ({⟨numₘ(start), head⟩ₘ}ₘ) (standard_sequence_from (start + 1) tail) ({⟨numₘ(start), head⟩ₘ}ₘ ∪ₘ
                standard_sequence_from (start + 1) tail) :=
        stdseq_weaken_binary hUnion
      have hSingletonSpec := singleton_term_spec_derives (⟨numₘ(start), head⟩ₘ) hPair
      have hSingletonSpec' :
          ⊢ₘ[standard_sequence_semantics_theory]
            singleton_spec (⟨numₘ(start), head⟩ₘ) ({⟨numₘ(start), head⟩ₘ}ₘ) :=
        stdseq_weaken_singleton hSingletonSpec
      have hSingletonIff := singleton_spec_membership_iff (⟨numₘ(start), head⟩ₘ) ({⟨numₘ(start), head⟩ₘ}ₘ) member
        hPair hSingleton hMember hSingletonSpec'
      have hSingletonPoint :
          ⊢ₘ[standard_sequence_semantics_theory] (member ∈ₘ {⟨numₘ(start), head⟩ₘ}ₘ) ↔ₘ (member ≐ₘ ⟨numₘ(start), head⟩ₘ) := by
        exact hSingletonIff
      have hTailIff := ih (start + 1) hTail
      have hUnionPoint :
          ⊢ₘ[standard_sequence_semantics_theory] (member ∈ₘ ({⟨numₘ(start), head⟩ₘ}ₘ ∪ₘ
                  standard_sequence_from (start + 1) tail)) ↔ₘ ((member ∈ₘ {⟨numₘ(start), head⟩ₘ}ₘ) ∨ₘ
                (member ∈ₘ standard_sequence_from (start + 1) tail)) := by
        have hMemberOpen (depth : Nat) (term : SetTerm) :
            Term.openAt SetSort.set depth term member = member :=
          Term.openAt_eq_self_of_boundClosed
            SetSort.set depth term member hMember.2
        have hNumOpen (depth : Nat) (term : SetTerm) :
            Term.openAt SetSort.set depth term (numₘ(start)) = numₘ(start) :=
          Term.openAt_eq_self_of_boundClosed
            SetSort.set depth term (numₘ(start)) (finite_numeral_term_admissible start).2
        have hHeadOpen (depth : Nat) (term : SetTerm) :
            Term.openAt SetSort.set depth term head = head :=
          Term.openAt_eq_self_of_boundClosed
            SetSort.set depth term head hHead.2
        have hRestOpen (depth : Nat) (term : SetTerm) :
            Term.openAt SetSort.set depth term (standard_sequence_from (start + 1) tail) =
              standard_sequence_from (start + 1) tail :=
          Term.openAt_eq_self_of_boundClosed
            SetSort.set depth term (standard_sequence_from (start + 1) tail) hRest.2
        simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
          Formula.openAt, Formula.closeFreeAt, Formula.next_depth,
          Formula.substituteFree, Term.openAt, Term.closeFreeAt,
          Term.substituteFree, set_variable, set_bound_variable,
          hMemberOpen, hNumOpen, hHeadOpen, hRestOpen] using (FirstOrder.Derives.forall_elim
            (term := member) hUnion')
      have hCombined :
          ⊢ₘ[standard_sequence_semantics_theory] ((member ∈ₘ {⟨numₘ(start), head⟩ₘ}ₘ) ∨ₘ (member ∈ₘ standard_sequence_from (start + 1) tail)) ↔ₘ
              ((member ≐ₘ ⟨numₘ(start), head⟩ₘ) ∨ₘ
                standard_sequence_member_condition (start + 1) tail member) := by
        exact stdseq_disj_congr hSingletonPoint hTailIff
      have hStep :
          ⊢ₘ[standard_sequence_semantics_theory] (member ∈ₘ ({⟨numₘ(start), head⟩ₘ}ₘ ∪ₘ
                  standard_sequence_from (start + 1) tail)) ↔ₘ ((member ≐ₘ ⟨numₘ(start), head⟩ₘ) ∨ₘ
                standard_sequence_member_condition (start + 1) tail member) := by
        exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (Metatheory.Derives.iff_trans_m (T := standard_sequence_semantics_theory) (Γ := [])
              (ψ := (member ∈ₘ ({⟨numₘ(start), head⟩ₘ}ₘ ∪ₘ
                  standard_sequence_from (start + 1) tail))) (φ := ((member ∈ₘ {⟨numₘ(start), head⟩ₘ}ₘ) ∨ₘ (member ∈ₘ standard_sequence_from (start + 1) tail)))
              (θ := ((member ≐ₘ ⟨numₘ(start), head⟩ₘ) ∨ₘ
                standard_sequence_member_condition (start + 1) tail member)) (Formula.Admissible.iff_right
                hUnionPoint.admissible) (Formula.Admissible.iff_left
                hUnionPoint.admissible) (Formula.Admissible.iff_right
                hCombined.admissible))
            hUnionPoint)
          hCombined
      simpa [standard_sequence_from, standard_sequence_member_condition] using hStep
private theorem stdseq_binary_union_member_iff (left right member : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hMember : Term.Admissible member SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] (member ∈ₘ (left ∪ₘ right)) ↔ₘ ((member ∈ₘ left) ∨ₘ (member ∈ₘ right)) := by
  have hSpec := stdseq_weaken_binary (binary_union_term_spec_derives left right hLeft hRight)
  have hLeftOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement left hLeft.2
  have hRightOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement right hRight.2
  have hMemberOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement member = member :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement member hMember.2
  simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt, Formula.next_depth,
    Formula.substituteFree, Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable, set_bound_variable,
    hLeftOpen, hRightOpen, hMemberOpen] using
      (FirstOrder.Derives.forall_elim (term := member) hSpec)
private theorem stdseq_singleton_member_iff (element member : SetTerm) (hElement : Term.Admissible element SetSort.set)
    (hMember : Term.Admissible member SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] (member ∈ₘ {element}ₘ) ↔ₘ (member ≐ₘ element) := by
  have hSingleton : Term.Admissible ({element}ₘ) SetSort.set :=
    singleton_term_admissible element hElement
  have hSpec := stdseq_weaken_singleton (singleton_term_spec_derives element hElement)
  exact singleton_spec_membership_iff
    element ({element}ₘ) member hElement hSingleton hMember hSpec
def standard_sequence_pair_member_condition (start : Nat) : List SetTerm → SetTerm → SetTerm → SetFormula
  | ([] : List SetTerm), _, _ => Formula.falsum
  | element :: rest, index, value =>
      ((index ≐ₘ numₘ(start)) ∧ₘ (value ≐ₘ element)) ∨ₘ
        standard_sequence_pair_member_condition (start + 1) rest index value
/-- 标准序列坐标成员条件按外部列表递归保持 admissibility。 -/
theorem standard_sequence_pair_member_condition_admissible (start : Nat) (elements : List SetTerm) (index value : SetTerm)
    (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hIndex : Term.Admissible index SetSort.set) (hValue : Term.Admissible value SetSort.set) :
    Formula.Admissible (standard_sequence_pair_member_condition
        start elements index value) := by
  induction elements generalizing start with
  | nil =>
      exact Formula.Admissible.falsum
  | cons head tail ih =>
      have hHead := hElements head (by simp)
      have hTail :
          ∀ element, element ∈ tail →
            Term.Admissible element SetSort.set := by
        intro element hElement
        exact hElements element (by simp [hElement])
      exact Formula.Admissible.disj (Formula.Admissible.conj (Formula.Admissible.equal
            hIndex (finite_numeral_term_admissible start)) (Formula.Admissible.equal hValue hHead)) (ih (start + 1) hTail)
/-- 标准序列坐标成员条件的可计算证书扩展。 -/
@[formula_check]
theorem standard_sequence_pair_member_condition_check
    (start : Nat) (elements : List SetTerm)
    (index value : SetTerm)
    (hElements : ∀ element, element ∈ elements →
      Term.CheckCertificate element SetSort.set)
    (hIndex : Term.CheckCertificate index SetSort.set)
    (hValue : Term.CheckCertificate value SetSort.set) :
    Formula.CheckCertificate
      (standard_sequence_pair_member_condition
        start elements index value) :=
  Formula.check_admissible_complete
    (standard_sequence_pair_member_condition_admissible
      start elements index value
      (fun element hElement =>
        (hElements element hElement).admissible)
      hIndex.admissible hValue.admissible)
theorem standard_sequence_from_pair_member_iff (start : Nat) {elements : List SetTerm} (index value : SetTerm) (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hIndex : Term.Admissible index SetSort.set) (hValue : Term.Admissible value SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] (⟨index, value⟩ₘ ∈ₘ standard_sequence_from start elements) ↔ₘ
        standard_sequence_pair_member_condition start elements index value := by
  induction elements generalizing start with
  | nil =>
      have hMember := standard_sequence_from_member_iff start (elements := []) (⟨index, value⟩ₘ)
        (by simp) (ordered_pair_term_admissible index value hIndex hValue)
      simpa [standard_sequence_from, standard_sequence_pair_member_condition] using hMember
  | cons head tail ih =>
      have hHead := hElements head (by simp)
      have hTail : ∀ element, element ∈ tail →
          Term.Admissible element SetSort.set := by
        intro element hElement
        exact hElements element (by simp [hElement])
      have hPairMember :
          Term.Admissible (⟨index, value⟩ₘ) SetSort.set :=
        ordered_pair_term_admissible index value hIndex hValue
      have hSingleton :
          Term.Admissible ({⟨numₘ(start), head⟩ₘ}ₘ) SetSort.set :=
        singleton_term_admissible _ (ordered_pair_term_admissible (numₘ(start)) head (finite_numeral_term_admissible start) hHead)
      have hRest :
          Term.Admissible (standard_sequence_from (start + 1) tail)
            SetSort.set :=
        seq_admissible_m (start + 1) hTail
      have hUnionPoint := stdseq_binary_union_member_iff ({⟨numₘ(start), head⟩ₘ}ₘ) (standard_sequence_from (start + 1) tail)
        (⟨index, value⟩ₘ) hSingleton hRest hPairMember
      have hSingletonPoint := stdseq_singleton_member_iff (⟨numₘ(start), head⟩ₘ) (⟨index, value⟩ₘ) (ordered_pair_term_admissible (numₘ(start)) head
          (finite_numeral_term_admissible start) hHead)
        hPairMember
      have hCoordinates := stdseq_weaken_ordered (ordered_pair_term_eq_iff_coordinates
          index value (numₘ(start)) head hIndex hValue (finite_numeral_term_admissible start) hHead)
      have hTailIff := ih (start + 1) hTail
      have hSingletonCoordinate :
          ⊢ₘ[standard_sequence_semantics_theory] (⟨index, value⟩ₘ ∈ₘ {⟨numₘ(start), head⟩ₘ}ₘ) ↔ₘ ((index ≐ₘ numₘ(start)) ∧ₘ (value ≐ₘ head)) := by
        have hFirst := FirstOrder.Derives.impElim (Metatheory.Derives.iff_trans_m (T := standard_sequence_semantics_theory) (Γ := [])
            (ψ := (⟨index, value⟩ₘ ∈ₘ {⟨numₘ(start), head⟩ₘ}ₘ)) (φ := (⟨index, value⟩ₘ ≐ₘ ⟨numₘ(start), head⟩ₘ))
            (θ := ((index ≐ₘ numₘ(start)) ∧ₘ (value ≐ₘ head))) (Formula.Admissible.iff_right
              hSingletonPoint.admissible) (Formula.Admissible.iff_left
              hSingletonPoint.admissible) (Formula.Admissible.iff_right
              hCoordinates.admissible))
          hSingletonPoint
        exact FirstOrder.Derives.impElim hFirst hCoordinates
      have hCombined := stdseq_disj_congr hSingletonCoordinate hTailIff
      have hTrans :
          ⊢ₘ[standard_sequence_semantics_theory] (⟨index, value⟩ₘ ∈ₘ ({⟨numₘ(start), head⟩ₘ}ₘ ∪ₘ
                standard_sequence_from (start + 1) tail)) ↔ₘ (((index ≐ₘ numₘ(start)) ∧ₘ (value ≐ₘ head)) ∨ₘ
                standard_sequence_pair_member_condition (start + 1) tail index value) := by
        have hFirst := FirstOrder.Derives.impElim (Metatheory.Derives.iff_trans_m (T := standard_sequence_semantics_theory) (Γ := [])
            (ψ := (⟨index, value⟩ₘ ∈ₘ ({⟨numₘ(start), head⟩ₘ}ₘ ∪ₘ
                standard_sequence_from (start + 1) tail))) (φ := ((⟨index, value⟩ₘ ∈ₘ {⟨numₘ(start), head⟩ₘ}ₘ) ∨ₘ
              (⟨index, value⟩ₘ ∈ₘ standard_sequence_from (start + 1) tail))) (θ := (((index ≐ₘ numₘ(start)) ∧ₘ (value ≐ₘ head)) ∨ₘ
              standard_sequence_pair_member_condition (start + 1) tail index value)) (Formula.Admissible.iff_right
              hUnionPoint.admissible) (Formula.Admissible.iff_left
              hUnionPoint.admissible) (Formula.Admissible.iff_right
              hCombined.admissible))
          hUnionPoint
        exact FirstOrder.Derives.impElim hFirst hCombined
      simpa [standard_sequence_from, standard_sequence_pair_member_condition] using hTrans
def standard_sequence_domain_condition (start : Nat) : List SetTerm → SetTerm → SetFormula
  | ([] : List SetTerm), _ => Formula.falsum
  | _ :: rest, index =>
      (index ≐ₘ numₘ(start)) ∨ₘ
        standard_sequence_domain_condition (start + 1) rest index
/-- 标准序列定义域条件按外部列表递归保持 admissibility。 -/
theorem standard_sequence_domain_condition_admissible (start : Nat) (elements : List SetTerm) (index : SetTerm) (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible (standard_sequence_domain_condition
        start elements index) := by
  induction elements generalizing start with
  | nil =>
      exact Formula.Admissible.falsum
  | cons _ tail ih =>
      exact Formula.Admissible.disj (Formula.Admissible.equal
          hIndex (finite_numeral_term_admissible start)) (ih (start + 1))
/-- 标准序列定义域条件的可计算证书扩展。 -/
@[formula_check]
theorem standard_sequence_domain_condition_check
    (start : Nat) (elements : List SetTerm) (index : SetTerm)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.CheckCertificate
      (standard_sequence_domain_condition start elements index) :=
  Formula.check_admissible_complete
    (standard_sequence_domain_condition_admissible
      start elements index hIndex)
private theorem standard_sequence_pair_member_condition_openAt (start : Nat) (elements : List SetTerm) (depth : Nat) (replacement index value : SetTerm)
    (hElements : ∀ element, element ∈ elements →
      Term.BoundClosed element) :
    Formula.openAt SetSort.set depth replacement (standard_sequence_pair_member_condition start elements index value) =
      standard_sequence_pair_member_condition start elements (Term.openAt SetSort.set depth replacement index)
        (Term.openAt SetSort.set depth replacement value) := by
  induction elements generalizing start with
  | nil =>
      rfl
  | cons head tail ih =>
      have hHead := hElements head (by simp)
      have hTail : ∀ element, element ∈ tail → Term.BoundClosed element := by
        intro element hElement
        exact hElements element (by simp [hElement])
      have hNum := (finite_numeral_term_admissible start).2
      have hNumOpen := Term.openAt_eq_self_of_boundClosed
        SetSort.set depth replacement (numₘ(start)) hNum
      have hHeadOpen := Term.openAt_eq_self_of_boundClosed
        SetSort.set depth replacement head hHead
      simp [standard_sequence_pair_member_condition, Formula.openAt, ih (start + 1) hTail,
        hNumOpen, hHeadOpen]
private theorem finite_numeral_term_fresh :
    ∀ number, (SetSort.set, 0) ∉ Term.freeSupport (numₘ(number)) := by
  intro number
  rw [finite_numeral_term_freeSupport number]
  exact List.not_mem_nil
theorem standard_sequence_from_fresh_at (id : FreeVarId) (start : Nat) {elements : List SetTerm} (hElementsFresh : ∀ element, element ∈ elements →
      (SetSort.set, id) ∉ Term.freeSupport element) : (SetSort.set, id) ∉
      Term.freeSupport (standard_sequence_from start elements) := by
  induction elements generalizing start with
  | nil =>
      intro hMember
      cases hMember
  | cons head tail ih =>
      have hHead := hElementsFresh head (by simp)
      have hTail : ∀ element, element ∈ tail → (SetSort.set, id) ∉ Term.freeSupport element := by
        intro element hElement
        exact hElementsFresh element (by simp [hElement])
      intro hMember
      have hSupport :
          Term.freeSupport (standard_sequence_from start (head :: tail)) =
            Term.freeSupport (numₘ(start)) ++ (Term.freeSupport head ++
                Term.freeSupport (standard_sequence_from (start + 1) tail)) := by
        simp [standard_sequence_from, Term.freeSupport,
          Term.freeSupportList]
      rw [hSupport] at hMember
      rcases List.mem_append.mp hMember with hMember | hMember
      · rw [finite_numeral_term_freeSupport start] at hMember
        cases hMember
      · rcases List.mem_append.mp hMember with hMember | hMember
        · exact hHead hMember
        · exact ih (start + 1) hTail hMember
private theorem standard_sequence_from_fresh (start : Nat) {elements : List SetTerm} (hElementsFresh : ∀ element, element ∈ elements →
      (SetSort.set, 0) ∉ Term.freeSupport element) : (SetSort.set, 0) ∉
      Term.freeSupport (standard_sequence_from start elements) := by
  induction elements generalizing start with
  | nil =>
      intro hMember
      cases hMember
  | cons head tail ih =>
      have hHead := hElementsFresh head (by simp)
      have hTail : ∀ element, element ∈ tail → (SetSort.set, 0) ∉ Term.freeSupport element := by
        intro element hElement
        exact hElementsFresh element (by simp [hElement])
      intro hMember
      have hSupport :
          Term.freeSupport (standard_sequence_from start (head :: tail)) =
            Term.freeSupport (numₘ(start)) ++ (Term.freeSupport head ++
                Term.freeSupport (standard_sequence_from (start + 1) tail)) := by
        simp [standard_sequence_from, Term.freeSupport,
          Term.freeSupportList]
      rw [hSupport] at hMember
      rcases List.mem_append.mp hMember with hMember | hMember
      · exact (finite_numeral_term_fresh start) hMember
      · rcases List.mem_append.mp hMember with hMember | hMember
        · exact hHead hMember
        · exact ih (start + 1) hTail hMember
private theorem standard_sequence_pair_member_condition_fresh (start : Nat) {elements : List SetTerm} (index : SetTerm)
    (hIndexFresh : (SetSort.set, 0) ∉ Term.freeSupport index) (hElementsFresh : ∀ element, element ∈ elements → (SetSort.set, 0) ∉ Term.freeSupport element) :
    (SetSort.set, 0) ∉
      Formula.freeSupport (standard_sequence_pair_member_condition start elements index bₛ#0) := by
  induction elements generalizing start with
  | nil =>
      intro h
      cases h
  | cons head tail ih =>
      have hHead := hElementsFresh head (by simp)
      have hTail : ∀ element, element ∈ tail → (SetSort.set, 0) ∉ Term.freeSupport element := by
        intro element hElement
        exact hElementsFresh element (by simp [hElement])
      have hRec := ih (start + 1) hTail
      intro hMember
      simp [standard_sequence_pair_member_condition,
        Formula.freeSupport] at hMember
      change (SetSort.set, 0) ∈
        Term.freeSupport index ++ (Term.freeSupport (numₘ(start)) ++ (Term.freeSupport (bₛ#0) ++ (Term.freeSupport head ++
                Formula.freeSupport (standard_sequence_pair_member_condition (start + 1) tail index bₛ#0)))) at hMember
      rcases List.mem_append.mp hMember with hIndex | hRest
      · exact hIndexFresh hIndex
      · rcases List.mem_append.mp hRest with hNum | hRest
        · exact (finite_numeral_term_fresh start) hNum
        · rcases List.mem_append.mp hRest with hBvar | hRest
          · cases hBvar
          · rcases List.mem_append.mp hRest with hHeadMember | hRecMember
            · exact hHead hHeadMember
            · exact hRec hRecMember
theorem relation_formula_fresh (left right : SetTerm) (hLeft : (SetSort.set, 0) ∉ Term.freeSupport left)
    (hRight : (SetSort.set, 0) ∉ Term.freeSupport right) : (SetSort.set, 0) ∉ Formula.freeSupport (left ∈ₘ right) := by
  intro hMember
  simp only [Formula.freeSupport, Term.freeSupportList] at hMember
  change (SetSort.set, 0) ∈
    Term.freeSupport left ++ (Term.freeSupport right ++ []) at hMember
  rcases List.mem_append.mp hMember with hLeftMember | hRightMember
  · exact hLeft hLeftMember
  · have hRightMember' : (SetSort.set, 0) ∈ Term.freeSupport right := by
      simpa using hRightMember
    exact hRight hRightMember'
private theorem equality_formula_fresh (left right : SetTerm) (hLeft : (SetSort.set, 0) ∉ Term.freeSupport left)
    (hRight : (SetSort.set, 0) ∉ Term.freeSupport right) : (SetSort.set, 0) ∉ Formula.freeSupport (left ≐ₘ right) := by
  intro hMember
  simp only [Formula.freeSupport] at hMember
  change (SetSort.set, 0) ∈
    Term.freeSupport left ++ Term.freeSupport right at hMember
  rcases List.mem_append.mp hMember with hLeftMember | hRightMember
  · exact hLeft hLeftMember
  · exact hRight hRightMember
private theorem disj_formula_fresh (left right : SetFormula) (hLeft : (SetSort.set, 0) ∉ Formula.freeSupport left)
    (hRight : (SetSort.set, 0) ∉ Formula.freeSupport right) : (SetSort.set, 0) ∉ Formula.freeSupport (left ∨ₘ right) := by
  intro hMember
  simp only [Formula.freeSupport] at hMember
  change (SetSort.set, 0) ∈
    Formula.freeSupport left ++ Formula.freeSupport right at hMember
  rcases List.mem_append.mp hMember with hLeftMember | hRightMember
  · exact hLeft hLeftMember
  · exact hRight hRightMember
private theorem conj_formula_fresh (left right : SetFormula) (hLeft : (SetSort.set, 0) ∉ Formula.freeSupport left)
    (hRight : (SetSort.set, 0) ∉ Formula.freeSupport right) : (SetSort.set, 0) ∉ Formula.freeSupport (left ∧ₘ right) := by
  intro hMember
  simp only [Formula.freeSupport] at hMember
  change (SetSort.set, 0) ∈
    Formula.freeSupport left ++ Formula.freeSupport right at hMember
  rcases List.mem_append.mp hMember with hLeftMember | hRightMember
  · exact hLeft hLeftMember
  · exact hRight hRightMember
theorem ordered_pair_term_fresh (left right : SetTerm) (hLeft : (SetSort.set, 0) ∉ Term.freeSupport left)
    (hRight : (SetSort.set, 0) ∉ Term.freeSupport right) : (SetSort.set, 0) ∉ Term.freeSupport (⟨left, right⟩ₘ) := by
  intro hMember
  simp only [Term.freeSupport, Term.freeSupportList] at hMember
  change (SetSort.set, 0) ∈
    Term.freeSupport left ++ (Term.freeSupport right ++ []) at hMember
  rcases List.mem_append.mp hMember with hLeftMember | hRightMember
  · exact hLeft hLeftMember
  · have hRightMember' : (SetSort.set, 0) ∈ Term.freeSupport right := by
      simpa using hRightMember
    exact hRight hRightMember'
private theorem standard_sequence_domain_condition_fresh (start : Nat) {elements : List SetTerm} (index : SetTerm)
    (hIndexFresh : (SetSort.set, 0) ∉ Term.freeSupport index) : (SetSort.set, 0) ∉
      Formula.freeSupport (standard_sequence_domain_condition start elements index) := by
  induction elements generalizing start with
  | nil =>
      intro hMember
      cases hMember
  | cons head tail ih =>
      have hTail := ih (start + 1)
      have hNumFresh := finite_numeral_term_fresh start
      exact disj_formula_fresh (index ≐ₘ numₘ(start)) (standard_sequence_domain_condition (start + 1) tail index)
        (equality_formula_fresh index (numₘ(start)) hIndexFresh hNumFresh)
        hTail
private theorem standard_sequence_from_graph_exists_iff_domain_condition_nil (start : Nat) (index : SetTerm) (hIndex : Term.Admissible index SetSort.set)
    (hIndexFresh : (SetSort.set, 0) ∉ Term.freeSupport index) :
    ⊢ₘ[standard_sequence_semantics_theory] (∃ₘ[SetSort.set],
        ⟨index, bₛ#0⟩ₘ ∈ₘ standard_sequence_from start []) ↔ₘ
        standard_sequence_domain_condition start [] index := by
  let base : SetFormula :=
    ⟨index, bₛ#0⟩ₘ ∈ₘ standard_sequence_from start []
  let point : SetFormula :=
    Formula.openAt SetSort.set 0 (x#0) base
  have hPairIff := standard_sequence_from_pair_member_iff start (elements := [])
    index (x#0) (by simp) hIndex (set_variable_admissible 0)
  have hPointIff :
      ⊢ₘ[standard_sequence_semantics_theory] point ↔ₘ Formula.falsum := by
    have hIndexOpen :
        Term.openAt SetSort.set 0 (x#0) index = index :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 (x#0) index hIndex.2
    have hSequenceOpen :
        Term.openAt SetSort.set 0 (x#0) (standard_sequence_from start []) =
          standard_sequence_from start [] :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 (x#0) (standard_sequence_from start []) (seq_admissible_m start (by simp)).2
    simpa [point, base, standard_sequence_from, standard_sequence_pair_member_condition,
      Formula.openAt, Term.openAt, hIndexOpen, hSequenceOpen] using hPairIff
  let hTheoryFresh : ∀ formula, standard_sequence_semantics_theory formula → (SetSort.set, 0) freshForₘ formula := by
    intro formula hFormula
    have hSentence := standard_sequence_semantics_theory_sentence hFormula
    rw [hSentence.2]
    intro hMember
    cases hMember
  have hExistsIff := Metatheory.Derives.exists_iff_mono (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := 0)
    hTheoryFresh (by intro formula hFormula; simp at hFormula)
    hPointIff
  have hBaseFresh : (SetSort.set, 0) freshForₘ base := by
    simp [base, Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, standard_sequence_from, hIndexFresh]
  have hExistsIff' :
      ⊢ₘ[standard_sequence_semantics_theory] (∃ₘ[SetSort.set], base) ↔ₘ (∃ₘ[SetSort.set], Formula.falsum) := by
    simpa [point, base,
      Formula.closeFreeAt_openAt SetSort.set 0 0 base hBaseFresh] using hExistsIff
  have hFalseVacuous := Metatheory.Derives.exists_vacuous_iff (T := standard_sequence_semantics_theory) (Γ := [])
    (sort := SetSort.set) (eigen := 0) (body := Formula.falsum)
    Formula.Admissible.falsum (by intro h; simp [Formula.freeSupport] at h)
  have hResult :
      ⊢ₘ[standard_sequence_semantics_theory] (∃ₘ[SetSort.set], base) ↔ₘ Formula.falsum := by
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (Metatheory.Derives.iff_trans_m (Formula.Admissible.iff_right hExistsIff'.admissible)
          (Formula.Admissible.iff_left hExistsIff'.admissible)
          Formula.Admissible.falsum)
        hExistsIff')
      hFalseVacuous
  simpa [base, standard_sequence_domain_condition] using hResult
theorem standard_sequence_from_graph_exists_iff_domain_condition (start : Nat) {elements : List SetTerm} (index : SetTerm)
    (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hIndex : Term.Admissible index SetSort.set) (hIndexFresh : (SetSort.set, 0) ∉ Term.freeSupport index)
    (hElementsFresh : ∀ element, element ∈ elements → (SetSort.set, 0) ∉ Term.freeSupport element) :
    ⊢ₘ[standard_sequence_semantics_theory] (∃ₘ[SetSort.set],
        ⟨index, bₛ#0⟩ₘ ∈ₘ standard_sequence_from start elements) ↔ₘ
        standard_sequence_domain_condition start elements index := by
  induction elements generalizing start with
  | nil =>
      exact standard_sequence_from_graph_exists_iff_domain_condition_nil
        start index hIndex hIndexFresh
  | cons head tail ih =>
      let fullSequence := standard_sequence_from start (head :: tail)
      let tailSequence := standard_sequence_from (start + 1) tail
      let fullBase : SetFormula :=
        ⟨index, bₛ#0⟩ₘ ∈ₘ fullSequence
      let tailBase : SetFormula :=
        ⟨index, bₛ#0⟩ₘ ∈ₘ tailSequence
      let pairBase : SetFormula := ((index ≐ₘ numₘ(start)) ∧ₘ (bₛ#0 ≐ₘ head)) ∨ₘ
          standard_sequence_pair_member_condition (start + 1) tail index bₛ#0
      let fullPoint : SetFormula :=
        Formula.openAt SetSort.set 0 (x#0) fullBase
      let tailPoint : SetFormula :=
        Formula.openAt SetSort.set 0 (x#0) tailBase
      let pairPoint : SetFormula := ((index ≐ₘ numₘ(start)) ∧ₘ (x#0 ≐ₘ head)) ∨ₘ
          standard_sequence_pair_member_condition (start + 1) tail index (x#0)
      let tailCondition : SetFormula :=
        standard_sequence_domain_condition (start + 1) tail index
      have hHead : Term.Admissible head SetSort.set :=
        hElements head (by simp)
      have hTail : ∀ element, element ∈ tail →
          Term.Admissible element SetSort.set := by
        intro element hElement
        exact hElements element (by simp [hElement])
      have hElementsFreshTail : ∀ element, element ∈ tail → (SetSort.set, 0) ∉ Term.freeSupport element := by
        intro element hElement
        exact hElementsFresh element (by simp [hElement])
      have hFullAdmissible : Term.Admissible fullSequence SetSort.set :=
        seq_admissible_m start hElements
      have hTailAdmissible : Term.Admissible tailSequence SetSort.set :=
        seq_admissible_m (start + 1) hTail
      have hElementsBound : ∀ element, element ∈ (head :: tail) →
          Term.BoundClosed element := by
        intro element hElement
        exact (hElements element hElement).2
      have hTailBound : ∀ element, element ∈ tail → Term.BoundClosed element := by
        intro element hElement
        exact (hTail element hElement).2
      have hFullIffRaw := standard_sequence_from_pair_member_iff start (elements := head :: tail) index (x#0)
        hElements hIndex (set_variable_admissible 0)
      have hFullPointIff :
          ⊢ₘ[standard_sequence_semantics_theory] fullPoint ↔ₘ pairPoint := by
        have hIndexOpen := Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 (x#0) index hIndex.2
        have hSequenceOpen := Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 (x#0) fullSequence hFullAdmissible.2
        have hNumOpen := Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 (x#0) (numₘ(start)) (finite_numeral_term_admissible start).2
        have hHeadOpen := Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 (x#0) head hHead.2
        simpa [fullPoint, pairPoint, fullBase, pairBase,
          fullSequence, Formula.openAt,
          Term.openAt, standard_sequence_pair_member_condition, hIndexOpen, hSequenceOpen,
          hNumOpen, hHeadOpen] using
          hFullIffRaw
      have hTailIffRaw := standard_sequence_from_pair_member_iff (start + 1) (elements := tail) index (x#0)
        hTail hIndex (set_variable_admissible 0)
      have hTailPointIff :
          ⊢ₘ[standard_sequence_semantics_theory] tailPoint ↔ₘ
            standard_sequence_pair_member_condition (start + 1) tail index (x#0) := by
        have hIndexOpen := Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 (x#0) index hIndex.2
        have hSequenceOpen := Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 (x#0) tailSequence hTailAdmissible.2
        simpa [tailPoint, tailBase, tailSequence, Formula.openAt,
          Term.openAt, hIndexOpen, hSequenceOpen] using hTailIffRaw
      have hTailGraphIff := ih (start + 1) hTail hElementsFreshTail
      have hHeadFresh := hElementsFresh head (by simp)
      have hFullSequenceFresh :=
        standard_sequence_from_fresh start hElementsFresh
      have hTailSequenceFresh :=
        standard_sequence_from_fresh (start + 1) hElementsFreshTail
      have hTailPairConditionFresh := standard_sequence_pair_member_condition_fresh (start + 1) index hIndexFresh hElementsFreshTail
      let hTheoryFresh : ∀ formula, standard_sequence_semantics_theory formula → (SetSort.set, 0) freshForₘ formula := by
        intro formula hFormula
        have hSentence := standard_sequence_semantics_theory_sentence hFormula
        rw [hSentence.2]
        intro hMember
        cases hMember
      have hFullBaseFresh : (SetSort.set, 0) freshForₘ fullBase := by
        have hBvarFresh : (SetSort.set, 0) ∉
            Term.freeSupport (bₛ#0) := by
          intro h
          cases h
        have hPairFresh := ordered_pair_term_fresh
          index (bₛ#0) hIndexFresh hBvarFresh
        simpa [fullBase] using (relation_formula_fresh (⟨index, bₛ#0⟩ₘ) fullSequence hPairFresh
              hFullSequenceFresh)
      have hTailBaseFresh : (SetSort.set, 0) freshForₘ tailBase := by
        have hBvarFresh : (SetSort.set, 0) ∉
            Term.freeSupport (bₛ#0) := by
          intro h
          cases h
        have hPairFresh := ordered_pair_term_fresh
          index (bₛ#0) hIndexFresh hBvarFresh
        simpa [tailBase] using (relation_formula_fresh (⟨index, bₛ#0⟩ₘ) tailSequence hPairFresh
              hTailSequenceFresh)
      have hPairBaseFresh : (SetSort.set, 0) freshForₘ pairBase := by
        have hBvarFresh : (SetSort.set, 0) ∉
            Term.freeSupport (bₛ#0) := by
          intro h
          cases h
        have hFirstFresh := conj_formula_fresh (index ≐ₘ numₘ(start)) (bₛ#0 ≐ₘ head) (equality_formula_fresh index (numₘ(start)) hIndexFresh
            (finite_numeral_term_fresh start)) (equality_formula_fresh (bₛ#0) head hBvarFresh hHeadFresh)
        simpa [pairBase] using (disj_formula_fresh ((index ≐ₘ numₘ(start)) ∧ₘ (bₛ#0 ≐ₘ head))
            (standard_sequence_pair_member_condition (start + 1) tail index bₛ#0)
            hFirstFresh hTailPairConditionFresh)
      have hPairPointOpen :
          Formula.openAt SetSort.set 0 (x#0) pairBase = pairPoint := by
        have hNumOpen := Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 (x#0) (numₘ(start)) (finite_numeral_term_admissible start).2
        have hHeadOpen := Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 (x#0) head hHead.2
        have hPairConditionOpen := standard_sequence_pair_member_condition_openAt (start + 1) tail 0 (x#0) index bₛ#0 hTailBound
        have hIndexOpen := Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 (x#0) index hIndex.2
        simp [pairBase, pairPoint, Formula.openAt, Term.openAt,
          hNumOpen, hHeadOpen, hPairConditionOpen, hIndexOpen]
      have hExistsFullPairRaw := Metatheory.Derives.exists_iff_mono (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := 0)
        hTheoryFresh (by intro formula hFormula; simp at hFormula)
        hFullPointIff
      have hExistsFullPair :
          ⊢ₘ[standard_sequence_semantics_theory] (∃ₘ[SetSort.set], fullBase) ↔ₘ (∃ₘ[SetSort.set], pairBase) := by
        have hFullClose :
            Formula.closeFreeAt SetSort.set 0 0 fullPoint = fullBase := by
          simpa [fullPoint] using (Formula.closeFreeAt_openAt SetSort.set 0 0 fullBase hFullBaseFresh)
        have hPairClose :
            Formula.closeFreeAt SetSort.set 0 0 pairPoint = pairBase := by
          rw [← hPairPointOpen]
          exact Formula.closeFreeAt_openAt SetSort.set 0 0 pairBase hPairBaseFresh
        have hRaw :
            ⊢ₘ[standard_sequence_semantics_theory] (∃ₘ[SetSort.set],
                Formula.closeFreeAt SetSort.set 0 0 fullPoint) ↔ₘ (∃ₘ[SetSort.set],
                Formula.closeFreeAt SetSort.set 0 0 pairPoint) := by
          exact hExistsFullPairRaw
        simpa [hFullClose, hPairClose] using hRaw
      have hTailConditionFresh : (SetSort.set, 0) freshForₘ tailCondition := by
        exact standard_sequence_domain_condition_fresh (start + 1) index hIndexFresh
      have hIndexNumFresh : (SetSort.set, 0) ∉
          Formula.freeSupport (index ≐ₘ numₘ(start)) :=
        equality_formula_fresh index (numₘ(start)) hIndexFresh (finite_numeral_term_fresh start)
      have hConclusionFresh : (SetSort.set, 0) freshForₘ ((index ≐ₘ numₘ(start)) ∨ₘ tailCondition) := by
        exact disj_formula_fresh _ _ hIndexNumFresh hTailConditionFresh
      have hRToTail :
          ⊢ₘ[standard_sequence_semantics_theory]
            standard_sequence_pair_member_condition (start + 1) tail index (x#0) ⟶ₘ
              tailCondition := by
        nd_apply FirstOrder.Derives.impIntro
        have hTailPoint' : (standard_sequence_pair_member_condition (start + 1) tail index (x#0) :: []) ⊢ₘ[
              standard_sequence_semantics_theory] tailPoint := by
          have hIff := FirstOrder.Derives.context_weaken (Γ := []) (Δ := [standard_sequence_pair_member_condition (start + 1) tail index (x#0)])
            (by simp) hTailPointIff
          exact FirstOrder.Derives.iffElimLeft hIff
            (.assumption (by simp))
        have hTailExists : (standard_sequence_pair_member_condition (start + 1) tail index (x#0) :: []) ⊢ₘ[
              standard_sequence_semantics_theory] (∃ₘ[SetSort.set], tailBase) := by
          apply FirstOrder.Derives.exists_intro_fvar
            SetSort.set 0 tailBase
          simpa [tailPoint] using hTailPoint'
        have hGraphIff' := FirstOrder.Derives.context_weaken (Γ := []) (Δ := [standard_sequence_pair_member_condition (start + 1) tail index (x#0)])
          (by simp) hTailGraphIff
        exact FirstOrder.Derives.iffElimRight hGraphIff' hTailExists
      have hPairPointToCondition :
          ⊢ₘ[standard_sequence_semantics_theory]
            pairPoint ⟶ₘ ((index ≐ₘ numₘ(start)) ∨ₘ tailCondition) := by
        nd_apply FirstOrder.Derives.impIntro
        have hPair : (pairPoint :: []) ⊢ₘ[standard_sequence_semantics_theory] pairPoint :=
          .assumption (by simp)
        apply FirstOrder.Derives.disjElim (left := (index ≐ₘ numₘ(start)) ∧ₘ (x#0 ≐ₘ head))
            (right := standard_sequence_pair_member_condition (start + 1) tail index (x#0)) (conclusion := (index ≐ₘ numₘ(start)) ∨ₘ tailCondition)
            hPair
        · exact FirstOrder.Derives.disjIntroLeft <|
            FirstOrder.Derives.conjElimLeft
              (left := index ≐ₘ numₘ(start))
              (right := x#0 ≐ₘ head)
              (.assumption (by simp))
        · have hRToTail' := FirstOrder.Derives.context_weaken (Γ := []) (Δ := [pairPoint]) (by simp) hRToTail
          have hRToTail'' := FirstOrder.Derives.context_weaken_cons (assumption := standard_sequence_pair_member_condition (start + 1) tail index (x#0))
            hRToTail'
          exact FirstOrder.Derives.disjIntroRight
            (FirstOrder.Derives.impElim hRToTail''
              (FirstOrder.Derives.assumption (by simp)))
      have hPairExistsToConditionRaw :=
        Metatheory.Derives.exists_imp_of_imp (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := 0)
          hTheoryFresh (by intro formula hFormula; simp at hFormula)
          hConclusionFresh hPairPointToCondition
      have hPairClose' :
          Formula.closeFreeAt SetSort.set 0 0 pairPoint = pairBase := by
        rw [← hPairPointOpen]
        exact Formula.closeFreeAt_openAt SetSort.set 0 0 pairBase hPairBaseFresh
      have hPairExistsToCondition :
          ⊢ₘ[standard_sequence_semantics_theory] (∃ₘ[SetSort.set], pairBase) ⟶ₘ ((index ≐ₘ numₘ(start)) ∨ₘ tailCondition) := by
        simpa [hPairClose'] using hPairExistsToConditionRaw
      have hHeadOpenPair :
          Formula.openAt SetSort.set 0 head pairBase = ((index ≐ₘ numₘ(start)) ∧ₘ (head ≐ₘ head)) ∨ₘ
              standard_sequence_pair_member_condition (start + 1) tail index head := by
        have hIndexOpen := Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 head index hIndex.2
        have hNumOpen := Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 head (numₘ(start)) (finite_numeral_term_admissible start).2
        have hHeadOpen := Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 head head hHead.2
        have hConditionOpen := standard_sequence_pair_member_condition_openAt (start + 1) tail 0 head index bₛ#0 hTailBound
        simp [pairBase, Formula.openAt, Term.openAt,
          hIndexOpen, hNumOpen, hHeadOpen, hConditionOpen]
      have hHeadToPairOpen :
          ⊢ₘ[standard_sequence_semantics_theory] (index ≐ₘ numₘ(start)) ⟶ₘ
              Formula.openAt SetSort.set 0 head pairBase := by
        nd_apply FirstOrder.Derives.impIntro
        rw [hHeadOpenPair]
        have hEq :
            ⊢ₘ[standard_sequence_semantics_theory] head ≐ₘ head :=
          FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set) head
        exact FirstOrder.Derives.disjIntroLeft
          (right := standard_sequence_pair_member_condition
            (start + 1) tail index head) <|
          FirstOrder.Derives.conjIntro
            (.assumption (by simp))
            (FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := [index ≐ₘ numₘ(start)])
              (by simp) hEq)
      have hHeadToPairExists :
          ⊢ₘ[standard_sequence_semantics_theory] (index ≐ₘ numₘ(start)) ⟶ₘ (∃ₘ[SetSort.set], pairBase) := by
        nd_apply FirstOrder.Derives.impIntro
        have hOpen := FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := [index ≐ₘ numₘ(start)])
            (by simp) hHeadToPairOpen)
          (.assumption (by simp))
        exact FirstOrder.Derives.exists_intro
          (term := head) hOpen
      have hTailPointToPairPoint :
          ⊢ₘ[standard_sequence_semantics_theory] tailPoint ⟶ₘ pairPoint := by
        nd_apply FirstOrder.Derives.impIntro
        have hTailPoint : (tailPoint :: []) ⊢ₘ[standard_sequence_semantics_theory] tailPoint :=
          .assumption (by simp)
        have hTailIff' := FirstOrder.Derives.context_weaken (Γ := []) (Δ := [tailPoint]) (by simp) hTailPointIff
        exact FirstOrder.Derives.disjIntroRight
          (left := (index ≐ₘ numₘ(start)) ∧ₘ (x#0 ≐ₘ head))
          (FirstOrder.Derives.iffElimRight hTailIff' hTailPoint)
      have hTailExistsToPairExistsRaw :=
        Metatheory.Derives.exists_imp_mono (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := 0)
          hTheoryFresh (by intro formula hFormula; simp at hFormula)
          hTailPointToPairPoint
      have hTailClose :
          Formula.closeFreeAt SetSort.set 0 0 tailPoint = tailBase := by
        simpa [tailPoint] using (Formula.closeFreeAt_openAt SetSort.set 0 0 tailBase hTailBaseFresh)
      have hTailExistsToPairExists :
          ⊢ₘ[standard_sequence_semantics_theory] (∃ₘ[SetSort.set], tailBase) ⟶ₘ (∃ₘ[SetSort.set], pairBase) := by
        simpa [hTailClose, hPairClose'] using hTailExistsToPairExistsRaw
      have hTailToPairExists :
          ⊢ₘ[standard_sequence_semantics_theory] tailCondition ⟶ₘ (∃ₘ[SetSort.set], pairBase) := by
        apply Metatheory.Derives.imp_trans (φ := tailCondition) (ψ := (∃ₘ[SetSort.set], tailBase)) (θ := (∃ₘ[SetSort.set], pairBase)) (by
            nd_apply FirstOrder.Derives.impIntro
            have hGraphIff' := FirstOrder.Derives.context_weaken (Γ := []) (Δ := [tailCondition]) (by simp) hTailGraphIff
            have hTailCondition' :
                [tailCondition] ⊢ₘ[standard_sequence_semantics_theory]
                  standard_sequence_domain_condition (start + 1) tail index := by
              exact FirstOrder.Derives.assumption (by simp [tailCondition])
            have hWitness := FirstOrder.Derives.iffElimLeft hGraphIff'
              hTailCondition'
            simpa [tailCondition] using hWitness)
          hTailExistsToPairExists
      have hConditionToPairExists :
          ⊢ₘ[standard_sequence_semantics_theory] ((index ≐ₘ numₘ(start)) ∨ₘ tailCondition) ⟶ₘ (∃ₘ[SetSort.set], pairBase) := by
        nd_apply FirstOrder.Derives.impIntro
        have hCondition : (((index ≐ₘ numₘ(start)) ∨ₘ tailCondition) :: []) ⊢ₘ[
              standard_sequence_semantics_theory] ((index ≐ₘ numₘ(start)) ∨ₘ tailCondition) :=
          .assumption (by simp)
        apply FirstOrder.Derives.disjElim (left := index ≐ₘ numₘ(start)) (right := tailCondition) (conclusion := ∃ₘ[SetSort.set], pairBase)
            hCondition
        · exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := [index ≐ₘ numₘ(start), (index ≐ₘ numₘ(start)) ∨ₘ tailCondition])
              (by simp) hHeadToPairExists) (.assumption (by simp))
        · exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := [tailCondition, (index ≐ₘ numₘ(start)) ∨ₘ tailCondition])
              (by simp) hTailToPairExists) (.assumption (by simp))
      have hPairExistsIff :
          ⊢ₘ[standard_sequence_semantics_theory] (∃ₘ[SetSort.set], pairBase) ↔ₘ ((index ≐ₘ numₘ(start)) ∨ₘ tailCondition) := by
        exact FirstOrder.Derives.iffIntro (FirstOrder.Derives.imp_elim_assumption hPairExistsToCondition)
          (FirstOrder.Derives.imp_elim_assumption hConditionToPairExists)
      have hFullToPair :
          ⊢ₘ[standard_sequence_semantics_theory] (∃ₘ[SetSort.set], fullBase) ⟶ₘ (∃ₘ[SetSort.set], pairBase) := by
        nd_apply FirstOrder.Derives.impIntro
        exact FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken (Γ := []) (Δ := [∃ₘ[SetSort.set], fullBase]) (by simp)
            hExistsFullPair) (.assumption (by simp))
      have hPairToFull :
          ⊢ₘ[standard_sequence_semantics_theory] (∃ₘ[SetSort.set], pairBase) ⟶ₘ (∃ₘ[SetSort.set], fullBase) := by
        nd_apply FirstOrder.Derives.impIntro
        exact FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken (Γ := []) (Δ := [∃ₘ[SetSort.set], pairBase]) (by simp)
            hExistsFullPair) (.assumption (by simp))
      have hFullToCondition :
          ⊢ₘ[standard_sequence_semantics_theory] (∃ₘ[SetSort.set], fullBase) ⟶ₘ ((index ≐ₘ numₘ(start)) ∨ₘ tailCondition) :=
        Metatheory.Derives.imp_trans hFullToPair hPairExistsToCondition
      have hConditionToFull :
          ⊢ₘ[standard_sequence_semantics_theory] ((index ≐ₘ numₘ(start)) ∨ₘ tailCondition) ⟶ₘ (∃ₘ[SetSort.set], fullBase) :=
        Metatheory.Derives.imp_trans hConditionToPairExists hPairToFull
      have hCombined :
          ⊢ₘ[standard_sequence_semantics_theory] (∃ₘ[SetSort.set], fullBase) ↔ₘ ((index ≐ₘ numₘ(start)) ∨ₘ tailCondition) := by
        exact FirstOrder.Derives.iffIntro (FirstOrder.Derives.imp_elim_assumption hFullToCondition) (FirstOrder.Derives.imp_elim_assumption hConditionToFull)
      simpa [fullBase, fullSequence, tailCondition,
        standard_sequence_domain_condition] using hCombined
private theorem stdseq_equality_to_ordered_pair (member left right : SetTerm) (hMember : Term.Admissible member SetSort.set)
    (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] (member ≐ₘ ⟨left, right⟩ₘ) ⟶ₘ
        is_ordered_pair_formula member := by
  let pair := ⟨left, right⟩ₘ
  let body : SetFormula := is_ordered_pair_formula (x#0)
  have hPair : Term.Admissible pair SetSort.set :=
    ordered_pair_term_admissible left right hLeft hRight
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      [member ≐ₘ pair] ⊢ₘ[standard_sequence_semantics_theory]
        member ≐ₘ pair :=
    .assumption (by simp)
  have hIff := Metatheory.Derives.equality_iff_of_equality (T := standard_sequence_semantics_theory) (Γ := [member ≐ₘ pair]) (sort := SetSort.set) (eigen := 0)
    (left := member) (right := pair) (body := body)
    hEquality
  have hPairOrdered :
      [member ≐ₘ pair] ⊢ₘ[standard_sequence_semantics_theory]
        is_ordered_pair_formula pair :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := [member ≐ₘ pair]) (by simp) (stdseq_weaken_relation_function
        (ordered_pair_term_is_ordered_pair_derives left right hLeft hRight))
  have hMemberOrdered := FirstOrder.Derives.iffElimLeft hIff (by
      simpa [body, pair, Formula.substituteFree,
        Term.substituteFree, set_variable] using hPairOrdered)
  simpa [body, pair, Formula.substituteFree,
    Term.substituteFree, set_variable] using hMemberOrdered
private theorem standard_sequence_member_condition_ordered_pair (start : Nat) {elements : List SetTerm} (member : SetTerm)
    (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hMember : Term.Admissible member SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory]
      standard_sequence_member_condition start elements member ⟶ₘ
        is_ordered_pair_formula member := by
  induction elements generalizing start with
  | nil =>
      nd_apply FirstOrder.Derives.impIntro
      exact FirstOrder.Derives.falsumElim (by
          simpa [standard_sequence_member_condition] using (FirstOrder.Derives.assumption (T := standard_sequence_semantics_theory)
              (Γ := [standard_sequence_member_condition start [] member]) (φ := standard_sequence_member_condition start [] member)
              (by simp)))
  | cons head tail ih =>
      have hHead : Term.Admissible head SetSort.set :=
        hElements head (by simp)
      have hTail : ∀ element, element ∈ tail →
          Term.Admissible element SetSort.set := by
        intro element hElement
        exact hElements element (by simp [hElement])
      have hHeadCase := stdseq_equality_to_ordered_pair
        member (numₘ(start)) head hMember (finite_numeral_term_admissible start) hHead
      have hTailCase := ih (start + 1) hTail
      nd_apply FirstOrder.Derives.impIntro
      apply FirstOrder.Derives.disjElim (left := member ≐ₘ ⟨numₘ(start), head⟩ₘ) (right := standard_sequence_member_condition (start + 1) tail member)
          (conclusion := is_ordered_pair_formula member) (by
            simpa [standard_sequence_member_condition] using (FirstOrder.Derives.assumption (T := standard_sequence_semantics_theory)
                (Γ := [standard_sequence_member_condition start (head :: tail) member]) (φ := standard_sequence_member_condition start (head :: tail) member)
                (by simp)))
      · exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := [member ≐ₘ ⟨numₘ(start), head⟩ₘ,
              standard_sequence_member_condition start (head :: tail) member]) (by simp) hHeadCase) (.assumption (by simp))
      · exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := [standard_sequence_member_condition (start + 1) tail member,
              standard_sequence_member_condition start (head :: tail) member]) (by simp) hTailCase) (.assumption (by simp))
private theorem stdseq_member_is_ordered_pair (start : Nat) {elements : List SetTerm} (member : SetTerm) (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hMember : Term.Admissible member SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] (member ∈ₘ standard_sequence_from start elements) ⟶ₘ
        is_ordered_pair_formula member := by
  have hMemberIff := standard_sequence_from_member_iff start member hElements hMember
  have hCondition := standard_sequence_member_condition_ordered_pair
    start member hElements hMember
  nd_apply FirstOrder.Derives.impIntro
  have hMemberIff' := FirstOrder.Derives.context_weaken (Γ := []) (Δ := [member ∈ₘ standard_sequence_from start elements]) (by simp) hMemberIff
  have hCondition' := FirstOrder.Derives.iffElimRight
    hMemberIff' (.assumption (by simp))
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := [member ∈ₘ standard_sequence_from start elements]) (by simp) hCondition)
    hCondition'
theorem standard_sequence_from_is_relation (start : Nat) {elements : List SetTerm} (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hElementsFresh : ∀ element, element ∈ elements → (SetSort.set, 0) ∉ Term.freeSupport element) :
    ⊢ₘ[standard_sequence_semantics_theory]
      is_relation_formula (standard_sequence_from start elements) := by
  let sequence := standard_sequence_from start elements
  have hSequence : Term.Admissible sequence SetSort.set :=
    seq_admissible_m start hElements
  have hSequenceFresh : (SetSort.set, 0) ∉ Term.freeSupport sequence := by
    exact standard_sequence_from_fresh start hElementsFresh
  have hSequenceClose :
      Term.closeFreeAt SetSort.set 0 0 sequence = sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 0 0 sequence hSequence.2 hSequenceFresh
  have hPoint := stdseq_member_is_ordered_pair start (x#0)
    hElements (set_variable_admissible 0)
  have hClosed :
      ⊢ₘ[standard_sequence_semantics_theory]
        ∀ₘ[SetSort.set, 0], ((x#0 ∈ₘ sequence) ⟶ₘ is_ordered_pair_formula (x#0)) := by
    derive_close (0) using hPoint
  have hCondition :
      ⊢ₘ[standard_sequence_semantics_theory] is_relation_condition sequence := by
    simpa [is_relation_condition, sequence,
      Formula.closeFreeAt, Term.closeFreeAt, hSequenceClose] using hClosed
  have hDefinition := stdseq_weaken_relation_predicate (is_relation_iff_condition sequence hSequence)
  exact FirstOrder.Derives.iffElimLeft hDefinition hCondition
theorem stdseq_domain_term_fresh (id : FreeVarId) (relation : SetTerm) (hRelationFresh : (SetSort.set, id) ∉ Term.freeSupport relation) :
    (SetSort.set, id) ∉ Term.freeSupport (domₘ(relation)) := by
  intro hMember
  simp [Term.freeSupport, Term.freeSupportList] at hMember
  exact hRelationFresh hMember
theorem stdseq_graph_exists_to_domain (relation index : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) (hRelationFresh : (SetSort.set, 0) ∉ Term.freeSupport relation)
    (hIndexFresh : (SetSort.set, 0) ∉ Term.freeSupport index) (hIsRelation :
      ⊢ₘ[standard_sequence_semantics_theory] is_relation_formula relation) :
    ⊢ₘ[standard_sequence_semantics_theory] (∃ₘ[SetSort.set], ⟨index, bₛ#0⟩ₘ ∈ₘ relation) ⟶ₘ (index ∈ₘ domₘ(relation)) := by
  let base : SetFormula := ⟨index, bₛ#0⟩ₘ ∈ₘ relation
  let point : SetFormula := ⟨index, x#0⟩ₘ ∈ₘ relation
  let conclusion : SetFormula := index ∈ₘ domₘ(relation)
  have hPointRaw := stdseq_weaken_function_predicate (relation_member_left_coordinate_mem_domain
      relation index (x#0) hRelation hIndex (set_variable_admissible 0))
  have hPointImp :
      ⊢ₘ[standard_sequence_semantics_theory] point ⟶ₘ conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    have hRaw := FirstOrder.Derives.context_weaken (Γ := []) (Δ := [point]) (by simp) hPointRaw
    have hRelation' := FirstOrder.Derives.context_weaken (Γ := []) (Δ := [point]) (by simp) hIsRelation
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim hRaw hRelation') (by
        simpa [point] using
          (FirstOrder.Derives.assumption
            (T := standard_sequence_semantics_theory)
            (Γ := [point]) (φ := point) (by simp)))
  let hTheoryFresh : ∀ formula, standard_sequence_semantics_theory formula → (SetSort.set, 0) freshForₘ formula := by
    intro formula hFormula
    have hSentence := standard_sequence_semantics_theory_sentence hFormula
    rw [hSentence.2]
    intro hMember
    cases hMember
  have hConclusionFresh : (SetSort.set, 0) freshForₘ conclusion := by
    exact relation_formula_fresh index (domₘ(relation))
      hIndexFresh (stdseq_domain_term_fresh 0 relation hRelationFresh)
  have hLift := Metatheory.Derives.exists_imp_of_imp (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := 0)
    hTheoryFresh (by intro formula hFormula; simp at hFormula)
    hConclusionFresh hPointImp
  have hPointOpen :
      Formula.openAt SetSort.set 0 (x#0) base = point := by
    have hIndexOpen := Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#0) index hIndex.2
    have hRelationOpen := Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#0) relation hRelation.2
    simp [base, point, Formula.openAt, Term.openAt,
      hIndexOpen, hRelationOpen]
  have hBaseFresh : (SetSort.set, 0) freshForₘ base := by
    have hBvarFresh : (SetSort.set, 0) ∉
        Term.freeSupport (bₛ#0) := by
      intro hMember
      cases hMember
    exact relation_formula_fresh (⟨index, bₛ#0⟩ₘ) relation (ordered_pair_term_fresh index (bₛ#0) hIndexFresh hBvarFresh)
      hRelationFresh
  have hClose :
      Formula.closeFreeAt SetSort.set 0 0 point = base := by
    rw [← hPointOpen]
    exact Formula.closeFreeAt_openAt SetSort.set 0 0 base hBaseFresh
  simpa [base, conclusion, hClose] using hLift
private theorem stdseq_domain_coordinate_to_graph_exists (relation index : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) (hRelationFresh : (SetSort.set, 0) ∉ Term.freeSupport relation)
    (hIndexFresh : (SetSort.set, 0) ∉ Term.freeSupport index) (hIsRelation :
      ⊢ₘ[standard_sequence_semantics_theory] is_relation_formula relation) :
    ⊢ₘ[standard_sequence_semantics_theory]
      relation_domain_member_condition relation index ⟶ₘ (∃ₘ[SetSort.set], ⟨index, bₛ#0⟩ₘ ∈ₘ relation) := by
  let pair := x#0
  let membership : SetFormula := pair ∈ₘ relation
  let coordinateEquality : SetFormula := index ≐ₘ (pair)₀ₘ
  let pairCondition : SetFormula := membership ∧ₘ coordinateEquality
  let conclusion : SetFormula :=
    ∃ₘ[SetSort.set], ⟨index, bₛ#0⟩ₘ ∈ₘ relation
  have hPair : Term.Admissible pair SetSort.set :=
    set_variable_admissible 0
  have hPairLeft : Term.Admissible (pair)₀ₘ SetSort.set :=
    left_projection_term_admissible pair hPair
  have hPairRight : Term.Admissible (pair)₁ₘ SetSort.set :=
    right_projection_term_admissible pair hPair
  have hProjectionPair :
      Term.Admissible (⟨(pair)₀ₘ, (pair)₁ₘ⟩ₘ) SetSort.set :=
    ordered_pair_term_admissible (pair)₀ₘ (pair)₁ₘ hPairLeft hPairRight
  have hCanonicalPair :
      Term.Admissible (⟨index, (pair)₁ₘ⟩ₘ) SetSort.set :=
    ordered_pair_term_admissible index (pair)₁ₘ hIndex hPairRight
  have hPairCase :
      ⊢ₘ[standard_sequence_semantics_theory] pairCondition ⟶ₘ conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature := [pairCondition]
    have hCondition : Γ ⊢ₘ[standard_sequence_semantics_theory] pairCondition :=
      .assumption (by simp [Γ])
    have hMembership : Γ ⊢ₘ[standard_sequence_semantics_theory] membership :=
      FirstOrder.Derives.conjElimLeft hCondition
    have hCoordinate : Γ ⊢ₘ[standard_sequence_semantics_theory] coordinateEquality :=
      FirstOrder.Derives.conjElimRight hCondition
    have hReconstructRaw := stdseq_weaken_relation_plane (is_relation_member_eq_ordered_pair_projections
        relation pair hRelation hPair)
    have hReconstruct :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          pair ≐ₘ ⟨(pair)₀ₘ, (pair)₁ₘ⟩ₘ := by
      have hRaw := FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hReconstructRaw
      have hRelation' := FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hIsRelation
      exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim hRaw hRelation') (by simpa [Γ, membership] using hMembership)
    have hProjectionToPair :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          ⟨(pair)₀ₘ, (pair)₁ₘ⟩ₘ ≐ₘ pair :=
      Metatheory.Derives.equality_symm hReconstruct
    have hCoordinates := FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) (stdseq_weaken_ordered (ordered_pair_term_eq_iff_coordinates
          index (pair)₁ₘ (pair)₀ₘ (pair)₁ₘ
          hIndex hPairRight hPairLeft hPairRight))
    have hRightReflexive :
        Γ ⊢ₘ[standard_sequence_semantics_theory] (pair)₁ₘ ≐ₘ (pair)₁ₘ :=
      FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) ((pair)₁ₘ)
    have hCanonicalToProjection :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          ⟨index, (pair)₁ₘ⟩ₘ ≐ₘ
            ⟨(pair)₀ₘ, (pair)₁ₘ⟩ₘ :=
      FirstOrder.Derives.iffElimLeft hCoordinates (FirstOrder.Derives.conjIntro (by simpa [Γ, coordinateEquality] using hCoordinate)
          hRightReflexive)
    have hCanonicalToPair :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          ⟨index, (pair)₁ₘ⟩ₘ ≐ₘ pair :=
      Metatheory.Derives.equality_trans
        hCanonicalToProjection hProjectionToPair
    have hTransport := membership_left_iff_of_equality (⟨index, (pair)₁ₘ⟩ₘ) pair relation
      hCanonicalPair hPair hRelation hCanonicalToPair
    have hCanonicalMembership :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          ⟨index, (pair)₁ₘ⟩ₘ ∈ₘ relation :=
      FirstOrder.Derives.iffElimLeft hTransport (by simpa [Γ, membership] using hMembership)
    nd_apply FirstOrder.Derives.exists_intro
      (term := (pair)₁ₘ)
    have hIndexOpen := Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (pair)₁ₘ index hIndex.2
    have hRelationOpen := Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (pair)₁ₘ relation hRelation.2
    simpa [conclusion, Formula.openAt, Term.openAt,
      hIndexOpen, hRelationOpen] using hCanonicalMembership
  let hTheoryFresh : ∀ formula, standard_sequence_semantics_theory formula → (SetSort.set, 0) freshForₘ formula := by
    intro formula hFormula
    have hSentence := standard_sequence_semantics_theory_sentence hFormula
    rw [hSentence.2]
    intro hMember
    cases hMember
  have hConclusionFresh : (SetSort.set, 0) freshForₘ conclusion := by
    have hBvarFresh : (SetSort.set, 0) ∉
        Term.freeSupport (bₛ#0) := by
      intro hMember
      cases hMember
    have hBaseFresh := relation_formula_fresh (⟨index, bₛ#0⟩ₘ) relation (ordered_pair_term_fresh index (bₛ#0) hIndexFresh hBvarFresh)
      hRelationFresh
    simpa [conclusion, Formula.freeSupport] using hBaseFresh
  have hLift := Metatheory.Derives.exists_imp_of_imp (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := 0)
    hTheoryFresh (by intro formula hFormula; simp at hFormula)
    hConclusionFresh hPairCase
  have hRelationClose :
      Term.closeFreeAt SetSort.set 0 0 relation = relation :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 0 0 relation hRelation.2 hRelationFresh
  have hIndexClose :
      Term.closeFreeAt SetSort.set 0 0 index = index :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 0 0 index hIndex.2 hIndexFresh
  simpa [pair, pairCondition, membership, coordinateEquality, conclusion,
    relation_domain_member_condition,
    relation_coordinate_member_condition,
    relation_coordinate_projection_term,
    Formula.closeFreeAt, Term.closeFreeAt,
    hRelationClose, hIndexClose] using hLift
private theorem stdseq_domain_to_graph_exists (relation index : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) (hRelationFresh : (SetSort.set, 0) ∉ Term.freeSupport relation)
    (hIndexFresh : (SetSort.set, 0) ∉ Term.freeSupport index) (hIsRelation :
      ⊢ₘ[standard_sequence_semantics_theory] is_relation_formula relation) :
    ⊢ₘ[standard_sequence_semantics_theory] (index ∈ₘ domₘ(relation)) ⟶ₘ (∃ₘ[SetSort.set], ⟨index, bₛ#0⟩ₘ ∈ₘ relation) := by
  have hDomainIffRaw := stdseq_weaken_relation_domain (is_relation_domain_member_iff relation index hRelation hIndex)
  have hDomainIff := FirstOrder.Derives.impElim hDomainIffRaw hIsRelation
  have hCoordinateToGraph := stdseq_domain_coordinate_to_graph_exists
    relation index hRelation hIndex hRelationFresh hIndexFresh hIsRelation
  nd_apply FirstOrder.Derives.impIntro
  have hIff := FirstOrder.Derives.context_weaken (Γ := []) (Δ := [index ∈ₘ domₘ(relation)]) (by simp) hDomainIff
  have hCondition := FirstOrder.Derives.iffElimRight hIff
    (FirstOrder.Derives.assumption (by simp))
  have hCoordinate := FirstOrder.Derives.conjElimRight hCondition
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := [index ∈ₘ domₘ(relation)]) (by simp)
      hCoordinateToGraph)
    hCoordinate
theorem standard_sequence_relation_domain_member_iff_graph_exists (relation index : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) (hRelationFresh : (SetSort.set, 0) ∉ Term.freeSupport relation)
    (hIndexFresh : (SetSort.set, 0) ∉ Term.freeSupport index) (hIsRelation :
      ⊢ₘ[standard_sequence_semantics_theory] is_relation_formula relation) :
    ⊢ₘ[standard_sequence_semantics_theory] (index ∈ₘ domₘ(relation)) ↔ₘ (∃ₘ[SetSort.set], ⟨index, bₛ#0⟩ₘ ∈ₘ relation) := by
  exact FirstOrder.Derives.iffIntro (FirstOrder.Derives.imp_elim_assumption (stdseq_domain_to_graph_exists relation index hRelation hIndex
        hRelationFresh hIndexFresh hIsRelation)) (FirstOrder.Derives.imp_elim_assumption (stdseq_graph_exists_to_domain relation index hRelation hIndex
        hRelationFresh hIndexFresh hIsRelation))
end YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation
