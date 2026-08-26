import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.Numeral
/-!
# 标准有限序列的空间与折叠语义
本模块证明标准序列的映射、有限序列空间成员、逐点求值与有限折叠性质。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false

/-- 闭项族可在调用点降格为任意单编号新鲜性。 -/
theorem stdseq_element_fresh_of_support_nil
    {elements : List SetTerm}
    (hElementsClosed : ∀ element, element ∈ elements →
      Term.freeSupport element = [])
    (id : FreeVarId) :
    ∀ element, element ∈ elements →
      (SetSort.set, id) ∉ Term.freeSupport element := by
  intro element hElement
  rw [hElementsClosed element hElement]
  exact List.not_mem_nil
/--
在任意标准语义扩张理论中，给定定义域等式和值域上界后，标准序列满足映射谓词。
-/
theorem standard_sequence_from_is_mapping_of_theory
    {T : SetTheory} (hTheory :
      ∀ formula,
        standard_sequence_semantics_theory formula → T formula) (hTheorySentence :
      ∀ formula, T formula → Formula.Sentence formula) (start : Nat) {elements : List SetTerm} (source target : SetTerm)
    (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hElementsClosed : ∀ element, element ∈ elements →
      Term.freeSupport element = []) (hSource : Term.Admissible source SetSort.set) (hTarget : Term.Admissible target SetSort.set)
    (hTargetClosed : Term.freeSupport target = []) (hDomainEquality :
      ⊢ₘ[T]
        source ≐ₘ domₘ(standard_sequence_from start elements)) (hTargetMember : ∀ element, element ∈ elements →
      ⊢ₘ[T] element ∈ₘ target) :
    ⊢ₘ[T]
      is_mapping_formula (standard_sequence_from start elements) source target := by
  let sequence := standard_sequence_from start elements
  have hSequence : Term.Admissible sequence SetSort.set :=
    seq_admissible_m start hElements
  have hFunction :=
    FirstOrder.Derives.theory_weaken hTheory <|
      standard_sequence_from_is_function
        start hElements
        (stdseq_element_fresh_of_support_nil
          hElementsClosed 0)
        (stdseq_element_fresh_of_support_nil
          hElementsClosed 1)
        (stdseq_element_fresh_of_support_nil
          hElementsClosed 2)
  have hRangeSubset :=
    standard_sequence_from_range_subset_of_theory
      hTheory hTheorySentence
      start target hElements hElementsClosed
      hTarget hTargetClosed hTargetMember
  have hCondition :
      ⊢ₘ[T]
        is_mapping_condition sequence source target :=
    FirstOrder.Derives.conjIntro (by simpa [sequence] using hFunction) (FirstOrder.Derives.conjIntro (by simpa [sequence] using hDomainEquality)
        (by simpa [sequence] using hRangeSubset))
  have hDefinition :=
    FirstOrder.Derives.theory_weaken hTheory <|
      stdseq_weaken_mapping_predicate (is_mapping_iff_condition
          sequence source target hSequence hSource hTarget)
  exact FirstOrder.Derives.iffElimLeft hDefinition hCondition
/-- 给定定义域等式和值域上界后，标准序列满足映射谓词。 -/
theorem standard_sequence_from_is_mapping (start : Nat) {elements : List SetTerm} (source target : SetTerm) (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hElementsClosed : ∀ element, element ∈ elements →
      Term.freeSupport element = []) (hSource : Term.Admissible source SetSort.set) (hTarget : Term.Admissible target SetSort.set)
    (hTargetClosed : Term.freeSupport target = []) (hDomainEquality :
      ⊢ₘ[standard_sequence_semantics_theory]
        source ≐ₘ domₘ(standard_sequence_from start elements)) (hTargetMember : ∀ element, element ∈ elements →
      ⊢ₘ[standard_sequence_semantics_theory] element ∈ₘ target) :
    ⊢ₘ[standard_sequence_semantics_theory]
      is_mapping_formula (standard_sequence_from start elements) source target :=
  standard_sequence_from_is_mapping_of_theory (fun _ hFormula => hFormula) (fun _ hFormula =>
      standard_sequence_semantics_theory_sentence hFormula)
    start source target hElements hElementsClosed
    hSource hTarget hTargetClosed
    hDomainEquality hTargetMember
/--
在任意标准语义扩张理论中，从零开始的标准序列满足有限序列成员条件。
-/
theorem standard_sequence_member_condition_derives_of_theory
    {T : SetTheory} (hTheory :
      ∀ formula,
        standard_sequence_semantics_theory formula → T formula) (hTheorySentence :
      ∀ formula, T formula → Formula.Sentence formula)
    {elements : List SetTerm} (target : SetTerm) (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hElementsClosed : ∀ element, element ∈ elements →
      Term.freeSupport element = []) (hTarget : Term.Admissible target SetSort.set) (hTargetClosed : Term.freeSupport target = [])
    (hTargetMember : ∀ element, element ∈ elements →
      ⊢ₘ[T] element ∈ₘ target) :
    ⊢ₘ[T]
      finite_sequence_member_condition target (standard_sequence elements) := by
  let sequence := standard_sequence elements
  let source := numₘ(elements.length)
  have hSequence : Term.Admissible sequence SetSort.set :=
    seq_admissible_m 0 hElements
  have hSource : Term.Admissible source SetSort.set :=
    finite_numeral_term_admissible elements.length
  have hDomain : Term.Admissible (domₘ(sequence)) SetSort.set :=
    domain_term_admissible sequence hSequence
  have hDomainEq :=
    FirstOrder.Derives.theory_weaken hTheory <|
      standard_sequence_domain_eq_numeral_length
        hElements
        (stdseq_element_fresh_of_support_nil
          hElementsClosed 0)
        (stdseq_element_fresh_of_support_nil
          hElementsClosed 1)
  have hSourceDomain :
      ⊢ₘ[T] source ≐ₘ domₘ(sequence) :=
    Metatheory.Derives.equality_symm
      (by simpa [sequence, source] using hDomainEq)
  have hMapping :=
    standard_sequence_from_is_mapping_of_theory
      hTheory hTheorySentence
      0 source target hElements hElementsClosed
      hSource hTarget hTargetClosed hSourceDomain hTargetMember
  have hSourceOmega :=
    FirstOrder.Derives.theory_weaken hTheory <|
      standard_sequence_finite_numeral_mem_omega elements.length
  nd_apply FirstOrder.Derives.exists_intro (term := source) (body := (bₛ#0 ∈ₘ ωₘ) ∧ₘ
        is_mapping_formula sequence bₛ#0 target)
  have hSequenceOpen := Term.openAt_eq_self_of_boundClosed
    SetSort.set 0 source sequence hSequence.2
  have hTargetOpen := Term.openAt_eq_self_of_boundClosed
    SetSort.set 0 source target hTarget.2
  simpa [finite_sequence_member_condition, sequence, source,
    Formula.openAt, Term.openAt, hSequenceOpen, hTargetOpen] using (FirstOrder.Derives.conjIntro
      hSourceOmega (by simpa [sequence, source] using hMapping))
/-- 从零开始的标准序列满足有限序列成员条件。 -/
theorem standard_sequence_member_condition_derives
    {elements : List SetTerm} (target : SetTerm) (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hElementsClosed : ∀ element, element ∈ elements →
      Term.freeSupport element = []) (hTarget : Term.Admissible target SetSort.set) (hTargetClosed : Term.freeSupport target = [])
    (hTargetMember : ∀ element, element ∈ elements →
      ⊢ₘ[standard_sequence_semantics_theory] element ∈ₘ target) :
    ⊢ₘ[standard_sequence_semantics_theory]
      finite_sequence_member_condition target (standard_sequence elements) :=
  standard_sequence_member_condition_derives_of_theory (fun _ hFormula => hFormula) (fun _ hFormula =>
      standard_sequence_semantics_theory_sentence hFormula)
    target hElements hElementsClosed
    hTarget hTargetClosed hTargetMember
/--
在任意标准语义扩张理论中，非空目标集上的标准序列属于相应的有限序列空间。
-/
theorem standard_sequence_mem_sequence_space_of_theory
    {T : SetTheory} (hTheory :
      ∀ formula,
        standard_sequence_semantics_theory formula → T formula) (hTheorySentence :
      ∀ formula, T formula → Formula.Sentence formula)
    {elements : List SetTerm} (target : SetTerm) (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hElementsClosed : ∀ element, element ∈ elements →
      Term.freeSupport element = []) (hTarget : Term.Admissible target SetSort.set) (hTargetClosed : Term.freeSupport target = []) (hTargetNonempty :
      ⊢ₘ[T] target ≠ₘ ∅ₘ) (hTargetMember : ∀ element, element ∈ elements →
      ⊢ₘ[T] element ∈ₘ target) :
    ⊢ₘ[T]
      standard_sequence elements ∈ₘ seq_spaceₘ(target) := by
  let sequence := standard_sequence elements
  let sequenceSpace := seq_spaceₘ(target)
  have hSequence : Term.Admissible sequence SetSort.set :=
    seq_admissible_m 0 hElements
  have hSequenceSpace : Term.Admissible sequenceSpace SetSort.set :=
    finite_sequence_space_term_admissible target hTarget
  have hContract :=
    FirstOrder.Derives.theory_weaken hTheory <|
      stdseq_weaken_finite_sequence_space (finite_sequence_space_definition_instance_derives
          target sequenceSpace hTarget hSequenceSpace)
  have hSpec :
      ⊢ₘ[T]
        finite_sequence_space_spec target sequenceSpace := by
    have hIff := FirstOrder.Derives.impElim hContract hTargetNonempty
    exact FirstOrder.Derives.iffElimRight hIff (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) sequenceSpace)
  have hAtSequence := FirstOrder.Derives.forall_elim
    (term := sequence) hSpec
  have hTargetOpen (depth : Nat) := Term.openAt_eq_self_of_boundClosed
    SetSort.set depth sequence target hTarget.2
  have hSequenceSpaceOpen (depth : Nat) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth sequence sequenceSpace hSequenceSpace.2
  have hMemberIff :
      ⊢ₘ[T] (sequence ∈ₘ sequenceSpace) ↔ₘ
          finite_sequence_member_condition target sequence := by
    simpa [finite_sequence_space_spec,
      finite_sequence_member_condition,
      Formula.openAt, Formula.next_depth, Term.openAt,
      hTargetOpen, hSequenceSpaceOpen] using hAtSequence
  exact FirstOrder.Derives.iffElimLeft hMemberIff (by
      simpa [sequence] using
        standard_sequence_member_condition_derives_of_theory
          hTheory hTheorySentence
          target hElements hElementsClosed
          hTarget hTargetClosed hTargetMember)

/--
上下文中的动态元素组成的标准序列属于有限序列空间。

与闭项版相比，本接口只要求内部函数证明使用的 `0/1/2` 对元素新鲜，并要求
值域与子集证明使用的 `0/1` 对目标项及上下文新鲜。
-/
theorem standard_sequence_mem_sequence_space_of_theory_context
    {T : SetTheory} {Γ : Context signature}
    (hTheory :
      ∀ formula,
        standard_sequence_semantics_theory formula → T formula)
    (hTheorySentence :
      ∀ formula, T formula → Formula.Sentence formula)
    {elements : List SetTerm}
    (target : SetTerm)
    (hElements :
      ∀ element, element ∈ elements →
        Term.Admissible element SetSort.set)
    (hElementsFreshZero :
      ∀ element, element ∈ elements →
        (SetSort.set, 0) ∉ Term.freeSupport element)
    (hElementsFreshOne :
      ∀ element, element ∈ elements →
        (SetSort.set, 1) ∉ Term.freeSupport element)
    (hElementsFreshTwo :
      ∀ element, element ∈ elements →
        (SetSort.set, 2) ∉ Term.freeSupport element)
    (hTarget : Term.Admissible target SetSort.set)
    (hTargetFreshZero :
      (SetSort.set, 0) ∉ Term.freeSupport target)
    (hTargetFreshOne :
      (SetSort.set, 1) ∉ Term.freeSupport target)
    (hContextFreshZero :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, 0) ∉ Formula.freeSupport formula)
    (hContextFreshOne :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, 1) ∉ Formula.freeSupport formula)
    (hTargetNonempty :
      Γ ⊢ₘ[T] target ≠ₘ ∅ₘ)
    (hTargetMember :
      ∀ element, element ∈ elements →
        Γ ⊢ₘ[T] element ∈ₘ target) :
    Γ ⊢ₘ[T]
      standard_sequence elements ∈ₘ
        seq_spaceₘ(target) := by
  let sequence := standard_sequence elements
  let source := numₘ(elements.length)
  let sequenceSpace := seq_spaceₘ(target)
  have hSequence :
      Term.Admissible sequence SetSort.set :=
    seq_admissible_m 0 hElements
  have hSource :
      Term.Admissible source SetSort.set :=
    finite_numeral_term_admissible elements.length
  have hSequenceSpace :
      Term.Admissible sequenceSpace SetSort.set :=
    finite_sequence_space_term_admissible
      target hTarget
  have hFunction :
      Γ ⊢ₘ[T] is_function_formula sequence :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <| by
          simpa [sequence] using
            standard_sequence_from_is_function
              0 hElements
              hElementsFreshZero
              hElementsFreshOne
              hElementsFreshTwo
  have hDomainEquality :
      Γ ⊢ₘ[T]
        source ≐ₘ domₘ(sequence) :=
    Metatheory.Derives.equality_symm <|
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          FirstOrder.Derives.theory_weaken hTheory <| by
            simpa [sequence, source] using
              standard_sequence_domain_eq_numeral_length
                hElements
                hElementsFreshZero
                hElementsFreshOne
  have hRangeSubset :
      Γ ⊢ₘ[T]
        ranₘ(sequence) ⊆ₘ target := by
    simpa [sequence] using
      standard_sequence_from_range_subset_of_theory_context
        hTheory hTheorySentence
        0 target hElements
        hElementsFreshZero hElementsFreshOne
        hTarget hTargetFreshZero hTargetFreshOne
        hContextFreshZero hContextFreshOne
        hTargetMember
  have hMappingCondition :
      Γ ⊢ₘ[T]
        is_mapping_condition sequence source target :=
    FirstOrder.Derives.conjIntro
      hFunction <|
        FirstOrder.Derives.conjIntro
          hDomainEquality hRangeSubset
  have hMappingDefinition :
      Γ ⊢ₘ[T]
        is_mapping_formula sequence source target ↔ₘ
          is_mapping_condition sequence source target :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <|
          stdseq_weaken_mapping_predicate <|
            is_mapping_iff_condition
              sequence source target
              hSequence hSource hTarget
  have hMapping :
      Γ ⊢ₘ[T]
        is_mapping_formula sequence source target :=
    FirstOrder.Derives.iffElimLeft
      hMappingDefinition hMappingCondition
  have hSourceOmega :
      Γ ⊢ₘ[T] source ∈ₘ ωₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <| by
          simpa [source] using
            standard_sequence_finite_numeral_mem_omega
              elements.length
  have hMemberCondition :
      Γ ⊢ₘ[T]
        finite_sequence_member_condition
          target sequence := by
    nd_apply FirstOrder.Derives.exists_intro
      (term := source)
      (body :=
        (bₛ#0 ∈ₘ ωₘ) ∧ₘ
          is_mapping_formula sequence bₛ#0 target)
    have hSequenceOpen :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 source sequence hSequence.2
    have hTargetOpen :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 source target hTarget.2
    simpa [finite_sequence_member_condition,
      Formula.openAt, Term.openAt,
      hSequenceOpen, hTargetOpen] using
        FirstOrder.Derives.conjIntro
          hSourceOmega hMapping
  have hContract :
      Γ ⊢ₘ[T]
        (target ≠ₘ ∅ₘ) ⟶ₘ
          ((sequenceSpace ≐ₘ seq_spaceₘ(target)) ↔ₘ
            finite_sequence_space_spec
              target sequenceSpace) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <|
          stdseq_weaken_finite_sequence_space <|
            finite_sequence_space_definition_instance_derives
              target sequenceSpace hTarget hSequenceSpace
  have hSpec :
      Γ ⊢ₘ[T]
        finite_sequence_space_spec
          target sequenceSpace :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.impElim
        hContract hTargetNonempty)
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) sequenceSpace)
  have hAtSequence :=
    FirstOrder.Derives.forall_elim
      (term := sequence) hSpec
  have hTargetOpen (depth : Nat) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth sequence target hTarget.2
  have hSequenceSpaceOpen (depth : Nat) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth sequence sequenceSpace
      hSequenceSpace.2
  have hMemberIff :
      Γ ⊢ₘ[T]
        (sequence ∈ₘ sequenceSpace) ↔ₘ
          finite_sequence_member_condition
            target sequence := by
    simpa [finite_sequence_space_spec,
      finite_sequence_member_condition,
      Formula.openAt, Formula.next_depth,
      Term.openAt, hTargetOpen,
      hSequenceSpaceOpen] using hAtSequence
  exact FirstOrder.Derives.iffElimLeft
    hMemberIff hMemberCondition

/-- 非空目标集上的标准序列属于相应的有限序列空间。 -/
theorem standard_sequence_mem_sequence_space
    {elements : List SetTerm} (target : SetTerm) (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hElementsClosed : ∀ element, element ∈ elements →
      Term.freeSupport element = []) (hTarget : Term.Admissible target SetSort.set) (hTargetClosed : Term.freeSupport target = []) (hTargetNonempty :
      ⊢ₘ[standard_sequence_semantics_theory] target ≠ₘ ∅ₘ) (hTargetMember : ∀ element, element ∈ elements →
      ⊢ₘ[standard_sequence_semantics_theory] element ∈ₘ target) :
    ⊢ₘ[standard_sequence_semantics_theory]
      standard_sequence elements ∈ₘ seq_spaceₘ(target) :=
  standard_sequence_mem_sequence_space_of_theory (fun _ hFormula => hFormula) (fun _ hFormula =>
      standard_sequence_semantics_theory_sentence hFormula)
    target hElements hElementsClosed
    hTarget hTargetClosed hTargetNonempty hTargetMember
/--
在任意标准语义扩张理论中，非空列表生成的标准序列属于相应的非空有限序列空间。
逐项成员证书允许直接来自扩张理论 `T`，因此可用于把对象化的公式编码行装配为更强
内部理论中的有限证明序列，而无需把这些行证书降回基础标准语义理论。
-/
theorem standard_sequence_mem_nonempty_sequence_space_of_theory
    {T : SetTheory} (hTheory :
      ∀ formula,
        standard_sequence_semantics_theory formula →
          T formula) (hTheorySentence :
      ∀ formula, T formula → Formula.Sentence formula)
    {elements : List SetTerm} (target : SetTerm) (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hElementsClosed : ∀ element, element ∈ elements →
      Term.freeSupport element = []) (hTarget : Term.Admissible target SetSort.set) (hTargetClosed : Term.freeSupport target = []) (hTargetNonempty :
      ⊢ₘ[T] target ≠ₘ ∅ₘ) (hTargetMember : ∀ element, element ∈ elements →
      ⊢ₘ[T] element ∈ₘ target) (hElementsNonempty : elements ≠ []) :
    ⊢ₘ[T]
      standard_sequence elements ∈ₘ seq₊_spaceₘ(target) := by
  let sequence := standard_sequence elements
  let positiveSpace := seq₊_spaceₘ(target)
  have hSequence : Term.Admissible sequence SetSort.set :=
    seq_admissible_m 0 hElements
  have hPositiveSpace :
      Term.Admissible positiveSpace SetSort.set :=
    nonempty_finite_sequence_space_term_admissible target hTarget
  have hContract :
      ⊢ₘ[T]
        nonempty_finite_sequence_space_definition_instance
          target positiveSpace :=
    FirstOrder.Derives.theory_weaken hTheory <|
      stdseq_weaken_nonempty_sequence_space <|
        nonempty_finite_sequence_space_definition_instance_derives
          target positiveSpace hTarget hPositiveSpace
  have hSpec :
      ⊢ₘ[T]
        nonempty_finite_sequence_space_spec
          target positiveSpace := by
    have hIff := FirstOrder.Derives.impElim
      hContract hTargetNonempty
    exact FirstOrder.Derives.iffElimRight hIff (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) positiveSpace)
  have hAtSequence := FirstOrder.Derives.forall_elim
    (term := sequence) hSpec
  have hTargetOpen (depth : Nat) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth sequence target hTarget.2
  have hPositiveSpaceOpen (depth : Nat) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth sequence positiveSpace hPositiveSpace.2
  have hZeroOpen (depth : Nat) :
      Term.openAt SetSort.set depth sequence (numₘ(0)) =
        numₘ(0) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth sequence (numₘ(0)) (finite_numeral_term_admissible 0).2
  have hMemberIff :
      ⊢ₘ[T] (sequence ∈ₘ positiveSpace) ↔ₘ
          nonempty_finite_sequence_member_condition
            target sequence := by
    simpa [nonempty_finite_sequence_space_spec,
      nonempty_finite_sequence_member_condition,
      Formula.openAt, Formula.next_depth, Term.openAt,
      hTargetOpen, hPositiveSpaceOpen, hZeroOpen] using hAtSequence
  have hSequenceSpace :
      ⊢ₘ[T]
        sequence ∈ₘ seq_spaceₘ(target) := by
    simpa [sequence] using
      standard_sequence_mem_sequence_space_of_theory
        hTheory hTheorySentence
        target hElements hElementsClosed
        hTarget hTargetClosed hTargetNonempty hTargetMember
  have hLengthPositive : 0 < elements.length := by
    cases elements with
    | nil =>
        exact (hElementsNonempty rfl).elim
    | cons head tail =>
        simp
  have hDomainEquality :
      ⊢ₘ[T]
        domₘ(sequence) ≐ₘ numₘ(elements.length) :=
    FirstOrder.Derives.theory_weaken hTheory <|
      standard_sequence_domain_eq_numeral_length
        hElements
        (stdseq_element_fresh_of_support_nil
          hElementsClosed 0)
        (stdseq_element_fresh_of_support_nil
          hElementsClosed 1)
  have hDomain :
      Term.Admissible (domₘ(sequence)) SetSort.set :=
    domain_term_admissible sequence hSequence
  have hNumeral :
      Term.Admissible (numₘ(elements.length)) SetSort.set :=
    finite_numeral_term_admissible elements.length
  have hZeroDomain :
      ⊢ₘ[T]
        numₘ(0) ∈ₘ domₘ(sequence) := by
    have hTransport := membership_right_iff_of_equality (numₘ(0)) (domₘ(sequence)) (numₘ(elements.length)) (finite_numeral_term_admissible 0) hDomain hNumeral
      (by simpa [sequence] using hDomainEquality)
    exact FirstOrder.Derives.iffElimLeft hTransport (FirstOrder.Derives.theory_weaken hTheory (standard_sequence_finite_numeral_mem_of_lt
          0 elements.length hLengthPositive))
  exact FirstOrder.Derives.iffElimLeft hMemberIff (by
      simpa [nonempty_finite_sequence_member_condition,
        sequence, positiveSpace] using
        FirstOrder.Derives.conjIntro hSequenceSpace hZeroDomain)
/-- 非空列表生成的标准序列属于相应的非空有限序列空间。 -/
theorem standard_sequence_mem_nonempty_sequence_space
    {elements : List SetTerm} (target : SetTerm) (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hElementsClosed : ∀ element, element ∈ elements →
      Term.freeSupport element = []) (hTarget : Term.Admissible target SetSort.set) (hTargetClosed : Term.freeSupport target = []) (hTargetNonempty :
      ⊢ₘ[standard_sequence_semantics_theory] target ≠ₘ ∅ₘ) (hTargetMember : ∀ element, element ∈ elements →
      ⊢ₘ[standard_sequence_semantics_theory] element ∈ₘ target) (hElementsNonempty : elements ≠ []) :
    ⊢ₘ[standard_sequence_semantics_theory]
      standard_sequence elements ∈ₘ seq₊_spaceₘ(target) :=
  standard_sequence_mem_nonempty_sequence_space_of_theory (fun _ hFormula => hFormula) (fun _ hFormula =>
      standard_sequence_semantics_theory_sentence hFormula)
    target hElements hElementsClosed
    hTarget hTargetClosed hTargetNonempty hTargetMember
    hElementsNonempty
/-- `flattenₘ` 在有限序列族 guard 下满足其完整折叠规格。 -/
theorem finite_sequence_flatten_term_spec_derives (family : SetTerm) (hFamily : Term.Admissible family SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory]
      finite_sequence_family_condition family ⟶ₘ
        finite_sequence_flatten_spec family (flattenₘ(family)) := by
  have hFlatten :
      Term.Admissible (flattenₘ(family)) SetSort.set :=
    finite_sequence_flatten_term_admissible family hFamily
  have hContract := stdseq_weaken_finite_sequence_flatten (finite_sequence_flatten_definition_instance_derives
      family (flattenₘ(family)) hFamily hFlatten)
  let condition := finite_sequence_family_condition family
  let Γ : Context signature := [condition]
  nd_apply FirstOrder.Derives.impIntro
  have hCondition : Γ ⊢ₘ[standard_sequence_semantics_theory] condition :=
    .assumption (by simp [Γ])
  have hIff := FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hContract)
    hCondition
  exact FirstOrder.Derives.iffElimRight hIff
    (FirstOrder.Derives.eq_refl_m (sort := SetSort.set) (flattenₘ(family)))
/--
开放元素组成的标准序列在 `getElem?` 位置逐点求值。

三个 freshness 前提恰好对应标准有限函数图证明内部的关系编号与单值性编号；
不要求元素闭合，也不要求把局部上下文提升为理论公理。
-/
theorem standard_sequence_from_apply_getElem?_of_theory
    {T : SetTheory} {Γ : Context signature}
    (hTheory :
      ∀ formula,
        standard_sequence_semantics_theory formula →
          T formula)
    (start : Nat) {elements : List SetTerm}
    {index : Nat} {element : SetTerm}
    (hGet : elements[index]? = some element)
    (hElements :
      ∀ item, item ∈ elements →
        Term.Admissible item SetSort.set)
    (hElementsFreshZero :
      ∀ item, item ∈ elements →
        (SetSort.set, 0) ∉ Term.freeSupport item)
    (hElementsFreshOne :
      ∀ item, item ∈ elements →
        (SetSort.set, 1) ∉ Term.freeSupport item)
    (hElementsFreshTwo :
      ∀ item, item ∈ elements →
        (SetSort.set, 2) ∉ Term.freeSupport item)
    (hElement : Term.Admissible element SetSort.set) :
    Γ ⊢ₘ[T]
      (standard_sequence_from start elements ·ₘ
          numₘ(start + index)) ≐ₘ element := by
  let sequence := standard_sequence_from start elements
  let argument := numₘ(start + index)
  have hSequence : Term.Admissible sequence SetSort.set :=
    seq_admissible_m start hElements
  have hArgument : Term.Admissible argument SetSort.set :=
    finite_numeral_term_admissible (start + index)
  have hSequenceFreshZero : (SetSort.set, 0) ∉ Term.freeSupport sequence := by
    exact standard_sequence_from_fresh_at 0 start hElementsFreshZero
  have hArgumentFreshZero : (SetSort.set, 0) ∉ Term.freeSupport argument := by
    rw [finite_numeral_term_freeSupport (start + index)]
    intro hMember
    cases hMember
  have hGraph :
      Γ ⊢ₘ[T]
        ⟨argument, element⟩ₘ ∈ₘ sequence := by
    exact FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <| by
          simpa [sequence, argument] using
            (standard_sequence_from_getElem?_graph_mem
              start hGet hElements hElement)
  have hDomainImp :
      Γ ⊢ₘ[T]
        (∃ₘ[SetSort.set],
            ⟨argument, bₛ#0⟩ₘ ∈ₘ sequence) ⟶ₘ
          argument ∈ₘ domₘ(sequence) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <|
          stdseq_graph_exists_to_domain
            sequence argument hSequence hArgument
            hSequenceFreshZero hArgumentFreshZero <| by
              simpa [sequence] using
                standard_sequence_from_is_relation
                  start hElements hElementsFreshZero
  have hGraphExists :
      Γ ⊢ₘ[T]
        ∃ₘ[SetSort.set],
          ⟨argument, bₛ#0⟩ₘ ∈ₘ sequence := by
    have hArgumentOpen := Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element argument hArgument.2
    have hSequenceOpen := Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element sequence hSequence.2
    nd_apply FirstOrder.Derives.exists_intro (term := element)
      (body := ⟨argument, bₛ#0⟩ₘ ∈ₘ sequence)
    simpa [Formula.openAt, Term.openAt,
      hArgumentOpen, hSequenceOpen] using hGraph
  have hDomain :
      Γ ⊢ₘ[T] argument ∈ₘ domₘ(sequence) :=
    FirstOrder.Derives.impElim hDomainImp hGraphExists
  have hFunction :
      Γ ⊢ₘ[T] is_function_formula sequence :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <| by
          simpa [sequence] using
            standard_sequence_from_is_function
              start hElements
              hElementsFreshZero
              hElementsFreshOne
              hElementsFreshTwo
  have hApplication :
      Γ ⊢ₘ[T]
        (is_function_formula sequence ∧ₘ
            argument ∈ₘ domₘ(sequence)) ⟶ₘ
          (⟨argument, element⟩ₘ ∈ₘ sequence) ⟶ₘ
            (element ≐ₘ (sequence ·ₘ argument)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <|
          stdseq_weaken_function_application <|
            function_application_eq_of_graph
              sequence argument element
              hSequence hArgument hElement
  have hValueEq :
      Γ ⊢ₘ[T]
        element ≐ₘ (sequence ·ₘ argument) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim hApplication
        (FirstOrder.Derives.conjIntro hFunction hDomain))
      hGraph
  have hSymmetry := Metatheory.Derives.equality_symm hValueEq
  simpa [sequence, argument] using hSymmetry

/-- 闭元素版本由开放元素接口直接退化得到。 -/
theorem standard_sequence_from_apply_getElem? (start : Nat) {elements : List SetTerm}
    {index : Nat} {element : SetTerm} (hGet : elements[index]? = some element) (hElements : ∀ item, item ∈ elements →
      Term.Admissible item SetSort.set) (hElementsClosed : ∀ item, item ∈ elements →
      Term.freeSupport item = []) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] (standard_sequence_from start elements ·ₘ
          numₘ(start + index)) ≐ₘ element := by
  exact standard_sequence_from_apply_getElem?_of_theory
    (fun _ hFormula => hFormula)
    start hGet hElements
    (stdseq_element_fresh_of_support_nil
      hElementsClosed 0)
    (stdseq_element_fresh_of_support_nil
      hElementsClosed 1)
    (stdseq_element_fresh_of_support_nil
      hElementsClosed 2)
    hElement
/-! ## 标准序列族与有限折叠 guard -/
/-- 相等的对象项满足同一个有限序列条件。 -/
theorem finite_sequence_condition_iff_of_equality
    {T : SetTheory} {Γ : Context signature} (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hEquality :
      Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      finite_sequence_condition left ↔ₘ
        finite_sequence_condition right := by
  let parameter := FreshVariable.fresh_id SetSort.set
    [Formula.equal left left, Formula.equal right right]
  let body : SetFormula := finite_sequence_condition (x#parameter)
  have hCongruence := Metatheory.Derives.equality_iff_of_equality (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := parameter)
    (left := left) (right := right) (body := body)
    hEquality
  simpa [body, finite_sequence_condition,
    Formula.substituteFree, Term.substituteFree,
    set_variable, is_function_formula,
    domain_term] using hCongruence
/-- 元素避开三个内部编号时，标准序列本身是有限序列。 -/
theorem standard_sequence_finite_sequence_condition
    {elements : List SetTerm} (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set)
    (hElementsFreshZero : ∀ element, element ∈ elements →
      (SetSort.set, 0) ∉ Term.freeSupport element)
    (hElementsFreshOne : ∀ element, element ∈ elements →
      (SetSort.set, 1) ∉ Term.freeSupport element)
    (hElementsFreshTwo : ∀ element, element ∈ elements →
      (SetSort.set, 2) ∉ Term.freeSupport element) :
    ⊢ₘ[standard_sequence_semantics_theory]
      finite_sequence_condition (standard_sequence elements) := by
  let sequence := standard_sequence elements
  have hSequence : Term.Admissible sequence SetSort.set :=
    seq_admissible_m 0 hElements
  have hDomain : Term.Admissible (domₘ(sequence)) SetSort.set :=
    domain_term_admissible sequence hSequence
  have hNumeral : Term.Admissible (numₘ(elements.length)) SetSort.set :=
    finite_numeral_term_admissible elements.length
  have hFunction := standard_sequence_from_is_function
    0 hElements hElementsFreshZero
      hElementsFreshOne hElementsFreshTwo
  have hDomainEquality := standard_sequence_domain_eq_numeral_length
    hElements hElementsFreshZero hElementsFreshOne
  have hDomainMembershipIff := membership_left_iff_of_equality (domₘ(sequence)) (numₘ(elements.length)) ωₘ
    hDomain hNumeral omega_term_admissible (by simpa [sequence] using hDomainEquality)
  have hDomainOmega :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(sequence) ∈ₘ ωₘ :=
    FirstOrder.Derives.iffElimLeft hDomainMembershipIff (standard_sequence_finite_numeral_mem_omega elements.length)
  exact FirstOrder.Derives.conjIntro (by simpa [sequence] using hFunction) (by simpa [sequence] using hDomainOmega)

/--
开放元素组成的标准序列在任意标准序列语义扩张理论中满足完整 `flattenₘ`
族条件。

逐点有限性保留调用方上下文；元素只需避开标准函数图实现内部的三个编号。
这是一阶参数族反演所需的最弱通用接口，不要求元素闭合。
-/
theorem standard_sequence_family_condition_derives_of_theory_context
    {T : SetTheory} {Γ : Context signature}
    (hTheory :
      ∀ formula,
        standard_sequence_semantics_theory formula →
          T formula)
    (hTheorySentence :
      ∀ formula, T formula →
        Formula.Sentence formula)
    {elements : List SetTerm}
    (hElements :
      ∀ element, element ∈ elements →
        Term.Admissible element SetSort.set)
    (hElementsFreshZero :
      ∀ element, element ∈ elements →
        (SetSort.set, 0) ∉ Term.freeSupport element)
    (hElementsFreshOne :
      ∀ element, element ∈ elements →
        (SetSort.set, 1) ∉ Term.freeSupport element)
    (hElementsFreshTwo :
      ∀ element, element ∈ elements →
        (SetSort.set, 2) ∉ Term.freeSupport element)
    (hElementFinite :
      ∀ element, element ∈ elements →
        Γ ⊢ₘ[T] finite_sequence_condition element) :
    Γ ⊢ₘ[T]
      finite_sequence_family_condition
        (standard_sequence elements) := by
  let sequence : SetTerm := standard_sequence elements
  have hSequence : Term.Admissible sequence SetSort.set := by
    simpa [sequence] using
      seq_admissible_m 0 hElements
  have hSequenceFinite :
      Γ ⊢ₘ[T] finite_sequence_condition sequence :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <| by
          simpa [sequence] using
            standard_sequence_finite_sequence_condition
              hElements
              hElementsFreshZero
              hElementsFreshOne
              hElementsFreshTwo
  have hSequenceDomain :
      Γ ⊢ₘ[T]
        domₘ(sequence) ≐ₘ numₘ(elements.length) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <| by
          simpa [sequence] using
            standard_sequence_domain_eq_numeral_length
              hElements
              hElementsFreshZero
              hElementsFreshOne
  let freshnessBasis : List SetFormula :=
    (sequence ≐ₘ sequence) :: Γ
  let indexId : FreeVarId :=
    FreshVariable.fresh_id SetSort.set freshnessBasis
  let index : SetTerm := x#indexId
  let domainMembership : SetFormula :=
    index ∈ₘ domₘ(sequence)
  let finiteCondition : SetFormula :=
    domainMembership ⟶ₘ
      finite_sequence_condition (sequence ·ₘ index)
  have hIndex : Term.Admissible index SetSort.set := by
    simpa [index] using
      set_variable_admissible indexId
  have hIndexFreshSequence :
      (SetSort.set, indexId) ∉
        Term.freeSupport sequence := by
    dsimp [indexId, freshnessBasis]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m
        (sort := SetSort.set)
        (formulas := (sequence ≐ₘ sequence) :: Γ)
        (formula := sequence ≐ₘ sequence)
        (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hIndexFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, indexId) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    dsimp [indexId, freshnessBasis]
    exact
      FreshVariable.fresh_id_not_mem_m
        (sort := SetSort.set)
        (formulas := (sequence ≐ₘ sequence) :: Γ)
        (formula := formula)
        (by simp [hFormula])
  have hTheoryFresh :
      ∀ formula, T formula →
        (SetSort.set, indexId) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    rw [(hTheorySentence formula hFormula).2]
    exact List.not_mem_nil
  have hPoint :
      Γ ⊢ₘ[T] finiteCondition := by
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature :=
      domainMembership :: Γ
    have hDomainMembership :
        Δ ⊢ₘ[T] domainMembership :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    have hDomainEquality :
        Δ ⊢ₘ[T]
          domₘ(sequence) ≐ₘ
            numₘ(elements.length) :=
      FirstOrder.Derives.context_weaken_cons
        hSequenceDomain
    have hNumeralMembership :
        Δ ⊢ₘ[T]
          index ∈ₘ numₘ(elements.length) :=
      FirstOrder.Derives.iffElimRight
        (membership_right_iff_of_equality
          index (domₘ(sequence))
          (numₘ(elements.length))
          hIndex
          (domain_term_admissible sequence hSequence)
          (finite_numeral_term_admissible
            elements.length)
          hDomainEquality)
        hDomainMembership
    have hNumeralCases :
        Δ ⊢ₘ[T]
          stdseq_numeral_member_condition
            elements.length index :=
      FirstOrder.Derives.iffElimRight
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ]) <|
            FirstOrder.Derives.theory_weaken hTheory <|
              stdseq_numeral_member_iff
                elements.length index hIndex)
        hNumeralMembership
    have hCases :
        stdseq_numeral_member_condition
              elements.length index :: Δ
          ⊢ₘ[T]
            finite_sequence_condition
              (sequence ·ₘ index) := by
      apply
        stdseq_numeral_member_condition_elim_context
          elements.length index
          (finite_sequence_condition
            (sequence ·ₘ index))
      intro position hPosition
      let Ε : Context signature :=
        (index ≐ₘ numₘ(position)) :: Δ
      let element : SetTerm := elements[position]
      have hElementMember :
          element ∈ elements := by
        simp [element]
      have hElement :
          Term.Admissible element SetSort.set :=
        hElements element hElementMember
      have hGet :
          elements[position]? = some element :=
        List.getElem?_eq_some_iff.mpr
          ⟨hPosition, rfl⟩
      have hIndexEquality :
          Ε ⊢ₘ[T]
            index ≐ₘ numₘ(position) :=
        FirstOrder.Derives.assumption
          (by simp [Ε])
      have hArgumentEquality :
          Ε ⊢ₘ[T]
            (sequence ·ₘ index) ≐ₘ
              (sequence ·ₘ numₘ(position)) :=
        function_application_term_congr_argument_of_equality
          sequence index (numₘ(position))
          hSequence hIndex
          (finite_numeral_term_admissible position)
          hIndexEquality
      have hPointValue :
          Ε ⊢ₘ[T]
            (sequence ·ₘ numₘ(position)) ≐ₘ
              element := by
        simpa [sequence] using
          standard_sequence_from_apply_getElem?_of_theory
            (Γ := Ε) hTheory 0 hGet hElements
            hElementsFreshZero
            hElementsFreshOne
            hElementsFreshTwo
            hElement
      have hValueEquality :
          Ε ⊢ₘ[T]
            (sequence ·ₘ index) ≐ₘ element :=
        Metatheory.Derives.equality_trans
          hArgumentEquality hPointValue
      have hElementFiniteAt :
          Ε ⊢ₘ[T]
            finite_sequence_condition element :=
        FirstOrder.Derives.context_weaken
          (Γ := Γ) (Δ := Ε) (by
            intro formula hFormula
            simp [Ε, Δ, hFormula])
          (hElementFinite element hElementMember)
      exact
        FirstOrder.Derives.iffElimLeft
          (finite_sequence_condition_iff_of_equality
            (sequence ·ₘ index) element
            (function_application_term_admissible
              sequence index hSequence hIndex)
            hElement hValueEquality)
          hElementFiniteAt
    exact FirstOrder.Derives.cut
      hNumeralCases hCases
  have hAllFiniteAtIndex :
      Γ ⊢ₘ[T]
        ∀ₘ[SetSort.set, indexId], finiteCondition :=
    FirstOrder.Derives.forall_intro
      (T := T) (Γ := Γ)
      (sort := SetSort.set) (eigen := indexId)
      hTheoryFresh hIndexFreshContext hPoint
  have hSequenceCloseIndex :
      Term.closeFreeAt SetSort.set indexId 0 sequence =
        sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 sequence
      hSequence.2 hIndexFreshSequence
  have hAllFinite :
      Γ ⊢ₘ[T]
        ∀ₘ[SetSort.set],
          (bₛ#0 ∈ₘ domₘ(sequence)) ⟶ₘ
            finite_sequence_condition
              (sequence ·ₘ bₛ#0) := by
    simpa [finiteCondition, domainMembership, index,
      finite_sequence_condition,
      Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt, set_variable,
      domain_term, function_application_term,
      is_function_formula,
      hSequenceCloseIndex] using
        hAllFiniteAtIndex
  exact FirstOrder.Derives.conjIntro
    hSequenceFinite <| by
      simpa [sequence,
        finite_sequence_family_condition] using
        hAllFinite

/--
若标准序列的每个元素本身都是有限序列，则该标准序列满足 `flattenₘ` 的完整族 guard。
-/
theorem standard_sequence_family_condition_derives
    {elements : List SetTerm} (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hElementsClosed : ∀ element, element ∈ elements →
      Term.freeSupport element = []) (hElementFinite : ∀ element, element ∈ elements →
      ⊢ₘ[standard_sequence_semantics_theory]
        finite_sequence_condition element) :
    ⊢ₘ[standard_sequence_semantics_theory]
      finite_sequence_family_condition (standard_sequence elements) := by
  exact
    standard_sequence_family_condition_derives_of_theory_context
      (fun _ hFormula => hFormula)
      (fun _ hFormula =>
        standard_sequence_semantics_theory_sentence hFormula)
      hElements
      (stdseq_element_fresh_of_support_nil
        hElementsClosed 0)
      (stdseq_element_fresh_of_support_nil
        hElementsClosed 1)
      (stdseq_element_fresh_of_support_nil
        hElementsClosed 2)
      hElementFinite
/--
函数、标准长度定义域和各标准位置上的逐点值唯一决定任意闭项标准序列。
这是标准序列外延性的通用入口。调用方只需给出元素项的 admissibility、闭性以及
源函数在每个外部列表位置上的值；有限定义域消去、开放参数全称化与函数外延性均
在本定理内部完成。token 序列和二维证明序列都应复用这一接口。
-/
theorem standard_sequence_eq_of_function_domain_pointwise
    {T : SetTheory} {Γ : Context signature} (hTheory :
      ∀ formula,
        standard_sequence_semantics_theory formula → T formula) (hTheorySentence :
      ∀ formula, T formula → Formula.Sentence formula) (source : SetTerm) (elements : List SetTerm) (hSource : Term.Admissible source SetSort.set) (hElements :
      ∀ element, element ∈ elements →
        Term.Admissible element SetSort.set) (hElementsClosed :
      ∀ element, element ∈ elements →
        Term.freeSupport element = []) (hFunction :
      Γ ⊢ₘ[T] is_function_formula source) (hDomain :
      Γ ⊢ₘ[T]
        domₘ(source) ≐ₘ numₘ(elements.length)) (hPoint :
      ∀ {index : Nat} {element : SetTerm},
        elements[index]? = some element →
          Γ ⊢ₘ[T] (source ·ₘ numₘ(index)) ≐ₘ element) :
    Γ ⊢ₘ[T]
      source ≐ₘ standard_sequence elements := by
  let standard : SetTerm := standard_sequence elements
  let pointBody : SetFormula := (bₛ#0 ∈ₘ domₘ(source)) ⟶ₘ ((source ·ₘ bₛ#0) ≐ₘ (standard ·ₘ bₛ#0))
  let freshnessBasis : List SetFormula :=
    [source ≐ₘ source, standard ≐ₘ standard, pointBody] ++ Γ
  let argumentId : FreeVarId :=
    FreshVariable.fresh_id SetSort.set freshnessBasis
  let argument : SetTerm := x#argumentId
  have hStandard :
      Term.Admissible standard SetSort.set := by
    simpa [standard] using
      seq_admissible_m 0 hElements
  have hArgument :
      Term.Admissible argument SetSort.set := by
    simpa [argument] using
      set_variable_admissible argumentId
  have hArgumentFreshSource : (SetSort.set, argumentId) ∉
        Term.freeSupport source := by
    dsimp [argumentId, freshnessBasis]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
          [source ≐ₘ source,
            standard ≐ₘ standard, pointBody] ++ Γ) (formula := source ≐ₘ source) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hArgumentFreshStandard : (SetSort.set, argumentId) ∉
        Term.freeSupport standard := by
    rw [show Term.freeSupport standard = [] by
      simpa [standard] using
        seq_support_nil_m
          0 hElementsClosed]
    exact List.not_mem_nil
  have hArgumentFreshPointBody : (SetSort.set, argumentId) ∉
        Formula.freeSupport pointBody := by
    dsimp [argumentId, freshnessBasis]
    exact FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
        [source ≐ₘ source,
          standard ≐ₘ standard, pointBody] ++ Γ) (formula := pointBody) (by simp)
  have hArgumentFreshContext :
      ∀ formula, formula ∈ Γ → (SetSort.set, argumentId) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    dsimp [argumentId, freshnessBasis]
    exact FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
        [source ≐ₘ source,
          standard ≐ₘ standard, pointBody] ++ Γ) (formula := formula) (by simp [hFormula])
  have hStandardFunction :
      Γ ⊢ₘ[T] is_function_formula standard := by
    exact FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <| by
          simpa [standard] using
            standard_sequence_from_is_function
              0 hElements
              (stdseq_element_fresh_of_support_nil
                hElementsClosed 0)
              (stdseq_element_fresh_of_support_nil
                hElementsClosed 1)
              (stdseq_element_fresh_of_support_nil
                hElementsClosed 2)
  have hStandardDomain :
      Γ ⊢ₘ[T]
        domₘ(standard) ≐ₘ numₘ(elements.length) := by
    exact FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <| by
          simpa [standard] using
            standard_sequence_domain_eq_numeral_length
              hElements
              (stdseq_element_fresh_of_support_nil
                hElementsClosed 0)
              (stdseq_element_fresh_of_support_nil
                hElementsClosed 1)
  have hNumeralStandard :
      Γ ⊢ₘ[T]
        numₘ(elements.length) ≐ₘ domₘ(standard) :=
    Metatheory.Derives.equality_symm hStandardDomain
  have hDomainAgreement :
      Γ ⊢ₘ[T]
        domₘ(source) ≐ₘ domₘ(standard) :=
    Metatheory.Derives.equality_trans hDomain hNumeralStandard
  have hPointOpened :
      Γ ⊢ₘ[T] (argument ∈ₘ domₘ(source)) ⟶ₘ ((source ·ₘ argument) ≐ₘ (standard ·ₘ argument)) := by
    have hArgumentDomain :
        Formula.Admissible (argument ∈ₘ domₘ(source)) :=
      membership_formula_admissible hArgument (domain_term_admissible source hSource)
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature := (argument ∈ₘ domₘ(source)) :: Γ
    have hArgumentDomainProof :
        Δ ⊢ₘ[T] argument ∈ₘ domₘ(source) :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hDomain' :
        Δ ⊢ₘ[T]
          domₘ(source) ≐ₘ numₘ(elements.length) :=
      FirstOrder.Derives.context_weaken_cons hDomain
    have hArgumentNumeral :
        Δ ⊢ₘ[T] argument ∈ₘ numₘ(elements.length) :=
      FirstOrder.Derives.iffElimRight (membership_right_iff_of_equality
          argument (domₘ(source)) (numₘ(elements.length))
          hArgument (domain_term_admissible source hSource) (finite_numeral_term_admissible elements.length)
          hDomain')
        hArgumentDomainProof
    have hMemberIff :=
      FirstOrder.Derives.theory_weaken hTheory <|
        stdseq_numeral_member_iff
          elements.length argument hArgument
    have hCondition :
        Δ ⊢ₘ[T]
          stdseq_numeral_member_condition
            elements.length argument :=
      FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp [Δ])
          hMemberIff)
        hArgumentNumeral
    have hApplicationSource :
        Term.Admissible (source ·ₘ argument) SetSort.set :=
      function_application_term_admissible
        source argument hSource hArgument
    have hApplicationStandard :
        Term.Admissible (standard ·ₘ argument) SetSort.set :=
      function_application_term_admissible
        standard argument hStandard hArgument
    have hCases :
        stdseq_numeral_member_condition
            elements.length argument :: Δ ⊢ₘ[T] (source ·ₘ argument) ≐ₘ (standard ·ₘ argument) := by
      nd_apply stdseq_numeral_member_condition_elim_context
        elements.length argument ((source ·ₘ argument) ≐ₘ (standard ·ₘ argument))
      intro index hIndex
      let Ε : Context signature := (argument ≐ₘ numₘ(index)) :: Δ
      have hArgumentNumeralEquality :
          Ε ⊢ₘ[T] argument ≐ₘ numₘ(index) :=
        FirstOrder.Derives.assumption (by simp [Ε])
      let element : SetTerm := elements[index]
      have hElementMem : element ∈ elements := by
        simp [element]
      have hElement :
          Term.Admissible element SetSort.set :=
        hElements element hElementMem
      have hGet :
          elements[index]? = some element :=
        List.getElem?_eq_some_iff.mpr
          ⟨hIndex, rfl⟩
      have hSourceAtNumeral :
          Ε ⊢ₘ[T] (source ·ₘ numₘ(index)) ≐ₘ element :=
        FirstOrder.Derives.context_weaken (Γ := Γ) (Δ := Ε) (by
            intro formula hFormula
            simp [Ε, Δ, hFormula]) (hPoint hGet)
      have hStandardAtNumeral :
          Ε ⊢ₘ[T] (standard ·ₘ numₘ(index)) ≐ₘ element :=
        FirstOrder.Derives.context_weaken (Γ := []) (Δ := Ε) (by simp [Ε, Δ]) <|
            FirstOrder.Derives.theory_weaken hTheory <| by
              simpa [standard] using
                standard_sequence_from_apply_getElem?
                  0 hGet hElements hElementsClosed hElement
      have hSourceArgument :
          Ε ⊢ₘ[T] (source ·ₘ argument) ≐ₘ (source ·ₘ numₘ(index)) :=
        function_application_term_congr_argument_of_equality
          source argument (numₘ(index))
          hSource hArgument (finite_numeral_term_admissible index)
          hArgumentNumeralEquality
      have hStandardArgument :
          Ε ⊢ₘ[T] (standard ·ₘ argument) ≐ₘ (standard ·ₘ numₘ(index)) :=
        function_application_term_congr_argument_of_equality
          standard argument (numₘ(index))
          hStandard hArgument (finite_numeral_term_admissible index)
          hArgumentNumeralEquality
      have hSourceValue :
          Ε ⊢ₘ[T] (source ·ₘ argument) ≐ₘ element :=
        Metatheory.Derives.equality_trans
          hSourceArgument hSourceAtNumeral
      have hStandardValue :
          Ε ⊢ₘ[T] (standard ·ₘ argument) ≐ₘ element :=
        Metatheory.Derives.equality_trans
          hStandardArgument hStandardAtNumeral
      have hStandardValueSymm :
          Ε ⊢ₘ[T]
            element ≐ₘ (standard ·ₘ argument) :=
        Metatheory.Derives.equality_symm hStandardValue
      exact Metatheory.Derives.equality_trans
        hSourceValue hStandardValueSymm
    exact FirstOrder.Derives.cut hCondition hCases
  have hSourceOpen :
      Term.openAt SetSort.set 0 argument source = source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 argument source hSource.2
  have hStandardOpen :
      Term.openAt SetSort.set 0 argument standard = standard :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 argument standard hStandard.2
  have hPointOpenedAsBody :
      Γ ⊢ₘ[T]
        Formula.openAt SetSort.set 0 argument pointBody := by
    simpa [pointBody, Formula.openAt,
      Formula.next_depth, Term.openAt,
      hSourceOpen, hStandardOpen] using hPointOpened
  have hTheoryFresh :
      ∀ formula, T formula → (SetSort.set, argumentId) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    rw [(hTheorySentence formula hFormula).2]
    exact List.not_mem_nil
  have hPointwise :
      Γ ⊢ₘ[T] ∀ₘ[SetSort.set], pointBody := by
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := argumentId) (body :=
          Formula.openAt SetSort.set 0 argument pointBody)
        hTheoryFresh hArgumentFreshContext
        hPointOpenedAsBody
    simpa [argument,
      Formula.closeFreeAt_openAt
        SetSort.set argumentId 0 pointBody
        hArgumentFreshPointBody] using hGeneralized
  have hAgreement :
      Γ ⊢ₘ[T]
        function_extensional_agreement
          source standard := by
    simpa [function_extensional_agreement,
      pointBody] using
      FirstOrder.Derives.conjIntro
        hDomainAgreement hPointwise
  have hExtensionality :=
    FirstOrder.Derives.theory_weaken hTheory <|
      standard_sequence_weaken_function_application <|
        functions_equal_of_extensional_agreement
          source standard hSource hStandard
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp)
        hExtensionality) (FirstOrder.Derives.conjIntro
        hFunction hStandardFunction))
    hAgreement
end YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation
