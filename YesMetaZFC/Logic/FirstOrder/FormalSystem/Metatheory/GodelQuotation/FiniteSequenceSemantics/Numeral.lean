import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.Core
/-!
# 标准有限序列的 numeral 与单值性语义
本模块承接值域投影、有限 numeral 归纳、定义域刻画与标准序列单值性。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false
/-- 标准有限序列项的检查证书由各元素证书递归组合。 -/
@[term_check]
theorem standard_sequence_from_check
    (start : Nat) {elements : List SetTerm}
    (hElements : ∀ element, element ∈ elements →
      Term.CheckCertificate element SetSort.set) :
    Term.CheckCertificate
      (standard_sequence_from start elements) SetSort.set :=
  Term.check_admissible_complete
    (seq_admissible_m start fun element hElement =>
      (hElements element hElement).admissible)
/-- 值域坐标条件可恢复为一个规范的图成员见证。 -/
private theorem stdseq_range_coordinate_to_graph_exists (relation value : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hValue : Term.Admissible value SetSort.set) (hRelationFresh : (SetSort.set, 0) ∉ Term.freeSupport relation)
    (hValueFresh : (SetSort.set, 0) ∉ Term.freeSupport value) (hIsRelation :
      ⊢ₘ[standard_sequence_semantics_theory] is_relation_formula relation) :
    ⊢ₘ[standard_sequence_semantics_theory]
      relation_range_member_condition relation value ⟶ₘ (∃ₘ[SetSort.set], ⟨bₛ#0, value⟩ₘ ∈ₘ relation) := by
  let pair := x#0
  let membership : SetFormula := pair ∈ₘ relation
  let coordinateEquality : SetFormula := value ≐ₘ (pair)₁ₘ
  let pairCondition : SetFormula := membership ∧ₘ coordinateEquality
  let conclusion : SetFormula :=
    ∃ₘ[SetSort.set], ⟨bₛ#0, value⟩ₘ ∈ₘ relation
  have hPair : Term.Admissible pair SetSort.set :=
    set_variable_admissible 0
  have hPairLeft : Term.Admissible (pair)₀ₘ SetSort.set :=
    left_projection_term_admissible pair hPair
  have hPairRight : Term.Admissible (pair)₁ₘ SetSort.set :=
    right_projection_term_admissible pair hPair
  have hProjectionPair :
      Term.Admissible (⟨(pair)₀ₘ, (pair)₁ₘ⟩ₘ) SetSort.set :=
    ordered_pair_term_admissible (pair)₀ₘ (pair)₁ₘ
      hPairLeft hPairRight
  have hCanonicalPair :
      Term.Admissible (⟨(pair)₀ₘ, value⟩ₘ) SetSort.set :=
    ordered_pair_term_admissible (pair)₀ₘ value hPairLeft hValue
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
          (pair)₀ₘ value (pair)₀ₘ (pair)₁ₘ
          hPairLeft hValue hPairLeft hPairRight))
    have hLeftReflexive :
        Γ ⊢ₘ[standard_sequence_semantics_theory] (pair)₀ₘ ≐ₘ (pair)₀ₘ :=
      FirstOrder.Derives.eq_refl_m (sort := SetSort.set) ((pair)₀ₘ)
    have hCanonicalToProjection :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          ⟨(pair)₀ₘ, value⟩ₘ ≐ₘ
            ⟨(pair)₀ₘ, (pair)₁ₘ⟩ₘ :=
      FirstOrder.Derives.iffElimLeft hCoordinates (FirstOrder.Derives.conjIntro hLeftReflexive (by simpa [Γ, coordinateEquality] using hCoordinate))
    have hCanonicalToPair :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          ⟨(pair)₀ₘ, value⟩ₘ ≐ₘ pair :=
      Metatheory.Derives.equality_trans
        hCanonicalToProjection hProjectionToPair
    have hTransport := membership_left_iff_of_equality (⟨(pair)₀ₘ, value⟩ₘ) pair relation
      hCanonicalPair hPair hRelation hCanonicalToPair
    have hCanonicalMembership :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          ⟨(pair)₀ₘ, value⟩ₘ ∈ₘ relation :=
      FirstOrder.Derives.iffElimLeft hTransport (by simpa [Γ, membership] using hMembership)
    nd_apply FirstOrder.Derives.exists_intro
      (term := (pair)₀ₘ)
      (body := ⟨bₛ#0, value⟩ₘ ∈ₘ relation)
    have hValueOpen := Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (pair)₀ₘ value hValue.2
    have hRelationOpen := Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (pair)₀ₘ relation hRelation.2
    simpa [Formula.openAt, Term.openAt,
      hValueOpen, hRelationOpen] using hCanonicalMembership
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
    have hBaseFresh := relation_formula_fresh (⟨bₛ#0, value⟩ₘ) relation (ordered_pair_term_fresh (bₛ#0) value hBvarFresh hValueFresh)
      hRelationFresh
    simpa [conclusion, Formula.freeSupport] using hBaseFresh
  have hLift := Metatheory.Derives.exists_imp_of_imp (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := 0)
    hTheoryFresh (by intro formula hFormula; simp at hFormula)
    hConclusionFresh hPairCase
  have hRelationClose :
      Term.closeFreeAt SetSort.set 0 0 relation = relation :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 0 0 relation hRelation.2 hRelationFresh
  have hValueClose :
      Term.closeFreeAt SetSort.set 0 0 value = value :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 0 0 value hValue.2 hValueFresh
  simpa [pair, pairCondition, membership, coordinateEquality, conclusion,
    relation_range_member_condition,
    relation_coordinate_member_condition,
    relation_coordinate_projection_term,
    Formula.closeFreeAt, Term.closeFreeAt,
    hRelationClose, hValueClose] using hLift
/-- 值域成员可展开为具有该右坐标的图成员见证。 -/
private theorem stdseq_range_to_graph_exists (relation value : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hValue : Term.Admissible value SetSort.set) (hRelationFresh : (SetSort.set, 0) ∉ Term.freeSupport relation)
    (hValueFresh : (SetSort.set, 0) ∉ Term.freeSupport value) (hIsRelation :
      ⊢ₘ[standard_sequence_semantics_theory] is_relation_formula relation) :
    ⊢ₘ[standard_sequence_semantics_theory] (value ∈ₘ ranₘ(relation)) ⟶ₘ (∃ₘ[SetSort.set], ⟨bₛ#0, value⟩ₘ ∈ₘ relation) := by
  have hRangeIffRaw := stdseq_weaken_relation_range (is_relation_range_member_iff relation value hRelation hValue)
  have hRangeIff := FirstOrder.Derives.impElim hRangeIffRaw hIsRelation
  have hCoordinateToGraph := stdseq_range_coordinate_to_graph_exists
    relation value hRelation hValue hRelationFresh hValueFresh hIsRelation
  nd_apply FirstOrder.Derives.impIntro
  let membership : SetFormula := value ∈ₘ ranₘ(relation)
  let Γ : Context signature := [membership]
  have hIff := FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hRangeIff
  have hCondition := FirstOrder.Derives.iffElimRight hIff (by
      simpa [Γ, membership] using
        (FirstOrder.Derives.assumption
          (T := standard_sequence_semantics_theory)
          (Γ := Γ) (φ := membership) (by simp [Γ])))
  have hCoordinate := FirstOrder.Derives.conjElimRight hCondition
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hCoordinateToGraph)
    hCoordinate
/--
有限 numeral 成员关系的显式析取规格。
`stdseq_numeral_member_condition (n + 1) index` 从最大候选 `n` 向零展开，
供任何需要把对象域成员还原成有限外部情形分析的编码证明复用。
-/
def stdseq_numeral_member_condition : Nat → SetTerm → SetFormula
  | 0, _ => Formula.falsum
  | number + 1, index =>
      (index ≐ₘ numₘ(number)) ∨ₘ
        stdseq_numeral_member_condition number index
/-- 有限 numeral 成员条件按 numeral 递归保持 admissibility。 -/
theorem stdseq_numeral_member_condition_admissible (number : Nat) (index : SetTerm) (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible (stdseq_numeral_member_condition number index) := by
  induction number with
  | zero =>
      exact Formula.Admissible.falsum
  | succ number ih =>
      exact Formula.Admissible.disj (Formula.Admissible.equal
          hIndex (finite_numeral_term_admissible number))
        ih
/-- numeral 成员条件的检查证书由指标项证书递归组合。 -/
@[formula_check]
theorem stdseq_numeral_member_condition_check
    (number : Nat) (index : SetTerm)
    (hIndex : Term.CheckCertificate index SetSort.set) :
    Formula.CheckCertificate
      (stdseq_numeral_member_condition number index) :=
  Formula.check_admissible_complete
    (stdseq_numeral_member_condition_admissible
      number index hIndex.admissible)
private theorem stdseq_iff_symm
    {left right : SetFormula} (hIff : ⊢ₘ[standard_sequence_semantics_theory] left ↔ₘ right) :
    ⊢ₘ[standard_sequence_semantics_theory] right ↔ₘ left := by
  exact FirstOrder.Derives.iffIntro
    (FirstOrder.Derives.iffElimLeft
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := [right]) (by simp) hIff)
      (.assumption (by simp)))
    (FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := [left]) (by simp) hIff)
      (.assumption (by simp)))
/-- 对象项属于标准 numeral 当且仅当满足其有限析取规格。 -/
theorem stdseq_numeral_member_iff (number : Nat) (index : SetTerm) (hIndex : Term.Admissible index SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] (index ∈ₘ numₘ(number)) ↔ₘ
        stdseq_numeral_member_condition number index := by
  induction number with
  | zero =>
      have hEmpty := stdseq_empty index hIndex
      apply FirstOrder.Derives.iffIntro
      · exact FirstOrder.Derives.negElim (FirstOrder.Derives.assumption (T := standard_sequence_semantics_theory) (Γ := [index ∈ₘ numₘ(0)])
            (φ := index ∈ₘ numₘ(0)) (by simp)) (FirstOrder.Derives.context_weaken (Γ := []) (Δ := [index ∈ₘ numₘ(0)]) (by simp)
            (by simpa [finite_numeral_term] using hEmpty))
      · exact FirstOrder.Derives.falsumElim (by
            simpa [stdseq_numeral_member_condition] using (FirstOrder.Derives.assumption (T := standard_sequence_semantics_theory)
                (Γ := [stdseq_numeral_member_condition 0 index]) (φ := stdseq_numeral_member_condition 0 index) (by simp)))
  | succ number ih =>
      have hSuccessor := stdseq_weaken_successor (successor_term_membership_iff (numₘ(number)) index (finite_numeral_term_admissible number) hIndex)
      have hLeftRefl :
          ⊢ₘ[standard_sequence_semantics_theory] (index ≐ₘ numₘ(number)) ↔ₘ (index ≐ₘ numₘ(number)) :=
        Metatheory.Derives.iff_refl_m (Formula.Admissible.equal hIndex (finite_numeral_term_admissible number))
      have hCondition := stdseq_disj_congr hLeftRefl ih
      have hStep := FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (Metatheory.Derives.iff_trans_m (T := standard_sequence_semantics_theory) (Γ := [])
            (ψ := index ∈ₘ Sₘ(numₘ(number))) (φ := (index ≐ₘ numₘ(number)) ∨ₘ (index ∈ₘ numₘ(number))) (θ := (index ≐ₘ numₘ(number)) ∨ₘ
              stdseq_numeral_member_condition number index) (Formula.Admissible.iff_right hSuccessor.admissible)
            (Formula.Admissible.iff_left hSuccessor.admissible) (Formula.Admissible.iff_right hCondition.admissible))
          hSuccessor)
        hCondition
      simpa [finite_numeral_term, stdseq_numeral_member_condition,
        successor_member_condition] using hStep
/--
有限 numeral 成员条件的通用消去规则。
调用方只需分别处理每个具体 numeral 分支；本定理统一完成有限析取的机械拆分。
-/
theorem stdseq_numeral_member_condition_elim_of_theory
    {T : SetTheory} (number : Nat) (point : SetTerm)
    (conclusion : SetFormula)
    (hBranch : ∀ index, index < number →
      ⊢ₘ[T] (point ≐ₘ numₘ(index)) ⟶ₘ conclusion)
    (hPointCheck : Term.CheckCertificate point SetSort.set := by
      prove_term_check)
    (hConclusionCheck : Formula.CheckCertificate conclusion := by
      prove_nd_formula_check) :
    ⊢ₘ[T]
      stdseq_numeral_member_condition number point ⟶ₘ conclusion := by
  induction number with
  | zero =>
      nd_apply FirstOrder.Derives.impIntro
      exact FirstOrder.Derives.falsumElim <| by
        simpa [stdseq_numeral_member_condition] using (FirstOrder.Derives.assumption (T := T) (Γ := [stdseq_numeral_member_condition 0 point])
            (φ := stdseq_numeral_member_condition 0 point) (by simp))
  | succ number ih =>
      let equality : SetFormula := point ≐ₘ numₘ(number)
      let tailCondition : SetFormula :=
        stdseq_numeral_member_condition number point
      let condition : SetFormula := equality ∨ₘ tailCondition
      let Γ : Context signature := [condition]
      have hHead := hBranch number (Nat.lt_succ_self number)
      have hTail := ih (fun index hIndex =>
        hBranch index (Nat.lt_trans hIndex (Nat.lt_succ_self number)))
      nd_apply FirstOrder.Derives.impIntro
      have hCases :
          Γ ⊢ₘ[T]
            equality ∨ₘ tailCondition := by
        simpa [Γ, condition] using
          (FirstOrder.Derives.assumption
            (T := T) (Γ := Γ) (φ := condition) (by simp [Γ]))
      have hStep :
          Γ ⊢ₘ[T] conclusion := by
        apply FirstOrder.Derives.disjElim hCases
        · exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := equality :: Γ) (by simp) (by simpa [equality] using hHead)) (by
              simpa [equality] using
                (FirstOrder.Derives.assumption
                  (T := T) (Γ := equality :: Γ)
                  (φ := equality) (by simp)))
        · exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := tailCondition :: Γ) (by simp)
              (by simpa [tailCondition] using hTail)) (by
              simpa [tailCondition] using
                (FirstOrder.Derives.assumption
                  (T := T) (Γ := tailCondition :: Γ)
                  (φ := tailCondition) (by simp)))
      simpa [Γ, condition, equality, tailCondition,
        stdseq_numeral_member_condition] using hStep
/--
有限 numeral 成员条件在任意 Hilbert 上下文中的消去规则。
与闭上下文版本相比，该接口保留调用方已有的局部假设；每个具体 numeral 分支只需
在相应等式加入上下文后给出结论。有限序列反演、逐点函数比较等证明因此无需把
局部假设重新编码为临时理论。
-/
theorem stdseq_numeral_member_condition_elim_context
    {T : SetTheory} {Γ : Context signature}
    (number : Nat) (point : SetTerm) (conclusion : SetFormula)
    (hBranch : ∀ index, index < number →
      (point ≐ₘ numₘ(index)) :: Γ ⊢ₘ[T] conclusion)
    (hPointCheck : Term.CheckCertificate point SetSort.set := by
      prove_term_check)
    (hConclusionCheck : Formula.CheckCertificate conclusion := by
      prove_nd_formula_check) :
    stdseq_numeral_member_condition number point :: Γ ⊢ₘ[T]
      conclusion := by
  induction number with
  | zero =>
      exact FirstOrder.Derives.falsumElim <| by
        simpa [stdseq_numeral_member_condition] using (FirstOrder.Derives.assumption (T := T) (Γ :=
              stdseq_numeral_member_condition 0 point :: Γ)
              (φ := stdseq_numeral_member_condition 0 point) (by simp))
  | succ number ih =>
      let equality : SetFormula := point ≐ₘ numₘ(number)
      let tailCondition : SetFormula :=
        stdseq_numeral_member_condition number point
      let condition : SetFormula := equality ∨ₘ tailCondition
      let Δ : Context signature := condition :: Γ
      have hCases :
          Δ ⊢ₘ[T] equality ∨ₘ tailCondition := by
        simpa [Δ, condition] using
          (FirstOrder.Derives.assumption
            (T := T) (Γ := Δ) (φ := condition) (by simp [Δ]))
      apply FirstOrder.Derives.disjElim hCases
      · exact FirstOrder.Derives.context_weaken (Γ := equality :: Γ) (Δ := equality :: Δ) (by
            intro formula hFormula
            rcases List.mem_cons.mp hFormula with rfl | hFormula
            · simp [Δ]
            · simp [Δ, hFormula]) (hBranch number (Nat.lt_succ_self number))
      · have hTailResult :
            tailCondition :: Γ ⊢ₘ[T] conclusion := by
          simpa [tailCondition] using
            ih (fun index hIndex =>
              hBranch index (Nat.lt_trans hIndex (Nat.lt_succ_self number)))
        exact FirstOrder.Derives.context_weaken (Γ := tailCondition :: Γ) (Δ := tailCondition :: Δ) (by
            intro formula hFormula
            rcases List.mem_cons.mp hFormula with rfl | hFormula
            · simp [Δ]
            · simp [Δ, hFormula])
          hTailResult
/--
两个有限 numeral 成员条件的二维通用消去规则。
该定理把嵌套的有限析取机械装配集中在标准序列语义层。调用方只需处理每一对
标准 numeral 坐标；证明码的 Gödel 配对反演、有限函数图比较等后续模块无需重复
书写两层析取消去。
-/
theorem stdseq_numeral_member_condition_elim_two_of_theory
    {T : SetTheory} (leftBound rightBound : Nat)
    (left right : SetTerm) (conclusion : SetFormula)
    (hBranch :
      ∀ leftIndex, leftIndex < leftBound →
        ∀ rightIndex, rightIndex < rightBound →
          ⊢ₘ[T] (left ≐ₘ numₘ(leftIndex)) ⟶ₘ ((right ≐ₘ numₘ(rightIndex)) ⟶ₘ
                conclusion))
    (hLeftCheck : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRightCheck : Term.CheckCertificate right SetSort.set := by
      prove_term_check)
    (hConclusionCheck : Formula.CheckCertificate conclusion := by
      prove_nd_formula_check) :
    ⊢ₘ[T]
      stdseq_numeral_member_condition leftBound left ⟶ₘ (stdseq_numeral_member_condition rightBound right ⟶ₘ
          conclusion) := by
  let rightCondition : SetFormula :=
    stdseq_numeral_member_condition rightBound right
  have hRightCondition :
      Formula.Admissible rightCondition := by
    simpa [rightCondition] using
      stdseq_numeral_member_condition_admissible
        rightBound right hRightCheck.admissible
  have hLeftBranches :
      ∀ leftIndex, leftIndex < leftBound →
        ⊢ₘ[T] (left ≐ₘ numₘ(leftIndex)) ⟶ₘ (rightCondition ⟶ₘ conclusion) := by
    intro leftIndex hLeftIndex
    have hRightBranches :
        ∀ rightIndex, rightIndex < rightBound →
          ⊢ₘ[T] (right ≐ₘ numₘ(rightIndex)) ⟶ₘ ((left ≐ₘ numₘ(leftIndex)) ⟶ₘ
                conclusion) := by
      intro rightIndex hRightIndex
      have hCurrent :=
        hBranch leftIndex hLeftIndex
          rightIndex hRightIndex
      exact FirstOrder.Derives.impElim (Metatheory.Derives.imp_exchange
          (Formula.Admissible.equal hRightCheck.admissible
            (finite_numeral_term_admissible rightIndex))
          (Formula.Admissible.equal hLeftCheck.admissible
            (finite_numeral_term_admissible leftIndex))
          hConclusionCheck.admissible)
        hCurrent
    have hRightCases :
        ⊢ₘ[T]
          rightCondition ⟶ₘ ((left ≐ₘ numₘ(leftIndex)) ⟶ₘ
              conclusion) := by
      simpa [rightCondition] using
        stdseq_numeral_member_condition_elim_of_theory
          rightBound right ((left ≐ₘ numₘ(leftIndex)) ⟶ₘ conclusion)
          hRightBranches
          (hPointCheck := hRightCheck)
          (hConclusionCheck := Formula.check_admissible_complete
            (Formula.Admissible.imp
              (Formula.Admissible.equal hLeftCheck.admissible
                (finite_numeral_term_admissible leftIndex))
              hConclusionCheck.admissible))
    exact FirstOrder.Derives.impElim (Metatheory.Derives.imp_exchange
        (Formula.Admissible.equal hLeftCheck.admissible
          (finite_numeral_term_admissible leftIndex))
        hRightCondition hConclusionCheck.admissible)
      hRightCases
  simpa [rightCondition] using
    stdseq_numeral_member_condition_elim_of_theory
      leftBound left (rightCondition ⟶ₘ conclusion)
      hLeftBranches
      (hPointCheck := hLeftCheck)
      (hConclusionCheck := Formula.check_admissible_complete
        (Formula.Admissible.imp hRightCondition
          hConclusionCheck.admissible))
theorem stdseq_numeral_member_condition_elim
    (number : Nat) (point : SetTerm) (conclusion : SetFormula)
    (hBranch : ∀ index, index < number →
      ⊢ₘ[standard_sequence_semantics_theory]
        (point ≐ₘ numₘ(index)) ⟶ₘ conclusion)
    (hPointCheck : Term.CheckCertificate point SetSort.set := by
      prove_term_check)
    (hConclusionCheck : Formula.CheckCertificate conclusion := by
      prove_nd_formula_check) :
    ⊢ₘ[standard_sequence_semantics_theory]
      stdseq_numeral_member_condition number point ⟶ₘ conclusion :=
  stdseq_numeral_member_condition_elim_of_theory
    number point conclusion hBranch
    (hPointCheck := hPointCheck)
    (hConclusionCheck := hConclusionCheck)
private def stdseq_interval_member_condition (start : Nat) : Nat → SetTerm → SetFormula
  | 0, _ => Formula.falsum
  | length + 1, index =>
      (index ≐ₘ numₘ(start)) ∨ₘ
        stdseq_interval_member_condition (start + 1) length index
private def stdseq_reverse_interval_condition (start : Nat) : Nat → SetTerm → SetFormula
  | 0, _ => Formula.falsum
  | length + 1, index =>
      (index ≐ₘ numₘ(start + length)) ∨ₘ
        stdseq_reverse_interval_condition start length index
private theorem stdseq_reverse_interval_condition_admissible (start length : Nat) (index : SetTerm) (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible (stdseq_reverse_interval_condition start length index) := by
  induction length with
  | zero =>
      exact Formula.Admissible.falsum
  | succ length ih =>
      exact Formula.Admissible.disj (Formula.Admissible.equal hIndex (finite_numeral_term_admissible (start + length)))
        ih
private theorem standard_sequence_domain_condition_eq_interval (start : Nat) {elements : List SetTerm} (index : SetTerm) :
    standard_sequence_domain_condition start elements index =
      stdseq_interval_member_condition start elements.length index := by
  induction elements generalizing start with
  | nil => rfl
  | cons head tail ih =>
      simp [standard_sequence_domain_condition, stdseq_interval_member_condition,
        ih (start + 1)]
private theorem stdseq_disj_rotate
    {first second rest : SetFormula} (hFirst : Formula.Admissible first) (hSecond : Formula.Admissible second) (hRest : Formula.Admissible rest) :
    ⊢ₘ[standard_sequence_semantics_theory] (first ∨ₘ (second ∨ₘ rest)) ↔ₘ (second ∨ₘ (first ∨ₘ rest)) := by
  derive_prop
private theorem stdseq_reverse_interval_shift (start length : Nat) (index : SetTerm) (hIndex : Term.Admissible index SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] ((index ≐ₘ numₘ(start)) ∨ₘ
          stdseq_reverse_interval_condition (start + 1) length index) ↔ₘ ((index ≐ₘ numₘ(start + length)) ∨ₘ
          stdseq_reverse_interval_condition start length index) := by
  induction length generalizing start with
  | zero =>
      simpa [stdseq_reverse_interval_condition] using (Metatheory.Derives.iff_refl_m (T := standard_sequence_semantics_theory) (Γ := [])
          (φ := (index ≐ₘ numₘ(start)) ∨ₘ Formula.falsum) (Formula.Admissible.disj (Formula.Admissible.equal hIndex (finite_numeral_term_admissible start))
            Formula.Admissible.falsum))
  | succ length ih =>
      have hRotate :
          ⊢ₘ[standard_sequence_semantics_theory] ((index ≐ₘ numₘ(start)) ∨ₘ ((index ≐ₘ numₘ(start + (length + 1))) ∨ₘ
                stdseq_reverse_interval_condition (start + 1) length index)) ↔ₘ ((index ≐ₘ numₘ(start + (length + 1))) ∨ₘ ((index ≐ₘ numₘ(start)) ∨ₘ
                stdseq_reverse_interval_condition (start + 1) length index)) :=
        stdseq_disj_rotate (Formula.Admissible.equal hIndex (finite_numeral_term_admissible start)) (Formula.Admissible.equal hIndex
            (finite_numeral_term_admissible (start + (length + 1)))) (stdseq_reverse_interval_condition_admissible (start + 1) length index hIndex)
      have hTail := stdseq_disj_congr (Metatheory.Derives.iff_refl_m (T := standard_sequence_semantics_theory) (Γ := [])
          (φ := index ≐ₘ numₘ(start + (length + 1))) (Formula.Admissible.equal hIndex (finite_numeral_term_admissible (start + (length + 1))))) (ih start)
      have hStep := FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (Metatheory.Derives.iff_trans_m (T := standard_sequence_semantics_theory) (Γ := [])
            (Formula.Admissible.iff_right hRotate.admissible) (Formula.Admissible.iff_left hRotate.admissible) (Formula.Admissible.iff_right hTail.admissible))
          hRotate)
        hTail
      simpa [stdseq_reverse_interval_condition, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hStep
private theorem stdseq_interval_reverse_iff (start length : Nat) (index : SetTerm) (hIndex : Term.Admissible index SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory]
      stdseq_interval_member_condition start length index ↔ₘ
        stdseq_reverse_interval_condition start length index := by
  induction length generalizing start with
  | zero =>
      exact Metatheory.Derives.iff_refl_m (T := standard_sequence_semantics_theory) (Γ := []) (φ := Formula.falsum)
        Formula.Admissible.falsum
  | succ length ih =>
      have hHeadRefl :
          ⊢ₘ[standard_sequence_semantics_theory] (index ≐ₘ numₘ(start)) ↔ₘ (index ≐ₘ numₘ(start)) :=
        Metatheory.Derives.iff_refl_m (Formula.Admissible.equal hIndex (finite_numeral_term_admissible start))
      have hFirst := stdseq_disj_congr hHeadRefl (ih (start + 1))
      have hShift := stdseq_reverse_interval_shift start length index hIndex
      have hStep := FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (Metatheory.Derives.iff_trans_m (T := standard_sequence_semantics_theory) (Γ := [])
            (Formula.Admissible.iff_right hFirst.admissible) (Formula.Admissible.iff_left hFirst.admissible) (Formula.Admissible.iff_right hShift.admissible))
          hFirst)
        hShift
      simpa [stdseq_interval_member_condition,
        stdseq_reverse_interval_condition] using hStep
private theorem stdseq_reverse_zero_eq_numeral_condition (length : Nat) (index : SetTerm) :
    stdseq_reverse_interval_condition 0 length index =
      stdseq_numeral_member_condition length index := by
  induction length with
  | zero => rfl
  | succ length ih =>
      simp [stdseq_reverse_interval_condition,
        stdseq_numeral_member_condition, ih]
theorem standard_sequence_domain_condition_iff_numeral_mem
    {elements : List SetTerm} (index : SetTerm) (hIndex : Term.Admissible index SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory]
      standard_sequence_domain_condition 0 elements index ↔ₘ (index ∈ₘ numₘ(elements.length)) := by
  have hInterval := stdseq_interval_reverse_iff
    0 elements.length index hIndex
  have hNumeral := stdseq_numeral_member_iff elements.length index hIndex
  have hNumeralSymm := stdseq_iff_symm hNumeral
  rw [standard_sequence_domain_condition_eq_interval 0 index,
    stdseq_reverse_zero_eq_numeral_condition] at *
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (Metatheory.Derives.iff_trans_m (T := standard_sequence_semantics_theory) (Γ := [])
        (Formula.Admissible.iff_right hInterval.admissible) (Formula.Admissible.iff_left hInterval.admissible)
        (Formula.Admissible.iff_right hNumeralSymm.admissible))
      hInterval)
    hNumeralSymm
theorem standard_sequence_domain_eq_numeral_length
    {elements : List SetTerm} (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set)
    (hElementsFreshZero : ∀ element, element ∈ elements →
      (SetSort.set, 0) ∉ Term.freeSupport element)
    (hElementsFreshOne : ∀ element, element ∈ elements →
      (SetSort.set, 1) ∉ Term.freeSupport element) :
    ⊢ₘ[standard_sequence_semantics_theory]
      domₘ(standard_sequence elements) ≐ₘ
        numₘ(elements.length) := by
  let sequence := standard_sequence elements
  let domain := domₘ(sequence)
  let numeral := numₘ(elements.length)
  have hSequence : Term.Admissible sequence SetSort.set :=
    seq_admissible_m 0 hElements
  have hDomain : Term.Admissible domain SetSort.set :=
    domain_term_admissible sequence hSequence
  have hNumeral : Term.Admissible numeral SetSort.set :=
    finite_numeral_term_admissible elements.length
  have hSequenceFreshZero : (SetSort.set, 0) ∉ Term.freeSupport sequence := by
    exact standard_sequence_from_fresh_at 0 0 hElementsFreshZero
  have hSequenceFreshOne : (SetSort.set, 1) ∉ Term.freeSupport sequence := by
    exact standard_sequence_from_fresh_at 1 0 hElementsFreshOne
  have hIndex : Term.Admissible (x#1) SetSort.set :=
    set_variable_admissible 1
  have hIndexFreshZero : (SetSort.set, 0) ∉ Term.freeSupport (x#1) := by
    native_decide
  have hRelation := standard_sequence_from_is_relation
    0 hElements hElementsFreshZero
  have hDomainGraph := standard_sequence_relation_domain_member_iff_graph_exists
    sequence (x#1) hSequence hIndex
    hSequenceFreshZero hIndexFreshZero hRelation
  have hGraphCondition := standard_sequence_from_graph_exists_iff_domain_condition
    0 (x#1) hElements hIndex hIndexFreshZero hElementsFreshZero
  have hConditionNumeral := standard_sequence_domain_condition_iff_numeral_mem (elements := elements) (x#1) hIndex
  have hDomainCondition := FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (Metatheory.Derives.iff_trans_m
        (T := standard_sequence_semantics_theory) (Γ := []) (Formula.Admissible.iff_right hDomainGraph.admissible)
        (Formula.Admissible.iff_left hDomainGraph.admissible) (Formula.Admissible.iff_right hGraphCondition.admissible))
      hDomainGraph)
    hGraphCondition
  have hPoint :
      ⊢ₘ[standard_sequence_semantics_theory] ((x#1) ∈ₘ domain) ↔ₘ ((x#1) ∈ₘ numeral) := by
    have hStep := FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (Metatheory.Derives.iff_trans_m (T := standard_sequence_semantics_theory) (Γ := [])
          (Formula.Admissible.iff_right hDomainCondition.admissible) (Formula.Admissible.iff_left hDomainCondition.admissible)
          (Formula.Admissible.iff_right hConditionNumeral.admissible))
        hDomainCondition)
      hConditionNumeral
    simpa [sequence, domain, numeral, standard_sequence] using hStep
  have hClosed :
      ⊢ₘ[standard_sequence_semantics_theory]
        ∀ₘ[SetSort.set, 1], (((x#1) ∈ₘ domain) ↔ₘ ((x#1) ∈ₘ numeral)) := by
    derive_close (1) using hPoint
  have hDomainFreshOne : (SetSort.set, 1) ∉ Term.freeSupport domain :=
    stdseq_domain_term_fresh 1 sequence hSequenceFreshOne
  have hNumeralFreshOne : (SetSort.set, 1) ∉ Term.freeSupport numeral := by
    rw [finite_numeral_term_freeSupport elements.length]
    intro hMember
    cases hMember
  have hDomainClose :
      Term.closeFreeAt SetSort.set 1 0 domain = domain :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 1 0 domain hDomain.2 hDomainFreshOne
  have hNumeralClose :
      Term.closeFreeAt SetSort.set 1 0 numeral = numeral :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 1 0 numeral hNumeral.2 hNumeralFreshOne
  have hAgreement :
      ⊢ₘ[standard_sequence_semantics_theory]
        membership_agreement domain numeral := by
    simpa [membership_agreement, Formula.closeFreeAt,
      Term.closeFreeAt, hDomainClose, hNumeralClose] using hClosed
  have hExtensionality := stdseq_weaken_extensionality (extensionality_instance_derives_of_admissible
      domain numeral hDomain hNumeral)
  have hEquality :
      ⊢ₘ[standard_sequence_semantics_theory] domain ≐ₘ numeral :=
    FirstOrder.Derives.impElim (by
        simpa [extensionality_instance, agreement_to_equality] using
          hExtensionality)
      hAgreement
  simpa [sequence, domain, numeral, standard_sequence] using hEquality
/--
基础公理排除任意闭集合项属于自身。
该结论不依赖有限序列的具体结构；放在标准序列联合理论中公开后，有限 numeral
互异、有限层级反演以及后续编码有界性可以共同复用同一条基础性接口。
-/
theorem standard_sequence_not_mem_self (term : SetTerm) (hTerm : Term.Admissible term SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] ¬ₘ (term ∈ₘ term) := by
  exact stdseq_weaken_membership_irreflexive (membership_irreflexive_instance_derives term hTerm)
/-- 外部自然数的严格次序在对象层解释为标准 numeral 的成员关系。 -/
theorem standard_sequence_finite_numeral_mem_of_lt (left right : Nat) (hLt : left < right) :
    ⊢ₘ[standard_sequence_semantics_theory]
      numₘ(left) ∈ₘ numₘ(right) := by
  induction right generalizing left with
  | zero =>
      exact False.elim (Nat.not_lt_zero left hLt)
  | succ right ih =>
      by_cases hEqual : left = right
      · subst left
        simpa [finite_numeral_term] using
          stdseq_weaken_successor (mem_successor_self (numₘ(right)) (finite_numeral_term_admissible right))
      · have hEarlier : left < right := by omega
        have hMember := ih left hEarlier
        have hStep := stdseq_weaken_successor (mem_successor_of_mem (numₘ(right)) (numₘ(left)) (finite_numeral_term_admissible right)
            (finite_numeral_term_admissible left))
        exact FirstOrder.Derives.impElim (by simpa [finite_numeral_term] using hStep)
          hMember
/--
标准 numeral 的成员关系随右端有限初段单调。
该接口保留开放的元素项，后续有限 hull 的传递性证明无需先把元素重新识别成
具体 numeral；有限析取只在本证明内部完成。
-/
theorem standard_sequence_finite_numeral_mem_mono (left right : Nat) (element : SetTerm) (hElement : Term.Admissible element SetSort.set) (hLe : left ≤ right) :
    ⊢ₘ[standard_sequence_semantics_theory] (element ∈ₘ numₘ(left)) ⟶ₘ (element ∈ₘ numₘ(right)) := by
  let sourceMembership : SetFormula :=
    element ∈ₘ numₘ(left)
  let targetMembership : SetFormula :=
    element ∈ₘ numₘ(right)
  let cases : SetFormula :=
    stdseq_numeral_member_condition left element
  have hCases :
      ⊢ₘ[standard_sequence_semantics_theory]
        cases ⟶ₘ targetMembership := by
    nd_apply stdseq_numeral_member_condition_elim
      left element targetMembership
    intro index hIndex
    let equality : SetFormula :=
      element ≐ₘ numₘ(index)
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature := [equality]
    have hEquality :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          element ≐ₘ numₘ(index) := by
      simpa [Γ, equality] using
        (FirstOrder.Derives.assumption
          (T := standard_sequence_semantics_theory)
          (Γ := Γ) (φ := equality) (by simp [Γ]))
    have hCanonical :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          numₘ(index) ∈ₘ numₘ(right) :=
      FirstOrder.Derives.context_weaken_cons (standard_sequence_finite_numeral_mem_of_lt
          index right (Nat.lt_of_lt_of_le hIndex hLe))
    exact FirstOrder.Derives.iffElimLeft (membership_left_iff_of_equality
        element (numₘ(index)) (numₘ(right))
        hElement (finite_numeral_term_admissible index) (finite_numeral_term_admissible right)
        hEquality)
      hCanonical
  have hMembershipIff :
      ⊢ₘ[standard_sequence_semantics_theory]
        sourceMembership ↔ₘ cases := by
    simpa [sourceMembership, cases] using
      stdseq_numeral_member_iff left element hElement
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [sourceMembership]
  have hSource :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        sourceMembership := by
    exact FirstOrder.Derives.assumption (by simp [Γ])
  have hCase :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        cases :=
    FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons
        hMembershipIff)
      hSource
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hCases)
    hCase
/--
标准有限初段具有传递性：初段元素的任意元素仍属于同一初段。
证明先把外层成员有限分类为某个标准 numeral，再沿对象等式运输内层成员关系，
最后使用上面的初段单调性。该结论是 proof-code 有限 hull 逐层保持传递性的基例。
-/
theorem standard_sequence_finite_numeral_mem_trans (bound : Nat) (container element : SetTerm) (hContainer : Term.Admissible container SetSort.set)
    (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] (container ∈ₘ numₘ(bound)) ⟶ₘ ((element ∈ₘ container) ⟶ₘ (element ∈ₘ numₘ(bound))) := by
  let containerMembership : SetFormula :=
    container ∈ₘ numₘ(bound)
  let elementMembership : SetFormula :=
    element ∈ₘ container
  let targetMembership : SetFormula :=
    element ∈ₘ numₘ(bound)
  let cases : SetFormula :=
    stdseq_numeral_member_condition bound container
  have hCases :
      ⊢ₘ[standard_sequence_semantics_theory]
        cases ⟶ₘ (elementMembership ⟶ₘ targetMembership) := by
    nd_apply stdseq_numeral_member_condition_elim
      bound container (elementMembership ⟶ₘ targetMembership)
    intro index hIndex
    let equality : SetFormula :=
      container ≐ₘ numₘ(index)
    nd_apply FirstOrder.Derives.impIntro
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature :=
      [elementMembership, equality]
    have hEquality :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          container ≐ₘ numₘ(index) := by
      exact FirstOrder.Derives.assumption (by simp [Γ, equality])
    have hMember :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          element ∈ₘ container := by
      exact FirstOrder.Derives.assumption (by simp [Γ, elementMembership])
    have hMemberAtIndex :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          element ∈ₘ numₘ(index) :=
      FirstOrder.Derives.iffElimRight (membership_right_iff_of_equality
          element container (numₘ(index))
          hElement hContainer (finite_numeral_term_admissible index)
          hEquality)
        hMember
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) (standard_sequence_finite_numeral_mem_mono
          index bound element hElement (Nat.le_of_lt hIndex)))
      hMemberAtIndex
  have hMembershipIff :
      ⊢ₘ[standard_sequence_semantics_theory]
        containerMembership ↔ₘ cases := by
    simpa [containerMembership, cases] using
      stdseq_numeral_member_iff bound container hContainer
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [elementMembership, containerMembership]
  have hContainerMember :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        containerMembership := by
    exact FirstOrder.Derives.assumption (by simp [Γ])
  have hElementMember :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        elementMembership := by
    exact FirstOrder.Derives.assumption (by simp [Γ])
  have hCase :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        cases :=
    FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ])
        hMembershipIff)
      hContainerMember
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ])
        hCases)
      hCase)
    hElementMember
/-- 严格较小的标准 numeral 不等于较大的标准 numeral。 -/
theorem standard_sequence_finite_numeral_ne_of_lt (left right : Nat) (hLt : left < right) :
    ⊢ₘ[standard_sequence_semantics_theory]
      ¬ₘ (numₘ(left) ≐ₘ numₘ(right)) := by
  let equality : SetFormula :=
    numₘ(left) ≐ₘ numₘ(right)
  nd_apply FirstOrder.Derives.negIntro
  have hEquality :
      [equality] ⊢ₘ[standard_sequence_semantics_theory] equality :=
    .assumption (by simp)
  have hMembership :
      [equality] ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(left) ∈ₘ numₘ(right) :=
    FirstOrder.Derives.context_weaken_cons (standard_sequence_finite_numeral_mem_of_lt left right hLt)
  have hTransport :=
    membership_right_iff_of_equality (numₘ(left)) (numₘ(left)) (numₘ(right)) (finite_numeral_term_admissible left) (finite_numeral_term_admissible left)
      (finite_numeral_term_admissible right)
      hEquality
  have hSelfMembership :
      [equality] ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(left) ∈ₘ numₘ(left) :=
    FirstOrder.Derives.iffElimLeft hTransport hMembership
  exact FirstOrder.Derives.negElim hSelfMembership (FirstOrder.Derives.context_weaken_cons (standard_sequence_not_mem_self (numₘ(left))
        (finite_numeral_term_admissible left)))
/-- 不同外部自然数对应的标准 numeral 在对象理论中互异。 -/
theorem standard_sequence_finite_numeral_ne
    {left right : Nat} (hNe : left ≠ right) :
    ⊢ₘ[standard_sequence_semantics_theory]
      ¬ₘ (numₘ(left) ≐ₘ numₘ(right)) := by
  rcases Nat.lt_or_gt_of_ne hNe with hLt | hGt
  · exact standard_sequence_finite_numeral_ne_of_lt left right hLt
  · have hReverse :=
      standard_sequence_finite_numeral_ne_of_lt right left hGt
    have hSymmetry :
        ⊢ₘ[standard_sequence_semantics_theory] (numₘ(left) ≐ₘ numₘ(right)) ⟶ₘ (numₘ(right) ≐ₘ numₘ(left)) :=
      Metatheory.Derives.equality_symm_imp
    nd_apply FirstOrder.Derives.negIntro
    have hEquality :
        [numₘ(left) ≐ₘ numₘ(right)]
          ⊢ₘ[standard_sequence_semantics_theory]
            numₘ(left) ≐ₘ numₘ(right) :=
      .assumption (by simp)
    have hReverseEquality := FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hSymmetry)
      hEquality
    exact FirstOrder.Derives.negElim hReverseEquality (FirstOrder.Derives.context_weaken_cons hReverse)
/-- 外部 `left < right` 不成立时，对象 numeral `left` 不属于 `right`。 -/
theorem standard_sequence_finite_numeral_not_mem_of_not_lt (left right : Nat) (hNotLt : ¬ left < right) :
    ⊢ₘ[standard_sequence_semantics_theory]
      ¬ₘ (numₘ(left) ∈ₘ numₘ(right)) := by
  let membership : SetFormula :=
    numₘ(left) ∈ₘ numₘ(right)
  let condition : SetFormula :=
    stdseq_numeral_member_condition right (numₘ(left))
  nd_apply FirstOrder.Derives.negIntro
  have hMembership :
      [membership] ⊢ₘ[standard_sequence_semantics_theory]
        membership :=
    FirstOrder.Derives.assumption (by simp)
  have hCondition :
      [membership] ⊢ₘ[standard_sequence_semantics_theory]
        condition := by
    exact FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons (stdseq_numeral_member_iff
          right (numₘ(left)) (finite_numeral_term_admissible left))) (by simpa [membership] using hMembership)
  have hElim :
      ⊢ₘ[standard_sequence_semantics_theory]
        condition ⟶ₘ Formula.falsum := by
    nd_apply stdseq_numeral_member_condition_elim
      right (numₘ(left)) Formula.falsum
    intro index hIndex
    nd_apply FirstOrder.Derives.impIntro
    have hNe : left ≠ index := by omega
    exact FirstOrder.Derives.negElim (FirstOrder.Derives.assumption (T := standard_sequence_semantics_theory) (Γ := [numₘ(left) ≐ₘ numₘ(index)])
        (φ := numₘ(left) ≐ₘ numₘ(index)) (by simp)) (FirstOrder.Derives.context_weaken_cons (standard_sequence_finite_numeral_ne hNe))
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (by simpa [condition] using hElim))
    hCondition
/-- 已越过的下标不会再次出现在标准序列的递归尾部。 -/
private theorem standard_sequence_pair_member_condition_index_ne (previous start : Nat) (hPrevious : previous < start)
    {elements : List SetTerm} (index value : SetTerm) (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hIndex : Term.Admissible index SetSort.set) (hValue : Term.Admissible value SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory]
      standard_sequence_pair_member_condition start elements index value ⟶ₘ
        ¬ₘ (index ≐ₘ numₘ(previous)) := by
  induction elements generalizing start with
  | nil =>
      nd_apply FirstOrder.Derives.impIntro
      have hCondition :
          [standard_sequence_pair_member_condition start [] index value]
            ⊢ₘ[standard_sequence_semantics_theory]
              standard_sequence_pair_member_condition start [] index value :=
        .assumption (by simp)
      have hFalse :
          [standard_sequence_pair_member_condition start [] index value]
            ⊢ₘ[standard_sequence_semantics_theory] Formula.falsum := by
        simpa [standard_sequence_pair_member_condition] using hCondition
      exact FirstOrder.Derives.falsumElim hFalse
  | cons head tail ih =>
      have hHead : Term.Admissible head SetSort.set :=
        hElements head (by simp)
      have hTail :
          ∀ element, element ∈ tail →
            Term.Admissible element SetSort.set := by
        intro element hElement
        exact hElements element (by simp [hElement])
      have hNumeralNe :
          ⊢ₘ[standard_sequence_semantics_theory]
            ¬ₘ (numₘ(previous) ≐ₘ numₘ(start)) :=
        standard_sequence_finite_numeral_ne_of_lt previous start hPrevious
      have hTailNe :=
        ih (start + 1) (Nat.lt_succ_of_lt hPrevious) hTail
      let headCase : SetFormula := (index ≐ₘ numₘ(start)) ∧ₘ (value ≐ₘ head)
      let tailCase : SetFormula :=
        standard_sequence_pair_member_condition (start + 1) tail index value
      let condition : SetFormula := headCase ∨ₘ tailCase
      let conclusion : SetFormula :=
        ¬ₘ (index ≐ₘ numₘ(previous))
      have hImp :
          ⊢ₘ[standard_sequence_semantics_theory] condition ⟶ₘ conclusion := by
        nd_apply FirstOrder.Derives.impIntro
        let Γ : Context signature := [condition]
        have hCondition : Γ ⊢ₘ[standard_sequence_semantics_theory] condition :=
          .assumption (by simp [Γ])
        apply FirstOrder.Derives.disjElim hCondition
        · nd_apply FirstOrder.Derives.negIntro
          let Δ : Context signature := (index ≐ₘ numₘ(previous)) :: headCase :: Γ
          have hHeadCase : Δ ⊢ₘ[standard_sequence_semantics_theory] headCase :=
            .assumption (by simp [Δ])
          have hIndexStart :
              Δ ⊢ₘ[standard_sequence_semantics_theory]
                index ≐ₘ numₘ(start) :=
            FirstOrder.Derives.conjElimLeft hHeadCase
          have hIndexPrevious :
              Δ ⊢ₘ[standard_sequence_semantics_theory]
                index ≐ₘ numₘ(previous) :=
            .assumption (by simp [Δ])
          have hPreviousIndex :
              Δ ⊢ₘ[standard_sequence_semantics_theory]
                numₘ(previous) ≐ₘ index :=
            Metatheory.Derives.equality_symm hIndexPrevious
          have hPreviousStart :
              Δ ⊢ₘ[standard_sequence_semantics_theory]
                numₘ(previous) ≐ₘ numₘ(start) :=
            Metatheory.Derives.equality_trans
              hPreviousIndex hIndexStart
          exact FirstOrder.Derives.negElim hPreviousStart (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp [Δ, Γ]) hNumeralNe)
        · have hTailImp := FirstOrder.Derives.context_weaken (Γ := []) (Δ := tailCase :: Γ) (by simp [Γ]) hTailNe
          have hTailCase :
              tailCase :: Γ ⊢ₘ[standard_sequence_semantics_theory] tailCase :=
            .assumption (by simp)
          exact FirstOrder.Derives.impElim (by simpa [tailCase, conclusion] using hTailImp)
            hTailCase
      simpa [condition, headCase, tailCase, conclusion,
        standard_sequence_pair_member_condition] using hImp
/-- 递归配对条件在同一下标处至多给出一个值。 -/
private theorem standard_sequence_pair_member_condition_unique (start : Nat) {elements : List SetTerm} (index first second : SetTerm)
    (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hIndex : Term.Admissible index SetSort.set) (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] (standard_sequence_pair_member_condition start elements index first ∧ₘ
          standard_sequence_pair_member_condition start elements index second) ⟶ₘ (first ≐ₘ second) := by
  induction elements generalizing start with
  | nil =>
      nd_apply FirstOrder.Derives.impIntro
      have hConditions :
          [standard_sequence_pair_member_condition start [] index first ∧ₘ
            standard_sequence_pair_member_condition start [] index second]
            ⊢ₘ[standard_sequence_semantics_theory]
              standard_sequence_pair_member_condition start [] index first ∧ₘ
                standard_sequence_pair_member_condition start [] index second :=
        .assumption (by simp)
      have hFalse :
          [standard_sequence_pair_member_condition start [] index first ∧ₘ
            standard_sequence_pair_member_condition start [] index second]
            ⊢ₘ[standard_sequence_semantics_theory] Formula.falsum := by
        simpa [standard_sequence_pair_member_condition] using (FirstOrder.Derives.conjElimLeft hConditions)
      exact FirstOrder.Derives.falsumElim hFalse
  | cons head tail ih =>
      have hHead : Term.Admissible head SetSort.set :=
        hElements head (by simp)
      have hTail :
          ∀ element, element ∈ tail →
            Term.Admissible element SetSort.set := by
        intro element hElement
        exact hElements element (by simp [hElement])
      have hHeadNeTailFirst := standard_sequence_pair_member_condition_index_ne
        start (start + 1) (Nat.lt_succ_self start) (elements := tail) index first hTail hIndex hFirst
      have hHeadNeTailSecond := standard_sequence_pair_member_condition_index_ne
        start (start + 1) (Nat.lt_succ_self start) (elements := tail) index second hTail hIndex hSecond
      have hTailUnique := ih (start + 1) hTail
      let headFirst : SetFormula := (index ≐ₘ numₘ(start)) ∧ₘ (first ≐ₘ head)
      let headSecond : SetFormula := (index ≐ₘ numₘ(start)) ∧ₘ (second ≐ₘ head)
      let tailFirst : SetFormula :=
        standard_sequence_pair_member_condition (start + 1) tail index first
      let tailSecond : SetFormula :=
        standard_sequence_pair_member_condition (start + 1) tail index second
      let equality : SetFormula := first ≐ₘ second
      have hHeadHead :
          ⊢ₘ[standard_sequence_semantics_theory] (headFirst ∧ₘ headSecond) ⟶ₘ equality := by
        nd_apply FirstOrder.Derives.impIntro
        let Γ : Context signature := [headFirst ∧ₘ headSecond]
        have hCases :
            Γ ⊢ₘ[standard_sequence_semantics_theory] headFirst ∧ₘ headSecond :=
          .assumption (by simp [Γ])
        have hFirstHead : Γ ⊢ₘ[standard_sequence_semantics_theory] first ≐ₘ head :=
          FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimLeft hCases)
        have hSecondHead : Γ ⊢ₘ[standard_sequence_semantics_theory] second ≐ₘ head :=
          FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimRight hCases)
        have hHeadSecond : Γ ⊢ₘ[standard_sequence_semantics_theory] head ≐ₘ second :=
          Metatheory.Derives.equality_symm hSecondHead
        exact Metatheory.Derives.equality_trans
          hFirstHead hHeadSecond
      have hHeadTail :
          ⊢ₘ[standard_sequence_semantics_theory] (headFirst ∧ₘ tailSecond) ⟶ₘ equality := by
        nd_apply FirstOrder.Derives.impIntro
        let Γ : Context signature := [headFirst ∧ₘ tailSecond]
        have hCases :
            Γ ⊢ₘ[standard_sequence_semantics_theory] headFirst ∧ₘ tailSecond :=
          .assumption (by simp [Γ])
        have hIndexStart :
            Γ ⊢ₘ[standard_sequence_semantics_theory] index ≐ₘ numₘ(start) :=
          FirstOrder.Derives.conjElimLeft (FirstOrder.Derives.conjElimLeft hCases)
        have hTailCase : Γ ⊢ₘ[standard_sequence_semantics_theory] tailSecond :=
          FirstOrder.Derives.conjElimRight hCases
        have hTailNe := FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ])
            (by simpa [tailSecond] using hHeadNeTailSecond))
          hTailCase
        exact FirstOrder.Derives.falsumElim
          (FirstOrder.Derives.negElim hIndexStart hTailNe)
      have hTailHead :
          ⊢ₘ[standard_sequence_semantics_theory] (tailFirst ∧ₘ headSecond) ⟶ₘ equality := by
        nd_apply FirstOrder.Derives.impIntro
        let Γ : Context signature := [tailFirst ∧ₘ headSecond]
        have hCases :
            Γ ⊢ₘ[standard_sequence_semantics_theory] tailFirst ∧ₘ headSecond :=
          .assumption (by simp [Γ])
        have hTailCase : Γ ⊢ₘ[standard_sequence_semantics_theory] tailFirst :=
          FirstOrder.Derives.conjElimLeft hCases
        have hIndexStart :
            Γ ⊢ₘ[standard_sequence_semantics_theory] index ≐ₘ numₘ(start) :=
          FirstOrder.Derives.conjElimLeft (FirstOrder.Derives.conjElimRight hCases)
        have hTailNe := FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ])
            (by simpa [tailFirst] using hHeadNeTailFirst))
          hTailCase
        exact FirstOrder.Derives.falsumElim
          (FirstOrder.Derives.negElim hIndexStart hTailNe)
      have hTailTail :
          ⊢ₘ[standard_sequence_semantics_theory] (tailFirst ∧ₘ tailSecond) ⟶ₘ equality := by
        simpa [tailFirst, tailSecond, equality] using hTailUnique
      have hCombined :
          ⊢ₘ[standard_sequence_semantics_theory] (((headFirst ∨ₘ tailFirst) ∧ₘ (headSecond ∨ₘ tailSecond)) ⟶ₘ equality) := by
        nd_apply FirstOrder.Derives.impIntro
        let Γ : Context signature :=
          [(headFirst ∨ₘ tailFirst) ∧ₘ (headSecond ∨ₘ tailSecond)]
        have hCases :
            Γ ⊢ₘ[standard_sequence_semantics_theory] (headFirst ∨ₘ tailFirst) ∧ₘ (headSecond ∨ₘ tailSecond) :=
          .assumption (by simp [Γ])
        have hFirstCases := FirstOrder.Derives.conjElimLeft hCases
        have hSecondCases := FirstOrder.Derives.conjElimRight hCases
        apply FirstOrder.Derives.disjElim hFirstCases
        · let ΓFirst : Context signature := headFirst :: Γ
          have hSecondCases' :
              ΓFirst ⊢ₘ[standard_sequence_semantics_theory]
                headSecond ∨ₘ tailSecond :=
            FirstOrder.Derives.context_weaken (Γ := Γ) (Δ := ΓFirst) (by
                intro ψ hψ
                simp only [ΓFirst, List.mem_cons]
                exact Or.inr hψ)
              hSecondCases
          apply FirstOrder.Derives.disjElim hSecondCases'
          · let ΓBoth : Context signature := headSecond :: ΓFirst
            exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := ΓBoth) (by simp [ΓBoth]) hHeadHead)
              (FirstOrder.Derives.conjIntro (.assumption (by simp [ΓFirst])) (.assumption (by simp)))
          · let ΓBoth : Context signature := tailSecond :: ΓFirst
            exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := ΓBoth) (by simp [ΓBoth]) hHeadTail)
              (FirstOrder.Derives.conjIntro (.assumption (by simp [ΓFirst])) (.assumption (by simp)))
        · let ΓFirst : Context signature := tailFirst :: Γ
          have hSecondCases' :
              ΓFirst ⊢ₘ[standard_sequence_semantics_theory]
                headSecond ∨ₘ tailSecond :=
            FirstOrder.Derives.context_weaken (Γ := Γ) (Δ := ΓFirst) (by
                intro ψ hψ
                simp only [ΓFirst, List.mem_cons]
                exact Or.inr hψ)
              hSecondCases
          apply FirstOrder.Derives.disjElim hSecondCases'
          · let ΓBoth : Context signature := headSecond :: ΓFirst
            exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := ΓBoth) (by simp [ΓBoth]) hTailHead)
              (FirstOrder.Derives.conjIntro (.assumption (by simp [ΓFirst])) (.assumption (by simp)))
          · let ΓBoth : Context signature := tailSecond :: ΓFirst
            exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := ΓBoth) (by simp [ΓBoth]) hTailTail)
              (FirstOrder.Derives.conjIntro (.assumption (by simp [ΓFirst])) (.assumption (by simp)))
      simpa [headFirst, headSecond, tailFirst, tailSecond,
        equality, standard_sequence_pair_member_condition] using hCombined
/-- 标准序列在同一下标处至多出现一个值。 -/
private theorem stdseq_pair_member_unique (start : Nat) {elements : List SetTerm} (index first second : SetTerm) (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hIndex : Term.Admissible index SetSort.set) (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] ((⟨index, first⟩ₘ ∈ₘ standard_sequence_from start elements) ∧ₘ
          (⟨index, second⟩ₘ ∈ₘ standard_sequence_from start elements)) ⟶ₘ (first ≐ₘ second) := by
  have hFirstIff := standard_sequence_from_pair_member_iff start index first
    hElements hIndex hFirst
  have hSecondIff := standard_sequence_from_pair_member_iff start index second
    hElements hIndex hSecond
  have hUnique := standard_sequence_pair_member_condition_unique
    start index first second hElements hIndex hFirst hSecond
  let premise : SetFormula := (⟨index, first⟩ₘ ∈ₘ standard_sequence_from start elements) ∧ₘ (⟨index, second⟩ₘ ∈ₘ standard_sequence_from start elements)
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [premise]
  have hPremise : Γ ⊢ₘ[standard_sequence_semantics_theory] premise :=
    .assumption (by simp [Γ])
  have hFirstMember := FirstOrder.Derives.conjElimLeft hPremise
  have hSecondMember := FirstOrder.Derives.conjElimRight hPremise
  have hFirstCondition := FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hFirstIff)
    (by simpa [premise] using hFirstMember)
  have hSecondCondition := FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hSecondIff)
    (by simpa [premise] using hSecondMember)
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hUnique)
    (FirstOrder.Derives.conjIntro hFirstCondition hSecondCondition)
/-- 元素避开三个内部编号时，标准序列满足集合编码函数谓词。 -/
theorem standard_sequence_from_is_function (start : Nat) {elements : List SetTerm} (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set)
    (hElementsFreshZero : ∀ element, element ∈ elements →
      (SetSort.set, 0) ∉ Term.freeSupport element)
    (hElementsFreshOne : ∀ element, element ∈ elements →
      (SetSort.set, 1) ∉ Term.freeSupport element)
    (hElementsFreshTwo : ∀ element, element ∈ elements →
      (SetSort.set, 2) ∉ Term.freeSupport element) :
    ⊢ₘ[standard_sequence_semantics_theory]
      is_function_formula (standard_sequence_from start elements) := by
  let sequence := standard_sequence_from start elements
  have hSequence : Term.Admissible sequence SetSort.set :=
    seq_admissible_m start hElements
  have hRelation :=
    standard_sequence_from_is_relation
      start hElements hElementsFreshZero
  have hSinglePoint := stdseq_pair_member_unique
    start (elements := elements) (x#0) (x#1) (x#2)
    hElements (set_variable_admissible 0) (set_variable_admissible 1) (set_variable_admissible 2)
  have hSingleClosed :
      ⊢ₘ[standard_sequence_semantics_theory]
        function_single_valued_condition (standard_sequence_from start elements) := by
    have hClosed :
        ⊢ₘ[standard_sequence_semantics_theory]
          ∀ₘ[SetSort.set, 0],
            ∀ₘ[SetSort.set, 1],
              ∀ₘ[SetSort.set, 2], ((⟨x#0, x#1⟩ₘ ∈ₘ
                    standard_sequence_from start elements) ∧ₘ (⟨x#0, x#2⟩ₘ ∈ₘ
                      standard_sequence_from start elements)) ⟶ₘ (x#1 ≐ₘ x#2) := by
      derive_close (0, 1, 2) using hSinglePoint
    have hSequenceFreshZero :
        (SetSort.set, 0) ∉ Term.freeSupport sequence :=
      standard_sequence_from_fresh_at
        0 start hElementsFreshZero
    have hSequenceFreshOne :
        (SetSort.set, 1) ∉ Term.freeSupport sequence :=
      standard_sequence_from_fresh_at
        1 start hElementsFreshOne
    have hSequenceFreshTwo :
        (SetSort.set, 2) ∉ Term.freeSupport sequence :=
      standard_sequence_from_fresh_at
        2 start hElementsFreshTwo
    have hSequenceCloseZero (depth : Nat) :
        Term.closeFreeAt SetSort.set 0 depth sequence = sequence :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 0 depth sequence hSequence.2
          hSequenceFreshZero
    have hSequenceCloseOne (depth : Nat) :
        Term.closeFreeAt SetSort.set 1 depth sequence = sequence :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 1 depth sequence hSequence.2
          hSequenceFreshOne
    have hSequenceCloseTwo (depth : Nat) :
        Term.closeFreeAt SetSort.set 2 depth sequence = sequence :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 2 depth sequence hSequence.2
          hSequenceFreshTwo
    simpa [function_single_valued_condition, sequence,
      Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt, hSequenceCloseZero,
      hSequenceCloseOne, hSequenceCloseTwo] using hClosed
  have hCondition :
      ⊢ₘ[standard_sequence_semantics_theory]
        is_function_condition sequence :=
    FirstOrder.Derives.conjIntro (by simpa [sequence] using hRelation) (by simpa [sequence] using hSingleClosed)
  have hDefinition := stdseq_weaken_function_predicate (is_function_iff_condition sequence hSequence)
  exact FirstOrder.Derives.iffElimLeft hDefinition hCondition
/-- `getElem?` 选出的列表元素确实出现在标准序列图中。 -/
theorem standard_sequence_from_getElem?_graph_mem (start : Nat) {elements : List SetTerm}
    {index : Nat} {element : SetTerm} (hGet : elements[index]? = some element) (hElements : ∀ item, item ∈ elements →
      Term.Admissible item SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory]
      ⟨numₘ(start + index), element⟩ₘ ∈ₘ
        standard_sequence_from start elements := by
  induction elements generalizing start index with
  | nil =>
      simp at hGet
  | cons head tail ih =>
      cases index with
      | zero =>
          simp at hGet
          subst element
          have hHead : Term.Admissible head SetSort.set :=
            hElements head (by simp)
          have hTail :
              ∀ item, item ∈ tail →
                Term.Admissible item SetSort.set := by
            intro item hItem
            exact hElements item (by simp [hItem])
          have hPairIff := standard_sequence_from_pair_member_iff
            start (elements := head :: tail) (numₘ(start)) head hElements (finite_numeral_term_admissible start) hHead
          have hCondition :
              ⊢ₘ[standard_sequence_semantics_theory]
                standard_sequence_pair_member_condition start (head :: tail) (numₘ(start)) head := by
            simp only [standard_sequence_pair_member_condition]
            apply FirstOrder.Derives.disjIntroLeft
              (right := standard_sequence_pair_member_condition
                (start + 1) tail (numₘ(start)) head)
            exact FirstOrder.Derives.conjIntro
              (FirstOrder.Derives.eq_refl_m
                (sort := SetSort.set) (numₘ(start)))
              (FirstOrder.Derives.eq_refl_m
                (sort := SetSort.set) head)
          simpa using FirstOrder.Derives.iffElimLeft hPairIff hCondition
      | succ index =>
          simp only [List.getElem?_cons_succ] at hGet
          have hTail :
              ∀ item, item ∈ tail →
                Term.Admissible item SetSort.set := by
            intro item hItem
            exact hElements item (by simp [hItem])
          have hTailGraph := ih (start + 1) hGet hTail
          let fullIndex := numₘ(start + Nat.succ index)
          have hTailGraph' :
              ⊢ₘ[standard_sequence_semantics_theory]
                ⟨fullIndex, element⟩ₘ ∈ₘ
                  standard_sequence_from (start + 1) tail := by
            simpa [fullIndex, Nat.succ_eq_add_one, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using hTailGraph
          have hTailIff := standard_sequence_from_pair_member_iff (start + 1) (elements := tail) fullIndex element
            hTail (finite_numeral_term_admissible (start + Nat.succ index))
            hElement
          have hTailCondition :=
            FirstOrder.Derives.iffElimRight hTailIff hTailGraph'
          have hFullIff := standard_sequence_from_pair_member_iff
            start (elements := head :: tail) fullIndex element
            hElements (finite_numeral_term_admissible (start + Nat.succ index))
            hElement
          have hFullCondition :
              ⊢ₘ[standard_sequence_semantics_theory]
                standard_sequence_pair_member_condition start (head :: tail)
                  fullIndex element := by
            simp only [standard_sequence_pair_member_condition]
            nd_apply FirstOrder.Derives.disjIntroRight
              (left :=
                (fullIndex ≐ₘ numₘ(start)) ∧ₘ
                  (element ≐ₘ head))
            exact hTailCondition
          simpa [fullIndex] using
            FirstOrder.Derives.iffElimLeft hFullIff hFullCondition
/--
若目标理论包含标准序列语义理论，且所有列表元素都属于目标集，则标准序列图中的
任意值在该目标理论中也属于目标集。
-/
theorem standard_sequence_from_graph_value_mem_of_theory
    {T : SetTheory} {Γ : Context signature} (hTheory :
      ∀ formula,
        standard_sequence_semantics_theory formula → T formula) (start : Nat) {elements : List SetTerm} (target index value : SetTerm)
    (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hTarget : Term.Admissible target SetSort.set) (hTargetMember : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ target) (hIndex : Term.Admissible index SetSort.set) (hValue : Term.Admissible value SetSort.set) :
    Γ ⊢ₘ[T] (⟨index, value⟩ₘ ∈ₘ standard_sequence_from start elements) ⟶ₘ (value ∈ₘ target) := by
  induction elements generalizing start with
  | nil =>
      have hPairIff :=
        FirstOrder.Derives.theory_weaken hTheory <|
          standard_sequence_from_pair_member_iff
            start (elements := []) index value (by simp) hIndex hValue
      let membership : SetFormula :=
        ⟨index, value⟩ₘ ∈ₘ standard_sequence_from start []
      nd_apply FirstOrder.Derives.impIntro
      let Δ : Context signature := membership :: Γ
      have hMember : Δ ⊢ₘ[T] membership :=
        .assumption (by simp [Δ])
      have hCondition := FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp [Δ]) hPairIff)
        (by simpa [membership] using hMember)
      exact FirstOrder.Derives.falsumElim
        (by simpa [standard_sequence_pair_member_condition] using hCondition)
  | cons head tail ih =>
      have hHead : Term.Admissible head SetSort.set :=
        hElements head (by simp)
      have hTail :
          ∀ element, element ∈ tail →
            Term.Admissible element SetSort.set := by
        intro element hElement
        exact hElements element (by simp [hElement])
      have hHeadMember := hTargetMember head (by simp)
      have hTailTargetMember :
          ∀ element, element ∈ tail →
            Γ ⊢ₘ[T] element ∈ₘ target := by
        intro element hElement
        exact hTargetMember element (by simp [hElement])
      have hTailImp := ih (start + 1) hTail hTailTargetMember
      have hFullIff :=
        FirstOrder.Derives.theory_weaken hTheory <|
          standard_sequence_from_pair_member_iff
            start (elements := head :: tail) index value
            hElements hIndex hValue
      have hTailIff :=
        FirstOrder.Derives.theory_weaken hTheory <|
          standard_sequence_from_pair_member_iff (start + 1) (elements := tail) index value
            hTail hIndex hValue
      let membership : SetFormula :=
        ⟨index, value⟩ₘ ∈ₘ
          standard_sequence_from start (head :: tail)
      let headCase : SetFormula := (index ≐ₘ numₘ(start)) ∧ₘ (value ≐ₘ head)
      let tailCase : SetFormula :=
        standard_sequence_pair_member_condition (start + 1) tail index value
      nd_apply FirstOrder.Derives.impIntro
      let Δ : Context signature := membership :: Γ
      have hMember : Δ ⊢ₘ[T] membership :=
        .assumption (by simp [Δ])
      have hCondition := FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp [Δ]) hFullIff)
        (by simpa [membership] using hMember)
      have hCases :
          Δ ⊢ₘ[T] headCase ∨ₘ tailCase := by
        simpa [headCase, tailCase,
          standard_sequence_pair_member_condition] using hCondition
      apply FirstOrder.Derives.disjElim hCases
      · let ΓHead : Context signature := headCase :: Δ
        have hHeadCase : ΓHead ⊢ₘ[T] headCase :=
          .assumption (by simp [ΓHead])
        have hValueHead :
            ΓHead ⊢ₘ[T] value ≐ₘ head :=
          FirstOrder.Derives.conjElimRight hHeadCase
        have hTransport := membership_left_iff_of_equality
          value head target hValue hHead hTarget hValueHead
        exact FirstOrder.Derives.iffElimLeft hTransport
          (FirstOrder.Derives.context_weaken
            (Γ := Γ) (Δ := ΓHead)
            (by
              intro formula hFormula
              simp [ΓHead, Δ, hFormula])
            hHeadMember)
      · let ΓTail : Context signature := tailCase :: Δ
        have hTailCase : ΓTail ⊢ₘ[T] tailCase :=
          .assumption (by simp [ΓTail])
        have hTailMember :
            ΓTail ⊢ₘ[T]
              ⟨index, value⟩ₘ ∈ₘ
                standard_sequence_from (start + 1) tail :=
          FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken (Γ := []) (Δ := ΓTail) (by simp [ΓTail]) hTailIff)
            (by simpa [tailCase] using hTailCase)
        exact FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := Γ) (Δ := ΓTail)
            (by
              intro formula hFormula
              simp [ΓTail, Δ, hFormula])
            hTailImp)
          hTailMember
private theorem stdseq_range_term_fresh (id : FreeVarId) (relation : SetTerm) (hRelationFresh : (SetSort.set, id) ∉ Term.freeSupport relation) :
    (SetSort.set, id) ∉ Term.freeSupport (ranₘ(relation)) := by
  intro hMember
  simp [Term.freeSupport, Term.freeSupportList] at hMember
  exact hRelationFresh hMember
/--
所有列表元素在任意标准语义扩张理论中属于目标集时，标准序列的值域包含于该目标集。
-/
theorem standard_sequence_from_range_subset_of_theory
    {T : SetTheory} (hTheory :
      ∀ formula,
        standard_sequence_semantics_theory formula → T formula) (hTheorySentence :
      ∀ formula, T formula → Formula.Sentence formula) (start : Nat) {elements : List SetTerm} (target : SetTerm) (hElements : ∀ element, element ∈ elements →
      Term.Admissible element SetSort.set) (hElementsClosed : ∀ element, element ∈ elements →
      Term.freeSupport element = []) (hTarget : Term.Admissible target SetSort.set) (hTargetClosed : Term.freeSupport target = [])
    (hTargetMember : ∀ element, element ∈ elements →
      ⊢ₘ[T] element ∈ₘ target) :
    ⊢ₘ[T]
      ranₘ(standard_sequence_from start elements) ⊆ₘ target := by
  let sequence := standard_sequence_from start elements
  let value := x#1
  have hSequence : Term.Admissible sequence SetSort.set :=
    seq_admissible_m start hElements
  have hRange : Term.Admissible (ranₘ(sequence)) SetSort.set :=
    range_term_admissible sequence hSequence
  have hElementsFresh (id : FreeVarId) :
      ∀ element, element ∈ elements → (SetSort.set, id) ∉ Term.freeSupport element := by
    intro element hElement
    rw [hElementsClosed element hElement]
    intro hMember
    cases hMember
  have hSequenceFresh (id : FreeVarId) : (SetSort.set, id) ∉ Term.freeSupport sequence :=
    standard_sequence_from_fresh_at id start (hElementsFresh id)
  have hTargetFresh (id : FreeVarId) : (SetSort.set, id) ∉ Term.freeSupport target := by
    rw [hTargetClosed]
    intro hMember
    cases hMember
  have hValueFreshZero : (SetSort.set, 0) ∉ Term.freeSupport value := by
    native_decide
  have hRangeToGraph :=
    FirstOrder.Derives.theory_weaken hTheory <|
      stdseq_range_to_graph_exists
        sequence value hSequence (set_variable_admissible 1) (hSequenceFresh 0) hValueFreshZero (standard_sequence_from_is_relation
          start hElements (hElementsFresh 0))
  have hGraphToTarget :=
    standard_sequence_from_graph_value_mem_of_theory
      hTheory start target (x#0) value hElements hTarget hTargetMember (set_variable_admissible 0) (set_variable_admissible 1)
  let base : SetFormula := ⟨bₛ#0, value⟩ₘ ∈ₘ sequence
  let pointGraph : SetFormula := ⟨x#0, value⟩ₘ ∈ₘ sequence
  let conclusion : SetFormula := value ∈ₘ target
  have hPointGraphImp :
      ⊢ₘ[T] pointGraph ⟶ₘ conclusion := by
    simpa [pointGraph, conclusion, value, sequence] using hGraphToTarget
  let hTheoryFresh : ∀ formula, T formula → (SetSort.set, 0) freshForₘ formula := by
    intro formula hFormula
    have hSentence := hTheorySentence formula hFormula
    rw [hSentence.2]
    intro hMember
    cases hMember
  have hConclusionFresh : (SetSort.set, 0) freshForₘ conclusion := by
    exact relation_formula_fresh value target hValueFreshZero (hTargetFresh 0)
  have hLift := Metatheory.Derives.exists_imp_of_imp (T := T) (Γ := []) (sort := SetSort.set) (eigen := 0)
    hTheoryFresh (by intro formula hFormula; simp at hFormula)
    hConclusionFresh hPointGraphImp
  have hPointOpen :
      Formula.openAt SetSort.set 0 (x#0) base = pointGraph := by
    have hValueOpen := Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#0) value (set_variable_admissible 1).2
    have hSequenceOpen := Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#0) sequence hSequence.2
    simp [base, pointGraph, Formula.openAt, Term.openAt,
      hValueOpen, hSequenceOpen]
  have hBaseFresh : (SetSort.set, 0) freshForₘ base := by
    have hBvarFresh : (SetSort.set, 0) ∉
        Term.freeSupport (bₛ#0) := by
      intro hMember
      cases hMember
    exact relation_formula_fresh (⟨bₛ#0, value⟩ₘ) sequence (ordered_pair_term_fresh (bₛ#0) value
        hBvarFresh hValueFreshZero) (hSequenceFresh 0)
  have hClose :
      Formula.closeFreeAt SetSort.set 0 0 pointGraph = base := by
    rw [← hPointOpen]
    exact Formula.closeFreeAt_openAt SetSort.set 0 0 base hBaseFresh
  have hExistsToTarget :
      ⊢ₘ[T] (∃ₘ[SetSort.set], base) ⟶ₘ conclusion := by
    simpa [base, conclusion, hClose] using hLift
  have hPoint :
      ⊢ₘ[T] (value ∈ₘ ranₘ(sequence)) ⟶ₘ conclusion := by
    let membership : SetFormula := value ∈ₘ ranₘ(sequence)
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature := [membership]
    have hMember : Γ ⊢ₘ[T] membership :=
      .assumption (by simp [Γ])
    have hExists := FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hRangeToGraph)
      (by simpa [membership] using hMember)
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hExistsToTarget) (by simpa [base] using hExists)
  have hClosed :
      ⊢ₘ[T]
        ∀ₘ[SetSort.set, 1], ((x#1 ∈ₘ ranₘ(sequence)) ⟶ₘ (x#1 ∈ₘ target)) := by
    have hTheoryFreshOne :
        ∀ formula, T formula → (SetSort.set, 1) ∉ Formula.freeSupport formula := by
      intro formula hFormula
      rw [(hTheorySentence formula hFormula).2]
      exact List.not_mem_nil
    simpa [value, conclusion] using (FirstOrder.Derives.forall_intro (T := T) (Γ := []) (sort := SetSort.set) (eigen := 1)
        hTheoryFreshOne (by simp) hPoint)
  have hRangeFreshOne : (SetSort.set, 1) ∉ Term.freeSupport (ranₘ(sequence)) :=
    stdseq_range_term_fresh 1 sequence (hSequenceFresh 1)
  have hRangeCloseOne :
      Term.closeFreeAt SetSort.set 1 0 (ranₘ(sequence)) =
        ranₘ(sequence) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 1 0 (ranₘ(sequence)) hRange.2 hRangeFreshOne
  have hTargetCloseOne :
      Term.closeFreeAt SetSort.set 1 0 target = target :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 1 0 target hTarget.2 (hTargetFresh 1)
  have hSubsetCondition :
      ⊢ₘ[T]
        subset_condition (ranₘ(sequence)) target := by
    simpa [subset_condition, Formula.closeFreeAt, Term.closeFreeAt,
      hRangeCloseOne, hTargetCloseOne] using hClosed
  have hDefinition :=
    FirstOrder.Derives.theory_weaken hTheory <|
      stdseq_weaken_subset (subset_definition_instance_derives_of_admissible (ranₘ(sequence)) target hRange hTarget)
  exact FirstOrder.Derives.iffElimLeft hDefinition hSubsetCondition

/--
上下文中的逐项成员证书可提升为标准序列的值域包含关系。

这里只要求编号 `0/1` 对元素、目标项和上下文新鲜；元素无需闭合。编号 `0`
用于展开值域成员的图见证，编号 `1` 用于封闭逐点子集条件。
-/
theorem standard_sequence_from_range_subset_of_theory_context
    {T : SetTheory} {Γ : Context signature}
    (hTheory :
      ∀ formula,
        standard_sequence_semantics_theory formula → T formula)
    (hTheorySentence :
      ∀ formula, T formula → Formula.Sentence formula)
    (start : Nat)
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
    (hTargetMember :
      ∀ element, element ∈ elements →
        Γ ⊢ₘ[T] element ∈ₘ target) :
    Γ ⊢ₘ[T]
      ranₘ(standard_sequence_from start elements) ⊆ₘ target := by
  let sequence := standard_sequence_from start elements
  let value := x#1
  have hSequence : Term.Admissible sequence SetSort.set :=
    seq_admissible_m start hElements
  have hRange : Term.Admissible (ranₘ(sequence)) SetSort.set :=
    range_term_admissible sequence hSequence
  have hSequenceFreshZero :
      (SetSort.set, 0) ∉ Term.freeSupport sequence :=
    standard_sequence_from_fresh_at
      0 start hElementsFreshZero
  have hSequenceFreshOne :
      (SetSort.set, 1) ∉ Term.freeSupport sequence :=
    standard_sequence_from_fresh_at
      1 start hElementsFreshOne
  have hValueFreshZero :
      (SetSort.set, 0) ∉ Term.freeSupport value := by
    native_decide
  have hRangeToGraph :=
    FirstOrder.Derives.theory_weaken hTheory <|
      stdseq_range_to_graph_exists
        sequence value hSequence
        (set_variable_admissible 1)
        hSequenceFreshZero hValueFreshZero
        (standard_sequence_from_is_relation
          start hElements hElementsFreshZero)
  have hGraphToTarget :=
    standard_sequence_from_graph_value_mem_of_theory
      hTheory start target (x#0) value
      hElements hTarget hTargetMember
      (set_variable_admissible 0)
      (set_variable_admissible 1)
  let base : SetFormula :=
    ⟨bₛ#0, value⟩ₘ ∈ₘ sequence
  let pointGraph : SetFormula :=
    ⟨x#0, value⟩ₘ ∈ₘ sequence
  let conclusion : SetFormula :=
    value ∈ₘ target
  have hPointGraphImp :
      Γ ⊢ₘ[T] pointGraph ⟶ₘ conclusion := by
    simpa [pointGraph, conclusion, value, sequence] using
      hGraphToTarget
  have hTheoryFreshZero :
      ∀ formula, T formula →
        (SetSort.set, 0) freshForₘ formula := by
    intro formula hFormula
    rw [(hTheorySentence formula hFormula).2]
    exact List.not_mem_nil
  have hConclusionFreshZero :
      (SetSort.set, 0) freshForₘ conclusion :=
    relation_formula_fresh
      value target hValueFreshZero hTargetFreshZero
  have hLift :=
    Metatheory.Derives.exists_imp_of_imp
      (T := T) (Γ := Γ)
      (sort := SetSort.set) (eigen := 0)
      hTheoryFreshZero hContextFreshZero
      hConclusionFreshZero hPointGraphImp
  have hPointOpen :
      Formula.openAt SetSort.set 0 (x#0) base =
        pointGraph := by
    have hValueOpen :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 (x#0) value
        (set_variable_admissible 1).2
    have hSequenceOpen :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 (x#0) sequence hSequence.2
    simp [base, pointGraph, Formula.openAt,
      Term.openAt, hValueOpen, hSequenceOpen]
  have hBaseFreshZero :
      (SetSort.set, 0) freshForₘ base := by
    have hBoundFresh :
        (SetSort.set, 0) ∉
          Term.freeSupport (bₛ#0) := by
      intro hMember
      cases hMember
    exact relation_formula_fresh
      (⟨bₛ#0, value⟩ₘ) sequence
      (ordered_pair_term_fresh
        (bₛ#0) value hBoundFresh hValueFreshZero)
      hSequenceFreshZero
  have hClose :
      Formula.closeFreeAt SetSort.set 0 0 pointGraph =
        base := by
    rw [← hPointOpen]
    exact Formula.closeFreeAt_openAt
      SetSort.set 0 0 base hBaseFreshZero
  have hExistsToTarget :
      Γ ⊢ₘ[T]
        (∃ₘ[SetSort.set], base) ⟶ₘ conclusion := by
    simpa [base, conclusion, hClose] using hLift
  have hPoint :
      Γ ⊢ₘ[T]
        (value ∈ₘ ranₘ(sequence)) ⟶ₘ conclusion := by
    let membership : SetFormula :=
      value ∈ₘ ranₘ(sequence)
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature := membership :: Γ
    have hMember : Δ ⊢ₘ[T] membership :=
      .assumption (by simp [Δ])
    have hExists :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ])
          hRangeToGraph)
        (by simpa [membership] using hMember)
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := Γ) (Δ := Δ)
        (by
          intro formula hFormula
          simp [Δ, hFormula])
        hExistsToTarget)
      (by simpa [base] using hExists)
  have hClosed :
      Γ ⊢ₘ[T]
        ∀ₘ[SetSort.set, 1],
          ((x#1 ∈ₘ ranₘ(sequence)) ⟶ₘ
            (x#1 ∈ₘ target)) := by
    have hTheoryFreshOne :
        ∀ formula, T formula →
          (SetSort.set, 1) ∉
            Formula.freeSupport formula := by
      intro formula hFormula
      rw [(hTheorySentence formula hFormula).2]
      exact List.not_mem_nil
    simpa [value, conclusion] using
      FirstOrder.Derives.forall_intro
        (T := T) (Γ := Γ)
        (sort := SetSort.set) (eigen := 1)
        hTheoryFreshOne hContextFreshOne hPoint
  have hRangeFreshOne :
      (SetSort.set, 1) ∉
        Term.freeSupport (ranₘ(sequence)) :=
    stdseq_range_term_fresh
      1 sequence hSequenceFreshOne
  have hRangeCloseOne :
      Term.closeFreeAt SetSort.set 1 0
          (ranₘ(sequence)) =
        ranₘ(sequence) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 1 0 (ranₘ(sequence))
      hRange.2 hRangeFreshOne
  have hTargetCloseOne :
      Term.closeFreeAt SetSort.set 1 0 target =
        target :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 1 0 target hTarget.2
      hTargetFreshOne
  have hSubsetCondition :
      Γ ⊢ₘ[T]
        subset_condition (ranₘ(sequence)) target := by
    simpa [subset_condition, Formula.closeFreeAt,
      Term.closeFreeAt, hRangeCloseOne,
      hTargetCloseOne] using hClosed
  have hDefinition :
      Γ ⊢ₘ[T]
        (ranₘ(sequence) ⊆ₘ target) ↔ₘ
          subset_condition (ranₘ(sequence)) target :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <|
          stdseq_weaken_subset <|
            subset_definition_instance_derives_of_admissible
              (ranₘ(sequence)) target hRange hTarget
  exact FirstOrder.Derives.iffElimLeft
    hDefinition hSubsetCondition
end YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation
