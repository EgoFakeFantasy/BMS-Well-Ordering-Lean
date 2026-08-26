import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.CartesianProduct
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Relation
/-!
# 关系的平面性质
本模块承接关系谓词、双重并集、笛卡尔积与有序对反转的组合定理。文献中的
`GX`、`YXD` 与 `rng` 仅在注释中作为索引；公共接口统一使用
`is_relation`、`is_ordered_pair` 与 `range`。
定义层继续保持最小理论，本模块才组合后续平面论证真正需要的公理。这样定义域、
值域和笛卡尔积可以独立复用，而关系的平方界与反转对称性共享同一个显式理论边界。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 统一理论边界 -/
/-- 关系平面定理所需的最小显式组合理论。 -/
def relation_plane_theory : SetTheory :=
  Theory.union
    relation_range_operator_theory (Theory.union
      cartesian_product_operator_theory
      ordered_pair_reverse_operator_theory)
/-- 关系值域函数符号理论嵌入关系平面理论。 -/
theorem relation_range_operator_theory_subset_relation_plane_theory
    {formula : SetFormula} (hFormula :
      relation_range_operator_theory formula) :
    relation_plane_theory formula :=
  Or.inl hFormula
/-- 笛卡尔积函数符号理论嵌入关系平面理论。 -/
theorem cartesian_product_operator_theory_subset_relation_plane_theory
    {formula : SetFormula} (hFormula :
      cartesian_product_operator_theory formula) :
    relation_plane_theory formula :=
  Or.inr (Or.inl hFormula)
/-- 有序对反转函数符号理论嵌入关系平面理论。 -/
theorem ordered_pair_reverse_operator_theory_subset_relation_plane_theory
    {formula : SetFormula} (hFormula :
      ordered_pair_reverse_operator_theory formula) :
    relation_plane_theory formula :=
  Or.inr (Or.inr hFormula)
/-- 关系谓词理论嵌入关系平面理论。 -/
theorem relation_predicate_theory_subset_relation_plane_theory
    {formula : SetFormula} (hFormula : relation_predicate_theory formula) :
    relation_plane_theory formula :=
  relation_range_operator_theory_subset_relation_plane_theory (relation_range_theory_subset_relation_range_operator_theory
      (relation_domain_operator_theory_subset_relation_range_theory (relation_domain_theory_subset_relation_domain_operator_theory
          (relation_predicate_theory_subset_relation_domain_theory
            hFormula))))
/-- 关系与函数基础理论嵌入关系平面理论。 -/
theorem relation_function_theory_subset_relation_plane_theory
    {formula : SetFormula} (hFormula : relation_function_theory formula) :
    relation_plane_theory formula :=
  relation_predicate_theory_subset_relation_plane_theory (relation_base_theory_subset_relation_predicate_theory
      (relation_function_theory_subset_relation_base_theory
        hFormula))
/-- 一元并集函数符号理论嵌入关系平面理论。 -/
theorem union_operator_theory_subset_relation_plane_theory
    {formula : SetFormula} (hFormula : union_operator_theory formula) :
    relation_plane_theory formula :=
  relation_range_operator_theory_subset_relation_plane_theory (relation_range_theory_subset_relation_range_operator_theory
      (relation_base_theory_subset_relation_range_theory (union_operator_theory_subset_relation_base_theory
          hFormula)))
/-- 右投影函数符号理论嵌入关系平面理论。 -/
theorem right_projection_operator_theory_subset_relation_plane_theory
    {formula : SetFormula} (hFormula :
      right_projection_operator_theory formula) :
    relation_plane_theory formula :=
  relation_range_operator_theory_subset_relation_plane_theory (relation_range_theory_subset_relation_range_operator_theory
      (relation_base_theory_subset_relation_range_theory (right_projection_operator_theory_subset_relation_base_theory
          hFormula)))
/-- 子集定义理论嵌入关系平面理论。 -/
theorem subset_theory_subset_relation_plane_theory
    {formula : SetFormula} (hFormula : subset_theory formula) :
    relation_plane_theory formula :=
  cartesian_product_operator_theory_subset_relation_plane_theory (cartesian_product_base_theory_subset_cartesian_product_operator_theory
      (power_set_operator_theory_subset_cartesian_product_base_theory (Or.inr (Or.inr hFormula))))
/-- 二元并函数符号理论嵌入关系平面理论。 -/
theorem binary_union_operator_theory_subset_relation_plane_theory
    {formula : SetFormula} (hFormula : binary_union_operator_theory formula) :
    relation_plane_theory formula :=
  cartesian_product_operator_theory_subset_relation_plane_theory (cartesian_product_base_theory_subset_cartesian_product_operator_theory
      (binary_union_operator_theory_subset_cartesian_product_base_theory
        hFormula))
/-- 幂集函数符号理论嵌入关系平面理论。 -/
theorem power_set_operator_theory_subset_relation_plane_theory
    {formula : SetFormula} (hFormula : power_set_operator_theory formula) :
    relation_plane_theory formula :=
  cartesian_product_operator_theory_subset_relation_plane_theory (cartesian_product_base_theory_subset_cartesian_product_operator_theory
      (power_set_operator_theory_subset_cartesian_product_base_theory
        hFormula))
/-- 有序对函数符号理论嵌入关系平面理论。 -/
theorem ordered_pair_operator_theory_subset_relation_plane_theory
    {formula : SetFormula} (hFormula : ordered_pair_operator_theory formula) :
    relation_plane_theory formula :=
  cartesian_product_operator_theory_subset_relation_plane_theory (cartesian_product_base_theory_subset_cartesian_product_operator_theory
      (ordered_pair_operator_theory_subset_cartesian_product_base_theory
        hFormula))
/-- 配对函数符号理论嵌入关系平面理论。 -/
theorem pairing_operator_theory_subset_relation_plane_theory
    {formula : SetFormula} (hFormula : pairing_operator_theory formula) :
    relation_plane_theory formula :=
  ordered_pair_operator_theory_subset_relation_plane_theory (singleton_operator_theory_subset_ordered_pair_operator_theory (Or.inr hFormula))
/-- 关系平面理论满足公共良构性边界。 -/
theorem relation_plane_theory_admissible :
    Theory.Admissible relation_plane_theory := by
  intro formula hFormula
  rcases hFormula with hFormula | hFormula
  · exact relation_range_operator_theory_admissible
      formula hFormula
  · rcases hFormula with hFormula | hFormula
    · exact cartesian_product_operator_theory_admissible
        formula hFormula
    · exact ordered_pair_reverse_operator_theory_admissible
        formula hFormula
/-- 关系平面理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem relation_plane_theory_sentence
    {formula : SetFormula} (hFormula : relation_plane_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with hFormula | hFormula
  · exact relation_range_operator_theory_sentence hFormula
  · rcases hFormula with hFormula | hFormula
    · exact cartesian_product_operator_theory_sentence hFormula
    · exact ordered_pair_reverse_operator_theory_sentence hFormula
/-! ## 并集与子集的通用合同 -/
/-- 集合族成员到其并集的子集成员条件。 -/
theorem member_implies_subset_condition_union (source member : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hMember : Term.Admissible member SetSort.set) :
    ⊢ₘ[union_operator_theory] (member ∈ₘ source) ⟶ₘ
        subset_condition member (⋃ₘ source) := by
  let member_mem : SetFormula :=
    member ∈ₘ source
  let subset_body : SetFormula := (bₛ#0 ∈ₘ member) ⟶ₘ (bₛ#0 ∈ₘ ⋃ₘ source)
  let element :=
    FreshVariable.fresh_id SetSort.set
      [member_mem, subset_body]
  have hElementFreshMember : (SetSort.set, element) freshForₘ
        member_mem := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshSubset : (SetSort.set, element) freshForₘ
        subset_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hSourceOpenOne :
      Term.openAt SetSort.set 1 (x#element) source =
        source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 (x#element) source hSource.2
  have hUnionOpenZero :
      Term.openAt SetSort.set 0 (x#element) (⋃ₘ source) =
        ⋃ₘ source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) (⋃ₘ source) (union_term_admissible source hSource).2
  have hMemberOpenZero :
      Term.openAt SetSort.set 0 (x#element) member =
        member :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) member hMember.2
  have hSourceOpenZero :
      Term.openAt SetSort.set 0 (x#element) source =
        source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) source hSource.2
  change
    ⊢ₘ[union_operator_theory]
      member_mem ⟶ₘ (∀ₘ[SetSort.set], subset_body)
  nd_apply FirstOrder.Derives.impIntro
  have hUnionSpec :
      [member_mem] ⊢ₘ[union_operator_theory]
        union_spec source (⋃ₘ source) :=
    FirstOrder.Derives.context_weaken_cons (union_term_spec_derives source hSource)
  have hUnionAtRaw :=
    FirstOrder.Derives.forall_elim (term := x#element) hUnionSpec
  have hUnionAt :
      [member_mem] ⊢ₘ[union_operator_theory] (x#element ∈ₘ ⋃ₘ source) ↔ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ source) ∧ₘ (x#element ∈ₘ bₛ#0)) := by
    simpa [union_spec, Formula.openAt,
      Formula.next_depth, Term.openAt,
      hSourceOpenOne, hUnionOpenZero] using
      hUnionAtRaw
  have hSubsetAt :
      [member_mem] ⊢ₘ[union_operator_theory] (x#element ∈ₘ member) ⟶ₘ (x#element ∈ₘ ⋃ₘ source) := by
    nd_apply FirstOrder.Derives.impIntro
    have hExists : (x#element ∈ₘ member) :: [member_mem]
          ⊢ₘ[union_operator_theory]
            ∃ₘ[SetSort.set], (bₛ#0 ∈ₘ source) ∧ₘ (x#element ∈ₘ bₛ#0) := by
      nd_apply FirstOrder.Derives.exists_intro (term := member)
      have hSourceOpen :
          Term.openAt SetSort.set 0 member source =
            source :=
        Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 member source hSource.2
      simpa [Formula.openAt, Term.openAt,
        hSourceOpen] using (FirstOrder.Derives.conjIntro (show (x#element ∈ₘ member) :: [member_mem]
              ⊢ₘ[union_operator_theory]
                member_mem from
            .assumption (by simp)) (show (x#element ∈ₘ member) :: [member_mem]
              ⊢ₘ[union_operator_theory]
                x#element ∈ₘ member from
            .assumption (by simp)))
    exact FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken_cons
        hUnionAt)
      hExists
  have hSubsetAtOpened :
      [member_mem] ⊢ₘ[union_operator_theory]
        Formula.openAt SetSort.set 0 (x#element) subset_body := by
    simpa [subset_body, Formula.openAt,
      Term.openAt, hMemberOpenZero,
      hSourceOpenZero] using hSubsetAt
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := union_operator_theory) (Γ := [member_mem]) (sort := SetSort.set) (eigen := element) (body :=
        Formula.openAt SetSort.set 0 (x#element) subset_body) (by
        intro formula hFormula
        have hSentence :=
          union_operator_theory_sentence hFormula
        rw [hSentence.2]
        simp) (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        exact hElementFreshMember)
      hSubsetAtOpened
  simpa [subset_condition,
    Formula.closeFreeAt_openAt
      SetSort.set element 0 subset_body
      hElementFreshSubset] using hGeneralized
/-- 文献引理 2.7(1)：集合族的任一成员都包含于该集合族的并集。 -/
theorem member_subset_union (source member : SetTerm) (hSource : Term.Admissible source SetSort.set) (hMember : Term.Admissible member SetSort.set) :
    ⊢ₘ[relation_plane_theory] (member ∈ₘ source) ⟶ₘ (member ⊆ₘ ⋃ₘ source) := by
  nd_apply FirstOrder.Derives.impIntro
  let member_mem : SetFormula :=
    member ∈ₘ source
  have hConditionImp :
      [member_mem] ⊢ₘ[relation_plane_theory]
        member_mem ⟶ₘ
          subset_condition member (⋃ₘ source) :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          union_operator_theory_subset_relation_plane_theory
            hFormula) (member_implies_subset_condition_union
          source member hSource hMember)
  have hCondition :
      [member_mem] ⊢ₘ[relation_plane_theory]
        subset_condition member (⋃ₘ source) :=
    FirstOrder.Derives.impElim
      hConditionImp (.assumption (by simp))
  have hDefinition :
      [member_mem] ⊢ₘ[relation_plane_theory]
        subset_definition_instance
          member (⋃ₘ source) :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          subset_theory_subset_relation_plane_theory
            hFormula) (subset_definition_instance_derives_of_admissible
          member (⋃ₘ source)
          hMember (union_term_admissible source hSource))
  exact FirstOrder.Derives.iffElimLeft
    hDefinition hCondition
/-- 文献引理 2.7(2)：一元并集关于子集关系单调。 -/
theorem subset_implies_union_subset_condition (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[relation_plane_theory] (left ⊆ₘ right) ⟶ₘ
        subset_condition (⋃ₘ left) (⋃ₘ right) := by
  let subset_formula : SetFormula :=
    left ⊆ₘ right
  let subset_body : SetFormula := (bₛ#0 ∈ₘ ⋃ₘ left) ⟶ₘ (bₛ#0 ∈ₘ ⋃ₘ right)
  let element :=
    FreshVariable.fresh_id SetSort.set
      [subset_formula, subset_body]
  let left_witness_body : SetFormula := (bₛ#0 ∈ₘ left) ∧ₘ (x#element ∈ₘ bₛ#0)
  let conclusion : SetFormula :=
    x#element ∈ₘ ⋃ₘ right
  let witness :=
    FreshVariable.fresh_id SetSort.set
      [subset_formula, subset_body,
        left_witness_body, conclusion,
        x#element ∈ₘ ⋃ₘ left]
  let witness_point :=
    Formula.openAt SetSort.set 0 (x#witness) left_witness_body
  have hElementFreshSubsetFormula : (SetSort.set, element) freshForₘ
        subset_formula := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshSubsetBody : (SetSort.set, element) freshForₘ
        subset_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hWitnessFreshSubsetFormula : (SetSort.set, witness) freshForₘ
        subset_formula := by
    dsimp [witness]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hWitnessFreshLeftMembership : (SetSort.set, witness) freshForₘ (x#element ∈ₘ ⋃ₘ left) := by
    dsimp [witness]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hWitnessFreshBody : (SetSort.set, witness) freshForₘ
        left_witness_body := by
    dsimp [witness]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hWitnessFreshConclusion : (SetSort.set, witness) freshForₘ
        conclusion := by
    dsimp [witness]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hLeftOpenOne :
      Term.openAt SetSort.set 1 (x#element) left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 (x#element) left hLeft.2
  have hRightOpenOne :
      Term.openAt SetSort.set 1 (x#element) right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 (x#element) right hRight.2
  have hLeftUnionOpenZero :
      Term.openAt SetSort.set 0 (x#element) (⋃ₘ left) =
        ⋃ₘ left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) (⋃ₘ left) (union_term_admissible left hLeft).2
  have hRightUnionOpenZero :
      Term.openAt SetSort.set 0 (x#element) (⋃ₘ right) =
        ⋃ₘ right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) (⋃ₘ right) (union_term_admissible right hRight).2
  change
    ⊢ₘ[relation_plane_theory]
      subset_formula ⟶ₘ (∀ₘ[SetSort.set], subset_body)
  nd_apply FirstOrder.Derives.impIntro
  have hSubsetDefinition :
      [subset_formula] ⊢ₘ[relation_plane_theory]
        subset_definition_instance left right :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          subset_theory_subset_relation_plane_theory
            hFormula) (subset_definition_instance_derives_of_admissible
          left right hLeft hRight)
  have hSubsetCondition :
      [subset_formula] ⊢ₘ[relation_plane_theory]
        subset_condition left right :=
    FirstOrder.Derives.iffElimRight
      hSubsetDefinition (by
        simpa [subset_formula] using (show
            [subset_formula] ⊢ₘ[relation_plane_theory]
              subset_formula from
            .assumption (by simp)))
  have hLeftSpec :
      [subset_formula] ⊢ₘ[relation_plane_theory]
        union_spec left (⋃ₘ left) :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          union_operator_theory_subset_relation_plane_theory
            hFormula) (union_term_spec_derives left hLeft)
  have hRightSpec :
      [subset_formula] ⊢ₘ[relation_plane_theory]
        union_spec right (⋃ₘ right) :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          union_operator_theory_subset_relation_plane_theory
            hFormula) (union_term_spec_derives right hRight)
  have hLeftAtRaw :=
    FirstOrder.Derives.forall_elim (term := x#element) hLeftSpec
  have hRightAtRaw :=
    FirstOrder.Derives.forall_elim (term := x#element) hRightSpec
  have hLeftAt :
      [subset_formula] ⊢ₘ[relation_plane_theory] (x#element ∈ₘ ⋃ₘ left) ↔ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ left) ∧ₘ (x#element ∈ₘ bₛ#0)) := by
    simpa [union_spec, Formula.openAt,
      Formula.next_depth, Term.openAt,
      hLeftOpenOne, hLeftUnionOpenZero] using
      hLeftAtRaw
  have hRightAt :
      [subset_formula] ⊢ₘ[relation_plane_theory] (x#element ∈ₘ ⋃ₘ right) ↔ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ right) ∧ₘ (x#element ∈ₘ bₛ#0)) := by
    simpa [union_spec, Formula.openAt,
      Formula.next_depth, Term.openAt,
      hRightOpenOne, hRightUnionOpenZero] using
      hRightAtRaw
  have hSubsetAt :
      [subset_formula] ⊢ₘ[relation_plane_theory] (x#element ∈ₘ ⋃ₘ left) ⟶ₘ
          conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature := (x#element ∈ₘ ⋃ₘ left) :: [subset_formula]
    have hLeftAtInContext :
        Γ ⊢ₘ[relation_plane_theory] (x#element ∈ₘ ⋃ₘ left) ↔ₘ (∃ₘ[SetSort.set],
              left_witness_body) := by
      simpa [Γ, left_witness_body] using
        FirstOrder.Derives.context_weaken_cons hLeftAt
    have hExists :
        Γ ⊢ₘ[relation_plane_theory]
          ∃ₘ[SetSort.set],
            left_witness_body :=
      FirstOrder.Derives.iffElimRight
        hLeftAtInContext (.assumption (by simp [Γ]))
    have hWitnessPointAdmissible :
        Formula.Admissible witness_point := by
      have hOpened :=
        Formula.Admissible.exists_openAt (σ := signature) (body := left_witness_body) (term := x#witness)
          SetSort.set
          hExists.admissible (set_variable_admissible witness)
      simpa [witness_point] using hOpened
    have hExistsClosed :
        Γ ⊢ₘ[relation_plane_theory]
          ∃ₘ[SetSort.set],
            Formula.closeFreeAt
              SetSort.set witness 0 witness_point := by
      have hCloseOpen :
          Formula.closeFreeAt
              SetSort.set witness 0 witness_point =
            left_witness_body := by
        dsimp [witness_point]
        exact Formula.closeFreeAt_openAt
          SetSort.set witness 0
          left_witness_body hWitnessFreshBody
      simpa [hCloseOpen] using hExists
    have hCase :
        witness_point :: Γ
          ⊢ₘ[relation_plane_theory]
            conclusion := by
      have hLeftOpenWitness :
          Term.openAt SetSort.set 0 (x#witness) left =
            left :=
        Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 (x#witness) left hLeft.2
      have hWitnessConjunction :
          witness_point :: Γ
            ⊢ₘ[relation_plane_theory] ((x#witness ∈ₘ left) ∧ₘ (x#element ∈ₘ x#witness)) := by
        simpa [witness_point,
          left_witness_body,
          Formula.openAt, Term.openAt,
          hLeftOpenWitness] using (show
            witness_point :: Γ
              ⊢ₘ[relation_plane_theory]
                witness_point from
            .assumption (by simp))
      have hSubsetConditionInCase :
          witness_point :: Γ
            ⊢ₘ[relation_plane_theory]
              subset_condition left right :=
        FirstOrder.Derives.context_weaken_cons (assumption := witness_point) <|
          FirstOrder.Derives.context_weaken_cons (assumption :=
              x#element ∈ₘ ⋃ₘ left)
            hSubsetCondition
      have hSubsetAtWitnessRaw :=
        FirstOrder.Derives.forall_elim
          (term := x#witness) hSubsetConditionInCase
      have hRightOpenWitness :
          Term.openAt SetSort.set 0 (x#witness) right =
            right :=
        Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 (x#witness) right hRight.2
      have hSubsetAtWitness :
          witness_point :: Γ
            ⊢ₘ[relation_plane_theory] (x#witness ∈ₘ left) ⟶ₘ (x#witness ∈ₘ right) := by
        simpa [subset_condition,
          Formula.openAt, Term.openAt,
          hLeftOpenWitness,
          hRightOpenWitness] using
          hSubsetAtWitnessRaw
      have hWitnessInRight :
          witness_point :: Γ
            ⊢ₘ[relation_plane_theory]
              x#witness ∈ₘ right :=
        FirstOrder.Derives.impElim
          hSubsetAtWitness (FirstOrder.Derives.conjElimLeft
            hWitnessConjunction)
      have hRightExists :
          witness_point :: Γ
            ⊢ₘ[relation_plane_theory]
              ∃ₘ[SetSort.set], (bₛ#0 ∈ₘ right) ∧ₘ (x#element ∈ₘ bₛ#0) := by
        nd_apply FirstOrder.Derives.exists_intro
          (term := x#witness)
        simpa [Formula.openAt, Term.openAt,
          hRightOpenWitness] using (FirstOrder.Derives.conjIntro
            hWitnessInRight (FirstOrder.Derives.conjElimRight
              hWitnessConjunction))
      exact FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons
            hRightAt)
        hRightExists
    exact FirstOrder.Derives.exists_elim (by
        intro formula hFormula
        have hSentence :=
          relation_plane_theory_sentence hFormula
        rw [hSentence.2]
        simp) (by
        intro formula hFormula
        rcases List.mem_cons.mp hFormula with rfl | hFormula
        · exact hWitnessFreshLeftMembership
        · rcases List.mem_singleton.mp hFormula with rfl
          exact hWitnessFreshSubsetFormula)
      hWitnessFreshConclusion
      hExistsClosed hCase
  have hSubsetAtOpened :
      [subset_formula] ⊢ₘ[relation_plane_theory]
        Formula.openAt SetSort.set 0 (x#element) subset_body := by
    simpa [subset_body, conclusion,
      Formula.openAt, Term.openAt,
      hLeftUnionOpenZero,
      hRightUnionOpenZero] using hSubsetAt
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := relation_plane_theory) (Γ := [subset_formula]) (sort := SetSort.set) (eigen := element) (body :=
        Formula.openAt SetSort.set 0 (x#element) subset_body) (by
        intro formula hFormula
        have hSentence :=
          relation_plane_theory_sentence hFormula
        rw [hSentence.2]
        simp) (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        exact hElementFreshSubsetFormula)
      hSubsetAtOpened
  simpa [subset_condition,
    Formula.closeFreeAt_openAt
      SetSort.set element 0 subset_body
      hElementFreshSubsetBody] using hGeneralized
/-- 文献引理 2.7(2)：一元并集关于子集关系单调。 -/
theorem union_mono (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[relation_plane_theory] (left ⊆ₘ right) ⟶ₘ (⋃ₘ left ⊆ₘ ⋃ₘ right) := by
  nd_apply FirstOrder.Derives.impIntro
  let subset_formula : SetFormula :=
    left ⊆ₘ right
  have hConditionImp :
      [subset_formula] ⊢ₘ[relation_plane_theory]
        subset_formula ⟶ₘ
          subset_condition (⋃ₘ left) (⋃ₘ right) :=
    FirstOrder.Derives.context_weaken_cons (subset_implies_union_subset_condition
        left right hLeft hRight)
  have hCondition :
      [subset_formula] ⊢ₘ[relation_plane_theory]
        subset_condition (⋃ₘ left) (⋃ₘ right) :=
    FirstOrder.Derives.impElim
      hConditionImp (.assumption (by simp))
  have hDefinition :
      [subset_formula] ⊢ₘ[relation_plane_theory]
        subset_definition_instance (⋃ₘ left) (⋃ₘ right) :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          subset_theory_subset_relation_plane_theory
            hFormula) (subset_definition_instance_derives_of_admissible (⋃ₘ left) (⋃ₘ right) (union_term_admissible left hLeft)
          (union_term_admissible right hRight))
  exact FirstOrder.Derives.iffElimLeft
    hDefinition hCondition
/-- 两层成员关系可折叠为一元并集成员关系。 -/
theorem mem_union_of_mem_of_mem (source container element : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hContainer : Term.Admissible container SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[relation_plane_theory] (container ∈ₘ source) ⟶ₘ (element ∈ₘ container) ⟶ₘ (element ∈ₘ ⋃ₘ source) := by
  have hSpec :
      ⊢ₘ[relation_plane_theory]
        union_spec source (⋃ₘ source) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        union_operator_theory_subset_relation_plane_theory
          hFormula) (union_term_spec_derives source hSource)
  have hAtRaw :=
    FirstOrder.Derives.forall_elim (term := element) hSpec
  have hSourceOpen :
      Term.openAt SetSort.set 1 element source =
        source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 element source hSource.2
  have hUnionOpen :
      Term.openAt SetSort.set 0
          element (⋃ₘ source) =
        ⋃ₘ source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element (⋃ₘ source) (union_term_admissible source hSource).2
  have hAt :
      ⊢ₘ[relation_plane_theory] (element ∈ₘ ⋃ₘ source) ↔ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ source) ∧ₘ (element ∈ₘ bₛ#0)) := by
    simpa [union_spec, Formula.openAt,
      Formula.next_depth, Term.openAt,
      hSourceOpen, hUnionOpen] using hAtRaw
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hExists :
      [element ∈ₘ container,
          container ∈ₘ source]
        ⊢ₘ[relation_plane_theory]
          ∃ₘ[SetSort.set], (bₛ#0 ∈ₘ source) ∧ₘ (element ∈ₘ bₛ#0) := by
    nd_apply FirstOrder.Derives.exists_intro (term := container)
    have hSourceOpenContainer :
        Term.openAt SetSort.set 0
            container source =
          source :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 container source hSource.2
    have hElementOpenContainer :
        Term.openAt SetSort.set 0
            container element =
          element :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 container element hElement.2
    simpa [Formula.openAt, Term.openAt,
      hSourceOpenContainer,
      hElementOpenContainer] using (FirstOrder.Derives.conjIntro (show
          [element ∈ₘ container,
              container ∈ₘ source]
            ⊢ₘ[relation_plane_theory]
              container ∈ₘ source from
          .assumption (by simp)) (show
          [element ∈ₘ container,
              container ∈ₘ source]
            ⊢ₘ[relation_plane_theory]
              element ∈ₘ container from
          .assumption (by simp)))
  exact FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.context_weaken_cons hAt)
    hExists
/-! ## 二元并的成员注入 -/
/-- 左侧成员可注入二元并。 -/
theorem mem_binary_union_left (left right element : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[relation_plane_theory] (element ∈ₘ left) ⟶ₘ (element ∈ₘ (left ∪ₘ right)) := by
  have hSpec :
      ⊢ₘ[relation_plane_theory]
        binary_union_spec
          left right (left ∪ₘ right) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        binary_union_operator_theory_subset_relation_plane_theory
          hFormula) (binary_union_term_spec_derives
        left right hLeft hRight)
  have hAtRaw :=
    FirstOrder.Derives.forall_elim (term := element) hSpec
  have hLeftOpen :
      Term.openAt SetSort.set 0 element left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element left hLeft.2
  have hRightOpen :
      Term.openAt SetSort.set 0 element right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element right hRight.2
  have hUnionOpen :
      Term.openAt SetSort.set 0
          element (left ∪ₘ right) =
        left ∪ₘ right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element (left ∪ₘ right) (binary_union_term_admissible
        left right hLeft hRight).2
  have hAt :
      ⊢ₘ[relation_plane_theory] (element ∈ₘ (left ∪ₘ right)) ↔ₘ ((element ∈ₘ left) ∨ₘ (element ∈ₘ right)) := by
    simpa [binary_union_spec,
      Formula.openAt, Term.openAt,
      hLeftOpen, hRightOpen,
      hUnionOpen] using hAtRaw
  nd_apply FirstOrder.Derives.impIntro
  exact FirstOrder.Derives.iffElimLeft
    (FirstOrder.Derives.context_weaken_cons hAt)
    (FirstOrder.Derives.disjIntroLeft (show
        [element ∈ₘ left] ⊢ₘ[relation_plane_theory]
          element ∈ₘ left from
        .assumption (by simp)))
/-- 右侧成员可注入二元并。 -/
theorem mem_binary_union_right (left right element : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[relation_plane_theory] (element ∈ₘ right) ⟶ₘ (element ∈ₘ (left ∪ₘ right)) := by
  have hSpec :
      ⊢ₘ[relation_plane_theory]
        binary_union_spec
          left right (left ∪ₘ right) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        binary_union_operator_theory_subset_relation_plane_theory
          hFormula) (binary_union_term_spec_derives
        left right hLeft hRight)
  have hAtRaw :=
    FirstOrder.Derives.forall_elim (term := element) hSpec
  have hLeftOpen :
      Term.openAt SetSort.set 0 element left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element left hLeft.2
  have hRightOpen :
      Term.openAt SetSort.set 0 element right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element right hRight.2
  have hUnionOpen :
      Term.openAt SetSort.set 0
          element (left ∪ₘ right) =
        left ∪ₘ right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element (left ∪ₘ right) (binary_union_term_admissible
        left right hLeft hRight).2
  have hAt :
      ⊢ₘ[relation_plane_theory] (element ∈ₘ (left ∪ₘ right)) ↔ₘ ((element ∈ₘ left) ∨ₘ (element ∈ₘ right)) := by
    simpa [binary_union_spec,
      Formula.openAt, Term.openAt,
      hLeftOpen, hRightOpen,
      hUnionOpen] using hAtRaw
  nd_apply FirstOrder.Derives.impIntro
  exact FirstOrder.Derives.iffElimLeft
    (FirstOrder.Derives.context_weaken_cons hAt)
    (FirstOrder.Derives.disjIntroRight (show
        [element ∈ₘ right] ⊢ₘ[relation_plane_theory]
          element ∈ₘ right from
        .assumption (by simp)))
/--
若左集合包含于右集合，则二元并吸收到右集合。
证明只展开一次子集定义和二元并成员规格，再由外延性收束为等式。
-/
theorem binary_union_term_eq_right_of_subset (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[relation_plane_theory] (left ⊆ₘ right) ⟶ₘ ((left ∪ₘ right) ≐ₘ right) := by
  let subset_formula : SetFormula := left ⊆ₘ right
  let union := left ∪ₘ right
  let agreement_body : SetFormula := (bₛ#0 ∈ₘ union) ↔ₘ (bₛ#0 ∈ₘ right)
  let element :=
    FreshVariable.fresh_id SetSort.set
      [subset_formula, agreement_body]
  let Γ : Context signature := [subset_formula]
  have hUnion :
      Term.Admissible union SetSort.set :=
    binary_union_term_admissible
      left right hLeft hRight
  have hElementFreshSubset : (SetSort.set, element) freshForₘ
        subset_formula := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshAgreement : (SetSort.set, element) freshForₘ
        agreement_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hLeftOpen :
      Term.openAt SetSort.set 0 (x#element) left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) left hLeft.2
  have hRightOpen :
      Term.openAt SetSort.set 0 (x#element) right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) right hRight.2
  have hUnionOpen :
      Term.openAt SetSort.set 0 (x#element) union =
        union :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) union hUnion.2
  nd_apply FirstOrder.Derives.impIntro
  have hSubsetDefinition :
      Γ ⊢ₘ[relation_plane_theory]
        subset_definition_instance left right :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          subset_theory_subset_relation_plane_theory
            hFormula) (subset_definition_instance_derives_of_admissible
          left right hLeft hRight)
  have hSubsetCondition :
      Γ ⊢ₘ[relation_plane_theory]
        subset_condition left right :=
    FirstOrder.Derives.iffElimRight
      hSubsetDefinition (show
        Γ ⊢ₘ[relation_plane_theory]
          left ⊆ₘ right from
        .assumption (by simp [Γ, subset_formula]))
  have hSubsetAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := x#element) hSubsetCondition
  have hSubsetAt :
      Γ ⊢ₘ[relation_plane_theory] (x#element ∈ₘ left) ⟶ₘ (x#element ∈ₘ right) := by
    simpa [subset_condition, Formula.openAt,
      Term.openAt, hLeftOpen,
      hRightOpen] using hSubsetAtRaw
  have hUnionSpec :
      Γ ⊢ₘ[relation_plane_theory]
        binary_union_spec left right union :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          binary_union_operator_theory_subset_relation_plane_theory
            hFormula) (by
          simpa [union] using
            binary_union_term_spec_derives
              left right hLeft hRight)
  have hUnionAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := x#element) hUnionSpec
  have hUnionAt :
      Γ ⊢ₘ[relation_plane_theory] (x#element ∈ₘ union) ↔ₘ ((x#element ∈ₘ left) ∨ₘ (x#element ∈ₘ right)) := by
    simpa [binary_union_spec,
      Formula.openAt, Term.openAt,
      hLeftOpen, hRightOpen,
      hUnionOpen] using hUnionAtRaw
  have hAgreementAt :
      Γ ⊢ₘ[relation_plane_theory] (x#element ∈ₘ union) ↔ₘ (x#element ∈ₘ right) := by
    apply FirstOrder.Derives.iffIntro
    · have hCases : (x#element ∈ₘ union) :: Γ
            ⊢ₘ[relation_plane_theory] (x#element ∈ₘ left) ∨ₘ (x#element ∈ₘ right) :=
        FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons
            hUnionAt) (.assumption (by simp))
      have hSubsetAt' :=
        FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ union)
          hSubsetAt
      derive_prop
    · exact FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken_cons
      hUnionAt) (FirstOrder.Derives.disjIntroRight (show
          (x#element ∈ₘ right) :: Γ
              ⊢ₘ[relation_plane_theory]
                x#element ∈ₘ right from
            .assumption (by simp)))
  have hAgreementAtOpened :
      Γ ⊢ₘ[relation_plane_theory]
        Formula.openAt SetSort.set 0 (x#element) agreement_body := by
    simpa [agreement_body, Formula.openAt,
      Term.openAt, hUnionOpen,
      hRightOpen] using hAgreementAt
  have hAgreement :
      Γ ⊢ₘ[relation_plane_theory]
        membership_agreement union right := by
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := relation_plane_theory) (Γ := Γ) (sort := SetSort.set) (eigen := element) (body :=
          Formula.openAt SetSort.set 0 (x#element) agreement_body) (by
          intro formula hFormula
          have hSentence :=
            relation_plane_theory_sentence hFormula
          rw [hSentence.2]
          simp) (by
          intro formula hFormula
          rcases List.mem_singleton.mp hFormula with rfl
          exact hElementFreshSubset)
        hAgreementAtOpened
    simpa [membership_agreement,
      Formula.closeFreeAt_openAt
        SetSort.set element 0 agreement_body
        hElementFreshAgreement] using hGeneralized
  have hExtensionality :
      Γ ⊢ₘ[relation_plane_theory]
        extensionality_instance union right :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          subset_theory_subset_relation_plane_theory (Or.inr hFormula)) (extensionality_instance_derives_of_admissible
          union right hUnion hRight)
  exact FirstOrder.Derives.impElim
    hExtensionality hAgreement
/-! ## 有限配对的子集合同 -/
/-- 配对规格在交换两个端点后保持不变。 -/
theorem pair_spec_comm_iff (left right pair : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ
      pair_spec left right pair ↔ₘ
        pair_spec right left pair := by
  let left_body : SetFormula := (bₛ#0 ∈ₘ pair) ↔ₘ
      pair_member_condition bₛ#0 left right
  let right_body : SetFormula := (bₛ#0 ∈ₘ pair) ↔ₘ
      pair_member_condition bₛ#0 right left
  let member :=
    FreshVariable.fresh_id SetSort.set
      [left_body, right_body]
  let left_point :=
    Formula.openAt SetSort.set 0 (x#member) left_body
  let right_point :=
    Formula.openAt SetSort.set 0 (x#member) right_body
  have hMemberFreshLeft : (SetSort.set, member) freshForₘ
        left_body := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hMemberFreshRight : (SetSort.set, member) freshForₘ
        right_body := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hPairOpen :
      Term.openAt SetSort.set 0 (x#member) pair =
        pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member) pair hPair.2
  have hLeftOpen :
      Term.openAt SetSort.set 0 (x#member) left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member) left hLeft.2
  have hRightOpen :
      Term.openAt SetSort.set 0 (x#member) right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member) right hRight.2
  have hPoint :
      ⊢ₘ left_point ↔ₘ right_point := by
    have hMemberAdmissible :
        Formula.Admissible (x#member ∈ₘ pair) :=
      membership_formula_admissible (set_variable_admissible member)
        hPair
    have hLeftEqualityAdmissible :
        Formula.Admissible (x#member ≐ₘ left) :=
      Formula.Admissible.equal (set_variable_admissible member)
        hLeft
    have hRightEqualityAdmissible :
        Formula.Admissible (x#member ≐ₘ right) :=
      Formula.Admissible.equal (set_variable_admissible member)
        hRight
    have hDisjunction :
        ⊢ₘ ((x#member ≐ₘ left) ∨ₘ (x#member ≐ₘ right)) ↔ₘ ((x#member ≐ₘ right) ∨ₘ (x#member ≐ₘ left)) :=
      FirstOrder.Derives.iffIntro (FirstOrder.Derives.impElim (Metatheory.Derives.disj_comm_m
            hLeftEqualityAdmissible
            hRightEqualityAdmissible) (.assumption (by simp))) (FirstOrder.Derives.impElim (Metatheory.Derives.disj_comm_m
            hRightEqualityAdmissible
            hLeftEqualityAdmissible) (.assumption (by simp)))
    simpa [left_point, right_point,
      left_body, right_body,
      pair_member_condition,
      Formula.openAt, Term.openAt,
      hPairOpen, hLeftOpen,
      hRightOpen] using
      Metatheory.Derives.iff_right_congr_m
        hMemberAdmissible hDisjunction
  have hClosed :
      ⊢ₘ (∀ₘ[SetSort.set, member], left_point) ↔ₘ (∀ₘ[SetSort.set, member], right_point) :=
    Metatheory.Derives.forall_iff_mono (T := (Theory.empty : SetTheory)) (Γ := []) (sort := SetSort.set) (eigen := member) (left := left_point)
      (right := right_point) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        cases hFormula)
      hPoint
  simpa [pair_spec, left_point, right_point,
    left_body, right_body,
    Formula.closeFreeAt_openAt
      SetSort.set member 0 left_body
      hMemberFreshLeft,
    Formula.closeFreeAt_openAt
      SetSort.set member 0 right_body
      hMemberFreshRight] using hClosed
/-- 规范无序对交换两个端点后相等。 -/
theorem unordered_pair_term_comm (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      {left, right}ₘ ≐ₘ {right, left}ₘ := by
  have hLeftSpec :
      ⊢ₘ[relation_plane_theory]
        pair_spec left right {left, right}ₘ :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        pairing_operator_theory_subset_relation_plane_theory
          hFormula) (unordered_pair_term_spec_derives
        left right hLeft hRight)
  have hRightCanonicalSpec :
      ⊢ₘ[relation_plane_theory]
        pair_spec right left {right, left}ₘ :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        pairing_operator_theory_subset_relation_plane_theory
          hFormula) (unordered_pair_term_spec_derives
        right left hRight hLeft)
  have hComm :
      ⊢ₘ[relation_plane_theory]
        pair_spec left right {right, left}ₘ ↔ₘ
          pair_spec right left {right, left}ₘ :=
    FirstOrder.Derives.theory_weaken (by simp [Theory.empty]) (pair_spec_comm_iff
        left right {right, left}ₘ
        hLeft hRight (unordered_pair_term_admissible
          right left hRight hLeft))
  have hRightSpec :
      ⊢ₘ[relation_plane_theory]
        pair_spec left right {right, left}ₘ :=
    FirstOrder.Derives.iffElimLeft
      hComm hRightCanonicalSpec
  have hUnique :
      ⊢ₘ[relation_plane_theory]
        pair_spec left right {left, right}ₘ ⟶ₘ
          pair_spec left right {right, left}ₘ ⟶ₘ ({left, right}ₘ ≐ₘ {right, left}ₘ) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        subset_theory_subset_relation_plane_theory (Or.inr hFormula)) (pair_unique
        left right {left, right}ₘ {right, left}ₘ
        hLeft hRight (unordered_pair_term_admissible
          left right hLeft hRight) (unordered_pair_term_admissible
          right left hRight hLeft))
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
      hUnique hLeftSpec)
    hRightSpec
/-- 一个配对候选的两个指定成员落在同一集合中时，该候选满足相应子集成员条件。 -/
theorem pair_spec_implies_subset_condition_of_members (left right pair source : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hPair : Term.Admissible pair SetSort.set) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ
      pair_spec left right pair ⟶ₘ (left ∈ₘ source) ⟶ₘ (right ∈ₘ source) ⟶ₘ
            subset_condition pair source := by
  let spec := pair_spec left right pair
  let left_mem : SetFormula := left ∈ₘ source
  let right_mem : SetFormula := right ∈ₘ source
  let subset_body : SetFormula := (bₛ#0 ∈ₘ pair) ⟶ₘ (bₛ#0 ∈ₘ source)
  let member :=
    FreshVariable.fresh_id SetSort.set
      [spec, left_mem, right_mem, subset_body]
  have hMemberFreshSpec : (SetSort.set, member) freshForₘ spec := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hMemberFreshLeft : (SetSort.set, member) freshForₘ left_mem := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hMemberFreshRight : (SetSort.set, member) freshForₘ right_mem := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hMemberFreshSubset : (SetSort.set, member) freshForₘ
        subset_body := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hPairOpenZero :
      Term.openAt SetSort.set 0 (x#member) pair =
        pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member) pair hPair.2
  have hSourceOpenZero :
      Term.openAt SetSort.set 0 (x#member) source =
        source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member) source hSource.2
  change
    ⊢ₘ spec ⟶ₘ (left_mem ⟶ₘ (right_mem ⟶ₘ (∀ₘ[SetSort.set], subset_body)))
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [right_mem, left_mem, spec]
  have hSpec :
      Γ ⊢ₘ spec :=
    .assumption (by simp [Γ])
  have hPairAt :=
    pair_spec_membership_iff
      left right pair (x#member)
      hLeft hRight hPair (set_variable_admissible member)
      hSpec
  have hSubsetAt :
      Γ ⊢ₘ (x#member ∈ₘ pair) ⟶ₘ (x#member ∈ₘ source) := by
    nd_apply FirstOrder.Derives.impIntro
    have hCases : (x#member ∈ₘ pair) :: Γ ⊢ₘ ((x#member ≐ₘ left) ∨ₘ (x#member ≐ₘ right)) :=
      FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons
          hPairAt) (.assumption (by simp))
    have hLeftCase : (x#member ∈ₘ pair) :: Γ ⊢ₘ (x#member ≐ₘ left) ⟶ₘ (x#member ∈ₘ source) := by
      nd_apply FirstOrder.Derives.impIntro
      have hEquality : (x#member ≐ₘ left) :: (x#member ∈ₘ pair) :: Γ ⊢ₘ
            x#member ≐ₘ left :=
        .assumption (by simp)
      have hTransport :=
        membership_left_iff_of_equality (x#member) left source (set_variable_admissible member)
          hLeft hSource hEquality
      exact FirstOrder.Derives.iffElimLeft
        hTransport (show (x#member ≐ₘ left) :: (x#member ∈ₘ pair) :: Γ ⊢ₘ
            left_mem from
          .assumption (by simp [Γ]))
    have hRightCase : (x#member ∈ₘ pair) :: Γ ⊢ₘ (x#member ≐ₘ right) ⟶ₘ (x#member ∈ₘ source) := by
      nd_apply FirstOrder.Derives.impIntro
      have hEquality : (x#member ≐ₘ right) :: (x#member ∈ₘ pair) :: Γ ⊢ₘ
            x#member ≐ₘ right :=
        .assumption (by simp)
      have hTransport :=
        membership_left_iff_of_equality (x#member) right source (set_variable_admissible member)
          hRight hSource hEquality
      exact FirstOrder.Derives.iffElimLeft
        hTransport (show (x#member ≐ₘ right) :: (x#member ∈ₘ pair) :: Γ ⊢ₘ
            right_mem from
          .assumption (by simp [Γ]))
    derive_prop
  have hSubsetAtOpened :
      Γ ⊢ₘ
        Formula.openAt SetSort.set 0 (x#member) subset_body := by
    simpa [subset_body, Formula.openAt,
      Term.openAt, hPairOpenZero,
      hSourceOpenZero] using hSubsetAt
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := (Theory.empty : SetTheory)) (Γ := Γ) (sort := SetSort.set) (eigen := member) (body :=
        Formula.openAt SetSort.set 0 (x#member) subset_body) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        rcases List.mem_cons.mp hFormula with rfl | hFormula
        · exact hMemberFreshRight
        · rcases List.mem_cons.mp hFormula with rfl | hFormula
          · exact hMemberFreshLeft
          · rcases List.mem_singleton.mp hFormula with rfl
            exact hMemberFreshSpec)
      hSubsetAtOpened
  simpa [subset_condition,
    Formula.closeFreeAt_openAt
      SetSort.set member 0 subset_body
      hMemberFreshSubset] using hGeneralized
/-- 在关系平面理论中，配对规格与两个成员事实推出真正的子集原子。 -/
theorem pair_spec_implies_subset_of_members (left right pair source : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hPair : Term.Admissible pair SetSort.set) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      pair_spec left right pair ⟶ₘ (left ∈ₘ source) ⟶ₘ (right ∈ₘ source) ⟶ₘ (pair ⊆ₘ source) := by
  have hCondition :
      ⊢ₘ[relation_plane_theory]
        pair_spec left right pair ⟶ₘ (left ∈ₘ source) ⟶ₘ (right ∈ₘ source) ⟶ₘ
              subset_condition pair source :=
    FirstOrder.Derives.theory_weaken (by simp [Theory.empty]) (pair_spec_implies_subset_condition_of_members
        left right pair source
        hLeft hRight hPair hSource)
  have hDefinition :
      ⊢ₘ[relation_plane_theory]
        subset_definition_instance pair source :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        subset_theory_subset_relation_plane_theory
          hFormula) (subset_definition_instance_derives_of_admissible
        pair source hPair hSource)
  derive_prop
/-- 无序对的两个端点属于同一集合时，该无序对是该集合的子集。 -/
theorem unordered_pair_subset_of_members (left right source : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[relation_plane_theory] (left ∈ₘ source) ⟶ₘ (right ∈ₘ source) ⟶ₘ ({left, right}ₘ ⊆ₘ source) := by
  have hSpec :
      ⊢ₘ[relation_plane_theory]
        pair_spec left right {left, right}ₘ :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        ordered_pair_operator_theory_subset_relation_plane_theory (singleton_operator_theory_subset_ordered_pair_operator_theory (Or.inr hFormula)))
      (unordered_pair_term_spec_derives
        left right hLeft hRight)
  have hSubset :=
    pair_spec_implies_subset_of_members
      left right {left, right}ₘ source
      hLeft hRight (unordered_pair_term_admissible
        left right hLeft hRight)
      hSource
  derive_prop
/-- 单点集元素属于给定集合时，该单点集是该集合的子集。 -/
theorem singleton_subset_of_mem (element source : SetTerm) (hElement : Term.Admissible element SetSort.set) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[relation_plane_theory] (element ∈ₘ source) ⟶ₘ ({element}ₘ ⊆ₘ source) := by
  have hRepeated :=
    unordered_pair_subset_of_members
      element element source
      hElement hElement hSource
  have hEquality :
      ⊢ₘ[relation_plane_theory]
        {element}ₘ ≐ₘ {element, element}ₘ :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        ordered_pair_operator_theory_subset_relation_plane_theory (singleton_operator_theory_subset_ordered_pair_operator_theory
            hFormula)) (singleton_definition_instance_derives
        element hElement)
  have hSubsetTransport :
      ⊢ₘ[relation_plane_theory] ({element, element}ₘ ⊆ₘ source) ⟶ₘ ({element}ₘ ⊆ₘ source) := by
    have hSymmetry :=
      Metatheory.Derives.equality_symm (T := relation_plane_theory) (Γ := [])
        hEquality
    let parameter :=
      FreshVariable.fresh_id SetSort.set
        [source ≐ₘ source]
    let body : SetFormula :=
      x#parameter ⊆ₘ source
    have hSourceFresh : (SetSort.set, parameter) ∉
          Term.freeSupport source := by
      dsimp [parameter]
      exact FreshVariable.fresh_term_not_mem_m
        SetSort.set source
    have hSourceFixedRepeated :
        Term.substituteFree SetSort.set parameter
            {element, element}ₘ source =
          source :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set parameter
        {element, element}ₘ source hSourceFresh
    have hSourceFixedSingleton :
        Term.substituteFree SetSort.set parameter
            {element}ₘ source =
          source :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set parameter
        {element}ₘ source hSourceFresh
    nd_apply FirstOrder.Derives.impIntro
    have hTransport :=
      FirstOrder.Derives.eq_subst_m
        (T := relation_plane_theory)
        (Γ := [{element, element}ₘ ⊆ₘ source])
        (sort := SetSort.set) (eigen := parameter)
        (left := {element, element}ₘ) (right := {element}ₘ)
        (body := body)
        (FirstOrder.Derives.context_weaken_cons hSymmetry) (by
          simpa [body, Formula.substituteFree,
            Term.substituteFree,
            hSourceFixedRepeated, set_variable] using (show
              [{element, element}ₘ ⊆ₘ source]
                ⊢ₘ[relation_plane_theory]
                  {element, element}ₘ ⊆ₘ source from
              .assumption (by simp)))
    simpa [body, Formula.substituteFree,
      Term.substituteFree,
      hSourceFixedSingleton, set_variable] using
      hTransport
  derive_prop
/-! ## 规范有限集的成员事实 -/
/-- 元素属于自身生成的单点集。 -/
theorem mem_singleton_self (element : SetTerm) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      element ∈ₘ {element}ₘ := by
  have hSpec :
      ⊢ₘ[relation_plane_theory]
        singleton_spec element {element}ₘ :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        ordered_pair_operator_theory_subset_relation_plane_theory (singleton_operator_theory_subset_ordered_pair_operator_theory
            hFormula)) (singleton_term_spec_derives element hElement)
  have hAt :=
    singleton_spec_membership_iff
      element {element}ₘ element
      hElement (singleton_term_admissible element hElement)
      hElement hSpec
  exact FirstOrder.Derives.iffElimLeft
    hAt (FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) element)
/-- 左端点属于其生成的无序对。 -/
theorem mem_unordered_pair_left (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      left ∈ₘ {left, right}ₘ := by
  have hSpec :
      ⊢ₘ[relation_plane_theory]
        pair_spec left right {left, right}ₘ :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        ordered_pair_operator_theory_subset_relation_plane_theory (singleton_operator_theory_subset_ordered_pair_operator_theory (Or.inr hFormula)))
      (unordered_pair_term_spec_derives
        left right hLeft hRight)
  have hAt :=
    pair_spec_membership_iff
      left right {left, right}ₘ left
      hLeft hRight (unordered_pair_term_admissible
        left right hLeft hRight)
      hLeft hSpec
  exact FirstOrder.Derives.iffElimLeft
    hAt (FirstOrder.Derives.disjIntroLeft
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) left))
/-- 右端点属于其生成的无序对。 -/
theorem mem_unordered_pair_right (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      right ∈ₘ {left, right}ₘ := by
  have hSpec :
      ⊢ₘ[relation_plane_theory]
        pair_spec left right {left, right}ₘ :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        ordered_pair_operator_theory_subset_relation_plane_theory (singleton_operator_theory_subset_ordered_pair_operator_theory (Or.inr hFormula)))
      (unordered_pair_term_spec_derives
        left right hLeft hRight)
  have hAt :=
    pair_spec_membership_iff
      left right {left, right}ₘ right
      hLeft hRight (unordered_pair_term_admissible
        left right hLeft hRight)
      hRight hSpec
  exact FirstOrder.Derives.iffElimLeft
    hAt (FirstOrder.Derives.disjIntroRight
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) right))
/-- 左坐标单点集属于对应的 Kuratowski 有序对。 -/
theorem singleton_mem_ordered_pair (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      {left}ₘ ∈ₘ ⟨left, right⟩ₘ := by
  have hSpec :
      ⊢ₘ[relation_plane_theory]
        ordered_pair_spec
          left right ⟨left, right⟩ₘ :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        ordered_pair_operator_theory_subset_relation_plane_theory
          hFormula) (ordered_pair_term_spec_derives
        left right hLeft hRight)
  have hAt :=
    pair_spec_membership_iff
      {left}ₘ {left, right}ₘ
      ⟨left, right⟩ₘ {left}ₘ (singleton_term_admissible left hLeft) (unordered_pair_term_admissible
        left right hLeft hRight) (ordered_pair_term_admissible
        left right hLeft hRight) (singleton_term_admissible left hLeft) (by
        simpa [ordered_pair_spec] using hSpec)
  exact FirstOrder.Derives.iffElimLeft
    hAt (FirstOrder.Derives.disjIntroLeft
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) {left}ₘ))
/-- 坐标无序对属于对应的 Kuratowski 有序对。 -/
theorem unordered_pair_mem_ordered_pair (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      {left, right}ₘ ∈ₘ
        ⟨left, right⟩ₘ := by
  have hSpec :
      ⊢ₘ[relation_plane_theory]
        ordered_pair_spec
          left right ⟨left, right⟩ₘ :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        ordered_pair_operator_theory_subset_relation_plane_theory
          hFormula) (ordered_pair_term_spec_derives
        left right hLeft hRight)
  have hAt :=
    pair_spec_membership_iff
      {left}ₘ {left, right}ₘ
      ⟨left, right⟩ₘ {left, right}ₘ (singleton_term_admissible left hLeft) (unordered_pair_term_admissible
        left right hLeft hRight) (ordered_pair_term_admissible
        left right hLeft hRight) (unordered_pair_term_admissible
        left right hLeft hRight) (by
        simpa [ordered_pair_spec] using hSpec)
  exact FirstOrder.Derives.iffElimLeft
    hAt (FirstOrder.Derives.disjIntroRight
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) {left, right}ₘ))
/--
规范 Kuratowski 有序对的一元并集恰好是其两个坐标的无序对。
中间把有序对项识别为 `{{left}, {left, right}}`，再使用二元并吸收律。
-/
theorem union_ordered_pair_term_eq_unordered_pair (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[relation_plane_theory] (⋃ₘ ⟨left, right⟩ₘ) ≐ₘ
        {left, right}ₘ := by
  let singleton := {left}ₘ
  let pair := {left, right}ₘ
  let ordered := ⟨left, right⟩ₘ
  let kuratowski := {singleton, pair}ₘ
  let binary := singleton ∪ₘ pair
  have hSingleton :
      Term.Admissible singleton SetSort.set :=
    singleton_term_admissible left hLeft
  have hPair :
      Term.Admissible pair SetSort.set :=
    unordered_pair_term_admissible
      left right hLeft hRight
  have hOrdered :
      Term.Admissible ordered SetSort.set :=
    ordered_pair_term_admissible
      left right hLeft hRight
  have hKuratowski :
      Term.Admissible kuratowski SetSort.set :=
    unordered_pair_term_admissible
      singleton pair hSingleton hPair
  have hBinary :
      Term.Admissible binary SetSort.set :=
    binary_union_term_admissible
      singleton pair hSingleton hPair
  have hUnionKuratowski :
      Term.Admissible (⋃ₘ kuratowski) SetSort.set :=
    union_term_admissible
      kuratowski hKuratowski
  have hOuterSpec :
      ⊢ₘ[relation_plane_theory]
        pair_spec singleton pair ordered := by
    simpa [singleton, pair, ordered,
      ordered_pair_spec] using (FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          ordered_pair_operator_theory_subset_relation_plane_theory
            hFormula) (ordered_pair_term_spec_derives
          left right hLeft hRight))
  have hOrderedKuratowskiIff :
      ⊢ₘ[relation_plane_theory] (ordered ≐ₘ kuratowski) ↔ₘ
          pair_spec singleton pair ordered := by
    simpa [kuratowski] using (FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          pairing_operator_theory_subset_relation_plane_theory
            hFormula) (by
          simpa [kuratowski] using
            unordered_pair_eq_iff_spec
              singleton pair ordered
              hSingleton hPair hOrdered))
  have hOrderedKuratowski :
      ⊢ₘ[relation_plane_theory]
        ordered ≐ₘ kuratowski :=
    FirstOrder.Derives.iffElimLeft
      hOrderedKuratowskiIff hOuterSpec
  have hUnionCongruence :
      ⊢ₘ[relation_plane_theory] (⋃ₘ ordered) ≐ₘ (⋃ₘ kuratowski) :=
    union_term_congr_of_equality
      ordered kuratowski
      hOrdered hKuratowski
      hOrderedKuratowski
  have hBinaryDefinition :
      ⊢ₘ[relation_plane_theory]
        binary ≐ₘ (⋃ₘ kuratowski) := by
    simpa [binary, kuratowski,
      singleton, pair] using (FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          binary_union_operator_theory_subset_relation_plane_theory
            hFormula) (binary_union_term_eq_union_pair_derives
          singleton pair hSingleton hPair))
  have hUnionKuratowskiBinary :
      ⊢ₘ[relation_plane_theory] (⋃ₘ kuratowski) ≐ₘ binary :=
    Metatheory.Derives.equality_symm
      hBinaryDefinition
  have hSingletonSubsetPair :
      ⊢ₘ[relation_plane_theory]
        singleton ⊆ₘ pair := by
    exact FirstOrder.Derives.impElim (by
        simpa [singleton, pair] using
          singleton_subset_of_mem
            left pair hLeft hPair) (by
        simpa [pair] using
          mem_unordered_pair_left
            left right hLeft hRight)
  have hAbsorption :
      ⊢ₘ[relation_plane_theory]
        binary ≐ₘ pair := by
    exact FirstOrder.Derives.impElim (by
        simpa [binary] using
          binary_union_term_eq_right_of_subset
            singleton pair
            hSingleton hPair)
      hSingletonSubsetPair
  have hUnionOrderedBinary :
      ⊢ₘ[relation_plane_theory] (⋃ₘ ordered) ≐ₘ binary :=
    Metatheory.Derives.equality_trans
      hUnionCongruence
      hUnionKuratowskiBinary
  simpa [ordered, pair] using
    Metatheory.Derives.equality_trans
      hUnionOrderedBinary hAbsorption
/-! ## 笛卡尔积标准母集 -/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
