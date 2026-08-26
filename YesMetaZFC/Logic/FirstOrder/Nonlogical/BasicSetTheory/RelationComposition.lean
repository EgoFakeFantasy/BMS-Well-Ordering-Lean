import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationProperties
/-!
# 关系逆与关系复合
本模块建立关系代数的第一层。文献对单个有序对反转与整条关系取逆都使用
上标 `-1`；新核严格区分二者：`pair⁻¹ₘ` 只反转一个有序对，
`converseₘ(relation)` 才表示关系逆。
关系复合的核心成员条件采用现代原子项写法：一个规范有序对属于
`second ∘ₘ first`，当且仅当存在中间点，使两条规范有序对分别属于
`first` 与 `second`。文献中的 `GX`、`YXD`、`ψ₉` 与有限变量编号只保留为
注释索引；由两条边自动推出的中间点值域/定义域条件不重复进入核心公式。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 关系逆规格 -/
/-- 当前元素满足关系逆筛选条件。 -/
def relation_converse_condition (relation : SetTerm) :
    SetFormula := (bₛ#0 ∈ₘ (ranₘ(relation) ×ₘ domₘ(relation))) ∧ₘ (is_ordered_pair_formula bₛ#0 ∧ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ relation) ∧ₘ (bₛ#1 ≐ₘ (bₛ#0)⁻¹ₘ)))
/-- `candidate` 是 `relation` 的关系逆。 -/
def relation_converse_spec (relation candidate : SetTerm) :
    SetFormula :=
  membership_specification
    candidate (relation_converse_condition relation)
/-- 关系逆规格在一个 admissible 元素处的点态形式。 -/
def relation_converse_member_condition (relation element : SetTerm) :
    SetFormula := (element ∈ₘ (ranₘ(relation) ×ₘ domₘ(relation))) ∧ₘ (is_ordered_pair_formula element ∧ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ relation) ∧ₘ
          (element ≐ₘ (bₛ#0)⁻¹ₘ)))
/-- 对固定关系断言一个关系逆候选存在。 -/
def relation_converse_exists (relation : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
        relation_converse_condition relation
/-- 从任意母集中分离关系逆元素。 -/
def relation_converse_separation_exists (relation source : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ((bₛ#0 ∈ₘ source) ∧ₘ (is_ordered_pair_formula bₛ#0 ∧ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ relation) ∧ₘ (bₛ#1 ≐ₘ (bₛ#0)⁻¹ₘ))))
/-- 任意关系参数和任意母集上的关系逆分离实例。 -/
def relation_converse_separation_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      relation_converse_separation_exists (x#0) (x#1)
/-- 关系逆函数符号的开放定义实例。 -/
def relation_converse_definition_instance (relation candidate : SetTerm) :
    SetFormula :=
  is_relation_formula relation ⟶ₘ ((candidate ≐ₘ converseₘ(relation)) ↔ₘ
      relation_converse_spec relation candidate)
/-- 关系逆函数符号定义公理。 -/
def relation_converse_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      relation_converse_definition_instance (x#0) (x#1)
/-! ## 关系复合规格 -/
/--
当前元素满足关系复合筛选条件。
最内层存在 binder 引入中间点，因此其中 `bₛ#1` 指向外层当前有序对。
-/
def relation_composition_condition (first second : SetTerm) :
    SetFormula := (bₛ#0 ∈ₘ (domₘ(first) ×ₘ ranₘ(second))) ∧ₘ (is_ordered_pair_formula bₛ#0 ∧ₘ (∃ₘ[SetSort.set], (⟨(bₛ#1)₀ₘ, bₛ#0⟩ₘ ∈ₘ first) ∧ₘ
          (⟨bₛ#0, (bₛ#1)₁ₘ⟩ₘ ∈ₘ second)))
/-- `candidate` 是 `second ∘ first`。 -/
def relation_composition_spec (first second candidate : SetTerm) :
    SetFormula :=
  membership_specification
    candidate (relation_composition_condition first second)
/-- 关系复合规格在一个 admissible 元素处的点态形式。 -/
def relation_composition_member_condition (first second element : SetTerm) :
    SetFormula := (element ∈ₘ (domₘ(first) ×ₘ ranₘ(second))) ∧ₘ (is_ordered_pair_formula element ∧ₘ (∃ₘ[SetSort.set], (⟨(element)₀ₘ, bₛ#0⟩ₘ ∈ₘ first) ∧ₘ
          (⟨bₛ#0, (element)₁ₘ⟩ₘ ∈ₘ second)))
/-- 对固定两个关系断言一个复合候选存在。 -/
def relation_composition_exists (first second : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
        relation_composition_condition first second
/-- 从任意母集中分离关系复合元素。 -/
def relation_composition_separation_exists (first second source : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ((bₛ#0 ∈ₘ source) ∧ₘ (is_ordered_pair_formula bₛ#0 ∧ₘ (∃ₘ[SetSort.set], (⟨(bₛ#1)₀ₘ, bₛ#0⟩ₘ ∈ₘ first) ∧ₘ
                (⟨bₛ#0, (bₛ#1)₁ₘ⟩ₘ ∈ₘ second))))
/-- 任意两个关系参数和任意母集上的复合分离实例。 -/
def relation_composition_separation_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        relation_composition_separation_exists (x#0) (x#1) (x#2)
/-- 关系复合函数符号的开放定义实例。 -/
def relation_composition_definition_instance (first second candidate : SetTerm) :
    SetFormula := (is_relation_formula first ∧ₘ
      is_relation_formula second) ⟶ₘ ((candidate ≐ₘ (second ∘ₘ first)) ↔ₘ
      relation_composition_spec
        first second candidate)
/-- 关系复合函数符号定义公理。 -/
def relation_composition_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        relation_composition_definition_instance (x#0) (x#1) (x#2)
/-! ## 理论边界 -/
/-- 在关系平面理论上加入关系逆分离实例。 -/
def relation_converse_theory : SetTheory :=
  Theory.insert
    relation_converse_separation_axiom
    relation_plane_theory
/-- 加入关系逆函数符号。 -/
def relation_converse_operator_theory : SetTheory :=
  Theory.insert
    relation_converse_definition_axiom
    relation_converse_theory
/-- 在关系逆层上加入关系复合分离实例。 -/
def relation_composition_theory : SetTheory :=
  Theory.insert
    relation_composition_separation_axiom
    relation_converse_operator_theory
/-- 加入关系复合函数符号。 -/
def relation_composition_operator_theory : SetTheory :=
  Theory.insert
    relation_composition_definition_axiom
    relation_composition_theory
/-! ## proof-carrying 良构性 -/
/-- 关系逆项满足 proof-carrying 项边界。 -/
theorem relation_converse_term_admissible (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    Term.Admissible (relation_converse_term relation)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .relationConverse [⟨relation, by assumption⟩]
      (by rfl) (by rfl)
/-- 关系逆项的合法性由关系项证书计算。 -/
@[term_check]
theorem relation_converse_term_check
    {relation : SetTerm}
    (hRelation : Term.CheckCertificate relation SetSort.set) :
    Term.CheckCertificate (relation_converse_term relation)
      SetSort.set :=
  Term.check_admissible_complete <|
    relation_converse_term_admissible relation hRelation.admissible
/-- 关系复合项满足 proof-carrying 项边界。 -/
theorem relation_composition_term_admissible (second first : SetTerm) (hSecond : Term.Admissible second SetSort.set)
    (hFirst : Term.Admissible first SetSort.set) :
    Term.Admissible (relation_composition_term second first)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .relationComposition [⟨second, by assumption⟩, ⟨first, by assumption⟩]
      (by rfl) (by rfl)
/-- 关系复合项的合法性由两个关系项证书计算。 -/
@[term_check]
theorem relation_composition_term_check
    {second first : SetTerm}
    (hSecond : Term.CheckCertificate second SetSort.set)
    (hFirst : Term.CheckCertificate first SetSort.set) :
    Term.CheckCertificate
      (relation_composition_term second first) SetSort.set :=
  Term.check_admissible_complete <|
    relation_composition_term_admissible
      second first hSecond.admissible hFirst.admissible
/-- 关系逆的单元素筛选谓词。母集界由 `separation_spec` 统一加入。 -/
private def relation_converse_predicate (relation : SetTerm) (hRelation : Term.Admissible
      relation SetSort.set) :
    SetPredicate where
  body :=
    is_ordered_pair_formula bₛ#0 ∧ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ relation) ∧ₘ (bₛ#1 ≐ₘ (bₛ#0)⁻¹ₘ))
  admissible_at := by
    prove_admissible_at
/-- 关系复合的单元素筛选谓词。母集界由 `separation_spec` 统一加入。 -/
private def relation_composition_predicate (first second : SetTerm) (hFirst : Term.Admissible
      first SetSort.set) (hSecond : Term.Admissible
      second SetSort.set) :
    SetPredicate where
  body :=
    is_ordered_pair_formula bₛ#0 ∧ₘ (∃ₘ[SetSort.set], (⟨(bₛ#1)₀ₘ, bₛ#0⟩ₘ ∈ₘ first) ∧ₘ (⟨bₛ#0, (bₛ#1)₁ₘ⟩ₘ ∈ₘ second))
  admissible_at := by
    prove_admissible_at
/-- 关系逆规格保持公式 admissibility。 -/
theorem relation_converse_spec_admissible
    {relation candidate : SetTerm} (hRelation : Term.Admissible
      relation SetSort.set) (hCandidate : Term.Admissible
      candidate SetSort.set) :
    Formula.Admissible (relation_converse_spec
        relation candidate) := by
  have hSource :
      Term.Admissible (ranₘ(relation) ×ₘ domₘ(relation))
        SetSort.set :=
    cartesian_product_term_admissible (ranₘ(relation)) (domₘ(relation)) (range_term_admissible relation hRelation) (domain_term_admissible relation hRelation)
  have hSpec :=
    SetPredicate.separation_spec_admissible (relation_converse_predicate
        relation hRelation)
      hSource hCandidate
  simpa [SetPredicate.separation_spec,
    relation_converse_predicate,
    relation_converse_spec,
    relation_converse_condition,
    membership_specification] using hSpec
/-- 关系逆规格的合法性由关系项与候选项证书计算。 -/
@[formula_check]
theorem relation_converse_spec_check
    {relation candidate : SetTerm}
    (hRelation : Term.CheckCertificate relation SetSort.set)
    (hCandidate : Term.CheckCertificate candidate SetSort.set) :
    Formula.CheckCertificate
      (relation_converse_spec relation candidate) :=
  Formula.check_admissible_complete <|
    relation_converse_spec_admissible
      hRelation.admissible hCandidate.admissible
/-- 关系复合规格保持公式 admissibility。 -/
theorem relation_composition_spec_admissible
    {first second candidate : SetTerm} (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) (hCandidate : Term.Admissible
      candidate SetSort.set) :
    Formula.Admissible (relation_composition_spec
        first second candidate) := by
  have hSource :
      Term.Admissible (domₘ(first) ×ₘ ranₘ(second))
        SetSort.set :=
    cartesian_product_term_admissible (domₘ(first)) (ranₘ(second)) (domain_term_admissible first hFirst) (range_term_admissible second hSecond)
  have hSpec :=
    SetPredicate.separation_spec_admissible (relation_composition_predicate
        first second hFirst hSecond)
      hSource hCandidate
  simpa [SetPredicate.separation_spec,
    relation_composition_predicate,
    relation_composition_spec,
    relation_composition_condition,
    membership_specification] using hSpec
/-- 关系复合规格的合法性由两个关系项与候选项证书计算。 -/
@[formula_check]
theorem relation_composition_spec_check
    {first second candidate : SetTerm}
    (hFirst : Term.CheckCertificate first SetSort.set)
    (hSecond : Term.CheckCertificate second SetSort.set)
    (hCandidate : Term.CheckCertificate candidate SetSort.set) :
    Formula.CheckCertificate
      (relation_composition_spec first second candidate) :=
  Formula.check_admissible_complete <|
    relation_composition_spec_admissible
      hFirst.admissible hSecond.admissible
      hCandidate.admissible
/-- 关系逆候选存在式保持公式 admissibility。 -/
theorem relation_converse_exists_admissible
    {relation : SetTerm} (hRelation : Term.Admissible
      relation SetSort.set) :
    Formula.Admissible (relation_converse_exists relation) := by
  have hSource :
      Term.Admissible (ranₘ(relation) ×ₘ domₘ(relation))
        SetSort.set :=
    cartesian_product_term_admissible (ranₘ(relation)) (domₘ(relation)) (range_term_admissible relation hRelation) (domain_term_admissible relation hRelation)
  have hExists :=
    SetPredicate.separation_exists_admissible (relation_converse_predicate
        relation hRelation)
      hSource
  simpa [SetPredicate.separation_exists,
    relation_converse_predicate,
    relation_converse_exists,
    relation_converse_condition] using hExists
/-- 关系复合候选存在式保持公式 admissibility。 -/
theorem relation_composition_exists_admissible
    {first second : SetTerm} (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) :
    Formula.Admissible (relation_composition_exists first second) := by
  have hSource :
      Term.Admissible (domₘ(first) ×ₘ ranₘ(second))
        SetSort.set :=
    cartesian_product_term_admissible (domₘ(first)) (ranₘ(second)) (domain_term_admissible first hFirst) (range_term_admissible second hSecond)
  have hExists :=
    SetPredicate.separation_exists_admissible (relation_composition_predicate
        first second hFirst hSecond)
      hSource
  simpa [SetPredicate.separation_exists,
    relation_composition_predicate,
    relation_composition_exists,
    relation_composition_condition] using hExists
/-- 关系逆定义实例保持公式 admissibility。 -/
theorem relation_converse_definition_instance_admissible
    {relation candidate : SetTerm} (hRelation : Term.Admissible
      relation SetSort.set) (hCandidate : Term.Admissible
      candidate SetSort.set) :
    Formula.Admissible (relation_converse_definition_instance
        relation candidate) :=
  Formula.Admissible.imp (is_relation_formula_admissible hRelation) (Formula.Admissible.iff (Formula.Admissible.equal
        hCandidate (relation_converse_term_admissible
          relation hRelation)) (relation_converse_spec_admissible
        hRelation hCandidate))
/-- 关系复合定义实例保持公式 admissibility。 -/
theorem relation_composition_definition_instance_admissible
    {first second candidate : SetTerm} (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) (hCandidate : Term.Admissible
      candidate SetSort.set) :
    Formula.Admissible (relation_composition_definition_instance
        first second candidate) :=
  Formula.Admissible.imp (Formula.Admissible.conj (is_relation_formula_admissible hFirst) (is_relation_formula_admissible hSecond)) (Formula.Admissible.iff
      (Formula.Admissible.equal
        hCandidate (relation_composition_term_admissible
          second first hSecond hFirst)) (relation_composition_spec_admissible
        hFirst hSecond hCandidate))
theorem relation_converse_separation_axiom_admissible :
    Formula.Admissible
      relation_converse_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem relation_converse_definition_axiom_admissible :
    Formula.Admissible
      relation_converse_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem relation_composition_separation_axiom_admissible :
    Formula.Admissible
      relation_composition_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem relation_composition_definition_axiom_admissible :
    Formula.Admissible
      relation_composition_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem relation_converse_theory_admissible :
    Theory.Admissible relation_converse_theory :=
  Theory.admissible_insert
    relation_converse_separation_axiom_admissible
    relation_plane_theory_admissible
theorem relation_converse_operator_theory_admissible :
    Theory.Admissible
      relation_converse_operator_theory :=
  Theory.admissible_insert
    relation_converse_definition_axiom_admissible
    relation_converse_theory_admissible
theorem relation_composition_theory_admissible :
    Theory.Admissible relation_composition_theory :=
  Theory.admissible_insert
    relation_composition_separation_axiom_admissible
    relation_converse_operator_theory_admissible
theorem relation_composition_operator_theory_admissible :
    Theory.Admissible
      relation_composition_operator_theory :=
  Theory.admissible_insert
    relation_composition_definition_axiom_admissible
    relation_composition_theory_admissible
/-! ## 闭理论边界 -/
@[derive_close_sentence]
theorem relation_converse_theory_sentence
    {formula : SetFormula} (hFormula : relation_converse_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact relation_converse_separation_axiom_admissible
    · native_decide
  · exact relation_plane_theory_sentence hFormula
@[derive_close_sentence]
theorem relation_converse_operator_theory_sentence
    {formula : SetFormula} (hFormula :
      relation_converse_operator_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact relation_converse_definition_axiom_admissible
    · native_decide
  · exact relation_converse_theory_sentence hFormula
@[derive_close_sentence]
theorem relation_composition_theory_sentence
    {formula : SetFormula} (hFormula : relation_composition_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact relation_composition_separation_axiom_admissible
    · native_decide
  · exact relation_converse_operator_theory_sentence
      hFormula
@[derive_close_sentence]
theorem relation_composition_operator_theory_sentence
    {formula : SetFormula} (hFormula :
      relation_composition_operator_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact relation_composition_definition_axiom_admissible
    · native_decide
  · exact relation_composition_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem relation_plane_theory_subset_relation_converse_theory
    {formula : SetFormula} (hFormula : relation_plane_theory formula) :
    relation_converse_theory formula :=
  Or.inr hFormula
theorem relation_converse_theory_subset_relation_converse_operator_theory
    {formula : SetFormula} (hFormula : relation_converse_theory formula) :
    relation_converse_operator_theory formula :=
  Or.inr hFormula
theorem relation_converse_operator_theory_subset_relation_composition_theory
    {formula : SetFormula} (hFormula :
      relation_converse_operator_theory formula) :
    relation_composition_theory formula :=
  Or.inr hFormula
/-- 关系平面理论嵌入关系复合存在性理论。 -/
theorem relation_plane_theory_subset_relation_composition_theory
    {formula : SetFormula} (hFormula : relation_plane_theory formula) :
    relation_composition_theory formula :=
  relation_converse_operator_theory_subset_relation_composition_theory (relation_converse_theory_subset_relation_converse_operator_theory
      (relation_plane_theory_subset_relation_converse_theory
        hFormula))
theorem relation_composition_theory_subset_relation_composition_operator_theory
    {formula : SetFormula} (hFormula : relation_composition_theory formula) :
    relation_composition_operator_theory formula :=
  Or.inr hFormula
theorem relation_plane_theory_subset_relation_composition_operator_theory
    {formula : SetFormula} (hFormula : relation_plane_theory formula) :
    relation_composition_operator_theory formula :=
  relation_composition_theory_subset_relation_composition_operator_theory (relation_converse_operator_theory_subset_relation_composition_theory
      (relation_converse_theory_subset_relation_converse_operator_theory (relation_plane_theory_subset_relation_converse_theory
          hFormula)))
/-! ## 分离公理与定义公理的实例化 -/
/-- 关系逆分离公理可在任意两个 admissible 集合项处实例化。 -/
theorem relation_converse_separation_instance_derives (relation source : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[relation_converse_theory]
      relation_converse_separation_exists
        relation source := by
  have hAxiom :
      ⊢ₘ[relation_converse_theory]
        relation_converse_separation_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hRelationInstance :=
    FirstOrder.Derives.forall_elim (term := relation) hAxiom
  have hSourceInstance :=
    FirstOrder.Derives.forall_elim (term := source) hRelationInstance
  have hRelationOpenZero :
      Term.openAt SetSort.set 0 source relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 source relation hRelation.2
  have hRelationOpenOne :
      Term.openAt SetSort.set 1 source relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 source relation hRelation.2
  have hRelationOpenTwo :
      Term.openAt SetSort.set 2 source relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 source relation hRelation.2
  have hRelationOpenThree :
      Term.openAt SetSort.set 3 source relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 3 source relation hRelation.2
  simpa [relation_converse_separation_axiom,
    relation_converse_separation_exists,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, ordered_pair_reverse_term,
    hRelationOpenZero, hRelationOpenOne,
    hRelationOpenTwo, hRelationOpenThree] using
    hSourceInstance
/-- 关系逆定义公理可在任意两个 admissible 集合项处实例化。 -/
theorem relation_converse_definition_instance_derives (relation candidate : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[relation_converse_operator_theory]
      relation_converse_definition_instance
        relation candidate := by
  have hAxiom :
      ⊢ₘ[relation_converse_operator_theory]
        relation_converse_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hRelationInstance :=
    FirstOrder.Derives.forall_elim (term := relation) hAxiom
  have hCandidateInstance :=
    FirstOrder.Derives.forall_elim (term := candidate) hRelationInstance
  have hRelationOpenZero :
      Term.openAt SetSort.set 0 candidate relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 candidate relation hRelation.2
  have hRelationOpenOne :
      Term.openAt SetSort.set 1 candidate relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 candidate relation hRelation.2
  have hRelationOpenTwo :
      Term.openAt SetSort.set 2 candidate relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 candidate relation hRelation.2
  simpa [relation_converse_definition_axiom,
    relation_converse_definition_instance,
    relation_converse_spec,
    relation_converse_condition,
    membership_specification,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, relation_converse_term,
    ordered_pair_reverse_term,
    hRelationOpenZero, hRelationOpenOne,
    hRelationOpenTwo] using hCandidateInstance
/-- 关系复合分离公理可在任意三个 admissible 集合项处实例化。 -/
theorem relation_composition_separation_instance_derives (first second source : SetTerm) (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[relation_composition_theory]
      relation_composition_separation_exists
        first second source := by
  have hAxiom :
      ⊢ₘ[relation_composition_theory]
        relation_composition_separation_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hFirstInstance :=
    FirstOrder.Derives.forall_elim (term := first) hAxiom
  have hSecondInstance :=
    FirstOrder.Derives.forall_elim (term := second) hFirstInstance
  have hSourceInstance :=
    FirstOrder.Derives.forall_elim (term := source) hSecondInstance
  have hFirstOpenZero :
      Term.openAt SetSort.set 0 source first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 source first hFirst.2
  have hFirstOpenOne :
      Term.openAt SetSort.set 1 source first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 source first hFirst.2
  have hFirstOpenTwo :
      Term.openAt SetSort.set 2 source first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 source first hFirst.2
  have hFirstOpenThree :
      Term.openAt SetSort.set 3 source first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 3 source first hFirst.2
  have hFirstOpenFourSecond :
      Term.openAt SetSort.set 4 second first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 4 second first hFirst.2
  have hSecondOpenZero :
      Term.openAt SetSort.set 0 source second =
        second :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 source second hSecond.2
  have hSecondOpenOne :
      Term.openAt SetSort.set 1 source second =
        second :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 source second hSecond.2
  have hSecondOpenTwo :
      Term.openAt SetSort.set 2 source second =
        second :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 source second hSecond.2
  have hSecondOpenThree :
      Term.openAt SetSort.set 3 source second =
        second :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 3 source second hSecond.2
  simpa [relation_composition_separation_axiom,
    relation_composition_separation_exists,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, ordered_pair_term,
    left_projection_term, right_projection_term,
    hFirstOpenZero, hFirstOpenOne,
    hFirstOpenTwo, hFirstOpenThree,
    hFirstOpenFourSecond,
    hSecondOpenZero, hSecondOpenOne,
    hSecondOpenTwo, hSecondOpenThree] using
    hSourceInstance
/-- 关系复合定义公理可在任意三个 admissible 集合项处实例化。 -/
theorem relation_composition_definition_instance_derives (first second candidate : SetTerm) (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[relation_composition_operator_theory]
      relation_composition_definition_instance
        first second candidate := by
  have hAxiom :
      ⊢ₘ[relation_composition_operator_theory]
        relation_composition_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hFirstInstance :=
    FirstOrder.Derives.forall_elim (term := first) hAxiom
  have hSecondInstance :=
    FirstOrder.Derives.forall_elim (term := second) hFirstInstance
  have hCandidateInstance :=
    FirstOrder.Derives.forall_elim (term := candidate) hSecondInstance
  have hFirstOpenZero :
      Term.openAt SetSort.set 0 candidate first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 candidate first hFirst.2
  have hFirstOpenOne :
      Term.openAt SetSort.set 1 candidate first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 candidate first hFirst.2
  have hFirstOpenTwo :
      Term.openAt SetSort.set 2 candidate first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 candidate first hFirst.2
  have hFirstOpenThree :
      Term.openAt SetSort.set 3 candidate first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 3 candidate first hFirst.2
  have hFirstOpenOneSecond :
      Term.openAt SetSort.set 1 second first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 second first hFirst.2
  have hFirstOpenTwoSecond :
      Term.openAt SetSort.set 2 second first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 second first hFirst.2
  have hFirstOpenThreeSecond :
      Term.openAt SetSort.set 3 second first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 3 second first hFirst.2
  have hSecondOpenZero :
      Term.openAt SetSort.set 0 candidate second =
        second :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 candidate second hSecond.2
  have hSecondOpenOne :
      Term.openAt SetSort.set 1 candidate second =
        second :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 candidate second hSecond.2
  have hSecondOpenTwo :
      Term.openAt SetSort.set 2 candidate second =
        second :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 candidate second hSecond.2
  have hSecondOpenThree :
      Term.openAt SetSort.set 3 candidate second =
        second :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 3 candidate second hSecond.2
  simpa [relation_composition_definition_axiom,
    relation_composition_definition_instance,
    relation_composition_spec,
    relation_composition_condition,
    membership_specification,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, relation_composition_term,
    ordered_pair_term, left_projection_term,
    right_projection_term,
    hFirstOpenZero, hFirstOpenOne,
    hFirstOpenTwo, hFirstOpenThree,
    hFirstOpenOneSecond, hFirstOpenTwoSecond,
    hFirstOpenThreeSecond,
    hSecondOpenZero, hSecondOpenOne,
    hSecondOpenTwo, hSecondOpenThree] using
    hCandidateInstance
/-! ## 点态规格、存在性与唯一性 -/
/-- 关系逆规格可在任意 admissible 元素处实例化。 -/
theorem relation_converse_spec_member_iff
    {T : SetTheory} {Γ : Context signature} (relation candidate element : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    Γ ⊢ₘ[T]
      relation_converse_spec relation candidate ⟶ₘ ((element ∈ₘ candidate) ↔ₘ
          relation_converse_member_condition
            relation element) := by
  nd_apply FirstOrder.Derives.impIntro
  have hSpec :
      relation_converse_spec relation candidate :: Γ
        ⊢ₘ[T]
        relation_converse_spec relation candidate :=
    .assumption (by simp)
  have hAt :=
    FirstOrder.Derives.forall_elim (term := element) hSpec
  have hCandidateOpen :
      Term.openAt SetSort.set 0
          element candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element candidate hCandidate.2
  have hRelationOpenZero :
      Term.openAt SetSort.set 0
          element relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element relation hRelation.2
  have hRelationOpenOne :
      Term.openAt SetSort.set 1
          element relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 element relation hRelation.2
  have hRelationOpenTwo :
      Term.openAt SetSort.set 2
          element relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 element relation hRelation.2
  simpa [relation_converse_spec,
    relation_converse_condition,
    relation_converse_member_condition,
    membership_specification,
    Formula.openAt, Formula.next_depth,
    Term.openAt, ordered_pair_reverse_term,
    hCandidateOpen, hRelationOpenZero,
    hRelationOpenOne,
    hRelationOpenTwo] using hAt
/-- 关系复合规格可在任意 admissible 元素处实例化。 -/
theorem relation_composition_spec_member_iff
    {T : SetTheory} {Γ : Context signature} (first second candidate element : SetTerm) (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    Γ ⊢ₘ[T]
      relation_composition_spec
          first second candidate ⟶ₘ ((element ∈ₘ candidate) ↔ₘ
          relation_composition_member_condition
            first second element) := by
  nd_apply FirstOrder.Derives.impIntro
  have hSpec :
      relation_composition_spec
          first second candidate :: Γ
        ⊢ₘ[T]
          relation_composition_spec
            first second candidate :=
    .assumption (by simp)
  have hAt :=
    FirstOrder.Derives.forall_elim (term := element) hSpec
  have hCandidateOpen :
      Term.openAt SetSort.set 0
          element candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element candidate hCandidate.2
  have hFirstOpenZero :
      Term.openAt SetSort.set 0
          element first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element first hFirst.2
  have hFirstOpenOne :
      Term.openAt SetSort.set 1
          element first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 element first hFirst.2
  have hFirstOpenTwo :
      Term.openAt SetSort.set 2
          element first =
        first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 element first hFirst.2
  have hSecondOpenOne :
      Term.openAt SetSort.set 1
          element second =
        second :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 element second hSecond.2
  have hSecondOpenZero :
      Term.openAt SetSort.set 0
          element second =
        second :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element second hSecond.2
  have hSecondOpenTwo :
      Term.openAt SetSort.set 2
          element second =
        second :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 element second hSecond.2
  simpa [relation_composition_spec,
    relation_composition_condition,
    relation_composition_member_condition,
    membership_specification,
    Formula.openAt, Formula.next_depth,
    Term.openAt, ordered_pair_term,
    left_projection_term, right_projection_term,
    hCandidateOpen, hFirstOpenZero,
    hFirstOpenOne,
    hFirstOpenTwo, hSecondOpenOne,
    hSecondOpenZero, hSecondOpenTwo] using hAt
/-- 任意 admissible 集合都有关系逆候选。 -/
theorem relation_converse_exists_derives (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_converse_theory]
      relation_converse_exists relation := by
  let source :=
    ranₘ(relation) ×ₘ domₘ(relation)
  have hSource :
      Term.Admissible source SetSort.set :=
    cartesian_product_term_admissible (ranₘ(relation)) (domₘ(relation)) (range_term_admissible relation hRelation) (domain_term_admissible relation hRelation)
  simpa [source, relation_converse_exists,
    relation_converse_condition,
    relation_converse_separation_exists] using
    relation_converse_separation_instance_derives
      relation source hRelation hSource
/-- 文献定理 2.38(1)：关系复合候选存在。 -/
theorem relation_composition_exists_derives (first second : SetTerm) (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_composition_theory]
      relation_composition_exists first second := by
  let source :=
    domₘ(first) ×ₘ ranₘ(second)
  have hSource :
      Term.Admissible source SetSort.set :=
    cartesian_product_term_admissible (domₘ(first)) (ranₘ(second)) (domain_term_admissible first hFirst) (range_term_admissible second hSecond)
  simpa [source, relation_composition_exists,
    relation_composition_condition,
    relation_composition_separation_exists] using
    relation_composition_separation_instance_derives
      first second source hFirst hSecond hSource
/-- 同一关系的两个关系逆候选相等。 -/
theorem relation_converse_unique (relation first second : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[extensionality_theory]
      relation_converse_spec relation first ⟶ₘ
        relation_converse_spec relation second ⟶ₘ (first ≐ₘ second) := by
  simpa [relation_converse_spec] using
    membership_specification_unique
      first second (relation_converse_condition relation)
      hFirst hSecond (relation_converse_spec_admissible
        hRelation hFirst) (relation_converse_spec_admissible
        hRelation hSecond)
/-- 文献定理 2.38(2)：同一对关系的两个复合候选相等。 -/
theorem relation_composition_unique (first second left right : SetTerm) (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[extensionality_theory]
      relation_composition_spec first second left ⟶ₘ
        relation_composition_spec first second right ⟶ₘ (left ≐ₘ right) := by
  simpa [relation_composition_spec] using
    membership_specification_unique
      left right (relation_composition_condition first second)
      hLeft hRight (relation_composition_spec_admissible
        hFirst hSecond hLeft) (relation_composition_spec_admissible
        hFirst hSecond hRight)
/-- 关系逆函数项在关系谓词背景下满足关系逆规格。 -/
theorem is_relation_converse_term_spec (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_converse_operator_theory]
      is_relation_formula relation ⟶ₘ
        relation_converse_spec
          relation (converseₘ(relation)) := by
  nd_apply FirstOrder.Derives.impIntro
  let predicate := is_relation_formula relation
  have hDefinition :
      [predicate]
        ⊢ₘ[relation_converse_operator_theory]
          relation_converse_definition_instance
            relation (converseₘ(relation)) :=
    FirstOrder.Derives.context_weaken_cons (relation_converse_definition_instance_derives
        relation (converseₘ(relation))
        hRelation (relation_converse_term_admissible
          relation hRelation))
  have hGraph :=
    FirstOrder.Derives.impElim
      hDefinition (show
        [predicate]
          ⊢ₘ[relation_converse_operator_theory]
            is_relation_formula relation from
        .assumption (by simp [predicate]))
  exact FirstOrder.Derives.iffElimRight
    hGraph (FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) (converseₘ(relation)))
/-- 关系复合函数项在两个关系谓词背景下满足复合规格。 -/
theorem are_relations_composition_term_spec (first second : SetTerm) (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_composition_operator_theory] (is_relation_formula first ∧ₘ
          is_relation_formula second) ⟶ₘ
        relation_composition_spec
          first second (second ∘ₘ first) := by
  nd_apply FirstOrder.Derives.impIntro
  let predicate :=
    is_relation_formula first ∧ₘ
      is_relation_formula second
  have hDefinition :
      [predicate]
        ⊢ₘ[relation_composition_operator_theory]
          relation_composition_definition_instance
            first second (second ∘ₘ first) :=
    FirstOrder.Derives.context_weaken_cons (relation_composition_definition_instance_derives
        first second (second ∘ₘ first)
        hFirst hSecond (relation_composition_term_admissible
          second first hSecond hFirst))
  have hGraph :=
    FirstOrder.Derives.impElim
      hDefinition (show
        [predicate]
          ⊢ₘ[relation_composition_operator_theory]
            is_relation_formula first ∧ₘ
              is_relation_formula second from
        .assumption (by simp [predicate]))
  exact FirstOrder.Derives.iffElimRight
    hGraph (FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) (second ∘ₘ first))
/-! ## 复合的关系性 -/
/-- 文献定理 2.39(1)：复合规格中的候选包含于定义域和值域的笛卡尔积。 -/
theorem relation_composition_spec_subset_product (first second candidate : SetTerm) (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[relation_composition_theory]
      relation_composition_spec first second candidate ⟶ₘ (candidate ⊆ₘ (domₘ(first) ×ₘ ranₘ(second))) := by
  let source := domₘ(first) ×ₘ ranₘ(second)
  have hSource :
      Term.Admissible source SetSort.set :=
    cartesian_product_term_admissible (domₘ(first)) (ranₘ(second)) (domain_term_admissible first hFirst) (range_term_admissible second hSecond)
  have hSubset :
      ⊢ₘ[subset_theory]
        membership_specification candidate ((bₛ#0 ∈ₘ source) ∧ₘ (is_ordered_pair_formula bₛ#0 ∧ₘ (∃ₘ[SetSort.set], (⟨(bₛ#1)₀ₘ, bₛ#0⟩ₘ ∈ₘ first) ∧ₘ
                    (⟨bₛ#0, (bₛ#1)₁ₘ⟩ₘ ∈ₘ second)))) ⟶ₘ (candidate ⊆ₘ source) :=
    membership_specification_subset_source
      candidate source (is_ordered_pair_formula bₛ#0 ∧ₘ (∃ₘ[SetSort.set], (⟨(bₛ#1)₀ₘ, bₛ#0⟩ₘ ∈ₘ first) ∧ₘ (⟨bₛ#0, (bₛ#1)₁ₘ⟩ₘ ∈ₘ second)))
      hCandidate hSource (by
        simpa [source,
          relation_composition_spec,
          relation_composition_condition] using (relation_composition_spec_admissible
            hFirst hSecond hCandidate))
  simpa [source, relation_composition_spec,
    relation_composition_condition] using (FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        relation_plane_theory_subset_relation_composition_theory (subset_theory_subset_relation_plane_theory
            hFormula))
      hSubset)
/-- 笛卡尔积成员条件蕴含有序对的存在坐标条件。 -/
theorem cartesian_product_member_condition_implies_is_ordered_pair_condition (left right element : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ
      cartesian_product_member_condition left right element ⟶ₘ
        is_ordered_pair_condition element := by
  let outer :=
    FreshVariable.fresh_id SetSort.set
      [cartesian_product_member_condition
        left right element,
       is_ordered_pair_condition element]
  let inner :=
    FreshVariable.fresh_id SetSort.set
      [cartesian_product_member_condition
        left right element,
       is_ordered_pair_condition element, (x#outer ∈ₘ left)]
  let inner_left : SetFormula := (x#outer ∈ₘ left) ∧ₘ ((x#inner ∈ₘ right) ∧ₘ (element ≐ₘ ⟨x#outer, x#inner⟩ₘ))
  let inner_right : SetFormula :=
    element ≐ₘ ⟨x#outer, x#inner⟩ₘ
  have hOuterNeInner : outer ≠ inner := by
    intro hEqual
    have hFresh : (SetSort.set, inner) ∉
          Formula.freeSupport (x#outer ∈ₘ left) := by
      dsimp [inner]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    rw [hEqual] at hFresh
    have hSupport : (SetSort.set, inner) ∈
          Formula.freeSupport (x#inner ∈ₘ left) := by
      simp only [Formula.freeSupport,
        Term.freeSupport, Term.freeSupportList]
      exact List.mem_cons_self
    exact hFresh hSupport
  have hInnerFreshLeft : (SetSort.set, inner) ∉
        Term.freeSupport left := by
    intro hMember
    have hFresh : (SetSort.set, inner) ∉
          Formula.freeSupport (cartesian_product_member_condition
              left right element) := by
      dsimp [inner]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    apply hFresh
    simp only [cartesian_product_member_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.nil_append,
      List.append_nil]
    exact List.mem_append_left (Term.freeSupport right ++ Term.freeSupport element)
      hMember
  have hInnerFreshRight : (SetSort.set, inner) ∉
        Term.freeSupport right := by
    intro hMember
    have hFresh : (SetSort.set, inner) ∉
          Formula.freeSupport (cartesian_product_member_condition
              left right element) := by
      dsimp [inner]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    apply hFresh
    simp only [cartesian_product_member_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.nil_append,
      List.append_nil]
    exact List.mem_append_right (Term.freeSupport left) (List.mem_append_left (Term.freeSupport element) hMember)
  have hInnerFreshElement : (SetSort.set, inner) ∉
        Term.freeSupport element := by
    intro hMember
    have hFresh : (SetSort.set, inner) ∉
          Formula.freeSupport (cartesian_product_member_condition
              left right element) := by
      dsimp [inner]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    apply hFresh
    simp only [cartesian_product_member_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.nil_append,
      List.append_nil]
    exact List.mem_append_right (Term.freeSupport left) (List.mem_append_right (Term.freeSupport right) hMember)
  have hOuterFreshLeft : (SetSort.set, outer) ∉
        Term.freeSupport left := by
    intro hMember
    have hFresh : (SetSort.set, outer) ∉
          Formula.freeSupport (cartesian_product_member_condition
              left right element) := by
      dsimp [outer]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    apply hFresh
    simp only [cartesian_product_member_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.nil_append,
      List.append_nil]
    exact List.mem_append_left (Term.freeSupport right ++ Term.freeSupport element)
      hMember
  have hOuterFreshRight : (SetSort.set, outer) ∉
        Term.freeSupport right := by
    intro hMember
    have hFresh : (SetSort.set, outer) ∉
          Formula.freeSupport (cartesian_product_member_condition
              left right element) := by
      dsimp [outer]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    apply hFresh
    simp only [cartesian_product_member_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.nil_append,
      List.append_nil]
    exact List.mem_append_right (Term.freeSupport left) (List.mem_append_left (Term.freeSupport element) hMember)
  have hOuterFreshElement : (SetSort.set, outer) ∉
        Term.freeSupport element := by
    intro hMember
    have hFresh : (SetSort.set, outer) ∉
          Formula.freeSupport (cartesian_product_member_condition
              left right element) := by
      dsimp [outer]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    apply hFresh
    simp only [cartesian_product_member_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.nil_append,
      List.append_nil]
    exact List.mem_append_right (Term.freeSupport left) (List.mem_append_right (Term.freeSupport right) hMember)
  have hInnerCloseLeft :
      Term.closeFreeAt SetSort.set inner 0 left =
        left :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set inner 0 left hLeft.2
      hInnerFreshLeft
  have hInnerCloseRight :
      Term.closeFreeAt SetSort.set inner 0 right =
        right :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set inner 0 right hRight.2
      hInnerFreshRight
  have hInnerCloseElement :
      Term.closeFreeAt SetSort.set inner 0 element =
        element :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set inner 0 element hElement.2
      hInnerFreshElement
  have hOuterCloseLeft :
      Term.closeFreeAt SetSort.set outer 1 left =
        left :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set outer 1 left hLeft.2
      hOuterFreshLeft
  have hOuterCloseRight :
      Term.closeFreeAt SetSort.set outer 1 right =
        right :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set outer 1 right hRight.2
      hOuterFreshRight
  have hOuterCloseElement :
      Term.closeFreeAt SetSort.set outer 1 element =
        element :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set outer 1 element hElement.2
      hOuterFreshElement
  have hInner :
      ⊢ₘ inner_left ⟶ₘ inner_right := by
    have hInnerLeftAdmissible :
        Formula.Admissible inner_left := by
      dsimp [inner_left]
      exact Formula.Admissible.conj (membership_formula_admissible (set_variable_admissible outer)
          hLeft) (Formula.Admissible.conj (membership_formula_admissible (set_variable_admissible inner)
            hRight) (Formula.Admissible.equal
            hElement (ordered_pair_term_admissible (x#outer) (x#inner) (set_variable_admissible outer) (set_variable_admissible inner))))
    nd_apply FirstOrder.Derives.impIntro
    have hInnerAssumption :
        [inner_left] ⊢ₘ inner_left :=
      FirstOrder.Derives.assumption (by simp)
    exact FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimRight
        hInnerAssumption)
  have hInnerLift :=
    FirstOrder.Metatheory.Derives.exists_imp_mono (T := (Theory.empty : SetTheory)) (Γ := []) (sort := SetSort.set) (eigen := inner) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        cases hFormula)
      hInner
  have hOuterLift :=
    FirstOrder.Metatheory.Derives.exists_imp_mono (T := (Theory.empty : SetTheory)) (Γ := []) (sort := SetSort.set) (eigen := outer) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        cases hFormula)
      hInnerLift
  simpa [cartesian_product_member_condition,
    is_ordered_pair_condition,
    inner_left, inner_right,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt, set_variable,
    set_bound_variable, hOuterNeInner,
    hInnerCloseLeft, hInnerCloseRight,
    hInnerCloseElement, hOuterCloseLeft,
    hOuterCloseRight, hOuterCloseElement] using
    hOuterLift
/-- 笛卡尔积的任意成员都是有序对。 -/
theorem cartesian_product_member_is_ordered_pair (left right element : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[relation_plane_theory] (element ∈ₘ (left ×ₘ right)) ⟶ₘ
        is_ordered_pair_formula element := by
  have hProduct :
      Term.Admissible (left ×ₘ right) SetSort.set :=
    cartesian_product_term_admissible
      left right hLeft hRight
  have hSpec :
      ⊢ₘ[relation_plane_theory]
        cartesian_product_spec
          left right (left ×ₘ right) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        cartesian_product_operator_theory_subset_relation_plane_theory
          hFormula) (cartesian_product_term_spec_derives
        left right hLeft hRight)
  have hPoint :
      ⊢ₘ[relation_plane_theory] ((element ∈ₘ (left ×ₘ right)) ↔ₘ ((element ∈ₘ
              cartesian_product_bound_term left right) ∧ₘ
            cartesian_product_member_condition
              left right element)) :=
    FirstOrder.Derives.impElim (cartesian_product_spec_member_iff (T := relation_plane_theory) (Γ := [])
        left right (left ×ₘ right) element
        hLeft hRight hProduct hElement)
      hSpec
  have hConditionBridge :
      ⊢ₘ[relation_plane_theory]
        cartesian_product_member_condition
            left right element ⟶ₘ
          is_ordered_pair_condition element :=
    FirstOrder.Derives.theory_weaken (by simp [Theory.empty]) (cartesian_product_member_condition_implies_is_ordered_pair_condition
        left right element hLeft hRight hElement)
  have hDefinition :
      ⊢ₘ[relation_plane_theory]
        is_ordered_pair_definition_instance element :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        relation_function_theory_subset_relation_plane_theory
          hFormula) (is_ordered_pair_definition_instance_derives
        element hElement)
  derive_prop
/-- 任意两个集合的笛卡尔积都是关系。 -/
theorem cartesian_product_is_relation (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      is_relation_formula (left ×ₘ right) := by
  let product := left ×ₘ right
  let relation_body : SetFormula := (bₛ#0 ∈ₘ product) ⟶ₘ
      is_ordered_pair_formula bₛ#0
  let member :=
    FreshVariable.fresh_id SetSort.set
      [relation_body]
  have hProduct :
      Term.Admissible product SetSort.set :=
    cartesian_product_term_admissible
      left right hLeft hRight
  have hMemberFreshBody : (SetSort.set, member) freshForₘ
        relation_body := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hProductOpen :
      Term.openAt SetSort.set 0 (x#member) product =
        product :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member)
      product hProduct.2
  have hPoint :
      ⊢ₘ[relation_plane_theory] (x#member ∈ₘ product) ⟶ₘ
          is_ordered_pair_formula (x#member) := by
    simpa [product] using
      cartesian_product_member_is_ordered_pair
        left right (x#member)
        hLeft hRight (set_variable_admissible member)
  have hPointOpened :
      ⊢ₘ[relation_plane_theory]
        Formula.openAt SetSort.set 0 (x#member) relation_body := by
    simpa [relation_body, Formula.openAt,
      Term.openAt, hProductOpen] using hPoint
  have hCondition :
      ⊢ₘ[relation_plane_theory]
        is_relation_condition product := by
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := relation_plane_theory) (Γ := []) (sort := SetSort.set) (eigen := member) (body :=
          Formula.openAt SetSort.set 0 (x#member) relation_body) (by
          intro formula hFormula
          have hSentence :=
            relation_plane_theory_sentence hFormula
          rw [hSentence.2]
          simp) (by
          intro formula hFormula
          cases hFormula)
        hPointOpened
    simpa [is_relation_condition,
      Formula.closeFreeAt_openAt
        SetSort.set member 0 relation_body
        hMemberFreshBody] using hGeneralized
  have hDefinition :
      ⊢ₘ[relation_plane_theory]
        is_relation_definition_instance product :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        relation_predicate_theory_subset_relation_plane_theory
          hFormula) (is_relation_definition_instance_derives
        product hProduct)
  exact FirstOrder.Derives.iffElimLeft
    hDefinition hCondition
/-- 关系的任意子集仍是关系。 -/
theorem is_relation_of_subset (relation candidate : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[relation_plane_theory]
      is_relation_formula relation ⟶ₘ (candidate ⊆ₘ relation) ⟶ₘ
          is_relation_formula candidate := by
  let relation_formula :=
    is_relation_formula relation
  let subset_formula : SetFormula :=
    candidate ⊆ₘ relation
  let relation_body : SetFormula := (bₛ#0 ∈ₘ candidate) ⟶ₘ
      is_ordered_pair_formula bₛ#0
  let member :=
    FreshVariable.fresh_id SetSort.set
      [relation_formula, subset_formula,
        relation_body]
  let Γ : Context signature :=
    [subset_formula, relation_formula]
  have hMemberFreshRelation : (SetSort.set, member) freshForₘ
        relation_formula := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hMemberFreshSubset : (SetSort.set, member) freshForₘ
        subset_formula := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hMemberFreshBody : (SetSort.set, member) freshForₘ
        relation_body := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hCandidateOpen :
      Term.openAt SetSort.set 0 (x#member) candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member)
      candidate hCandidate.2
  have hRelationOpen :
      Term.openAt SetSort.set 0 (x#member) relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member)
      relation hRelation.2
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hRelationFormula :
      Γ ⊢ₘ[relation_plane_theory]
        is_relation_formula relation := by
    simpa [Γ, relation_formula] using (show
        Γ ⊢ₘ[relation_plane_theory]
          relation_formula from
        .assumption (by simp [Γ]))
  have hSubsetFormula :
      Γ ⊢ₘ[relation_plane_theory]
        candidate ⊆ₘ relation := by
    simpa [Γ, subset_formula] using (show
        Γ ⊢ₘ[relation_plane_theory]
          subset_formula from
        .assumption (by simp [Γ]))
  have hSubsetDefinition :
      Γ ⊢ₘ[relation_plane_theory]
        subset_definition_instance
          candidate relation :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.theory_weaken (fun _ hFormula =>
            subset_theory_subset_relation_plane_theory
              hFormula) (subset_definition_instance_derives_of_admissible
            candidate relation hCandidate hRelation)
  have hSubsetCondition :
      Γ ⊢ₘ[relation_plane_theory]
        subset_condition candidate relation :=
    FirstOrder.Derives.iffElimRight
      hSubsetDefinition hSubsetFormula
  have hSubsetAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := x#member) hSubsetCondition
  have hSubsetAt :
      Γ ⊢ₘ[relation_plane_theory] (x#member ∈ₘ candidate) ⟶ₘ (x#member ∈ₘ relation) := by
    simpa [subset_condition,
      Formula.openAt, Term.openAt,
      hCandidateOpen, hRelationOpen] using
      hSubsetAtRaw
  have hRelationPoint :
      Γ ⊢ₘ[relation_plane_theory]
        is_relation_formula relation ⟶ₘ (x#member ∈ₘ relation) ⟶ₘ
            is_ordered_pair_formula (x#member) :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.theory_weaken (fun _ hFormula =>
            relation_predicate_theory_subset_relation_plane_theory
              hFormula) (is_relation_member_is_ordered_pair
            relation (x#member)
            hRelation (set_variable_admissible member))
  have hMemberImp :
      Γ ⊢ₘ[relation_plane_theory] (x#member ∈ₘ candidate) ⟶ₘ
          is_ordered_pair_formula (x#member) := by
    have hMemberAdmissible :
        Formula.Admissible (x#member ∈ₘ candidate) :=
      membership_formula_admissible (set_variable_admissible member)
        hCandidate
    nd_apply FirstOrder.Derives.impIntro
    have hMember : (x#member ∈ₘ candidate) :: Γ
          ⊢ₘ[relation_plane_theory]
            x#member ∈ₘ candidate :=
      .assumption (by simp)
    have hSubsetAtInContext :=
      FirstOrder.Derives.context_weaken_cons (assumption :=
          x#member ∈ₘ candidate)
        hSubsetAt
    have hRelationPointInContext :=
      FirstOrder.Derives.context_weaken_cons (assumption :=
          x#member ∈ₘ candidate)
        hRelationPoint
    have hRelationFormulaInContext :=
      FirstOrder.Derives.context_weaken_cons (assumption :=
          x#member ∈ₘ candidate)
        hRelationFormula
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
        hRelationPointInContext
        hRelationFormulaInContext) (FirstOrder.Derives.impElim
        hSubsetAtInContext hMember)
  have hMemberImpOpened :
      Γ ⊢ₘ[relation_plane_theory]
        Formula.openAt SetSort.set 0 (x#member) relation_body := by
    simpa [relation_body, Formula.openAt,
      Term.openAt, hCandidateOpen] using
      hMemberImp
  have hCandidateCondition :
      Γ ⊢ₘ[relation_plane_theory]
        is_relation_condition candidate := by
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := relation_plane_theory) (Γ := Γ) (sort := SetSort.set) (eigen := member) (body :=
          Formula.openAt SetSort.set 0 (x#member) relation_body) (by
          intro formula hFormula
          have hSentence :=
            relation_plane_theory_sentence hFormula
          rw [hSentence.2]
          simp) (by
          intro formula hFormula
          rcases List.mem_cons.mp hFormula with
            rfl | hFormula
          · exact hMemberFreshSubset
          · rcases List.mem_singleton.mp hFormula with rfl
            exact hMemberFreshRelation)
        hMemberImpOpened
    simpa [is_relation_condition,
      Formula.closeFreeAt_openAt
        SetSort.set member 0 relation_body
        hMemberFreshBody] using hGeneralized
  have hCandidateDefinition :
      Γ ⊢ₘ[relation_plane_theory]
        is_relation_definition_instance candidate :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.theory_weaken (fun _ hFormula =>
            relation_predicate_theory_subset_relation_plane_theory
              hFormula) (is_relation_definition_instance_derives
            candidate hCandidate)
  exact FirstOrder.Derives.iffElimLeft
    hCandidateDefinition hCandidateCondition
/-- 文献定理 2.39(2) 的强化形式：笛卡尔积的任意子集都是关系。 -/
theorem subset_cartesian_product_is_relation (left right candidate : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[relation_plane_theory] (candidate ⊆ₘ (left ×ₘ right)) ⟶ₘ
        is_relation_formula candidate := by
  have hProductRelation :=
    cartesian_product_is_relation
      left right hLeft hRight
  have hSubsetClosure :=
    is_relation_of_subset (left ×ₘ right) candidate (cartesian_product_term_admissible
        left right hLeft hRight)
      hCandidate
  derive_prop
/-- 文献定理 2.39(3)：满足复合规格的集合是关系。 -/
theorem relation_composition_spec_is_relation (first second candidate : SetTerm) (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[relation_composition_theory]
      relation_composition_spec first second candidate ⟶ₘ
        is_relation_formula candidate := by
  have hSubset :=
    relation_composition_spec_subset_product
      first second candidate
      hFirst hSecond hCandidate
  have hRelation :
      ⊢ₘ[relation_composition_theory] (candidate ⊆ₘ (domₘ(first) ×ₘ ranₘ(second))) ⟶ₘ
          is_relation_formula candidate :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        relation_plane_theory_subset_relation_composition_theory
          hFormula) (subset_cartesian_product_is_relation (domₘ(first)) (ranₘ(second)) candidate (domain_term_admissible first hFirst)
        (range_term_admissible second hSecond)
        hCandidate)
  derive_prop
/-- 文献定理 2.39(4)：两个关系的复合函数项仍是关系。 -/
theorem are_relations_composition_is_relation (first second : SetTerm) (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_composition_operator_theory] (is_relation_formula first ∧ₘ
          is_relation_formula second) ⟶ₘ
        is_relation_formula (second ∘ₘ first) := by
  have hSpec :=
    are_relations_composition_term_spec
      first second hFirst hSecond
  have hSpecRelation :
      ⊢ₘ[relation_composition_operator_theory]
        relation_composition_spec
            first second (second ∘ₘ first) ⟶ₘ
          is_relation_formula (second ∘ₘ first) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        relation_composition_theory_subset_relation_composition_operator_theory
          hFormula) (relation_composition_spec_is_relation
        first second (second ∘ₘ first)
        hFirst hSecond (relation_composition_term_admissible
          second first hSecond hFirst))
  derive_prop
/-! ## 全称闭包接口 -/
/-- 关系逆候选存在性的单变量全称闭包。 -/
theorem relation_converse_exists_forall (relation : FreeVarId) :
    ⊢ₘ[relation_converse_theory]
      ∀ₘ[SetSort.set, relation],
        relation_converse_exists (x#relation) := by
  derive_close (relation) using
    relation_converse_exists_derives (x#relation) (set_variable_admissible relation)
/-- 关系逆唯一性的三变量全称闭包。 -/
theorem relation_converse_unique_forall (relation first second : FreeVarId) :
    ⊢ₘ[relation_converse_theory]
      ∀ₘ[SetSort.set, relation],
        ∀ₘ[SetSort.set, first],
          ∀ₘ[SetSort.set, second],
            relation_converse_spec (x#relation) (x#first) ⟶ₘ
              relation_converse_spec (x#relation) (x#second) ⟶ₘ (x#first ≐ₘ x#second) := by
  have hUnique :
      ⊢ₘ[relation_converse_theory]
        relation_converse_spec (x#relation) (x#first) ⟶ₘ
          relation_converse_spec (x#relation) (x#second) ⟶ₘ (x#first ≐ₘ x#second) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        relation_plane_theory_subset_relation_converse_theory (relation_predicate_theory_subset_relation_plane_theory
            (relation_base_theory_subset_relation_predicate_theory (extensionality_theory_subset_relation_base_theory
                hFormula)))) (relation_converse_unique (x#relation) (x#first) (x#second) (set_variable_admissible relation) (set_variable_admissible first)
        (set_variable_admissible second))
  derive_close (relation, first, second) using hUnique
/-- 规范关系逆项规格的单变量全称闭包。 -/
theorem is_relation_converse_term_spec_forall (relation : FreeVarId) :
    ⊢ₘ[relation_converse_operator_theory]
      ∀ₘ[SetSort.set, relation],
        is_relation_formula (x#relation) ⟶ₘ
          relation_converse_spec (x#relation) (converseₘ(x#relation)) := by
  derive_close (relation) using
    is_relation_converse_term_spec (x#relation) (set_variable_admissible relation)
/-- 文献定理 2.38(1)：关系复合存在性的双变量全称闭包。 -/
theorem relation_composition_exists_forall (first second : FreeVarId) :
    ⊢ₘ[relation_composition_theory]
      ∀ₘ[SetSort.set, first],
        ∀ₘ[SetSort.set, second],
          relation_composition_exists (x#first) (x#second) := by
  derive_close (first, second) using
    relation_composition_exists_derives (x#first) (x#second) (set_variable_admissible first) (set_variable_admissible second)
/-- 文献定理 2.38(2)：关系复合唯一性的四变量全称闭包。 -/
theorem relation_composition_unique_forall (first second left right : FreeVarId) :
    ⊢ₘ[relation_composition_theory]
      ∀ₘ[SetSort.set, first],
        ∀ₘ[SetSort.set, second],
          ∀ₘ[SetSort.set, left],
            ∀ₘ[SetSort.set, right],
              relation_composition_spec (x#first) (x#second) (x#left) ⟶ₘ
                relation_composition_spec (x#first) (x#second) (x#right) ⟶ₘ (x#left ≐ₘ x#right) := by
  have hUnique :
      ⊢ₘ[relation_composition_theory]
        relation_composition_spec (x#first) (x#second) (x#left) ⟶ₘ
          relation_composition_spec (x#first) (x#second) (x#right) ⟶ₘ (x#left ≐ₘ x#right) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        relation_plane_theory_subset_relation_composition_theory (relation_predicate_theory_subset_relation_plane_theory
            (relation_base_theory_subset_relation_predicate_theory (extensionality_theory_subset_relation_base_theory
                hFormula)))) (relation_composition_unique (x#first) (x#second) (x#left) (x#right) (set_variable_admissible first)
        (set_variable_admissible second) (set_variable_admissible left) (set_variable_admissible right))
  derive_close (first, second, left, right) using hUnique
/-- 规范关系复合项规格的双变量全称闭包。 -/
theorem are_relations_composition_term_spec_forall (first second : FreeVarId) :
    ⊢ₘ[relation_composition_operator_theory]
      ∀ₘ[SetSort.set, first],
        ∀ₘ[SetSort.set, second], (is_relation_formula (x#first) ∧ₘ
              is_relation_formula (x#second)) ⟶ₘ
            relation_composition_spec (x#first) (x#second) ((x#second) ∘ₘ (x#first)) := by
  derive_close (first, second) using
    are_relations_composition_term_spec (x#first) (x#second) (set_variable_admissible first) (set_variable_admissible second)
/-- 文献定理 2.39(1) 的三变量全称闭包。 -/
theorem relation_composition_spec_subset_product_forall (first second candidate : FreeVarId) :
    ⊢ₘ[relation_composition_theory]
      ∀ₘ[SetSort.set, first],
        ∀ₘ[SetSort.set, second],
          ∀ₘ[SetSort.set, candidate],
            relation_composition_spec (x#first) (x#second) (x#candidate) ⟶ₘ (x#candidate ⊆ₘ (domₘ(x#first) ×ₘ ranₘ(x#second))) := by
  derive_close (first, second, candidate) using
    relation_composition_spec_subset_product (x#first) (x#second) (x#candidate) (set_variable_admissible first) (set_variable_admissible second)
      (set_variable_admissible candidate)
/-- 文献定理 2.39(2) 的三变量全称闭包。 -/
theorem subset_cartesian_product_is_relation_forall (left right candidate : FreeVarId) :
    ⊢ₘ[relation_plane_theory]
      ∀ₘ[SetSort.set, left],
        ∀ₘ[SetSort.set, right],
          ∀ₘ[SetSort.set, candidate], (x#candidate ⊆ₘ (x#left ×ₘ x#right)) ⟶ₘ
              is_relation_formula (x#candidate) := by
  derive_close (left, right, candidate) using
    subset_cartesian_product_is_relation (x#left) (x#right) (x#candidate) (set_variable_admissible left) (set_variable_admissible right)
      (set_variable_admissible candidate)
/-- 文献定理 2.39(3) 的三变量全称闭包。 -/
theorem relation_composition_spec_is_relation_forall (first second candidate : FreeVarId) :
    ⊢ₘ[relation_composition_theory]
      ∀ₘ[SetSort.set, first],
        ∀ₘ[SetSort.set, second],
          ∀ₘ[SetSort.set, candidate],
            relation_composition_spec (x#first) (x#second) (x#candidate) ⟶ₘ
              is_relation_formula (x#candidate) := by
  derive_close (first, second, candidate) using
    relation_composition_spec_is_relation (x#first) (x#second) (x#candidate) (set_variable_admissible first) (set_variable_admissible second)
      (set_variable_admissible candidate)
/-- 文献定理 2.39(4) 的双变量全称闭包。 -/
theorem are_relations_composition_is_relation_forall (first second : FreeVarId) :
    ⊢ₘ[relation_composition_operator_theory]
      ∀ₘ[SetSort.set, first],
        ∀ₘ[SetSort.set, second], (is_relation_formula (x#first) ∧ₘ
              is_relation_formula (x#second)) ⟶ₘ
            is_relation_formula ((x#second) ∘ₘ (x#first)) := by
  derive_close (first, second) using
    are_relations_composition_is_relation (x#first) (x#second) (set_variable_admissible first) (set_variable_admissible second)
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
