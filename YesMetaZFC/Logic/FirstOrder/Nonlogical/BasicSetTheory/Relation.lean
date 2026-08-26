import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationFunction
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Union
/-!
# 关系、定义域与值域
本模块把文献中的关系谓词 `GX`、定义域和值域构造整理成共享的坐标筛选框架。
`GX` 与 `YXD` 只在注释中保留为文献索引；公共接口使用 `is_relation` 与
`is_ordered_pair`。
文献为双重并集另外引入函数符号。新核已有一元并集原子项，因此直接使用
`⋃ₘ ⋃ₘ relation`，只补充 proof-carrying 规格与存在性接口。定义域和值域的
存在性均来自闭的“任意关系参数、任意母集”的分离实例，而不是把最终结论本身
作为公理。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 关系谓词 -/
/-- 文献 `GX` 的现代规格：关系的每个成员都是规范有序对。 -/
def is_relation_condition (relation : SetTerm) : SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ relation) ⟶ₘ
      is_ordered_pair_formula bₛ#0
/-- 关系谓词符号的开放定义实例。 -/
def is_relation_definition_instance (relation : SetTerm) :
    SetFormula :=
  is_relation_formula relation ↔ₘ
    is_relation_condition relation
/-- 关系谓词符号的定义公理。 -/
def is_relation_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_relation_definition_instance (x#0)
/-! ## 双重并集 -/
/-- 文献双重并集运算的非冗余表示。 -/
abbrev double_union_term (relation : SetTerm) : SetTerm :=
  ⋃ₘ ⋃ₘ relation
/-- 双重并集成员条件。 -/
def double_union_member_condition (relation element : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set], (bₛ#0 ∈ₘ ⋃ₘ relation) ∧ₘ (element ∈ₘ bₛ#0)
/-- 双重并集复合项的平凡存在公式。 -/
def double_union_term_exists (relation : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    bₛ#0 ≐ₘ double_union_term relation
/-! ## 共享坐标筛选核心 -/
/-- 关系中有序对的两个坐标。 -/
inductive RelationCoordinate where
  | domain
  | range
  deriving DecidableEq, Repr
/-- 按坐标选择有序对投影项。 -/
def relation_coordinate_projection_term (coordinate : RelationCoordinate) (pair : SetTerm) :
    SetTerm :=
  match coordinate with
  | .domain => (pair)₀ₘ
  | .range => (pair)₁ₘ
/-- 一个元素由关系中某个有序对的指定坐标取得。 -/
def relation_coordinate_member_condition (coordinate : RelationCoordinate) (relation element : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set], (bₛ#0 ∈ₘ relation) ∧ₘ (element ≐ₘ
        relation_coordinate_projection_term
          coordinate bₛ#0)
/--
`candidate` 是 `relation` 的指定坐标集合。
候选集从 `⋃ₘ ⋃ₘ relation` 中分离；关系成员见证保持为内层 bound 变量，因此
不会发生 locally nameless 捕获。
-/
def relation_coordinate_spec (coordinate : RelationCoordinate) (relation candidate : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ candidate) ↔ₘ ((bₛ#0 ∈ₘ double_union_term relation) ∧ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ relation) ∧ₘ (bₛ#1 ≐ₘ
              relation_coordinate_projection_term
                coordinate bₛ#0)))
/-- 对固定关系断言指定坐标集合存在。 -/
def relation_coordinate_exists (coordinate : RelationCoordinate) (relation : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ((bₛ#0 ∈ₘ double_union_term relation) ∧ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ relation) ∧ₘ (bₛ#1 ≐ₘ
                relation_coordinate_projection_term
                  coordinate bₛ#0)))
/-- 从任意母集中分离指定坐标的闭公理实例体。 -/
def relation_coordinate_separation_exists (coordinate : RelationCoordinate) (relation source : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ((bₛ#0 ∈ₘ source) ∧ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ relation) ∧ₘ (bₛ#1 ≐ₘ
                relation_coordinate_projection_term
                  coordinate bₛ#0)))
/-- 任意关系参数与任意母集上的坐标分离公理。 -/
def relation_coordinate_separation_axiom (coordinate : RelationCoordinate) :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      relation_coordinate_separation_exists
        coordinate (x#0) (x#1)
/-! ## 定义域与值域的数学接口 -/
/-- 定义域成员条件。 -/
abbrev relation_domain_member_condition :=
  relation_coordinate_member_condition
    RelationCoordinate.domain
/-- 定义域规格。 -/
abbrev relation_domain_spec :=
  relation_coordinate_spec
    RelationCoordinate.domain
/-- 定义域存在公式。 -/
abbrev relation_domain_exists :=
  relation_coordinate_exists
    RelationCoordinate.domain
/-- 定义域分离公理。 -/
abbrev relation_domain_separation_axiom :=
  relation_coordinate_separation_axiom
    RelationCoordinate.domain
/-- 值域成员条件。 -/
abbrev relation_range_member_condition :=
  relation_coordinate_member_condition
    RelationCoordinate.range
/-- 值域规格。 -/
abbrev relation_range_spec :=
  relation_coordinate_spec
    RelationCoordinate.range
/-- 值域存在公式。 -/
abbrev relation_range_exists :=
  relation_coordinate_exists
    RelationCoordinate.range
/-- 值域分离公理。 -/
abbrev relation_range_separation_axiom :=
  relation_coordinate_separation_axiom
    RelationCoordinate.range
/-! ## 定义域函数符号 -/
/-- 定义域函数符号的开放定义实例。 -/
def domain_definition_instance (relation candidate : SetTerm) :
    SetFormula :=
  is_relation_formula relation ⟶ₘ ((candidate ≐ₘ domₘ(relation)) ↔ₘ
      relation_domain_spec relation candidate)
/-- 定义域函数符号的定义公理。 -/
def domain_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      domain_definition_instance (x#0) (x#1)
/-- 定义域函数项的平凡存在公式。 -/
def domain_term_exists (relation : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    bₛ#0 ≐ₘ domₘ(relation)
/-! ## 理论组合 -/
/-- 左右投影与一元并集所需的最小公共理论。 -/
def relation_base_theory : SetTheory :=
  Theory.union
    right_projection_operator_theory
    union_operator_theory
/-- 在公共基座上加入关系谓词。 -/
def relation_predicate_theory : SetTheory :=
  Theory.insert
    is_relation_definition_axiom
    relation_base_theory
/-- 加入定义域分离实例。 -/
def relation_domain_theory : SetTheory :=
  Theory.insert
    relation_domain_separation_axiom
    relation_predicate_theory
/-- 加入定义域函数符号。 -/
def relation_domain_operator_theory : SetTheory :=
  Theory.insert
    domain_definition_axiom
    relation_domain_theory
/-- 在已有关系与定义域层上加入值域分离实例。 -/
def relation_range_theory : SetTheory :=
  Theory.insert
    relation_range_separation_axiom
    relation_domain_operator_theory
/-! ## 值域函数符号 -/
/-- 值域函数符号的开放定义实例。文献中的 `rng` 只作为索引保留。 -/
def range_definition_instance (relation candidate : SetTerm) :
    SetFormula :=
  is_relation_formula relation ⟶ₘ ((candidate ≐ₘ ranₘ(relation)) ↔ₘ
      relation_range_spec relation candidate)
/-- 值域函数符号的定义公理。 -/
def range_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      range_definition_instance (x#0) (x#1)
/-- 在值域存在理论上加入值域函数符号。 -/
def relation_range_operator_theory : SetTheory :=
  Theory.insert
    range_definition_axiom
    relation_range_theory
/-! ## proof-carrying 良构性边界 -/
/-- 指定坐标投影项保持 proof-carrying 项边界。 -/
theorem relation_coordinate_projection_term_admissible (coordinate : RelationCoordinate) (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    Term.Admissible (relation_coordinate_projection_term
        coordinate pair)
      SetSort.set := by
  cases coordinate
  · exact left_projection_term_admissible pair hPair
  · exact right_projection_term_admissible pair hPair
/-- 双重并集项保持 proof-carrying 项边界。 -/
theorem double_union_term_admissible (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    Term.Admissible (double_union_term relation)
      SetSort.set :=
  union_term_admissible (⋃ₘ relation) (union_term_admissible relation hRelation)
/-- 双重并集项的合法性由关系项证书计算。 -/
@[term_check]
theorem double_union_term_check
    {relation : SetTerm}
    (hRelation : Term.CheckCertificate relation SetSort.set) :
    Term.CheckCertificate
      (double_union_term relation) SetSort.set :=
  Term.check_admissible_complete <|
    double_union_term_admissible relation hRelation.admissible
private abbrev relation_coordinate_predicate_scope :
    Scope signature :=
  Scope.push (Scope.push Scope.empty SetSort.set)
    SetSort.set
/-- 坐标筛选条件作为公共分离谓词。 -/
def relation_coordinate_predicate (coordinate : RelationCoordinate) (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    SetPredicate where
  body :=
    ∃ₘ[SetSort.set], (bₛ#0 ∈ₘ relation) ∧ₘ (bₛ#1 ≐ₘ
          relation_coordinate_projection_term
            coordinate bₛ#0)
  admissible_at := by
    cases coordinate <;> prove_admissible_at
/-- 关系坐标成员条件保持公式 admissibility。 -/
theorem relation_coordinate_member_condition_admissible
    {coordinate : RelationCoordinate}
    {relation element : SetTerm} (hRelation : Term.Admissible relation SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    Formula.Admissible (relation_coordinate_member_condition
        coordinate relation element) := by
  cases coordinate <;> prove_admissible
/-- 关系谓词定义公理满足公共良构性边界。 -/
theorem is_relation_definition_axiom_admissible :
    Formula.Admissible
      is_relation_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 关系公共基座仍然 admissible。 -/
theorem relation_base_theory_admissible :
    Theory.Admissible relation_base_theory := by
  intro formula hFormula
  rcases hFormula with hFormula | hFormula
  · exact right_projection_operator_theory_admissible
      formula hFormula
  · exact union_operator_theory_admissible
      formula hFormula
/-- 加入关系谓词后的理论仍然 admissible。 -/
theorem relation_predicate_theory_admissible :
    Theory.Admissible relation_predicate_theory :=
  Theory.admissible_insert
    is_relation_definition_axiom_admissible
    relation_base_theory_admissible
/-- 定义域分离公理满足公共良构性边界。 -/
theorem relation_domain_separation_axiom_admissible :
    Formula.Admissible
      relation_domain_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 加入定义域分离实例后的理论仍然 admissible。 -/
theorem relation_domain_theory_admissible :
    Theory.Admissible relation_domain_theory :=
  Theory.admissible_insert
    relation_domain_separation_axiom_admissible
    relation_predicate_theory_admissible
/-- 定义域函数符号定义公理满足公共良构性边界。 -/
theorem domain_definition_axiom_admissible :
    Formula.Admissible
      domain_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 定义域函数符号扩张后的理论仍然 admissible。 -/
theorem relation_domain_operator_theory_admissible :
    Theory.Admissible relation_domain_operator_theory :=
  Theory.admissible_insert
    domain_definition_axiom_admissible
    relation_domain_theory_admissible
/-- 值域分离公理满足公共良构性边界。 -/
theorem relation_range_separation_axiom_admissible :
    Formula.Admissible
      relation_range_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 加入值域分离实例后的理论仍然 admissible。 -/
theorem relation_range_theory_admissible :
    Theory.Admissible relation_range_theory :=
  Theory.admissible_insert
    relation_range_separation_axiom_admissible
    relation_domain_operator_theory_admissible
/-- 值域函数符号定义公理满足公共良构性边界。 -/
theorem range_definition_axiom_admissible :
    Formula.Admissible
      range_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 加入值域函数符号后的理论仍然 admissible。 -/
theorem relation_range_operator_theory_admissible :
    Theory.Admissible
      relation_range_operator_theory :=
  Theory.admissible_insert
    range_definition_axiom_admissible
    relation_range_theory_admissible
/-- 定义域函数项保持 proof-carrying 项边界。 -/
theorem domain_term_admissible (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    Term.Admissible (domain_term relation)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .domain [⟨relation, by assumption⟩]
      (by rfl) (by rfl)
/-- 定义域项的合法性由关系项证书计算。 -/
@[term_check]
theorem domain_term_check
    {relation : SetTerm}
    (hRelation : Term.CheckCertificate relation SetSort.set) :
    Term.CheckCertificate (domain_term relation) SetSort.set :=
  Term.check_admissible_complete <|
    domain_term_admissible relation hRelation.admissible
/-- 值域函数项保持 proof-carrying 项边界。 -/
theorem range_term_admissible (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    Term.Admissible (range_term relation)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .range [⟨relation, by assumption⟩]
      (by rfl) (by rfl)
/-- 值域项的合法性由关系项证书计算。 -/
@[term_check]
theorem range_term_check
    {relation : SetTerm}
    (hRelation : Term.CheckCertificate relation SetSort.set) :
    Term.CheckCertificate (range_term relation) SetSort.set :=
  Term.check_admissible_complete <|
    range_term_admissible relation hRelation.admissible
/-! ## 公式级 proof-carrying 边界 -/
/-- 关系谓词原子在 admissible 项处仍然 admissible。 -/
theorem is_relation_formula_admissible
    {relation : SetTerm} (hRelation : Term.Admissible relation SetSort.set) :
    Formula.Admissible (is_relation_formula relation) := by
  apply Formula.Admissible.rel
  simpa [signature] using (ArgsAdmissible.cons hRelation
      ArgsAdmissible.nil)
/-- 关系谓词原子的合法性由对象项证书计算。 -/
@[formula_check]
theorem is_relation_formula_check
    {relation : SetTerm}
    (hRelation : Term.CheckCertificate relation SetSort.set) :
    Formula.CheckCertificate (is_relation_formula relation) :=
  Formula.check_admissible_complete <|
    is_relation_formula_admissible hRelation.admissible
/-- “每个成员都是有序对”的关系条件保持公式 admissibility。 -/
theorem is_relation_condition_admissible
    {relation : SetTerm} (hRelation : Term.Admissible relation SetSort.set) :
    Formula.Admissible (is_relation_condition relation) := by
  prove_admissible
/-- 关系谓词定义实例保持公式 admissibility。 -/
theorem is_relation_definition_instance_admissible
    {relation : SetTerm} (hRelation : Term.Admissible relation SetSort.set) :
    Formula.Admissible (is_relation_definition_instance relation) :=
  Formula.Admissible.iff (is_relation_formula_admissible hRelation) (is_relation_condition_admissible hRelation)
/--
任意 admissible 集合项都可作为一个相等见证存在式的右端。
该局部公共引理统一服务双重并集、定义域项与值域项的平凡存在合同。
-/
private theorem relation_term_witness_exists_admissible
    {term : SetTerm} (hTerm : Term.Admissible term SetSort.set) :
    Formula.Admissible (∃ₘ[SetSort.set], bₛ#0 ≐ₘ term) := by
  prove_admissible
/-- 双重并集项的平凡存在式保持公式 admissibility。 -/
theorem double_union_term_exists_admissible
    {relation : SetTerm} (hRelation : Term.Admissible relation SetSort.set) :
    Formula.Admissible (double_union_term_exists relation) := by
  simpa [double_union_term_exists] using
    relation_term_witness_exists_admissible (double_union_term_admissible
        relation hRelation)
/-- 坐标规格保持公式 admissibility。 -/
theorem relation_coordinate_spec_admissible
    {coordinate : RelationCoordinate}
    {relation candidate : SetTerm} (hRelation : Term.Admissible relation SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (relation_coordinate_spec
        coordinate relation candidate) := by
  have hSeparation :=
    SetPredicate.separation_spec_admissible (relation_coordinate_predicate
        coordinate relation hRelation) (double_union_term_admissible
        relation hRelation)
      hCandidate
  simpa [SetPredicate.separation_spec,
    relation_coordinate_predicate,
    relation_coordinate_spec] using hSeparation
/-- 坐标集合存在式保持公式 admissibility。 -/
theorem relation_coordinate_exists_admissible
    {coordinate : RelationCoordinate}
    {relation : SetTerm} (hRelation : Term.Admissible relation SetSort.set) :
    Formula.Admissible (relation_coordinate_exists
        coordinate relation) := by
  have hSeparation :=
    SetPredicate.separation_exists_admissible (relation_coordinate_predicate
        coordinate relation hRelation) (double_union_term_admissible
        relation hRelation)
  simpa [SetPredicate.separation_exists,
    relation_coordinate_predicate,
    relation_coordinate_exists] using hSeparation
/-- 任意母集上的坐标分离存在式保持公式 admissibility。 -/
theorem relation_coordinate_separation_exists_admissible
    {coordinate : RelationCoordinate}
    {relation source : SetTerm} (hRelation : Term.Admissible relation SetSort.set) (hSource : Term.Admissible source SetSort.set) :
    Formula.Admissible (relation_coordinate_separation_exists
        coordinate relation source) := by
  have hSeparation :=
    SetPredicate.separation_exists_admissible (relation_coordinate_predicate
        coordinate relation hRelation)
      hSource
  simpa [SetPredicate.separation_exists,
    relation_coordinate_predicate,
    relation_coordinate_separation_exists] using
      hSeparation
/-- 定义域函数符号定义实例保持公式 admissibility。 -/
theorem domain_definition_instance_admissible
    {relation candidate : SetTerm} (hRelation : Term.Admissible relation SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (domain_definition_instance relation candidate) :=
  Formula.Admissible.imp (is_relation_formula_admissible hRelation) (Formula.Admissible.iff (Formula.Admissible.equal
        hCandidate (domain_term_admissible
          relation hRelation)) (relation_coordinate_spec_admissible (coordinate := RelationCoordinate.domain)
        hRelation hCandidate))
/-- 值域函数符号定义实例保持公式 admissibility。 -/
theorem range_definition_instance_admissible
    {relation candidate : SetTerm} (hRelation : Term.Admissible relation SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (range_definition_instance relation candidate) :=
  Formula.Admissible.imp (is_relation_formula_admissible hRelation) (Formula.Admissible.iff (Formula.Admissible.equal
        hCandidate (range_term_admissible
          relation hRelation)) (relation_coordinate_spec_admissible (coordinate := RelationCoordinate.range)
        hRelation hCandidate))
/-- 定义域函数项存在式保持公式 admissibility。 -/
theorem domain_term_exists_admissible
    {relation : SetTerm} (hRelation : Term.Admissible relation SetSort.set) :
    Formula.Admissible (domain_term_exists relation) := by
  simpa [domain_term_exists] using
    relation_term_witness_exists_admissible (domain_term_admissible relation hRelation)
/-- 值域函数项存在式保持公式 admissibility。 -/
theorem range_term_exists_admissible
    {relation : SetTerm} (hRelation : Term.Admissible relation SetSort.set) :
    Formula.Admissible (∃ₘ[SetSort.set], bₛ#0 ≐ₘ ranₘ(relation)) :=
  relation_term_witness_exists_admissible (range_term_admissible relation hRelation)
/-! ## 闭理论边界 -/
/-- 关系公共基座中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem relation_base_theory_sentence
    {formula : SetFormula} (hFormula : relation_base_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with hFormula | hFormula
  · exact right_projection_operator_theory_sentence
      hFormula
  · exact union_operator_theory_sentence hFormula
/-- 关系谓词理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem relation_predicate_theory_sentence
    {formula : SetFormula} (hFormula : relation_predicate_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact relation_predicate_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · exact (relation_base_theory_sentence hFormula).2
/-- 定义域存在理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem relation_domain_theory_sentence
    {formula : SetFormula} (hFormula : relation_domain_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact relation_domain_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · exact (relation_predicate_theory_sentence hFormula).2
/-- 定义域函数符号理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem relation_domain_operator_theory_sentence
    {formula : SetFormula} (hFormula :
      relation_domain_operator_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact relation_domain_operator_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · exact (relation_domain_theory_sentence hFormula).2
/-- 值域存在理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem relation_range_theory_sentence
    {formula : SetFormula} (hFormula : relation_range_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact relation_range_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · exact (relation_domain_operator_theory_sentence
          hFormula).2
/-- 值域函数符号理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem relation_range_operator_theory_sentence
    {formula : SetFormula} (hFormula :
      relation_range_operator_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact relation_range_operator_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · exact (relation_range_theory_sentence hFormula).2
/-! ## 理论嵌入 -/
/-- 右投影理论嵌入关系公共基座。 -/
theorem right_projection_operator_theory_subset_relation_base_theory
    {formula : SetFormula} (hFormula :
      right_projection_operator_theory formula) :
    relation_base_theory formula :=
  Or.inl hFormula
/-- 一元并集理论嵌入关系公共基座。 -/
theorem union_operator_theory_subset_relation_base_theory
    {formula : SetFormula} (hFormula : union_operator_theory formula) :
    relation_base_theory formula :=
  Or.inr hFormula
/-- 关系与函数基座嵌入关系公共基座。 -/
theorem relation_function_theory_subset_relation_base_theory
    {formula : SetFormula} (hFormula : relation_function_theory formula) :
    relation_base_theory formula :=
  right_projection_operator_theory_subset_relation_base_theory (relation_function_theory_subset_right_projection_operator_theory
      hFormula)
/-- 外延理论嵌入关系公共基座。 -/
theorem extensionality_theory_subset_relation_base_theory
    {formula : SetFormula} (hFormula : extensionality_theory formula) :
    relation_base_theory formula :=
  right_projection_operator_theory_subset_relation_base_theory (ordered_pair_operator_theory_subset_right_projection_operator_theory
      (extensionality_theory_subset_ordered_pair_operator_theory
        hFormula))
/-- 关系公共基座嵌入关系谓词理论。 -/
theorem relation_base_theory_subset_relation_predicate_theory
    {formula : SetFormula} (hFormula : relation_base_theory formula) :
    relation_predicate_theory formula :=
  Or.inr hFormula
/-- 关系谓词理论嵌入定义域存在理论。 -/
theorem relation_predicate_theory_subset_relation_domain_theory
    {formula : SetFormula} (hFormula : relation_predicate_theory formula) :
    relation_domain_theory formula :=
  Or.inr hFormula
/-- 定义域存在理论嵌入定义域函数符号理论。 -/
theorem relation_domain_theory_subset_relation_domain_operator_theory
    {formula : SetFormula} (hFormula : relation_domain_theory formula) :
    relation_domain_operator_theory formula :=
  Or.inr hFormula
/-- 定义域函数符号理论嵌入值域存在理论。 -/
theorem relation_domain_operator_theory_subset_relation_range_theory
    {formula : SetFormula} (hFormula :
      relation_domain_operator_theory formula) :
    relation_range_theory formula :=
  Or.inr hFormula
/-- 值域存在理论嵌入值域函数符号理论。 -/
theorem relation_range_theory_subset_relation_range_operator_theory
    {formula : SetFormula} (hFormula :
      relation_range_theory formula) :
    relation_range_operator_theory formula :=
  Or.inr hFormula
/-- 关系公共基座嵌入定义域存在理论。 -/
theorem relation_base_theory_subset_relation_domain_theory
    {formula : SetFormula} (hFormula : relation_base_theory formula) :
    relation_domain_theory formula :=
  relation_predicate_theory_subset_relation_domain_theory (relation_base_theory_subset_relation_predicate_theory
      hFormula)
/-- 关系公共基座嵌入定义域函数符号理论。 -/
theorem relation_base_theory_subset_relation_domain_operator_theory
    {formula : SetFormula} (hFormula : relation_base_theory formula) :
    relation_domain_operator_theory formula :=
  relation_domain_theory_subset_relation_domain_operator_theory (relation_base_theory_subset_relation_domain_theory
      hFormula)
/-- 关系公共基座嵌入值域存在理论。 -/
theorem relation_base_theory_subset_relation_range_theory
    {formula : SetFormula} (hFormula : relation_base_theory formula) :
    relation_range_theory formula :=
  relation_domain_operator_theory_subset_relation_range_theory (relation_base_theory_subset_relation_domain_operator_theory
      hFormula)
/-- 关系公共基座嵌入值域函数符号理论。 -/
theorem relation_base_theory_subset_relation_range_operator_theory
    {formula : SetFormula} (hFormula : relation_base_theory formula) :
    relation_range_operator_theory formula :=
  relation_range_theory_subset_relation_range_operator_theory (relation_base_theory_subset_relation_range_theory
      hFormula)
/-! ## 关系谓词的实例化合同 -/
/-- 关系谓词定义公理可在任意 admissible 集合项处实例化。 -/
theorem is_relation_definition_instance_derives (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_predicate_theory]
      is_relation_definition_instance relation := by
  have hAxiom :
      ⊢ₘ[relation_predicate_theory]
        is_relation_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hInstance :=
    FirstOrder.Derives.forall_elim (term := relation) hAxiom
  simpa [is_relation_definition_axiom,
    is_relation_definition_instance,
    is_relation_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable] using hInstance
/-- 关系谓词等价于“每个成员都是有序对”的现代规格。 -/
theorem is_relation_iff_condition (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_predicate_theory]
      is_relation_formula relation ↔ₘ
        is_relation_condition relation :=
  is_relation_definition_instance_derives
    relation hRelation
/-- 关系的任意成员都满足有序对谓词。 -/
theorem is_relation_member_is_ordered_pair (relation member : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hMember : Term.Admissible member SetSort.set) :
    ⊢ₘ[relation_predicate_theory]
      is_relation_formula relation ⟶ₘ (member ∈ₘ relation) ⟶ₘ
          is_ordered_pair_formula member := by
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let relation_formula :=
    is_relation_formula relation
  let membership_formula :=
    member ∈ₘ relation
  let Γ : Context signature :=
    [membership_formula, relation_formula]
  have hDefinition :
      Γ ⊢ₘ[relation_predicate_theory]
        is_relation_definition_instance relation :=
    FirstOrder.Derives.context_weaken_cons (assumption := membership_formula) <|
      FirstOrder.Derives.context_weaken_cons (assumption := relation_formula) <|
        is_relation_definition_instance_derives
          relation hRelation
  have hRelationFormula :
      Γ ⊢ₘ[relation_predicate_theory]
        is_relation_formula relation := by
    simpa [Γ, relation_formula] using (show Γ ⊢ₘ[relation_predicate_theory]
          relation_formula from
        .assumption (by simp [Γ]))
  have hCondition :
      Γ ⊢ₘ[relation_predicate_theory]
        is_relation_condition relation :=
    FirstOrder.Derives.iffElimRight
      hDefinition hRelationFormula
  have hAtRaw :=
    FirstOrder.Derives.forall_elim (term := member) hCondition
  have hRelationOpen :
      Term.openAt SetSort.set 0 member relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 member relation hRelation.2
  have hAt :
      Γ ⊢ₘ[relation_predicate_theory] (member ∈ₘ relation) ⟶ₘ
          is_ordered_pair_formula member := by
    simpa [is_relation_condition,
      Formula.openAt, Term.openAt,
      hRelationOpen] using hAtRaw
  have hMembership :
      Γ ⊢ₘ[relation_predicate_theory]
        member ∈ₘ relation := by
    simpa [Γ, membership_formula] using (show Γ ⊢ₘ[relation_predicate_theory]
          membership_formula from
        .assumption (by simp [Γ]))
  exact FirstOrder.Derives.impElim
    hAt hMembership
/-! ## 双重并集合同 -/
/-- 双重并集项满足外层一元并集规格。 -/
theorem double_union_term_spec_derives (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_base_theory]
      union_spec (⋃ₘ relation) (double_union_term relation) :=
  FirstOrder.Derives.theory_weaken (fun _ hFormula =>
      union_operator_theory_subset_relation_base_theory
        hFormula) (union_term_spec_derives (⋃ₘ relation) (union_term_admissible relation hRelation))
/-- 双重并集成员关系等价于外层并集的存在见证规格。 -/
theorem double_union_member_iff (relation element : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[relation_base_theory] (element ∈ₘ double_union_term relation) ↔ₘ
        double_union_member_condition
          relation element := by
  have hSpec :=
    double_union_term_spec_derives
      relation hRelation
  have hAt :=
    FirstOrder.Derives.forall_elim (term := element) hSpec
  have hInner :
      Term.Admissible (⋃ₘ relation) SetSort.set :=
    union_term_admissible relation hRelation
  have hDouble :
      Term.Admissible (double_union_term relation)
        SetSort.set :=
    double_union_term_admissible
      relation hRelation
  have hInnerOpen :
      Term.openAt SetSort.set 1 element (⋃ₘ relation) =
        ⋃ₘ relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 element (⋃ₘ relation) hInner.2
  have hDoubleOpen :
      Term.openAt SetSort.set 0 element (double_union_term relation) =
        double_union_term relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element (double_union_term relation)
      hDouble.2
  simpa [union_spec,
    double_union_member_condition,
    Formula.openAt, Formula.next_depth,
    Term.openAt, hInnerOpen,
    hDoubleOpen] using hAt
/-- 双重并集复合项自身给出存在见证。 -/
theorem double_union_term_exists_derives (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_base_theory]
      double_union_term_exists relation := by
  unfold double_union_term_exists
  nd_apply FirstOrder.Derives.exists_intro
    (term := double_union_term relation)
  have hRelationOpen :
      Term.openAt SetSort.set 0 (double_union_term relation) relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (double_union_term relation)
      relation hRelation.2
  simpa [double_union_term,
    Formula.openAt, Term.openAt,
    hRelationOpen] using
      (FirstOrder.Derives.eq_refl_m
        (T := relation_base_theory) (Γ := [])
        (sort := SetSort.set) (double_union_term relation))
/-! ## 坐标筛选规格与公共分离接口 -/
/-- 共享坐标规格正是公共分离规格。 -/
theorem relation_coordinate_spec_eq_separation_spec (coordinate : RelationCoordinate) (relation candidate : SetTerm)
    (hRelation : Term.Admissible relation SetSort.set) :
    relation_coordinate_spec
        coordinate relation candidate = (relation_coordinate_predicate
          coordinate relation hRelation).separation_spec (double_union_term relation)
        candidate := by
  rfl
/-- 坐标规格可在任意 admissible 元素处实例化。 -/
theorem relation_coordinate_spec_member_iff
    {T : SetTheory} {Γ : Context signature} (coordinate : RelationCoordinate) (relation candidate element : SetTerm)
    (hRelation : Term.Admissible relation SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    Γ ⊢ₘ[T]
      relation_coordinate_spec
          coordinate relation candidate ⟶ₘ ((element ∈ₘ candidate) ↔ₘ ((element ∈ₘ
              double_union_term relation) ∧ₘ
            relation_coordinate_member_condition
              coordinate relation element)) := by
  have hSpecAdmissible :
      Formula.Admissible
        (relation_coordinate_spec coordinate relation candidate) :=
    relation_coordinate_spec_admissible hRelation hCandidate
  nd_apply FirstOrder.Derives.impIntro
  let spec :=
    relation_coordinate_spec
      coordinate relation candidate
  have hSpec :
      spec :: Γ ⊢ₘ[T] spec :=
    .assumption (by simp)
  have hAt :=
    FirstOrder.Derives.forall_elim (term := element) hSpec
  have hDouble :
      Term.Admissible (double_union_term relation)
        SetSort.set :=
    double_union_term_admissible
      relation hRelation
  have hCandidateOpen :
      Term.openAt SetSort.set 0
          element candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element
      candidate hCandidate.2
  have hDoubleOpen :
      Term.openAt SetSort.set 0
          element (double_union_term relation) =
        double_union_term relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element (double_union_term relation)
      hDouble.2
  have hRelationOpen :
      Term.openAt SetSort.set 1
          element relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 element
      relation hRelation.2
  cases coordinate <;>
    simpa [spec, relation_coordinate_spec,
      relation_coordinate_member_condition,
      relation_coordinate_projection_term,
      Formula.openAt, Formula.next_depth,
      Term.openAt, left_projection_term,
      right_projection_term, hCandidateOpen,
      hDoubleOpen, hRelationOpen] using hAt
/-- 从一个坐标分离公理实例化任意 admissible 关系参数与母集。 -/
private theorem relation_coordinate_separation_instance_of_axiom
    {T : SetTheory} {Γ : Context signature} (coordinate : RelationCoordinate) (relation source : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hSource : Term.Admissible source SetSort.set) (hAxiom :
      Γ ⊢ₘ[T]
        relation_coordinate_separation_axiom coordinate) :
    Γ ⊢ₘ[T]
      relation_coordinate_separation_exists
        coordinate relation source := by
  have hRelationInstance :=
    FirstOrder.Derives.forall_elim (term := relation) hAxiom
  have hSourceInstance :=
    FirstOrder.Derives.forall_elim (term := source) hRelationInstance
  have hRelationOpenSource :
      Term.openAt SetSort.set 3 source relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 3 source relation hRelation.2
  cases coordinate <;>
    simpa [relation_coordinate_separation_axiom,
      relation_coordinate_separation_exists,
      relation_coordinate_projection_term,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable, left_projection_term,
      right_projection_term,
      hRelationOpenSource] using hSourceInstance
/-- 定义域分离公理可在任意 admissible 关系参数与母集处实例化。 -/
theorem relation_domain_separation_instance_derives (relation source : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[relation_domain_theory]
      relation_coordinate_separation_exists
        RelationCoordinate.domain
        relation source :=
  relation_coordinate_separation_instance_of_axiom
    RelationCoordinate.domain
    relation source hRelation hSource (FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl))
/-- 值域分离公理可在任意 admissible 关系参数与母集处实例化。 -/
theorem relation_range_separation_instance_derives (relation source : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[relation_range_theory]
      relation_coordinate_separation_exists
        RelationCoordinate.range
        relation source :=
  relation_coordinate_separation_instance_of_axiom
    RelationCoordinate.range
    relation source hRelation hSource (FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl))
/-- 同一关系的同一坐标规格具有唯一结果。 -/
theorem relation_coordinate_unique (coordinate : RelationCoordinate) (relation first second : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_base_theory]
      relation_coordinate_spec
          coordinate relation first ⟶ₘ
        relation_coordinate_spec
            coordinate relation second ⟶ₘ (first ≐ₘ second) := by
  let source :=
    double_union_term relation
  let predicate :=
    relation_coordinate_predicate
      coordinate relation hRelation
  have hSource :
      Term.Admissible source SetSort.set :=
    double_union_term_admissible
      relation hRelation
  have hUnique :
      ⊢ₘ[extensionality_theory]
        predicate.separation_spec source first ⟶ₘ
          predicate.separation_spec source second ⟶ₘ (first ≐ₘ second) :=
    SetPredicate.separation_unique_of_admissible
      predicate source first second
      hSource hFirst hSecond
  have hWeakened :
      ⊢ₘ[relation_base_theory]
        predicate.separation_spec source first ⟶ₘ
          predicate.separation_spec source second ⟶ₘ (first ≐ₘ second) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        extensionality_theory_subset_relation_base_theory
          hFormula)
      hUnique
  simpa [source, predicate,
    relation_coordinate_spec_eq_separation_spec] using
    hWeakened
/-! ## 定义域存在性与唯一性 -/
/-- 定义域规格可在任意 admissible 元素处实例化。 -/
theorem relation_domain_spec_member_iff
    {T : SetTheory} {Γ : Context signature} (relation candidate element : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    Γ ⊢ₘ[T]
      relation_domain_spec relation candidate ⟶ₘ ((element ∈ₘ candidate) ↔ₘ ((element ∈ₘ
              double_union_term relation) ∧ₘ
            relation_domain_member_condition
              relation element)) :=
  relation_coordinate_spec_member_iff
    RelationCoordinate.domain
    relation candidate element
    hRelation hCandidate hElement
/-- 任意 admissible 集合都有按左投影筛选得到的定义域候选。 -/
theorem relation_domain_exists_derives (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_domain_theory]
      relation_domain_exists relation := by
  have hSeparation :=
    relation_domain_separation_instance_derives
      relation (double_union_term relation)
      hRelation (double_union_term_admissible
        relation hRelation)
  simpa [relation_domain_exists,
    relation_coordinate_exists,
    relation_coordinate_separation_exists] using
    hSeparation
/-- 文献形式：若给定集合是关系，则其定义域存在。 -/
theorem is_relation_implies_domain_exists (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_domain_theory]
      is_relation_formula relation ⟶ₘ
        relation_domain_exists relation := by
  have hExists :=
    relation_domain_exists_derives
      relation hRelation
  nd_apply FirstOrder.Derives.impIntro
  exact FirstOrder.Derives.context_weaken_cons
    hExists
/-- 同一关系的两个定义域候选必相等。 -/
theorem relation_domain_unique (relation first second : SetTerm) (hRelation : Term.Admissible relation SetSort.set) (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_base_theory]
      relation_domain_spec
          relation first ⟶ₘ
        relation_domain_spec
            relation second ⟶ₘ (first ≐ₘ second) :=
  relation_coordinate_unique
    RelationCoordinate.domain
    relation first second
    hRelation hFirst hSecond
/-- 文献形式：关系谓词背景下定义域规格保持唯一。 -/
theorem is_relation_domain_unique (relation first second : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_domain_theory]
      is_relation_formula relation ⟶ₘ
        relation_domain_spec
            relation first ⟶ₘ
          relation_domain_spec
              relation second ⟶ₘ (first ≐ₘ second) := by
  have hUnique :
      ⊢ₘ[relation_domain_theory]
        relation_domain_spec
            relation first ⟶ₘ
          relation_domain_spec
              relation second ⟶ₘ (first ≐ₘ second) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        relation_base_theory_subset_relation_domain_theory
          hFormula) (relation_domain_unique
        relation first second
        hRelation hFirst hSecond)
  nd_apply FirstOrder.Derives.impIntro
  exact FirstOrder.Derives.context_weaken_cons
    hUnique
/-! ## 定义域函数符号合同 -/
/-- 定义域定义公理可在任意 admissible 集合项处实例化。 -/
theorem domain_definition_instance_derives (relation candidate : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[relation_domain_operator_theory]
      domain_definition_instance
        relation candidate := by
  have hAxiom :
      ⊢ₘ[relation_domain_operator_theory]
        domain_definition_axiom :=
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
  simpa [domain_definition_axiom,
    domain_definition_instance,
    relation_domain_spec,
    relation_coordinate_spec,
    relation_coordinate_projection_term,
    double_union_term,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, domain_term,
    union_term, left_projection_term,
    hRelationOpenZero, hRelationOpenOne,
    hRelationOpenTwo] using
    hCandidateInstance
/-- 候选项等于 `dom`，当且仅当它满足定义域规格。 -/
theorem domain_eq_iff_spec (relation candidate : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[relation_domain_operator_theory]
      is_relation_formula relation ⟶ₘ ((candidate ≐ₘ domₘ(relation)) ↔ₘ
          relation_domain_spec
            relation candidate) :=
  domain_definition_instance_derives
    relation candidate hRelation hCandidate
/-- 关系谓词背景下，规范定义域项满足定义域规格。 -/
theorem is_relation_domain_term_spec (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_domain_operator_theory]
      is_relation_formula relation ⟶ₘ
        relation_domain_spec
          relation (domₘ(relation)) := by
  nd_apply FirstOrder.Derives.impIntro
  let relation_formula :=
    is_relation_formula relation
  have hDefinition :
      [relation_formula]
        ⊢ₘ[relation_domain_operator_theory]
          domain_definition_instance
            relation (domₘ(relation)) :=
    FirstOrder.Derives.context_weaken_cons (domain_definition_instance_derives
        relation (domₘ(relation))
        hRelation (domain_term_admissible
          relation hRelation))
  have hRelationFormula :
      [relation_formula]
        ⊢ₘ[relation_domain_operator_theory]
          is_relation_formula relation := by
    simpa [relation_formula] using (show
        [relation_formula]
          ⊢ₘ[relation_domain_operator_theory]
            relation_formula from
        .assumption (by simp))
  have hGraph :
      [relation_formula]
        ⊢ₘ[relation_domain_operator_theory] ((domₘ(relation) ≐ₘ
              domₘ(relation)) ↔ₘ
            relation_domain_spec
              relation (domₘ(relation))) :=
    FirstOrder.Derives.impElim
      hDefinition hRelationFormula
  exact FirstOrder.Derives.iffElimRight
    hGraph (FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) (domₘ(relation)))
/-- 定义域函数项自身给出一个相等见证。 -/
theorem domain_term_exists_derives (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_domain_operator_theory]
      domain_term_exists relation := by
  unfold domain_term_exists
  nd_apply FirstOrder.Derives.exists_intro
    (term := domₘ(relation))
  have hRelationOpen :
      Term.openAt SetSort.set 0 (domₘ(relation)) relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (domₘ(relation))
      relation hRelation.2
  simpa [Formula.openAt, Term.openAt,
    domain_term, hRelationOpen] using
      (FirstOrder.Derives.eq_refl_m
        (T := relation_domain_operator_theory) (Γ := [])
        (sort := SetSort.set) (domₘ(relation)))
/-- 文献形式：关系谓词背景下存在一个等于规范定义域项的对象。 -/
theorem is_relation_implies_domain_term_exists (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_domain_operator_theory]
      is_relation_formula relation ⟶ₘ
        domain_term_exists relation := by
  have hExists :=
    domain_term_exists_derives
      relation hRelation
  nd_apply FirstOrder.Derives.impIntro
  exact FirstOrder.Derives.context_weaken_cons
    hExists
/-! ## 定义域的点态函数合同 -/
/-- 关系谓词背景下，`dom` 的成员关系满足文献定义域规格。 -/
theorem is_relation_domain_member_iff (relation element : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[relation_domain_operator_theory]
      is_relation_formula relation ⟶ₘ ((element ∈ₘ domₘ(relation)) ↔ₘ ((element ∈ₘ
              double_union_term relation) ∧ₘ
              relation_domain_member_condition
                relation element)) := by
  have hSpec :=
    is_relation_domain_term_spec
      relation hRelation
  have hPoint :
      ⊢ₘ[relation_domain_operator_theory]
        relation_domain_spec
            relation (domₘ(relation)) ⟶ₘ ((element ∈ₘ domₘ(relation)) ↔ₘ ((element ∈ₘ
                double_union_term relation) ∧ₘ
              relation_domain_member_condition
                relation element)) :=
    relation_domain_spec_member_iff
      relation (domₘ(relation)) element
      hRelation (domain_term_admissible
        relation hRelation)
      hElement
  nd_apply FirstOrder.Derives.impIntro
  have hSpecInContext :=
    FirstOrder.Derives.context_weaken_cons (assumption := is_relation_formula relation)
      hSpec
  have hPointInContext :=
    FirstOrder.Derives.context_weaken_cons (assumption := is_relation_formula relation)
      hPoint
  exact FirstOrder.Derives.impElim
    hPointInContext (FirstOrder.Derives.impElim
      hSpecInContext (.assumption (by simp)))
/-! ## 值域存在性与唯一性 -/
/-- 值域规格可在任意 admissible 元素处实例化。 -/
theorem relation_range_spec_member_iff
    {T : SetTheory} {Γ : Context signature} (relation candidate element : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    Γ ⊢ₘ[T]
      relation_range_spec relation candidate ⟶ₘ ((element ∈ₘ candidate) ↔ₘ ((element ∈ₘ
              double_union_term relation) ∧ₘ
            relation_range_member_condition
              relation element)) :=
  relation_coordinate_spec_member_iff
    RelationCoordinate.range
    relation candidate element
    hRelation hCandidate hElement
/-- 任意 admissible 集合都有按右投影筛选得到的值域候选。 -/
theorem relation_range_exists_derives (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_range_theory]
      relation_range_exists relation := by
  have hSeparation :=
    relation_range_separation_instance_derives
      relation (double_union_term relation)
      hRelation (double_union_term_admissible
        relation hRelation)
  simpa [relation_range_exists,
    relation_coordinate_exists,
    relation_coordinate_separation_exists] using
    hSeparation
/-- 文献形式：若给定集合是关系，则其值域存在。 -/
theorem is_relation_implies_range_exists (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_range_theory]
      is_relation_formula relation ⟶ₘ
        relation_range_exists relation := by
  have hExists :=
    relation_range_exists_derives
      relation hRelation
  nd_apply FirstOrder.Derives.impIntro
  exact FirstOrder.Derives.context_weaken_cons
    hExists
/-- 同一关系的两个值域候选必相等。 -/
theorem relation_range_unique (relation first second : SetTerm) (hRelation : Term.Admissible relation SetSort.set) (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_base_theory]
      relation_range_spec
          relation first ⟶ₘ
        relation_range_spec
            relation second ⟶ₘ (first ≐ₘ second) :=
  relation_coordinate_unique
    RelationCoordinate.range
    relation first second
    hRelation hFirst hSecond
/-- 文献形式：关系谓词背景下值域规格保持唯一。 -/
theorem is_relation_range_unique (relation first second : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[relation_range_theory]
      is_relation_formula relation ⟶ₘ
        relation_range_spec
            relation first ⟶ₘ
          relation_range_spec
              relation second ⟶ₘ (first ≐ₘ second) := by
  have hUnique :
      ⊢ₘ[relation_range_theory]
        relation_range_spec
            relation first ⟶ₘ
          relation_range_spec
              relation second ⟶ₘ (first ≐ₘ second) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        relation_base_theory_subset_relation_range_theory
          hFormula) (relation_range_unique
        relation first second
        hRelation hFirst hSecond)
  nd_apply FirstOrder.Derives.impIntro
  exact FirstOrder.Derives.context_weaken_cons
    hUnique
/-! ## 值域函数符号合同 -/
/-- 值域定义公理可在任意 admissible 集合项处实例化。 -/
theorem range_definition_instance_derives (relation candidate : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[relation_range_operator_theory]
      range_definition_instance
        relation candidate := by
  have hAxiom :
      ⊢ₘ[relation_range_operator_theory]
        range_definition_axiom :=
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
  simpa [range_definition_axiom,
    range_definition_instance,
    relation_range_spec,
    relation_coordinate_spec,
    relation_coordinate_projection_term,
    double_union_term,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, range_term,
    union_term, right_projection_term,
    hRelationOpenZero, hRelationOpenOne,
    hRelationOpenTwo] using
    hCandidateInstance
/-- 候选项等于 `range`，当且仅当它满足值域规格。 -/
theorem range_eq_iff_spec (relation candidate : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[relation_range_operator_theory]
      is_relation_formula relation ⟶ₘ ((candidate ≐ₘ ranₘ(relation)) ↔ₘ
          relation_range_spec
            relation candidate) :=
  range_definition_instance_derives
    relation candidate hRelation hCandidate
/-- 关系谓词背景下，规范值域项满足值域规格。 -/
theorem is_relation_range_term_spec (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_range_operator_theory]
      is_relation_formula relation ⟶ₘ
        relation_range_spec
          relation (ranₘ(relation)) := by
  nd_apply FirstOrder.Derives.impIntro
  let relation_formula :=
    is_relation_formula relation
  have hDefinition :
      [relation_formula]
        ⊢ₘ[relation_range_operator_theory]
          range_definition_instance
            relation (ranₘ(relation)) :=
    FirstOrder.Derives.context_weaken_cons (range_definition_instance_derives
        relation (ranₘ(relation))
        hRelation (range_term_admissible
          relation hRelation))
  have hRelationFormula :
      [relation_formula]
        ⊢ₘ[relation_range_operator_theory]
          is_relation_formula relation := by
    simpa [relation_formula] using (show
        [relation_formula]
          ⊢ₘ[relation_range_operator_theory]
            relation_formula from
        .assumption (by simp))
  have hGraph :
      [relation_formula]
        ⊢ₘ[relation_range_operator_theory] ((ranₘ(relation) ≐ₘ
              ranₘ(relation)) ↔ₘ
            relation_range_spec
              relation (ranₘ(relation))) :=
    FirstOrder.Derives.impElim
      hDefinition hRelationFormula
  exact FirstOrder.Derives.iffElimRight
    hGraph (FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) (ranₘ(relation)))
/-- 值域函数项自身给出一个相等见证。 -/
theorem range_term_exists_derives (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_range_operator_theory]
      ∃ₘ[SetSort.set],
        bₛ#0 ≐ₘ ranₘ(relation) := by
  nd_apply FirstOrder.Derives.exists_intro
    (term := ranₘ(relation))
  have hRelationOpen :
      Term.openAt SetSort.set 0 (ranₘ(relation)) relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (ranₘ(relation))
      relation hRelation.2
  simpa [Formula.openAt, Term.openAt,
    range_term, hRelationOpen] using
      (FirstOrder.Derives.eq_refl_m
        (T := relation_range_operator_theory) (Γ := [])
        (sort := SetSort.set) (ranₘ(relation)))
/-- 文献形式：关系谓词背景下存在一个等于规范值域项的对象。 -/
theorem is_relation_implies_range_term_exists (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[relation_range_operator_theory]
      is_relation_formula relation ⟶ₘ (∃ₘ[SetSort.set],
          bₛ#0 ≐ₘ ranₘ(relation)) := by
  have hExists :=
    range_term_exists_derives
      relation hRelation
  nd_apply FirstOrder.Derives.impIntro
  exact FirstOrder.Derives.context_weaken_cons
    hExists
/-! ## 值域的点态函数合同 -/
/-- 关系谓词背景下，`range` 的成员关系满足值域规格。 -/
theorem is_relation_range_member_iff (relation element : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[relation_range_operator_theory]
      is_relation_formula relation ⟶ₘ ((element ∈ₘ ranₘ(relation)) ↔ₘ ((element ∈ₘ
              double_union_term relation) ∧ₘ
              relation_range_member_condition
                relation element)) := by
  have hSpec :=
    is_relation_range_term_spec
      relation hRelation
  have hPoint :
      ⊢ₘ[relation_range_operator_theory]
        relation_range_spec
            relation (ranₘ(relation)) ⟶ₘ ((element ∈ₘ ranₘ(relation)) ↔ₘ ((element ∈ₘ
                double_union_term relation) ∧ₘ
              relation_range_member_condition
                relation element)) :=
    relation_range_spec_member_iff
      relation (ranₘ(relation)) element
      hRelation (range_term_admissible
        relation hRelation)
      hElement
  nd_apply FirstOrder.Derives.impIntro
  have hSpecInContext :=
    FirstOrder.Derives.context_weaken_cons (assumption := is_relation_formula relation)
      hSpec
  have hPointInContext :=
    FirstOrder.Derives.context_weaken_cons (assumption := is_relation_formula relation)
      hPoint
  exact FirstOrder.Derives.impElim
    hPointInContext (FirstOrder.Derives.impElim
      hSpecInContext (.assumption (by simp)))
/-! ## 全称闭包接口 -/
/-- 关系谓词定义的单变量全称闭包。 -/
theorem is_relation_iff_condition_forall (relation : FreeVarId) :
    ⊢ₘ[relation_predicate_theory]
      ∀ₘ[SetSort.set, relation],
        is_relation_formula (x#relation) ↔ₘ
          is_relation_condition (x#relation) := by
  derive_close (relation) using
    is_relation_iff_condition (x#relation) (set_variable_admissible relation)
/-- 关系成员必为有序对的双变量全称闭包。 -/
theorem is_relation_member_is_ordered_pair_forall (relation member : FreeVarId) :
    ⊢ₘ[relation_predicate_theory]
      ∀ₘ[SetSort.set, relation],
        ∀ₘ[SetSort.set, member],
          is_relation_formula (x#relation) ⟶ₘ (x#member ∈ₘ x#relation) ⟶ₘ
              is_ordered_pair_formula (x#member) := by
  derive_close (relation, member) using
    is_relation_member_is_ordered_pair (x#relation) (x#member) (set_variable_admissible relation) (set_variable_admissible member)
/-- 双重并集成员规格的双变量全称闭包。 -/
theorem double_union_member_iff_forall (relation element : FreeVarId) :
    ⊢ₘ[relation_base_theory]
      ∀ₘ[SetSort.set, relation],
        ∀ₘ[SetSort.set, element], (x#element ∈ₘ
              double_union_term (x#relation)) ↔ₘ
            double_union_member_condition (x#relation) (x#element) := by
  derive_close (relation, element) using
    double_union_member_iff (x#relation) (x#element) (set_variable_admissible relation) (set_variable_admissible element)
/-- 双重并集复合项存在性的单变量全称闭包。 -/
theorem double_union_term_exists_forall (relation : FreeVarId) :
    ⊢ₘ[relation_base_theory]
      ∀ₘ[SetSort.set, relation],
        double_union_term_exists (x#relation) := by
  derive_close (relation) using
    double_union_term_exists_derives (x#relation) (set_variable_admissible relation)
/-- 定义域存在性的单变量全称闭包。 -/
theorem is_relation_domain_exists_forall (relation : FreeVarId) :
    ⊢ₘ[relation_domain_theory]
      ∀ₘ[SetSort.set, relation],
        is_relation_formula (x#relation) ⟶ₘ
          relation_domain_exists (x#relation) := by
  derive_close (relation) using
    is_relation_implies_domain_exists (x#relation) (set_variable_admissible relation)
/-- 定义域唯一性的三变量全称闭包。 -/
theorem is_relation_domain_unique_forall (relation first second : FreeVarId) :
    ⊢ₘ[relation_domain_theory]
      ∀ₘ[SetSort.set, relation],
        ∀ₘ[SetSort.set, first],
          ∀ₘ[SetSort.set, second],
            is_relation_formula (x#relation) ⟶ₘ
              relation_domain_spec (x#relation) (x#first) ⟶ₘ
                relation_domain_spec (x#relation) (x#second) ⟶ₘ (x#first ≐ₘ x#second) := by
  derive_close (relation, first, second) using
    is_relation_domain_unique (x#relation) (x#first) (x#second) (set_variable_admissible relation) (set_variable_admissible first)
      (set_variable_admissible second)
/-- 定义域函数符号描述合同的双变量全称闭包。 -/
theorem domain_eq_iff_spec_forall (relation candidate : FreeVarId) :
    ⊢ₘ[relation_domain_operator_theory]
      ∀ₘ[SetSort.set, relation],
        ∀ₘ[SetSort.set, candidate],
          is_relation_formula (x#relation) ⟶ₘ ((x#candidate ≐ₘ
                domₘ(x#relation)) ↔ₘ
              relation_domain_spec (x#relation) (x#candidate)) := by
  derive_close (relation, candidate) using
    domain_eq_iff_spec (x#relation) (x#candidate) (set_variable_admissible relation) (set_variable_admissible candidate)
/-- `dom` 点态成员合同的双变量全称闭包。 -/
theorem is_relation_domain_member_iff_forall (relation element : FreeVarId) :
    ⊢ₘ[relation_domain_operator_theory]
      ∀ₘ[SetSort.set, relation],
        ∀ₘ[SetSort.set, element],
          is_relation_formula (x#relation) ⟶ₘ ((x#element ∈ₘ
                domₘ(x#relation)) ↔ₘ ((x#element ∈ₘ
                  double_union_term (x#relation)) ∧ₘ
                relation_domain_member_condition (x#relation) (x#element))) := by
  derive_close (relation, element) using
    is_relation_domain_member_iff (x#relation) (x#element) (set_variable_admissible relation) (set_variable_admissible element)
/-- 定义域函数项平凡存在性的单变量全称闭包。 -/
theorem is_relation_domain_term_exists_forall (relation : FreeVarId) :
    ⊢ₘ[relation_domain_operator_theory]
      ∀ₘ[SetSort.set, relation],
        is_relation_formula (x#relation) ⟶ₘ
          domain_term_exists (x#relation) := by
  derive_close (relation) using
    is_relation_implies_domain_term_exists (x#relation) (set_variable_admissible relation)
/-- 值域存在性的单变量全称闭包。 -/
theorem is_relation_range_exists_forall (relation : FreeVarId) :
    ⊢ₘ[relation_range_theory]
      ∀ₘ[SetSort.set, relation],
        is_relation_formula (x#relation) ⟶ₘ
          relation_range_exists (x#relation) := by
  derive_close (relation) using
    is_relation_implies_range_exists (x#relation) (set_variable_admissible relation)
/-- 值域唯一性的三变量全称闭包。 -/
theorem is_relation_range_unique_forall (relation first second : FreeVarId) :
    ⊢ₘ[relation_range_theory]
      ∀ₘ[SetSort.set, relation],
        ∀ₘ[SetSort.set, first],
          ∀ₘ[SetSort.set, second],
            is_relation_formula (x#relation) ⟶ₘ
              relation_range_spec (x#relation) (x#first) ⟶ₘ
                relation_range_spec (x#relation) (x#second) ⟶ₘ (x#first ≐ₘ x#second) := by
  derive_close (relation, first, second) using
    is_relation_range_unique (x#relation) (x#first) (x#second) (set_variable_admissible relation) (set_variable_admissible first)
      (set_variable_admissible second)
/-- 值域函数符号描述合同的双变量全称闭包。 -/
theorem range_eq_iff_spec_forall (relation candidate : FreeVarId) :
    ⊢ₘ[relation_range_operator_theory]
      ∀ₘ[SetSort.set, relation],
        ∀ₘ[SetSort.set, candidate],
          is_relation_formula (x#relation) ⟶ₘ ((x#candidate ≐ₘ
                ranₘ(x#relation)) ↔ₘ
              relation_range_spec (x#relation) (x#candidate)) := by
  derive_close (relation, candidate) using
    range_eq_iff_spec (x#relation) (x#candidate) (set_variable_admissible relation) (set_variable_admissible candidate)
/-- `range` 点态成员合同的双变量全称闭包。 -/
theorem is_relation_range_member_iff_forall (relation element : FreeVarId) :
    ⊢ₘ[relation_range_operator_theory]
      ∀ₘ[SetSort.set, relation],
        ∀ₘ[SetSort.set, element],
          is_relation_formula (x#relation) ⟶ₘ ((x#element ∈ₘ
                ranₘ(x#relation)) ↔ₘ ((x#element ∈ₘ
                  double_union_term (x#relation)) ∧ₘ
                relation_range_member_condition (x#relation) (x#element))) := by
  derive_close (relation, element) using
    is_relation_range_member_iff (x#relation) (x#element) (set_variable_admissible relation) (set_variable_admissible element)
/-- 文献定理 2.33：关系的规范值域函数项存在。 -/
theorem is_relation_range_term_exists_forall (relation : FreeVarId) :
    ⊢ₘ[relation_range_operator_theory]
      ∀ₘ[SetSort.set, relation],
        is_relation_formula (x#relation) ⟶ₘ (∃ₘ[SetSort.set],
            bₛ#0 ≐ₘ ranₘ(x#relation)) := by
  derive_close (relation) using
    is_relation_implies_range_term_exists (x#relation) (set_variable_admissible relation)
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
