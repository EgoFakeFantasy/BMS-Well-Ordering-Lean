import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.HypertransfiniteRecursion
/-!
# 彻底有限集合
本模块建立有限层级与遗传有限集的定义设施：
* `Vseqₘ` 是以空集为初值、以后继位置取幂集的有限层级递归序列；
* `Vωₘ` 是有限层级值域的并集，通常记作 `V_ω`；
* `tcₘ` 是传递闭包描述符；
* `hereditarily_finiteₘ` 以传递闭包的有穷性定义遗传有限；
* `FinSubₘ(A)` 是 `A` 的全部有限子集组成的集合。
自然数上的纸面关系 `< = ∈_ω` 直接复用已有的成员关系限制项
`εₘ(ωₘ)`，不再为一个可由现有构造表达的关系重复引入原子符号。
文献中的 `CDYQ`、`CDBB`、`YXZJ`、`DGSJ` 与有限编号仅保留为注释索引。
本模块只落定义公理、分离接口、记号和 proof-carrying 良构性边界；有限层级的
存在性、遗传有限集闭性、有限编码和后续典型列举定理留给后续证明层。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 传递闭包 -/
/-- `candidate` 是 `source` 的最小传递超集。 -/
def transitive_closure_spec (source candidate : SetTerm) :
    SetFormula := ((source ⊆ₘ candidate) ∧ₘ
      is_transitive_set_formula candidate) ∧ₘ (∀ₘ[SetSort.set], (((source ⊆ₘ bₛ#0) ∧ₘ
          is_transitive_set_formula bₛ#0) ⟶ₘ (candidate ⊆ₘ bₛ#0)))
/-- 传递闭包函数符号的开放定义实例；文献索引为 `CDBB`。 -/
def transitive_closure_definition_instance (source candidate : SetTerm) :
    SetFormula := (candidate ≐ₘ tcₘ(source)) ↔ₘ
    transitive_closure_spec source candidate
/-- 传递闭包定义公理。 -/
def transitive_closure_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      transitive_closure_definition_instance (x#0) (x#1)
/-! ## 有限层级与 `V_ω` -/
/-- 有限层级递归步：下一层是当前层的幂集。 -/
def finite_hierarchy_step_body : SetFormula :=
  x#2 ≐ₘ 𝒫ₘ(x#1)
/-- 有限层级递归步的 proof-carrying 参数。 -/
def finite_hierarchy_step : RecursiveStep where
  body := finite_hierarchy_step_body
  admissible := by
    apply Formula.check_admissible_sound
    native_decide
/-- 有限层级序列的递归规格。 -/
def finite_hierarchy_spec (sequence : SetTerm) :
    SetFormula :=
  transfinite_recursion_spec
    finite_hierarchy_step
    ∅ₘ
    sequence
/-- 有限层级递归序列定义公理；文献中对应 `V₀`、`Vₙ₊₁` 的约定。 -/
def finite_hierarchy_definition_axiom : SetFormula :=
  finite_hierarchy_spec Vseqₘ
/-- 有限层级值域的并集规格；通常记作 `V_ω`。 -/
def finite_universe_spec (universe_set : SetTerm) :
    SetFormula :=
  universe_set ≐ₘ ⋃ₘ(ranₘ(Vseqₘ))
/-- `V_ω` 定义公理。 -/
def finite_universe_definition_axiom : SetFormula :=
  finite_universe_spec Vωₘ
/-- `V_ω` 以上有限个幂集层的元层项构造。 -/
def finite_universe_successor_term : Nat → SetTerm
  | 0 => Vωₘ
  | n + 1 => 𝒫ₘ(finite_universe_successor_term n)
/-- 有限层级序列在指定自然数处的函数求值项。 -/
abbrev finite_hierarchy_value_term (index : SetTerm) :
    SetTerm :=
  Vseqₘ ·ₘ index
namespace Symbols
/-- 有限层级序列在指定指标处的值。 -/
scoped notation:max "Vₘ(" index ")" =>
  finite_hierarchy_value_term index
/-- 从 `V_ω` 开始迭代有限次幂集。 -/
scoped notation:max "Vω⁺ₘ[" level "]" =>
  finite_universe_successor_term level
end Symbols
/-! ## 自然数上的成员序 -/
/-- 自然数上的成员序关系项，即 `εₘ(ωₘ)`。 -/
abbrev natural_membership_order_term : SetTerm :=
  εₘ(ωₘ)
/-- 自然数成员序的点态条件；文献记号为 `< = ∈_ω`。 -/
def natural_membership_order_condition (left right : SetTerm) :
    SetFormula := (left ∈ₘ ωₘ) ∧ₘ ((right ∈ₘ ωₘ) ∧ₘ (left ∈ₘ right))
/-- 自然数成员序关系项的点态规格。 -/
def natural_membership_order_spec (relation : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (⟨bₛ#1, bₛ#0⟩ₘ ∈ₘ relation) ↔ₘ
        natural_membership_order_condition
          bₛ#1 bₛ#0
/-! ## 遗传有限集 -/
/-- 集合遗传有限，当且仅当其传递闭包是有穷集。 -/
def hereditarily_finite_condition (set : SetTerm) :
    SetFormula :=
  finiteₘ(tcₘ(set))
/-- 遗传有限谓词的开放定义实例；文献索引为 `CDYQ`。 -/
def hereditarily_finite_definition_instance (set : SetTerm) :
    SetFormula :=
  hereditarily_finiteₘ(set) ↔ₘ
    hereditarily_finite_condition set
/-- 遗传有限谓词定义公理。 -/
def hereditarily_finite_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    hereditarily_finite_definition_instance (x#0)
/-! ## 有限子集收集 -/
/-- `source` 的有限子集成员条件。 -/
def finite_subset_collection_member_condition (source : SetTerm) :
    SetFormula := (bₛ#0 ∈ₘ 𝒫ₘ(source)) ∧ₘ
    finiteₘ(bₛ#0)
/-- `FinSubₘ(source)` 的成员规格。 -/
def finite_subset_collection_spec (source candidate : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ candidate) ↔ₘ
      finite_subset_collection_member_condition source
/-- 对固定源集断言有限子集收集存在。 -/
def finite_subset_collection_separation_exists (source : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    finite_subset_collection_spec source bₛ#0
/-- 任意源集上的有限子集收集分离公理。 -/
def finite_subset_collection_separation_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    finite_subset_collection_separation_exists (x#0)
/-- 有限子集收集函数符号的开放定义实例；文献索引为 `YXZJ`。 -/
def finite_subset_collection_definition_instance (source candidate : SetTerm) :
    SetFormula := (candidate ≐ₘ FinSubₘ(source)) ↔ₘ
    finite_subset_collection_spec source candidate
/-- 有限子集收集函数符号定义公理。 -/
def finite_subset_collection_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      finite_subset_collection_definition_instance (x#0) (x#1)
/-! ## 理论组合 -/
/--
传递闭包定义层。
本文件只加入定义公理，不证明传递闭包或有限层级的集合存在性；因此基础依赖精确
收缩为自然数算术层。替换模式留给真正的递归存在性定理，不再虚挂在编码定义链上。
-/
def transitive_closure_operator_theory : SetTheory :=
  Theory.insert
    transitive_closure_definition_axiom
    natural_arithmetic_theory
/-- 有限层级递归序列定义层。 -/
def finite_hierarchy_operator_theory : SetTheory :=
  Theory.insert
    finite_hierarchy_definition_axiom
    transitive_closure_operator_theory
/-- `V_ω` 定义层。 -/
def finite_universe_operator_theory : SetTheory :=
  Theory.insert
    finite_universe_definition_axiom
    finite_hierarchy_operator_theory
/-- 遗传有限谓词定义层。 -/
def hereditarily_finite_predicate_theory : SetTheory :=
  Theory.insert
    hereditarily_finite_definition_axiom
    finite_universe_operator_theory
/-- 有限子集收集的分离层。 -/
def finite_subset_collection_separation_theory : SetTheory :=
  Theory.insert
    finite_subset_collection_separation_axiom
    hereditarily_finite_predicate_theory
/-- 有限子集收集函数符号定义层。 -/
def finite_subset_collection_operator_theory : SetTheory :=
  Theory.insert
    finite_subset_collection_definition_axiom
    finite_subset_collection_separation_theory
/-- 彻底有限集合层的统一理论入口。 -/
def hereditarily_finite_theory : SetTheory :=
  finite_subset_collection_operator_theory
/-! ## proof-carrying 项边界 -/
theorem transitive_closure_term_admissible (set : SetTerm) (hSet : Term.Admissible set SetSort.set) :
    Term.Admissible (tcₘ(set)) SetSort.set := by
  simpa using
    set_function_application_admissible
      .transitiveClosure [⟨set, by assumption⟩]
      (by rfl) (by rfl)
theorem finite_hierarchy_term_admissible :
    Term.Admissible Vseqₘ SetSort.set := by
  simpa using
    set_function_application_admissible
      .finiteHierarchy []
      (by rfl) (by rfl)
theorem finite_universe_term_admissible :
    Term.Admissible Vωₘ SetSort.set := by
  simpa using
    set_function_application_admissible
      .finiteUniverse []
      (by rfl) (by rfl)
theorem finite_hierarchy_value_term_admissible (index : SetTerm) (hIndex : Term.Admissible index SetSort.set) :
    Term.Admissible (finite_hierarchy_value_term index)
      SetSort.set :=
  function_application_term_admissible
    Vseqₘ index
    finite_hierarchy_term_admissible
    hIndex
theorem finite_universe_successor_term_admissible (level : Nat) :
    Term.Admissible (finite_universe_successor_term level)
      SetSort.set := by
  induction level with
  | zero =>
      exact finite_universe_term_admissible
  | succ level ih =>
      exact power_set_term_admissible _
        ih
theorem finite_subset_collection_term_admissible (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    Term.Admissible (FinSubₘ(source))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .finiteSubsetCollection [⟨source, by assumption⟩]
      (by rfl) (by rfl)
theorem natural_membership_order_term_admissible :
    Term.Admissible natural_membership_order_term SetSort.set :=
  membership_relation_term_admissible
    ωₘ omega_term_admissible
/-! ## 良构性与理论边界 -/
theorem transitive_closure_definition_axiom_admissible :
    Formula.Admissible
      transitive_closure_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_hierarchy_definition_axiom_admissible :
    Formula.Admissible
      finite_hierarchy_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_universe_definition_axiom_admissible :
    Formula.Admissible
      finite_universe_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem hereditarily_finite_definition_axiom_admissible :
    Formula.Admissible
      hereditarily_finite_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_subset_collection_separation_axiom_admissible :
    Formula.Admissible
      finite_subset_collection_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_subset_collection_definition_axiom_admissible :
    Formula.Admissible
      finite_subset_collection_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem transitive_closure_operator_theory_admissible :
    Theory.Admissible transitive_closure_operator_theory :=
  Theory.admissible_insert
    transitive_closure_definition_axiom_admissible
    natural_arithmetic_theory_admissible
theorem finite_hierarchy_operator_theory_admissible :
    Theory.Admissible finite_hierarchy_operator_theory :=
  Theory.admissible_insert
    finite_hierarchy_definition_axiom_admissible
    transitive_closure_operator_theory_admissible
theorem finite_universe_operator_theory_admissible :
    Theory.Admissible finite_universe_operator_theory :=
  Theory.admissible_insert
    finite_universe_definition_axiom_admissible
    finite_hierarchy_operator_theory_admissible
theorem hereditarily_finite_predicate_theory_admissible :
    Theory.Admissible hereditarily_finite_predicate_theory :=
  Theory.admissible_insert
    hereditarily_finite_definition_axiom_admissible
    finite_universe_operator_theory_admissible
theorem finite_subset_collection_separation_theory_admissible :
    Theory.Admissible
      finite_subset_collection_separation_theory :=
  Theory.admissible_insert
    finite_subset_collection_separation_axiom_admissible
    hereditarily_finite_predicate_theory_admissible
theorem finite_subset_collection_operator_theory_admissible :
    Theory.Admissible
      finite_subset_collection_operator_theory :=
  Theory.admissible_insert
    finite_subset_collection_definition_axiom_admissible
    finite_subset_collection_separation_theory_admissible
theorem hereditarily_finite_theory_admissible :
    Theory.Admissible hereditarily_finite_theory :=
  finite_subset_collection_operator_theory_admissible
/-! ## 闭理论边界与嵌入 -/
@[derive_close_sentence]
theorem transitive_closure_operator_theory_sentence
    {formula : SetFormula} (hFormula : transitive_closure_operator_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact transitive_closure_definition_axiom_admissible
    · native_decide
  · exact natural_arithmetic_theory_sentence hFormula
@[derive_close_sentence]
theorem finite_hierarchy_operator_theory_sentence
    {formula : SetFormula} (hFormula : finite_hierarchy_operator_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact finite_hierarchy_definition_axiom_admissible
    · native_decide
  · exact transitive_closure_operator_theory_sentence hFormula
@[derive_close_sentence]
theorem finite_universe_operator_theory_sentence
    {formula : SetFormula} (hFormula : finite_universe_operator_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact finite_universe_definition_axiom_admissible
    · native_decide
  · exact finite_hierarchy_operator_theory_sentence hFormula
@[derive_close_sentence]
theorem hereditarily_finite_predicate_theory_sentence
    {formula : SetFormula} (hFormula : hereditarily_finite_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact hereditarily_finite_definition_axiom_admissible
    · native_decide
  · exact finite_universe_operator_theory_sentence hFormula
@[derive_close_sentence]
theorem finite_subset_collection_separation_theory_sentence
    {formula : SetFormula} (hFormula : finite_subset_collection_separation_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact finite_subset_collection_separation_axiom_admissible
    · native_decide
  · exact hereditarily_finite_predicate_theory_sentence hFormula
@[derive_close_sentence]
theorem finite_subset_collection_operator_theory_sentence
    {formula : SetFormula} (hFormula : finite_subset_collection_operator_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact finite_subset_collection_definition_axiom_admissible
    · native_decide
  · exact finite_subset_collection_separation_theory_sentence hFormula
@[derive_close_sentence]
theorem hereditarily_finite_theory_sentence
    {formula : SetFormula} (hFormula : hereditarily_finite_theory formula) :
    Formula.Sentence formula :=
  finite_subset_collection_operator_theory_sentence hFormula
theorem natural_arithmetic_theory_subset_transitive_closure_operator_theory
    {formula : SetFormula} (hFormula : natural_arithmetic_theory formula) :
    transitive_closure_operator_theory formula :=
  Or.inr hFormula
theorem transitive_closure_operator_theory_subset_finite_hierarchy_operator_theory
    {formula : SetFormula} (hFormula : transitive_closure_operator_theory formula) :
    finite_hierarchy_operator_theory formula :=
  Or.inr hFormula
theorem finite_hierarchy_operator_theory_subset_finite_universe_operator_theory
    {formula : SetFormula} (hFormula : finite_hierarchy_operator_theory formula) :
    finite_universe_operator_theory formula :=
  Or.inr hFormula
theorem finite_universe_operator_theory_subset_hereditarily_finite_predicate_theory
    {formula : SetFormula} (hFormula : finite_universe_operator_theory formula) :
    hereditarily_finite_predicate_theory formula :=
  Or.inr hFormula
theorem hereditarily_finite_predicate_theory_subset_finite_subset_collection_separation_theory
    {formula : SetFormula} (hFormula : hereditarily_finite_predicate_theory formula) :
    finite_subset_collection_separation_theory formula :=
  Or.inr hFormula
theorem finite_subset_collection_separation_theory_subset_hereditarily_finite_theory
    {formula : SetFormula} (hFormula : finite_subset_collection_separation_theory formula) :
    hereditarily_finite_theory formula :=
  Or.inr hFormula
/-! ## 定理留位 -/
/-!
后续证明层按需承载以下文献内容：
* `V₀ = ∅`、`Vₙ₊₁ = 𝒫(Vₙ)` 与 `V_ω = ⋃ range(Vseqₘ)` 的具体展开；
* `V_{ω+n}` 的有限幂集层闭性；
* 遗传有限集对空集、配对、幂集、并集和有限子集收集的闭性；
* 自然数成员序、有限二进制编码及 `V_ω` 内的典型列举；
* 有限序列、有限函数与后续递归编码的存在性与唯一性。
这些内容都消费本模块的定义公理和 `finite_*_term_admissible` 接口，不在基础设施
层预先引入文献编号或机械证明展开。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
