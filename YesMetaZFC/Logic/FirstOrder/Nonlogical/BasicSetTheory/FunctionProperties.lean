import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Function
/-
# 关系与函数的属性层
本模块先落地关系与函数章节的基础设施：单射、满射、双射、恒等映射、
映射收集、传递集以及成员关系限制的现代对象语言规格。
文献索引 `DanS`、`ManS`、`ShuS`、`HanS`、`InSh`、`ChuD` 与 `ε` 只保留
在注释中。文献中的 `rng` 统一由公共的 `ranₘ`/`range` 接口承载。
截图中后续的闭性、存在唯一性和具体函数定理暂不伪造为公理；本模块只建立
它们未来证明所需的公式、分离实例、定义公理、理论链和 proof-carrying 边界。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 单射、满射与双射 -/
/-- 单射的单值逆像条件。文献索引为 `DanS`。 -/
def injectivity_condition (function : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set],
    ∀ₘ[SetSort.set],
      ∀ₘ[SetSort.set], ((⟨bₛ#2, bₛ#0⟩ₘ ∈ₘ function) ∧ₘ (⟨bₛ#1, bₛ#0⟩ₘ ∈ₘ function)) ⟶ₘ (bₛ#2 ≐ₘ bₛ#1)
/-- `function` 是从 `source` 到 `target` 的单射。 -/
def is_injective_condition (function source target : SetTerm) :
    SetFormula :=
  is_mapping_formula function source target ∧ₘ
    injectivity_condition function
/-- 单射谓词的开放定义实例。 -/
def is_injective_definition_instance (function source target : SetTerm) :
    SetFormula :=
  is_injective_formula function source target ↔ₘ
    is_injective_condition function source target
/-- 单射谓词定义公理。 -/
def is_injective_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        is_injective_definition_instance (x#0) (x#1) (x#2)
/-- 满射的现代规格。文献索引为 `ManS`，文献中的 `rng` 使用 `ranₘ`。 -/
def is_surjective_condition (function source target : SetTerm) :
    SetFormula :=
  is_function_formula function ∧ₘ ((source ≐ₘ domₘ(function)) ∧ₘ (target ≐ₘ ranₘ(function)))
/-- 满射谓词的开放定义实例。 -/
def is_surjective_definition_instance (function source target : SetTerm) :
    SetFormula :=
  is_surjective_formula function source target ↔ₘ
    is_surjective_condition function source target
/-- 满射谓词定义公理。 -/
def is_surjective_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        is_surjective_definition_instance (x#0) (x#1) (x#2)
/-- 双射就是同时满足单射与满射。文献索引为 `ShuS`。 -/
def is_bijection_condition (function source target : SetTerm) :
    SetFormula :=
  is_injective_formula function source target ∧ₘ
    is_surjective_formula function source target
/-- 双射谓词的开放定义实例。 -/
def is_bijection_definition_instance (function source target : SetTerm) :
    SetFormula :=
  is_bijection_formula function source target ↔ₘ
    is_bijection_condition function source target
/-- 双射谓词定义公理。 -/
def is_bijection_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        is_bijection_definition_instance (x#0) (x#1) (x#2)
/-! ## 恒等映射 -/
/--
恒等映射的成员条件。
该条件作为 `membership_specification` 的体使用；因此内层见证下的 `bₛ#1`
表示当前待筛选元素，`bₛ#0` 表示源集合中的见证。
-/
def identity_member_condition (source : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set], (bₛ#0 ∈ₘ source) ∧ₘ (bₛ#1 ≐ₘ ⟨bₛ#0, bₛ#0⟩ₘ)
/-- 恒等映射的成员规格。 -/
def identity_spec (source candidate : SetTerm) :
    SetFormula :=
  membership_specification
    candidate (identity_member_condition source)
/-- 恒等映射函数符号的开放定义实例。 -/
def identity_definition_instance (source candidate : SetTerm) :
    SetFormula := (candidate ≐ₘ Idₘ(source)) ↔ₘ
    identity_spec source candidate
/-- 恒等映射函数符号定义公理。 -/
def identity_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      identity_definition_instance (x#0) (x#1)
/--
恒等映射的闭分离实例。
母集取 `source × source`，这样分离出的集合天然位于源集合的平方中。
-/
def identity_separation_exists (source : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ((bₛ#0 ∈ₘ (source ×ₘ source)) ∧ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ source) ∧ₘ (bₛ#1 ≐ₘ ⟨bₛ#0, bₛ#0⟩ₘ)))
/-- 任意源集合上的恒等映射分离实例。 -/
def identity_separation_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    identity_separation_exists (x#0)
/-! ## 映射收集 -/
/-- 从 `source` 到 `target` 的映射收集规格。 -/
def mapping_collection_spec (source target candidate : SetTerm) :
    SetFormula := (candidate ∈ₘ 𝒫ₘ(source ×ₘ target)) ∧ₘ
    membership_specification
      candidate (is_mapping_formula bₛ#0 source target)
/-- 映射收集函数符号的开放定义实例。 -/
def mapping_collection_definition_instance (source target candidate : SetTerm) :
    SetFormula := (set_nonempty_condition source ∧ₘ
      set_nonempty_condition target) ⟶ₘ ((candidate ≐ₘ Mapₘ(source, target)) ↔ₘ
      mapping_collection_spec source target candidate)
/-- 映射收集函数符号定义公理。 -/
def mapping_collection_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        mapping_collection_definition_instance (x#0) (x#1) (x#2)
/-- 映射收集的闭分离实例。 -/
def mapping_collection_separation_exists (source target : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ((bₛ#0 ∈ₘ 𝒫ₘ(source ×ₘ target)) ∧ₘ
          is_mapping_formula bₛ#0 source target)
/-- 任意源集与目标集上的映射收集分离实例。 -/
def mapping_collection_separation_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      mapping_collection_separation_exists (x#0) (x#1)
/-! ## 传递集与成员关系限制 -/
/-- 传递集条件。文献索引为 `ChuD`。 -/
def is_transitive_set_condition (set : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ set) ⟶ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ⟶ₘ (bₛ#0 ∈ₘ set))
/-- 传递集谓词的开放定义实例。 -/
def is_transitive_set_definition_instance (set : SetTerm) :
    SetFormula :=
  is_transitive_set_formula set ↔ₘ
    is_transitive_set_condition set
/-- 传递集谓词定义公理。 -/
def is_transitive_set_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_transitive_set_definition_instance (x#0)
/--
成员关系限制的元素条件。
该条件作为 `membership_specification` 的体使用。两层内层见证下，
`bₛ#2` 是当前元素，`bₛ#1` 与 `bₛ#0` 分别是有序对的两个坐标。
-/
def membership_relation_member_condition : SetFormula :=
  ∃ₘ[SetSort.set],
    ∃ₘ[SetSort.set], (bₛ#2 ≐ₘ ⟨bₛ#1, bₛ#0⟩ₘ) ∧ₘ (bₛ#1 ∈ₘ bₛ#0)
/-- 成员关系限制的成员规格。 -/
def membership_relation_spec (source candidate : SetTerm) :
    SetFormula :=
  membership_specification
    candidate ((bₛ#0 ∈ₘ 𝒫ₘ(source ×ₘ source)) ∧ₘ
      membership_relation_member_condition)
/-- 成员关系限制函数符号的开放定义实例。 -/
def membership_relation_definition_instance (source candidate : SetTerm) :
    SetFormula :=
  is_transitive_set_formula source ⟶ₘ ((candidate ≐ₘ εₘ(source)) ↔ₘ
      membership_relation_spec source candidate)
/-- 成员关系限制函数符号定义公理。 -/
def membership_relation_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      membership_relation_definition_instance (x#0) (x#1)
/-- 成员关系限制的闭分离实例。 -/
def membership_relation_separation_exists (source : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ((bₛ#0 ∈ₘ 𝒫ₘ(source ×ₘ source)) ∧ₘ (∃ₘ[SetSort.set],
            ∃ₘ[SetSort.set], (bₛ#2 ≐ₘ ⟨bₛ#1, bₛ#0⟩ₘ) ∧ₘ (bₛ#1 ∈ₘ bₛ#0)))
/-- 任意源集合上的成员关系限制分离实例。 -/
def membership_relation_separation_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    membership_relation_separation_exists (x#0)
/-! ## 理论组合 -/
/-- 单射谓词层。 -/
def injective_predicate_theory : SetTheory :=
  Theory.insert
    is_injective_definition_axiom
    function_application_theory
/-- 满射谓词层。 -/
def surjective_predicate_theory : SetTheory :=
  Theory.insert
    is_surjective_definition_axiom
    injective_predicate_theory
/-- 双射谓词层。 -/
def bijection_predicate_theory : SetTheory :=
  Theory.insert
    is_bijection_definition_axiom
    surjective_predicate_theory
/-- 恒等映射存在与定义层。 -/
def identity_operator_theory : SetTheory :=
  Theory.insert
    identity_definition_axiom (Theory.insert
      identity_separation_axiom
      bijection_predicate_theory)
/-- 映射收集存在与定义层。 -/
def mapping_collection_operator_theory : SetTheory :=
  Theory.insert
    mapping_collection_definition_axiom (Theory.insert
      mapping_collection_separation_axiom
      identity_operator_theory)
/-- 传递集谓词层。 -/
def transitive_set_theory : SetTheory :=
  Theory.insert
    is_transitive_set_definition_axiom
    mapping_collection_operator_theory
/-- 成员关系限制存在与定义层。 -/
def membership_relation_operator_theory : SetTheory :=
  Theory.insert
    membership_relation_definition_axiom (Theory.insert
      membership_relation_separation_axiom
      transitive_set_theory)
/-! ## proof-carrying 项边界 -/
/-- 恒等映射项满足 proof-carrying 项边界。 -/
theorem identity_term_admissible (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    Term.Admissible (identity_term source)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .identity [⟨source, by assumption⟩]
      (by rfl) (by rfl)
/-- 映射收集项满足 proof-carrying 项边界。 -/
theorem mapping_collection_term_admissible (source target : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hTarget : Term.Admissible target SetSort.set) :
    Term.Admissible (mapping_collection_term source target)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .mappingCollection [⟨source, by assumption⟩, ⟨target, by assumption⟩]
      (by rfl) (by rfl)
/-- 成员关系限制项满足 proof-carrying 项边界。 -/
theorem membership_relation_term_admissible (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    Term.Admissible (membership_relation_term source)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .membershipRelation [⟨source, by assumption⟩]
      (by rfl) (by rfl)
/-! ## 公共良构性边界 -/
theorem is_injective_definition_axiom_admissible :
    Formula.Admissible
      is_injective_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_surjective_definition_axiom_admissible :
    Formula.Admissible
      is_surjective_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_bijection_definition_axiom_admissible :
    Formula.Admissible
      is_bijection_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem identity_definition_axiom_admissible :
    Formula.Admissible
      identity_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem identity_separation_axiom_admissible :
    Formula.Admissible
      identity_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem mapping_collection_definition_axiom_admissible :
    Formula.Admissible
      mapping_collection_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem mapping_collection_separation_axiom_admissible :
    Formula.Admissible
      mapping_collection_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_transitive_set_definition_axiom_admissible :
    Formula.Admissible
      is_transitive_set_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem membership_relation_definition_axiom_admissible :
    Formula.Admissible
      membership_relation_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem membership_relation_separation_axiom_admissible :
    Formula.Admissible
      membership_relation_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem injective_predicate_theory_admissible :
    Theory.Admissible injective_predicate_theory :=
  Theory.admissible_insert
    is_injective_definition_axiom_admissible
    function_application_theory_admissible
theorem surjective_predicate_theory_admissible :
    Theory.Admissible surjective_predicate_theory :=
  Theory.admissible_insert
    is_surjective_definition_axiom_admissible
    injective_predicate_theory_admissible
theorem bijection_predicate_theory_admissible :
    Theory.Admissible bijection_predicate_theory :=
  Theory.admissible_insert
    is_bijection_definition_axiom_admissible
    surjective_predicate_theory_admissible
theorem identity_operator_theory_admissible :
    Theory.Admissible identity_operator_theory :=
  Theory.admissible_insert
    identity_definition_axiom_admissible (Theory.admissible_insert
      identity_separation_axiom_admissible
      bijection_predicate_theory_admissible)
theorem mapping_collection_operator_theory_admissible :
    Theory.Admissible mapping_collection_operator_theory :=
  Theory.admissible_insert
    mapping_collection_definition_axiom_admissible (Theory.admissible_insert
      mapping_collection_separation_axiom_admissible
      identity_operator_theory_admissible)
theorem transitive_set_theory_admissible :
    Theory.Admissible transitive_set_theory :=
  Theory.admissible_insert
    is_transitive_set_definition_axiom_admissible
    mapping_collection_operator_theory_admissible
theorem membership_relation_operator_theory_admissible :
    Theory.Admissible membership_relation_operator_theory :=
  Theory.admissible_insert
    membership_relation_definition_axiom_admissible (Theory.admissible_insert
      membership_relation_separation_axiom_admissible
      transitive_set_theory_admissible)
/-! ## 闭理论边界 -/
@[derive_close_sentence]
theorem injective_predicate_theory_sentence
    {formula : SetFormula} (hFormula : injective_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_injective_definition_axiom_admissible
    · native_decide
  · exact function_application_theory_sentence hFormula
@[derive_close_sentence]
theorem surjective_predicate_theory_sentence
    {formula : SetFormula} (hFormula : surjective_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_surjective_definition_axiom_admissible
    · native_decide
  · exact injective_predicate_theory_sentence hFormula
@[derive_close_sentence]
theorem bijection_predicate_theory_sentence
    {formula : SetFormula} (hFormula : bijection_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_bijection_definition_axiom_admissible
    · native_decide
  · exact surjective_predicate_theory_sentence hFormula
@[derive_close_sentence]
theorem identity_operator_theory_sentence
    {formula : SetFormula} (hFormula : identity_operator_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact identity_definition_axiom_admissible
    · native_decide
  · rcases hFormula with rfl | hFormula
    · constructor
      · exact identity_separation_axiom_admissible
      · native_decide
    · exact bijection_predicate_theory_sentence hFormula
@[derive_close_sentence]
theorem mapping_collection_operator_theory_sentence
    {formula : SetFormula} (hFormula : mapping_collection_operator_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact mapping_collection_definition_axiom_admissible
    · native_decide
  · rcases hFormula with rfl | hFormula
    · constructor
      · exact mapping_collection_separation_axiom_admissible
      · native_decide
    · exact identity_operator_theory_sentence hFormula
@[derive_close_sentence]
theorem transitive_set_theory_sentence
    {formula : SetFormula} (hFormula : transitive_set_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_transitive_set_definition_axiom_admissible
    · native_decide
  · exact mapping_collection_operator_theory_sentence hFormula
@[derive_close_sentence]
theorem membership_relation_operator_theory_sentence
    {formula : SetFormula} (hFormula : membership_relation_operator_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact membership_relation_definition_axiom_admissible
    · native_decide
  · rcases hFormula with rfl | hFormula
    · constructor
      · exact membership_relation_separation_axiom_admissible
      · native_decide
    · exact transitive_set_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem function_application_theory_subset_injective_predicate_theory
    {formula : SetFormula} (hFormula : function_application_theory formula) :
    injective_predicate_theory formula :=
  Or.inr hFormula
theorem injective_predicate_theory_subset_surjective_predicate_theory
    {formula : SetFormula} (hFormula : injective_predicate_theory formula) :
    surjective_predicate_theory formula :=
  Or.inr hFormula
theorem surjective_predicate_theory_subset_bijection_predicate_theory
    {formula : SetFormula} (hFormula : surjective_predicate_theory formula) :
    bijection_predicate_theory formula :=
  Or.inr hFormula
theorem bijection_predicate_theory_subset_identity_operator_theory
    {formula : SetFormula} (hFormula : bijection_predicate_theory formula) :
    identity_operator_theory formula :=
  Or.inr (Or.inr hFormula)
theorem identity_operator_theory_subset_mapping_collection_operator_theory
    {formula : SetFormula} (hFormula : identity_operator_theory formula) :
    mapping_collection_operator_theory formula :=
  Or.inr (Or.inr hFormula)
theorem mapping_collection_operator_theory_subset_transitive_set_theory
    {formula : SetFormula} (hFormula : mapping_collection_operator_theory formula) :
    transitive_set_theory formula :=
  Or.inr hFormula
theorem transitive_set_theory_subset_membership_relation_operator_theory
    {formula : SetFormula} (hFormula : transitive_set_theory formula) :
    membership_relation_operator_theory formula :=
  Or.inr (Or.inr hFormula)
/-!
## 待证明定理索引
下面的文献定理只作为后续证明任务的模块索引，不在当前基础设施层伪造为
`axiom` 或带 `sorry` 的声明：
* 2.41：双射在有序对反转下的可逆性；
* 2.42：恒等映射、映射复合、函数/单射/满射/双射的闭性；
* 2.43：常值映射的限制与存在唯一性；
* 2.44：恒等映射的性质与映射全体的存在唯一性；
* 2.45：传递集的空集、后继、幂集、并集及成员对性质；
* 2.46：传递集上的成员关系限制存在唯一性及其定义公理合同。
这些定理应在本模块的公式规格和理论链之上，按需使用 `prove_auto` 或手工
证明；它们不属于符号与理论基础设施本身。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
