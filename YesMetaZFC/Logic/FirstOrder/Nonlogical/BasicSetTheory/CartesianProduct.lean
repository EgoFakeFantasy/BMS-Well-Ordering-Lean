import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationFunction
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Union
/-!
# 笛卡尔积
文献先为若干层并集、幂集复合分别加入定义公理，再在
`𝒫ₘ(𝒫ₘ(left ∪ₘ right))` 上应用分离。新核已经把这些构造作为原子函数项及其
proof-carrying 定义合同，因此本模块只保留可复用的复合项接口，并把真正新增的
数学内容限制为一个闭分离实例。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 复合母集 -/
/-- 文献三重复合对应的幂集项。 -/
abbrev power_set_binary_union_term (left right : SetTerm) :
    SetTerm :=
  𝒫ₘ(left ∪ₘ right)
/-- 笛卡尔积构造使用的四重复合母集。 -/
abbrev cartesian_product_bound_term (left right : SetTerm) :
    SetTerm :=
  𝒫ₘ(𝒫ₘ(left ∪ₘ right))
/-! ## 笛卡尔积规格 -/
/--
`element` 是 `left` 与 `right` 中元素组成的规范有序对。
该公式只用于 bound-closed 的 `element` 参数；在集合规格的元素 binder 下，
对应的原始 locally nameless 公式由 `cartesian_product_spec` 直接给出。
-/
def cartesian_product_member_condition (left right element : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∃ₘ[SetSort.set], (bₛ#1 ∈ₘ left) ∧ₘ ((bₛ#0 ∈ₘ right) ∧ₘ (element ≐ₘ ⟨bₛ#1, bₛ#0⟩ₘ))
/--
`product` 是从标准母集中分离出的笛卡尔积。
最内层两个存在 binder 依次引入左、右坐标，因此 `bₛ#2` 指向最外层的当前元素。
-/
def cartesian_product_spec (left right product : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ product) ↔ₘ ((bₛ#0 ∈ₘ
          cartesian_product_bound_term left right) ∧ₘ (∃ₘ[SetSort.set],
          ∃ₘ[SetSort.set], (bₛ#1 ∈ₘ left) ∧ₘ ((bₛ#0 ∈ₘ right) ∧ₘ (bₛ#2 ≐ₘ
                  ⟨bₛ#1, bₛ#0⟩ₘ))))
/-- 对固定两个集合断言满足上述规格的结果存在。 -/
def cartesian_product_exists (left right : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ((bₛ#0 ∈ₘ
            cartesian_product_bound_term left right) ∧ₘ (∃ₘ[SetSort.set],
            ∃ₘ[SetSort.set], (bₛ#1 ∈ₘ left) ∧ₘ ((bₛ#0 ∈ₘ right) ∧ₘ (bₛ#2 ≐ₘ
                    ⟨bₛ#1, bₛ#0⟩ₘ))))
/-- 笛卡尔积筛选谓词体所在的三层集合变量 scope。 -/
private abbrev cartesian_product_predicate_scope :
    Scope signature :=
  Scope.push (Scope.push (Scope.push Scope.empty SetSort.set)
      SetSort.set)
    SetSort.set
/--
以任意 admissible 集合项为参数的笛卡尔积筛选谓词。
公共自由变量版本只是该 proof-carrying 构造器的一个实例；规格与存在式的
admissibility 因而可以统一复用分离层。
-/
private def cartesian_product_term_predicate (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    SetPredicate where
  body :=
    ∃ₘ[SetSort.set],
      ∃ₘ[SetSort.set], (bₛ#1 ∈ₘ left) ∧ₘ ((bₛ#0 ∈ₘ right) ∧ₘ (bₛ#2 ≐ₘ
              ⟨bₛ#1, bₛ#0⟩ₘ))
  admissible_at := by
    prove_admissible_at
/-- 以自由参数表示的笛卡尔积筛选谓词。 -/
def cartesian_product_predicate (left right : FreeVarId) :
    SetPredicate :=
  cartesian_product_term_predicate (x#left) (x#right) (set_variable_admissible left) (set_variable_admissible right)
/-- 文献中笛卡尔积构造所需的闭分离实例。 -/
def cartesian_product_separation_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      cartesian_product_exists (x#0) (x#1)
/-! ## 理论组合 -/
/--
复合母集与规范有序对所需的最小描述符理论。
交集、投影与反转不参与笛卡尔积存在唯一性的核心证明。
-/
def cartesian_product_base_theory : SetTheory :=
  Theory.union
    ordered_pair_operator_theory (Theory.union
      power_set_operator_theory
      binary_union_operator_theory)
/-- 在复合项基础上加入笛卡尔积的闭分离实例。 -/
def cartesian_product_theory : SetTheory :=
  Theory.insert
    cartesian_product_separation_axiom
    cartesian_product_base_theory
/-- 笛卡尔积函数符号的开放定义实例。 -/
def cartesian_product_definition_instance (left right candidate : SetTerm) :
    SetFormula := (candidate ≐ₘ (left ×ₘ right)) ↔ₘ
    cartesian_product_spec left right candidate
/-- 笛卡尔积函数符号的定义公理。 -/
def cartesian_product_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        cartesian_product_definition_instance (x#0) (x#1) (x#2)
/-- 在笛卡尔积存在理论上加入二元函数符号。 -/
def cartesian_product_operator_theory : SetTheory :=
  Theory.insert
    cartesian_product_definition_axiom
    cartesian_product_theory
/-! ## 良构性与闭理论边界 -/
/-- 文献三重复合项保持 proof-carrying 项边界。 -/
theorem power_set_binary_union_term_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible (power_set_binary_union_term left right)
      SetSort.set :=
  power_set_term_admissible (left ∪ₘ right) (binary_union_term_admissible
      left right hLeft hRight)
/-- 笛卡尔积母集项保持 proof-carrying 项边界。 -/
theorem cartesian_product_bound_term_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible (cartesian_product_bound_term left right)
      SetSort.set :=
  power_set_term_admissible (power_set_binary_union_term left right) (power_set_binary_union_term_admissible
      left right hLeft hRight)
/-- 笛卡尔积函数项保持 proof-carrying 项边界。 -/
theorem cartesian_product_term_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible (cartesian_product_term left right)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .cartesianProduct [⟨left, by assumption⟩, ⟨right, by assumption⟩]
      (by rfl) (by rfl)
/-- 笛卡尔积项的合法性由两个因子项证书组合。 -/
@[term_check]
theorem cartesian_product_term_check
    {left right : SetTerm}
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set) :
    Term.CheckCertificate
      (cartesian_product_term left right) SetSort.set :=
  Term.check_admissible_complete <|
    cartesian_product_term_admissible
      left right hLeft.admissible hRight.admissible
/-- 笛卡尔积成员条件保持公式 admissibility。 -/
theorem cartesian_product_member_condition_admissible
    {left right element : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hElement : Term.Admissible element SetSort.set) :
    Formula.Admissible (cartesian_product_member_condition
        left right element) := by
  prove_admissible
/-- 笛卡尔积规格保持公式 admissibility。 -/
theorem cartesian_product_spec_admissible
    {left right product : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hProduct : Term.Admissible product SetSort.set) :
    Formula.Admissible (cartesian_product_spec left right product) := by
  have hSeparation :=
    SetPredicate.separation_spec_admissible (cartesian_product_term_predicate
        left right hLeft hRight) (cartesian_product_bound_term_admissible
        left right hLeft hRight)
      hProduct
  simpa [SetPredicate.separation_spec,
    cartesian_product_term_predicate,
    cartesian_product_spec] using hSeparation
/-- 笛卡尔积存在式保持公式 admissibility。 -/
theorem cartesian_product_exists_admissible
    {left right : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Formula.Admissible (cartesian_product_exists left right) := by
  have hSeparation :=
    SetPredicate.separation_exists_admissible (cartesian_product_term_predicate
        left right hLeft hRight) (cartesian_product_bound_term_admissible
        left right hLeft hRight)
  simpa [SetPredicate.separation_exists,
    cartesian_product_term_predicate,
    cartesian_product_exists] using hSeparation
/-- 笛卡尔积函数符号定义实例保持公式 admissibility。 -/
theorem cartesian_product_definition_instance_admissible
    {left right candidate : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (cartesian_product_definition_instance
        left right candidate) :=
  Formula.Admissible.iff (Formula.Admissible.equal
      hCandidate (cartesian_product_term_admissible
        left right hLeft hRight)) (cartesian_product_spec_admissible
      hLeft hRight hCandidate)
/-- 闭笛卡尔积分离公理满足公共良构性边界。 -/
theorem cartesian_product_separation_axiom_admissible :
    Formula.Admissible
      cartesian_product_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 笛卡尔积复合项基础理论仍然 admissible。 -/
theorem cartesian_product_base_theory_admissible :
    Theory.Admissible cartesian_product_base_theory := by
  intro formula hFormula
  rcases hFormula with hFormula | hFormula
  · exact ordered_pair_operator_theory_admissible
      formula hFormula
  · rcases hFormula with hFormula | hFormula
    · exact power_set_operator_theory_admissible
        formula hFormula
    · exact binary_union_operator_theory_admissible
        formula hFormula
/-- 加入闭分离实例后的笛卡尔积理论仍然 admissible。 -/
theorem cartesian_product_theory_admissible :
    Theory.Admissible cartesian_product_theory :=
  Theory.admissible_insert
    cartesian_product_separation_axiom_admissible
    cartesian_product_base_theory_admissible
/-- 笛卡尔积函数符号定义公理满足公共良构性边界。 -/
theorem cartesian_product_definition_axiom_admissible :
    Formula.Admissible
      cartesian_product_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 笛卡尔积函数符号扩张后的理论仍然 admissible。 -/
theorem cartesian_product_operator_theory_admissible :
    Theory.Admissible
      cartesian_product_operator_theory :=
  Theory.admissible_insert
    cartesian_product_definition_axiom_admissible
    cartesian_product_theory_admissible
/-- 笛卡尔积复合项基础理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem cartesian_product_base_theory_sentence
    {formula : SetFormula} (hFormula : cartesian_product_base_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with hFormula | hFormula
  · exact ordered_pair_operator_theory_sentence
      hFormula
  · rcases hFormula with hFormula | hFormula
    · exact power_set_operator_theory_sentence
        hFormula
    · exact binary_union_operator_theory_sentence
        hFormula
/-- 笛卡尔积理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem cartesian_product_theory_sentence
    {formula : SetFormula} (hFormula : cartesian_product_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact cartesian_product_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · exact (cartesian_product_base_theory_sentence
          hFormula).2
/-- 笛卡尔积函数符号理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem cartesian_product_operator_theory_sentence
    {formula : SetFormula} (hFormula :
      cartesian_product_operator_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact cartesian_product_operator_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · exact (cartesian_product_theory_sentence hFormula).2
/-! ## 理论嵌入 -/
/-- 有序对描述符理论嵌入笛卡尔积基础理论。 -/
theorem ordered_pair_operator_theory_subset_cartesian_product_base_theory
    {formula : SetFormula} (hFormula : ordered_pair_operator_theory formula) :
    cartesian_product_base_theory formula :=
  Or.inl hFormula
/-- 幂集描述符理论嵌入笛卡尔积基础理论。 -/
theorem power_set_operator_theory_subset_cartesian_product_base_theory
    {formula : SetFormula} (hFormula : power_set_operator_theory formula) :
    cartesian_product_base_theory formula :=
  Or.inr (Or.inl hFormula)
/-- 二元并描述符理论嵌入笛卡尔积基础理论。 -/
theorem binary_union_operator_theory_subset_cartesian_product_base_theory
    {formula : SetFormula} (hFormula : binary_union_operator_theory formula) :
    cartesian_product_base_theory formula :=
  Or.inr (Or.inr hFormula)
/-- 笛卡尔积基础理论嵌入闭分离理论。 -/
theorem cartesian_product_base_theory_subset_cartesian_product_theory
    {formula : SetFormula} (hFormula : cartesian_product_base_theory formula) :
    cartesian_product_theory formula :=
  Or.inr hFormula
/-- 笛卡尔积存在理论嵌入函数符号理论。 -/
theorem cartesian_product_theory_subset_cartesian_product_operator_theory
    {formula : SetFormula} (hFormula : cartesian_product_theory formula) :
    cartesian_product_operator_theory formula :=
  Or.inr hFormula
/-- 笛卡尔积基础理论嵌入函数符号理论。 -/
theorem cartesian_product_base_theory_subset_cartesian_product_operator_theory
    {formula : SetFormula} (hFormula : cartesian_product_base_theory formula) :
    cartesian_product_operator_theory formula :=
  cartesian_product_theory_subset_cartesian_product_operator_theory (cartesian_product_base_theory_subset_cartesian_product_theory
      hFormula)
/-- 外延理论嵌入笛卡尔积基础理论。 -/
theorem extensionality_theory_subset_cartesian_product_base_theory
    {formula : SetFormula} (hFormula : extensionality_theory formula) :
    cartesian_product_base_theory formula :=
  ordered_pair_operator_theory_subset_cartesian_product_base_theory (extensionality_theory_subset_ordered_pair_operator_theory
      hFormula)
/-! ## 三重与四重复合合同 -/
/-- 文献三重复合项满足幂集规格。 -/
theorem power_set_binary_union_term_spec_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[cartesian_product_base_theory]
      power_set_spec (left ∪ₘ right) (power_set_binary_union_term left right) :=
  FirstOrder.Derives.theory_weaken (fun _ hFormula =>
      power_set_operator_theory_subset_cartesian_product_base_theory
        hFormula) (power_set_term_spec_derives (left ∪ₘ right) (binary_union_term_admissible
        left right hLeft hRight))
/-- 文献四重复合母集满足外层幂集规格。 -/
theorem cartesian_product_bound_term_spec_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[cartesian_product_base_theory]
      power_set_spec (power_set_binary_union_term left right) (cartesian_product_bound_term left right) :=
  FirstOrder.Derives.theory_weaken (fun _ hFormula =>
      power_set_operator_theory_subset_cartesian_product_base_theory
        hFormula) (power_set_term_spec_derives (power_set_binary_union_term left right) (power_set_binary_union_term_admissible
        left right hLeft hRight))
/-- 三重复合项的成员关系等价于对子集条件。 -/
theorem mem_power_set_binary_union_term_iff_subset (left right element : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[cartesian_product_base_theory] (element ∈ₘ
          power_set_binary_union_term left right) ↔ₘ (element ⊆ₘ (left ∪ₘ right)) := by
  have hSpec :=
    power_set_binary_union_term_spec_derives
      left right hLeft hRight
  have hAt :=
    FirstOrder.Derives.forall_elim (term := element) hSpec
  have hUnion :
      Term.Admissible (left ∪ₘ right) SetSort.set :=
    binary_union_term_admissible
      left right hLeft hRight
  have hPower :
      Term.Admissible (power_set_binary_union_term left right)
        SetSort.set :=
    power_set_binary_union_term_admissible
      left right hLeft hRight
  have hUnionOpen :
      Term.openAt SetSort.set 0
          element (left ∪ₘ right) = (left ∪ₘ right) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element (left ∪ₘ right) hUnion.2
  have hPowerOpen :
      Term.openAt SetSort.set 0
          element (power_set_binary_union_term left right) =
        power_set_binary_union_term left right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element (power_set_binary_union_term left right)
      hPower.2
  simpa [power_set_spec,
    Formula.openAt, Term.openAt,
    hUnionOpen, hPowerOpen] using hAt
/-- 四重复合母集的成员关系等价于对三重复合项的子集条件。 -/
theorem mem_cartesian_product_bound_term_iff_subset (left right element : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[cartesian_product_base_theory] (element ∈ₘ
          cartesian_product_bound_term left right) ↔ₘ (element ⊆ₘ
          power_set_binary_union_term left right) := by
  have hSpec :=
    cartesian_product_bound_term_spec_derives
      left right hLeft hRight
  have hAt :=
    FirstOrder.Derives.forall_elim (term := element) hSpec
  have hInner :
      Term.Admissible (power_set_binary_union_term left right)
        SetSort.set :=
    power_set_binary_union_term_admissible
      left right hLeft hRight
  have hBound :
      Term.Admissible (cartesian_product_bound_term left right)
        SetSort.set :=
    cartesian_product_bound_term_admissible
      left right hLeft hRight
  have hInnerOpen :
      Term.openAt SetSort.set 0
          element (power_set_binary_union_term left right) =
        power_set_binary_union_term left right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element (power_set_binary_union_term left right)
      hInner.2
  have hBoundOpen :
      Term.openAt SetSort.set 0
          element (cartesian_product_bound_term left right) =
        cartesian_product_bound_term left right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element (cartesian_product_bound_term left right)
      hBound.2
  simpa [power_set_spec,
    Formula.openAt, Term.openAt,
    hInnerOpen, hBoundOpen] using hAt
/-! ## 分离存在性与唯一性 -/
/-- 自由参数下，笛卡尔积规格正是公共分离规格。 -/
theorem cartesian_product_spec_eq_separation_spec (left right : FreeVarId) (product : SetTerm) :
    cartesian_product_spec (x#left) (x#right) product = (cartesian_product_predicate left right).separation_spec (cartesian_product_bound_term
          (x#left) (x#right))
        product := by
  rfl
/-- 笛卡尔积规格可在任意 admissible 元素处实例化。 -/
theorem cartesian_product_spec_member_iff
    {T : SetTheory} {Γ : Context signature} (left right product element : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hProduct : Term.Admissible product SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    Γ ⊢ₘ[T]
      cartesian_product_spec left right product ⟶ₘ ((element ∈ₘ product) ↔ₘ ((element ∈ₘ
              cartesian_product_bound_term left right) ∧ₘ
            cartesian_product_member_condition
              left right element)) := by
  have hSpecAdmissible :
      Formula.Admissible (cartesian_product_spec left right product) :=
    cartesian_product_spec_admissible hLeft hRight hProduct
  nd_apply FirstOrder.Derives.impIntro
  let spec :=
    cartesian_product_spec left right product
  have hSpec :
      spec :: Γ ⊢ₘ[T] spec :=
    .assumption (by simp)
  have hAt :=
    FirstOrder.Derives.forall_elim (term := element) hSpec
  have hBound :
      Term.Admissible (cartesian_product_bound_term left right)
        SetSort.set :=
    cartesian_product_bound_term_admissible
      left right hLeft hRight
  have hProductOpen :
      Term.openAt SetSort.set 0
          element product =
        product :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element product hProduct.2
  have hBoundOpen :
      Term.openAt SetSort.set 0 element (cartesian_product_bound_term left right) =
        cartesian_product_bound_term left right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element (cartesian_product_bound_term left right)
      hBound.2
  have hLeftOpenTwo :
      Term.openAt SetSort.set 2 element left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 element left hLeft.2
  have hRightOpenTwo :
      Term.openAt SetSort.set 2 element right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 element right hRight.2
  simpa [spec, cartesian_product_spec,
    cartesian_product_member_condition,
    Formula.openAt, Formula.next_depth,
    Term.openAt, hProductOpen, hBoundOpen,
    hLeftOpenTwo, hRightOpenTwo] using hAt
/-- 闭分离公理可在任意两个 admissible 集合项处实例化。 -/
theorem cartesian_product_exists_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[cartesian_product_theory]
      cartesian_product_exists left right := by
  have hAxiom :
      ⊢ₘ[cartesian_product_theory]
        cartesian_product_separation_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hLeftInstance :=
    FirstOrder.Derives.forall_elim (term := left) hAxiom
  have hRightInstance :=
    FirstOrder.Derives.forall_elim (term := right) hLeftInstance
  have hLeftOpenTwo :
      Term.openAt SetSort.set 2 right left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 right left hLeft.2
  have hLeftOpenFour :
      Term.openAt SetSort.set 4 right left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 4 right left hLeft.2
  simpa [cartesian_product_separation_axiom,
    cartesian_product_exists,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, binary_union_term,
    power_set_term, ordered_pair_term,
    hLeftOpenTwo, hLeftOpenFour] using
      hRightInstance
/-! ## 定义扩张的实例化合同 -/
/-- 笛卡尔积函数符号定义公理可在任意 admissible 集合项处实例化。 -/
theorem cartesian_product_definition_instance_derives (left right candidate : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[cartesian_product_operator_theory]
      cartesian_product_definition_instance
        left right candidate := by
  have hAxiom :
      ⊢ₘ[cartesian_product_operator_theory]
        cartesian_product_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hLeftInstance :=
    FirstOrder.Derives.forall_elim (term := left) hAxiom
  have hRightInstance :=
    FirstOrder.Derives.forall_elim (term := right) hLeftInstance
  have hCandidateInstance :=
    FirstOrder.Derives.forall_elim (term := candidate) hRightInstance
  have hLeftOpenOneRight :
      Term.openAt SetSort.set 1 right left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 right left hLeft.2
  have hLeftOpenTwoRight :
      Term.openAt SetSort.set 2 right left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 right left hLeft.2
  have hLeftOpenFourRight :
      Term.openAt SetSort.set 4 right left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 4 right left hLeft.2
  have hLeftOpenZeroCandidate :
      Term.openAt SetSort.set 0 candidate left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 candidate left hLeft.2
  have hLeftOpenOneCandidate :
      Term.openAt SetSort.set 1 candidate left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 candidate left hLeft.2
  have hLeftOpenThreeCandidate :
      Term.openAt SetSort.set 3 candidate left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 3 candidate left hLeft.2
  have hRightOpenZeroCandidate :
      Term.openAt SetSort.set 0 candidate right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 candidate right hRight.2
  have hRightOpenOneCandidate :
      Term.openAt SetSort.set 1 candidate right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 candidate right hRight.2
  have hRightOpenThreeCandidate :
      Term.openAt SetSort.set 3 candidate right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 3 candidate right hRight.2
  simpa [cartesian_product_definition_axiom,
    cartesian_product_definition_instance,
    cartesian_product_spec,
    cartesian_product_bound_term,
    power_set_binary_union_term,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, cartesian_product_term,
    power_set_term, binary_union_term,
    ordered_pair_term,
    hLeftOpenOneRight, hLeftOpenTwoRight,
    hLeftOpenFourRight,
    hLeftOpenZeroCandidate, hLeftOpenOneCandidate,
    hLeftOpenThreeCandidate,
    hRightOpenZeroCandidate, hRightOpenOneCandidate,
    hRightOpenThreeCandidate] using hCandidateInstance
/-- 定义扩张中的笛卡尔积项满足其成员规格。 -/
theorem cartesian_product_term_spec_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[cartesian_product_operator_theory]
      cartesian_product_spec left right (left ×ₘ right) := by
  have hDefinition :=
    cartesian_product_definition_instance_derives
      left right (left ×ₘ right)
      hLeft hRight (cartesian_product_term_admissible
        left right hLeft hRight)
  exact FirstOrder.Derives.iffElimRight
    hDefinition (FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) (left ×ₘ right))
/-- 一个候选项等于规范笛卡尔积，当且仅当它满足笛卡尔积规格。 -/
theorem cartesian_product_eq_iff_spec (left right candidate : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[cartesian_product_operator_theory] (candidate ≐ₘ (left ×ₘ right)) ↔ₘ
        cartesian_product_spec left right candidate :=
  cartesian_product_definition_instance_derives
    left right candidate hLeft hRight hCandidate
/-- 同一对参数的两个笛卡尔积候选必相等。 -/
theorem cartesian_product_unique (left right first second : FreeVarId) :
    ⊢ₘ[cartesian_product_base_theory]
      cartesian_product_spec (x#left) (x#right) (x#first) ⟶ₘ
        cartesian_product_spec (x#left) (x#right) (x#second) ⟶ₘ (x#first ≐ₘ x#second) := by
  let bound :=
    cartesian_product_bound_term (x#left) (x#right)
  have hBound :
      Term.Admissible bound SetSort.set :=
    cartesian_product_bound_term_admissible (x#left) (x#right) (set_variable_admissible left) (set_variable_admissible right)
  have hUnique :
      ⊢ₘ[extensionality_theory] (cartesian_product_predicate left right).separation_spec
            bound (x#first) ⟶ₘ (cartesian_product_predicate left right).separation_spec
              bound (x#second) ⟶ₘ (x#first ≐ₘ x#second) :=
    SetPredicate.separation_unique_of_admissible (cartesian_product_predicate left right)
      bound (x#first) (x#second)
      hBound (set_variable_admissible first) (set_variable_admissible second)
  have hWeakened :
      ⊢ₘ[cartesian_product_base_theory] (cartesian_product_predicate left right).separation_spec
            bound (x#first) ⟶ₘ (cartesian_product_predicate left right).separation_spec
              bound (x#second) ⟶ₘ (x#first ≐ₘ x#second) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        extensionality_theory_subset_cartesian_product_base_theory
          hFormula)
      hUnique
  simpa [bound,
    cartesian_product_spec_eq_separation_spec] using
    hWeakened
/-! ## 全称闭包接口 -/
/-- 笛卡尔积存在性的双变量全称闭包。 -/
theorem cartesian_product_exists_forall (left right : FreeVarId) :
    ⊢ₘ[cartesian_product_theory]
      ∀ₘ[SetSort.set, left],
        ∀ₘ[SetSort.set, right],
          cartesian_product_exists (x#left) (x#right) := by
  derive_close (left, right) using
    cartesian_product_exists_derives (x#left) (x#right) (set_variable_admissible left) (set_variable_admissible right)
/-- 笛卡尔积唯一性的四变量全称闭包。 -/
theorem cartesian_product_unique_forall (left right first second : FreeVarId) :
    ⊢ₘ[cartesian_product_base_theory]
      ∀ₘ[SetSort.set, left],
        ∀ₘ[SetSort.set, right],
          ∀ₘ[SetSort.set, first],
            ∀ₘ[SetSort.set, second],
              cartesian_product_spec (x#left) (x#right) (x#first) ⟶ₘ
                cartesian_product_spec (x#left) (x#right) (x#second) ⟶ₘ (x#first ≐ₘ x#second) := by
  derive_close (left, right, first, second) using
    cartesian_product_unique
      left right first second
/-- 笛卡尔积函数符号合同的三变量全称闭包。 -/
theorem cartesian_product_eq_iff_spec_forall (left right candidate : FreeVarId) :
    ⊢ₘ[cartesian_product_operator_theory]
      ∀ₘ[SetSort.set, left],
        ∀ₘ[SetSort.set, right],
          ∀ₘ[SetSort.set, candidate], (x#candidate ≐ₘ (x#left ×ₘ x#right)) ↔ₘ
              cartesian_product_spec (x#left) (x#right) (x#candidate) := by
  derive_close (left, right, candidate) using
    cartesian_product_eq_iff_spec (x#left) (x#right) (x#candidate) (set_variable_admissible left) (set_variable_admissible right)
      (set_variable_admissible candidate)
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
