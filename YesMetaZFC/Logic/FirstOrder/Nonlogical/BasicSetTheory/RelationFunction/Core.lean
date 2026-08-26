import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Intersection
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Reordering
/-!
# 关系与函数基础
本模块从 Kuratowski 有序对开始建立关系与函数层。文献把有序对成员条件、函数符号
定义和“是有序对”谓词分别写成较长的变量化公式；这里保留完全相同的数学内容，
但把它们因子化到已经证明的无序对、单点集和公共成员接口上。
文献中的拼音缩写 `YXD` 只在注释中作为检索索引出现。Lean 标识符统一采用
`is_ordered_pair` 这一数学语义命名。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## Kuratowski 有序对 -/
/-- Kuratowski 有序对的成员条件。 -/
def ordered_pair_member_condition (member left right : SetTerm) :
    SetFormula := (member ≐ₘ {left}ₘ) ∨ₘ (member ≐ₘ {left, right}ₘ)
/-- 文献采用的经典蕴含写法。 -/
def ordered_pair_paper_condition (member left right : SetTerm) :
    SetFormula := (¬ₘ (member ≐ₘ {left}ₘ)) ⟶ₘ (member ≐ₘ {left, right}ₘ)
/-- `pair` 是由 `left`、`right` 构成的 Kuratowski 有序对。 -/
def ordered_pair_spec (left right pair : SetTerm) :
    SetFormula :=
  pair_spec {left}ₘ {left, right}ₘ pair
/-- 文献蕴含写法下的 Kuratowski 有序对规格。 -/
def ordered_pair_paper_spec (left right pair : SetTerm) :
    SetFormula :=
  pair_paper_spec {left}ₘ {left, right}ₘ pair
/-- 对固定坐标断言 Kuratowski 有序对存在。 -/
def ordered_pair_exists (left right : SetTerm) :
    SetFormula :=
  pair_exists {left}ₘ {left, right}ₘ
/-- 文献蕴含写法下的有序对存在公式。 -/
def ordered_pair_paper_exists (left right : SetTerm) :
    SetFormula :=
  pair_paper_exists {left}ₘ {left, right}ₘ
/-- 有序对函数符号的开放定义实例。 -/
def ordered_pair_definition_instance (left right candidate : SetTerm) :
    SetFormula := (candidate ≐ₘ ⟨left, right⟩ₘ) ↔ₘ
    ordered_pair_spec left right candidate
/-- 有序对函数符号的定义公理。 -/
def ordered_pair_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ordered_pair_definition_instance (x#0) (x#1) (x#2)
/-- 在单点集描述符理论上加入有序对函数符号。 -/
def ordered_pair_operator_theory : SetTheory :=
  Theory.insert
    ordered_pair_definition_axiom
    singleton_operator_theory
/-! ## 有序对谓词与投影 -/
/--
一个集合是有序对，当且仅当它等于某个规范有序对项。
这与文献中 `YXD` 的长展开等价，但把已经由定义公理固定的 Kuratowski 编码视为
原子接口，避免后续关系与函数定理重复维护同一棵公式树。
-/
def is_ordered_pair_condition (pair : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∃ₘ[SetSort.set],
      pair ≐ₘ ⟨bₛ#1, bₛ#0⟩ₘ
/-- 有序对谓词符号的开放定义实例。 -/
def is_ordered_pair_definition_instance (pair : SetTerm) :
    SetFormula :=
  is_ordered_pair_formula pair ↔ₘ
    is_ordered_pair_condition pair
/-- 有序对谓词符号的定义公理。 -/
def is_ordered_pair_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_ordered_pair_definition_instance (x#0)
/-- 当前关系与函数层的首个理论。 -/
def relation_function_theory : SetTheory :=
  Theory.insert
    is_ordered_pair_definition_axiom
    ordered_pair_operator_theory
/-- `left` 满足 `pair` 的左投影规格。 -/
def left_projection_spec (pair left : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ pair) ⟶ₘ (bₛ#1 ∈ₘ bₛ#0)) ↔ₘ (bₛ#0 ≐ₘ left)
/-- 对固定有序对断言其左投影存在。 -/
def left_projection_exists (pair : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ pair) ⟶ₘ (bₛ#1 ∈ₘ bₛ#0)) ↔ₘ (bₛ#0 ≐ₘ bₛ#1)
/--
`right` 满足 `pair` 的右投影规格。
右投影直接按有序对坐标刻画，不再重复展开 Kuratowski 编码。
-/
def right_projection_spec (pair right : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    pair ≐ₘ ⟨bₛ#0, right⟩ₘ
/--
对固定有序对断言其右投影存在。
外层 binder 是右坐标，内层 binder 是左坐标，所以等式中的索引依次为
`bₛ#0`、`bₛ#1`。这里不把外层 `bₛ#0` 传入会再开 binder 的 helper，
避免 locally nameless 捕获。
-/
def right_projection_exists (pair : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∃ₘ[SetSort.set],
      pair ≐ₘ ⟨bₛ#0, bₛ#1⟩ₘ
/-! ## 投影与反转函数符号的定义扩张 -/
/-- 左投影函数符号的开放定义实例。 -/
def left_projection_definition_instance (pair candidate : SetTerm) :
    SetFormula :=
  is_ordered_pair_formula pair ⟶ₘ (((pair)₀ₘ ≐ₘ candidate) ↔ₘ
      left_projection_spec pair candidate)
/-- 左投影函数符号的定义公理。 -/
def left_projection_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      left_projection_definition_instance (x#0) (x#1)
/-- 在有序对谓词理论上加入左投影函数符号。 -/
def left_projection_operator_theory : SetTheory :=
  Theory.insert
    left_projection_definition_axiom
    relation_function_theory
/-- 右投影函数符号的开放定义实例。 -/
def right_projection_definition_instance (pair candidate : SetTerm) :
    SetFormula :=
  is_ordered_pair_formula pair ⟶ₘ (((pair)₁ₘ ≐ₘ candidate) ↔ₘ
      right_projection_spec pair candidate)
/-- 右投影函数符号的定义公理。 -/
def right_projection_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      right_projection_definition_instance (x#0) (x#1)
/-- 在左投影描述符理论上加入右投影函数符号。 -/
def right_projection_operator_theory : SetTheory :=
  Theory.insert
    right_projection_definition_axiom
    left_projection_operator_theory
/-- `reverse` 是交换 `pair` 两个坐标得到的规范有序对。 -/
def ordered_pair_reverse_spec (pair reverse : SetTerm) :
    SetFormula :=
  reverse ≐ₘ ⟨(pair)₁ₘ, (pair)₀ₘ⟩ₘ
/-- 文献中的反转规格：结果是有序对，且两个投影交换。 -/
def ordered_pair_reverse_paper_spec (pair reverse : SetTerm) :
    SetFormula :=
  is_ordered_pair_formula reverse ∧ₘ (((reverse)₀ₘ ≐ₘ (pair)₁ₘ) ∧ₘ ((reverse)₁ₘ ≐ₘ (pair)₀ₘ))
/-- 对固定有序对断言一个满足文献规格的反转结果存在。 -/
def ordered_pair_reverse_exists (pair : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ordered_pair_reverse_paper_spec
      pair bₛ#0
/-- 有序对反转函数符号的开放定义实例。 -/
def ordered_pair_reverse_definition_instance (pair candidate : SetTerm) :
    SetFormula := (candidate ≐ₘ pair⁻¹ₘ) ↔ₘ
    ordered_pair_reverse_spec pair candidate
/-- 有序对反转函数符号的定义公理。 -/
def ordered_pair_reverse_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ordered_pair_reverse_definition_instance (x#0) (x#1)
/-- 在左右投影理论上加入有序对反转函数符号。 -/
def ordered_pair_reverse_operator_theory : SetTheory :=
  Theory.insert
    ordered_pair_reverse_definition_axiom
    right_projection_operator_theory
/-! ## 文献规格与现代规格的桥 -/
/-- 文献成员条件与现代析取条件等价。 -/
theorem ordered_pair_paper_condition_iff_member_condition (member left right : SetTerm) (hMember : Term.Admissible member SetSort.set)
    (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ
      ordered_pair_paper_condition member left right ↔ₘ
        ordered_pair_member_condition member left right := by
  simpa [ordered_pair_paper_condition,
    ordered_pair_member_condition] using
    pair_paper_condition_iff_member_condition
      member {left}ₘ {left, right}ₘ
      hMember (singleton_term_admissible left hLeft) (unordered_pair_term_admissible
        left right hLeft hRight)
/-- 文献有序对规格与现代规格等价。 -/
theorem ordered_pair_paper_spec_iff_spec (left right pair : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ
      ordered_pair_paper_spec left right pair ↔ₘ
        ordered_pair_spec left right pair := by
  simpa [ordered_pair_paper_spec,
    ordered_pair_spec] using
    pair_paper_spec_iff_spec
      {left}ₘ {left, right}ₘ pair (singleton_term_admissible left hLeft) (unordered_pair_term_admissible
        left right hLeft hRight)
      hPair
/-- 文献有序对存在公式与现代规格存在公式等价。 -/
theorem ordered_pair_paper_exists_iff_exists (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ
      ordered_pair_paper_exists left right ↔ₘ
        ordered_pair_exists left right := by
  simpa [ordered_pair_paper_exists,
    ordered_pair_exists] using
    pair_paper_exists_iff_exists
      {left}ₘ {left, right}ₘ (singleton_term_admissible left hLeft) (unordered_pair_term_admissible
        left right hLeft hRight)
/-! ## proof-carrying 良构性边界 -/
/-- 有序对项满足 proof-carrying 项边界。 -/
theorem ordered_pair_term_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible (ordered_pair_term left right) SetSort.set := by
  simpa using
    set_function_application_admissible
      .orderedPair [⟨left, by assumption⟩, ⟨right, by assumption⟩]
      (by rfl) (by rfl)
/-- 有序对项的合法性由两个坐标项的计算证书组合。 -/
@[term_check]
theorem ordered_pair_term_check
    {left right : SetTerm}
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set) :
    Term.CheckCertificate (ordered_pair_term left right) SetSort.set :=
  Term.check_admissible_complete <|
    ordered_pair_term_admissible left right
      hLeft.admissible hRight.admissible
/-- 左投影项满足 proof-carrying 项边界。 -/
theorem left_projection_term_admissible (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    Term.Admissible (left_projection_term pair) SetSort.set := by
  simpa using
    set_function_application_admissible
      .leftProjection [⟨pair, by assumption⟩]
      (by rfl) (by rfl)
/-- 左投影项的合法性由输入项证书计算。 -/
@[term_check]
theorem left_projection_term_check
    {pair : SetTerm}
    (hPair : Term.CheckCertificate pair SetSort.set) :
    Term.CheckCertificate (left_projection_term pair) SetSort.set :=
  Term.check_admissible_complete <|
    left_projection_term_admissible pair hPair.admissible
/-- 右投影项满足 proof-carrying 项边界。 -/
theorem right_projection_term_admissible (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    Term.Admissible (right_projection_term pair) SetSort.set := by
  simpa using
    set_function_application_admissible
      .rightProjection [⟨pair, by assumption⟩]
      (by rfl) (by rfl)
/-- 右投影项的合法性由输入项证书计算。 -/
@[term_check]
theorem right_projection_term_check
    {pair : SetTerm}
    (hPair : Term.CheckCertificate pair SetSort.set) :
    Term.CheckCertificate (right_projection_term pair) SetSort.set :=
  Term.check_admissible_complete <|
    right_projection_term_admissible pair hPair.admissible
/-- 有序对反转项满足 proof-carrying 项边界。 -/
theorem ordered_pair_reverse_term_admissible (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    Term.Admissible (ordered_pair_reverse_term pair) SetSort.set := by
  simpa using
    set_function_application_admissible
      .orderedPairReverse [⟨pair, by assumption⟩]
      (by rfl) (by rfl)
/-- 有序对反转项的合法性由输入项证书计算。 -/
@[term_check]
theorem ordered_pair_reverse_term_check
    {pair : SetTerm}
    (hPair : Term.CheckCertificate pair SetSort.set) :
    Term.CheckCertificate
      (ordered_pair_reverse_term pair) SetSort.set :=
  Term.check_admissible_complete <|
    ordered_pair_reverse_term_admissible pair hPair.admissible
/-- Kuratowski 有序对成员条件保持公式 admissibility。 -/
theorem ordered_pair_member_condition_admissible
    {member left right : SetTerm} (hMember : Term.Admissible member SetSort.set) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Formula.Admissible (ordered_pair_member_condition member left right) :=
  pair_member_condition_admissible
    hMember (singleton_term_admissible left hLeft) (unordered_pair_term_admissible
      left right hLeft hRight)
/-- 文献有序对成员条件保持公式 admissibility。 -/
theorem ordered_pair_paper_condition_admissible
    {member left right : SetTerm} (hMember : Term.Admissible member SetSort.set) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Formula.Admissible (ordered_pair_paper_condition member left right) :=
  pair_paper_condition_admissible
    hMember (singleton_term_admissible left hLeft) (unordered_pair_term_admissible
      left right hLeft hRight)
/-- Kuratowski 有序对规格保持公式 admissibility。 -/
theorem ordered_pair_spec_admissible
    {left right pair : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hPair : Term.Admissible pair SetSort.set) :
    Formula.Admissible (ordered_pair_spec left right pair) :=
  pair_spec_admissible (singleton_term_admissible left hLeft) (unordered_pair_term_admissible
      left right hLeft hRight)
    hPair
/-- 文献 Kuratowski 有序对规格保持公式 admissibility。 -/
theorem ordered_pair_paper_spec_admissible
    {left right pair : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hPair : Term.Admissible pair SetSort.set) :
    Formula.Admissible (ordered_pair_paper_spec left right pair) :=
  pair_paper_spec_admissible (singleton_term_admissible left hLeft) (unordered_pair_term_admissible
      left right hLeft hRight)
    hPair
/-- 有序对函数符号定义实例保持公式 admissibility。 -/
theorem ordered_pair_definition_instance_admissible
    {left right candidate : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (ordered_pair_definition_instance
        left right candidate) :=
  Formula.Admissible.iff (Formula.Admissible.equal
      hCandidate (ordered_pair_term_admissible
        left right hLeft hRight)) (ordered_pair_spec_admissible
      hLeft hRight hCandidate)
/-- “是有序对”原子在 admissible 项处仍然 admissible。 -/
theorem is_ordered_pair_formula_admissible
    {pair : SetTerm} (hPair : Term.Admissible pair SetSort.set) :
    Formula.Admissible (is_ordered_pair_formula pair) := by
  apply Formula.Admissible.rel
  simpa [signature] using (ArgsAdmissible.cons hPair
      ArgsAdmissible.nil)
/-- “是有序对”原子的合法性由对象项证书计算。 -/
@[formula_check]
theorem is_ordered_pair_formula_check
    {pair : SetTerm}
    (hPair : Term.CheckCertificate pair SetSort.set) :
    Formula.CheckCertificate (is_ordered_pair_formula pair) :=
  Formula.check_admissible_complete <|
    is_ordered_pair_formula_admissible hPair.admissible
/-- “存在两个坐标使给定项为规范有序对”的条件保持公式 admissibility。 -/
theorem is_ordered_pair_condition_admissible
    {pair : SetTerm} (hPair : Term.Admissible pair SetSort.set) :
    Formula.Admissible (is_ordered_pair_condition pair) := by
  prove_admissible
/-- “是有序对”谓词的开放定义实例保持公式 admissibility。 -/
theorem is_ordered_pair_definition_instance_admissible
    {pair : SetTerm} (hPair : Term.Admissible pair SetSort.set) :
    Formula.Admissible (is_ordered_pair_definition_instance pair) :=
  Formula.Admissible.iff (is_ordered_pair_formula_admissible hPair) (is_ordered_pair_condition_admissible hPair)
/-- 左投影规格保持公式 admissibility。 -/
theorem left_projection_spec_admissible
    {pair left : SetTerm} (hPair : Term.Admissible pair SetSort.set) (hLeft : Term.Admissible left SetSort.set) :
    Formula.Admissible (left_projection_spec pair left) := by
  prove_admissible
/-- 左投影规格的合法性由有序对项与候选项证书组合。 -/
@[formula_check]
theorem left_projection_spec_check
    {pair left : SetTerm}
    (hPair : Term.CheckCertificate pair SetSort.set)
    (hLeft : Term.CheckCertificate left SetSort.set) :
    Formula.CheckCertificate (left_projection_spec pair left) :=
  Formula.check_admissible_complete <|
    left_projection_spec_admissible
      hPair.admissible hLeft.admissible
/-- 左投影存在式保持公式 admissibility。 -/
theorem left_projection_exists_admissible
    {pair : SetTerm} (hPair : Term.Admissible pair SetSort.set) :
    Formula.Admissible (left_projection_exists pair) := by
  prove_admissible
/-- 右投影规格保持公式 admissibility。 -/
theorem right_projection_spec_admissible
    {pair right : SetTerm} (hPair : Term.Admissible pair SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Formula.Admissible (right_projection_spec pair right) := by
  prove_admissible
/-- 右投影规格的合法性由有序对项与候选项证书组合。 -/
@[formula_check]
theorem right_projection_spec_check
    {pair right : SetTerm}
    (hPair : Term.CheckCertificate pair SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set) :
    Formula.CheckCertificate (right_projection_spec pair right) :=
  Formula.check_admissible_complete <|
    right_projection_spec_admissible
      hPair.admissible hRight.admissible
/-- 右投影存在式保持公式 admissibility。 -/
theorem right_projection_exists_admissible
    {pair : SetTerm} (hPair : Term.Admissible pair SetSort.set) :
    Formula.Admissible (right_projection_exists pair) := by
  prove_admissible
/-- 左投影函数符号的开放定义实例保持公式 admissibility。 -/
theorem left_projection_definition_instance_admissible
    {pair candidate : SetTerm} (hPair : Term.Admissible pair SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (left_projection_definition_instance
        pair candidate) :=
  Formula.Admissible.imp (is_ordered_pair_formula_admissible hPair) (Formula.Admissible.iff (Formula.Admissible.equal
        (left_projection_term_admissible pair hPair)
        hCandidate) (left_projection_spec_admissible
        hPair hCandidate))
/-- 右投影函数符号的开放定义实例保持公式 admissibility。 -/
theorem right_projection_definition_instance_admissible
    {pair candidate : SetTerm} (hPair : Term.Admissible pair SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (right_projection_definition_instance
        pair candidate) :=
  Formula.Admissible.imp (is_ordered_pair_formula_admissible hPair) (Formula.Admissible.iff (Formula.Admissible.equal
        (right_projection_term_admissible pair hPair)
        hCandidate) (right_projection_spec_admissible
        hPair hCandidate))
/-- 有序对反转的规范规格保持公式 admissibility。 -/
theorem ordered_pair_reverse_spec_admissible
    {pair reverse : SetTerm} (hPair : Term.Admissible pair SetSort.set) (hReverse : Term.Admissible reverse SetSort.set) :
    Formula.Admissible (ordered_pair_reverse_spec pair reverse) :=
  Formula.Admissible.equal
    hReverse (ordered_pair_term_admissible (right_projection_term pair) (left_projection_term pair) (right_projection_term_admissible pair hPair)
      (left_projection_term_admissible pair hPair))
/-- 有序对反转规范规格的合法性由两个项证书组合。 -/
@[formula_check]
theorem ordered_pair_reverse_spec_check
    {pair reverse : SetTerm}
    (hPair : Term.CheckCertificate pair SetSort.set)
    (hReverse : Term.CheckCertificate reverse SetSort.set) :
    Formula.CheckCertificate
      (ordered_pair_reverse_spec pair reverse) :=
  Formula.check_admissible_complete <|
    ordered_pair_reverse_spec_admissible
      hPair.admissible hReverse.admissible
/-- 文献有序对反转规格保持公式 admissibility。 -/
theorem ordered_pair_reverse_paper_spec_admissible
    {pair reverse : SetTerm} (hPair : Term.Admissible pair SetSort.set) (hReverse : Term.Admissible reverse SetSort.set) :
    Formula.Admissible (ordered_pair_reverse_paper_spec pair reverse) :=
  Formula.Admissible.conj (is_ordered_pair_formula_admissible hReverse) (Formula.Admissible.conj (Formula.Admissible.equal (left_projection_term_admissible
          reverse hReverse) (right_projection_term_admissible
          pair hPair)) (Formula.Admissible.equal (right_projection_term_admissible
          reverse hReverse) (left_projection_term_admissible
          pair hPair)))
/-- 文献有序对反转规格的合法性由两个项证书组合。 -/
@[formula_check]
theorem ordered_pair_reverse_paper_spec_check
    {pair reverse : SetTerm}
    (hPair : Term.CheckCertificate pair SetSort.set)
    (hReverse : Term.CheckCertificate reverse SetSort.set) :
    Formula.CheckCertificate
      (ordered_pair_reverse_paper_spec pair reverse) :=
  Formula.check_admissible_complete <|
    ordered_pair_reverse_paper_spec_admissible
      hPair.admissible hReverse.admissible
/-- 有序对反转存在式保持公式 admissibility。 -/
theorem ordered_pair_reverse_exists_admissible
    {pair : SetTerm} (hPair : Term.Admissible pair SetSort.set) :
    Formula.Admissible (ordered_pair_reverse_exists pair) := by
  prove_admissible
/-- 有序对反转函数符号定义实例保持公式 admissibility。 -/
theorem ordered_pair_reverse_definition_instance_admissible
    {pair candidate : SetTerm} (hPair : Term.Admissible pair SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (ordered_pair_reverse_definition_instance
        pair candidate) :=
  Formula.Admissible.iff (Formula.Admissible.equal
      hCandidate (ordered_pair_reverse_term_admissible
        pair hPair)) (ordered_pair_reverse_spec_admissible
      hPair hCandidate)
/-- 有序对函数符号定义公理满足公共良构性边界。 -/
theorem ordered_pair_definition_axiom_admissible :
    Formula.Admissible ordered_pair_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 有序对函数符号扩张后的理论仍然 admissible。 -/
theorem ordered_pair_operator_theory_admissible :
    Theory.Admissible ordered_pair_operator_theory :=
  Theory.admissible_insert
    ordered_pair_definition_axiom_admissible
    singleton_operator_theory_admissible
/-- 有序对谓词定义公理满足公共良构性边界。 -/
theorem is_ordered_pair_definition_axiom_admissible :
    Formula.Admissible is_ordered_pair_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 关系与函数基础理论仍然 admissible。 -/
theorem relation_function_theory_admissible :
    Theory.Admissible relation_function_theory :=
  Theory.admissible_insert
    is_ordered_pair_definition_axiom_admissible
    ordered_pair_operator_theory_admissible
/-- 左投影函数符号定义公理满足公共良构性边界。 -/
theorem left_projection_definition_axiom_admissible :
    Formula.Admissible left_projection_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 左投影函数符号扩张后的理论仍然 admissible。 -/
theorem left_projection_operator_theory_admissible :
    Theory.Admissible left_projection_operator_theory :=
  Theory.admissible_insert
    left_projection_definition_axiom_admissible
    relation_function_theory_admissible
/-- 右投影函数符号定义公理满足公共良构性边界。 -/
theorem right_projection_definition_axiom_admissible :
    Formula.Admissible right_projection_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 右投影函数符号扩张后的理论仍然 admissible。 -/
theorem right_projection_operator_theory_admissible :
    Theory.Admissible right_projection_operator_theory :=
  Theory.admissible_insert
    right_projection_definition_axiom_admissible
    left_projection_operator_theory_admissible
/-- 有序对反转函数符号定义公理满足公共良构性边界。 -/
theorem ordered_pair_reverse_definition_axiom_admissible :
    Formula.Admissible ordered_pair_reverse_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 有序对反转函数符号扩张后的理论仍然 admissible。 -/
theorem ordered_pair_reverse_operator_theory_admissible :
    Theory.Admissible ordered_pair_reverse_operator_theory :=
  Theory.admissible_insert
    ordered_pair_reverse_definition_axiom_admissible
    right_projection_operator_theory_admissible
/-- 有序对函数符号理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem ordered_pair_operator_theory_sentence
    {formula : SetFormula} (hFormula : ordered_pair_operator_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact ordered_pair_operator_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · exact (singleton_operator_theory_sentence hFormula).2
/-- 关系与函数基础理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem relation_function_theory_sentence
    {formula : SetFormula} (hFormula : relation_function_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact relation_function_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · exact (ordered_pair_operator_theory_sentence
          hFormula).2
/-- 左投影函数符号理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem left_projection_operator_theory_sentence
    {formula : SetFormula} (hFormula : left_projection_operator_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact left_projection_operator_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · exact (relation_function_theory_sentence hFormula).2
/-- 右投影函数符号理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem right_projection_operator_theory_sentence
    {formula : SetFormula} (hFormula : right_projection_operator_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact right_projection_operator_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · exact (left_projection_operator_theory_sentence hFormula).2
/-- 有序对反转函数符号理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem ordered_pair_reverse_operator_theory_sentence
    {formula : SetFormula} (hFormula : ordered_pair_reverse_operator_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact ordered_pair_reverse_operator_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · exact (right_projection_operator_theory_sentence hFormula).2
/-! ## 理论嵌入 -/
/-- 单点集理论嵌入有序对函数符号理论。 -/
theorem singleton_operator_theory_subset_ordered_pair_operator_theory
    {formula : SetFormula} (hFormula : singleton_operator_theory formula) :
    ordered_pair_operator_theory formula :=
  Or.inr hFormula
/-- 有序对函数符号理论嵌入关系与函数基础理论。 -/
theorem ordered_pair_operator_theory_subset_relation_function_theory
    {formula : SetFormula} (hFormula : ordered_pair_operator_theory formula) :
    relation_function_theory formula :=
  Or.inr hFormula
/-- 单点集理论嵌入关系与函数基础理论。 -/
theorem singleton_operator_theory_subset_relation_function_theory
    {formula : SetFormula} (hFormula : singleton_operator_theory formula) :
    relation_function_theory formula :=
  ordered_pair_operator_theory_subset_relation_function_theory (singleton_operator_theory_subset_ordered_pair_operator_theory
      hFormula)
/-- 外延理论嵌入有序对函数符号理论。 -/
theorem extensionality_theory_subset_ordered_pair_operator_theory
    {formula : SetFormula} (hFormula : extensionality_theory formula) :
    ordered_pair_operator_theory formula :=
  Or.inr (Or.inr (Or.inr (Or.inr hFormula)))
/-- 关系与函数基座嵌入左投影函数符号理论。 -/
theorem relation_function_theory_subset_left_projection_operator_theory
    {formula : SetFormula} (hFormula : relation_function_theory formula) :
    left_projection_operator_theory formula :=
  Or.inr hFormula
/-- 有序对函数符号理论嵌入左投影函数符号理论。 -/
theorem ordered_pair_operator_theory_subset_left_projection_operator_theory
    {formula : SetFormula} (hFormula : ordered_pair_operator_theory formula) :
    left_projection_operator_theory formula :=
  relation_function_theory_subset_left_projection_operator_theory (ordered_pair_operator_theory_subset_relation_function_theory
      hFormula)
/-- 左投影函数符号理论嵌入右投影函数符号理论。 -/
theorem left_projection_operator_theory_subset_right_projection_operator_theory
    {formula : SetFormula} (hFormula : left_projection_operator_theory formula) :
    right_projection_operator_theory formula :=
  Or.inr hFormula
/-- 右投影函数符号理论嵌入有序对反转函数符号理论。 -/
theorem right_projection_operator_theory_subset_ordered_pair_reverse_operator_theory
    {formula : SetFormula} (hFormula : right_projection_operator_theory formula) :
    ordered_pair_reverse_operator_theory formula :=
  Or.inr hFormula
/-- 关系与函数基座嵌入右投影函数符号理论。 -/
theorem relation_function_theory_subset_right_projection_operator_theory
    {formula : SetFormula} (hFormula : relation_function_theory formula) :
    right_projection_operator_theory formula :=
  left_projection_operator_theory_subset_right_projection_operator_theory (relation_function_theory_subset_left_projection_operator_theory
      hFormula)
/-- 有序对函数符号理论嵌入右投影函数符号理论。 -/
theorem ordered_pair_operator_theory_subset_right_projection_operator_theory
    {formula : SetFormula} (hFormula : ordered_pair_operator_theory formula) :
    right_projection_operator_theory formula :=
  relation_function_theory_subset_right_projection_operator_theory (ordered_pair_operator_theory_subset_relation_function_theory
      hFormula)
/-- 关系与函数基座嵌入有序对反转函数符号理论。 -/
theorem relation_function_theory_subset_ordered_pair_reverse_operator_theory
    {formula : SetFormula} (hFormula : relation_function_theory formula) :
    ordered_pair_reverse_operator_theory formula :=
  right_projection_operator_theory_subset_ordered_pair_reverse_operator_theory (relation_function_theory_subset_right_projection_operator_theory
      hFormula)
/-! ## 有序对存在性与唯一性 -/
/-- 任意两个 admissible 集合项都有 Kuratowski 有序对。 -/
theorem ordered_pair_exists_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[pairing_theory]
      ordered_pair_exists left right := by
  simpa [ordered_pair_exists] using
    pair_exists_derives
      {left}ₘ {left, right}ₘ (singleton_term_admissible left hLeft) (unordered_pair_term_admissible
        left right hLeft hRight)
/-- 文献蕴含规格下，任意两个 admissible 集合项都有 Kuratowski 有序对。 -/
theorem ordered_pair_paper_exists_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[pairing_theory]
      ordered_pair_paper_exists left right := by
  have hBridge :
      ⊢ₘ[pairing_theory]
        ordered_pair_paper_exists left right ↔ₘ
          ordered_pair_exists left right :=
    FirstOrder.Derives.of_empty (ordered_pair_paper_exists_iff_exists
        left right hLeft hRight)
  exact FirstOrder.Derives.iffElimLeft
    hBridge (ordered_pair_exists_derives
      left right hLeft hRight)
/-- 同一坐标规格的两个 Kuratowski 有序对候选必相等。 -/
theorem ordered_pair_unique (first second left right : SetTerm) (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set)
    (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[extensionality_theory]
      ordered_pair_spec first second left ⟶ₘ
        ordered_pair_spec first second right ⟶ₘ (left ≐ₘ right) := by
  simpa [ordered_pair_spec] using
    pair_unique
      {first}ₘ {first, second}ₘ left right (singleton_term_admissible first hFirst) (unordered_pair_term_admissible
        first second hFirst hSecond)
      hLeft hRight
/-- 文献蕴含规格下，同一坐标的两个有序对候选必相等。 -/
theorem ordered_pair_paper_unique (first second left right : SetTerm) (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[extensionality_theory]
      ordered_pair_paper_spec first second left ⟶ₘ
        ordered_pair_paper_spec first second right ⟶ₘ (left ≐ₘ right) := by
  have hLeftPaperAdmissible :
      Formula.Admissible (ordered_pair_paper_spec
          first second left) :=
    ordered_pair_paper_spec_admissible
      hFirst hSecond hLeft
  have hRightPaperAdmissible :
      Formula.Admissible (ordered_pair_paper_spec
          first second right) :=
    ordered_pair_paper_spec_admissible
      hFirst hSecond hRight
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [ordered_pair_paper_spec first second right,
      ordered_pair_paper_spec first second left]
  have hLeftBridge :
      Γ ⊢ₘ[extensionality_theory]
        ordered_pair_paper_spec first second left ↔ₘ
          ordered_pair_spec first second left :=
    FirstOrder.Derives.of_empty (ordered_pair_paper_spec_iff_spec
        first second left
        hFirst hSecond hLeft)
  have hRightBridge :
      Γ ⊢ₘ[extensionality_theory]
        ordered_pair_paper_spec first second right ↔ₘ
          ordered_pair_spec first second right :=
    FirstOrder.Derives.of_empty (ordered_pair_paper_spec_iff_spec
        first second right
        hFirst hSecond hRight)
  have hLeftModern :
      Γ ⊢ₘ[extensionality_theory]
        ordered_pair_spec first second left :=
    FirstOrder.Derives.iffElimRight
      hLeftBridge (.assumption (by simp [Γ])
        )
  have hRightModern :
      Γ ⊢ₘ[extensionality_theory]
        ordered_pair_spec first second right :=
    FirstOrder.Derives.iffElimRight
      hRightBridge (.assumption (by simp [Γ])
        )
  have hUnique :
      Γ ⊢ₘ[extensionality_theory]
        ordered_pair_spec first second left ⟶ₘ
          ordered_pair_spec first second right ⟶ₘ (left ≐ₘ right) :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.context_weaken_cons (ordered_pair_unique
          first second left right
          hFirst hSecond hLeft hRight)
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
      hUnique hLeftModern)
    hRightModern
/-! ## 定义扩张的实例化合同 -/
/-- 有序对函数符号定义公理可在任意 admissible 集合项处实例化。 -/
theorem ordered_pair_definition_instance_derives (left right candidate : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[ordered_pair_operator_theory]
      ordered_pair_definition_instance
        left right candidate := by
  have hAxiom :
      ⊢ₘ[ordered_pair_operator_theory]
        ordered_pair_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hLeftInstance :=
    FirstOrder.Derives.forall_elim
      (term := left) hAxiom
  have hRightInstance :=
    FirstOrder.Derives.forall_elim
      (term := right) hLeftInstance
  have hCandidateInstance :=
    FirstOrder.Derives.forall_elim
      (term := candidate) hRightInstance
  have hLeftOpenOneRight :
      Term.openAt SetSort.set 1 right left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 right left hLeft.2
  have hLeftOpenTwoRight :
      Term.openAt SetSort.set 2 right left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 right left hLeft.2
  have hLeftOpenZeroCandidate :
      Term.openAt SetSort.set 0 candidate left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 candidate left hLeft.2
  have hLeftOpenOneCandidate :
      Term.openAt SetSort.set 1 candidate left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 candidate left hLeft.2
  have hRightOpenZeroCandidate :
      Term.openAt SetSort.set 0 candidate right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 candidate right hRight.2
  have hRightOpenOneCandidate :
      Term.openAt SetSort.set 1 candidate right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 candidate right hRight.2
  simpa [ordered_pair_definition_axiom,
    ordered_pair_definition_instance,
    ordered_pair_spec, pair_spec,
    pair_member_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, ordered_pair_term,
    singleton_term, unordered_pair_term,
    hLeftOpenOneRight, hLeftOpenTwoRight,
    hLeftOpenZeroCandidate, hLeftOpenOneCandidate,
    hRightOpenZeroCandidate,
    hRightOpenOneCandidate] using hCandidateInstance
/-- 定义扩张中的有序对项满足 Kuratowski 规格。 -/
theorem ordered_pair_term_spec_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[ordered_pair_operator_theory]
      ordered_pair_spec left right
        ⟨left, right⟩ₘ := by
  have hDefinition :=
    ordered_pair_definition_instance_derives
      left right ⟨left, right⟩ₘ
      hLeft hRight (ordered_pair_term_admissible
        left right hLeft hRight)
  exact FirstOrder.Derives.iffElimRight
    hDefinition (FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) ⟨left, right⟩ₘ)
/-- 一个候选项等于规范有序对，当且仅当它满足对应规格。 -/
theorem ordered_pair_eq_iff_spec (left right candidate : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[ordered_pair_operator_theory] (candidate ≐ₘ ⟨left, right⟩ₘ) ↔ₘ
        ordered_pair_spec left right candidate :=
  ordered_pair_definition_instance_derives
    left right candidate hLeft hRight hCandidate
/-- 有序对谓词定义公理可在任意 admissible 集合项处实例化。 -/
theorem is_ordered_pair_definition_instance_derives (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ[relation_function_theory]
      is_ordered_pair_definition_instance pair := by
  have hAxiom :
      ⊢ₘ[relation_function_theory]
        is_ordered_pair_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hInstance :=
    FirstOrder.Derives.forall_elim
      (term := pair) hAxiom
  simpa [is_ordered_pair_definition_axiom,
    is_ordered_pair_definition_instance,
    is_ordered_pair_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, ordered_pair_term] using hInstance
/-! ## 左投影的规范规格 -/
/-- 左投影规格在任意 admissible 成员项处的点态实例。 -/
theorem left_projection_spec_membership_iff
    {T : SetTheory} {Γ : Context signature} (pair left member : SetTerm) (hPair : Term.Admissible pair SetSort.set) (hLeft : Term.Admissible left SetSort.set)
    (hMember : Term.Admissible member SetSort.set) (hSpec : Γ ⊢ₘ[T] left_projection_spec pair left) :
    Γ ⊢ₘ[T]
      pair_common_member_condition pair member ↔ₘ (member ≐ₘ left) := by
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := member) hSpec
  have hPairOpenOne :
      Term.openAt SetSort.set 1 member pair = pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 member pair hPair.2
  have hLeftOpenZero :
      Term.openAt SetSort.set 0 member left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 member left hLeft.2
  simpa [left_projection_spec,
    pair_common_member_condition,
    Formula.openAt, Formula.next_depth,
    Term.openAt, hPairOpenOne,
    hLeftOpenZero] using hAt
/-- 同一个集合的两个左投影候选必相等。 -/
theorem left_projection_unique (pair left right : SetTerm) (hPair : Term.Admissible pair SetSort.set) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ
      left_projection_spec pair left ⟶ₘ
        left_projection_spec pair right ⟶ₘ (left ≐ₘ right) := by
  have hLeftSpecAdmissible :
      Formula.Admissible (left_projection_spec pair left) :=
    left_projection_spec_admissible
      hPair hLeft
  have hRightSpecAdmissible :
      Formula.Admissible (left_projection_spec pair right) :=
    left_projection_spec_admissible
      hPair hRight
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [left_projection_spec pair right,
      left_projection_spec pair left]
  have hLeftSpec :
      Γ ⊢ₘ left_projection_spec pair left :=
    .assumption (by simp [Γ])
  have hRightSpec :
      Γ ⊢ₘ left_projection_spec pair right :=
    .assumption (by simp [Γ])
  have hLeftAtLeft :=
    left_projection_spec_membership_iff
      pair left left hPair hLeft hLeft hLeftSpec
  have hRightAtLeft :=
    left_projection_spec_membership_iff
      pair right left hPair hRight hLeft hRightSpec
  have hCommon :
      Γ ⊢ₘ pair_common_member_condition pair left :=
    FirstOrder.Derives.iffElimLeft
      hLeftAtLeft (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) left)
  exact FirstOrder.Derives.iffElimRight
    hRightAtLeft hCommon
/-- 规范 Kuratowski 有序对的左投影是其第一坐标。 -/
theorem ordered_pair_term_left_projection_spec (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[ordered_pair_operator_theory]
      left_projection_spec
        ⟨left, right⟩ₘ left := by
  let singleton := singleton_term left
  let pair := unordered_pair_term left right
  let ordered := ordered_pair_term left right
  let projection_body : SetFormula := (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ ordered) ⟶ₘ (bₛ#1 ∈ₘ bₛ#0)) ↔ₘ (bₛ#0 ≐ₘ left)
  let member :=
    FreshVariable.fresh_id SetSort.set
      [projection_body]
  let common_at :=
    pair_common_member_condition
      ordered (x#member)
  let point : SetFormula :=
    common_at ↔ₘ (x#member ≐ₘ left)
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
  have hOuterSpec :
      ⊢ₘ[ordered_pair_operator_theory]
        pair_spec singleton pair ordered := by
    simpa [singleton, pair, ordered,
      ordered_pair_spec] using
      ordered_pair_term_spec_derives
        left right hLeft hRight
  have hSingletonSpec :
      ⊢ₘ[ordered_pair_operator_theory]
        singleton_spec left singleton :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        singleton_operator_theory_subset_ordered_pair_operator_theory
          hFormula) (by
        simpa [singleton] using
          singleton_term_spec_derives
            left hLeft)
  have hPairSpec :
      ⊢ₘ[ordered_pair_operator_theory]
        pair_spec left right pair :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        singleton_operator_theory_subset_ordered_pair_operator_theory (Or.inr hFormula)) (by
        simpa [pair] using
          unordered_pair_term_spec_derives
            left right hLeft hRight)
  have hCommonImp :
      ⊢ₘ[ordered_pair_operator_theory]
        pair_spec singleton pair ordered ⟶ₘ (common_at ↔ₘ ((x#member ∈ₘ singleton) ∧ₘ (x#member ∈ₘ pair))) :=
    FirstOrder.Derives.of_empty (by
        simpa [common_at] using
          pair_common_member_condition_iff
            singleton pair ordered (x#member)
            hSingleton hPair hOrdered (set_variable_admissible member))
  have hCommon :
      ⊢ₘ[ordered_pair_operator_theory]
        common_at ↔ₘ ((x#member ∈ₘ singleton) ∧ₘ (x#member ∈ₘ pair)) :=
    FirstOrder.Derives.impElim
      hCommonImp hOuterSpec
  have hSingletonAt :=
    singleton_spec_membership_iff
      left singleton (x#member)
      hLeft hSingleton (set_variable_admissible member)
      hSingletonSpec
  have hPairAt :=
    pair_spec_membership_iff
      left right pair (x#member)
      hLeft hRight hPair (set_variable_admissible member)
      hPairSpec
  have hPoint :
      ⊢ₘ[ordered_pair_operator_theory] point := by
    dsimp [point]
    have hMemberAdmissible :
        Term.Admissible (x#member) SetSort.set :=
      set_variable_admissible member
    have hCommonAdmissible :
        Formula.Admissible common_at :=
      pair_common_member_condition_admissible
        hOrdered hMemberAdmissible
    have hMemberInSingletonAdmissible :
        Formula.Admissible (x#member ∈ₘ singleton) :=
      membership_formula_admissible
        hMemberAdmissible hSingleton
    have hMemberInPairAdmissible :
        Formula.Admissible (x#member ∈ₘ pair) :=
      membership_formula_admissible
        hMemberAdmissible hPair
    have hMemberEqLeftAdmissible :
        Formula.Admissible (x#member ≐ₘ left) :=
      Formula.Admissible.equal
        hMemberAdmissible hLeft
    have hMemberEqRightAdmissible :
        Formula.Admissible (x#member ≐ₘ right) :=
      Formula.Admissible.equal
        hMemberAdmissible hRight
    apply FirstOrder.Derives.iffIntro
    · have hCommon' :=
        FirstOrder.Derives.context_weaken_cons (assumption := common_at)
          hCommon
      have hConjunction :=
        FirstOrder.Derives.iffElimRight
          hCommon' (.assumption (by simp)
            )
      have hSingletonMembership :=
        FirstOrder.Derives.conjElimLeft
          hConjunction
      exact FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons (assumption := common_at)
          hSingletonAt)
        hSingletonMembership
    · have hEquality :
          [x#member ≐ₘ left]
            ⊢ₘ[ordered_pair_operator_theory]
              x#member ≐ₘ left :=
        .assumption (by simp)
      have hSingletonMembership :=
        FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken_cons (assumption := x#member ≐ₘ left)
            hSingletonAt)
          hEquality
      have hPairMembership :=
        FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken_cons (assumption := x#member ≐ₘ left)
          hPairAt) (FirstOrder.Derives.disjIntroLeft
            hEquality)
      exact FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken_cons (assumption := x#member ≐ₘ left)
          hCommon) (FirstOrder.Derives.conjIntro
          hSingletonMembership hPairMembership)
  have hMemberFreshBody : (SetSort.set, member) freshForₘ
        projection_body := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hOrderedOpenOne :
      Term.openAt SetSort.set 1 (x#member) ordered =
        ordered :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 (x#member) ordered hOrdered.2
  have hLeftOpenZero :
      Term.openAt SetSort.set 0 (x#member) left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member) left hLeft.2
  have hPointOpened :
      ⊢ₘ[ordered_pair_operator_theory]
        Formula.openAt SetSort.set 0 (x#member) projection_body := by
    simpa [point, common_at, projection_body,
      pair_common_member_condition,
      Formula.openAt, Formula.next_depth,
      Term.openAt, hOrderedOpenOne,
      hLeftOpenZero] using hPoint
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := ordered_pair_operator_theory) (Γ := []) (sort := SetSort.set) (eigen := member) (body :=
        Formula.openAt SetSort.set 0 (x#member) projection_body) (by
        intro formula hFormula
        have hSentence :=
          ordered_pair_operator_theory_sentence
            hFormula
        rw [hSentence.2]
        simp) (by
        intro formula hFormula
        cases hFormula)
      hPointOpened
  simpa [left_projection_spec, ordered,
    projection_body,
    Formula.closeFreeAt_openAt
      SetSort.set member 0 projection_body
      hMemberFreshBody] using hGeneralized
/-- 左投影规格可沿其来源集合的等式运输。 -/
theorem left_projection_spec_transport_pair_of_equality
    {T : SetTheory} {Γ : Context signature} (pair_left pair_right left : SetTerm) (hPairLeft : Term.Admissible pair_left SetSort.set)
    (hPairRight : Term.Admissible pair_right SetSort.set) (hLeft : Term.Admissible left SetSort.set) (hPairEquality :
      Γ ⊢ₘ[T] pair_left ≐ₘ pair_right) (hLeftSpec :
      Γ ⊢ₘ[T] left_projection_spec pair_left left)
    : Γ ⊢ₘ[T] left_projection_spec pair_right left := by
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [left ≐ₘ left]
  let body : SetFormula :=
    left_projection_spec (x#parameter) left
  have hLeftFresh : (SetSort.set, parameter) ∉
        Term.freeSupport left := by
    dsimp [parameter]
    exact FreshVariable.fresh_term_not_mem_m
      SetSort.set left
  have hLeftFixedPairLeft :
      Term.substituteFree SetSort.set
          parameter pair_left left =
        left :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter pair_left left
      hLeftFresh
  have hLeftFixedPairRight :
      Term.substituteFree SetSort.set
          parameter pair_right left =
        left :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter pair_right left
      hLeftFresh
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := parameter) (left := pair_left) (right := pair_right)
      (body := body)
      hPairEquality
  have hCongruenceNormalized :
      Γ ⊢ₘ[T]
        left_projection_spec pair_left left ↔ₘ
          left_projection_spec pair_right left := by
    simpa [body, left_projection_spec,
      Formula.substituteFree, Formula.next_depth,
      Term.substituteFree, hLeftFixedPairLeft,
      hLeftFixedPairRight, set_variable] using
      hCongruence
  exact FirstOrder.Derives.iffElimRight
    hCongruenceNormalized hLeftSpec
/-- 相等集合上的两个左投影候选必相等。 -/
theorem left_projection_unique_of_pair_equality
    {T : SetTheory} {Γ : Context signature} (pair_left pair_right left right : SetTerm) (hPairLeft : Term.Admissible pair_left SetSort.set)
    (hPairRight : Term.Admissible pair_right SetSort.set) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hPairEquality :
      Γ ⊢ₘ[T] pair_left ≐ₘ pair_right) (hLeftSpec :
      Γ ⊢ₘ[T] left_projection_spec pair_left left) (hRightSpec :
      Γ ⊢ₘ[T] left_projection_spec pair_right right) :
    Γ ⊢ₘ[T] left ≐ₘ right := by
  have hLeftSpecRight :=
    left_projection_spec_transport_pair_of_equality
      pair_left pair_right left
      hPairLeft hPairRight hLeft
      hPairEquality hLeftSpec
  have hUnique :
      Γ ⊢ₘ[T]
        left_projection_spec pair_right left ⟶ₘ
          left_projection_spec pair_right right ⟶ₘ (left ≐ₘ right) :=
    FirstOrder.Derives.of_empty (left_projection_unique
        pair_right left right
        hPairRight hLeft hRight)
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
      hUnique hLeftSpecRight)
    hRightSpec
/-- 一个左投影规格候选立即见证左投影存在。 -/
theorem left_projection_spec_implies_exists (pair candidate : SetTerm) (hPair : Term.Admissible pair SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ
      left_projection_spec pair candidate ⟶ₘ
        left_projection_exists pair := by
  nd_apply FirstOrder.Derives.impIntro
  unfold left_projection_exists
  nd_apply FirstOrder.Derives.exists_intro (term := candidate)
  have hPairOpenTwo :
      Term.openAt SetSort.set 2 candidate pair = pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 candidate pair hPair.2
  simpa [left_projection_spec,
    Formula.openAt, Formula.next_depth,
    Term.openAt, hPairOpenTwo] using (show
      [left_projection_spec pair candidate] ⊢ₘ
        left_projection_spec pair candidate from
      .assumption (by simp))
/-- 规范有序对项具有左投影。 -/
theorem ordered_pair_term_left_projection_exists (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[ordered_pair_operator_theory]
      left_projection_exists
        ⟨left, right⟩ₘ := by
  have hPair :=
    ordered_pair_term_admissible
      left right hLeft hRight
  have hSpec :=
    ordered_pair_term_left_projection_spec
      left right hLeft hRight
  have hExistsImp :
      ⊢ₘ[ordered_pair_operator_theory]
        left_projection_spec
            ⟨left, right⟩ₘ left ⟶ₘ
          left_projection_exists
            ⟨left, right⟩ₘ :=
    FirstOrder.Derives.of_empty (left_projection_spec_implies_exists
        ⟨left, right⟩ₘ left hPair hLeft)
  exact FirstOrder.Derives.impElim
    hExistsImp hSpec
/-- 等于某个规范有序对的集合具有左投影。 -/
theorem ordered_pair_equality_implies_left_projection_exists (pair left right : SetTerm) (hPair : Term.Admissible pair SetSort.set)
    (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[ordered_pair_operator_theory] (pair ≐ₘ ⟨left, right⟩ₘ) ⟶ₘ
        left_projection_exists pair := by
  let ordered := ordered_pair_term left right
  have hOrdered :
      Term.Admissible ordered SetSort.set :=
    ordered_pair_term_admissible
      left right hLeft hRight
  have hEqualityAdmissible :
      Formula.Admissible (pair ≐ₘ ordered) :=
    Formula.Admissible.equal
      hPair hOrdered
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [pair ≐ₘ ordered]
  have hEquality :
      Γ ⊢ₘ[ordered_pair_operator_theory]
        pair ≐ₘ ordered :=
    .assumption (by simp [Γ])
  have hSymmetry :
      Γ ⊢ₘ[ordered_pair_operator_theory]
        ordered ≐ₘ pair :=
    Metatheory.Derives.equality_symm
      hEquality
  have hCanonical :
      Γ ⊢ₘ[ordered_pair_operator_theory]
        left_projection_spec ordered left :=
    FirstOrder.Derives.context_weaken_cons (by
        simpa [ordered] using
          ordered_pair_term_left_projection_spec
            left right hLeft hRight)
  have hTransported :
      Γ ⊢ₘ[ordered_pair_operator_theory]
        left_projection_spec pair left :=
    left_projection_spec_transport_pair_of_equality
      ordered pair left
      hOrdered hPair hLeft
      hSymmetry hCanonical
  have hExistsImp :
      Γ ⊢ₘ[ordered_pair_operator_theory]
        left_projection_spec pair left ⟶ₘ
          left_projection_exists pair :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.of_empty (left_projection_spec_implies_exists
          pair left hPair hLeft)
  exact FirstOrder.Derives.impElim
    hExistsImp hTransported
/-! ## 有序对规格的坐标运输 -/
/-- 有序对规格可沿第一坐标的等式运输。 -/
theorem ordered_pair_spec_transport_left_of_equality
    {T : SetTheory} {Γ : Context signature} (source target right pair : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hTarget : Term.Admissible target SetSort.set) (hRight : Term.Admissible right SetSort.set) (hPair : Term.Admissible pair SetSort.set)
    (hEquality : Γ ⊢ₘ[T] source ≐ₘ target) (hSpec : Γ ⊢ₘ[T] ordered_pair_spec source right pair) :
    Γ ⊢ₘ[T] ordered_pair_spec target right pair := by
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [right ≐ₘ right, pair ≐ₘ pair]
  let body : SetFormula :=
    ordered_pair_spec (x#parameter) right pair
  have hRightFresh : (SetSort.set, parameter) ∉
        Term.freeSupport right := by
    dsimp [parameter]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
          [right ≐ₘ right, pair ≐ₘ pair]) (formula := right ≐ₘ right) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hPairFresh : (SetSort.set, parameter) ∉
        Term.freeSupport pair := by
    dsimp [parameter]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
          [right ≐ₘ right, pair ≐ₘ pair]) (formula := pair ≐ₘ pair) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hRightFixedSource :
      Term.substituteFree SetSort.set
          parameter source right =
        right :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter source right
      hRightFresh
  have hRightFixedTarget :
      Term.substituteFree SetSort.set
          parameter target right =
        right :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter target right
      hRightFresh
  have hPairFixedSource :
      Term.substituteFree SetSort.set
          parameter source pair =
        pair :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter source pair
      hPairFresh
  have hPairFixedTarget :
      Term.substituteFree SetSort.set
          parameter target pair =
        pair :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter target pair
      hPairFresh
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := parameter) (left := source) (right := target) (body := body)
      hEquality
  have hNormalized :
      Γ ⊢ₘ[T]
        ordered_pair_spec source right pair ↔ₘ
          ordered_pair_spec target right pair := by
    simpa [body, ordered_pair_spec, pair_spec,
      pair_member_condition,
      Formula.substituteFree, Formula.next_depth,
      Term.substituteFree, hRightFixedSource,
      hRightFixedTarget, hPairFixedSource,
      hPairFixedTarget, set_variable,
      singleton_term, unordered_pair_term] using
      hCongruence
  exact FirstOrder.Derives.iffElimRight
    hNormalized hSpec
/-- 有序对规格可沿第二坐标的等式运输。 -/
theorem ordered_pair_spec_transport_right_of_equality
    {T : SetTheory} {Γ : Context signature} (left source target pair : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hSource : Term.Admissible source SetSort.set) (hTarget : Term.Admissible target SetSort.set) (hPair : Term.Admissible pair SetSort.set)
    (hEquality : Γ ⊢ₘ[T] source ≐ₘ target) (hSpec : Γ ⊢ₘ[T] ordered_pair_spec left source pair) :
    Γ ⊢ₘ[T] ordered_pair_spec left target pair := by
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [left ≐ₘ left, pair ≐ₘ pair]
  let body : SetFormula :=
    ordered_pair_spec left (x#parameter) pair
  have hLeftFresh : (SetSort.set, parameter) ∉
        Term.freeSupport left := by
    dsimp [parameter]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
          [left ≐ₘ left, pair ≐ₘ pair]) (formula := left ≐ₘ left) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hPairFresh : (SetSort.set, parameter) ∉
        Term.freeSupport pair := by
    dsimp [parameter]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
          [left ≐ₘ left, pair ≐ₘ pair]) (formula := pair ≐ₘ pair) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hLeftFixedSource :
      Term.substituteFree SetSort.set
          parameter source left =
        left :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter source left
      hLeftFresh
  have hLeftFixedTarget :
      Term.substituteFree SetSort.set
          parameter target left =
        left :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter target left
      hLeftFresh
  have hPairFixedSource :
      Term.substituteFree SetSort.set
          parameter source pair =
        pair :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter source pair
      hPairFresh
  have hPairFixedTarget :
      Term.substituteFree SetSort.set
          parameter target pair =
        pair :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter target pair
      hPairFresh
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := parameter) (left := source) (right := target) (body := body)
      hEquality
  have hNormalized :
      Γ ⊢ₘ[T]
        ordered_pair_spec left source pair ↔ₘ
          ordered_pair_spec left target pair := by
    simpa [body, ordered_pair_spec, pair_spec,
      pair_member_condition,
      Formula.substituteFree, Formula.next_depth,
      Term.substituteFree, hLeftFixedSource,
      hLeftFixedTarget, hPairFixedSource,
      hPairFixedTarget, set_variable,
      singleton_term, unordered_pair_term] using
      hCongruence
  exact FirstOrder.Derives.iffElimRight
    hNormalized hSpec
/-- 两个坐标的等式可依次运输整个有序对规格。 -/
theorem ordered_pair_spec_transport_coordinates_of_equalities
    {T : SetTheory} {Γ : Context signature} (left_source left_target right_source right_target pair : SetTerm)
    (hLeftSource : Term.Admissible left_source SetSort.set) (hLeftTarget : Term.Admissible left_target SetSort.set)
    (hRightSource : Term.Admissible right_source SetSort.set) (hRightTarget : Term.Admissible right_target SetSort.set)
    (hPair : Term.Admissible pair SetSort.set) (hLeftEquality :
      Γ ⊢ₘ[T] left_source ≐ₘ left_target) (hRightEquality :
      Γ ⊢ₘ[T] right_source ≐ₘ right_target) (hSpec :
      Γ ⊢ₘ[T]
        ordered_pair_spec left_source right_source pair) :
    Γ ⊢ₘ[T]
      ordered_pair_spec left_target right_target pair := by
  have hLeftTransport :=
    ordered_pair_spec_transport_left_of_equality
      left_source left_target right_source pair
      hLeftSource hLeftTarget hRightSource hPair
      hLeftEquality hSpec
  exact ordered_pair_spec_transport_right_of_equality
    left_target right_source right_target pair
    hLeftTarget hRightSource hRightTarget hPair
    hRightEquality hLeftTransport
/-! ## 有序对函数符号的单一性 -/
/-- 两个规范有序对项相等，当且仅当其两个坐标分别相等。 -/
theorem ordered_pair_term_eq_iff_coordinates (left₁ right₁ left₂ right₂ : SetTerm) (hLeft₁ : Term.Admissible left₁ SetSort.set)
    (hRight₁ : Term.Admissible right₁ SetSort.set) (hLeft₂ : Term.Admissible left₂ SetSort.set) (hRight₂ : Term.Admissible right₂ SetSort.set) :
    ⊢ₘ[ordered_pair_operator_theory] (⟨left₁, right₁⟩ₘ ≐ₘ
          ⟨left₂, right₂⟩ₘ) ↔ₘ ((left₁ ≐ₘ left₂) ∧ₘ (right₁ ≐ₘ right₂)) := by
  let pair₁ := ordered_pair_term left₁ right₁
  let pair₂ := ordered_pair_term left₂ right₂
  have hPair₁ :
      Term.Admissible pair₁ SetSort.set :=
    ordered_pair_term_admissible
      left₁ right₁ hLeft₁ hRight₁
  have hPair₂ :
      Term.Admissible pair₂ SetSort.set :=
    ordered_pair_term_admissible
      left₂ right₂ hLeft₂ hRight₂
  apply FirstOrder.Derives.iffIntro
  · let Γ : Context signature :=
      [pair₁ ≐ₘ pair₂]
    have hPairEquality :
        Γ ⊢ₘ[ordered_pair_operator_theory]
          pair₁ ≐ₘ pair₂ :=
      .assumption (by simp [Γ])
    have hLeftProjection₁ :
        Γ ⊢ₘ[ordered_pair_operator_theory]
          left_projection_spec pair₁ left₁ :=
      FirstOrder.Derives.context_weaken_cons (by
          simpa [pair₁] using
            ordered_pair_term_left_projection_spec
              left₁ right₁ hLeft₁ hRight₁)
    have hLeftProjection₂ :
        Γ ⊢ₘ[ordered_pair_operator_theory]
          left_projection_spec pair₂ left₂ :=
      FirstOrder.Derives.context_weaken_cons (by
          simpa [pair₂] using
            ordered_pair_term_left_projection_spec
              left₂ right₂ hLeft₂ hRight₂)
    have hLeftEquality :
        Γ ⊢ₘ[ordered_pair_operator_theory]
          left₁ ≐ₘ left₂ :=
      left_projection_unique_of_pair_equality
        pair₁ pair₂ left₁ left₂
        hPair₁ hPair₂ hLeft₁ hLeft₂
        hPairEquality hLeftProjection₁
        hLeftProjection₂
    have hLeftSymmetry :
        Γ ⊢ₘ[ordered_pair_operator_theory]
          left₂ ≐ₘ left₁ :=
      Metatheory.Derives.equality_symm
        hLeftEquality
    have hOuterSpec₁ :
        Γ ⊢ₘ[ordered_pair_operator_theory]
          ordered_pair_spec left₁ right₁ pair₁ :=
      FirstOrder.Derives.context_weaken_cons (by
          simpa [pair₁] using
            ordered_pair_term_spec_derives
              left₁ right₁ hLeft₁ hRight₁)
    have hOuterSpec₂ :
        Γ ⊢ₘ[ordered_pair_operator_theory]
          ordered_pair_spec left₂ right₂ pair₂ :=
      FirstOrder.Derives.context_weaken_cons (by
          simpa [pair₂] using
            ordered_pair_term_spec_derives
              left₂ right₂ hLeft₂ hRight₂)
    have hOuterSpec₂Aligned :
        Γ ⊢ₘ[ordered_pair_operator_theory]
          ordered_pair_spec left₁ right₂ pair₂ :=
      ordered_pair_spec_transport_left_of_equality
        left₂ left₁ right₂ pair₂
        hLeft₂ hLeft₁ hRight₂ hPair₂
        hLeftSymmetry hOuterSpec₂
    let singleton :=
      singleton_term left₁
    let inner₁ :=
      unordered_pair_term left₁ right₁
    let inner₂ :=
      unordered_pair_term left₁ right₂
    have hSingleton :
        Term.Admissible singleton SetSort.set :=
      singleton_term_admissible left₁ hLeft₁
    have hInner₁ :
        Term.Admissible inner₁ SetSort.set :=
      unordered_pair_term_admissible
        left₁ right₁ hLeft₁ hRight₁
    have hInner₂ :
        Term.Admissible inner₂ SetSort.set :=
      unordered_pair_term_admissible
        left₁ right₂ hLeft₁ hRight₂
    have hInnerEquality :
        Γ ⊢ₘ[ordered_pair_operator_theory]
          inner₁ ≐ₘ inner₂ := by
      simpa [ordered_pair_spec, singleton,
        inner₁, inner₂] using
        pair_spec_right_unique_of_pair_equality
          singleton inner₁ inner₂ pair₁ pair₂
          hSingleton hInner₁ hInner₂
          hPair₁ hPair₂ (by
            simpa [ordered_pair_spec, singleton,
              inner₁] using hOuterSpec₁) (by
            simpa [ordered_pair_spec, singleton,
              inner₂] using hOuterSpec₂Aligned)
          hPairEquality
    have hInnerSpec₁ :
        Γ ⊢ₘ[ordered_pair_operator_theory]
          pair_spec left₁ right₁ inner₁ :=
      FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.theory_weaken (fun _ hFormula =>
            singleton_operator_theory_subset_ordered_pair_operator_theory (Or.inr hFormula)) (by
            simpa [inner₁] using
              unordered_pair_term_spec_derives
                left₁ right₁ hLeft₁ hRight₁)
    have hInnerSpec₂ :
        Γ ⊢ₘ[ordered_pair_operator_theory]
          pair_spec left₁ right₂ inner₂ :=
      FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.theory_weaken (fun _ hFormula =>
            singleton_operator_theory_subset_ordered_pair_operator_theory (Or.inr hFormula)) (by
            simpa [inner₂] using
              unordered_pair_term_spec_derives
                left₁ right₂ hLeft₁ hRight₂)
    have hRightEquality :
        Γ ⊢ₘ[ordered_pair_operator_theory]
          right₁ ≐ₘ right₂ :=
      pair_spec_right_unique_of_pair_equality
        left₁ right₁ right₂ inner₁ inner₂
        hLeft₁ hRight₁ hRight₂
        hInner₁ hInner₂ hInnerSpec₁
        hInnerSpec₂ hInnerEquality
    exact FirstOrder.Derives.conjIntro
      hLeftEquality hRightEquality
  · let Γ : Context signature :=
      [(left₁ ≐ₘ left₂) ∧ₘ (right₁ ≐ₘ right₂)]
    have hCoordinates :
        Γ ⊢ₘ[ordered_pair_operator_theory] (left₁ ≐ₘ left₂) ∧ₘ (right₁ ≐ₘ right₂) :=
      .assumption (by simp [Γ])
    have hLeftEquality :=
      FirstOrder.Derives.conjElimLeft
        hCoordinates
    have hRightEquality :=
      FirstOrder.Derives.conjElimRight
        hCoordinates
    have hOuterSpec₁ :
        Γ ⊢ₘ[ordered_pair_operator_theory]
          ordered_pair_spec left₁ right₁ pair₁ :=
      FirstOrder.Derives.context_weaken_cons (by
          simpa [pair₁] using
            ordered_pair_term_spec_derives
              left₁ right₁ hLeft₁ hRight₁)
    have hOuterSpec₁Transported :
        Γ ⊢ₘ[ordered_pair_operator_theory]
          ordered_pair_spec left₂ right₂ pair₁ :=
      ordered_pair_spec_transport_coordinates_of_equalities
        left₁ left₂ right₁ right₂ pair₁
        hLeft₁ hLeft₂ hRight₁ hRight₂ hPair₁
        hLeftEquality hRightEquality hOuterSpec₁
    have hOuterSpec₂ :
        Γ ⊢ₘ[ordered_pair_operator_theory]
          ordered_pair_spec left₂ right₂ pair₂ :=
      FirstOrder.Derives.context_weaken_cons (by
          simpa [pair₂] using
            ordered_pair_term_spec_derives
              left₂ right₂ hLeft₂ hRight₂)
    have hUnique :
        Γ ⊢ₘ[ordered_pair_operator_theory]
          ordered_pair_spec left₂ right₂ pair₁ ⟶ₘ
            ordered_pair_spec left₂ right₂ pair₂ ⟶ₘ (pair₁ ≐ₘ pair₂) :=
      FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.theory_weaken (fun _ hFormula =>
            extensionality_theory_subset_ordered_pair_operator_theory
              hFormula) (ordered_pair_unique
            left₂ right₂ pair₁ pair₂
            hLeft₂ hRight₂ hPair₁ hPair₂)
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
        hUnique hOuterSpec₁Transported)
      hOuterSpec₂
/-! ## 有序对谓词与左投影存在性 -/
/-- 每个规范有序对项都满足“是有序对”谓词。 -/
theorem ordered_pair_term_is_ordered_pair_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[relation_function_theory]
      is_ordered_pair_formula
        ⟨left, right⟩ₘ := by
  let ordered := ordered_pair_term left right
  have hOrdered :
      Term.Admissible ordered SetSort.set :=
    ordered_pair_term_admissible
      left right hLeft hRight
  have hDefinition :
      ⊢ₘ[relation_function_theory]
        is_ordered_pair_definition_instance ordered :=
    is_ordered_pair_definition_instance_derives
      ordered hOrdered
  have hCondition :
      ⊢ₘ[relation_function_theory]
        is_ordered_pair_condition ordered := by
    have hConditionAdmissible :
        Formula.Admissible (is_ordered_pair_condition ordered) :=
      is_ordered_pair_condition_admissible
        hOrdered
    unfold is_ordered_pair_condition
    nd_apply FirstOrder.Derives.exists_intro (term := left)
    have hRightExistentialAdmissible :
        Formula.Admissible (Formula.openAt SetSort.set 0 left (∃ₘ[SetSort.set],
              ordered ≐ₘ ⟨bₛ#1, bₛ#0⟩ₘ)) :=
      Formula.Admissible.exists_openAt (σ := signature) (body :=
          ∃ₘ[SetSort.set],
            ordered ≐ₘ ⟨bₛ#1, bₛ#0⟩ₘ) (term := left)
        SetSort.set (by
          simpa [is_ordered_pair_condition] using
            hConditionAdmissible)
        hLeft
    nd_apply FirstOrder.Derives.exists_intro (term := right)
    have hOrderedOpenOne :
        Term.openAt SetSort.set 1 left ordered =
          ordered :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 1 left ordered hOrdered.2
    have hOrderedOpenZero :
        Term.openAt SetSort.set 0 right ordered =
          ordered :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 right ordered hOrdered.2
    have hLeftOpenZero :
        Term.openAt SetSort.set 0 right left =
          left :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 right left hLeft.2
    simpa [ordered, ordered_pair_term,
      Formula.openAt, Formula.next_depth,
      Term.openAt, hOrderedOpenOne,
      hOrderedOpenZero, hLeftOpenZero] using
      (FirstOrder.Derives.eq_refl_m
        (T := relation_function_theory) (Γ := [])
        (sort := SetSort.set) ordered)
  exact FirstOrder.Derives.iffElimLeft
    hDefinition hCondition
/-- 有序对条件推出左投影存在。 -/
theorem is_ordered_pair_condition_implies_left_projection_exists (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ[relation_function_theory]
      is_ordered_pair_condition pair ⟶ₘ
        left_projection_exists pair := by
  let condition :=
    is_ordered_pair_condition pair
  let conclusion :=
    left_projection_exists pair
  let left_bound_body : SetFormula :=
    ∃ₘ[SetSort.set],
      pair ≐ₘ ⟨bₛ#1, bₛ#0⟩ₘ
  let left :=
    FreshVariable.fresh_id SetSort.set
      [condition, conclusion, left_bound_body]
  let left_point :=
    Formula.openAt SetSort.set 0 (x#left) left_bound_body
  have hLeftFreshCondition : (SetSort.set, left) freshForₘ
        condition := by
    dsimp [left]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hLeftFreshConclusion : (SetSort.set, left) freshForₘ
        conclusion := by
    dsimp [left]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hLeftFreshBoundBody : (SetSort.set, left) freshForₘ
        left_bound_body := by
    dsimp [left]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hConditionAdmissible :
      Formula.Admissible condition := by
    dsimp [condition]
    exact is_ordered_pair_condition_admissible
      hPair
  have hLeftPointAdmissible :
      Formula.Admissible left_point := by
    have hOpened :=
      Formula.Admissible.exists_openAt (σ := signature) (body := left_bound_body) (term := x#left)
        SetSort.set (by
          simpa [condition,
            is_ordered_pair_condition,
            left_bound_body] using
            hConditionAdmissible) (set_variable_admissible left)
    simpa [left_point] using hOpened
  change
    ⊢ₘ[relation_function_theory]
      condition ⟶ₘ conclusion
  nd_apply FirstOrder.Derives.impIntro
  have hLeftExists :
      [condition] ⊢ₘ[relation_function_theory] (∃ₘ[SetSort.set, left],
          left_point) := by
    simpa [condition,
      is_ordered_pair_condition,
      left_point, left_bound_body,
      Formula.closeFreeAt_openAt
        SetSort.set left 0 left_bound_body
        hLeftFreshBoundBody] using (show
        [condition] ⊢ₘ[relation_function_theory]
          condition from
        .assumption (by simp))
  have hLeftCase :
      left_point :: [condition]
        ⊢ₘ[relation_function_theory]
          conclusion := by
    let right_bound_body : SetFormula :=
      pair ≐ₘ ⟨x#left, bₛ#0⟩ₘ
    let right :=
      FreshVariable.fresh_id SetSort.set
        [right_bound_body, left_point,
          condition, conclusion]
    let right_point :=
      Formula.openAt SetSort.set 0 (x#right) right_bound_body
    have hRightFreshBoundBody : (SetSort.set, right) freshForₘ
          right_bound_body := by
      dsimp [right]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    have hRightFreshLeftPoint : (SetSort.set, right) freshForₘ
          left_point := by
      dsimp [right]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    have hRightFreshCondition : (SetSort.set, right) freshForₘ
          condition := by
      dsimp [right]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    have hRightFreshConclusion : (SetSort.set, right) freshForₘ
          conclusion := by
      dsimp [right]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    have hPairOpenOne :
        Term.openAt SetSort.set 1 (x#left) pair =
          pair :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 1 (x#left) pair hPair.2
    have hRightPointAdmissible :
        Formula.Admissible right_point := by
      have hOpened :=
        Formula.Admissible.exists_openAt (σ := signature) (body := right_bound_body) (term := x#right)
          SetSort.set (by
            simpa [left_point, left_bound_body,
              right_bound_body, Formula.openAt,
              Formula.next_depth, Term.openAt,
              hPairOpenOne] using
              hLeftPointAdmissible) (set_variable_admissible right)
      simpa [right_point] using hOpened
    have hRightExists :
        left_point :: [condition]
          ⊢ₘ[relation_function_theory] (∃ₘ[SetSort.set, right],
              right_point) := by
      have hLeftPointNormalized :
          left_point :: [condition]
            ⊢ₘ[relation_function_theory]
              Formula.existsE SetSort.set
                right_bound_body := by
        simpa [left_point, left_bound_body,
          right_bound_body,
          Formula.openAt, Formula.next_depth,
          Term.openAt, hPairOpenOne] using (show
            left_point :: [condition]
              ⊢ₘ[relation_function_theory]
              left_point from
            .assumption (by simp))
      have hRightClosure :
          Formula.closeFreeAt SetSort.set
              right 0 right_point =
            right_bound_body := by
        dsimp [right_point]
        exact Formula.closeFreeAt_openAt
          SetSort.set right 0
          right_bound_body
          hRightFreshBoundBody
      change
        left_point :: [condition]
          ⊢ₘ[relation_function_theory]
            Formula.existsE SetSort.set (Formula.closeFreeAt SetSort.set
                right 0 right_point)
      rw [hRightClosure]
      exact hLeftPointNormalized
    have hRightCase :
        right_point :: left_point :: [condition]
          ⊢ₘ[relation_function_theory]
            conclusion := by
      have hPairOpenZero :
          Term.openAt SetSort.set 0 (x#right) pair =
            pair :=
        Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 (x#right) pair hPair.2
      have hEquality :
          right_point :: left_point :: [condition]
            ⊢ₘ[relation_function_theory]
              pair ≐ₘ ⟨x#left, x#right⟩ₘ := by
        simpa [right_point, right_bound_body,
          Formula.openAt, Term.openAt,
          hPairOpenZero] using (show
            right_point :: left_point :: [condition]
              ⊢ₘ[relation_function_theory]
                right_point from
            .assumption (by simp))
      have hBridge :
          right_point :: left_point :: [condition]
            ⊢ₘ[relation_function_theory] (pair ≐ₘ
                  ⟨x#left, x#right⟩ₘ) ⟶ₘ
                conclusion :=
        FirstOrder.Derives.context_weaken_cons (assumption := right_point) <|
          FirstOrder.Derives.context_weaken_cons (assumption := left_point) <|
            FirstOrder.Derives.context_weaken_cons (assumption := condition) <|
              FirstOrder.Derives.theory_weaken (fun _ hFormula =>
                  ordered_pair_operator_theory_subset_relation_function_theory
                    hFormula) (by
                  simpa [conclusion] using
                    ordered_pair_equality_implies_left_projection_exists
                      pair (x#left) (x#right)
                      hPair (set_variable_admissible left) (set_variable_admissible right))
      exact FirstOrder.Derives.impElim
        hBridge hEquality
    exact FirstOrder.Derives.exists_elim (by
        intro formula hFormula
        have hSentence :=
          relation_function_theory_sentence
            hFormula
        rw [hSentence.2]
        simp) (by
        intro formula hFormula
        rcases List.mem_cons.mp hFormula with
          rfl | hFormula
        · exact hRightFreshLeftPoint
        · rcases List.mem_singleton.mp hFormula with rfl
          exact hRightFreshCondition)
      hRightFreshConclusion
      hRightExists hRightCase
  exact FirstOrder.Derives.exists_elim (by
      intro formula hFormula
      have hSentence :=
        relation_function_theory_sentence
          hFormula
      rw [hSentence.2]
      simp) (by
      intro formula hFormula
      rcases List.mem_singleton.mp hFormula with rfl
      exact hLeftFreshCondition)
    hLeftFreshConclusion
    hLeftExists hLeftCase
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
