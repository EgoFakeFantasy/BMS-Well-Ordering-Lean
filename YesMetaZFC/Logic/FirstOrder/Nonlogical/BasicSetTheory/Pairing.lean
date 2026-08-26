import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Monotonicity
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.PowerSet
/-!
# 配对与单点集
配对公理的核心规格采用现代的析取写法 `x = a ∨ x = b`。文献使用的
`¬(x = a) → x = b` 作为显式兼容规格保留，并在对象经典逻辑内证明二者等价。
无序对与单点集均是具体签名中的真实函数符号，其数学含义由本模块的定义公理给出。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-- `element` 是 `left` 或 `right`。 -/
def pair_member_condition (element left right : SetTerm) :
    SetFormula := (element ≐ₘ left) ∨ₘ (element ≐ₘ right)
/-- 文献采用的经典配对成员条件。 -/
def pair_paper_condition (element left right : SetTerm) :
    SetFormula := (¬ₘ (element ≐ₘ left)) ⟶ₘ (element ≐ₘ right)
/-- `pair` 恰好含有 `left` 与 `right`。 -/
def pair_spec (left right pair : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ pair) ↔ₘ
      pair_member_condition bₛ#0 left right
/-- 文献蕴含写法下的配对规格。 -/
def pair_paper_spec (left right pair : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ pair) ↔ₘ
      pair_paper_condition bₛ#0 left right
/-- 对固定的两个集合断言其无序对存在。 -/
def pair_exists (left right : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
        pair_member_condition bₛ#0 left right
/-- 文献蕴含写法下的配对存在公式。 -/
def pair_paper_exists (left right : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
        pair_paper_condition bₛ#0 left right
/-- 配对存在公理。 -/
def pairing_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      pair_exists (x#0) (x#1)
/-- 文献原式的闭配对公理。 -/
def pairing_paper_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      pair_paper_exists (x#0) (x#1)
/-- 只在外延理论上加入配对存在公理。 -/
def pairing_theory : SetTheory :=
  Theory.insert pairing_axiom extensionality_theory
/-- 无序对函数符号的开放定义实例。 -/
def pair_definition_instance (left right candidate : SetTerm) :
    SetFormula := (candidate ≐ₘ {left, right}ₘ) ↔ₘ
    pair_spec left right candidate
/-- 无序对函数符号的定义公理。 -/
def pair_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        pair_definition_instance (x#0) (x#1) (x#2)
/-- 在配对存在理论上加入无序对函数符号的保守定义扩张。 -/
def pairing_operator_theory : SetTheory :=
  Theory.insert pair_definition_axiom pairing_theory
/-- `singleton` 恰好只含有 `element`。 -/
def singleton_spec (element singleton : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ singleton) ↔ₘ (bₛ#0 ≐ₘ element)
/-- 对固定集合断言其单点集存在。 -/
def singleton_exists (element : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ (bₛ#0 ≐ₘ element)
/-- 单点集函数符号的开放定义实例。 -/
def singleton_definition_instance (element : SetTerm) :
    SetFormula :=
  {element}ₘ ≐ₘ {element, element}ₘ
/-- 单点集函数符号的定义公理。 -/
def singleton_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    singleton_definition_instance (x#0)
/-- 在无序对描述符理论上加入单点集函数符号的定义扩张。 -/
def singleton_operator_theory : SetTheory :=
  Theory.insert
    singleton_definition_axiom
    pairing_operator_theory
/-- 配对成员条件在三个 admissible 集合项处仍然 admissible。 -/
theorem pair_member_condition_admissible
    {element left right : SetTerm} (hElement : Term.Admissible element SetSort.set) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Formula.Admissible (pair_member_condition element left right) :=
  Formula.Admissible.disj (Formula.Admissible.equal hElement hLeft) (Formula.Admissible.equal hElement hRight)
/-- 文献配对成员条件在三个 admissible 集合项处仍然 admissible。 -/
theorem pair_paper_condition_admissible
    {element left right : SetTerm} (hElement : Term.Admissible element SetSort.set) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Formula.Admissible (pair_paper_condition element left right) :=
  Formula.Admissible.imp (Formula.Admissible.neg (Formula.Admissible.equal hElement hLeft)) (Formula.Admissible.equal hElement hRight)
/-- 配对规格在三个 admissible 集合项处仍然 admissible。 -/
theorem pair_spec_admissible
    {left right pair : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hPair : Term.Admissible pair SetSort.set) :
    Formula.Admissible (pair_spec left right pair) := by
  prove_admissible
/-- 配对规格的计算证书由三个集合项证书直接组合。 -/
@[formula_check]
theorem pair_spec_check
    {left right pair : SetTerm}
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set)
    (hPair : Term.CheckCertificate pair SetSort.set) :
    Formula.CheckCertificate (pair_spec left right pair) :=
  Formula.check_admissible_complete <|
    pair_spec_admissible
      hLeft.admissible hRight.admissible hPair.admissible
/-- 文献配对规格在三个 admissible 集合项处仍然 admissible。 -/
theorem pair_paper_spec_admissible
    {left right pair : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hPair : Term.Admissible pair SetSort.set) :
    Formula.Admissible (pair_paper_spec left right pair) := by
  prove_admissible
/-- 单点集规格在 admissible 的元素项与候选项处仍然 admissible。 -/
theorem singleton_spec_admissible
    {element singleton : SetTerm} (hElement : Term.Admissible element SetSort.set) (hSingleton : Term.Admissible singleton SetSort.set) :
    Formula.Admissible (singleton_spec element singleton) := by
  prove_admissible
/-- 文献配对成员条件与现代析取条件在对象经典逻辑中等价。 -/
theorem pair_paper_condition_iff_member_condition (element left right : SetTerm) (hElement : Term.Admissible element SetSort.set)
    (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ
      pair_paper_condition element left right ↔ₘ
        pair_member_condition element left right := by
  simpa [pair_paper_condition, pair_member_condition] using (Metatheory.Derives.neg_imp_disj_iff_m (σ := signature) (T := (Theory.empty : SetTheory)) (Γ := [])
      (φ := element ≐ₘ left) (ψ := element ≐ₘ right) (Formula.Admissible.equal hElement hLeft) (Formula.Admissible.equal hElement hRight))
/-- 文献配对规格与现代配对规格在对象经典逻辑中等价。 -/
theorem pair_paper_spec_iff_spec (left right pair : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ
      pair_paper_spec left right pair ↔ₘ
        pair_spec left right pair := by
  let paper_body : SetFormula := (bₛ#0 ∈ₘ pair) ↔ₘ
      pair_paper_condition bₛ#0 left right
  let modern_body : SetFormula := (bₛ#0 ∈ₘ pair) ↔ₘ
      pair_member_condition bₛ#0 left right
  let element :=
    FreshVariable.fresh_id SetSort.set
      [paper_body, modern_body]
  let paper_point :=
    Formula.openAt SetSort.set 0 (x#element) paper_body
  let modern_point :=
    Formula.openAt SetSort.set 0 (x#element) modern_body
  have hElementFreshPaper : (SetSort.set, element) freshForₘ paper_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshModern : (SetSort.set, element) freshForₘ modern_body := by
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
  have hPairOpen :
      Term.openAt SetSort.set 0 (x#element) pair =
        pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) pair hPair.2
  have hOpenedElement :
      Term.Admissible (Term.openAt SetSort.set 0 (x#element) bₛ#0)
        SetSort.set := by
    simpa [Term.openAt] using
      set_variable_admissible element
  have hOpenedLeft :
      Term.Admissible (Term.openAt SetSort.set 0 (x#element) left)
        SetSort.set := by
    simpa [hLeftOpen] using hLeft
  have hOpenedRight :
      Term.Admissible (Term.openAt SetSort.set 0 (x#element) right)
        SetSort.set := by
    simpa [hRightOpen] using hRight
  have hOpenedPair :
      Term.Admissible (Term.openAt SetSort.set 0 (x#element) pair)
        SetSort.set := by
    simpa [hPairOpen] using hPair
  have hPointIff :
      ⊢ₘ paper_point ↔ₘ modern_point := by
    have hCondition :=
      pair_paper_condition_iff_member_condition (Term.openAt SetSort.set 0 (x#element) bₛ#0) (Term.openAt SetSort.set 0 (x#element) left)
        (Term.openAt SetSort.set 0 (x#element) right)
        hOpenedElement hOpenedLeft hOpenedRight
    have hCongruence :=
      Metatheory.Derives.iff_right_congr_m (σ := signature) (T := (Theory.empty : SetTheory)) (Γ := []) (φ :=
          Term.openAt SetSort.set 0 (x#element) bₛ#0 ∈ₘ
            Term.openAt SetSort.set 0 (x#element) pair) (membership_formula_admissible
          hOpenedElement hOpenedPair)
        hCondition
    simpa [paper_point, modern_point,
      paper_body, modern_body,
      pair_paper_condition, pair_member_condition,
      Formula.openAt, Term.openAt] using hCongruence
  have hClosed :
      ⊢ₘ (∀ₘ[SetSort.set, element], paper_point) ↔ₘ (∀ₘ[SetSort.set, element], modern_point) :=
    Metatheory.Derives.forall_iff_mono (T := (Theory.empty : SetTheory)) (Γ := []) (sort := SetSort.set) (eigen := element) (left := paper_point)
      (right := modern_point) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        cases hFormula)
      hPointIff
  simpa [pair_paper_spec, pair_spec,
    paper_point, modern_point,
    Formula.closeFreeAt_openAt
      SetSort.set element 0 paper_body
      hElementFreshPaper,
    Formula.closeFreeAt_openAt
      SetSort.set element 0 modern_body
      hElementFreshModern] using hClosed
/-- 文献配对存在公式与现代配对存在公式等价。 -/
theorem pair_paper_exists_iff_exists (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ
      pair_paper_exists left right ↔ₘ
        pair_exists left right := by
  let paper_body : SetFormula :=
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
        pair_paper_condition bₛ#0 left right
  let modern_body : SetFormula :=
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
        pair_member_condition bₛ#0 left right
  let candidate :=
    FreshVariable.fresh_id SetSort.set
      [paper_body, modern_body]
  let paper_point :=
    Formula.openAt SetSort.set 0 (x#candidate) paper_body
  let modern_point :=
    Formula.openAt SetSort.set 0 (x#candidate) modern_body
  have hCandidateFreshPaper : (SetSort.set, candidate) freshForₘ paper_body := by
    dsimp [candidate]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hCandidateFreshModern : (SetSort.set, candidate) freshForₘ modern_body := by
    dsimp [candidate]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hLeftOpenOne :
      Term.openAt SetSort.set 1 (x#candidate) left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 (x#candidate)
      left hLeft.2
  have hRightOpenOne :
      Term.openAt SetSort.set 1 (x#candidate) right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 (x#candidate)
      right hRight.2
  have hPointIff :
      ⊢ₘ paper_point ↔ₘ modern_point := by
    simpa [paper_point, modern_point,
      paper_body, modern_body,
      pair_paper_spec, pair_spec,
      pair_paper_condition,
      pair_member_condition,
      Formula.openAt, Formula.next_depth,
      Term.openAt, hLeftOpenOne,
      hRightOpenOne, set_variable,
      set_bound_variable] using
      pair_paper_spec_iff_spec
        left right (x#candidate)
        hLeft hRight (set_variable_admissible candidate)
  have hClosed :
      ⊢ₘ (∃ₘ[SetSort.set, candidate], paper_point) ↔ₘ (∃ₘ[SetSort.set, candidate], modern_point) :=
    Metatheory.Derives.exists_iff_mono (T := (Theory.empty : SetTheory)) (Γ := []) (sort := SetSort.set) (eigen := candidate) (left := paper_point)
      (right := modern_point) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        cases hFormula)
      hPointIff
  simpa [pair_paper_exists, pair_exists,
    paper_point, modern_point,
    Formula.closeFreeAt_openAt
      SetSort.set candidate 0 paper_body
      hCandidateFreshPaper,
    Formula.closeFreeAt_openAt
      SetSort.set candidate 0 modern_body
      hCandidateFreshModern] using hClosed
/-- 文献原式的闭配对公理与现代析取版闭公理等价。 -/
theorem pairing_paper_axiom_iff_pairing_axiom :
    ⊢ₘ
      pairing_paper_axiom ↔ₘ
        pairing_axiom := by
  have hOpen :
      ⊢ₘ
        pair_paper_exists (x#0) (x#1) ↔ₘ
          pair_exists (x#0) (x#1) :=
    pair_paper_exists_iff_exists (x#0) (x#1) (set_variable_admissible 0) (set_variable_admissible 1)
  have hRightClosed :=
    Metatheory.Derives.forall_iff_mono (T := (Theory.empty : SetTheory)) (Γ := []) (sort := SetSort.set) (eigen := 1) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        cases hFormula)
      hOpen
  have hBothClosed :=
    Metatheory.Derives.forall_iff_mono (T := (Theory.empty : SetTheory)) (Γ := []) (sort := SetSort.set) (eigen := 0) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        cases hFormula)
      hRightClosed
  simpa [pairing_paper_axiom,
    pairing_axiom] using hBothClosed
/-- 无序对项满足 proof-carrying 项边界。 -/
theorem unordered_pair_term_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible (unordered_pair_term left right) SetSort.set := by
  simpa [unordered_pair_term] using
    set_function_application_admissible
      .unorderedPair [⟨left, hLeft⟩, ⟨right, hRight⟩]
      (by rfl) (by rfl)

/-- 无序对项的合法性由两个参数的计算证书组合。 -/
@[term_check]
theorem unordered_pair_term_check
    {left right : SetTerm}
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set) :
    Term.CheckCertificate (unordered_pair_term left right) SetSort.set :=
  Term.check_admissible_complete <|
    unordered_pair_term_admissible left right
      hLeft.admissible hRight.admissible

/-- 单点集项满足 proof-carrying 项边界。 -/
theorem singleton_term_admissible (element : SetTerm) (hElement : Term.Admissible element SetSort.set) :
    Term.Admissible (singleton_term element) SetSort.set := by
  simpa using
    set_function_application_admissible
      .singleton [⟨element, by assumption⟩]
      (by rfl) (by rfl)
/-- 单点集项的合法性由元素项证书计算。 -/
@[term_check]
theorem singleton_term_check
    {element : SetTerm}
    (hElement : Term.CheckCertificate element SetSort.set) :
    Term.CheckCertificate (singleton_term element) SetSort.set :=
  Term.check_admissible_complete <|
    singleton_term_admissible element hElement.admissible
/-- 无序对函数符号的开放定义实例在 admissible 参数处仍然 admissible。 -/
theorem pair_definition_instance_admissible
    {left right candidate : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (pair_definition_instance
        left right candidate) :=
  Formula.Admissible.iff (Formula.Admissible.equal
      hCandidate (unordered_pair_term_admissible
        left right hLeft hRight)) (pair_spec_admissible
      hLeft hRight hCandidate)
/-- 单点集函数符号的开放定义实例在 admissible 参数处仍然 admissible。 -/
theorem singleton_definition_instance_admissible
    {element : SetTerm} (hElement : Term.Admissible element SetSort.set) :
    Formula.Admissible (singleton_definition_instance element) :=
  Formula.Admissible.equal (singleton_term_admissible element hElement) (unordered_pair_term_admissible
      element element hElement hElement)
/-- 配对存在公理满足公共 proof-carrying 良构性边界。 -/
theorem pairing_axiom_admissible :
    Formula.Admissible pairing_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 配对存在理论仍然 admissible。 -/
theorem pairing_theory_admissible :
    Theory.Admissible pairing_theory :=
  Theory.admissible_insert
    pairing_axiom_admissible
    extensionality_theory_admissible
/-- 无序对函数符号定义公理满足公共 proof-carrying 良构性边界。 -/
theorem pair_definition_axiom_admissible :
    Formula.Admissible pair_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 无序对函数符号定义扩张后的理论仍然 admissible。 -/
theorem pairing_operator_theory_admissible :
    Theory.Admissible pairing_operator_theory :=
  Theory.admissible_insert
    pair_definition_axiom_admissible
    pairing_theory_admissible
/-- 单点集函数符号定义公理满足公共 proof-carrying 良构性边界。 -/
theorem singleton_definition_axiom_admissible :
    Formula.Admissible singleton_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 单点集函数符号定义扩张后的理论仍然 admissible。 -/
theorem singleton_operator_theory_admissible :
    Theory.Admissible singleton_operator_theory :=
  Theory.admissible_insert
    singleton_definition_axiom_admissible
    pairing_operator_theory_admissible
/-- 无序对运算符理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem pairing_operator_theory_sentence
    {formula : SetFormula} (hFormula : pairing_operator_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact pairing_operator_theory_admissible
      formula hFormula
  · change
      formula = pair_definition_axiom ∨ (formula = pairing_axiom ∨
          extensionality_theory formula) at hFormula
    rcases hFormula with rfl | hFormula
    · native_decide
    · rcases hFormula with rfl | hFormula
      · native_decide
      · change formula = extensionality_axiom at hFormula
        subst formula
        native_decide
/-- 单点集运算符理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem singleton_operator_theory_sentence
    {formula : SetFormula} (hFormula : singleton_operator_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact singleton_operator_theory_admissible
      formula hFormula
  · change
      formula = singleton_definition_axiom ∨
        pairing_operator_theory formula at hFormula
    rcases hFormula with rfl | hFormula
    · native_decide
    · exact (pairing_operator_theory_sentence hFormula).2
/-- 配对存在公理可在任意两个 admissible 集合项处实例化。 -/
theorem pair_exists_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[pairing_theory]
      pair_exists left right := by
  have hAxiom :
      ⊢ₘ[pairing_theory] pairing_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hLeftInstance :=
    FirstOrder.Derives.forall_elim
      (term := left) hAxiom
  have hRightInstance :=
    FirstOrder.Derives.forall_elim
      (term := right) hLeftInstance
  have hLeftOpenTwo :
      Term.openAt SetSort.set 2 right left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 right left hLeft.2
  simpa [pairing_axiom, pair_exists,
    pair_member_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, hLeftOpenTwo,
    set_variable,
    set_bound_variable] using hRightInstance
/-- 同一对元素的两个配对候选必相等。 -/
theorem pair_unique (first second left right : SetTerm) (hFirst : Term.Admissible first SetSort.set) (hSecond : Term.Admissible second SetSort.set)
    (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[extensionality_theory]
      pair_spec first second left ⟶ₘ
        pair_spec first second right ⟶ₘ (left ≐ₘ right) := by
  simpa [pair_spec,
    membership_specification] using
    membership_specification_unique
      left right (pair_member_condition
        bₛ#0 first second)
      hLeft hRight (pair_spec_admissible
        hFirst hSecond hLeft) (pair_spec_admissible
        hFirst hSecond hRight)
/-- 重复元素的配对规格恰好就是单点集规格。 -/
theorem pair_repeated_spec_iff_singleton_spec (element candidate : SetTerm) (hElement : Term.Admissible element SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ
      pair_spec element element candidate ↔ₘ
        singleton_spec element candidate := by
  let pair_body : SetFormula := (bₛ#0 ∈ₘ candidate) ↔ₘ
      pair_member_condition
        bₛ#0 element element
  let singleton_body : SetFormula := (bₛ#0 ∈ₘ candidate) ↔ₘ (bₛ#0 ≐ₘ element)
  let member :=
    FreshVariable.fresh_id SetSort.set
      [pair_body, singleton_body]
  let pair_point :=
    Formula.openAt SetSort.set 0 (x#member) pair_body
  let singleton_point :=
    Formula.openAt SetSort.set 0 (x#member) singleton_body
  have hMemberFreshPair : (SetSort.set, member) freshForₘ pair_body := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hMemberFreshSingleton : (SetSort.set, member) freshForₘ
        singleton_body := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementOpen :
      Term.openAt SetSort.set 0 (x#member) element =
        element :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member)
      element hElement.2
  have hCandidateOpen :
      Term.openAt SetSort.set 0 (x#member) candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member)
      candidate hCandidate.2
  have hOpenedMember :
      Term.Admissible (Term.openAt SetSort.set 0 (x#member) bₛ#0)
        SetSort.set := by
    simpa [Term.openAt] using
      set_variable_admissible member
  have hOpenedElement :
      Term.Admissible (Term.openAt SetSort.set 0 (x#member) element)
        SetSort.set := by
    simpa [hElementOpen] using hElement
  have hOpenedCandidate :
      Term.Admissible (Term.openAt SetSort.set 0 (x#member) candidate)
        SetSort.set := by
    simpa [hCandidateOpen] using hCandidate
  have hPointIff :
      ⊢ₘ pair_point ↔ₘ singleton_point := by
    let equality : SetFormula :=
      Term.openAt SetSort.set 0 (x#member) bₛ#0 ≐ₘ
        Term.openAt SetSort.set 0 (x#member) element
    have hEqualityAdmissible :
        Formula.Admissible equality := by
      dsimp [equality]
      exact Formula.Admissible.equal
        hOpenedMember hOpenedElement
    have hIdempotent :
        ⊢ₘ (equality ∨ₘ equality) ↔ₘ
          equality :=
      Metatheory.Derives.disj_idem_m (σ := signature) (T := (Theory.empty : SetTheory)) (Γ := []) (φ := equality)
        hEqualityAdmissible
    have hCongruence :=
      Metatheory.Derives.iff_right_congr_m (σ := signature) (T := (Theory.empty : SetTheory)) (Γ := []) (φ :=
          Term.openAt SetSort.set 0 (x#member) bₛ#0 ∈ₘ
            Term.openAt SetSort.set 0 (x#member) candidate) (membership_formula_admissible
          hOpenedMember hOpenedCandidate)
        hIdempotent
    simpa [pair_point, singleton_point,
      pair_body, singleton_body, equality,
      pair_member_condition,
      Formula.openAt, Term.openAt] using hCongruence
  have hClosed :
      ⊢ₘ (∀ₘ[SetSort.set, member], pair_point) ↔ₘ (∀ₘ[SetSort.set, member], singleton_point) :=
    Metatheory.Derives.forall_iff_mono (T := (Theory.empty : SetTheory)) (Γ := []) (sort := SetSort.set) (eigen := member) (left := pair_point)
      (right := singleton_point) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        cases hFormula)
      hPointIff
  simpa [pair_spec, singleton_spec,
    pair_point, singleton_point,
    Formula.closeFreeAt_openAt
      SetSort.set member 0 pair_body
      hMemberFreshPair,
    Formula.closeFreeAt_openAt
      SetSort.set member 0 singleton_body
      hMemberFreshSingleton] using hClosed
/-- 配对存在公理推出任意集合的单点集存在。 -/
theorem singleton_exists_derives (element : SetTerm) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[pairing_theory]
      singleton_exists element := by
  let pair_body : SetFormula :=
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
        pair_member_condition
          bₛ#0 element element
  let singleton_body : SetFormula :=
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ (bₛ#0 ≐ₘ element)
  let candidate :=
    FreshVariable.fresh_id SetSort.set
      [pair_body, singleton_body]
  let pair_point :=
    Formula.openAt SetSort.set 0 (x#candidate) pair_body
  let singleton_point :=
    Formula.openAt SetSort.set 0 (x#candidate) singleton_body
  have hCandidateFreshPair : (SetSort.set, candidate) freshForₘ pair_body := by
    dsimp [candidate]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hCandidateFreshSingleton : (SetSort.set, candidate) freshForₘ
        singleton_body := by
    dsimp [candidate]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementOpenOne :
      Term.openAt SetSort.set 1 (x#candidate) element =
        element :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 (x#candidate)
      element hElement.2
  have hPointIff :
      ⊢ₘ pair_point ↔ₘ singleton_point := by
    simpa [pair_point, singleton_point,
      pair_body, singleton_body,
      pair_spec, singleton_spec,
      pair_member_condition,
      Formula.openAt, Formula.next_depth,
      Term.openAt, hElementOpenOne,
      set_variable, set_bound_variable] using
      pair_repeated_spec_iff_singleton_spec
        element (x#candidate)
        hElement (set_variable_admissible candidate)
  have hClosed :
      ⊢ₘ (∃ₘ[SetSort.set, candidate], pair_point) ↔ₘ (∃ₘ[SetSort.set, candidate], singleton_point) :=
    Metatheory.Derives.exists_iff_mono (T := (Theory.empty : SetTheory)) (Γ := []) (sort := SetSort.set) (eigen := candidate) (left := pair_point)
      (right := singleton_point) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        cases hFormula)
      hPointIff
  have hExistenceBridge :
      ⊢ₘ
        pair_exists element element ↔ₘ
          singleton_exists element := by
    simpa [pair_exists, singleton_exists,
      pair_point, singleton_point,
      Formula.closeFreeAt_openAt
        SetSort.set candidate 0 pair_body
        hCandidateFreshPair,
      Formula.closeFreeAt_openAt
        SetSort.set candidate 0 singleton_body
        hCandidateFreshSingleton] using hClosed
  have hPair :
      ⊢ₘ[pairing_theory]
        pair_exists element element :=
    pair_exists_derives
      element element hElement hElement
  exact FirstOrder.Derives.iffElimRight (FirstOrder.Derives.of_empty hExistenceBridge)
    hPair
/-- 无序对定义公理可在任意三个 admissible 集合项处实例化。 -/
theorem pair_definition_instance_derives (left right candidate : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[pairing_operator_theory]
      pair_definition_instance
        left right candidate := by
  have hAxiom :
      ⊢ₘ[pairing_operator_theory]
        pair_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
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
  simpa [pair_definition_axiom,
    pair_definition_instance, pair_spec,
    pair_member_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable,
    unordered_pair_term,
    hLeftOpenOneRight, hLeftOpenTwoRight,
    hLeftOpenZeroCandidate, hLeftOpenOneCandidate,
    hRightOpenZeroCandidate,
    hRightOpenOneCandidate] using hCandidateInstance
/-- 定义扩张中的无序对项满足配对规格。 -/
theorem unordered_pair_term_spec_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[pairing_operator_theory]
      pair_spec left right {left, right}ₘ := by
  have hDefinition :=
    pair_definition_instance_derives
      left right {left, right}ₘ
      hLeft hRight (unordered_pair_term_admissible
        left right hLeft hRight)
  exact FirstOrder.Derives.iffElimRight
    hDefinition (FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) {left, right}ₘ)
/-- 一个候选项等于规范无序对，当且仅当它满足对应配对规格。 -/
theorem unordered_pair_eq_iff_spec (left right candidate : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[pairing_operator_theory] (candidate ≐ₘ {left, right}ₘ) ↔ₘ
        pair_spec left right candidate :=
  pair_definition_instance_derives
    left right candidate hLeft hRight hCandidate
/-- 两个参数的已证明等式可组合为无序对项等式。 -/
theorem unordered_pair_term_congr_of_equalities
    {T : SetTheory} {Γ : Context signature} (left_first right_first left_second right_second : SetTerm) (hLeftFirst : Term.Admissible left_first SetSort.set)
    (hRightFirst : Term.Admissible right_first SetSort.set) (hLeftSecond : Term.Admissible left_second SetSort.set)
    (hRightSecond : Term.Admissible right_second SetSort.set) (hFirstEquality :
      Γ ⊢ₘ[T] left_first ≐ₘ right_first) (hSecondEquality :
      Γ ⊢ₘ[T] left_second ≐ₘ right_second) :
    Γ ⊢ₘ[T]
      {left_first, left_second}ₘ ≐ₘ
        {right_first, right_second}ₘ := by
  exact Metatheory.Derives.binary_term_constructor_congr_of_equalities
    unordered_pair_term
    unordered_pair_term_admissible
    (by intros; simp [Term.substituteFree])
    left_first right_first left_second right_second
    hLeftFirst hRightFirst hLeftSecond hRightSecond
    hFirstEquality hSecondEquality
/-- 两组自由变量等式推出对应无序对项相等。 -/
theorem unordered_pair_term_congr (left_first right_first left_second right_second : FreeVarId) :
    ⊢ₘ[pairing_operator_theory] (x#left_first ≐ₘ x#right_first) ⟶ₘ ((x#left_second ≐ₘ x#right_second) ⟶ₘ ({x#left_first, x#left_second}ₘ ≐ₘ
            {x#right_first, x#right_second}ₘ)) := by
  have hFirstEqualityAdmissible :
      Formula.Admissible (x#left_first ≐ₘ x#right_first) :=
    Formula.Admissible.equal (set_variable_admissible left_first) (set_variable_admissible right_first)
  have hSecondEqualityAdmissible :
      Formula.Admissible (x#left_second ≐ₘ x#right_second) :=
    Formula.Admissible.equal (set_variable_admissible left_second) (set_variable_admissible right_second)
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  exact unordered_pair_term_congr_of_equalities (T := pairing_operator_theory) (Γ :=
      [x#left_second ≐ₘ x#right_second,
        x#left_first ≐ₘ x#right_first]) (x#left_first) (x#right_first) (x#left_second) (x#right_second) (set_variable_admissible left_first)
    (set_variable_admissible right_first)
    (set_variable_admissible left_second)
    (set_variable_admissible right_second)
    (.assumption (by simp)) (.assumption (by simp))
/-- 两组参数等式可运输同一个候选对象的无序对等式。 -/
theorem unordered_pair_eq_transport (left_first right_first left_second right_second candidate : FreeVarId) :
    ⊢ₘ[pairing_operator_theory] (x#left_first ≐ₘ x#right_first) ⟶ₘ ((x#left_second ≐ₘ x#right_second) ⟶ₘ ((x#candidate ≐ₘ
              {x#left_first, x#left_second}ₘ) ⟶ₘ (x#candidate ≐ₘ
              {x#right_first, x#right_second}ₘ))) := by
  let left_pair :=
    unordered_pair_term (x#left_first) (x#left_second)
  let right_pair :=
    unordered_pair_term (x#right_first) (x#right_second)
  have hLeftFirst :
      Term.Admissible (x#left_first) SetSort.set :=
    set_variable_admissible left_first
  have hRightFirst :
      Term.Admissible (x#right_first) SetSort.set :=
    set_variable_admissible right_first
  have hLeftSecond :
      Term.Admissible (x#left_second) SetSort.set :=
    set_variable_admissible left_second
  have hRightSecond :
      Term.Admissible (x#right_second) SetSort.set :=
    set_variable_admissible right_second
  have hCandidate :
      Term.Admissible (x#candidate) SetSort.set :=
    set_variable_admissible candidate
  have hLeftPair :
      Term.Admissible left_pair SetSort.set :=
    unordered_pair_term_admissible (x#left_first) (x#left_second)
      hLeftFirst hLeftSecond
  have hRightPair :
      Term.Admissible right_pair SetSort.set :=
    unordered_pair_term_admissible (x#right_first) (x#right_second)
      hRightFirst hRightSecond
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hPairEquality :
        [x#candidate ≐ₘ left_pair,
          x#left_second ≐ₘ x#right_second,
          x#left_first ≐ₘ x#right_first]
        ⊢ₘ[pairing_operator_theory]
          left_pair ≐ₘ right_pair := by
    simpa [left_pair, right_pair] using
      unordered_pair_term_congr_of_equalities (T := pairing_operator_theory) (Γ :=
          [x#candidate ≐ₘ left_pair,
            x#left_second ≐ₘ x#right_second,
            x#left_first ≐ₘ x#right_first]) (x#left_first) (x#right_first) (x#left_second) (x#right_second)
        hLeftFirst hRightFirst
        hLeftSecond hRightSecond
        (.assumption (by simp)) (.assumption (by simp))
  have hCandidateEquality :
      [x#candidate ≐ₘ left_pair,
          x#left_second ≐ₘ x#right_second,
          x#left_first ≐ₘ x#right_first]
        ⊢ₘ[pairing_operator_theory]
          x#candidate ≐ₘ left_pair :=
    .assumption (by simp)
  exact Metatheory.Derives.equality_trans
    hCandidateEquality hPairEquality
/-- 单点集定义公理可在任意 admissible 集合项处实例化。 -/
theorem singleton_definition_instance_derives (element : SetTerm) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[singleton_operator_theory]
      singleton_definition_instance element := by
  have hAxiom :
      ⊢ₘ[singleton_operator_theory]
        singleton_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hInstance :=
    FirstOrder.Derives.forall_elim
      (term := element) hAxiom
  simpa [singleton_definition_axiom,
    singleton_definition_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.substituteFree, Term.substituteFree,
    singleton_term, unordered_pair_term] using hInstance
/-- 定义扩张中的单点集项等于对应的重复无序对项。 -/
theorem singleton_term_eq_pair_derives (element : SetTerm) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[singleton_operator_theory]
      {element}ₘ ≐ₘ {element, element}ₘ := by
  simpa [singleton_definition_instance] using
    singleton_definition_instance_derives
      element hElement
/-- 定义扩张中的单点集项满足单点集规格。 -/
theorem singleton_term_spec_derives (element : SetTerm) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[singleton_operator_theory]
      singleton_spec element {element}ₘ := by
  let singleton := singleton_term element
  let repeated_pair :=
    unordered_pair_term element element
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [Formula.equal element element]
  have hElementFresh : (SetSort.set, parameter) ∉
        Term.freeSupport element := by
    dsimp [parameter]
    exact FreshVariable.fresh_term_not_mem_m
      SetSort.set element
  have hElementFixedSingleton :
      Term.substituteFree SetSort.set
          parameter singleton element =
        element :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter singleton
      element hElementFresh
  have hElementFixedPair :
      Term.substituteFree SetSort.set
          parameter repeated_pair element =
        element :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter repeated_pair
      element hElementFresh
  have hSingleton :
      Term.Admissible singleton SetSort.set :=
    singleton_term_admissible element hElement
  have hRepeatedPair :
      Term.Admissible repeated_pair SetSort.set :=
    unordered_pair_term_admissible
      element element hElement hElement
  have hEquality :
      ⊢ₘ[singleton_operator_theory]
        singleton ≐ₘ repeated_pair := by
    simpa [singleton, repeated_pair] using
      singleton_term_eq_pair_derives
        element hElement
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality (T := singleton_operator_theory) (Γ := []) (sort := SetSort.set) (eigen := parameter) (left := singleton)
      (right := repeated_pair) (body :=
        singleton_spec element (x#parameter))
      hEquality
  have hCongruenceNormalized :
      ⊢ₘ[singleton_operator_theory]
        singleton_spec element singleton ↔ₘ
          singleton_spec element repeated_pair := by
    simpa [singleton_spec,
      Formula.substituteFree, Term.substituteFree,
      hElementFixedSingleton, hElementFixedPair,
      set_variable] using hCongruence
  have hPairSpec :
      ⊢ₘ[singleton_operator_theory]
        pair_spec element element repeated_pair :=
    FirstOrder.Derives.theory_weaken (by
        intro formula hFormula
        exact Or.inr hFormula) (by
        simpa [repeated_pair] using
          unordered_pair_term_spec_derives
            element element hElement hElement)
  have hPairSingletonBridge :
      ⊢ₘ[singleton_operator_theory]
        pair_spec element element repeated_pair ↔ₘ
          singleton_spec element repeated_pair :=
    FirstOrder.Derives.of_empty (pair_repeated_spec_iff_singleton_spec
        element repeated_pair
        hElement hRepeatedPair)
  have hRepeatedPairSpec :=
    FirstOrder.Derives.iffElimRight
      hPairSingletonBridge hPairSpec
  exact FirstOrder.Derives.iffElimLeft
    hCongruenceNormalized hRepeatedPairSpec
/-- 配对规格在任意 admissible 成员项处的点态实例。 -/
theorem pair_spec_membership_iff
    {T : SetTheory} {Γ : Context signature} (left right pair member : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hPair : Term.Admissible pair SetSort.set) (hMember : Term.Admissible member SetSort.set)
    (hSpec : Γ ⊢ₘ[T] pair_spec left right pair) :
    Γ ⊢ₘ[T] (member ∈ₘ pair) ↔ₘ ((member ≐ₘ left) ∨ₘ (member ≐ₘ right)) := by
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := member) hSpec
  simpa [pair_spec, pair_member_condition,
    Formula.openAt, Term.openAt,
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 member left hLeft.2,
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 member right hRight.2,
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 member pair hPair.2] using hAt
/-- 单点集规格在任意 admissible 成员项处的点态实例。 -/
theorem singleton_spec_membership_iff
    {T : SetTheory} {Γ : Context signature} (element singleton member : SetTerm) (hElement : Term.Admissible element SetSort.set)
    (hSingleton : Term.Admissible singleton SetSort.set) (hMember : Term.Admissible member SetSort.set) (hSpec : Γ ⊢ₘ[T] singleton_spec element singleton) :
    Γ ⊢ₘ[T] (member ∈ₘ singleton) ↔ₘ (member ≐ₘ element) := by
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := member) hSpec
  simpa [singleton_spec, Formula.openAt,
    Term.openAt,
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 member element hElement.2,
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 member singleton
      hSingleton.2] using hAt
/--
同一个配对候选在首项固定时，第二项唯一。
证明只实例化左右候选本身，并由 `derive_prop` 完成两个析取分支中的等式组合。
-/
theorem pair_spec_right_unique (first left right pair : SetTerm) (hFirst : Term.Admissible first SetSort.set) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ
      pair_spec first left pair ⟶ₘ
        pair_spec first right pair ⟶ₘ (left ≐ₘ right) := by
  have hLeftSpecAdmissible :
      Formula.Admissible (pair_spec first left pair) :=
    pair_spec_admissible
      hFirst hLeft hPair
  have hRightSpecAdmissible :
      Formula.Admissible (pair_spec first right pair) :=
    pair_spec_admissible
      hFirst hRight hPair
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [pair_spec first right pair,
      pair_spec first left pair]
  have hLeftSpec :
      Γ ⊢ₘ pair_spec first left pair :=
    .assumption (by simp [Γ])
  have hRightSpec :
      Γ ⊢ₘ pair_spec first right pair :=
    .assumption (by simp [Γ])
  have hLeftAtLeft :=
    pair_spec_membership_iff
      first left pair left
      hFirst hLeft hPair hLeft hLeftSpec
  have hRightAtLeft :=
    pair_spec_membership_iff
      first right pair left
      hFirst hRight hPair hLeft hRightSpec
  have hLeftMem :
      Γ ⊢ₘ left ∈ₘ pair :=
    FirstOrder.Derives.iffElimLeft
      hLeftAtLeft
        (FirstOrder.Derives.disjIntroRight
          (FirstOrder.Derives.eq_refl_m left))
  have hLeftCases :
      Γ ⊢ₘ (left ≐ₘ first) ∨ₘ (left ≐ₘ right) :=
    FirstOrder.Derives.iffElimRight
      hRightAtLeft hLeftMem
  have hRightAtRight :=
    pair_spec_membership_iff
      first right pair right
      hFirst hRight hPair hRight hRightSpec
  have hLeftAtRight :=
    pair_spec_membership_iff
      first left pair right
      hFirst hLeft hPair hRight hLeftSpec
  have hRightMem :
      Γ ⊢ₘ right ∈ₘ pair :=
    FirstOrder.Derives.iffElimLeft
      hRightAtRight
        (FirstOrder.Derives.disjIntroRight
          (FirstOrder.Derives.eq_refl_m right))
  have hRightCases :
      Γ ⊢ₘ (right ≐ₘ first) ∨ₘ (right ≐ₘ left) :=
    FirstOrder.Derives.iffElimRight
      hLeftAtRight hRightMem
  have hRightLeftSymm :
      Γ ⊢ₘ (right ≐ₘ left) ⟶ₘ (left ≐ₘ right) :=
    Metatheory.Derives.equality_symm_imp
  have hRightFirstSymm :
      Γ ⊢ₘ (right ≐ₘ first) ⟶ₘ (first ≐ₘ right) :=
    Metatheory.Derives.equality_symm_imp
  have hTrans :
      Γ ⊢ₘ (left ≐ₘ first) ⟶ₘ ((first ≐ₘ right) ⟶ₘ (left ≐ₘ right)) :=
    Metatheory.Derives.equality_trans_imp
  derive_prop
/-- 相等的两个配对候选在首项固定时具有相同的第二项。 -/
theorem pair_spec_right_unique_of_pair_equality
    {T : SetTheory} {Γ : Context signature} (first left right pair_left pair_right : SetTerm) (hFirst : Term.Admissible first SetSort.set)
    (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) (hPairLeft : Term.Admissible pair_left SetSort.set)
    (hPairRight : Term.Admissible pair_right SetSort.set) (hLeftSpec :
      Γ ⊢ₘ[T] pair_spec first left pair_left) (hRightSpec :
      Γ ⊢ₘ[T] pair_spec first right pair_right) (hPairEquality :
      Γ ⊢ₘ[T] pair_left ≐ₘ pair_right) :
    Γ ⊢ₘ[T] left ≐ₘ right := by
  have hLeftAtLeft :=
    pair_spec_membership_iff
      first left pair_left left
      hFirst hLeft hPairLeft hLeft hLeftSpec
  have hRightAtLeft :=
    pair_spec_membership_iff
      first right pair_right left
      hFirst hRight hPairRight hLeft hRightSpec
  have hLeftMem :
      Γ ⊢ₘ[T] left ∈ₘ pair_left :=
    FirstOrder.Derives.iffElimLeft
      hLeftAtLeft
        (FirstOrder.Derives.disjIntroRight
          (FirstOrder.Derives.eq_refl_m left))
  have hLeftMembershipTransport :=
    membership_right_iff_of_equality
      left pair_left pair_right
      hLeft hPairLeft hPairRight hPairEquality
  have hLeftMemRight :
      Γ ⊢ₘ[T] left ∈ₘ pair_right :=
    FirstOrder.Derives.iffElimRight
      hLeftMembershipTransport hLeftMem
  have hLeftCases :
      Γ ⊢ₘ[T] (left ≐ₘ first) ∨ₘ (left ≐ₘ right) :=
    FirstOrder.Derives.iffElimRight
      hRightAtLeft hLeftMemRight
  have hRightAtRight :=
    pair_spec_membership_iff
      first right pair_right right
      hFirst hRight hPairRight hRight hRightSpec
  have hLeftAtRight :=
    pair_spec_membership_iff
      first left pair_left right
      hFirst hLeft hPairLeft hRight hLeftSpec
  have hRightMem :
      Γ ⊢ₘ[T] right ∈ₘ pair_right :=
    FirstOrder.Derives.iffElimLeft
      hRightAtRight
        (FirstOrder.Derives.disjIntroRight
          (FirstOrder.Derives.eq_refl_m right))
  have hRightMembershipTransport :=
    membership_right_iff_of_equality
      right pair_left pair_right
      hRight hPairLeft hPairRight hPairEquality
  have hRightMemLeft :
      Γ ⊢ₘ[T] right ∈ₘ pair_left :=
    FirstOrder.Derives.iffElimLeft
      hRightMembershipTransport hRightMem
  have hRightCases :
      Γ ⊢ₘ[T] (right ≐ₘ first) ∨ₘ (right ≐ₘ left) :=
    FirstOrder.Derives.iffElimRight
      hLeftAtRight hRightMemLeft
  have hRightLeftSymm :
      Γ ⊢ₘ[T] (right ≐ₘ left) ⟶ₘ (left ≐ₘ right) :=
    Metatheory.Derives.equality_symm_imp
  have hRightFirstSymm :
      Γ ⊢ₘ[T] (right ≐ₘ first) ⟶ₘ (first ≐ₘ right) :=
    Metatheory.Derives.equality_symm_imp
  have hTrans :
      Γ ⊢ₘ[T] (left ≐ₘ first) ⟶ₘ ((first ≐ₘ right) ⟶ₘ (left ≐ₘ right)) :=
    Metatheory.Derives.equality_trans_imp
  derive_prop
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
