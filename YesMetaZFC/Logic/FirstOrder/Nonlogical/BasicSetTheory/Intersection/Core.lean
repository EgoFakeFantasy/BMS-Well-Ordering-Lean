import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Pairing
/-!
# 非空族交集与二元交
一元交的核心规格直接表达“属于族中每个成员”。存在性仍从一个具体分离实例
推出：先由非空性取得族中成员，再在该成员上按公共成员条件分离。文献中选择
承载集合的机械步骤只保留为构造层接口，不进入交集项的长期定义。
一元交函数符号只在非空族上由描述符公理刻画。二元交随后定义为无序对的一元交，
并导出通常的成员合取规格。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-- `candidate` 正好由 `family` 中每个集合的公共元素组成。 -/
def intersection_spec (family candidate : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ candidate) ↔ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ family) ⟶ₘ (bₛ#1 ∈ₘ bₛ#0))
/-- 对固定非空族断言其交集候选存在。 -/
def intersection_exists (family : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ family) ⟶ₘ (bₛ#1 ∈ₘ bₛ#0))
/--
从 `source` 分离 `family` 的公共元素所得的候选规格。
`source ∈ family` 时，这一规格与 `intersection_spec family candidate` 等价。
-/
def intersection_separation_spec (family source candidate : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ candidate) ↔ₘ ((bₛ#0 ∈ₘ source) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ family) ⟶ₘ (bₛ#1 ∈ₘ bₛ#0)))
/-- 对固定族与承载集合断言上述分离结果存在。 -/
def intersection_separation_exists (family source : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ((bₛ#0 ∈ₘ source) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ family) ⟶ₘ (bₛ#1 ∈ₘ bₛ#0)))
/-- 交集构造实际消费的闭分离公理实例。 -/
def intersection_separation_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      intersection_separation_exists (x#0) (x#1)
/--
交集存在性所需的基础理论。
它组合子集定义、空集描述符和交集公共成员谓词的一个闭分离实例。
-/
def intersection_base_theory : SetTheory :=
  Theory.insert
    intersection_separation_axiom (Theory.union subset_theory empty_set_symbol_theory)
/-- 一元交函数符号的开放定义实例。 -/
def intersection_definition_instance (family candidate : SetTerm) :
    SetFormula :=
  set_nonempty_condition family ⟶ₘ ((candidate ≐ₘ ⋂ₘ family) ↔ₘ
      intersection_spec family candidate)
/-- 一元交函数符号的定义公理。 -/
def intersection_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      intersection_definition_instance (x#0) (x#1)
/-- 在交集存在基础上加入一元交函数符号。 -/
def intersection_operator_theory : SetTheory :=
  Theory.insert
    intersection_definition_axiom
    intersection_base_theory
/-- `candidate` 正好由同时属于 `left` 与 `right` 的元素组成。 -/
def binary_intersection_spec (left right candidate : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ candidate) ↔ₘ ((bₛ#0 ∈ₘ left) ∧ₘ (bₛ#0 ∈ₘ right))
/-- `element` 属于 `pair` 中的每个成员。 -/
def pair_common_member_condition (pair element : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ pair) ⟶ₘ (element ∈ₘ bₛ#0)
/-- 文献中的二元交描述：先取无序对，再取该非空族的一元交。 -/
def binary_intersection_descriptor (left right candidate : SetTerm) :
    SetFormula :=
  candidate ≐ₘ ⋂ₘ {left, right}ₘ
/-- 配对与一元交描述符公理的合并理论。 -/
def binary_intersection_base_theory : SetTheory :=
  Theory.union
    pairing_operator_theory
    intersection_operator_theory
/-- 二元交函数符号的开放定义实例。 -/
def binary_intersection_definition_instance (left right : SetTerm) :
    SetFormula := (left ∩ₘ right) ≐ₘ (⋂ₘ {left, right}ₘ)
/-- 二元交函数符号的定义公理。 -/
def binary_intersection_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      binary_intersection_definition_instance (x#0) (x#1)
/-- 在配对与一元交描述符理论上加入二元交函数符号。 -/
def binary_intersection_operator_theory : SetTheory :=
  Theory.insert
    binary_intersection_definition_axiom
    binary_intersection_base_theory
/-- 一元交项保持 proof-carrying 项边界。 -/
theorem intersection_term_admissible (family : SetTerm) (hFamily : Term.Admissible family SetSort.set) :
    Term.Admissible (intersection_term family) SetSort.set := by
  simpa using
    set_function_application_admissible
      .intersection [⟨family, by assumption⟩]
      (by rfl) (by rfl)

/-- 一元交项的合法性由参数计算证书组合。 -/
@[term_check]
theorem intersection_term_check
    {family : SetTerm}
    (hFamily : Term.CheckCertificate family SetSort.set) :
    Term.CheckCertificate (intersection_term family) SetSort.set :=
  Term.check_admissible_complete <|
    intersection_term_admissible family hFamily.admissible

/-- 二元交项保持 proof-carrying 项边界。 -/
theorem binary_intersection_term_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible (binary_intersection_term left right)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .binaryIntersection [⟨left, by assumption⟩, ⟨right, by assumption⟩]
      (by rfl) (by rfl)

/-- 二元交项的合法性由两个参数计算证书组合。 -/
@[term_check]
theorem binary_intersection_term_check
    {left right : SetTerm}
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set) :
    Term.CheckCertificate (binary_intersection_term left right) SetSort.set :=
  Term.check_admissible_complete <|
    binary_intersection_term_admissible left right
      hLeft.admissible hRight.admissible

/-- 一元交规格在 admissible 的族项与候选项处仍然 admissible。 -/
theorem intersection_spec_admissible
    {family candidate : SetTerm} (hFamily : Term.Admissible family SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (intersection_spec family candidate) := by
  prove_admissible

/-- 一元交规格的合法性由两个参数计算证书组合。 -/
@[formula_check]
theorem intersection_spec_check
    {family candidate : SetTerm}
    (hFamily : Term.CheckCertificate family SetSort.set)
    (hCandidate : Term.CheckCertificate candidate SetSort.set) :
    Formula.CheckCertificate (intersection_spec family candidate) :=
  Formula.check_admissible_complete <|
    intersection_spec_admissible
      hFamily.admissible hCandidate.admissible

/-- 一元交存在式在 admissible 族项处仍然 admissible。 -/
theorem intersection_exists_admissible
    {family : SetTerm} (hFamily : Term.Admissible family SetSort.set) :
    Formula.Admissible (intersection_exists family) := by
  prove_admissible
/-- 交集分离规格在三个 admissible 集合项处仍然 admissible。 -/
theorem intersection_separation_spec_admissible
    {family source candidate : SetTerm} (hFamily : Term.Admissible family SetSort.set) (hSource : Term.Admissible source SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (intersection_separation_spec
        family source candidate) := by
  prove_admissible
/-- 一元交函数符号的开放定义实例在 admissible 参数处仍然 admissible。 -/
theorem intersection_definition_instance_admissible
    {family candidate : SetTerm} (hFamily : Term.Admissible family SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (intersection_definition_instance
        family candidate) :=
  Formula.Admissible.imp (set_nonempty_condition_admissible hFamily) (Formula.Admissible.iff (Formula.Admissible.equal
        hCandidate (intersection_term_admissible
          family hFamily)) (intersection_spec_admissible
        hFamily hCandidate))
/-- 二元交规格在三个 admissible 集合项处仍然 admissible。 -/
theorem binary_intersection_spec_admissible
    {left right candidate : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (binary_intersection_spec
        left right candidate) := by
  prove_admissible

/-- 二元交规格的合法性由三个参数计算证书组合。 -/
@[formula_check]
theorem binary_intersection_spec_check
    {left right candidate : SetTerm}
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set)
    (hCandidate : Term.CheckCertificate candidate SetSort.set) :
    Formula.CheckCertificate
      (binary_intersection_spec left right candidate) :=
  Formula.check_admissible_complete <|
    binary_intersection_spec_admissible
      hLeft.admissible hRight.admissible hCandidate.admissible

/-- 配对公共成员条件在 admissible 配对项与元素项处仍然 admissible。 -/
theorem pair_common_member_condition_admissible
    {pair element : SetTerm} (hPair : Term.Admissible pair SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    Formula.Admissible (pair_common_member_condition
        pair element) := by
  prove_admissible
/-- 二元交描述符在三个 admissible 集合项处仍然 admissible。 -/
theorem binary_intersection_descriptor_admissible
    {left right candidate : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (binary_intersection_descriptor
        left right candidate) :=
  Formula.Admissible.equal
    hCandidate (intersection_term_admissible (unordered_pair_term left right) (unordered_pair_term_admissible
        left right hLeft hRight))
/-- 二元交函数符号的开放定义实例在 admissible 参数处仍然 admissible。 -/
theorem binary_intersection_definition_instance_admissible
    {left right : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Formula.Admissible (binary_intersection_definition_instance
        left right) :=
  Formula.Admissible.equal (binary_intersection_term_admissible
      left right hLeft hRight) (intersection_term_admissible (unordered_pair_term left right) (unordered_pair_term_admissible
        left right hLeft hRight))
/-- 交集分离公理满足公共 proof-carrying 良构性边界。 -/
theorem intersection_separation_axiom_admissible :
    Formula.Admissible intersection_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 交集基础理论仍然 admissible。 -/
theorem intersection_base_theory_admissible :
    Theory.Admissible intersection_base_theory := by
  intro formula hFormula
  rcases hFormula with rfl | hFormula
  · exact intersection_separation_axiom_admissible
  · rcases hFormula with hFormula | hFormula
    · exact subset_theory_admissible formula hFormula
    · exact empty_set_symbol_theory_admissible
        formula hFormula
/-- 一元交定义公理满足公共良构性边界。 -/
theorem intersection_definition_axiom_admissible :
    Formula.Admissible intersection_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 一元交描述符理论仍然 admissible。 -/
theorem intersection_operator_theory_admissible :
    Theory.Admissible intersection_operator_theory :=
  Theory.admissible_insert
    intersection_definition_axiom_admissible
    intersection_base_theory_admissible
/-- 配对与一元交描述符理论的合并仍然 admissible。 -/
theorem binary_intersection_base_theory_admissible :
    Theory.Admissible binary_intersection_base_theory := by
  intro formula hFormula
  rcases hFormula with hFormula | hFormula
  · exact pairing_operator_theory_admissible
      formula hFormula
  · exact intersection_operator_theory_admissible
      formula hFormula
/-- 二元交定义公理满足公共良构性边界。 -/
theorem binary_intersection_definition_axiom_admissible :
    Formula.Admissible
      binary_intersection_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 二元交描述符理论仍然 admissible。 -/
theorem binary_intersection_operator_theory_admissible :
    Theory.Admissible
      binary_intersection_operator_theory :=
  Theory.admissible_insert
    binary_intersection_definition_axiom_admissible
    binary_intersection_base_theory_admissible
/-- 交集基础理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem intersection_base_theory_sentence
    {formula : SetFormula} (hFormula : intersection_base_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact intersection_base_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · rcases hFormula with hFormula | hFormula
      · change
          formula = subset_definition_axiom ∨
            extensionality_theory formula at hFormula
        rcases hFormula with rfl | hFormula
        · native_decide
        · change formula = extensionality_axiom at hFormula
          subst formula
          native_decide
      · change
          formula = empty_set_definition_axiom ∨ (formula = empty_predicate.separation_axiom ∨
              extensionality_theory formula) at hFormula
        rcases hFormula with rfl | hFormula
        · native_decide
        · rcases hFormula with rfl | hFormula
          · native_decide
          · change formula = extensionality_axiom at hFormula
            subst formula
            native_decide
/-- 一元交描述符理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem intersection_operator_theory_sentence
    {formula : SetFormula} (hFormula : intersection_operator_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact intersection_operator_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · exact (intersection_base_theory_sentence hFormula).2
/-- 二元交基础理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem binary_intersection_base_theory_sentence
    {formula : SetFormula} (hFormula : binary_intersection_base_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with hFormula | hFormula
  · exact pairing_operator_theory_sentence hFormula
  · exact intersection_operator_theory_sentence hFormula
/-- 二元交描述符理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem binary_intersection_operator_theory_sentence
    {formula : SetFormula} (hFormula : binary_intersection_operator_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact binary_intersection_operator_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · exact (binary_intersection_base_theory_sentence
          hFormula).2
/-- 子集理论嵌入交集基础理论。 -/
theorem subset_theory_subset_intersection_base_theory
    {formula : SetFormula} (hFormula : subset_theory formula) :
    intersection_base_theory formula :=
  Or.inr (Or.inl hFormula)
/-- 外延理论嵌入交集基础理论。 -/
theorem extensionality_theory_subset_intersection_base_theory
    {formula : SetFormula} (hFormula : extensionality_theory formula) :
    intersection_base_theory formula :=
  subset_theory_subset_intersection_base_theory (Or.inr hFormula)
/-- 空集描述符理论嵌入交集基础理论。 -/
theorem empty_set_symbol_theory_subset_intersection_base_theory
    {formula : SetFormula} (hFormula : empty_set_symbol_theory formula) :
    intersection_base_theory formula :=
  Or.inr (Or.inr hFormula)
/-- 交集基础理论嵌入一元交描述符理论。 -/
theorem intersection_base_theory_subset_intersection_operator_theory
    {formula : SetFormula} (hFormula : intersection_base_theory formula) :
    intersection_operator_theory formula :=
  Or.inr hFormula
/-- 配对描述符理论嵌入二元交基础理论。 -/
theorem pairing_operator_theory_subset_binary_intersection_base_theory
    {formula : SetFormula} (hFormula : pairing_operator_theory formula) :
    binary_intersection_base_theory formula :=
  Or.inl hFormula
/-- 空集描述符理论嵌入二元交基础理论。 -/
theorem empty_set_symbol_theory_subset_binary_intersection_base_theory
    {formula : SetFormula} (hFormula : empty_set_symbol_theory formula) :
    binary_intersection_base_theory formula :=
  Or.inr <|
    intersection_base_theory_subset_intersection_operator_theory <|
      empty_set_symbol_theory_subset_intersection_base_theory hFormula
/-- 一元交描述符理论嵌入二元交基础理论。 -/
theorem intersection_operator_theory_subset_binary_intersection_base_theory
    {formula : SetFormula} (hFormula : intersection_operator_theory formula) :
    binary_intersection_base_theory formula :=
  Or.inr hFormula
/-- 二元交基础理论嵌入二元交描述符理论。 -/
theorem binary_intersection_base_theory_subset_binary_intersection_operator_theory
    {formula : SetFormula} (hFormula : binary_intersection_base_theory formula) :
    binary_intersection_operator_theory formula :=
  Or.inr hFormula
/-- 一元交描述符理论嵌入二元交描述符理论。 -/
theorem intersection_operator_theory_subset_binary_intersection_operator_theory
    {formula : SetFormula} (hFormula : intersection_operator_theory formula) :
    binary_intersection_operator_theory formula :=
  binary_intersection_base_theory_subset_binary_intersection_operator_theory <|
    intersection_operator_theory_subset_binary_intersection_base_theory
      hFormula
/-- 配对描述符理论嵌入二元交描述符理论。 -/
theorem pairing_operator_theory_subset_binary_intersection_operator_theory
    {formula : SetFormula} (hFormula : pairing_operator_theory formula) :
    binary_intersection_operator_theory formula :=
  binary_intersection_base_theory_subset_binary_intersection_operator_theory <|
    pairing_operator_theory_subset_binary_intersection_base_theory
      hFormula
/-- 外延理论嵌入二元交描述符理论。 -/
theorem extensionality_theory_subset_binary_intersection_operator_theory
    {formula : SetFormula} (hFormula : extensionality_theory formula) :
    binary_intersection_operator_theory formula :=
  intersection_operator_theory_subset_binary_intersection_operator_theory <|
    intersection_base_theory_subset_intersection_operator_theory <|
      extensionality_theory_subset_intersection_base_theory
        hFormula
/-- 闭分离公理可在任意两个 admissible 集合项处实例化。 -/
theorem intersection_separation_exists_derives (family source : SetTerm) (hFamily : Term.Admissible family SetSort.set)
    (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[intersection_base_theory]
      intersection_separation_exists family source := by
  have hAxiom :
      ⊢ₘ[intersection_base_theory]
        intersection_separation_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hFamilyInstance :=
    FirstOrder.Derives.forall_elim
      (term := family) hAxiom
  have hSourceInstance :=
    FirstOrder.Derives.forall_elim
      (term := source) hFamilyInstance
  have hFamilyOpenThree :
      Term.openAt SetSort.set 3 source family = family :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 3 source family hFamily.2
  simpa [intersection_separation_axiom,
    intersection_separation_exists,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hFamilyOpenThree] using
      hSourceInstance
/-- 一元交定义公理可在任意两个 admissible 集合项处实例化。 -/
theorem intersection_definition_instance_derives (family candidate : SetTerm) (hFamily : Term.Admissible family SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[intersection_operator_theory]
      intersection_definition_instance
        family candidate := by
  have hAxiom :
      ⊢ₘ[intersection_operator_theory]
        intersection_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hFamilyInstance :=
    FirstOrder.Derives.forall_elim
      (term := family) hAxiom
  have hCandidateInstance :=
    FirstOrder.Derives.forall_elim
      (term := candidate) hFamilyInstance
  have hFamilyOpenZero :
      Term.openAt SetSort.set 0 candidate family = family :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 candidate family hFamily.2
  have hFamilyOpenOne :
      Term.openAt SetSort.set 1 candidate family = family :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 candidate family hFamily.2
  have hFamilyOpenTwo :
      Term.openAt SetSort.set 2 candidate family = family :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 candidate family hFamily.2
  simpa [intersection_definition_axiom,
    intersection_definition_instance,
    intersection_spec, set_nonempty_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, intersection_term,
    empty_set_term, hFamilyOpenZero,
    hFamilyOpenOne, hFamilyOpenTwo] using
      hCandidateInstance
/-- 二元交定义公理可在任意两个 admissible 集合项处实例化。 -/
theorem binary_intersection_definition_instance_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[binary_intersection_operator_theory]
      binary_intersection_definition_instance
        left right := by
  have hAxiom :
      ⊢ₘ[binary_intersection_operator_theory]
        binary_intersection_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hLeftInstance :=
    FirstOrder.Derives.forall_elim
      (term := left) hAxiom
  have hRightInstance :=
    FirstOrder.Derives.forall_elim
      (term := right) hLeftInstance
  have hLeftOpenZero :
      Term.openAt SetSort.set 0 right left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 right left hLeft.2
  have hLeftOpenOne :
      Term.openAt SetSort.set 1 right left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 right left hLeft.2
  simpa [binary_intersection_definition_axiom,
    binary_intersection_definition_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, intersection_term,
    binary_intersection_term,
    unordered_pair_term, hLeftOpenZero,
    hLeftOpenOne] using hRightInstance
/--
从族中一个成员分离公共元素，与直接交集规格等价。
文献中的非空前提在这里是冗余的：`source ∈ family` 已经给出了所需见证。
-/
theorem intersection_separation_spec_iff_of_mem (family source candidate : SetTerm) (hFamily : Term.Admissible family SetSort.set)
    (hSource : Term.Admissible source SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ (source ∈ₘ family) ⟶ₘ (intersection_separation_spec
            family source candidate ↔ₘ
          intersection_spec family candidate) := by
  let source_mem : SetFormula := source ∈ₘ family
  let separation := intersection_separation_spec
    family source candidate
  let direct := intersection_spec family candidate
  let separation_body : SetFormula := (bₛ#0 ∈ₘ candidate) ↔ₘ ((bₛ#0 ∈ₘ source) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ family) ⟶ₘ (bₛ#1 ∈ₘ bₛ#0)))
  let direct_body : SetFormula := (bₛ#0 ∈ₘ candidate) ↔ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ family) ⟶ₘ (bₛ#1 ∈ₘ bₛ#0))
  let element :=
    FreshVariable.fresh_id SetSort.set
      [source_mem, separation, direct,
        separation_body, direct_body]
  let common_at : SetFormula :=
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ family) ⟶ₘ (x#element ∈ₘ bₛ#0)
  have hElementFreshSourceMem : (SetSort.set, element) freshForₘ
        source_mem := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshSeparation : (SetSort.set, element) freshForₘ
        separation := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshDirect : (SetSort.set, element) freshForₘ
        direct := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshSeparationBody : (SetSort.set, element) freshForₘ
        separation_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshDirectBody : (SetSort.set, element) freshForₘ
        direct_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hFamilyOpenOne :
      Term.openAt SetSort.set 1 (x#element) family =
        family :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 (x#element) family hFamily.2
  have hSourceOpen :
      Term.openAt SetSort.set 0 (x#element) source =
        source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) source hSource.2
  have hCandidateOpen :
      Term.openAt SetSort.set 0 (x#element) candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) candidate hCandidate.2
  have hFamilyOpenSource :
      Term.openAt SetSort.set 0 source family = family :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 source family hFamily.2
  have hSourceMemAdmissible :
      Formula.Admissible source_mem := by
    dsimp [source_mem]
    exact membership_formula_admissible hSource hFamily
  have hSeparationAdmissible :
      Formula.Admissible separation := by
    dsimp [separation]
    exact intersection_separation_spec_admissible
      hFamily hSource hCandidate
  have hDirectAdmissible :
      Formula.Admissible direct := by
    dsimp [direct]
    exact intersection_spec_admissible
      hFamily hCandidate
  have hElementAdmissible :
      Term.Admissible (x#element) SetSort.set :=
    set_variable_admissible element
  have hElementMemCandidateAdmissible :
      Formula.Admissible (x#element ∈ₘ candidate) :=
    membership_formula_admissible
      hElementAdmissible hCandidate
  have hElementMemSourceAdmissible :
      Formula.Admissible (x#element ∈ₘ source) :=
    membership_formula_admissible
      hElementAdmissible hSource
  change ⊢ₘ source_mem ⟶ₘ (separation ↔ₘ direct)
  nd_apply FirstOrder.Derives.impIntro
  apply FirstOrder.Derives.iffIntro
  · have hSeparation :
        separation :: [source_mem] ⊢ₘ
          separation :=
      .assumption (by simp)
    have hSeparationAtRaw :=
      FirstOrder.Derives.forall_elim
        (term := x#element) hSeparation
    have hSeparationAt :
        separation :: [source_mem] ⊢ₘ (x#element ∈ₘ candidate) ↔ₘ ((x#element ∈ₘ source) ∧ₘ
              common_at) := by
      simpa [separation,
        intersection_separation_spec,
        separation_body, common_at,
        Formula.openAt, Formula.next_depth,
        Term.openAt, hFamilyOpenOne,
        hSourceOpen, hCandidateOpen] using
          hSeparationAtRaw
    have hDirectAt :
        separation :: [source_mem] ⊢ₘ (x#element ∈ₘ candidate) ↔ₘ
            common_at := by
      have hCommonAtAdmissible :
          Formula.Admissible common_at :=
        Formula.Admissible.conj_right <|
          Formula.Admissible.iff_right
            hSeparationAt.admissible
      apply FirstOrder.Derives.iffIntro
      · have hSeparationAt' :=
          FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ candidate)
            hSeparationAt
        have hConjunction :=
          FirstOrder.Derives.iffElimRight
            hSeparationAt' (.assumption (by simp)
              )
        exact FirstOrder.Derives.conjElimRight
          hConjunction
      · have hCommon :
            common_at ::
                separation :: [source_mem] ⊢ₘ
              common_at :=
          .assumption (by simp)
        have hCommonAtSourceRaw :=
          FirstOrder.Derives.forall_elim
            (term := source) hCommon
        have hCommonAtSource :
            common_at ::
                separation :: [source_mem] ⊢ₘ (source ∈ₘ family) ⟶ₘ (x#element ∈ₘ source) := by
          simpa [common_at, Formula.openAt,
            Term.openAt, hFamilyOpenSource] using
              hCommonAtSourceRaw
        have hSourceMem :
            common_at ::
                separation :: [source_mem] ⊢ₘ
              source ∈ₘ family :=
          .assumption (by simp [source_mem])
        have hElementSource :=
          FirstOrder.Derives.impElim
            hCommonAtSource hSourceMem
        have hConjunction :=
          FirstOrder.Derives.conjIntro
            hElementSource hCommon
        have hSeparationAt' :=
          FirstOrder.Derives.context_weaken_cons (assumption := common_at)
            hSeparationAt
        exact FirstOrder.Derives.iffElimLeft
          hSeparationAt' hConjunction
    have hDirectAtOpened :
        separation :: [source_mem] ⊢ₘ
          Formula.openAt SetSort.set 0 (x#element) direct_body := by
      simpa [direct_body, common_at,
        Formula.openAt, Formula.next_depth,
        Term.openAt, hFamilyOpenOne,
        hCandidateOpen] using hDirectAt
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := (Theory.empty : SetTheory)) (Γ := [separation, source_mem]) (sort := SetSort.set) (eigen := element) (body :=
          Formula.openAt SetSort.set 0 (x#element) direct_body) (by
          intro formula hFormula
          cases hFormula) (by
          intro formula hFormula
          rcases List.mem_cons.mp hFormula with rfl | hFormula
          · exact hElementFreshSeparation
          · rcases List.mem_singleton.mp hFormula with rfl
            exact hElementFreshSourceMem)
        hDirectAtOpened
    simpa [direct, intersection_spec,
      Formula.closeFreeAt_openAt
        SetSort.set element 0 direct_body
        hElementFreshDirectBody] using hGeneralized
  · have hDirect :
        direct :: [source_mem] ⊢ₘ direct :=
      .assumption (by simp)
    have hDirectAtRaw :=
      FirstOrder.Derives.forall_elim
        (term := x#element) hDirect
    have hDirectAt :
        direct :: [source_mem] ⊢ₘ (x#element ∈ₘ candidate) ↔ₘ
            common_at := by
      simpa [direct, intersection_spec,
        direct_body, common_at,
        Formula.openAt, Formula.next_depth,
        Term.openAt, hFamilyOpenOne,
        hCandidateOpen] using hDirectAtRaw
    have hSeparationAt :
        direct :: [source_mem] ⊢ₘ (x#element ∈ₘ candidate) ↔ₘ ((x#element ∈ₘ source) ∧ₘ
              common_at) := by
      have hCommonAtAdmissible :
          Formula.Admissible common_at :=
        Formula.Admissible.iff_right
          hDirectAt.admissible
      have hConjunctionAdmissible :
          Formula.Admissible ((x#element ∈ₘ source) ∧ₘ
              common_at) :=
        Formula.Admissible.conj
          hElementMemSourceAdmissible
          hCommonAtAdmissible
      apply FirstOrder.Derives.iffIntro
      · have hDirectAt' :=
          FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ candidate)
            hDirectAt
        have hCommon :=
          FirstOrder.Derives.iffElimRight
            hDirectAt' (.assumption (by simp)
              )
        have hCommonAtSourceRaw :=
          FirstOrder.Derives.forall_elim
            (term := source) hCommon
        have hCommonAtSource : (x#element ∈ₘ candidate) ::
                direct :: [source_mem] ⊢ₘ (source ∈ₘ family) ⟶ₘ (x#element ∈ₘ source) := by
          simpa [common_at, Formula.openAt,
            Term.openAt, hFamilyOpenSource] using
              hCommonAtSourceRaw
        have hSourceMem : (x#element ∈ₘ candidate) ::
                direct :: [source_mem] ⊢ₘ
              source ∈ₘ family :=
          .assumption (by simp [source_mem])
        exact FirstOrder.Derives.conjIntro (FirstOrder.Derives.impElim
            hCommonAtSource hSourceMem)
          hCommon
      · have hConjunction : ((x#element ∈ₘ source) ∧ₘ common_at) ::
                direct :: [source_mem] ⊢ₘ (x#element ∈ₘ source) ∧ₘ
                common_at :=
          .assumption (by simp)
        have hCommon :=
          FirstOrder.Derives.conjElimRight
            hConjunction
        have hDirectAt' :=
          FirstOrder.Derives.context_weaken_cons (assumption := (x#element ∈ₘ source) ∧ₘ
                common_at)
            hDirectAt
        exact FirstOrder.Derives.iffElimLeft
          hDirectAt' hCommon
    have hSeparationAtOpened :
        direct :: [source_mem] ⊢ₘ
          Formula.openAt SetSort.set 0 (x#element) separation_body := by
      simpa [separation_body, common_at,
        Formula.openAt, Formula.next_depth,
        Term.openAt, hFamilyOpenOne,
        hSourceOpen, hCandidateOpen] using
          hSeparationAt
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := (Theory.empty : SetTheory)) (Γ := [direct, source_mem]) (sort := SetSort.set) (eigen := element) (body :=
          Formula.openAt SetSort.set 0 (x#element) separation_body) (by
          intro formula hFormula
          cases hFormula) (by
          intro formula hFormula
          rcases List.mem_cons.mp hFormula with rfl | hFormula
          · exact hElementFreshDirect
          · rcases List.mem_singleton.mp hFormula with rfl
            exact hElementFreshSourceMem)
        hSeparationAtOpened
    simpa [separation,
      intersection_separation_spec,
      Formula.closeFreeAt_openAt
        SetSort.set element 0 separation_body
        hElementFreshSeparationBody] using hGeneralized
/-- 交集候选是族中每个成员的子集成员条件。 -/
theorem intersection_spec_implies_subset_condition_of_mem (family candidate member : SetTerm) (hFamily : Term.Admissible family SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) (hMember : Term.Admissible member SetSort.set) :
    ⊢ₘ
      intersection_spec family candidate ⟶ₘ ((member ∈ₘ family) ⟶ₘ
          subset_condition candidate member) := by
  let spec := intersection_spec family candidate
  let member_mem : SetFormula := member ∈ₘ family
  let subset_body : SetFormula := (bₛ#0 ∈ₘ candidate) ⟶ₘ (bₛ#0 ∈ₘ member)
  let element :=
    FreshVariable.fresh_id SetSort.set
      [spec, member_mem, subset_body]
  let common_at : SetFormula :=
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ family) ⟶ₘ (x#element ∈ₘ bₛ#0)
  have hElementFreshSpec : (SetSort.set, element) freshForₘ spec := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshMemberMem : (SetSort.set, element) freshForₘ
        member_mem := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshSubsetBody : (SetSort.set, element) freshForₘ
        subset_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hFamilyOpenOne :
      Term.openAt SetSort.set 1 (x#element) family =
        family :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 (x#element) family hFamily.2
  have hCandidateOpen :
      Term.openAt SetSort.set 0 (x#element) candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) candidate hCandidate.2
  have hMemberOpen :
      Term.openAt SetSort.set 0 (x#element) member =
        member :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) member hMember.2
  have hFamilyOpenMember :
      Term.openAt SetSort.set 0 member family = family :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 member family hFamily.2
  have hSpecAdmissible :
      Formula.Admissible spec := by
    dsimp [spec]
    exact intersection_spec_admissible
      hFamily hCandidate
  have hMemberMemAdmissible :
      Formula.Admissible member_mem := by
    dsimp [member_mem]
    exact membership_formula_admissible
      hMember hFamily
  have hElementAdmissible :
      Term.Admissible (x#element) SetSort.set :=
    set_variable_admissible element
  have hElementMemCandidateAdmissible :
      Formula.Admissible (x#element ∈ₘ candidate) :=
    membership_formula_admissible
      hElementAdmissible hCandidate
  change ⊢ₘ spec ⟶ₘ (member_mem ⟶ₘ (∀ₘ[SetSort.set], subset_body))
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hSpec :
      member_mem :: [spec] ⊢ₘ spec :=
    .assumption (by simp)
  have hSpecAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := x#element) hSpec
  have hSpecAt :
      member_mem :: [spec] ⊢ₘ (x#element ∈ₘ candidate) ↔ₘ
          common_at := by
    simpa [spec, intersection_spec,
      common_at, Formula.openAt,
      Formula.next_depth, Term.openAt,
      hFamilyOpenOne, hCandidateOpen] using
        hSpecAtRaw
  have hSubsetAt :
      member_mem :: [spec] ⊢ₘ (x#element ∈ₘ candidate) ⟶ₘ (x#element ∈ₘ member) := by
    nd_apply FirstOrder.Derives.impIntro
    have hSpecAt' :=
      FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ candidate)
        hSpecAt
    have hCommon :=
      FirstOrder.Derives.iffElimRight
        hSpecAt' (.assumption (by simp)
          )
    have hCommonAtMemberRaw :=
      FirstOrder.Derives.forall_elim
        (term := member) hCommon
    have hCommonAtMember : (x#element ∈ₘ candidate) ::
            member_mem :: [spec] ⊢ₘ
          member_mem ⟶ₘ (x#element ∈ₘ member) := by
      simpa [common_at, member_mem,
        Formula.openAt, Term.openAt,
        hFamilyOpenMember] using
          hCommonAtMemberRaw
    exact FirstOrder.Derives.impElim
      hCommonAtMember (.assumption (by simp)
        )
  have hSubsetAtOpened :
      member_mem :: [spec] ⊢ₘ
        Formula.openAt SetSort.set 0 (x#element) subset_body := by
    simpa [subset_body, Formula.openAt,
      Term.openAt, hCandidateOpen,
      hMemberOpen] using hSubsetAt
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := (Theory.empty : SetTheory)) (Γ := [member_mem, spec]) (sort := SetSort.set) (eigen := element) (body :=
        Formula.openAt SetSort.set 0 (x#element) subset_body) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        rcases List.mem_cons.mp hFormula with rfl | hFormula
        · exact hElementFreshMemberMem
        · rcases List.mem_singleton.mp hFormula with rfl
          exact hElementFreshSpec)
      hSubsetAtOpened
  simpa [subset_condition,
    Formula.closeFreeAt_openAt
      SetSort.set element 0 subset_body
      hElementFreshSubsetBody] using hGeneralized
/--
交集候选是族中每个成员的子集。
这比文献引理 2.1 更强：非空性由 `member ∈ family` 自动蕴含，无需重复列出。
-/
theorem intersection_spec_implies_subset_of_mem (family candidate member : SetTerm) (hFamily : Term.Admissible family SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) (hMember : Term.Admissible member SetSort.set) :
    ⊢ₘ[subset_theory]
      intersection_spec family candidate ⟶ₘ ((member ∈ₘ family) ⟶ₘ (candidate ⊆ₘ member)) := by
  let spec := intersection_spec family candidate
  let member_mem : SetFormula := member ∈ₘ family
  have hSpecAdmissible :
      Formula.Admissible spec := by
    dsimp [spec]
    exact intersection_spec_admissible
      hFamily hCandidate
  have hMemberMemAdmissible :
      Formula.Admissible member_mem := by
    dsimp [member_mem]
    exact membership_formula_admissible
      hMember hFamily
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hConditionImp :
      member_mem :: [spec] ⊢ₘ[subset_theory]
        spec ⟶ₘ (member_mem ⟶ₘ
            subset_condition candidate member) :=
    FirstOrder.Derives.context_weaken_cons (assumption := member_mem) <|
      FirstOrder.Derives.context_weaken_cons (assumption := spec) <|
        FirstOrder.Derives.of_empty <|
          intersection_spec_implies_subset_condition_of_mem
            family candidate member
            hFamily hCandidate hMember
  have hCondition :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
      hConditionImp (.assumption (by simp)
          )) (.assumption (by simp))
  have hDefinition :
      member_mem :: [spec] ⊢ₘ[subset_theory]
        subset_definition_instance
          candidate member :=
    FirstOrder.Derives.context_weaken_cons (assumption := member_mem) <|
      FirstOrder.Derives.context_weaken_cons (assumption := spec) <|
        subset_definition_instance_derives_of_admissible
          candidate member hCandidate hMember
  exact FirstOrder.Derives.iffElimLeft
    hDefinition hCondition
/-- 同一族的两个直接交集候选必相等。 -/
theorem intersection_unique (family left right : SetTerm) (hFamily : Term.Admissible family SetSort.set) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[extensionality_theory]
      intersection_spec family left ⟶ₘ
        intersection_spec family right ⟶ₘ (left ≐ₘ right) := by
  simpa [intersection_spec,
    membership_specification] using
    membership_specification_unique
      left right (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ family) ⟶ₘ (bₛ#1 ∈ₘ bₛ#0))
      hLeft hRight (intersection_spec_admissible
        hFamily hLeft) (intersection_spec_admissible
        hFamily hRight)
/--
从两个不同族成员上分离出的公共元素集合相等。
这就是文献引理 2.3 的现代接口；非空前提已由两个成员假设吸收。
-/
theorem intersection_choice_independent (family first_source second_source left right : SetTerm) (hFamily : Term.Admissible family SetSort.set)
    (hFirstSource : Term.Admissible first_source SetSort.set) (hSecondSource : Term.Admissible second_source SetSort.set)
    (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[extensionality_theory] (first_source ∈ₘ family) ⟶ₘ ((second_source ∈ₘ family) ⟶ₘ (intersection_separation_spec
              family first_source left ⟶ₘ (intersection_separation_spec
                family second_source right ⟶ₘ (left ≐ₘ right)))) := by
  let first_mem : SetFormula :=
    first_source ∈ₘ family
  let second_mem : SetFormula :=
    second_source ∈ₘ family
  let left_separation :=
    intersection_separation_spec
      family first_source left
  let right_separation :=
    intersection_separation_spec
      family second_source right
  let left_direct := intersection_spec family left
  let right_direct := intersection_spec family right
  have hFirstMemAdmissible :
      Formula.Admissible first_mem := by
    dsimp [first_mem]
    exact membership_formula_admissible
      hFirstSource hFamily
  have hSecondMemAdmissible :
      Formula.Admissible second_mem := by
    dsimp [second_mem]
    exact membership_formula_admissible
      hSecondSource hFamily
  have hLeftSeparationAdmissible :
      Formula.Admissible left_separation := by
    dsimp [left_separation]
    exact intersection_separation_spec_admissible
      hFamily hFirstSource hLeft
  have hRightSeparationAdmissible :
      Formula.Admissible right_separation := by
    dsimp [right_separation]
    exact intersection_separation_spec_admissible
      hFamily hSecondSource hRight
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hFirstBridgeImp :
      right_separation :: left_separation ::
          second_mem :: [first_mem]
        ⊢ₘ[extensionality_theory]
          first_mem ⟶ₘ (left_separation ↔ₘ left_direct) :=
    FirstOrder.Derives.context_weaken_cons (assumption := right_separation) <|
      FirstOrder.Derives.context_weaken_cons (assumption := left_separation) <|
        FirstOrder.Derives.context_weaken_cons (assumption := second_mem) <|
          FirstOrder.Derives.context_weaken_cons (assumption := first_mem) <|
            FirstOrder.Derives.of_empty <|
              by
                simpa [first_mem, left_separation,
                  left_direct] using
                  intersection_separation_spec_iff_of_mem
                    family first_source left
                    hFamily hFirstSource hLeft
  have hSecondBridgeImp :
      right_separation :: left_separation ::
          second_mem :: [first_mem]
        ⊢ₘ[extensionality_theory]
          second_mem ⟶ₘ (right_separation ↔ₘ right_direct) :=
    FirstOrder.Derives.context_weaken_cons (assumption := right_separation) <|
      FirstOrder.Derives.context_weaken_cons (assumption := left_separation) <|
        FirstOrder.Derives.context_weaken_cons (assumption := second_mem) <|
          FirstOrder.Derives.context_weaken_cons (assumption := first_mem) <|
            FirstOrder.Derives.of_empty <|
              by
                simpa [second_mem, right_separation,
                  right_direct] using
                  intersection_separation_spec_iff_of_mem
                    family second_source right
                    hFamily hSecondSource hRight
  have hFirstBridge :=
    FirstOrder.Derives.impElim
      hFirstBridgeImp (.assumption (by simp))
  have hSecondBridge :=
    FirstOrder.Derives.impElim
      hSecondBridgeImp (.assumption (by simp))
  have hLeftDirect :
      right_separation :: left_separation ::
          second_mem :: [first_mem]
        ⊢ₘ[extensionality_theory]
          left_direct :=
    FirstOrder.Derives.iffElimRight
      hFirstBridge (.assumption (by simp))
  have hRightDirect :
      right_separation :: left_separation ::
          second_mem :: [first_mem]
        ⊢ₘ[extensionality_theory]
          right_direct :=
    FirstOrder.Derives.iffElimRight
      hSecondBridge (.assumption (by simp))
  have hUnique :
      right_separation :: left_separation ::
          second_mem :: [first_mem]
        ⊢ₘ[extensionality_theory]
          left_direct ⟶ₘ (right_direct ⟶ₘ (left ≐ₘ right)) :=
    FirstOrder.Derives.context_weaken_cons (assumption := right_separation) <|
      FirstOrder.Derives.context_weaken_cons (assumption := left_separation) <|
        FirstOrder.Derives.context_weaken_cons (assumption := second_mem) <|
          FirstOrder.Derives.context_weaken_cons (assumption := first_mem) <|
            by
              simpa [left_direct, right_direct] using
                intersection_unique
                  family left right
                  hFamily hLeft hRight
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
      hUnique hLeftDirect)
    hRightDirect
/-- 同一承载集合上的两个交集分离候选必相等。 -/
theorem intersection_separation_unique_of_mem (family source left right : SetTerm) (hFamily : Term.Admissible family SetSort.set)
    (hSource : Term.Admissible source SetSort.set) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[extensionality_theory] (source ∈ₘ family) ⟶ₘ (intersection_separation_spec
            family source left ⟶ₘ (intersection_separation_spec
              family source right ⟶ₘ (left ≐ₘ right))) := by
  let source_mem : SetFormula := source ∈ₘ family
  let left_separation :=
    intersection_separation_spec family source left
  let right_separation :=
    intersection_separation_spec family source right
  have hSourceMemAdmissible :
      Formula.Admissible source_mem := by
    dsimp [source_mem]
    exact membership_formula_admissible
      hSource hFamily
  have hLeftSeparationAdmissible :
      Formula.Admissible left_separation := by
    dsimp [left_separation]
    exact intersection_separation_spec_admissible
      hFamily hSource hLeft
  have hRightSeparationAdmissible :
      Formula.Admissible right_separation := by
    dsimp [right_separation]
    exact intersection_separation_spec_admissible
      hFamily hSource hRight
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hGeneral :
      right_separation :: left_separation ::
          [source_mem] ⊢ₘ[extensionality_theory]
        source_mem ⟶ₘ (source_mem ⟶ₘ (left_separation ⟶ₘ (right_separation ⟶ₘ (left ≐ₘ right)))) :=
    FirstOrder.Derives.context_weaken_cons (assumption := right_separation) <|
      FirstOrder.Derives.context_weaken_cons (assumption := left_separation) <|
        FirstOrder.Derives.context_weaken_cons (assumption := source_mem) <|
          by
            simpa [source_mem, left_separation,
              right_separation] using
              intersection_choice_independent
                family source source left right
                hFamily hSource hSource hLeft hRight
  have hStepOne :=
    FirstOrder.Derives.impElim
      hGeneral (.assumption (by simp))
  have hStepTwo :=
    FirstOrder.Derives.impElim
      hStepOne (.assumption (by simp))
  have hStepThree :=
    FirstOrder.Derives.impElim
      hStepTwo (.assumption (by simp))
  exact FirstOrder.Derives.impElim
    hStepThree (.assumption (by simp [right_separation]))
/-- 已选中的族成员可以直接消费交集分离存在公理。 -/
theorem intersection_separation_exists_of_mem (family source : SetTerm) (hFamily : Term.Admissible family SetSort.set)
    (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[intersection_base_theory] (source ∈ₘ family) ⟶ₘ
        intersection_separation_exists
          family source := by
  nd_apply FirstOrder.Derives.impIntro
  exact FirstOrder.Derives.context_weaken_cons (intersection_separation_exists_derives
      family source hFamily hSource)
/-- 一个直接交集候选立即见证交集存在。 -/
theorem intersection_spec_implies_exists (family candidate : SetTerm) (hFamily : Term.Admissible family SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ
      intersection_spec family candidate ⟶ₘ
        intersection_exists family := by
  nd_apply FirstOrder.Derives.impIntro
  unfold intersection_exists
  nd_apply FirstOrder.Derives.exists_intro (term := candidate)
  have hFamilyOpenTwo :
      Term.openAt SetSort.set 2 candidate family = family :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 candidate family hFamily.2
  simpa [intersection_spec, Formula.openAt,
    Formula.next_depth, Term.openAt,
    hFamilyOpenTwo] using (show
        [intersection_spec family candidate] ⊢ₘ
          intersection_spec family candidate from
        .assumption (by simp))
/-- 非空族的交集存在，由选中成员上的分离实例构造。 -/
theorem intersection_exists_derives (family : SetTerm) (hFamily : Term.Admissible family SetSort.set) :
    ⊢ₘ[intersection_base_theory]
      set_nonempty_condition family ⟶ₘ
        intersection_exists family := by
  let nonempty := set_nonempty_condition family
  let conclusion := intersection_exists family
  let member_bound_body : SetFormula :=
    bₛ#0 ∈ₘ family
  let member :=
    FreshVariable.fresh_id SetSort.set
      [nonempty, conclusion, member_bound_body]
  let member_point :=
    Formula.openAt SetSort.set 0 (x#member) member_bound_body
  have hMemberFreshNonempty : (SetSort.set, member) freshForₘ
        nonempty := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hMemberFreshConclusion : (SetSort.set, member) freshForₘ
        conclusion := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hMemberFreshBoundBody : (SetSort.set, member) freshForₘ
        member_bound_body := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hFamilyOpenMember :
      Term.openAt SetSort.set 0 (x#member) family =
        family :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member) family hFamily.2
  have hNonemptyAdmissible :
      Formula.Admissible nonempty := by
    dsimp [nonempty]
    exact set_nonempty_condition_admissible
      hFamily
  have hMemberPointAdmissible :
      Formula.Admissible member_point := by
    have hOpened :=
      Formula.Admissible.exists_openAt (σ := signature) (body := bₛ#0 ∈ₘ family) (term := x#member)
        SetSort.set (by
          simpa [set_has_member] using
            set_has_member_admissible hFamily) (set_variable_admissible member)
    simpa [set_has_member, member_point,
      member_bound_body, Formula.openAt,
      Term.openAt, hFamilyOpenMember] using
        hOpened
  change
    ⊢ₘ[intersection_base_theory]
      nonempty ⟶ₘ conclusion
  nd_apply FirstOrder.Derives.impIntro
  have hHasMemberImp :
      [nonempty] ⊢ₘ[intersection_base_theory]
        nonempty ⟶ₘ set_has_member family :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          empty_set_symbol_theory_subset_intersection_base_theory
            hFormula) (by
          simpa [nonempty] using
            set_nonempty_implies_has_member
              family hFamily)
  have hHasMember :=
    FirstOrder.Derives.impElim
      hHasMemberImp (.assumption (by simp))
  have hHasMemberClosed :
      [nonempty] ⊢ₘ[intersection_base_theory] (∃ₘ[SetSort.set, member],
          member_point) := by
    simpa [set_has_member,
      member_point, member_bound_body,
      Formula.closeFreeAt_openAt
        SetSort.set member 0 member_bound_body
        hMemberFreshBoundBody] using hHasMember
  have hMemberCase :
      member_point :: [nonempty]
        ⊢ₘ[intersection_base_theory]
          conclusion := by
    have hMemberMem :
        member_point :: [nonempty]
          ⊢ₘ[intersection_base_theory]
            x#member ∈ₘ family := by
      simpa [member_point, member_bound_body,
        Formula.openAt, Term.openAt,
        hFamilyOpenMember] using (show
          member_point :: [nonempty]
            ⊢ₘ[intersection_base_theory]
          member_point from
          .assumption (by simp))
    let separation_bound_body : SetFormula :=
      ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ((bₛ#0 ∈ₘ x#member) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ family) ⟶ₘ (bₛ#1 ∈ₘ bₛ#0)))
    let candidate :=
      FreshVariable.fresh_id SetSort.set
        [separation_bound_body, member_point,
          nonempty, conclusion]
    let candidate_point :=
      Formula.openAt SetSort.set 0 (x#candidate) separation_bound_body
    have hCandidateFreshSeparationBody : (SetSort.set, candidate) freshForₘ
          separation_bound_body := by
      dsimp [candidate]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    have hCandidateFreshMemberPoint : (SetSort.set, candidate) freshForₘ
          member_point := by
      dsimp [candidate]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    have hCandidateFreshNonempty : (SetSort.set, candidate) freshForₘ
          nonempty := by
      dsimp [candidate]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    have hCandidateFreshConclusion : (SetSort.set, candidate) freshForₘ
          conclusion := by
      dsimp [candidate]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    have hFamilyOpenCandidateTwo :
        Term.openAt SetSort.set 2 (x#candidate) family =
          family :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 2 (x#candidate) family hFamily.2
    have hSeparationExists :
        member_point :: [nonempty]
          ⊢ₘ[intersection_base_theory]
            intersection_separation_exists
              family (x#member) :=
      FirstOrder.Derives.context_weaken_cons (assumption := member_point) <|
        FirstOrder.Derives.context_weaken_cons (assumption := nonempty) <|
          intersection_separation_exists_derives
            family (x#member)
            hFamily (set_variable_admissible member)
    have hCandidatePointAdmissible :
        Formula.Admissible candidate_point := by
      have hOpened :=
        Formula.Admissible.exists_openAt (σ := signature) (body := separation_bound_body) (term := x#candidate)
          SetSort.set (by
            simpa [intersection_separation_exists,
              separation_bound_body] using
              hSeparationExists.admissible) (set_variable_admissible candidate)
      simpa [intersection_separation_exists,
        candidate_point, separation_bound_body,
        Formula.openAt, Formula.next_depth,
        Term.openAt, hFamilyOpenCandidateTwo] using
          hOpened
    have hSeparationExistsClosed :
        member_point :: [nonempty]
          ⊢ₘ[intersection_base_theory] (∃ₘ[SetSort.set, candidate],
              candidate_point) := by
      simpa [intersection_separation_exists,
        separation_bound_body, candidate_point,
        Formula.closeFreeAt_openAt
          SetSort.set candidate 0
          separation_bound_body
          hCandidateFreshSeparationBody] using
            hSeparationExists
    have hCandidateCase :
        candidate_point :: member_point :: [nonempty]
          ⊢ₘ[intersection_base_theory]
            conclusion := by
      have hSeparationSpec :
          candidate_point :: member_point :: [nonempty]
            ⊢ₘ[intersection_base_theory]
              intersection_separation_spec
                family (x#member) (x#candidate) := by
        simpa [candidate_point,
          separation_bound_body,
          intersection_separation_spec,
          Formula.openAt, Formula.next_depth,
          Term.openAt,
          hFamilyOpenCandidateTwo] using (show
            candidate_point :: member_point :: [nonempty]
              ⊢ₘ[intersection_base_theory]
                candidate_point from
            .assumption (by simp))
      have hBridgeImp :
          candidate_point :: member_point :: [nonempty]
            ⊢ₘ[intersection_base_theory] (x#member ∈ₘ family) ⟶ₘ (intersection_separation_spec
                    family (x#member) (x#candidate) ↔ₘ
                  intersection_spec
                    family (x#candidate)) :=
        FirstOrder.Derives.context_weaken_cons (assumption := candidate_point) <|
          FirstOrder.Derives.context_weaken_cons (assumption := member_point) <|
            FirstOrder.Derives.context_weaken_cons (assumption := nonempty) <|
              FirstOrder.Derives.of_empty <|
                intersection_separation_spec_iff_of_mem
                  family (x#member) (x#candidate)
                  hFamily (set_variable_admissible member) (set_variable_admissible candidate)
      have hMemberMem' :
          candidate_point :: member_point :: [nonempty]
            ⊢ₘ[intersection_base_theory]
              x#member ∈ₘ family :=
        FirstOrder.Derives.context_weaken_cons (assumption := candidate_point)
          hMemberMem
      have hBridge :=
        FirstOrder.Derives.impElim
          hBridgeImp hMemberMem'
      have hDirect :=
        FirstOrder.Derives.iffElimRight
          hBridge hSeparationSpec
      have hExistsImp :
          candidate_point :: member_point :: [nonempty]
            ⊢ₘ[intersection_base_theory]
              intersection_spec
                  family (x#candidate) ⟶ₘ
                conclusion :=
        FirstOrder.Derives.context_weaken_cons (assumption := candidate_point) <|
          FirstOrder.Derives.context_weaken_cons (assumption := member_point) <|
            FirstOrder.Derives.context_weaken_cons (assumption := nonempty) <|
              FirstOrder.Derives.of_empty <|
                by
                  simpa [conclusion] using
                    intersection_spec_implies_exists
                      family (x#candidate)
                      hFamily (set_variable_admissible candidate)
      exact FirstOrder.Derives.impElim
        hExistsImp hDirect
    exact FirstOrder.Derives.exists_elim (by
        intro formula hFormula
        have hSentence :=
          intersection_base_theory_sentence hFormula
        rw [hSentence.2]
        simp) (by
        intro formula hFormula
        rcases List.mem_cons.mp hFormula with rfl | hFormula
        · exact hCandidateFreshMemberPoint
        · rcases List.mem_singleton.mp hFormula with rfl
          exact hCandidateFreshNonempty)
      hCandidateFreshConclusion
      hSeparationExistsClosed hCandidateCase
  exact FirstOrder.Derives.exists_elim (by
      intro formula hFormula
      have hSentence :=
        intersection_base_theory_sentence hFormula
      rw [hSentence.2]
      simp) (by
      intro formula hFormula
      rcases List.mem_singleton.mp hFormula with rfl
      exact hMemberFreshNonempty)
    hMemberFreshConclusion
    hHasMemberClosed hMemberCase
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
