import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Pairing
/-!
# 并集与二元并
一元并集存在公理保持在只含外延性的最小理论上；并集函数符号随后作为描述符扩张
加入。二元并函数符号则建立在配对与一元并两个描述符理论的合并之上，其定义公理
直接表达文献中的“先取无序对，再取一元并集”。
核心成员规格使用现代的析取写法，文献中的机械变量编号只保留在闭公理的实例化
边界，不传播到后续定理接口。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-- `union` 恰好由 `source` 的所有元素的元素组成。 -/
def union_spec (source union : SetTerm) : SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ union) ↔ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ source) ∧ₘ (bₛ#1 ∈ₘ bₛ#0))
/-- 对固定集合断言其并集存在。 -/
def union_exists (source : SetTerm) : SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ source) ∧ₘ (bₛ#1 ∈ₘ bₛ#0))
/-- 并集存在公理。 -/
def union_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    union_exists (x#0)
/-- 只在外延理论上加入并集存在公理。 -/
def union_theory : SetTheory :=
  Theory.insert union_axiom extensionality_theory
/-- 一元并集函数符号的开放定义实例。 -/
def union_definition_instance (source : SetTerm) : SetFormula :=
  union_spec source (⋃ₘ source)
/-- 一元并集函数符号的定义公理。 -/
def union_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    union_definition_instance (x#0)
/-- 在并集存在理论上加入一元并集函数符号的描述符扩张。 -/
def union_operator_theory : SetTheory :=
  Theory.insert union_definition_axiom union_theory
/-- `candidate` 是 `left` 与 `right` 的二元并。 -/
def binary_union_spec (left right candidate : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ candidate) ↔ₘ ((bₛ#0 ∈ₘ left) ∨ₘ (bₛ#0 ∈ₘ right))
/-- 文献中的二元并描述：先取无序对，再对该无序对取一元并集。 -/
def binary_union_descriptor (left right candidate : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set], (bₛ#0 ≐ₘ {left, right}ₘ) ∧ₘ (candidate ≐ₘ ⋃ₘ bₛ#0)
/-- 配对与一元并描述符公理的合并理论。 -/
def binary_union_base_theory : SetTheory :=
  Theory.union pairing_operator_theory union_operator_theory
/-- 二元并函数符号的开放定义实例。 -/
def binary_union_definition_instance (left right : SetTerm) :
    SetFormula := (left ∪ₘ right) ≐ₘ (⋃ₘ {left, right}ₘ)
/-- 二元并函数符号的定义公理。 -/
def binary_union_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      binary_union_definition_instance (x#0) (x#1)
/-- 在配对与一元并描述符理论上加入二元并函数符号。 -/
def binary_union_operator_theory : SetTheory :=
  Theory.insert
    binary_union_definition_axiom
    binary_union_base_theory
/-- 一元并集项保持 proof-carrying 项边界。 -/
theorem union_term_admissible (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    Term.Admissible (union_term source) SetSort.set := by
  simpa using
    set_function_application_admissible
      .union [⟨source, by assumption⟩]
      (by rfl) (by rfl)

/-- 一元并项的合法性由参数计算证书组合。 -/
@[term_check]
theorem union_term_check
    {source : SetTerm}
    (hSource : Term.CheckCertificate source SetSort.set) :
    Term.CheckCertificate (union_term source) SetSort.set :=
  Term.check_admissible_complete <|
    union_term_admissible source hSource.admissible

/-- 二元并项保持 proof-carrying 项边界。 -/
theorem binary_union_term_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible (binary_union_term left right) SetSort.set := by
  simpa using
    set_function_application_admissible
      .binaryUnion [⟨left, by assumption⟩, ⟨right, by assumption⟩]
      (by rfl) (by rfl)

/-- 二元并项的合法性由两个参数计算证书组合。 -/
@[term_check]
theorem binary_union_term_check
    {left right : SetTerm}
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set) :
    Term.CheckCertificate (binary_union_term left right) SetSort.set :=
  Term.check_admissible_complete <|
    binary_union_term_admissible left right
      hLeft.admissible hRight.admissible

/-- 一元并集规格在 admissible 的源项与候选项处仍然 admissible。 -/
theorem union_spec_admissible
    {source union : SetTerm} (hSource : Term.Admissible source SetSort.set) (hUnion : Term.Admissible union SetSort.set) :
    Formula.Admissible (union_spec source union) := by
  prove_admissible

/-- 一元并规格的合法性由两个参数计算证书组合。 -/
@[formula_check]
theorem union_spec_check
    {source union : SetTerm}
    (hSource : Term.CheckCertificate source SetSort.set)
    (hUnion : Term.CheckCertificate union SetSort.set) :
    Formula.CheckCertificate (union_spec source union) :=
  Formula.check_admissible_complete <|
    union_spec_admissible hSource.admissible hUnion.admissible

/-- 一元并集函数符号的开放定义实例在 admissible 源项处仍然 admissible。 -/
theorem union_definition_instance_admissible
    {source : SetTerm} (hSource : Term.Admissible source SetSort.set) :
    Formula.Admissible (union_definition_instance source) :=
  union_spec_admissible hSource (union_term_admissible source hSource)
/-- 二元并规格在三个 admissible 集合项处仍然 admissible。 -/
theorem binary_union_spec_admissible
    {left right candidate : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (binary_union_spec left right candidate) := by
  prove_admissible

/-- 二元并规格的合法性由三个参数计算证书组合。 -/
@[formula_check]
theorem binary_union_spec_check
    {left right candidate : SetTerm}
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set)
    (hCandidate : Term.CheckCertificate candidate SetSort.set) :
    Formula.CheckCertificate (binary_union_spec left right candidate) :=
  Formula.check_admissible_complete <|
    binary_union_spec_admissible
      hLeft.admissible hRight.admissible hCandidate.admissible

/-- 文献二元并描述符在三个 admissible 集合项处仍然 admissible。 -/
theorem binary_union_descriptor_admissible
    {left right candidate : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (binary_union_descriptor
        left right candidate) := by
  prove_admissible
/-- 二元并函数符号的开放定义实例在 admissible 参数处仍然 admissible。 -/
theorem binary_union_definition_instance_admissible
    {left right : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Formula.Admissible (binary_union_definition_instance
        left right) :=
  Formula.Admissible.equal (binary_union_term_admissible
      left right hLeft hRight) (union_term_admissible (unordered_pair_term left right) (unordered_pair_term_admissible
        left right hLeft hRight))
/-- 并集存在公理满足公共 proof-carrying 良构性边界。 -/
theorem union_axiom_admissible :
    Formula.Admissible union_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 并集存在理论仍然 admissible。 -/
theorem union_theory_admissible :
    Theory.Admissible union_theory :=
  Theory.admissible_insert
    union_axiom_admissible
    extensionality_theory_admissible
/-- 一元并集函数符号定义公理满足公共良构性边界。 -/
theorem union_definition_axiom_admissible :
    Formula.Admissible union_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 一元并集描述符理论仍然 admissible。 -/
theorem union_operator_theory_admissible :
    Theory.Admissible union_operator_theory :=
  Theory.admissible_insert
    union_definition_axiom_admissible
    union_theory_admissible
/-- 配对与一元并描述符理论的合并仍然 admissible。 -/
theorem binary_union_base_theory_admissible :
    Theory.Admissible binary_union_base_theory := by
  intro formula hFormula
  rcases hFormula with hFormula | hFormula
  · exact pairing_operator_theory_admissible
      formula hFormula
  · exact union_operator_theory_admissible
      formula hFormula
/-- 二元并函数符号定义公理满足公共良构性边界。 -/
theorem binary_union_definition_axiom_admissible :
    Formula.Admissible binary_union_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 二元并描述符理论仍然 admissible。 -/
theorem binary_union_operator_theory_admissible :
    Theory.Admissible binary_union_operator_theory :=
  Theory.admissible_insert
    binary_union_definition_axiom_admissible
    binary_union_base_theory_admissible
/-- 一元并集描述符理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem union_operator_theory_sentence
    {formula : SetFormula} (hFormula : union_operator_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact union_operator_theory_admissible
      formula hFormula
  · change
      formula = union_definition_axiom ∨ (formula = union_axiom ∨
          extensionality_theory formula) at hFormula
    rcases hFormula with rfl | hFormula
    · native_decide
    · rcases hFormula with rfl | hFormula
      · native_decide
      · change formula = extensionality_axiom at hFormula
        subst formula
        native_decide
/-- 二元并描述符理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem binary_union_operator_theory_sentence
    {formula : SetFormula} (hFormula : binary_union_operator_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact binary_union_operator_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · rcases hFormula with hFormula | hFormula
      · exact (pairing_operator_theory_sentence hFormula).2
      · exact (union_operator_theory_sentence hFormula).2
/-- 配对描述符理论嵌入二元并描述符理论。 -/
theorem pairing_operator_theory_subset_binary_union_operator_theory
    {formula : SetFormula} (hFormula : pairing_operator_theory formula) :
    binary_union_operator_theory formula :=
  Or.inr (Or.inl hFormula)
/-- 一元并描述符理论嵌入二元并描述符理论。 -/
theorem union_operator_theory_subset_binary_union_operator_theory
    {formula : SetFormula} (hFormula : union_operator_theory formula) :
    binary_union_operator_theory formula :=
  Or.inr (Or.inr hFormula)
/-- 并集存在公理可在任意 admissible 集合项处实例化。 -/
theorem union_exists_derives (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[union_theory]
      union_exists source := by
  have hAxiom :
      ⊢ₘ[union_theory] union_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hInstance :=
    FirstOrder.Derives.forall_elim
      (term := source) hAxiom
  simpa [union_axiom, union_exists,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable] using hInstance
/-- 一元并集函数符号定义公理可在任意 admissible 集合项处实例化。 -/
theorem union_definition_instance_derives (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[union_operator_theory]
      union_definition_instance source := by
  have hAxiom :
      ⊢ₘ[union_operator_theory]
        union_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hInstance :=
    FirstOrder.Derives.forall_elim
      (term := source) hAxiom
  simpa [union_definition_axiom,
    union_definition_instance, union_spec,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, union_term] using hInstance
/-- 定义扩张中的一元并集项满足并集规格。 -/
theorem union_term_spec_derives (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[union_operator_theory]
      union_spec source (⋃ₘ source) := by
  simpa [union_definition_instance] using
    union_definition_instance_derives source hSource
/-- 同一集合的两个并集候选必相等。 -/
theorem union_unique (source left right : SetTerm) (hSource : Term.Admissible source SetSort.set) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[extensionality_theory]
      union_spec source left ⟶ₘ
        union_spec source right ⟶ₘ (left ≐ₘ right) := by
  simpa [union_spec,
    membership_specification] using
    membership_specification_unique
      left right (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ source) ∧ₘ (bₛ#1 ∈ₘ bₛ#0))
      hLeft hRight (union_spec_admissible
        hSource hLeft) (union_spec_admissible
        hSource hRight)
/-- 一个集合项等于 `source` 的并集，当且仅当它满足并集规格。 -/
theorem union_eq_iff_spec (source candidate : SetTerm) (hSource : Term.Admissible source SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[union_operator_theory] (candidate ≐ₘ ⋃ₘ source) ↔ₘ
        union_spec source candidate := by
  let union := union_term source
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [Formula.equal source source]
  have hUnion :
      Term.Admissible union SetSort.set :=
    union_term_admissible source hSource
  have hParameterFreshSource : (SetSort.set, parameter) ∉
        Term.freeSupport source := by
    dsimp [parameter]
    exact FreshVariable.fresh_term_not_mem_m
      SetSort.set source
  have hSourceFixedCandidate :
      Term.substituteFree SetSort.set
          parameter candidate source =
        source :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter candidate source
      hParameterFreshSource
  have hSourceFixedUnion :
      Term.substituteFree SetSort.set
          parameter union source =
        source :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter union source
      hParameterFreshSource
  have hCandidateUnionEqualityAdmissible :
      Formula.Admissible (candidate ≐ₘ union) :=
    Formula.Admissible.equal
      hCandidate hUnion
  have hCandidateSpecAdmissible :
      Formula.Admissible (union_spec source candidate) :=
    union_spec_admissible
      hSource hCandidate
  change
    ⊢ₘ[union_operator_theory] (candidate ≐ₘ union) ↔ₘ
        union_spec source candidate
  apply FirstOrder.Derives.iffIntro
  · have hEquality :
        [candidate ≐ₘ union] ⊢ₘ[union_operator_theory]
          candidate ≐ₘ union :=
      .assumption (by simp)
    have hCongruence :=
      Metatheory.Derives.equality_iff_of_equality (T := union_operator_theory) (Γ := [candidate ≐ₘ union]) (sort := SetSort.set) (eigen := parameter)
        (left := candidate) (right := union) (body := union_spec source (x#parameter))
        hEquality
    have hCongruenceNormalized :
        [candidate ≐ₘ union] ⊢ₘ[union_operator_theory]
          union_spec source candidate ↔ₘ
            union_spec source union := by
      simpa [union_spec,
        Formula.substituteFree, Term.substituteFree,
        hSourceFixedCandidate, hSourceFixedUnion,
        set_variable] using hCongruence
    have hUnionSpec :
        [candidate ≐ₘ union] ⊢ₘ[union_operator_theory]
          union_spec source union :=
      FirstOrder.Derives.context_weaken_cons (by
          simpa [union] using
            union_term_spec_derives source hSource)
    exact FirstOrder.Derives.iffElimLeft
      hCongruenceNormalized hUnionSpec
  · have hCandidateSpec :
        [union_spec source candidate] ⊢ₘ[union_operator_theory]
          union_spec source candidate :=
      .assumption (by simp)
    have hUnionSpec :
        [union_spec source candidate] ⊢ₘ[union_operator_theory]
          union_spec source union :=
      FirstOrder.Derives.context_weaken_cons (by
          simpa [union] using
            union_term_spec_derives source hSource)
    have hUnique :
        [union_spec source candidate] ⊢ₘ[union_operator_theory]
          union_spec source candidate ⟶ₘ
            union_spec source union ⟶ₘ (candidate ≐ₘ union) :=
      FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.theory_weaken (by
            intro formula hFormula
            change
              formula = union_definition_axiom ∨ (formula = union_axiom ∨
                  extensionality_theory formula)
            exact Or.inr (Or.inr hFormula)) (union_unique
            source candidate union
            hSource hCandidate hUnion)
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
        hUnique hCandidateSpec)
      hUnionSpec
/-- 已证明的集合等式可直接提升为一元并集函数项等式。 -/
theorem union_term_congr_of_equality
    {T : SetTheory} {Γ : Context signature} (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] (⋃ₘ left) ≐ₘ (⋃ₘ right) := by
  exact Metatheory.Derives.unary_term_constructor_congr_of_equality
    union_term
    union_term_admissible
    (by intros; simp [Term.substituteFree])
    left right hLeft hRight hEquality
/-- 一元并集函数项保持自由集合变量的等式。 -/
theorem union_term_congr (left right : FreeVarId) :
    ⊢ₘ (x#left ≐ₘ x#right) ⟶ₘ ((⋃ₘ x#left) ≐ₘ (⋃ₘ x#right)) := by
  nd_apply FirstOrder.Derives.impIntro
  exact union_term_congr_of_equality
    (x#left) (x#right)
    (set_variable_admissible left)
    (set_variable_admissible right)
    (.assumption (by simp))
/-- 等价的源集合可运输同一个候选对象的一元并集等式。 -/
theorem union_eq_transport (left right candidate : FreeVarId) :
    ⊢ₘ (x#left ≐ₘ x#right) ⟶ₘ ((x#candidate ≐ₘ ⋃ₘ x#left) ⟶ₘ (x#candidate ≐ₘ ⋃ₘ x#right)) := by
  let left_union := union_term (x#left)
  let right_union := union_term (x#right)
  have hLeftUnion :
      Term.Admissible left_union SetSort.set :=
    union_term_admissible (x#left) (set_variable_admissible left)
  have hRightUnion :
      Term.Admissible right_union SetSort.set :=
    union_term_admissible (x#right) (set_variable_admissible right)
  have hLeftAdmissible :
      Term.Admissible (x#left) SetSort.set :=
    set_variable_admissible left
  have hRightAdmissible :
      Term.Admissible (x#right) SetSort.set :=
    set_variable_admissible right
  have hCandidateAdmissible :
      Term.Admissible (x#candidate) SetSort.set :=
    set_variable_admissible candidate
  change
    ⊢ₘ (x#left ≐ₘ x#right) ⟶ₘ ((x#candidate ≐ₘ left_union) ⟶ₘ (x#candidate ≐ₘ right_union))
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hSourceEquality :
      [x#candidate ≐ₘ left_union,
          x#left ≐ₘ x#right] ⊢ₘ
        x#left ≐ₘ x#right :=
    .assumption (by simp)
  have hCandidateEquality :
      [x#candidate ≐ₘ left_union,
          x#left ≐ₘ x#right] ⊢ₘ
        x#candidate ≐ₘ left_union :=
    .assumption (by simp)
  have hUnionEquality :
      [x#candidate ≐ₘ left_union,
          x#left ≐ₘ x#right] ⊢ₘ
        left_union ≐ₘ right_union := by
    simpa [left_union, right_union] using
      union_term_congr_of_equality (T := (Theory.empty : SetTheory)) (Γ :=
          [x#candidate ≐ₘ left_union,
            x#left ≐ₘ x#right]) (x#left) (x#right) (set_variable_admissible left) (set_variable_admissible right)
        hSourceEquality
  exact Metatheory.Derives.equality_trans
    hCandidateEquality hUnionEquality
/-- 一元并集候选图刻画的双变量全称闭包。 -/
theorem union_eq_iff_spec_forall (source candidate : FreeVarId) :
    ⊢ₘ[union_operator_theory]
      ∀ₘ[SetSort.set, source],
        ∀ₘ[SetSort.set, candidate], (x#candidate ≐ₘ ⋃ₘ x#source) ↔ₘ
            union_spec (x#source) (x#candidate) := by
  have hOpen :
      ⊢ₘ[union_operator_theory] (x#candidate ≐ₘ ⋃ₘ x#source) ↔ₘ
          union_spec (x#source) (x#candidate) :=
    union_eq_iff_spec (x#source) (x#candidate) (set_variable_admissible source) (set_variable_admissible candidate)
  derive_close (source, candidate) using hOpen
/-- 一元并集函数项等式合同的双变量全称闭包。 -/
theorem union_term_congr_forall (left right : FreeVarId) :
    ⊢ₘ[union_operator_theory]
      ∀ₘ[SetSort.set, left],
        ∀ₘ[SetSort.set, right], (x#left ≐ₘ x#right) ⟶ₘ ((⋃ₘ x#left) ≐ₘ (⋃ₘ x#right)) := by
  derive_close (left, right) using
    union_term_congr left right
/-- 二元并定义公理可在任意两个 admissible 集合项处实例化。 -/
theorem binary_union_definition_instance_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[binary_union_operator_theory]
      binary_union_definition_instance
        left right := by
  have hAxiom :
      ⊢ₘ[binary_union_operator_theory]
        binary_union_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hLeftInstance :=
    FirstOrder.Derives.forall_elim
      (term := left) hAxiom
  have hRightInstance :=
    FirstOrder.Derives.forall_elim
      (term := right) hLeftInstance
  have hLeftOpenOneRight :
      Term.openAt SetSort.set 1 right left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 right left hLeft.2
  have hLeftOpenZeroRight :
      Term.openAt SetSort.set 0 right left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 right left hLeft.2
  simpa [binary_union_definition_axiom,
    binary_union_definition_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, binary_union_term,
    union_term, unordered_pair_term,
    hLeftOpenOneRight, hLeftOpenZeroRight] using hRightInstance
/-- 二元并项按定义等于对应无序对的一元并集。 -/
theorem binary_union_term_eq_union_pair_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[binary_union_operator_theory] (left ∪ₘ right) ≐ₘ (⋃ₘ {left, right}ₘ) := by
  simpa [binary_union_definition_instance] using
    binary_union_definition_instance_derives
      left right hLeft hRight
/--
一个候选项等于规范二元并，当且仅当存在文献所用的中间无序对并且候选等于其并集。
-/
theorem binary_union_eq_iff_descriptor (left right candidate : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[binary_union_operator_theory] (candidate ≐ₘ (left ∪ₘ right)) ↔ₘ
        binary_union_descriptor left right candidate := by
  let pair := unordered_pair_term left right
  let union := union_term pair
  let binary := binary_union_term left right
  have hPair :
      Term.Admissible pair SetSort.set :=
    unordered_pair_term_admissible
      left right hLeft hRight
  have hUnion :
      Term.Admissible union SetSort.set :=
    union_term_admissible pair hPair
  have hBinary :
      Term.Admissible binary SetSort.set :=
    binary_union_term_admissible
      left right hLeft hRight
  have hDefinition :
      ⊢ₘ[binary_union_operator_theory]
        binary ≐ₘ union := by
    simpa [binary, union, pair] using
      binary_union_term_eq_union_pair_derives
        left right hLeft hRight
  have hLeftOpenPair :
      Term.openAt SetSort.set 0 pair left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 pair left hLeft.2
  have hRightOpenPair :
      Term.openAt SetSort.set 0 pair right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 pair right hRight.2
  have hCandidateOpenPair :
      Term.openAt SetSort.set 0 pair candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 pair candidate hCandidate.2
  have hDescriptorAdmissible :
      Formula.Admissible (binary_union_descriptor
          left right candidate) :=
    binary_union_descriptor_admissible
      hLeft hRight hCandidate
  have hCandidateBinaryAdmissible :
      Formula.Admissible (candidate ≐ₘ binary) :=
    Formula.Admissible.equal
      hCandidate hBinary
  change
    ⊢ₘ[binary_union_operator_theory] (candidate ≐ₘ binary) ↔ₘ
        binary_union_descriptor left right candidate
  apply FirstOrder.Derives.iffIntro
  · have hCandidateBinary :
        [candidate ≐ₘ binary]
          ⊢ₘ[binary_union_operator_theory]
            candidate ≐ₘ binary :=
      .assumption (by simp)

    have hDefinition' :
        [candidate ≐ₘ binary]
          ⊢ₘ[binary_union_operator_theory]
            binary ≐ₘ union :=
      FirstOrder.Derives.context_weaken_cons
        hDefinition
    have hCandidateUnion :
        [candidate ≐ₘ binary]
          ⊢ₘ[binary_union_operator_theory]
            candidate ≐ₘ union :=
      Metatheory.Derives.equality_trans
        hCandidateBinary hDefinition'
    nd_apply FirstOrder.Derives.exists_intro (term := pair)
    simpa [binary_union_descriptor,
      pair, union, Formula.openAt,
      Term.openAt, hLeftOpenPair,
      hRightOpenPair,
      hCandidateOpenPair] using (FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.eq_refl_m (sort := SetSort.set) pair)
        hCandidateUnion)
  · let descriptor_body : SetFormula := (bₛ#0 ≐ₘ pair) ∧ₘ (candidate ≐ₘ ⋃ₘ bₛ#0)
    let descriptor : SetFormula :=
      ∃ₘ[SetSort.set], descriptor_body
    let conclusion : SetFormula :=
      candidate ≐ₘ binary
    let witness :=
      FreshVariable.fresh_id SetSort.set
        [descriptor_body, descriptor, conclusion]
    let witness_body :=
      Formula.openAt SetSort.set 0 (x#witness) descriptor_body
    have hWitnessFreshDescriptorBody : (SetSort.set, witness) freshForₘ
          descriptor_body := by
      dsimp [witness]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    have hWitnessFreshDescriptor : (SetSort.set, witness) freshForₘ
          descriptor := by
      dsimp [witness]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    have hWitnessFreshConclusion : (SetSort.set, witness) freshForₘ
          conclusion := by
      dsimp [witness]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    have hLocalDescriptorAdmissible :
        Formula.Admissible descriptor := by
      simpa [descriptor, descriptor_body,
        binary_union_descriptor, pair] using
        hDescriptorAdmissible
    have hWitnessBodyAdmissible :
        Formula.Admissible witness_body := by
      dsimp [witness_body]
      refine Formula.Admissible.exists_openAt (σ := signature) (body := descriptor_body) (term := x#witness)
        SetSort.set ?_ (set_variable_admissible witness)
      exact hLocalDescriptorAdmissible
    have hDescriptor :
        [descriptor] ⊢ₘ[binary_union_operator_theory]
          binary_union_descriptor
            left right candidate :=
      .assumption (by
        simp [descriptor, descriptor_body,
          binary_union_descriptor, pair])
    have hExists :
        [descriptor] ⊢ₘ[binary_union_operator_theory]
          ∃ₘ[SetSort.set],
            Formula.closeFreeAt
              SetSort.set witness 0 witness_body := by
      have hCloseOpen :
          Formula.closeFreeAt
              SetSort.set witness 0 witness_body =
            descriptor_body := by
        dsimp [witness_body]
        exact
        Formula.closeFreeAt_openAt
          SetSort.set witness 0
            descriptor_body
            hWitnessFreshDescriptorBody
      simpa [descriptor, descriptor_body,
        binary_union_descriptor, pair,
        hCloseOpen] using hDescriptor
    have hCase :
        witness_body :: [descriptor]
          ⊢ₘ[binary_union_operator_theory]
            conclusion := by
      have hConjunction :
          witness_body :: [descriptor]
            ⊢ₘ[binary_union_operator_theory] (x#witness ≐ₘ pair) ∧ₘ (candidate ≐ₘ ⋃ₘ x#witness) := by
        have hAssumption :
            witness_body :: [descriptor]
              ⊢ₘ[binary_union_operator_theory]
                witness_body :=
          .assumption (by simp)

        have hPairOpenWitness :
            Term.openAt SetSort.set 0 (x#witness) pair =
              pair :=
          Term.openAt_eq_self_of_boundClosed
            SetSort.set 0 (x#witness)
            pair hPair.2
        have hCandidateOpenWitness :
            Term.openAt SetSort.set 0 (x#witness) candidate =
              candidate :=
          Term.openAt_eq_self_of_boundClosed
            SetSort.set 0 (x#witness)
            candidate hCandidate.2
        simpa [witness_body, descriptor_body,
          Formula.openAt, Term.openAt,
          hPairOpenWitness,
          hCandidateOpenWitness] using hAssumption
      have hWitnessPair :
          witness_body :: [descriptor]
            ⊢ₘ[binary_union_operator_theory]
              x#witness ≐ₘ pair :=
        FirstOrder.Derives.conjElimLeft
          hConjunction
      have hCandidateWitnessUnion :
          witness_body :: [descriptor]
            ⊢ₘ[binary_union_operator_theory]
              candidate ≐ₘ ⋃ₘ x#witness :=
        FirstOrder.Derives.conjElimRight
          hConjunction
      have hWitnessUnionPairUnion :
          witness_body :: [descriptor]
            ⊢ₘ[binary_union_operator_theory] (⋃ₘ x#witness) ≐ₘ union := by
        simpa [union] using
          union_term_congr_of_equality (x#witness) pair (set_variable_admissible witness)
            hPair hWitnessPair
      have hCandidateUnion :
          witness_body :: [descriptor]
            ⊢ₘ[binary_union_operator_theory]
              candidate ≐ₘ union :=
        Metatheory.Derives.equality_trans
          hCandidateWitnessUnion
          hWitnessUnionPairUnion
      have hUnionBinary :
          witness_body :: [descriptor]
            ⊢ₘ[binary_union_operator_theory]
              union ≐ₘ binary :=
        Metatheory.Derives.equality_symm
          (FirstOrder.Derives.context_weaken (by
              intro formula hFormula
              cases hFormula)
            hDefinition)
      exact Metatheory.Derives.equality_trans
        hCandidateUnion hUnionBinary
    exact FirstOrder.Derives.exists_elim (by
        intro formula hFormula
        have hSentence :=
          binary_union_operator_theory_sentence hFormula
        rw [hSentence.2]
        simp) (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        exact hWitnessFreshDescriptor)
        hWitnessFreshConclusion
        hExists hCase
/-- 二元并项满足文献中的“配对后取并集”描述。 -/
theorem binary_union_term_descriptor_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[binary_union_operator_theory]
      binary_union_descriptor
        left right (left ∪ₘ right) := by
  exact FirstOrder.Derives.iffElimRight (binary_union_eq_iff_descriptor
      left right (left ∪ₘ right)
      hLeft hRight (binary_union_term_admissible
        left right hLeft hRight))
    (FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) (left ∪ₘ right))
/--
无序对规格与一元并规格组合成二元并的成员析取规格。
这是后续有限并与后继构造复用的公共桥；中间见证只在本证明内部出现。
-/
theorem pair_union_spec_implies_binary_union_spec (left right pair union : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hPair : Term.Admissible pair SetSort.set) (hUnion : Term.Admissible union SetSort.set) :
    ⊢ₘ
      pair_spec left right pair ⟶ₘ
        union_spec pair union ⟶ₘ
          binary_union_spec left right union := by
  let pair_formula := pair_spec left right pair
  let union_formula := union_spec pair union
  let result_body : SetFormula := (bₛ#0 ∈ₘ union) ↔ₘ ((bₛ#0 ∈ₘ left) ∨ₘ (bₛ#0 ∈ₘ right))
  let element :=
    FreshVariable.fresh_id SetSort.set
      [pair_formula, union_formula, result_body]
  let membership_disjunction : SetFormula := (x#element ∈ₘ left) ∨ₘ (x#element ∈ₘ right)
  let point : SetFormula := (x#element ∈ₘ union) ↔ₘ
      membership_disjunction
  have hElementFreshPair : (SetSort.set, element) freshForₘ
        pair_formula := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshUnion : (SetSort.set, element) freshForₘ
        union_formula := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshResult : (SetSort.set, element) freshForₘ
        result_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hPairOpenOne :
      Term.openAt SetSort.set 1 (x#element) pair =
        pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 (x#element) pair hPair.2
  have hUnionOpenZero :
      Term.openAt SetSort.set 0 (x#element) union =
        union :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) union hUnion.2
  have hPairFormulaAdmissible :
      Formula.Admissible pair_formula := by
    dsimp [pair_formula]
    exact pair_spec_admissible
      hLeft hRight hPair
  have hUnionFormulaAdmissible :
      Formula.Admissible union_formula := by
    dsimp [union_formula]
    exact union_spec_admissible
      hPair hUnion
  have hElementAdmissible :
      Term.Admissible (x#element) SetSort.set :=
    set_variable_admissible element
  have hElementMemUnionAdmissible :
      Formula.Admissible (x#element ∈ₘ union) :=
    membership_formula_admissible
      hElementAdmissible hUnion
  have hElementMemLeftAdmissible :
      Formula.Admissible (x#element ∈ₘ left) :=
    membership_formula_admissible
      hElementAdmissible hLeft
  have hElementMemRightAdmissible :
      Formula.Admissible (x#element ∈ₘ right) :=
    membership_formula_admissible
      hElementAdmissible hRight
  have hMembershipDisjunctionAdmissible :
      Formula.Admissible membership_disjunction := by
    dsimp [membership_disjunction]
    exact Formula.Admissible.disj
      hElementMemLeftAdmissible
      hElementMemRightAdmissible
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hPairFormula :
      [union_formula, pair_formula] ⊢ₘ
        pair_formula :=
    .assumption (by simp)
  have hUnionFormula :
      [union_formula, pair_formula] ⊢ₘ
        union_formula :=
    .assumption (by simp)
  have hUnionAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := x#element) hUnionFormula
  have hUnionAt :
      [union_formula, pair_formula] ⊢ₘ (x#element ∈ₘ union) ↔ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ pair) ∧ₘ (x#element ∈ₘ bₛ#0)) := by
    simpa [union_formula, union_spec,
      Formula.openAt, Formula.next_depth,
      Term.openAt, hPairOpenOne,
      hUnionOpenZero] using hUnionAtRaw
  have hUnionWitnessExistsAdmissible :
      Formula.Admissible (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ pair) ∧ₘ (x#element ∈ₘ bₛ#0)) :=
    Formula.Admissible.iff_right
      hUnionAt.admissible
  have hPoint :
      [union_formula, pair_formula] ⊢ₘ point := by
    apply FirstOrder.Derives.iffIntro
    · let witness_body : SetFormula := (bₛ#0 ∈ₘ pair) ∧ₘ (x#element ∈ₘ bₛ#0)
      let conclusion : SetFormula := (x#element ∈ₘ left) ∨ₘ (x#element ∈ₘ right)
      let witness :=
        FreshVariable.fresh_id SetSort.set
          [pair_formula, union_formula,
            x#element ∈ₘ union,
            witness_body, conclusion]
      let witness_point :=
        Formula.openAt SetSort.set 0 (x#witness) witness_body
      have hWitnessFreshPair : (SetSort.set, witness) freshForₘ
            pair_formula := by
        dsimp [witness]
        exact FreshVariable.fresh_id_not_mem_m (by simp)
      have hWitnessFreshUnion : (SetSort.set, witness) freshForₘ
            union_formula := by
        dsimp [witness]
        exact FreshVariable.fresh_id_not_mem_m (by simp)
      have hWitnessFreshMembership : (SetSort.set, witness) freshForₘ (x#element ∈ₘ union) := by
        dsimp [witness]
        exact FreshVariable.fresh_id_not_mem_m (by simp)
      have hWitnessFreshBody : (SetSort.set, witness) freshForₘ
            witness_body := by
        dsimp [witness]
        exact FreshVariable.fresh_id_not_mem_m (by simp)
      have hWitnessFreshConclusion : (SetSort.set, witness) freshForₘ
            conclusion := by
        dsimp [witness]
        exact FreshVariable.fresh_id_not_mem_m (by simp)
      have hWitnessNeElement :
          witness ≠ element := by
        intro hEqual
        apply hWitnessFreshMembership
        rw [hEqual]
        change (SetSort.set, element) ∈
            Term.freeSupportList
              [(x#element : SetTerm), union]
        exact Term.mem_freeSupportList_of_mem (term := (x#element : SetTerm)) (terms := [(x#element : SetTerm), union]) (by simp) (by
            change (SetSort.set, element) ∈
                [(SetSort.set, element)]
            simp)
      have hUnionAt' : (x#element ∈ₘ union) ::
              [union_formula, pair_formula] ⊢ₘ (x#element ∈ₘ union) ↔ₘ (∃ₘ[SetSort.set], witness_body) :=
        FirstOrder.Derives.context_weaken_cons (by
            simpa [witness_body] using hUnionAt)
      have hExists : (x#element ∈ₘ union) ::
              [union_formula, pair_formula] ⊢ₘ
            ∃ₘ[SetSort.set], witness_body :=
        FirstOrder.Derives.iffElimRight
          hUnionAt' (.assumption (by simp))
      have hExistsClosed : (x#element ∈ₘ union) ::
              [union_formula, pair_formula] ⊢ₘ
            ∃ₘ[SetSort.set],
              Formula.closeFreeAt
                SetSort.set witness 0 witness_point := by
        have hCloseOpen :
            Formula.closeFreeAt
                SetSort.set witness 0 witness_point =
              witness_body := by
          dsimp [witness_point]
          exact Formula.closeFreeAt_openAt
            SetSort.set witness 0 witness_body
            hWitnessFreshBody
        simpa [hCloseOpen] using hExists
      have hCase :
          witness_point :: (x#element ∈ₘ union) ::
                [union_formula, pair_formula] ⊢ₘ
            conclusion := by
        have hConjunctionRaw :
            witness_point :: (x#element ∈ₘ union) ::
                  [union_formula, pair_formula] ⊢ₘ
              witness_point :=
          .assumption (by simp)
        have hPairOpenWitness :
            Term.openAt SetSort.set 0 (x#witness) pair =
              pair :=
          Term.openAt_eq_self_of_boundClosed
            SetSort.set 0 (x#witness)
            pair hPair.2
        have hConjunction :
            witness_point :: (x#element ∈ₘ union) ::
                  [union_formula, pair_formula] ⊢ₘ (x#witness ∈ₘ pair) ∧ₘ (x#element ∈ₘ x#witness) := by
          simpa [witness_point, witness_body,
            Formula.openAt, Term.openAt,
            hPairOpenWitness] using hConjunctionRaw
        have hWitnessInPair :=
          FirstOrder.Derives.conjElimLeft
            hConjunction
        have hElementInWitness :=
          FirstOrder.Derives.conjElimRight
            hConjunction
        have hPairFormula' :
            witness_point :: (x#element ∈ₘ union) ::
                  [union_formula, pair_formula] ⊢ₘ
              pair_formula :=
          .assumption (by simp)
        have hPairAtRaw :=
          FirstOrder.Derives.forall_elim
            (term := x#witness) hPairFormula'
        have hPairOpenZero :
            Term.openAt SetSort.set 0 (x#witness) pair =
              pair :=
          Term.openAt_eq_self_of_boundClosed
            SetSort.set 0 (x#witness)
            pair hPair.2
        have hLeftOpenZero :
            Term.openAt SetSort.set 0 (x#witness) left =
              left :=
          Term.openAt_eq_self_of_boundClosed
            SetSort.set 0 (x#witness)
            left hLeft.2
        have hRightOpenZero :
            Term.openAt SetSort.set 0 (x#witness) right =
              right :=
          Term.openAt_eq_self_of_boundClosed
            SetSort.set 0 (x#witness)
            right hRight.2
        have hPairAt :
            witness_point :: (x#element ∈ₘ union) ::
                  [union_formula, pair_formula] ⊢ₘ (x#witness ∈ₘ pair) ↔ₘ ((x#witness ≐ₘ left) ∨ₘ (x#witness ≐ₘ right)) := by
          simpa [pair_formula, pair_spec,
            pair_member_condition,
            Formula.openAt, Term.openAt,
            hPairOpenZero, hLeftOpenZero,
            hRightOpenZero] using hPairAtRaw
        have hChoice :
            witness_point :: (x#element ∈ₘ union) ::
                  [union_formula, pair_formula] ⊢ₘ (x#witness ≐ₘ left) ∨ₘ (x#witness ≐ₘ right) :=
          FirstOrder.Derives.iffElimRight
            hPairAt hWitnessInPair
        apply FirstOrder.Derives.disjElim hChoice
        · have hEquality : (x#witness ≐ₘ left) ::
                  witness_point :: (x#element ∈ₘ union) ::
                      [union_formula, pair_formula] ⊢ₘ
                x#witness ≐ₘ left :=
            .assumption (by simp)
          have hElementInWitness' : (x#witness ≐ₘ left) ::
                  witness_point :: (x#element ∈ₘ union) ::
                      [union_formula, pair_formula] ⊢ₘ
                x#element ∈ₘ x#witness :=
            FirstOrder.Derives.context_weaken_cons
              hElementInWitness
          have hSubstitution :=
            Metatheory.Derives.equality_substitute_free_variable (T := (Theory.empty : SetTheory)) (Γ := (x#witness ≐ₘ left) ::
                  witness_point :: (x#element ∈ₘ union) ::
                      [union_formula, pair_formula]) (sort := SetSort.set) (eigen := witness) (replacement := left) (body := x#element ∈ₘ x#witness)
          have hTransport :=
            FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
                hSubstitution hEquality)
              hElementInWitness'
          have hElementInLeft : (x#witness ≐ₘ left) ::
                  witness_point :: (x#element ∈ₘ union) ::
                      [union_formula, pair_formula] ⊢ₘ
                x#element ∈ₘ left := by
            simpa [Formula.substituteFree,
              Term.substituteFree, set_variable,
              hWitnessNeElement,
              Ne.symm hWitnessNeElement] using hTransport
          exact FirstOrder.Derives.disjIntroLeft
            hElementInLeft
        · have hEquality : (x#witness ≐ₘ right) ::
                  witness_point :: (x#element ∈ₘ union) ::
                      [union_formula, pair_formula] ⊢ₘ
                x#witness ≐ₘ right :=
            .assumption (by simp)
          have hElementInWitness' : (x#witness ≐ₘ right) ::
                  witness_point :: (x#element ∈ₘ union) ::
                      [union_formula, pair_formula] ⊢ₘ
                x#element ∈ₘ x#witness :=
            FirstOrder.Derives.context_weaken_cons
              hElementInWitness
          have hSubstitution :=
            Metatheory.Derives.equality_substitute_free_variable (T := (Theory.empty : SetTheory)) (Γ := (x#witness ≐ₘ right) ::
                  witness_point :: (x#element ∈ₘ union) ::
                      [union_formula, pair_formula]) (sort := SetSort.set) (eigen := witness) (replacement := right) (body := x#element ∈ₘ x#witness)
          have hTransport :=
            FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
                hSubstitution hEquality)
              hElementInWitness'
          have hElementInRight : (x#witness ≐ₘ right) ::
                  witness_point :: (x#element ∈ₘ union) ::
                      [union_formula, pair_formula] ⊢ₘ
                x#element ∈ₘ right := by
            simpa [Formula.substituteFree,
              Term.substituteFree, set_variable,
              hWitnessNeElement,
              Ne.symm hWitnessNeElement] using hTransport
          exact FirstOrder.Derives.disjIntroRight
            hElementInRight
      exact FirstOrder.Derives.exists_elim (by
          intro formula hFormula
          cases hFormula) (by
          intro formula hFormula
          rcases List.mem_cons.mp hFormula with rfl | hFormula
          · exact hWitnessFreshMembership
          · rcases List.mem_cons.mp hFormula with rfl | hFormula
            · exact hWitnessFreshUnion
            · rcases List.mem_cons.mp hFormula with rfl | hFormula
              · exact hWitnessFreshPair
              · exact False.elim (List.not_mem_nil hFormula))
        hWitnessFreshConclusion
        hExistsClosed hCase
    · have hUnionAt' :
          membership_disjunction :: [union_formula, pair_formula] ⊢ₘ (x#element ∈ₘ union) ↔ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ pair) ∧ₘ (x#element ∈ₘ bₛ#0)) :=
        FirstOrder.Derives.context_weaken_cons
          hUnionAt
      have hChoice :
          membership_disjunction :: [union_formula, pair_formula] ⊢ₘ
            membership_disjunction :=
        .assumption (by simp)
      have hExists :
          membership_disjunction :: [union_formula, pair_formula] ⊢ₘ
            ∃ₘ[SetSort.set], (bₛ#0 ∈ₘ pair) ∧ₘ (x#element ∈ₘ bₛ#0) := by
        apply FirstOrder.Derives.disjElim hChoice
        · have hElementInLeft : (x#element ∈ₘ left) ::
                  membership_disjunction ::
                    [union_formula, pair_formula] ⊢ₘ
                x#element ∈ₘ left :=
            .assumption (by simp)
          have hPairFormula' : (x#element ∈ₘ left) ::
                  membership_disjunction ::
                    [union_formula, pair_formula] ⊢ₘ
                pair_formula :=
            .assumption (by simp)
          have hPairAtRaw :=
            FirstOrder.Derives.forall_elim
              (term := left) hPairFormula'
          have hPairOpenLeft :
              Term.openAt SetSort.set 0 left pair =
                pair :=
            Term.openAt_eq_self_of_boundClosed
              SetSort.set 0 left pair hPair.2
          have hLeftOpenLeft :
              Term.openAt SetSort.set 0 left left =
                left :=
            Term.openAt_eq_self_of_boundClosed
              SetSort.set 0 left left hLeft.2
          have hRightOpenLeft :
              Term.openAt SetSort.set 0 left right =
                right :=
            Term.openAt_eq_self_of_boundClosed
              SetSort.set 0 left right hRight.2
          have hPairAt : (x#element ∈ₘ left) ::
                  membership_disjunction ::
                    [union_formula, pair_formula] ⊢ₘ (left ∈ₘ pair) ↔ₘ ((left ≐ₘ left) ∨ₘ (left ≐ₘ right)) := by
            simpa [pair_formula, pair_spec,
              pair_member_condition,
              Formula.openAt, Term.openAt,
              hPairOpenLeft, hLeftOpenLeft,
              hRightOpenLeft] using hPairAtRaw
          have hLeftInPair : (x#element ∈ₘ left) ::
                  membership_disjunction ::
                    [union_formula, pair_formula] ⊢ₘ
                left ∈ₘ pair :=
            FirstOrder.Derives.iffElimLeft
              hPairAt (FirstOrder.Derives.disjIntroLeft
                (FirstOrder.Derives.eq_refl_m
                  (sort := SetSort.set) left))
          nd_apply FirstOrder.Derives.exists_intro (term := left)
          have hPairOpenLeftZero :
              Term.openAt SetSort.set 0 left pair =
                pair :=
            hPairOpenLeft
          simpa [Formula.openAt, Term.openAt,
            hPairOpenLeftZero] using (FirstOrder.Derives.conjIntro
              hLeftInPair hElementInLeft)
        · have hElementInRight : (x#element ∈ₘ right) ::
                  membership_disjunction ::
                    [union_formula, pair_formula] ⊢ₘ
                x#element ∈ₘ right :=
            .assumption (by simp)
          have hPairFormula' : (x#element ∈ₘ right) ::
                  membership_disjunction ::
                    [union_formula, pair_formula] ⊢ₘ
                pair_formula :=
            .assumption (by simp)
          have hPairAtRaw :=
            FirstOrder.Derives.forall_elim
              (term := right) hPairFormula'
          have hPairOpenRight :
              Term.openAt SetSort.set 0 right pair =
                pair :=
            Term.openAt_eq_self_of_boundClosed
              SetSort.set 0 right pair hPair.2
          have hLeftOpenRight :
              Term.openAt SetSort.set 0 right left =
                left :=
            Term.openAt_eq_self_of_boundClosed
              SetSort.set 0 right left hLeft.2
          have hRightOpenRight :
              Term.openAt SetSort.set 0 right right =
                right :=
            Term.openAt_eq_self_of_boundClosed
              SetSort.set 0 right right hRight.2
          have hPairAt : (x#element ∈ₘ right) ::
                  membership_disjunction ::
                    [union_formula, pair_formula] ⊢ₘ (right ∈ₘ pair) ↔ₘ ((right ≐ₘ left) ∨ₘ (right ≐ₘ right)) := by
            simpa [pair_formula, pair_spec,
              pair_member_condition,
              Formula.openAt, Term.openAt,
              hPairOpenRight, hLeftOpenRight,
              hRightOpenRight] using hPairAtRaw
          have hRightInPair : (x#element ∈ₘ right) ::
                  membership_disjunction ::
                    [union_formula, pair_formula] ⊢ₘ
                right ∈ₘ pair :=
            FirstOrder.Derives.iffElimLeft
              hPairAt (FirstOrder.Derives.disjIntroRight
                (FirstOrder.Derives.eq_refl_m
                  (sort := SetSort.set) right))
          nd_apply FirstOrder.Derives.exists_intro (term := right)
          simpa [Formula.openAt, Term.openAt,
            hPairOpenRight] using (FirstOrder.Derives.conjIntro
              hRightInPair hElementInRight)
      exact FirstOrder.Derives.iffElimLeft
        hUnionAt' hExists
  have hPointOpened :
      [union_formula, pair_formula] ⊢ₘ
        Formula.openAt SetSort.set 0 (x#element) result_body := by
    have hLeftOpenZero :
        Term.openAt SetSort.set 0 (x#element) left =
          left :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 (x#element)
        left hLeft.2
    have hRightOpenZero :
        Term.openAt SetSort.set 0 (x#element) right =
          right :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 (x#element)
        right hRight.2
    simpa [point, result_body,
      Formula.openAt, Term.openAt,
      hUnionOpenZero, hLeftOpenZero,
      hRightOpenZero] using hPoint
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := (Theory.empty : SetTheory)) (Γ := [union_formula, pair_formula]) (sort := SetSort.set) (eigen := element) (body :=
        Formula.openAt SetSort.set 0 (x#element) result_body) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        rcases List.mem_cons.mp hFormula with rfl | hFormula
        · exact hElementFreshUnion
        · rcases List.mem_cons.mp hFormula with rfl | hFormula
          · exact hElementFreshPair
          · exact False.elim (List.not_mem_nil hFormula))
      hPointOpened
  simpa [pair_formula, union_formula,
    binary_union_spec, result_body,
    Formula.closeFreeAt_openAt
      SetSort.set element 0 result_body
      hElementFreshResult] using hGeneralized
/-- 二元并项满足成员析取规格。 -/
theorem binary_union_term_spec_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[binary_union_operator_theory]
      binary_union_spec
        left right (left ∪ₘ right) := by
  let pair := unordered_pair_term left right
  let union := binary_union_term left right
  have hPair :
      Term.Admissible pair SetSort.set :=
    unordered_pair_term_admissible
      left right hLeft hRight
  have hUnion :
      Term.Admissible union SetSort.set :=
    binary_union_term_admissible
      left right hLeft hRight
  have hPairSpec :
      ⊢ₘ[binary_union_operator_theory]
        pair_spec left right pair :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        pairing_operator_theory_subset_binary_union_operator_theory
          hFormula) (by
        simpa [pair] using
          unordered_pair_term_spec_derives
            left right hLeft hRight)
  have hUnionEqSpec :
      ⊢ₘ[binary_union_operator_theory] (union ≐ₘ ⋃ₘ pair) ↔ₘ
          union_spec pair union :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        union_operator_theory_subset_binary_union_operator_theory
          hFormula) (union_eq_iff_spec pair union hPair hUnion)
  have hDefinition :
      ⊢ₘ[binary_union_operator_theory]
        union ≐ₘ ⋃ₘ pair := by
    simpa [union, pair] using
      binary_union_term_eq_union_pair_derives
        left right hLeft hRight
  have hUnionSpec :
      ⊢ₘ[binary_union_operator_theory]
        union_spec pair union :=
    FirstOrder.Derives.iffElimRight
      hUnionEqSpec hDefinition
  have hBridge :
      ⊢ₘ[binary_union_operator_theory]
        pair_spec left right pair ⟶ₘ
          union_spec pair union ⟶ₘ
            binary_union_spec left right union :=
    FirstOrder.Derives.of_empty (pair_union_spec_implies_binary_union_spec
        left right pair union
        hLeft hRight hPair hUnion)
  simpa [union] using
    FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
        hBridge hPairSpec)
      hUnionSpec
/-- 两个参数的已证明等式可组合为二元并项等式。 -/
theorem binary_union_term_congr_of_equalities
    {Γ : Context signature} (left_first right_first left_second right_second : SetTerm) (hLeftFirst : Term.Admissible left_first SetSort.set)
    (hRightFirst : Term.Admissible right_first SetSort.set) (hLeftSecond : Term.Admissible left_second SetSort.set)
    (hRightSecond : Term.Admissible right_second SetSort.set) (hFirstEquality :
      Γ ⊢ₘ[binary_union_operator_theory]
        left_first ≐ₘ right_first) (hSecondEquality :
      Γ ⊢ₘ[binary_union_operator_theory]
        left_second ≐ₘ right_second) :
    Γ ⊢ₘ[binary_union_operator_theory] (left_first ∪ₘ left_second) ≐ₘ (right_first ∪ₘ right_second) := by
  exact Metatheory.Derives.binary_term_constructor_congr_of_equalities
    binary_union_term
    binary_union_term_admissible
    (by intros; simp [Term.substituteFree])
    left_first right_first left_second right_second
    hLeftFirst hRightFirst hLeftSecond hRightSecond
    hFirstEquality hSecondEquality
/-- 两组自由变量等式推出对应二元并项相等。 -/
theorem binary_union_term_congr (left_first right_first left_second right_second : FreeVarId) :
    ⊢ₘ[binary_union_operator_theory] (x#left_first ≐ₘ x#right_first) ⟶ₘ ((x#left_second ≐ₘ x#right_second) ⟶ₘ ((x#left_first ∪ₘ x#left_second) ≐ₘ
            (x#right_first ∪ₘ x#right_second))) := by
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  exact binary_union_term_congr_of_equalities (Γ :=
      [x#left_second ≐ₘ x#right_second,
        x#left_first ≐ₘ x#right_first]) (x#left_first) (x#right_first) (x#left_second) (x#right_second) (set_variable_admissible left_first)
    (set_variable_admissible right_first)
    (set_variable_admissible left_second)
    (set_variable_admissible right_second)
    (.assumption (by simp)) (.assumption (by simp))
/-- 文献二元并候选图刻画的三变量全称闭包。 -/
theorem binary_union_eq_iff_descriptor_forall (left right candidate : FreeVarId) :
    ⊢ₘ[binary_union_operator_theory]
      ∀ₘ[SetSort.set, left],
        ∀ₘ[SetSort.set, right],
          ∀ₘ[SetSort.set, candidate], (x#candidate ≐ₘ (x#left ∪ₘ x#right)) ↔ₘ
              binary_union_descriptor (x#left) (x#right) (x#candidate) := by
  have hOpen :
      ⊢ₘ[binary_union_operator_theory] (x#candidate ≐ₘ (x#left ∪ₘ x#right)) ↔ₘ
          binary_union_descriptor (x#left) (x#right) (x#candidate) :=
    binary_union_eq_iff_descriptor (x#left) (x#right) (x#candidate) (set_variable_admissible left) (set_variable_admissible right)
      (set_variable_admissible candidate)
  derive_close (left, right, candidate) using hOpen
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
