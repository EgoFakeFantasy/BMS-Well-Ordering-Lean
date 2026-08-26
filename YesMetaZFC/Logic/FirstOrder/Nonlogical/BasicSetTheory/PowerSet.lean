import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.EmptySet
/-!
# 幂集
幂集存在公理只依赖原子的子集关系；其唯一性只依赖外延性。这里先在最小理论上
建立存在与唯一性，再把一元函数符号 `𝒫ₘ` 作为描述符定义扩张加入。需要同时消费
空集、分离或其他构造时，可在后续模块中用理论弱化组合这些独立接口。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-- `power` 正好由 `source` 的所有子集组成。 -/
def power_set_spec (source power : SetTerm) : SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ power) ↔ₘ (bₛ#0 ⊆ₘ source)
/-- 对固定集合断言一个幂集存在。 -/
def power_set_exists (source : SetTerm) : SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ (bₛ#0 ⊆ₘ source)
/-- 幂集存在公理。 -/
def power_set_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    power_set_exists (x#0)
/-- 在子集理论上加入幂集存在公理。 -/
def power_set_theory : SetTheory :=
  Theory.insert power_set_axiom subset_theory
/-- 幂集函数符号的开放定义实例。 -/
def power_set_definition_instance (source : SetTerm) : SetFormula :=
  power_set_spec source (𝒫ₘ(source))
/-- 幂集函数符号的定义公理。 -/
def power_set_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    power_set_definition_instance (x#0)
/-- 在幂集存在理论上加入幂集函数符号的保守定义扩张。 -/
def power_set_operator_theory : SetTheory :=
  Theory.insert power_set_definition_axiom power_set_theory
/-- 幂集项保持 proof-carrying 项边界。 -/
theorem power_set_term_admissible (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    Term.Admissible (power_set_term source) SetSort.set := by
  simpa using
    set_function_application_admissible
      .powerSet [⟨source, by assumption⟩]
      (by rfl) (by rfl)
/-- 幂集规格在 admissible 的源项与候选项处仍然 admissible。 -/
theorem power_set_spec_admissible
    {source power : SetTerm} (hSource : Term.Admissible source SetSort.set) (hPower : Term.Admissible power SetSort.set) :
    Formula.Admissible (power_set_spec source power) := by
  prove_admissible
/-- 幂集函数符号的开放定义实例在 admissible 源项处仍然 admissible。 -/
theorem power_set_definition_instance_admissible
    {source : SetTerm} (hSource : Term.Admissible source SetSort.set) :
    Formula.Admissible (power_set_definition_instance source) := by
  exact power_set_spec_admissible hSource (power_set_term_admissible source hSource)
/-- 幂集存在公式满足公共 proof-carrying 良构性边界。 -/
theorem power_set_exists_admissible
    {source : SetTerm} (hSource : Term.Admissible source SetSort.set) :
    Formula.Admissible (power_set_exists source) := by
  prove_admissible
/-- 幂集存在公理满足公共 proof-carrying 良构性边界。 -/
theorem power_set_axiom_admissible :
    Formula.Admissible power_set_axiom := by
  apply Formula.Admissible.forall_closeFreeAt
  apply power_set_exists_admissible
  exact ⟨
    TermWellSorted.fvar (σ := signature) SetSort.set 0,
    TermScoped.fvar (σ := signature) (ctx := (Scope.empty : Scope signature))
      SetSort.set 0⟩
/-- 幂集存在理论仍然 admissible。 -/
theorem power_set_theory_admissible :
    Theory.Admissible power_set_theory :=
  Theory.admissible_insert
    power_set_axiom_admissible
    subset_theory_admissible
/-- 幂集函数符号定义公理满足公共 proof-carrying 良构性边界。 -/
theorem power_set_definition_axiom_admissible :
    Formula.Admissible power_set_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 幂集函数符号定义扩张后的理论仍然 admissible。 -/
theorem power_set_operator_theory_admissible :
    Theory.Admissible power_set_operator_theory :=
  Theory.admissible_insert
    power_set_definition_axiom_admissible
    power_set_theory_admissible
/-- 幂集运算符理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem power_set_operator_theory_sentence
    {formula : SetFormula} (hFormula : power_set_operator_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact power_set_operator_theory_admissible
      formula hFormula
  · change
      formula = power_set_definition_axiom ∨ (formula = power_set_axiom ∨ (formula = subset_definition_axiom ∨
            extensionality_theory formula)) at hFormula
    rcases hFormula with rfl | hFormula
    · native_decide
    · rcases hFormula with rfl | hFormula
      · native_decide
      · rcases hFormula with rfl | hFormula
        · native_decide
        · change formula = extensionality_axiom at hFormula
          subst formula
          native_decide
/-- 幂集存在公理可在任意 admissible 集合项处实例化。 -/
theorem power_set_exists_derives (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[power_set_theory]
      power_set_exists source := by
  have hAxiom :
      ⊢ₘ[power_set_theory] power_set_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hInstance :=
    FirstOrder.Derives.forall_elim
      (term := source) hAxiom
  simpa [power_set_axiom, power_set_exists,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.substituteFree, Term.substituteFree] using hInstance
/-- 幂集函数符号定义公理可在任意 admissible 集合项处实例化。 -/
theorem power_set_definition_instance_derives (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[power_set_operator_theory]
      power_set_definition_instance source := by
  have hAxiom :
      ⊢ₘ[power_set_operator_theory]
        power_set_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hInstance :=
    FirstOrder.Derives.forall_elim
      (term := source) hAxiom
  simpa [power_set_definition_axiom,
    power_set_definition_instance, power_set_spec,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.substituteFree, Term.substituteFree] using hInstance
/-- 定义扩张中的幂集项满足幂集规格。 -/
theorem power_set_term_spec_derives (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[power_set_operator_theory]
      power_set_spec source (𝒫ₘ(source)) := by
  simpa [power_set_definition_instance] using
    power_set_definition_instance_derives source hSource
/--
规范幂集项的成员关系等价于子集关系。
这是幂集定义合同最常用的逐点消去形式；有限图编码、笛卡尔积母集以及后续
有界证明码的有限见证域都统一复用这一接口。
-/
theorem mem_power_set_term_iff_subset (source element : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[power_set_operator_theory] (element ∈ₘ 𝒫ₘ(source)) ↔ₘ (element ⊆ₘ source) := by
  have hSpec :=
    power_set_term_spec_derives source hSource
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := element) hSpec
  have hPower :
      Term.Admissible (𝒫ₘ(source)) SetSort.set :=
    power_set_term_admissible source hSource
  have hSourceOpen :
      Term.openAt SetSort.set 0 element source =
        source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element source hSource.2
  have hPowerOpen :
      Term.openAt SetSort.set 0
          element (𝒫ₘ(source)) =
        𝒫ₘ(source) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element (𝒫ₘ(source)) hPower.2
  simpa [power_set_spec,
    Formula.openAt, Term.openAt,
    hSourceOpen, hPowerOpen] using hAt
/-- 同一集合的两个幂集候选必相等。 -/
theorem power_set_unique (source left right : SetTerm) (hSource : Term.Admissible source SetSort.set) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[extensionality_theory]
      power_set_spec source left ⟶ₘ
        power_set_spec source right ⟶ₘ (left ≐ₘ right) := by
  simpa [power_set_spec,
    membership_specification] using
    membership_specification_unique
      left right (bₛ#0 ⊆ₘ source)
      hLeft hRight (power_set_spec_admissible
        hSource hLeft) (power_set_spec_admissible
        hSource hRight)
/--
一个 admissible 集合项等于 `source` 的幂集，当且仅当它满足幂集规格。
正向使用等词替换把定义公理从规范幂集项运输到候选项，反向只使用外延唯一性。
-/
theorem power_set_eq_iff_spec (source candidate : SetTerm) (hSource : Term.Admissible source SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[power_set_operator_theory] (candidate ≐ₘ 𝒫ₘ(source)) ↔ₘ
        power_set_spec source candidate := by
  let power := power_set_term source
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [Formula.equal source source]
  have hPower :
      Term.Admissible power SetSort.set := by
    exact power_set_term_admissible source hSource
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
  have hSourceFixedPower :
      Term.substituteFree SetSort.set
          parameter power source =
        source :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter power source
      hParameterFreshSource
  have hCandidatePowerEqualityAdmissible :
      Formula.Admissible (candidate ≐ₘ power) :=
    Formula.Admissible.equal
      hCandidate hPower
  have hCandidateSpecAdmissible :
      Formula.Admissible (power_set_spec source candidate) :=
    power_set_spec_admissible
      hSource hCandidate
  change
    ⊢ₘ[power_set_operator_theory] (candidate ≐ₘ power) ↔ₘ
        power_set_spec source candidate
  apply FirstOrder.Derives.iffIntro
  · have hEquality :
        [candidate ≐ₘ power] ⊢ₘ[power_set_operator_theory]
          candidate ≐ₘ power :=
      .assumption (by simp)
    have hCongruence :=
      Metatheory.Derives.equality_iff_of_equality (T := power_set_operator_theory) (Γ := [candidate ≐ₘ power]) (sort := SetSort.set) (eigen := parameter)
        (left := candidate) (right := power) (body := power_set_spec source (x#parameter))
        hEquality
    have hCongruenceNormalized :
        [candidate ≐ₘ power] ⊢ₘ[power_set_operator_theory]
          power_set_spec source candidate ↔ₘ
            power_set_spec source power := by
      simpa [power_set_spec,
        Formula.substituteFree, Term.substituteFree,
        hSourceFixedCandidate, hSourceFixedPower,
        set_variable] using hCongruence
    have hPowerSpec :
        [candidate ≐ₘ power] ⊢ₘ[power_set_operator_theory]
          power_set_spec source power :=
      FirstOrder.Derives.context_weaken_cons (by
          simpa [power] using
            power_set_term_spec_derives source hSource)
    exact FirstOrder.Derives.iffElimLeft
      hCongruenceNormalized hPowerSpec
  · have hCandidateSpec :
        [power_set_spec source candidate] ⊢ₘ[power_set_operator_theory]
          power_set_spec source candidate :=
      .assumption (by simp)
    have hPowerSpec :
        [power_set_spec source candidate] ⊢ₘ[power_set_operator_theory]
          power_set_spec source power :=
      FirstOrder.Derives.context_weaken_cons (by
          simpa [power] using
            power_set_term_spec_derives source hSource)
    have hUnique :
        [power_set_spec source candidate] ⊢ₘ[power_set_operator_theory]
          power_set_spec source candidate ⟶ₘ
            power_set_spec source power ⟶ₘ (candidate ≐ₘ power) :=
      FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.theory_weaken (by
            intro formula hFormula
            change
              formula = power_set_definition_axiom ∨ (formula = power_set_axiom ∨ (formula = subset_definition_axiom ∨
                    extensionality_theory formula))
            exact Or.inr (Or.inr (Or.inr hFormula))) (power_set_unique
            source candidate power
            hSource hCandidate hPower)
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
        hUnique hCandidateSpec)
      hPowerSpec
/-- 已证明的集合等式可直接提升为幂集函数项等式。 -/
theorem power_set_term_congr_of_equality
    {T : SetTheory} {Γ : Context signature} (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] 𝒫ₘ(left) ≐ₘ 𝒫ₘ(right) := by
  exact Metatheory.Derives.unary_term_constructor_congr_of_equality
    power_set_term
    power_set_term_admissible
    (by intros; simp [Term.substituteFree])
    left right hLeft hRight hEquality
/-- 幂集函数项保持自由集合变量的等式。 -/
theorem power_set_term_congr (left right : FreeVarId) :
    ⊢ₘ (x#left ≐ₘ x#right) ⟶ₘ (𝒫ₘ(x#left) ≐ₘ 𝒫ₘ(x#right)) := by
  have hEqualityAdmissible :
      Formula.Admissible (x#left ≐ₘ x#right) :=
    Formula.Admissible.equal (set_variable_admissible left) (set_variable_admissible right)
  nd_apply FirstOrder.Derives.impIntro
  exact power_set_term_congr_of_equality
    (x#left) (x#right)
    (set_variable_admissible left)
    (set_variable_admissible right)
    (.assumption (by simp))
/-- 等价的源集合可运输同一个候选对象的幂集等式。 -/
theorem power_set_eq_transport (left right candidate : FreeVarId) :
    ⊢ₘ (x#left ≐ₘ x#right) ⟶ₘ ((x#candidate ≐ₘ 𝒫ₘ(x#left)) ⟶ₘ (x#candidate ≐ₘ 𝒫ₘ(x#right))) := by
  let left_power := power_set_term (x#left)
  let right_power := power_set_term (x#right)
  have hLeftPower :
      Term.Admissible left_power SetSort.set :=
    power_set_term_admissible (x#left) (set_variable_admissible left)
  have hRightPower :
      Term.Admissible right_power SetSort.set :=
    power_set_term_admissible (x#right) (set_variable_admissible right)
  have hLeftAdmissible :
      Term.Admissible (x#left) SetSort.set :=
    set_variable_admissible left
  have hRightAdmissible :
      Term.Admissible (x#right) SetSort.set :=
    set_variable_admissible right
  have hCandidateAdmissible :
      Term.Admissible (x#candidate) SetSort.set :=
    set_variable_admissible candidate
  have hSourceEqualityAdmissible :
      Formula.Admissible (x#left ≐ₘ x#right) :=
    Formula.Admissible.equal
      hLeftAdmissible hRightAdmissible
  have hCandidateEqualityAdmissible :
      Formula.Admissible (x#candidate ≐ₘ left_power) :=
    Formula.Admissible.equal
      hCandidateAdmissible hLeftPower
  change
    ⊢ₘ (x#left ≐ₘ x#right) ⟶ₘ ((x#candidate ≐ₘ left_power) ⟶ₘ (x#candidate ≐ₘ right_power))
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hSourceEquality :
      [x#candidate ≐ₘ left_power,
          x#left ≐ₘ x#right] ⊢ₘ
        x#left ≐ₘ x#right :=
    .assumption (by simp)
  have hCandidateEquality :
      [x#candidate ≐ₘ left_power,
          x#left ≐ₘ x#right] ⊢ₘ
        x#candidate ≐ₘ left_power :=
    .assumption (by simp)
  have hPowerEquality :
      [x#candidate ≐ₘ left_power,
          x#left ≐ₘ x#right] ⊢ₘ
        left_power ≐ₘ right_power := by
    simpa [left_power, right_power] using
      power_set_term_congr_of_equality (T := (Theory.empty : SetTheory)) (Γ :=
          [x#candidate ≐ₘ left_power,
            x#left ≐ₘ x#right]) (x#left) (x#right) (set_variable_admissible left) (set_variable_admissible right)
        hSourceEquality
  exact Metatheory.Derives.equality_trans
    hCandidateEquality hPowerEquality
/-- 幂集候选图刻画的双变量全称闭包。 -/
theorem power_set_eq_iff_spec_forall (source candidate : FreeVarId) :
    ⊢ₘ[power_set_operator_theory]
      ∀ₘ[SetSort.set, source],
        ∀ₘ[SetSort.set, candidate], (x#candidate ≐ₘ 𝒫ₘ(x#source)) ↔ₘ
            power_set_spec (x#source) (x#candidate) := by
  have hOpen :
      ⊢ₘ[power_set_operator_theory] (x#candidate ≐ₘ 𝒫ₘ(x#source)) ↔ₘ
          power_set_spec (x#source) (x#candidate) :=
    power_set_eq_iff_spec (x#source) (x#candidate) (set_variable_admissible source) (set_variable_admissible candidate)
  derive_close (source, candidate) using hOpen
/-- 幂集函数项等式合同的双变量全称闭包。 -/
theorem power_set_term_congr_forall (left right : FreeVarId) :
    ⊢ₘ[power_set_operator_theory]
      ∀ₘ[SetSort.set, left],
        ∀ₘ[SetSort.set, right], (x#left ≐ₘ x#right) ⟶ₘ (𝒫ₘ(x#left) ≐ₘ 𝒫ₘ(x#right)) := by
  derive_close (left, right) using
    power_set_term_congr left right
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
