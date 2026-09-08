import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Basic

/-!
# 幂集

幂集规格直接建立在内在类型的子集关系上。存在公理与函数符号定义均为闭句；
实例化只经过结构化 free 替换，不再携带 admissibility、变量编号或闭性旁证。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-- `power` 正好由 `source` 的所有子集组成。 -/
def power_set_spec {bound free : SetContext}
    (source power : SetTerm bound free) : SetFormula bound free :=
  let subset : SetFormula bound (SetSort.set :: free) :=
    let element : SetTerm bound (SetSort.set :: free) := .fvar .here
    element ⊆ₘ source.weakenFree SetSort.set
  membership_specification power subset

/-- 对固定集合断言一个幂集存在。 -/
def power_set_exists {bound free : SetContext}
    (source : SetTerm bound free) : SetFormula bound free :=
  let power : SetTerm bound (SetSort.set :: free) := .fvar .here
  (power_set_spec (source.weakenFree SetSort.set) power)
    |>.existsFreeTop SetSort.set

/-- 幂集存在公理。 -/
def power_set_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (power_set_exists
      (FreshVariable.newest
        (σ := signature) (free := []) SetSort.set))

/-- 在子集理论上加入幂集存在公理。 -/
def power_set_theory : SetTheory :=
  Theory.insert power_set_axiom subset_theory

/-- 幂集函数符号的开放定义实例。 -/
def power_set_definition_instance {bound free : SetContext}
    (source : SetTerm bound free) : SetFormula bound free :=
  power_set_spec source (𝒫ₘ(source))

/-- 幂集函数符号的定义公理。 -/
def power_set_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (power_set_definition_instance
      (FreshVariable.newest
        (σ := signature) (free := []) SetSort.set))

/-- 在幂集存在理论上加入幂集函数符号定义。 -/
def power_set_operator_theory : SetTheory :=
  Theory.insert power_set_definition_axiom power_set_theory

/-- 幂集存在公理可在任意集合项处实例化。 -/
theorem power_set_exists_derives
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[power_set_theory] power_set_exists source := by
  let body : SetOpenFormula [SetSort.set] :=
    power_set_exists
      (FreshVariable.newest
        (σ := signature) (free := []) SetSort.set)
  let τ : VariableSubstitution signature [SetSort.set] [] free :=
    VariableSubstitution.cons source VariableSubstitution.empty
  have hClosed :
      ([] : Context signature []) ⊢ₘ[power_set_theory]
        Formula.fromSentence power_set_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, power_set_axiom, power_set_exists,
    power_set_spec, membership_specification,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId,
    FreshVariable.newest] using! hInstance

/-- 幂集函数符号定义公理可在任意集合项处实例化。 -/
theorem power_set_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[power_set_operator_theory]
      power_set_definition_instance source := by
  let body : SetOpenFormula [SetSort.set] :=
    power_set_definition_instance
      (FreshVariable.newest
        (σ := signature) (free := []) SetSort.set)
  let τ : VariableSubstitution signature [SetSort.set] [] free :=
    VariableSubstitution.cons source VariableSubstitution.empty
  have hClosed :
      ([] : Context signature []) ⊢ₘ[power_set_operator_theory]
        Formula.fromSentence power_set_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, power_set_definition_axiom,
    power_set_definition_instance, power_set_spec,
    membership_specification, Formula.substituteFree,
    Substitution.free_map, Formula.substitute,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons,
    VariableSubstitution.empty, VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId,
    FreshVariable.newest] using! hInstance

/-- 规范幂集项满足幂集规格。 -/
theorem power_set_term_spec_derives
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[power_set_operator_theory]
      power_set_spec source (𝒫ₘ(source)) := by
  simpa [power_set_definition_instance] using
    (power_set_definition_instance_derives (Γ := Γ) source)

/-- 规范幂集项的成员关系等价于子集关系。 -/
theorem mem_power_set_term_iff_subset
    {free : SetContext} {Γ : Context signature free}
    (source element : SetOpenTerm free) :
    Γ ⊢ₘ[power_set_operator_theory]
      (element ∈ₘ 𝒫ₘ(source)) ↔ₘ (element ⊆ₘ source) := by
  have hSpecification := power_set_term_spec_derives
    (Γ := Γ) source
  have hAt := FirstOrder.Derives.forall_elim element hSpecification
  simpa [power_set_spec, membership_specification] using! hAt

/-- 同一集合的两个幂集候选必相等。 -/
theorem power_set_unique
    {free : SetContext} {Γ : Context signature free}
    (source left right : SetOpenTerm free) :
    Γ ⊢ₘ[extensionality_theory]
      power_set_spec source left ⟶ₘ
        power_set_spec source right ⟶ₘ (left ≐ₘ right) := by
  let subset : SetOpenFormula (SetSort.set :: free) :=
    let element : SetOpenTerm (SetSort.set :: free) := .fvar .here
    element ⊆ₘ source.weakenFree SetSort.set
  simpa [power_set_spec, subset] using
    (membership_specification_unique (Γ := Γ) left right subset)

/-- 一个集合等于规范幂集项，当且仅当它满足幂集规格。 -/
theorem power_set_eq_iff_spec
    {free : SetContext} {Γ : Context signature free}
    (source candidate : SetOpenTerm free) :
    Γ ⊢ₘ[power_set_operator_theory]
      (candidate ≐ₘ 𝒫ₘ(source)) ↔ₘ power_set_spec source candidate := by
  let power : SetOpenTerm free := 𝒫ₘ(source)
  apply FirstOrder.Derives.iff_intro
  · have hEquality :
        ((candidate ≐ₘ power) :: Γ) ⊢ₘ[power_set_operator_theory]
          candidate ≐ₘ power :=
      FirstOrder.Derives.assumption List.mem_cons_self
    let body : Formula signature [SetSort.set] free :=
      power_set_spec
        (source.weakenBound SetSort.set) (.bvar .here)
    have hCongruence := Metatheory.Derives.equality_iff_of_equality
      (T := power_set_operator_theory)
      (Γ := (candidate ≐ₘ power) :: Γ) body hEquality
    have hPowerSpec :
        ((candidate ≐ₘ power) :: Γ) ⊢ₘ[power_set_operator_theory]
          power_set_spec source power
        := FirstOrder.Derives.context_weaken_cons
        (assumption := candidate ≐ₘ power)
        (by simpa [power] using
          (power_set_term_spec_derives (Γ := Γ) source))
    have hCongruence' :
        ((candidate ≐ₘ power) :: Γ) ⊢ₘ[power_set_operator_theory]
          power_set_spec source candidate ↔ₘ
            power_set_spec source power := by
      simpa [body, power_set_spec, membership_specification] using! hCongruence
    simpa [power] using
      FirstOrder.Derives.iff_elim_right hCongruence' hPowerSpec
  · have hCandidateSpec :
        (power_set_spec source candidate :: Γ) ⊢ₘ[power_set_operator_theory]
          power_set_spec source candidate :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hPowerSpec :
        (power_set_spec source candidate :: Γ) ⊢ₘ[power_set_operator_theory]
          power_set_spec source power :=
      FirstOrder.Derives.context_weaken_cons
        (assumption := power_set_spec source candidate)
        (by simpa [power] using
          (power_set_term_spec_derives (Γ := Γ) source))
    have hUnique :
        (power_set_spec source candidate :: Γ) ⊢ₘ[power_set_operator_theory]
          power_set_spec source candidate ⟶ₘ
            power_set_spec source power ⟶ₘ (candidate ≐ₘ power) :=
      FirstOrder.Derives.context_weaken_cons
        (assumption := power_set_spec source candidate)
        (FirstOrder.Derives.theory_weaken (by
          intro sentence hSentence
          exact Or.inr (Or.inr (Or.inr hSentence)))
          (power_set_unique (Γ := Γ) source candidate power))
    exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim hUnique hCandidateSpec)
      hPowerSpec

/-- 已证明的集合等式可直接提升为幂集函数项等式。 -/
theorem power_set_term_congr_of_equality
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] 𝒫ₘ(left) ≐ₘ 𝒫ₘ(right) := by
  let termContext : SetTerm [SetSort.set] free :=
    𝒫ₘ((.bvar .here : SetTerm [SetSort.set] free))
  simpa [termContext] using!
    (Metatheory.Derives.term_context_congr_of_equality
      (T := T) (Γ := Γ) termContext hEquality)

/-- 幂集项合同的蕴含形式。 -/
theorem power_set_term_congr
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (left ≐ₘ right) ⟶ₘ (𝒫ₘ(left) ≐ₘ 𝒫ₘ(right)) := by
  apply FirstOrder.Derives.imp_intro
  exact power_set_term_congr_of_equality left right
    (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 等价的源集合可运输同一个候选对象的幂集等式。 -/
theorem power_set_eq_transport
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right candidate : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (left ≐ₘ right) ⟶ₘ
        ((candidate ≐ₘ 𝒫ₘ(left)) ⟶ₘ
          (candidate ≐ₘ 𝒫ₘ(right))) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  have hSourceEquality :
      ((candidate ≐ₘ 𝒫ₘ(left)) :: (left ≐ₘ right) :: Γ) ⊢ₘ[T]
        left ≐ₘ right :=
    FirstOrder.Derives.assumption (by simp)
  have hCandidateEquality :
      ((candidate ≐ₘ 𝒫ₘ(left)) :: (left ≐ₘ right) :: Γ) ⊢ₘ[T]
        candidate ≐ₘ 𝒫ₘ(left) :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hPowerEquality := power_set_term_congr_of_equality
    (T := T)
    (Γ := (candidate ≐ₘ 𝒫ₘ(left)) :: (left ≐ₘ right) :: Γ)
    left right hSourceEquality
  exact Metatheory.Derives.equality_trans
    hCandidateEquality hPowerEquality

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
