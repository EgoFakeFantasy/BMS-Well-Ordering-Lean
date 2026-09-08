import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.BasicFiniteTheory
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure

/-!
# 无穷公理与最小归纳集

本模块用内在类型语法定义归纳集、归纳核与 `ω`。归纳核的存在性采用参数化分离
schema，闭定义公理直接产出 `SetSentence`，不再维护变量编号、admissibility、
检查证书或闭句证明链。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 无穷公理与归纳集 -/

def infinity_condition {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  (∅ₘ ∈ₘ set) ∧ₘ
    ((element ∈ₘ set.weakenFree SetSort.set ⟶ₘ
      (Sₘ(element) ∈ₘ set.weakenFree SetSort.set)).forallFreeTop SetSort.set)

def infinity_axiom : SetSentence :=
  let free := [SetSort.set]
  let set : SetOpenTerm free := .fvar .here
  (infinity_condition set).existsFreeTop SetSort.set

def is_inductive_set_condition {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  infinity_condition set

def is_inductive_set_definition_instance {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  is_inductive_set_formula set ↔ₘ is_inductive_set_condition set

def is_inductive_set_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_inductive_set_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set]))

/-! ## 归纳核 -/

def inductive_core_member_condition {bound free : SetContext}
    (source element : SetTerm bound free) : SetFormula bound free :=
  let inductiveSet : SetTerm bound (SetSort.set :: free) := .fvar .here
  (element ∈ₘ source) ∧ₘ
    ((is_inductive_set_formula inductiveSet ⟶ₘ
      (element.weakenFree SetSort.set ∈ₘ inductiveSet)).forallFreeTop SetSort.set)

def inductive_core_spec {bound free : SetContext}
    (source candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    (inductive_core_member_condition
      (source.weakenFree SetSort.set) element)

def inductive_core_separation_exists {bound free : SetContext}
    (source : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (inductive_core_spec
    (source.weakenFree SetSort.set) candidate).existsFreeTop SetSort.set

def inductive_core_predicate {free : SetContext}
    (source : SetOpenTerm free) : SetPredicate free where
  body :=
    let element : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    (inductive_core_member_condition
      (source.weakenFree SetSort.set) element).abstractFreeTop

def inductive_core_definition_instance {bound free : SetContext}
    (source candidate : SetTerm bound free) : SetFormula bound free :=
  is_inductive_set_formula source ⟶ₘ
    ((candidate ≐ₘ coreₘ(source)) ↔ₘ
      inductive_core_spec source candidate)

def inductive_core_definition_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set]
  let source : SetOpenTerm free := .fvar (.there .here)
  let candidate : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (inductive_core_definition_instance source candidate)

/-! ## 常元 `ω` -/

def least_inductive_member_condition {bound free : SetContext}
    (element : SetTerm bound free) : SetFormula bound free :=
  let inductiveSet : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((is_inductive_set_formula inductiveSet ⟶ₘ
      (element.weakenFree SetSort.set ∈ₘ inductiveSet)).forallFreeTop SetSort.set)

def least_inductive_spec {bound free : SetContext}
    (candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    (least_inductive_member_condition element)

def omega_spec {bound free : SetContext}
    (candidate : SetTerm bound free) : SetFormula bound free :=
  is_inductive_set_formula candidate ∧ₘ
    (coreₘ(candidate) ≐ₘ candidate)

def omega_definition_instance {bound free : SetContext}
    (candidate : SetTerm bound free) : SetFormula bound free :=
  (candidate ≐ₘ ωₘ) ↔ₘ omega_spec candidate

def omega_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (omega_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set]))

/-! ## 理论组合 -/

def infinity_axiom_theory : SetTheory :=
  Theory.insert infinity_axiom basic_finite_theory

def inductive_set_theory : SetTheory :=
  Theory.insert is_inductive_set_definition_axiom infinity_axiom_theory

def inductive_core_separation_theory : SetTheory :=
  fun sentence =>
    (∃ (free : SetContext) (source : SetOpenTerm free),
      sentence = (inductive_core_predicate source).separation_axiom) ∨
    inductive_set_theory sentence

def inductive_core_theory : SetTheory :=
  Theory.insert inductive_core_definition_axiom
    inductive_core_separation_theory

def inductive_core_base_theory : SetTheory :=
  fun sentence =>
    (∃ (free : SetContext) (source : SetOpenTerm free),
      sentence = (inductive_core_predicate source).separation_axiom) ∨
    Theory.insert is_inductive_set_definition_axiom
      (Theory.insert infinity_axiom extensionality_theory) sentence

def omega_base_theory : SetTheory :=
  Theory.insert inductive_core_definition_axiom
    (Theory.insert is_inductive_set_definition_axiom
      (Theory.insert infinity_axiom extensionality_theory))

def omega_operator_theory : SetTheory :=
  Theory.insert omega_definition_axiom omega_base_theory

def infinity_theory : SetTheory :=
  Theory.insert omega_definition_axiom inductive_core_theory

/-! ## `ω` 的定义实例与有限 numeral -/

private theorem infinity_inductive_set_axiom_derives :
    ([] : Context signature []) ⊢ₘ[infinity_theory]
      Formula.fromSentence is_inductive_set_definition_axiom :=
  FirstOrder.Derives.theory_axiom (by
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))

private theorem infinity_omega_axiom_derives :
    ([] : Context signature []) ⊢ₘ[infinity_theory]
      Formula.fromSentence omega_definition_axiom :=
  FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)

/-- 归纳集定义可在任意开放上下文中直接实例化。 -/
theorem infinity_inductive_set_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (set : SetOpenTerm free) :
    Γ ⊢ₘ[infinity_theory]
      is_inductive_set_definition_instance set := by
  let body : SetOpenFormula [SetSort.set] :=
    is_inductive_set_definition_instance (.fvar .here)
  let τ : VariableSubstitution signature [SetSort.set] [] free :=
    VariableSubstitution.cons set VariableSubstitution.empty
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ (by
      simpa [is_inductive_set_definition_axiom, body] using
        infinity_inductive_set_axiom_derives)
  simpa [body, τ, is_inductive_set_definition_instance,
    is_inductive_set_condition, infinity_condition,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftFree,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.boundId] using hInstance

/-- `ω` 定义可在任意开放上下文中直接实例化。 -/
theorem infinity_omega_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (candidate : SetOpenTerm free) :
    Γ ⊢ₘ[infinity_theory]
      omega_definition_instance candidate := by
  let body : SetOpenFormula [SetSort.set] :=
    omega_definition_instance (.fvar .here)
  let τ : VariableSubstitution signature [SetSort.set] [] free :=
    VariableSubstitution.cons candidate VariableSubstitution.empty
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ (by
      simpa [omega_definition_axiom, body] using
        infinity_omega_axiom_derives)
  simpa [body, τ, omega_definition_instance, omega_spec,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftFree,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.boundId] using hInstance

/-- `ω` 满足归纳集谓词。 -/
theorem infinity_omega_inductive_derives
    {free : SetContext} {Γ : Context signature free} :
    Γ ⊢ₘ[infinity_theory] is_inductive_set_formula ωₘ := by
  have hSpec : Γ ⊢ₘ[infinity_theory] omega_spec ωₘ :=
    FirstOrder.Derives.iff_elim_left
      (infinity_omega_definition_instance_derives ωₘ)
      (Metatheory.Derives.equality_refl ωₘ)
  exact FirstOrder.Derives.conj_elim_left hSpec

/-- `ω` 的归纳闭包展开为零和后继两部分。 -/
theorem infinity_omega_inductive_condition_derives
    {free : SetContext} {Γ : Context signature free} :
    Γ ⊢ₘ[infinity_theory] infinity_condition ωₘ :=
  FirstOrder.Derives.iff_elim_left
    (infinity_inductive_set_definition_instance_derives ωₘ)
    infinity_omega_inductive_derives

/-- 零属于 `ω`。 -/
theorem infinity_zero_mem_omega
    {free : SetContext} {Γ : Context signature free} :
    Γ ⊢ₘ[infinity_theory] (∅ₘ : SetOpenTerm free) ∈ₘ ωₘ :=
  FirstOrder.Derives.conj_elim_left
    infinity_omega_inductive_condition_derives

/-- `ω` 对后继封闭。 -/
theorem infinity_successor_mem_omega
    {free : SetContext} {Γ : Context signature free}
    (number : SetOpenTerm free)
    (hNumber : Γ ⊢ₘ[infinity_theory] number ∈ₘ ωₘ) :
    Γ ⊢ₘ[infinity_theory] Sₘ(number) ∈ₘ ωₘ := by
  have hClosure := FirstOrder.Derives.conj_elim_right
    (infinity_omega_inductive_condition_derives
      (free := free) (Γ := Γ))
  have hInstance := FirstOrder.Derives.forall_elim
    (term := number) hClosure
  simpa [infinity_condition] using!
    FirstOrder.Derives.imp_elim hInstance hNumber

/-- 每个外部有限 numeral 都属于 `ω`。 -/
theorem infinity_finite_numeral_mem_omega
    {free : SetContext} {Γ : Context signature free}
    (number : Nat) :
    Γ ⊢ₘ[infinity_theory]
      (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ := by
  induction number with
  | zero =>
      exact infinity_zero_mem_omega
  | succ number ih =>
      simpa [finite_numeral_term] using
        infinity_successor_mem_omega
          (numₘ(number) : SetOpenTerm free) ih

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
