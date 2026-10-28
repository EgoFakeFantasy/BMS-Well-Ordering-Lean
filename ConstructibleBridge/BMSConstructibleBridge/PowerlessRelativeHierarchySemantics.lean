import BMSConstructibleBridge.PowerlessRelativeHierarchySyntax

/-! # 纯相对层次公式的逐参数语义

本文件只核对同一图商中的零、后继、极限与历史规格；没有使用完整源理论。
层次存在性及两套定义的等价仍须由实际集合函数构造和内部归纳提供。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeHierarchySemantics

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) := SecondOrderQuotient.structure_l hℳ

def empty_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (a : type_l hℳ) : Prop := ∀ x, ¬mem_l hℳ x a

def successor_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (a b : type_l hℳ) : Prop := ∀ x, mem_l hℳ x b ↔ mem_l hℳ x a ∨ x = a

def limit_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (a : type_l hℳ) : Prop :=
  (∃ x, mem_l hℳ x a) ∧ ∀ x, mem_l hℳ x a → ∃ y, mem_l hℳ y a ∧ mem_l hℳ x y

def union_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (f a c : type_l hℳ) : Prop :=
  ∀ x, mem_l hℳ x c ↔ ∃ b d, mem_l hℳ b a ∧ SecondOrderFunctionObjects.value_l hℳ f b d ∧ mem_l hℳ x d

def successor_step_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (f a c : type_l hℳ) : Prop :=
  ∃ b d, successor_l hℳ b a ∧ SecondOrderFunctionObjects.value_l hℳ f b d ∧ SecondOrderMemberDef.spec_l hℳ d c

def step_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B f a c : type_l hℳ) : Prop :=
  (empty_l hℳ a ∧ c = B) ∨ successor_step_l hℳ f a c ∨ (limit_l hℳ a ∧ union_l hℳ f a c)

def history_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B A f r : type_l hℳ) : Prop :=
  SecondOrderFunctionObjects.map_l hℳ f A r ∧ ∀ a c,
    mem_l hℳ a A ∧ SecondOrderFunctionObjects.value_l hℳ f a c → step_l hℳ B f a c

def level_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B a c : type_l hℳ) : Prop :=
  ∃ A f r, SetTheory.Structure.IsOrdinal
    (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (quotient_l hℳ)) A ∧
      mem_l hℳ a A ∧ history_l hℳ B A f r ∧ SecondOrderFunctionObjects.value_l hℳ f a c

theorem empty_formula_l {Γ Δ : SortContext ℒ} (η : Env (quotient_l hℳ) Γ Δ) (a : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchySyntax.empty_m a).satisfies η ↔ empty_l hℳ (a.eval η) := by
  simp only [PowerlessRelativeHierarchySyntax.empty_m, PowerlessRelativeHierarchySyntax.up, Formula.satisfies,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval, Term.eval_weakenBound]
  rfl

theorem ordinal_formula_l {Γ Δ : SortContext ℒ} (η : Env (quotient_l hℳ) Γ Δ) (a : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchySyntax.ordinal_m a).satisfies η ↔
      SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (quotient_l hℳ)) (a.eval η) := by
  rw [PowerlessRelativeHierarchySyntax.ordinal_m, Formula.satisfies_substitute]
  have hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (quotient_l hℳ)) :=
    ⟨SecondOrderQuotient.ext_l hℳ⟩
  exact (SetTheory.Definitional.Project.FirstOrderSemantics.formula_correct hExt
    SecondOrderGraphOrdinalFormula.project_m SecondOrderGraphOrdinalFormula.project_closed_m
    (η.pullback (PowerlessRelativeHierarchySyntax.ordinal_substitution_m a))
    (fun _ => a.eval η)).trans (SetTheory.Definitional.Project.Formula.satisfies_isOrdinal_iff _
      SetTheory.Definitional.Term.newest)

theorem successor_formula_l {Γ Δ : SortContext ℒ} (η : Env (quotient_l hℳ) Γ Δ) (a b : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchySyntax.successor_m a b).satisfies η ↔ successor_l hℳ (a.eval η) (b.eval η) := by
  simp only [PowerlessRelativeHierarchySyntax.successor_m, PowerlessRelativeHierarchySyntax.up, Formula.satisfies,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval, Term.eval_weakenBound]
  rfl

theorem limit_formula_l {Γ Δ : SortContext ℒ} (η : Env (quotient_l hℳ) Γ Δ) (a : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchySyntax.limit_m a).satisfies η ↔ limit_l hℳ (a.eval η) := by
  simp only [PowerlessRelativeHierarchySyntax.limit_m, PowerlessRelativeHierarchySyntax.up, Formula.satisfies,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval, Term.eval_weakenBound]
  rfl

theorem union_formula_l {Γ Δ : SortContext ℒ} (η : Env (quotient_l hℳ) Γ Δ) (f a c : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchySyntax.union_m f a c).satisfies η ↔ union_l hℳ (f.eval η) (a.eval η) (c.eval η) := by
  simp only [PowerlessRelativeHierarchySyntax.union_m, PowerlessRelativeHierarchySyntax.up, Formula.satisfies, SecondOrderObjectSyntax.value_l hℳ,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval, Term.eval_weakenBound]
  rfl

theorem successor_step_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (quotient_l hℳ) Γ Δ) (f a c : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchySyntax.successor_step_m f a c).satisfies η ↔
      successor_step_l hℳ (f.eval η) (a.eval η) (c.eval η) := by
  simp only [PowerlessRelativeHierarchySyntax.successor_step_m, Formula.satisfies, successor_formula_l,
    SecondOrderObjectSyntax.value_l hℳ, PowerlessMemberDefDerives.formula_l K,
    PowerlessRelativeHierarchySyntax.up, Term.eval_weakenBound, Term.eval]
  rfl

theorem step_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (quotient_l hℳ) Γ Δ) (B f a c : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchySyntax.step_m B f a c).satisfies η ↔
      step_l hℳ (B.eval η) (f.eval η) (a.eval η) (c.eval η) := by
  simp only [PowerlessRelativeHierarchySyntax.step_m, Formula.satisfies, empty_formula_l,
    successor_step_formula_l K, limit_formula_l, union_formula_l]
  rfl

theorem history_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (quotient_l hℳ) Γ Δ) (B A f r : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchySyntax.history_m B A f r).satisfies η ↔
      history_l hℳ (B.eval η) (A.eval η) (f.eval η) (r.eval η) := by
  simp only [PowerlessRelativeHierarchySyntax.history_m, Formula.satisfies, SecondOrderObjectSyntax.map_l hℳ,
    SecondOrderObjectSyntax.value_l hℳ, step_formula_l K, SecondOrderObjectSyntax.member_m,
    PowerlessRelativeHierarchySyntax.up, Arguments.eval, Term.eval, Term.eval_weakenBound]
  rfl

theorem level_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (quotient_l hℳ) Γ Δ) (B a c : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchySyntax.level_m B a c).satisfies η ↔ level_l hℳ (B.eval η) (a.eval η) (c.eval η) := by
  simp only [PowerlessRelativeHierarchySyntax.level_m, Formula.satisfies, ordinal_formula_l,
    history_formula_l K, SecondOrderObjectSyntax.value_l hℳ, SecondOrderObjectSyntax.member_m,
    PowerlessRelativeHierarchySyntax.up, Arguments.eval, Term.eval, Term.eval_weakenBound]
  rfl

theorem class_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (quotient_l hℳ) Γ Δ) (B x : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchySyntax.class_m B x).satisfies η ↔
      ∃ a c : type_l hℳ, level_l hℳ (B.eval η) a c ∧ mem_l hℳ (x.eval η) c := by
  simp only [PowerlessRelativeHierarchySyntax.class_m, PowerlessRelativeHierarchySyntax.up,
    Formula.satisfies, level_formula_l K, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval, Term.eval_weakenBound]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeHierarchySemantics
