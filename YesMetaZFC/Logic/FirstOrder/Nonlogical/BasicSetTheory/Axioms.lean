import YesMetaZFC.Logic.FirstOrder.Admissibility
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Language
/-!
# 基本集合论的首组非逻辑公理
外延性、子集定义与真子集定义在这里作为真实理论公理进入 `Derives`。公式参数先
以 free 变量书写，再由 `Formula.forall_close` 统一关闭；定义体内部的成员变量直接
使用 locally nameless 的当前 bound 变量，不传播文献中的机械变量避让约定。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-- 两个集合具有完全相同的元素。参数应是 bound-closed 项。 -/
def membership_agreement (left right : SetTerm) : SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ left) ↔ₘ (bₛ#0 ∈ₘ right)
/-- 等式推出成员外延一致。 -/
def equality_to_agreement (left right : SetTerm) : SetFormula := (left ≐ₘ right) ⟶ₘ membership_agreement left right
/-- 成员外延一致推出等式。 -/
def agreement_to_equality (left right : SetTerm) : SetFormula :=
  membership_agreement left right ⟶ₘ (left ≐ₘ right)
/-- 外延公理的开放双变量实例。 -/
def extensionality_instance (left right : SetTerm) : SetFormula :=
  agreement_to_equality left right
/-- 外延公理。 -/
def extensionality_axiom : SetFormula :=
  Metatheory.Formula.forall_close
    [(SetSort.set, 0), (SetSort.set, 1)] (extensionality_instance (x#0) (x#1))
/-- 子集关系的成员条件。参数应是 bound-closed 项。 -/
def subset_condition (left right : SetTerm) : SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ left) ⟶ₘ (bₛ#0 ∈ₘ right)
/-- 子集定义公理的开放双变量实例。 -/
def subset_definition_instance (left right : SetTerm) : SetFormula := (left ⊆ₘ right) ↔ₘ subset_condition left right
/-- 子集关系符号的定义公理。 -/
def subset_definition_axiom : SetFormula :=
  Metatheory.Formula.forall_close
    [(SetSort.set, 0), (SetSort.set, 1)] (subset_definition_instance (x#0) (x#1))
/-- 真子集关系的成员条件。参数应是 bound-closed 项。 -/
def proper_subset_condition (left right : SetTerm) : SetFormula := (left ⊆ₘ right) ∧ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ right) ∧ₘ ¬ₘ (bₛ#0 ∈ₘ left))
/-- 真子集定义公理的开放双变量实例。 -/
def proper_subset_definition_instance (left right : SetTerm) : SetFormula := (left ⊂ₘ right) ↔ₘ proper_subset_condition left right
/-- 真子集关系符号的定义公理。 -/
def proper_subset_definition_axiom : SetFormula :=
  Metatheory.Formula.forall_close
    [(SetSort.set, 0), (SetSort.set, 1)] (proper_subset_definition_instance (x#0) (x#1))
/-- 只含外延公理的首个具体理论。 -/
def extensionality_theory : SetTheory :=
  Theory.singleton extensionality_axiom
/-- 在外延理论上加入子集定义公理。 -/
def subset_theory : SetTheory :=
  Theory.insert subset_definition_axiom extensionality_theory
/-- 在子集理论上再加入真子集定义公理。 -/
def proper_subset_theory : SetTheory :=
  Theory.insert proper_subset_definition_axiom subset_theory
theorem extensionality_axiom_admissible :
    Formula.Admissible extensionality_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem subset_definition_axiom_admissible :
    Formula.Admissible subset_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem proper_subset_definition_axiom_admissible :
    Formula.Admissible proper_subset_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem extensionality_theory_admissible :
    Theory.Admissible extensionality_theory := by
  intro formula hFormula
  rw [extensionality_theory, Theory.singleton] at hFormula
  subst formula
  exact extensionality_axiom_admissible
theorem subset_theory_admissible :
    Theory.Admissible subset_theory :=
  Theory.admissible_insert
    subset_definition_axiom_admissible
    extensionality_theory_admissible
theorem proper_subset_theory_admissible :
    Theory.Admissible proper_subset_theory :=
  Theory.admissible_insert
    proper_subset_definition_axiom_admissible
    subset_theory_admissible
/-- 外延理论中的公理均为闭公式。 -/
@[derive_close_sentence]
theorem extensionality_theory_sentence
    {formula : SetFormula} (hFormula : extensionality_theory formula) :
    Formula.Sentence formula := by
  rw [extensionality_theory, Theory.singleton] at hFormula
  subst formula
  constructor
  · exact extensionality_axiom_admissible
  · native_decide
/-- 子集理论中的公理均为闭公式。 -/
@[derive_close_sentence]
theorem subset_theory_sentence
    {formula : SetFormula} (hFormula : subset_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact subset_definition_axiom_admissible
    · native_decide
  · exact extensionality_theory_sentence hFormula
/-- 真子集理论中的公理均为闭公式。 -/
@[derive_close_sentence]
theorem proper_subset_theory_sentence
    {formula : SetFormula} (hFormula : proper_subset_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact proper_subset_definition_axiom_admissible
    · native_decide
  · exact subset_theory_sentence hFormula
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
