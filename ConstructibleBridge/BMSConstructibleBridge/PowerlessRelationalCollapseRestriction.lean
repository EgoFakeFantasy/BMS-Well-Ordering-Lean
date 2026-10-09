import BMSConstructibleBridge.PowerlessRelationalCollapseExtensionBound
import BMSConstructibleBridge.SecondOrderFunctionRestriction
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseRestriction

/-! # 一般关系坍缩在封闭子域上的实际限制

纯隶属 ℒ，原 Z₂。由原二阶理解产生同一 H 的实际限制 F，
不用 H/F 的 Class 资格，也不用 Collection。子域的前驱封闭使其
满足一般关系的原局部检查器；限制图进入类或共同层仍需另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseRestriction

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem closed_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (A I E : Term ℒ Γ Δ .set) : (PowerlessRelationalCollapsePartial.closed_m A I E).satisfies η ↔
      ∀ x, mem_l hℳ x (E.eval η) → ∀ a, mem_l hℳ a (I.eval η) →
        SecondOrderFunctionObjects.value_l hℳ (A.eval η) a x → mem_l hℳ a (E.eval η) := by
  simp only [PowerlessRelationalCollapsePartial.closed_m, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    Term.eval_weakenBound, Term.eval]
  rfl

theorem exists_l {A I E T H : Raw}
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hSub : ∀ x, mem_l hℳ x E → mem_l hℳ x I)
    (hClosed : ∀ x, mem_l hℳ x E → ∀ a, mem_l hℳ a I →
      SecondOrderFunctionObjects.value_l hℳ A a x → mem_l hℳ a E) :
    ∃ F, PowerlessRelationalCollapsePartial.partial_l A I E T F ∧
      ∀ x y, SecondOrderFunctionObjects.value_l hℳ F x y ↔
        mem_l hℳ x E ∧ SecondOrderFunctionObjects.value_l hℳ H x y := by
  obtain ⟨F, hF, hRead⟩ := SecondOrderFunctionRestriction.exists_l hℳ hH.2.1 hSub
  exact ⟨F, PowerlessRelationalCollapseExtensionBound.restriction_l hH hSub hClosed hF hRead, hRead⟩

def result_m {Γ Δ : SortContext ℒ} (A I E T H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj
    (PowerlessRelationalCollapsePartial.partial_m (up A) (up I) (up E) (up T) (.bvar .here))
    (PowerlessRelativeMembershipCollapseRestriction.restriction_m (up E) (up H) (.bvar .here))

theorem result_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (A I E T H : Term ℒ Γ Δ .set) : (result_m A I E T H).satisfies η ↔
      ∃ F, PowerlessRelationalCollapsePartial.partial_l (A.eval η) (I.eval η) (E.eval η) (T.eval η) F ∧
        ∀ x y, SecondOrderFunctionObjects.value_l hℳ F x y ↔
          mem_l hℳ x (E.eval η) ∧ SecondOrderFunctionObjects.value_l hℳ (H.eval η) x y := by
  simp only [result_m, Formula.satisfies, PowerlessRelationalCollapsePartial.formula_l,
    PowerlessRelativeMembershipCollapseRestriction.restriction_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (A I E T H : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
    .imp (PowerlessRelativeMembershipCollapsePartial.subset_m E I) <|
      .imp (PowerlessRelationalCollapsePartial.closed_m A I E) (result_m A I E T H)

def sentence_m {Δ : SortContext ℒ} (A I E T H : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m A I E T H)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (A I E T H : Term ℒ [] Δ .set) : (sentence_m A I E T H).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, result_formula_l, SecondOrderCollapseSyntax.formula_l,
    PowerlessRelativeMembershipCollapsePartial.subset_m, closed_formula_l,
    Formula.LevyBound.boundedForall, Formula.LevyBound.membership, membershipLevyBound,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval]
  exact fun hH hSub hClosed => exists_l (hℳ := hℳ) hH hSub hClosed

theorem derives_m {Δ : SortContext ℒ} (A I E T H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m A I E T H)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ A I E T H)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseRestriction
