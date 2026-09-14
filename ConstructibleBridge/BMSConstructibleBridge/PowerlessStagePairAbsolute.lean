import BMSConstructibleBridge.PowerlessOrdinalBounded
import BMSConstructibleBridge.PowerlessStagePair

/-!
# 原极限和 proper 公式的传递子域解释

仅使用环境核心与子域传递性。原序数公式由已证有界解释处理；
其余见证都由实际成员关系取回，不要求子域满足核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStagePairAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {U : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
  (hUT : PowerlessNaturalOrder.transitive_l U)

include hℳ hUT

theorem limit_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (α : Term ℒ Γ Δ .set) :
    (PowerlessStagePair.limit_m α).satisfies η ↔ PowerlessStagePair.limit_l (α.eval η).val := by
  simp only [PowerlessStagePair.limit_m, Formula.satisfies,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  apply and_congr (PowerlessOrdinalBounded.source_l hℳ hUT η α)
  change ((∃ x : type_l U, member_l ℳ x.val (α.eval η).val) ∧
    ∀ x : type_l U, member_l ℳ x.val (α.eval η).val →
      ∃ y : type_l U, member_l ℳ y.val (α.eval η).val ∧ member_l ℳ x.val y.val) ↔ _
  constructor
  · rintro ⟨⟨x, hx⟩, h⟩
    refine ⟨⟨x.val, hx⟩, ?_⟩
    intro x hx
    obtain ⟨y, hy, hxy⟩ := h ⟨x, hUT (α.eval η).val x (α.eval η).property hx⟩ hx
    exact ⟨y.val, hy, hxy⟩
  · rintro ⟨⟨x, hx⟩, h⟩
    refine ⟨⟨⟨x, hUT (α.eval η).val x (α.eval η).property hx⟩, hx⟩, ?_⟩
    intro x hx
    obtain ⟨y, hy, hxy⟩ := h x.val hx
    exact ⟨⟨y, hUT (α.eval η).val y (α.eval η).property hy⟩, hy, hxy⟩

theorem proper_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w α β : Term ℒ Γ Δ .set) :
    (PowerlessStagePair.proper_m w α β).satisfies η ↔
      PowerlessStagePair.proper_l (w.eval η).val (α.eval η).val (β.eval η).val :=
  and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr (limit_l hℳ hUT η α) (limit_l hℳ hUT η β)))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStagePairAbsolute
