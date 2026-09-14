import BMSConstructibleBridge.SecondOrderCollapseGraph
import BMSConstructibleBridge.SecondOrderRegularRelation

/-!
# 内部集合坍缩函数的满射和递归方程

函数在原关系域域上取图根商值，其值域传递且恰为该函数的像。递归方程只
使用实际集合函数求值，允许不同节点坍缩到同一对象，不假定原关系外延。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCollapseFunction

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def spec_l (hℳ : Theory.Models ℳ theory_m) (a d u f : SecondOrderQuotient.type_l hℳ) : Prop :=
  (∀ b c, SecondOrderQuotient.mem_l hℳ b u → SecondOrderQuotient.mem_l hℳ c b →
    SecondOrderQuotient.mem_l hℳ c u) ∧
  SecondOrderFunctionObjects.map_l hℳ f d u ∧
  (∀ y, SecondOrderQuotient.mem_l hℳ y u → ∃ x, SecondOrderQuotient.mem_l hℳ x d ∧
    SecondOrderFunctionObjects.value_l hℳ f x y) ∧
  ∀ k y, SecondOrderQuotient.mem_l hℳ k d → SecondOrderFunctionObjects.value_l hℳ f k y →
    ∀ x, SecondOrderQuotient.mem_l hℳ x y ↔ ∃ j, SecondOrderQuotient.mem_l hℳ j d ∧
      SecondOrderFunctionObjects.value_l hℳ a j k ∧ SecondOrderFunctionObjects.value_l hℳ f j x

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R S : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b)
    (hS : ∀ n, SecondOrderDomain.wf_l S n) (A D : SecondOrderQuotient.type_l hℳ)
    (hA : ∀ a b, relation_l S a b ↔ SecondOrderFunctionObjects.value_l hℳ A
      (SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR a))
      (SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR b)))
    (hD : ∀ x, SecondOrderQuotient.mem_l hℳ x D ↔ ∃ n, SecondOrderCollapseGraph.field_l S n ∧
      x = SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR n)) :
    ∃ u f, spec_l hℳ A D u f := by
  let N (n : num_l ℳ) := SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR n)
  let C (n : num_l ℳ) := SecondOrderQuotient.mk_l hℳ (SecondOrderCollapseGraph.code_l S hS n)
  obtain ⟨U, hU, hT⟩ := SecondOrderCollapseGraph.range_l hℳ S hS
  have h₀ : ∀ x, SecondOrderQuotient.mem_l hℳ x (SecondOrderQuotient.mk_l hℳ U) ↔
      ∃ n, SecondOrderCollapseGraph.field_l S n ∧ x = C n := by
    intro x
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact (hU X).trans (exists_congr (fun n => and_congr Iff.rfl
      (SecondOrderQuotient.eq_iff_l hℳ X (SecondOrderCollapseGraph.code_l S hS n)).symm))
  have h₁ : ∀ x n, SecondOrderQuotient.mem_l hℳ x (C n) ↔
      ∃ m, relation_l S m n ∧ x = C m := by
    intro x n
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    change (∃ m, relation_l S m n ∧ SecondOrderBisimulation.eq_l X.real S X.root m) ↔ _
    exact exists_congr (fun m => and_congr Iff.rfl
      (SecondOrderQuotient.eq_iff_l hℳ X (SecondOrderCollapseGraph.code_l S hS m)).symm)
  have h₂ (n m : num_l ℳ) (h : N n = N m) : n = m :=
    (SecondOrderNaturalNumbers.eq_l hℳ R hR n m).mp ((SecondOrderQuotient.eq_iff_l hℳ _ _).mp h)
  obtain ⟨f, hf⟩ := SecondOrderCollapseGraph.graph_l hℳ R S hR hS
  have h₃ : ∀ x y, SecondOrderFunctionObjects.value_l hℳ f x y ↔
      ∃ n, SecondOrderCollapseGraph.field_l S n ∧ x = N n ∧ y = C n := by
    intro x y
    constructor
    · rintro ⟨p, hp, h⟩
      obtain ⟨n, hn, h₄⟩ := (hf p).mp hp
      exact ⟨n, hn, (SecondOrderPairObjects.ordered_eq_l hℳ h h₄).mp rfl⟩
    · rintro ⟨n, hn, rfl, rfl⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (N n) (C n)
      exact ⟨p, (hf p).mpr ⟨n, hn, hp⟩, hp⟩
  refine ⟨SecondOrderQuotient.mk_l hℳ U, f, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro b c hb hc
    obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ b
    obtain ⟨C, rfl⟩ := SecondOrderQuotient.surj_l hℳ c
    exact hT B C hb hc
  · intro p hp
    obtain ⟨n, hn, h⟩ := (hf p).mp hp
    exact ⟨N n, C n, (hD _).mpr ⟨n, hn, rfl⟩, (h₀ _).mpr ⟨n, hn, rfl⟩, h⟩
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := (hD x).mp hx
    refine ⟨C n, ⟨(h₀ _).mpr ⟨n, hn, rfl⟩, (h₃ _ _).mpr ⟨n, hn, rfl, rfl⟩⟩, ?_⟩
    rintro y ⟨_, hy⟩
    obtain ⟨m, _, h, hy⟩ := (h₃ _ _).mp hy
    exact hy.trans (congrArg C (h₂ n m h).symm)
  · intro y hy
    obtain ⟨n, hn, rfl⟩ := (h₀ y).mp hy
    exact ⟨N n, (hD _).mpr ⟨n, hn, rfl⟩, (h₃ _ _).mpr ⟨n, hn, rfl, rfl⟩⟩
  · intro k y _ hy x
    obtain ⟨n, _, rfl, rfl⟩ := (h₃ k y).mp hy
    rw [h₁]
    constructor
    · rintro ⟨m, hm, rfl⟩
      have h : SecondOrderCollapseGraph.field_l S m := ⟨n, Or.inl hm⟩
      exact ⟨N m, (hD _).mpr ⟨m, h, rfl⟩, (hA m n).mp hm, (h₃ _ _).mpr ⟨m, h, rfl, rfl⟩⟩
    · rintro ⟨j, _, hj, hx⟩
      obtain ⟨m, _, rfl, rfl⟩ := (h₃ j x).mp hx
      exact ⟨m, (hA m n).mpr hj, rfl⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCollapseFunction
