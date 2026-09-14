import BMSConstructibleBridge.SecondOrderEnumeration
import BMSConstructibleBridge.SecondOrderMixedImage
import BMSConstructibleBridge.SecondOrderNaturalNumbers
import BMSConstructibleBridge.SecondOrderFunctionObjects

/-!
# 任意模型图商中对象的内部可数性

同一成员的原根表示统一取最小编号，再将选根关系转换为真正的集合函数图。
目标自然数对象覆盖模型全部数域；不将外部可数性或外部函数图当作内部证书。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCountability

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b)
    (Ω A : SecondOrderGraph.code_l ℳ)
    (hΩ : ∀ B, SecondOrderGraph.mem_l B Ω ↔ ∃ n,
      SecondOrderGraph.eq_l B (SecondOrderNaturalGraph.code_l hℳ R hR n)) :
    ∃ f : SecondOrderQuotient.type_l hℳ,
      SecondOrderFunctionObjects.map_l hℳ f (SecondOrderQuotient.mk_l hℳ A)
        (SecondOrderQuotient.mk_l hℳ Ω) ∧ SecondOrderFunctionObjects.injective_l hℳ f := by
  obtain ⟨S, hS⟩ := SecondOrderEnumeration.exists_l hℳ A.real A.root
  have h₀ : ∀ a n, relation_l S a n → SecondOrderDomain.wf_l A.real a ∧ SecondOrderDomain.wf_l R n := by
    intro a n h
    exact ⟨SecondOrderDomain.child_l hℳ A.real A.root a A.wf ((hS a n).mp h).1,
      SecondOrderNaturalGraph.wf_l hℳ R hR n⟩
  let N (n : num_l ℳ) := SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR n)
  let C (a n : num_l ℳ) (h : relation_l S a n) :=
    SecondOrderQuotient.mk_l hℳ (SecondOrderGraph.child_l hℳ A a ((hS a n).mp h).1)
  obtain ⟨f, hf⟩ := SecondOrderMixedImage.exists_l hℳ A.real R S h₀
  have hF : ∀ p, SecondOrderQuotient.mem_l hℳ p f ↔ ∃ a n, ∃ h : relation_l S a n,
      SecondOrderPairObjects.ordered_l hℳ (C a n h) (N n) p := hf
  have h₁ : ∀ x y, SecondOrderFunctionObjects.value_l hℳ f x y ↔
      ∃ a n, ∃ h : relation_l S a n, x = C a n h ∧ y = N n := by
    intro x y
    constructor
    · rintro ⟨p, hp, h⟩
      obtain ⟨a, n, h₂, h₃⟩ := (hF p).mp hp
      exact ⟨a, n, h₂, (SecondOrderPairObjects.ordered_eq_l hℳ h h₃).mp rfl⟩
    · rintro ⟨a, n, h, rfl, rfl⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (C a n h) (N n)
      exact ⟨p, (hF p).mpr ⟨a, n, h, hp⟩, hp⟩
  have h₂ (n : num_l ℳ) : SecondOrderQuotient.mem_l hℳ (N n) (SecondOrderQuotient.mk_l hℳ Ω) :=
    (hΩ _).mpr ⟨n, SecondOrderGraph.refl_l hℳ _⟩
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨a, n, h, h₃⟩ := (hF p).mp hp
    exact ⟨C a n h, N n, SecondOrderGraph.child_mem_l hℳ A a ((hS a n).mp h).1, h₂ n, h₃⟩
  · intro x hx
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    obtain ⟨a, ha, h⟩ := hx
    obtain ⟨n, hn⟩ := SecondOrderEnumeration.total_l hℳ A.real A.root a ha
    have h₃ := (hS a n).mpr hn
    have h₄ : SecondOrderQuotient.mk_l hℳ X = C a n h₃ :=
      (SecondOrderQuotient.eq_iff_l hℳ X _).mpr h
    refine ⟨N n, ⟨h₂ n, (h₁ _ _).mpr ⟨a, n, h₃, h₄, rfl⟩⟩, ?_⟩
    rintro y ⟨_, hy⟩
    obtain ⟨b, m, h₅, h₆, h₇⟩ := (h₁ _ _).mp hy
    have h₈ : SecondOrderBisimulation.eq_l A.real A.real a b :=
      (SecondOrderQuotient.eq_iff_l hℳ _ _).mp (h₄.symm.trans h₆)
    have h₉ := SecondOrderEnumeration.congr_l hℳ A.real A.root a b n m h₈ hn ((hS b m).mp h₅)
    exact h₇.trans (congrArg N h₉.symm)
  · intro x z y hx hz
    obtain ⟨a, n, ha, hx, hy⟩ := (h₁ x y).mp hx
    obtain ⟨b, m, hb, hz, hy₁⟩ := (h₁ z y).mp hz
    have h₃ : n = m := (SecondOrderNaturalNumbers.eq_l hℳ R hR n m).mp
      ((SecondOrderQuotient.eq_iff_l hℳ _ _).mp (hy.symm.trans hy₁))
    have h₄ := (SecondOrderEnumeration.eq_iff_l hℳ A.real A.root a b n m
      ((hS a n).mp ha) ((hS b m).mp hb)).mpr h₃
    have h₅ : C a n ha = C b m hb := (SecondOrderQuotient.eq_iff_l hℳ _ _).mpr h₄
    exact hx.trans (h₅.trans hz.symm)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCountability
