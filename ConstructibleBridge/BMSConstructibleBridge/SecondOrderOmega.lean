import BMSConstructibleBridge.SecondOrderNaturalNumbers

/-!
# 图商内最小归纳对象的精确规格

归纳性与最小性均量化商模型的全部对象。自然数像是该模型自己的 ω，而不是
只有标准有限根的外部集合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOmega

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderQuotient

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def inductive_l (hℳ : Theory.Models ℳ theory_m) (i : type_l hℳ) : Prop :=
  (∃ e, (∀ x, ¬SecondOrderQuotient.mem_l hℳ x e) ∧ SecondOrderQuotient.mem_l hℳ e i) ∧
    ∀ a, SecondOrderQuotient.mem_l hℳ a i → ∃ b, SecondOrderQuotient.mem_l hℳ b i ∧
      ∀ c, SecondOrderQuotient.mem_l hℳ c b ↔ SecondOrderQuotient.mem_l hℳ c a ∨ c = a

def omega_l (hℳ : Theory.Models ℳ theory_m) (o : type_l hℳ) : Prop :=
  inductive_l hℳ o ∧ ∀ i, inductive_l hℳ i →
    ∀ x, SecondOrderQuotient.mem_l hℳ x o → SecondOrderQuotient.mem_l hℳ x i

theorem inductive_iff_l (hℳ : Theory.Models ℳ theory_m) (I : SecondOrderGraph.code_l ℳ) :
    inductive_l hℳ (mk_l hℳ I) ↔ SecondOrderNaturalNumbers.inductive_l I := by
  constructor
  · rintro ⟨⟨e, he, he₁⟩, h⟩
    obtain ⟨E, rfl⟩ := surj_l hℳ e
    refine ⟨⟨E, fun A => he (mk_l hℳ A), he₁⟩, ?_⟩
    intro A hA
    obtain ⟨b, hb, h₁⟩ := h (mk_l hℳ A) hA
    obtain ⟨B, rfl⟩ := surj_l hℳ b
    exact ⟨B, hb, fun C => (h₁ (mk_l hℳ C)).trans (or_congr Iff.rfl (eq_iff_l hℳ C A))⟩
  · rintro ⟨⟨E, hE, he⟩, h⟩
    refine ⟨⟨mk_l hℳ E, ?_, he⟩, ?_⟩
    · intro x
      obtain ⟨X, rfl⟩ := surj_l hℳ x
      exact hE X
    · intro a ha
      obtain ⟨A, rfl⟩ := surj_l hℳ a
      obtain ⟨B, hb, h₁⟩ := h A ha
      refine ⟨mk_l hℳ B, hb, fun c => ?_⟩
      obtain ⟨C, rfl⟩ := surj_l hℳ c
      exact (h₁ C).trans (or_congr Iff.rfl (eq_iff_l hℳ C A).symm)

theorem range_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a b, SecondOrderPairing.relation_l R a b ↔ SecondOrderOrder.lt_l a b)
    (Ω : SecondOrderGraph.code_l ℳ)
    (hΩ : ∀ A, SecondOrderGraph.mem_l A Ω ↔ ∃ n,
      SecondOrderGraph.eq_l A (SecondOrderNaturalGraph.code_l hℳ R hR n)) :
    omega_l hℳ (mk_l hℳ Ω) := by
  refine ⟨(inductive_iff_l hℳ Ω).mpr
    (SecondOrderNaturalNumbers.range_inductive_l hℳ R hR Ω hΩ), ?_⟩
  intro i hi x hx
  obtain ⟨I, rfl⟩ := surj_l hℳ i
  obtain ⟨X, rfl⟩ := surj_l hℳ x
  exact SecondOrderNaturalNumbers.least_l hℳ R hR Ω hΩ I ((inductive_iff_l hℳ I).mp hi) X hx

theorem exists_l (hℳ : Theory.Models ℳ theory_m) : ∃ o, omega_l hℳ o := by
  obtain ⟨R, hR⟩ := SecondOrderNaturalGraph.relation_exists_l hℳ
  obtain ⟨Ω, hΩ⟩ := SecondOrderNaturalNumbers.range_l hℳ R hR
  exact ⟨mk_l hℳ Ω, range_l hℳ R hR Ω hΩ⟩

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {o p : type_l hℳ}
    (ho : omega_l hℳ o) (hp : omega_l hℳ p) : o = p :=
  SecondOrderQuotient.ext_l hℳ o p (fun x => ⟨ho.2 p hp.1 x, hp.2 o ho.1 x⟩)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOmega
