import BMSConstructibleBridge.SecondOrderNaturalSubsets
import BMSConstructibleBridge.SecondOrderRelationDecode

/-!
# 内部正则关系的数图根域

集合论关系的正则性指其域域上每个非空内部子集有极小元。若解码后的数图
有内部下降链，其数值像本身是内部集合，直接违反正则性；不使用外部 Acc。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRegularRelation

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def field_l (hℳ : Theory.Models ℳ theory_m) (a o x : SecondOrderQuotient.type_l hℳ) : Prop :=
  SecondOrderQuotient.mem_l hℳ x o ∧ ∃ y, SecondOrderQuotient.mem_l hℳ y o ∧
    (SecondOrderFunctionObjects.value_l hℳ a x y ∨ SecondOrderFunctionObjects.value_l hℳ a y x)

def regular_l (hℳ : Theory.Models ℳ theory_m) (a o : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∀ d, (∃ x, SecondOrderQuotient.mem_l hℳ x d) →
    (∀ x, SecondOrderQuotient.mem_l hℳ x d → field_l hℳ a o x) →
    ∃ y, SecondOrderQuotient.mem_l hℳ y d ∧
      ∀ x, SecondOrderQuotient.mem_l hℳ x d → ¬SecondOrderFunctionObjects.value_l hℳ a x y

def relation_l (hℳ : Theory.Models ℳ theory_m) (a o : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∀ p, SecondOrderQuotient.mem_l hℳ p a → ∃ x y,
    SecondOrderQuotient.mem_l hℳ x o ∧ SecondOrderQuotient.mem_l hℳ y o ∧
      SecondOrderPairObjects.ordered_l hℳ x y p

/-- 原关系的定义域与值域之并，不在此定义中预加 ω 限制。 -/
def domain_l (hℳ : Theory.Models ℳ theory_m) (a x : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∃ y, SecondOrderFunctionObjects.value_l hℳ a x y ∨ SecondOrderFunctionObjects.value_l hℳ a y x

def wellFounded_l (hℳ : Theory.Models ℳ theory_m) (a : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∀ d, (∃ x, SecondOrderQuotient.mem_l hℳ x d) →
    (∀ x, SecondOrderQuotient.mem_l hℳ x d → domain_l hℳ a x) →
    ∃ y, SecondOrderQuotient.mem_l hℳ y d ∧
      ∀ x, SecondOrderQuotient.mem_l hℳ x d → ¬SecondOrderFunctionObjects.value_l hℳ a x y

theorem endpoints_l (hℳ : Theory.Models ℳ theory_m) (a o x y : SecondOrderQuotient.type_l hℳ)
    (ha : relation_l hℳ a o) (h : SecondOrderFunctionObjects.value_l hℳ a x y) :
    SecondOrderQuotient.mem_l hℳ x o ∧ SecondOrderQuotient.mem_l hℳ y o := by
  obtain ⟨p, hp, h⟩ := h
  obtain ⟨b, c, hb, hc, h₁⟩ := ha p hp
  obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ h h₁).mp rfl
  exact ⟨hb, hc⟩

/-- 对 ω 上真正的关系，两种域域表示完全相同。 -/
theorem field_iff_l (hℳ : Theory.Models ℳ theory_m) (a o : SecondOrderQuotient.type_l hℳ)
    (ha : relation_l hℳ a o) (x : SecondOrderQuotient.type_l hℳ) :
    field_l hℳ a o x ↔ domain_l hℳ a x := by
  constructor
  · rintro ⟨_, y, _, h⟩
    exact ⟨y, h⟩
  · rintro ⟨y, h | h⟩
    · have h₁ := endpoints_l hℳ a o x y ha h
      exact ⟨h₁.1, y, h₁.2, Or.inl h⟩
    · have h₁ := endpoints_l hℳ a o y x ha h
      exact ⟨h₁.2, y, h₁.1, Or.inr h⟩

theorem regular_iff_l (hℳ : Theory.Models ℳ theory_m) (a o : SecondOrderQuotient.type_l hℳ)
    (ha : relation_l hℳ a o) : regular_l hℳ a o ↔ wellFounded_l hℳ a := by
  unfold regular_l wellFounded_l
  simp only [field_iff_l hℳ a o ha]

/-- 原集合论正则性使每个解码根满足原无内部下降链公式。 -/
theorem wf_l (hℳ : Theory.Models ℳ theory_m) (R S : set_l ℳ)
    (hR : ∀ a b, SecondOrderPairing.relation_l R a b ↔ SecondOrderOrder.lt_l a b)
    (A Ω : SecondOrderQuotient.type_l hℳ)
    (hΩ : ∀ n, SecondOrderQuotient.mem_l hℳ
      (SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR n)) Ω)
    (hS : ∀ a b, SecondOrderPairing.relation_l S a b ↔ SecondOrderFunctionObjects.value_l hℳ A
      (SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR a))
      (SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR b)))
    (hA : regular_l hℳ A Ω) (a : num_l ℳ) : SecondOrderDomain.wf_l S a := by
  intro X hX h₀
  by_contra h
  have h₁ : ∀ i b c, SecondOrderPairing.relation_l X i b → SecondOrderPairing.relation_l X (succ_l i) c →
      SecondOrderPairing.relation_l S c b := by
    intro i b c hb hc
    by_contra h₂
    exact h ⟨i, b, c, hb, hc, h₂⟩
  let N (n : num_l ℳ) := SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR n)
  obtain ⟨d, hd⟩ := SecondOrderNaturalSubsets.range_l hℳ R hR X
  have h₂ : ∀ x, SecondOrderQuotient.mem_l hℳ x d → field_l hℳ A Ω x := by
    intro x hx
    obtain ⟨i, b, hb, rfl⟩ := (hd x).mp hx
    obtain ⟨c, hc, _⟩ := hX (succ_l i)
    exact ⟨hΩ b, N c, hΩ c, Or.inr ((hS c b).mp (h₁ i b c hb hc))⟩
  obtain ⟨y, hy, h₃⟩ := hA d ⟨N a, (hd _).mpr ⟨zero_l ℳ, a, h₀, rfl⟩⟩ h₂
  obtain ⟨i, b, hb, rfl⟩ := (hd y).mp hy
  obtain ⟨c, hc, _⟩ := hX (succ_l i)
  exact h₃ (N c) ((hd _).mpr ⟨succ_l i, c, hc, rfl⟩) ((hS c b).mp (h₁ i b c hb hc))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRegularRelation
