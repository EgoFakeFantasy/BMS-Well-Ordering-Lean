import BMSConstructibleBridge.SecondOrderPairSet
import Mathlib.Data.Set.Insert

/-!
# 内部对象的无序对与 Kuratowski 有序对

所有等式为图商中的真正相等。成员规格给出有序对两坐标的唯一性，不依赖
宿主集合论坍缩或把图商嵌入 ZFSet。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairObjects

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic
open SecondOrderQuotient

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def pair_l (hℳ : Theory.Models ℳ theory_m) (a b p : type_l hℳ) : Prop :=
  ∀ c, mem_l hℳ c p ↔ c = a ∨ c = b

def ordered_l (hℳ : Theory.Models ℳ theory_m) (a b p : type_l hℳ) : Prop :=
  ∃ s t, pair_l hℳ a a s ∧ pair_l hℳ a b t ∧ pair_l hℳ s t p

theorem pair_exists_l (hℳ : Theory.Models ℳ theory_m) (a b : type_l hℳ) :
    ∃ p, pair_l hℳ a b p := SecondOrderPairSet.models_l hℳ a b

theorem pair_eq_l (hℳ : Theory.Models ℳ theory_m) {a b c d p q : type_l hℳ}
    (hp : pair_l hℳ a b p) (hq : pair_l hℳ c d q) :
    p = q ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    apply Set.pair_eq_pair_iff.mp
    ext x
    change (x = a ∨ x = b) ↔ (x = c ∨ x = d)
    exact (hp x).symm.trans (h ▸ hq x)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact SecondOrderQuotient.ext_l hℳ p q (fun x => (hp x).trans (hq x).symm)
    · exact SecondOrderQuotient.ext_l hℳ p q (fun x => (hp x).trans (or_comm.trans (hq x).symm))

theorem pair_unique_l (hℳ : Theory.Models ℳ theory_m) {a b p q : type_l hℳ}
    (hp : pair_l hℳ a b p) (hq : pair_l hℳ a b q) : p = q :=
  (pair_eq_l hℳ hp hq).mpr (Or.inl ⟨rfl, rfl⟩)

theorem ordered_exists_l (hℳ : Theory.Models ℳ theory_m) (a b : type_l hℳ) :
    ∃ p, ordered_l hℳ a b p := by
  obtain ⟨s, hs⟩ := pair_exists_l hℳ a a
  obtain ⟨t, ht⟩ := pair_exists_l hℳ a b
  obtain ⟨p, hp⟩ := pair_exists_l hℳ s t
  exact ⟨p, s, t, hs, ht, hp⟩

theorem ordered_eq_l (hℳ : Theory.Models ℳ theory_m) {a b c d p q : type_l hℳ}
    (hp : ordered_l hℳ a b p) (hq : ordered_l hℳ c d q) : p = q ↔ a = c ∧ b = d := by
  obtain ⟨s, t, hs, ht, hp⟩ := hp
  obtain ⟨v, w, hv, hw, hq⟩ := hq
  constructor
  · intro h
    rcases (pair_eq_l hℳ hp hq).mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have h₃ : a = c := ((pair_eq_l hℳ hs hv).mp h₁).elim And.left And.left
      have h₄ := (pair_eq_l hℳ ht hw).mp h₂
      refine ⟨h₃, h₄.elim And.right ?_⟩
      exact fun h₅ => h₅.2.trans (h₃.symm.trans h₅.1)
    · have h₃ : a = c ∧ a = d := by
        rcases (pair_eq_l hℳ hs hw).mp h₁ with h | h
        · exact h
        · exact h.symm
      have h₄ : b = c := ((pair_eq_l hℳ ht hv).mp h₂).elim And.right And.right
      exact ⟨h₃.1, h₄.trans (h₃.1.symm.trans h₃.2)⟩
  · rintro ⟨rfl, rfl⟩
    have h₁ := pair_unique_l hℳ hs hv
    have h₂ := pair_unique_l hℳ ht hw
    exact (pair_eq_l hℳ hp hq).mpr (Or.inl ⟨h₁, h₂⟩)

theorem ordered_unique_l (hℳ : Theory.Models ℳ theory_m) {a b p q : type_l hℳ}
    (hp : ordered_l hℳ a b p) (hq : ordered_l hℳ a b q) : p = q :=
  (ordered_eq_l hℳ hp hq).mpr ⟨rfl, rfl⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairObjects
