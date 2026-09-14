import BMSConstructibleBridge.SecondOrderFormulaCompilation

/-! # 数码赋值与源结构环境的对应及量词扩张 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSourceEnvironment

open Logic FirstOrder SecondOrderSyntax SecondOrderModel
open SecondOrderSequenceSyntax (read_l)
open SecondOrderAssignmentSyntax (extension_l)
open SecondOrderFormulaCompilation (term_l)

set_option autoImplicit false

universe u v

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} {𝒩 : FirstOrder.Structure.{0, 0, 0, v} ℒ}

def represents_l {Γ Δ : SortContext ℒ} (f : num_l ℳ → 𝒩.Carrier .set)
    (η : Env 𝒩 Γ Δ) (E D : set_l ℳ) (c : num_l ℳ) : Prop :=
  ∀ t : Term ℒ Γ Δ .set, ∃ x, read_l E c (term_l ℳ t) x ∧
    (∀ y, read_l E c (term_l ℳ t) y → y = x) ∧ mem_l x D ∧ f x = t.eval η

theorem extend_l {Γ Δ : SortContext ℒ} (f : num_l ℳ → 𝒩.Carrier .set)
    (η : Env 𝒩 Γ Δ) (E D : set_l ℳ) (c l d x : num_l ℳ)
    (hη : represents_l f η E D c) (hd : extension_l E c l d x) (hx : mem_l x D) :
    represents_l f (η.pushBound (f x)) E D d := by
  have h (t : Term ℒ Γ Δ .set) : ∃ y, read_l E d (term_l ℳ (t.weakenBound SetTheory.SetSort.set)) y ∧
      (∀ z, read_l E d (term_l ℳ (t.weakenBound SetTheory.SetSort.set)) z → z = y) ∧
        mem_l y D ∧ f y = (t.weakenBound SetTheory.SetSort.set).eval (η.pushBound (f x)) := by
    obtain ⟨y, hy, hU, hD, hf⟩ := hη t
    rw [SecondOrderFormulaCompilation.term_weaken_l]
    exact ⟨y, (hd.2.2 _ y).mpr hy, fun z hz => hU z ((hd.2.2 _ z).mp hz), hD,
      hf.trans (Term.eval_weakenBound η (f x) t).symm⟩
  intro t
  match t with
  | .bvar .here => exact ⟨x, (hd.2.1 x).mpr rfl, fun y hy => (hd.2.1 y).mp hy, hx, rfl⟩
  | .bvar (.there w) => exact h (.bvar w)
  | .fvar w => exact h (.fvar w)
  | .app g _ => nomatch g

theorem empty_l (f : num_l ℳ → 𝒩.Carrier .set) (E D : set_l ℳ) (c : num_l ℳ) :
    represents_l f Env.empty E D c := by
  intro t
  match t with
  | .bvar w => nomatch w
  | .fvar w => nomatch w
  | .app g _ => nomatch g

theorem atom_l {Γ Δ : SortContext ℒ} (f : num_l ℳ → 𝒩.Carrier .set) (η : Env 𝒩 Γ Δ)
    (E D G : set_l ℳ) (c : num_l ℳ) (hη : represents_l f η E D c)
    (P : 𝒩.Carrier .set → 𝒩.Carrier .set → Prop)
    (hG : ∀ x y, mem_l x D → mem_l y D → (SecondOrderPairing.relation_l G x y ↔ P (f x) (f y)))
    (s t : Term ℒ Γ Δ .set) :
    (∃ x y, read_l E c (term_l ℳ s) x ∧ read_l E c (term_l ℳ t) y ∧ SecondOrderPairing.relation_l G x y) ↔
      P (s.eval η) (t.eval η) := by
  obtain ⟨a, ha, hA, hDa, hfa⟩ := hη s
  obtain ⟨b, hb, hB, hDb, hfb⟩ := hη t
  rw [← hfa, ← hfb]
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    have hx₀ := hA x hx
    have hy₀ := hB y hy
    subst x y
    exact (hG a b hDa hDb).mp hxy
  · intro h
    exact ⟨a, b, ha, hb, (hG a b hDa hDb).mpr h⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSourceEnvironment
