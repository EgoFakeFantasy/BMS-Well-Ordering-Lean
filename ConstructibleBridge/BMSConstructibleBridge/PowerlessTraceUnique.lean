import BMSConstructibleBridge.PowerlessTrace

/-! # 内部有限递归轨迹的相容性与唯一性 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTraceUnique

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural PowerlessTrace

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def agree_m : Formula ℒ [] [.set, .set, .set] :=
  .forallE .set (.forallE .set (.imp
    (SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.fvar .here) (.bvar (.there .here)))
    (.imp (SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar .here))
      (.equal (.bvar (.there .here)) (.bvar .here)))))

theorem agree_formula_l (η : Env ℳ [] [.set, .set, .set]) : agree_m.satisfies η ↔
    ∀ x y, value_l (η.freeVal (.there .here)) (η.freeVal .here) x →
      value_l (η.freeVal (.there (.there .here))) (η.freeVal .here) y → x = y := by
  simp only [agree_m, Formula.satisfies, value_formula_l]
  rfl

theorem below_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω n S k l : carrier_l ℳ} (hω : omega_l ω) (hn : member_l ℳ n ω)
    (hS : successor_l n S) (hl : successor_l k l) (h : member_l ℳ l S) : member_l ℳ k n := by
  have h₀ := (hl k).mpr (Or.inr rfl)
  rcases (hS l).mp h with h | h
  · exact PowerlessNaturalOrder.member_transitive_l hℳ hω n hn l k h h₀
  · exact h ▸ h₀

/-- 不同长度的轨迹在每个共同输入处取值一致；无需先选一族轨迹。 -/
theorem compatible_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x y z,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) →
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree z) → y = z)
    {ω f g n m e a : carrier_l ℳ} (hω : omega_l ω) (hn : member_l ℳ n ω) (hm : member_l ℳ m ω)
    (he : PowerlessNatural.zero_l e) (hf : trace_l φ η f n e a) (hg : trace_l φ η g m e a) :
    ∀ k x y, value_l f k x → value_l g k y → x = y := by
  obtain ⟨S, B, hS, hf, hF, h₀⟩ := hf
  obtain ⟨T, C, hT, hg, hG, h₁⟩ := hg
  let ζ : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases f (fun _ => g), free := fun _ => ω }
  have h₂ : ∀ k, agree_m.satisfies ((PowerlessComprehension.env_l ζ).pushFree k) ↔
      ∀ x y, value_l f k x → value_l g k y → x = y := fun k => agree_formula_l _
  have h₃ := PowerlessNatural.induction_l hℳ agree_m ζ hω
    (fun z hz => (h₂ z).mpr (by
      have h₄ := PowerlessNatural.zero_unique_l hℳ hz he
      subst z
      intro x y hx hy
      exact (PowerlessFunction.value_unique_l hℳ hf hx hF).trans
        (PowerlessFunction.value_unique_l hℳ hg hy hG).symm))
    (fun k l _ hl h₄ => (h₂ l).mpr (by
      intro x y hx hy
      have hk := below_l hℳ hω hn hS hl (PowerlessFunction.value_mem_l hℳ hf hx).1
      have hl₀ := below_l hℳ hω hm hT hl (PowerlessFunction.value_mem_l hℳ hg hy).1
      obtain ⟨v, hv, _⟩ := hf.2 k ((hS k).mpr (Or.inl hk))
      obtain ⟨w, hw, _⟩ := hg.2 k ((hT k).mpr (Or.inl hl₀))
      have h₅ := (h₂ k).mp h₄ v w hv.2 hw.2
      subst w
      exact h v x y (h₀ k l v x hk hl hv.2 hx) (h₁ k l v y hl₀ hl hw.2 hy)))
  intro k x y hx hy
  have hk := (PowerlessFunction.value_mem_l hℳ hf hx).1
  have h₄ := PowerlessNaturalOrder.subset_l hℳ hω S (successor_mem_l hℳ hω hn hS) k hk
  exact (h₂ k).mp (h₃ k h₄) x y hx hy

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x y z,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) →
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree z) → y = z)
    {ω f g n e a : carrier_l ℳ} (hω : omega_l ω) (hn : member_l ℳ n ω)
    (he : PowerlessNatural.zero_l e) (hf : trace_l φ η f n e a) (hg : trace_l φ η g n e a) : f = g := by
  have h₀ := compatible_l hℳ φ η h hω hn hn he hf hg
  obtain ⟨S, B, hS, hf, _⟩ := hf
  obtain ⟨T, C, hT, hg, _⟩ := hg
  have h₁ := successor_unique_l hℳ hS hT
  subst T
  apply PowerlessFunction.ext_l hℳ hf hg
  intro k hk x
  constructor
  · intro hx
    obtain ⟨y, hy, _⟩ := hg.2 k hk
    exact (h₀ k x y hx hy.2).symm ▸ hy.2
  · intro hx
    obtain ⟨y, hy, _⟩ := hf.2 k hk
    exact h₀ k y x hy.2 hx ▸ hy.2

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTraceUnique
