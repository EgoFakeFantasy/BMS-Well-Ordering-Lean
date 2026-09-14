import BMSConstructibleBridge.PowerlessTriangular
import BMSConstructibleBridge.PowerlessAdditionBounds

/-!
# 三角数配对值与对角线区间

令 c=T(a+b)+a。证明第 s 条对角线的值落在 [T(s),T(s+1))，
再用不同区间的严格次序和同一区间内的加法消去证明坐标唯一。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessPairingCode

open Logic FirstOrder ThirdOrderSemantics PowerlessAddition PowerlessTriangular

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def code_l (ω e T a b c : carrier_l ℳ) : Prop :=
  ∃ s t, addition_l ω e a b s ∧ value_l T s t ∧ addition_l ω e t a c

def code_m {Γ Δ : SortContext ℒ} (ω e T a b c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (x : Term ℒ Γ Δ .set) := (x.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.existsE .set (.conj
    (PowerlessAdditionSyntax.addition_m (w ω) (w e) (w a) (w b) (.bvar (.there .here)))
    (.conj (SecondOrderObjectSyntax.value_m (w T) (.bvar (.there .here)) (.bvar .here))
      (PowerlessAdditionSyntax.addition_m (w ω) (w e) (.bvar .here) (w a) (w c)))))

theorem code_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T a b c : Term ℒ Γ Δ .set) :
    (code_m ω e T a b c).satisfies η ↔ code_l (ω.eval η) (e.eval η) (T.eval η) (a.eval η) (b.eval η) (c.eval η) := by
  simp only [code_m, code_l, Formula.satisfies, PowerlessAdditionSyntax.addition_formula_l,
    value_formula_l, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T a b : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hT : triangular_l ω e T) (ha : member_l ℳ a ω) (hb : member_l ℳ b ω) :
    ∃ c, member_l ℳ c ω ∧ code_l ω e T a b c := by
  obtain ⟨s, hs, h₀⟩ := PowerlessAddition.exists_l hℳ hω he ha hb
  obtain ⟨t, ht, _⟩ := hT.1.2 s hs
  obtain ⟨c, hc, h₁⟩ := PowerlessAddition.exists_l hℳ hω he ht.1 ha
  exact ⟨c, hc, s, t, h₀, ht.2, h₁⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T a b c d : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hT : triangular_l ω e T) (hc : code_l ω e T a b c) (hd : code_l ω e T a b d) : c = d := by
  obtain ⟨s, t, h₀, ht, hc⟩ := hc
  obtain ⟨r, v, h₁, hv, hd⟩ := hd
  have h₂ := PowerlessAddition.unique_l hℳ hω he h₀ h₁
  subst r
  have h₃ := PowerlessFunction.value_unique_l hℳ hT.1 ht hv
  subst v
  exact PowerlessAddition.unique_l hℳ hω he hc hd

theorem output_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T a b c : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hT : triangular_l ω e T) (hc : code_l ω e T a b c) : member_l ℳ c ω := by
  obtain ⟨s, t, _, ht, hc⟩ := hc
  exact PowerlessAdditionBounds.output_l hℳ hω he (PowerlessFunction.value_mem_l hℳ hT.1 ht).2 hc

theorem interval_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T a b c s t k v : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hT : triangular_l ω e T) (ha : member_l ℳ a ω) (hs : addition_l ω e a b s)
    (ht : value_l T s t) (hc : addition_l ω e t a c)
    (hk : PowerlessNatural.successor_l s k) (hv : value_l T k v) :
    (member_l ℳ t c ∨ t = c) ∧ member_l ℳ c v := by
  have ht₀ := PowerlessFunction.value_mem_l hℳ hT.1 ht
  refine ⟨PowerlessAdditionBounds.lower_l hℳ hω he ht₀.2 hc, ?_⟩
  exact PowerlessAdditionOrder.monotone_l hℳ hω he
    ((hk a).mpr (PowerlessAdditionBounds.lower_l hℳ hω he ha hs)) hc
    (hT.2.2 s k t v ht₀.1 hk ht hv)

theorem diagonal_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T a b c s t d g r v : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hT : triangular_l ω e T) (ha : member_l ℳ a ω) (hs : addition_l ω e a b s)
    (ht : value_l T s t) (hc : addition_l ω e t a c)
    (hv : value_l T r v) (hg : addition_l ω e v d g) (hsr : member_l ℳ s r) : member_l ℳ c g := by
  have hs₀ := (PowerlessFunction.value_mem_l hℳ hT.1 ht).1
  have hr₀ := PowerlessFunction.value_mem_l hℳ hT.1 hv
  obtain ⟨k, hk⟩ := PowerlessNatural.successor_exists_l hℳ s
  obtain ⟨u, hu, _⟩ := hT.1.2 k (PowerlessNatural.successor_mem_l hℳ hω hs₀ hk)
  have h₀ := (interval_l hℳ hω he hT ha hs ht hc hk hu.2).2
  have h₁ : member_l ℳ c v := by
    rcases PowerlessNaturalStep.bound_l hℳ hω r hr₀.1 s k hsr hk with h₁ | h₁
    · exact PowerlessNaturalOrder.member_transitive_l hℳ hω v hr₀.2 u c
        (PowerlessTriangular.monotone_l hℳ hω he hT h₁ hu.2 hv) h₀
    · subst k
      exact (PowerlessFunction.value_unique_l hℳ hT.1 hu.2 hv) ▸ h₀
  rcases PowerlessAdditionBounds.lower_l hℳ hω he hr₀.2 hg with h₂ | h₂
  · exact PowerlessNaturalOrder.member_transitive_l hℳ hω g
      (PowerlessAdditionBounds.output_l hℳ hω he hr₀.2 hg) v c h₂ h₁
  · exact h₂ ▸ h₁

theorem injective_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T a b c d f : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hT : triangular_l ω e T) (ha : member_l ℳ a ω) (hd : member_l ℳ d ω)
    (hc : code_l ω e T a b c) (hf : code_l ω e T d f c) : a = d ∧ b = f := by
  obtain ⟨s, t, hs, ht, hc⟩ := hc
  obtain ⟨r, v, hr, hv, hf⟩ := hf
  rcases PowerlessNaturalCompare.compare_l hℳ hω s (PowerlessFunction.value_mem_l hℳ hT.1 ht).1
      r (PowerlessFunction.value_mem_l hℳ hT.1 hv).1 with h₀ | h₀ | h₀
  · have h₁ := diagonal_l hℳ hω he hT ha hs ht hc hv hf h₀
    exact (PowerlessNatural.asymmetry_l hℳ h₁ h₁).elim
  · subst r
    have h₁ := PowerlessFunction.value_unique_l hℳ hT.1 ht hv
    subst v
    have h₂ := PowerlessAdditionOrder.cancel_l hℳ hω he hc hf
    subst d
    exact ⟨rfl, PowerlessAdditionOrder.cancel_l hℳ hω he hs hr⟩
  · have h₁ := diagonal_l hℳ hω he hT hd hr hv hf ht hc h₀
    exact (PowerlessNatural.asymmetry_l hℳ h₁ h₁).elim

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessPairingCode
