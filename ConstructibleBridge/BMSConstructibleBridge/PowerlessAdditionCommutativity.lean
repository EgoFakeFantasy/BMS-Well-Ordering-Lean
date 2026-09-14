import BMSConstructibleBridge.PowerlessAdditionSuccessor

/-! # 由同一内部递归图推出加法交换律 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionCommutativity

open Logic FirstOrder ThirdOrderSemantics PowerlessAddition PowerlessAdditionSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem comm_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a b : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (ha : member_l ℳ a ω) (hb : member_l ℳ b ω) :
    ∀ c, addition_l ω e a b c ↔ addition_l ω e b a c := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 3 :=
    { bound := Fin.cases a (Fin.cases ω (fun _ => e)), free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    addition_m (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  have h : ∀ n c, φ.satisfies (((PowerlessComprehension.env_l η).pushFree n).pushFree c) ↔
      addition_l ω e n a c := by
    intro n c
    exact addition_formula_l _ _ _ _ _ _
  obtain ⟨f, B, hf, _, hV⟩ := PowerlessMapping.exists_l hℳ φ η ω
    (fun n hn => by
      obtain ⟨c, _, hc⟩ := PowerlessAddition.exists_l hℳ hω he hn ha
      exact ⟨c, (h n c).mpr hc⟩)
    (fun n _ c d hc hd => PowerlessAddition.unique_l hℳ hω he ((h n c).mp hc) ((h n d).mp hd))
  have h₀ : ∀ n, member_l ℳ n ω → ∀ c, value_l f n c ↔ addition_l ω e n a c :=
    fun n hn c => (hV n hn c).trans (h n c)
  have h₁ : iteration_l ω e a f := by
    refine ⟨B, hf, (h₀ e (PowerlessNatural.zero_mem_l hℳ hω he) a).mpr
      (PowerlessAdditionLaws.left_zero_l hℳ hω he ha), ?_⟩
    intro n m x y hn hm hx hy
    exact (step_formula_l ω x y).mpr (PowerlessAdditionSuccessor.left_l hℳ hω he hn hm ha
      ((h₀ n hn x).mp hx) ((h₀ m (PowerlessNatural.successor_mem_l hℳ hω hn hm) y).mp hy))
  intro c
  constructor
  · rintro ⟨g, hg, hc⟩
    have h₂ := iteration_unique_l hℳ hω he hg h₁
    subst g
    exact (h₀ b hb c).mp hc
  · intro hc
    exact ⟨f, h₁, (h₀ b hb c).mpr hc⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionCommutativity
