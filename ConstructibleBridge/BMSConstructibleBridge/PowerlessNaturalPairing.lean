import BMSConstructibleBridge.PowerlessPairingCode

/-!
# 内部 ω×ω 到 ω 的实际单射

纯配对公式的唯一性用于收集函数图，坐标唯一性用于单射证明。
无需完整幂集、宿主自然数编码或上游 hZF 算术接口。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessNaturalPairing

open Logic FirstOrder ThirdOrderSemantics PowerlessPairingCode PowerlessTriangular

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def graph_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  .existsE .set (.existsE .set (.conj
    (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.fvar (.there .here)))
    (code_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here))))) (.bvar (.there .here)) (.bvar .here) (.fvar .here))))

theorem graph_formula_l (η : Env ℳ [] [.set, .set, .set, .set, .set]) : graph_m.satisfies η ↔
    ∃ a b, ordered_l a b (η.freeVal (.there .here)) ∧
      code_l (η.freeVal (.there (.there .here))) (η.freeVal (.there (.there (.there .here))))
        (η.freeVal (.there (.there (.there (.there .here))))) a b (η.freeVal .here) := by
  simp only [graph_m, Formula.satisfies, ordered_formula_l, code_formula_l]
  rfl

theorem graph_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T P : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hT : triangular_l ω e T) (hP : PowerlessProduct.product_l ω ω P) :
    ∃ f, map_l f P ω ∧ ∀ p, member_l ℳ p P → ∀ c,
      value_l f p c ↔ ∃ a b, ordered_l a b p ∧ code_l ω e T a b c := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 3 :=
    { bound := Fin.cases ω (Fin.cases e (fun _ => T)), free := fun _ => ω }
  have h : ∀ p c, graph_m.satisfies (((PowerlessComprehension.env_l η).pushFree p).pushFree c) ↔
      ∃ a b, ordered_l a b p ∧ code_l ω e T a b c := fun p c => graph_formula_l _
  obtain ⟨f, B, hf, _, h₀⟩ := PowerlessMapping.exists_l hℳ graph_m η P
    (fun p hp => by
      obtain ⟨a, ha, b, hb, h₁⟩ := (hP p).mp hp
      obtain ⟨c, _, hc⟩ := PowerlessPairingCode.exists_l hℳ hω he hT ha hb
      exact ⟨c, (h p c).mpr ⟨a, b, h₁, hc⟩⟩)
    (fun p _ c d hc hd => by
      obtain ⟨a, b, h₁, hc⟩ := (h p c).mp hc
      obtain ⟨x, y, h₂, hd⟩ := (h p d).mp hd
      obtain ⟨h₃, h₄⟩ := (PowerlessBasic.ordered_eq_l hℳ h₁ h₂).mp rfl
      subst x
      subst y
      exact PowerlessPairingCode.unique_l hℳ hω he hT hc hd)
  have h₁ : ∀ p c, value_l f p c → member_l ℳ c ω := by
    intro p c hc
    obtain ⟨a, b, _, h₂⟩ := (h p c).mp ((h₀ p (PowerlessFunction.value_mem_l hℳ hf hc).1 c).mp hc)
    exact PowerlessPairingCode.output_l hℳ hω he hT h₂
  exact ⟨f, PowerlessFunction.range_l hℳ hf h₁, fun p hp c => (h₀ p hp c).trans (h p c)⟩

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e P : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hP : PowerlessProduct.product_l ω ω P) : ∃ f, map_l f P ω ∧ ThirdOrderSemantics.injective_l f := by
  obtain ⟨T, hT⟩ := PowerlessTriangular.exists_l hℳ hω he
  obtain ⟨f, hf, h₀⟩ := graph_l hℳ hω he hT hP
  refine ⟨f, hf, ?_⟩
  intro p q c hp hq
  have hp₀ := (PowerlessFunction.value_mem_l hℳ hf hp).1
  have hq₀ := (PowerlessFunction.value_mem_l hℳ hf hq).1
  obtain ⟨a, b, hp₁, hc⟩ := (h₀ p hp₀ c).mp hp
  obtain ⟨d, k, hq₁, hd⟩ := (h₀ q hq₀ c).mp hq
  have h₁ : ∀ x y r, member_l ℳ r P → ordered_l x y r → member_l ℳ x ω := by
    intro x y r hr h₂
    obtain ⟨s, hs, t, _, h₃⟩ := (hP r).mp hr
    exact ((PowerlessBasic.ordered_eq_l hℳ h₂ h₃).mp rfl).1.symm ▸ hs
  obtain ⟨h₂, h₃⟩ := PowerlessPairingCode.injective_l hℳ hω he hT
    (h₁ a b p hp₀ hp₁) (h₁ d k q hq₀ hq₁) hc hd
  subst d
  subst k
  exact PowerlessBasic.ordered_unique_l hℳ hp₁ hq₁

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessNaturalPairing
