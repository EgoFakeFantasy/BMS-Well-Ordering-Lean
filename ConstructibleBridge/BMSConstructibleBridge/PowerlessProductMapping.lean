import BMSConstructibleBridge.PowerlessProduct
import BMSConstructibleBridge.PowerlessMapping
import BMSConstructibleBridge.PowerlessFunction

/-! # 逐坐标映射的实际乘积图 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessProductMapping

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def graph_l (f g p q : carrier_l ℳ) : Prop :=
  ∃ a b c d, ordered_l a b p ∧ value_l f a c ∧ value_l g b d ∧ ordered_l c d q

def graph_m : Formula ℒ [] [.set, .set, .set, .set] :=
  .existsE .set (.existsE .set (.existsE .set (.existsE .set (.conj
    (SecondOrderObjectSyntax.ordered_m (.bvar (.there (.there (.there .here))))
      (.bvar (.there (.there .here))) (.fvar (.there .here)))
    (.conj (SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here)))
      (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)))
    (.conj (SecondOrderObjectSyntax.value_m (.fvar (.there (.there (.there .here))))
      (.bvar (.there (.there .here))) (.bvar .here))
      (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))))))))

theorem graph_formula_l (η : Env ℳ [] [.set, .set, .set, .set]) : graph_m.satisfies η ↔
    graph_l (η.freeVal (.there (.there .here))) (η.freeVal (.there (.there (.there .here))))
      (η.freeVal (.there .here)) (η.freeVal .here) := by
  simp only [graph_m, graph_l, Formula.satisfies, ordered_formula_l, value_formula_l]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f g A B C D P Q : carrier_l ℳ} (hf : map_l f A B) (hg : map_l g C D)
    (hP : PowerlessProduct.product_l A C P) (hQ : PowerlessProduct.product_l B D Q) :
    ∃ k, map_l k P Q ∧ ∀ p q, value_l k p q ↔ graph_l f g p q := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases f (fun _ => g), free := fun _ => A }
  have h : ∀ p q, graph_m.satisfies (((PowerlessComprehension.env_l η).pushFree p).pushFree q) ↔
      graph_l f g p q := fun p q => graph_formula_l _
  obtain ⟨k, E, hk, _, h₀⟩ := PowerlessMapping.exists_l hℳ graph_m η P
    (fun p hp => by
      obtain ⟨a, ha, b, hb, hp⟩ := (hP p).mp hp
      obtain ⟨c, hc, _⟩ := hf.2 a ha
      obtain ⟨d, hd, _⟩ := hg.2 b hb
      obtain ⟨q, hq⟩ := PowerlessBasic.ordered_exists_l hℳ c d
      exact ⟨q, (h p q).mpr ⟨a, b, c, d, hp, hc.2, hd.2, hq⟩⟩)
    (fun p _ q r hq hr => by
      obtain ⟨a, b, c, d, hp, hc, hd, hq⟩ := (h p q).mp hq
      obtain ⟨x, y, z, v, hp₁, hz, hv, hr⟩ := (h p r).mp hr
      obtain ⟨h₁, h₂⟩ := (PowerlessBasic.ordered_eq_l hℳ hp hp₁).mp rfl
      subst x
      subst y
      have h₁ := PowerlessFunction.value_unique_l hℳ hf hc hz
      have h₂ := PowerlessFunction.value_unique_l hℳ hg hd hv
      subst z
      subst v
      exact PowerlessBasic.ordered_unique_l hℳ hq hr)
  have h₁ : ∀ p q, value_l k p q ↔ graph_l f g p q := by
    intro p q
    constructor
    · intro hq
      exact (h p q).mp ((h₀ p (PowerlessFunction.value_mem_l hℳ hk hq).1 q).mp hq)
    · rintro ⟨a, b, c, d, hp, hc, hd, hq⟩
      have hp₀ := (hP p).mpr ⟨a, (PowerlessFunction.value_mem_l hℳ hf hc).1,
        b, (PowerlessFunction.value_mem_l hℳ hg hd).1, hp⟩
      exact (h₀ p hp₀ q).mpr ((h p q).mpr ⟨a, b, c, d, hp, hc, hd, hq⟩)
  refine ⟨k, PowerlessFunction.range_l hℳ hk ?_, h₁⟩
  intro p q hq
  obtain ⟨a, b, c, d, _, hc, hd, hq⟩ := (h₁ p q).mp hq
  exact (hQ q).mpr ⟨c, (PowerlessFunction.value_mem_l hℳ hf hc).2,
    d, (PowerlessFunction.value_mem_l hℳ hg hd).2, hq⟩

theorem injective_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f g k : carrier_l ℳ} (hf : ThirdOrderSemantics.injective_l f) (hg : ThirdOrderSemantics.injective_l g)
    (h : ∀ p q, value_l k p q ↔ graph_l f g p q) : ThirdOrderSemantics.injective_l k := by
  intro p r q hp hr
  obtain ⟨a, b, c, d, hp, hc, hd, hq⟩ := (h p q).mp hp
  obtain ⟨x, y, z, v, hr, hz, hv, hq₁⟩ := (h r q).mp hr
  obtain ⟨h₀, h₁⟩ := (PowerlessBasic.ordered_eq_l hℳ hq hq₁).mp rfl
  subst z
  subst v
  have h₀ := hf a x c hc hz
  have h₁ := hg b y d hd hv
  subst x
  subst y
  exact PowerlessBasic.ordered_unique_l hℳ hp hr

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessProductMapping
