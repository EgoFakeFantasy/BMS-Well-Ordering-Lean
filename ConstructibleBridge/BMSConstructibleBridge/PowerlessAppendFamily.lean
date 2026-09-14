import BMSConstructibleBridge.PowerlessAppendGraph
import BMSConstructibleBridge.PowerlessProduct

/-! # 一族函数图的全部单坐标扩张 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAppendFamily

open Logic FirstOrder ThirdOrderSemantics PowerlessAppendGraph

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def graph_m : Formula ℒ [] [.set, .set, .set] :=
  .existsE .set (.existsE .set (.conj
    (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.fvar (.there .here)))
    (append_m (.bvar (.there .here)) (.fvar (.there (.there .here))) (.bvar .here) (.fvar .here))))

theorem graph_formula_l (η : Env ℳ [] [.set, .set, .set]) : graph_m.satisfies η ↔
    ∃ f a, ordered_l f a (η.freeVal (.there .here)) ∧
      append_l f (η.freeVal (.there (.there .here))) a (η.freeVal .here) := by
  simp only [graph_m, Formula.satisfies, ordered_formula_l, append_formula_l]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (n P A : carrier_l ℳ) :
    ∃ Q F B, PowerlessProduct.product_l P A Q ∧ ThirdOrderSemantics.map_l F Q B ∧
      (∀ g, member_l ℳ g B → ∃ p, ThirdOrderSemantics.value_l F p g) ∧
      ∀ g, member_l ℳ g B ↔ ∃ f, member_l ℳ f P ∧ ∃ a, member_l ℳ a A ∧ append_l f n a g := by
  obtain ⟨Q, hQ⟩ := PowerlessProduct.exists_l hℳ P A
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => n, free := fun _ => A }
  have h : ∀ p g, graph_m.satisfies (((PowerlessComprehension.env_l η).pushFree p).pushFree g) ↔
      ∃ f a, ordered_l f a p ∧ append_l f n a g := fun p g => graph_formula_l _
  obtain ⟨F, B, hF, hB, h₀⟩ := PowerlessMapping.exists_l hℳ graph_m η Q
    (fun p hp => by
      obtain ⟨f, _, a, _, hp⟩ := (hQ p).mp hp
      obtain ⟨g, hg⟩ := PowerlessAppendGraph.exists_l hℳ f n a
      exact ⟨g, (h p g).mpr ⟨f, a, hp, hg⟩⟩)
    (fun p _ g k hg hk => by
      obtain ⟨f, a, hp, hg⟩ := (h p g).mp hg
      obtain ⟨l, b, hp₀, hk⟩ := (h p k).mp hk
      obtain ⟨h₁, h₂⟩ := (PowerlessBasic.ordered_eq_l hℳ hp hp₀).mp rfl
      subst l
      subst b
      exact PowerlessAppendGraph.unique_l hℳ hg hk)
  refine ⟨Q, F, B, hQ, hF, ?_, ?_⟩
  · intro g hg
    obtain ⟨p, hp, hg⟩ := (hB g).mp hg
    exact ⟨p, (h₀ p hp g).mpr hg⟩
  · intro g
    rw [hB g]
    constructor
    · rintro ⟨p, hp, hg⟩
      obtain ⟨f, a, hp₀, hg⟩ := (h p g).mp hg
      obtain ⟨k, hk, b, hb, hp₁⟩ := (hQ p).mp hp
      obtain ⟨h₁, h₂⟩ := (PowerlessBasic.ordered_eq_l hℳ hp₀ hp₁).mp rfl
      subst k
      subst b
      exact ⟨f, hk, a, hb, hg⟩
    · rintro ⟨f, hf, a, ha, hg⟩
      obtain ⟨p, hp⟩ := PowerlessBasic.ordered_exists_l hℳ f a
      exact ⟨p, (hQ p).mpr ⟨f, hf, a, ha, hp⟩, (h p g).mpr ⟨f, a, hp, hg⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAppendFamily
