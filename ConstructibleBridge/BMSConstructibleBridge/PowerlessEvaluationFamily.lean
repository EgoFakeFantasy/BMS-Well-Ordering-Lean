import BMSConstructibleBridge.PowerlessEvaluationSlice
import BMSConstructibleBridge.PowerlessProduct

/-!
# 全部求值子集的实际集合族

对 ω×S 中的数码和参数图作实际可定义映射，值域精确为求值切片。
这是原始求值族，不将它未经源语义核验直接称为经典 Def(A)。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationFamily

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationSlice

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def family_l (ω A F S D : carrier_l ℳ) : Prop :=
  ∀ B, member_l ℳ B D ↔ ∃ c, member_l ℳ c ω ∧ ∃ f, member_l ℳ f S ∧ slice_l ω A F c f B

def family_m {Γ Δ : SortContext ℒ} (ω A F S D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
  let v (t : Term ℒ Γ Δ .set) := (w t).weakenBound SetTheory.SetSort.set
  let u (t : Term ℒ Γ Δ .set) := (v t).weakenBound SetTheory.SetSort.set
  .forallE .set (.iff (SecondOrderObjectSyntax.member_m (.bvar .here) (w D))
    (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (v ω))
      (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (u S))
        (slice_m (u ω) (u A) (u F) (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here)))))))))

theorem family_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω A F S D : Term ℒ Γ Δ .set) :
    (family_m ω A F S D).satisfies η ↔ family_l (ω.eval η) (A.eval η) (F.eval η) (S.eval η) (D.eval η) := by
  simp only [family_m, family_l, Formula.satisfies, slice_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def graph_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  .existsE .set (.existsE .set (.conj
    (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.fvar (.there .here)))
    (slice_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here))))) (.bvar (.there .here)) (.bvar .here) (.fvar .here))))

theorem graph_formula_l (ω A F p B : carrier_l ℳ) :
    graph_m.satisfies (((PowerlessComprehension.env_l
      (Γ := [.set, .set, .set])
      { bound := Fin.cases ω (Fin.cases A (fun _ => F)), free := fun _ => A }).pushFree p).pushFree B) ↔
      ∃ c f, ordered_l c f p ∧ slice_l ω A F c f B := by
  simp only [graph_m, Formula.satisfies, ordered_formula_l, slice_formula_l]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (ω A F S : carrier_l ℳ) :
    ∃ P G D, PowerlessProduct.product_l ω S P ∧ map_l G P D ∧
      (∀ B, member_l ℳ B D → ∃ p, value_l G p B) ∧ family_l ω A F S D := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 3 :=
    { bound := Fin.cases ω (Fin.cases A (fun _ => F)), free := fun _ => A }
  obtain ⟨P, hP⟩ := PowerlessProduct.exists_l hℳ ω S
  obtain ⟨G, D, hG, hD, h₀⟩ := PowerlessMapping.exists_l hℳ graph_m η P
    (fun p hp => by
      obtain ⟨c, _, f, _, hp⟩ := (hP p).mp hp
      obtain ⟨B, hB⟩ := PowerlessEvaluationSlice.exists_l hℳ ω A F c f
      exact ⟨B, (graph_formula_l ω A F p B).mpr ⟨c, f, hp, hB⟩⟩)
    (fun p _ B C hB hC => by
      obtain ⟨c, f, hp, hB⟩ := (graph_formula_l ω A F p B).mp hB
      obtain ⟨d, g, hq, hC⟩ := (graph_formula_l ω A F p C).mp hC
      obtain ⟨hc, hf⟩ := (PowerlessBasic.ordered_eq_l hℳ hp hq).mp rfl
      subst d
      subst g
      exact PowerlessEvaluationSlice.unique_l hℳ hB hC)
  refine ⟨P, G, D, hP, hG, ?_, fun B => ?_⟩
  · intro B hB
    obtain ⟨p, hp, hB⟩ := (hD B).mp hB
    exact ⟨p, (h₀ p hp B).mpr hB⟩
  · constructor
    · intro hB
      obtain ⟨p, hp, hB⟩ := (hD B).mp hB
      obtain ⟨c, hc, f, hf, hp⟩ := (hP p).mp hp
      obtain ⟨d, g, hq, hB⟩ := (graph_formula_l ω A F p B).mp hB
      obtain ⟨h₁, h₂⟩ := (PowerlessBasic.ordered_eq_l hℳ hp hq).mp rfl
      subst d
      subst g
      exact ⟨c, hc, f, hf, hB⟩
    · rintro ⟨c, hc, f, hf, hB⟩
      obtain ⟨p, hp⟩ := PowerlessBasic.ordered_exists_l hℳ c f
      exact (hD B).mpr ⟨p, (hP p).mpr ⟨c, hc, f, hf, hp⟩,
        (graph_formula_l ω A F p B).mpr ⟨c, f, hp, hB⟩⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A F S D E : carrier_l ℳ} (hD : family_l ω A F S D) (hE : family_l ω A F S E) : D = E :=
  (PowerlessTheory.ext_l hℳ).eq_of_same_members D E (fun B => (hD B).trans (hE B).symm)

theorem subset_l {ω A F S D B : carrier_l ℳ} (hD : family_l ω A F S D) (hB : member_l ℳ B D) :
    ThirdOrderSemantics.subset_l B A := by
  obtain ⟨_, _, _, _, hB⟩ := (hD B).mp hB
  exact PowerlessEvaluationSlice.subset_l hB

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationFamily
