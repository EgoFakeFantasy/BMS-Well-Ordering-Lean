import BMSConstructibleBridge.PowerlessEvaluationAgreement
import BMSConstructibleBridge.PowerlessLevyEntry

/-!
# 全内部有限赋值上的有向查询保持

F 为上域、G 为下域求值图时，Σ 极性要求 G→F，Π 极性要求 F→G。
命题以原纯 Formula 表示，供内部证书归纳使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationDirection

open Logic FirstOrder ThirdOrderSemantics
open PowerlessEvaluationClause (query_l query_m query_formula_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def direction_l (ω A F G c : carrier_l ℳ) : Prop :=
  ∀ f, (∃ m, member_l ℳ m ω ∧ map_l f m A) → query_l F c f → query_l G c f

def direction_m {Γ Δ : SortContext ℒ} (ω A F G c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .forallE .set (.imp (.existsE .set (.conj
    (SecondOrderObjectSyntax.member_m (.bvar .here) ((w ω).weakenBound SetTheory.SetSort.set))
    (SecondOrderObjectSyntax.map_m (.bvar (.there .here)) (.bvar .here) ((w A).weakenBound SetTheory.SetSort.set))))
    (.imp (query_m (w F) (w c) (.bvar .here)) (query_m (w G) (w c) (.bvar .here))))

theorem direction_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω A F G c : Term ℒ Γ Δ .set) :
    (direction_m ω A F G c).satisfies η ↔
      direction_l (ω.eval η) (A.eval η) (F.eval η) (G.eval η) (c.eval η) := by
  simp only [direction_m, direction_l, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, map_formula_l, query_formula_l, Term.eval_weakenBound]
  rfl

def polarity_l (ω A F G e t p c : carrier_l ℳ) : Prop :=
  (p = e → direction_l ω A G F c) ∧ (p = t → direction_l ω A F G c)

def polarity_m {Γ Δ : SortContext ℒ} (ω A F G e t p c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (.imp (.equal p e) (direction_m ω A G F c)) (.imp (.equal p t) (direction_m ω A F G c))

theorem polarity_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω A F G e t p c : Term ℒ Γ Δ .set) :
    (polarity_m ω A F G e t p c).satisfies η ↔
      polarity_l (ω.eval η) (A.eval η) (F.eval η) (G.eval η) (e.eval η) (t.eval η) (p.eval η) (c.eval η) := by
  simp only [polarity_m, polarity_l, Formula.satisfies, direction_formula_l]

theorem agreement_l {ω A F G e t p c : carrier_l ℳ} (h : PowerlessEvaluationAgreement.point_l ω A F G c) :
    polarity_l ω A F G e t p c :=
  ⟨fun _ f hf => (h f hf).mpr, fun _ f hf => (h f hf).mp⟩

theorem sigma_l {ω A F G e t c : carrier_l ℳ} (het : e ≠ t) (h : direction_l ω A G F c) :
    polarity_l ω A F G e t e c := ⟨fun _ => h, fun ht => (het ht).elim⟩

theorem nand_l {ω A F G a b c : carrier_l ℳ}
    (hF : ∀ f, (∃ m, member_l ℳ m ω ∧ map_l f m A) → (query_l F c f ↔ ¬(query_l F a f ∧ query_l F b f)))
    (hG : ∀ f, (∃ m, member_l ℳ m ω ∧ map_l f m A) → (query_l G c f ↔ ¬(query_l G a f ∧ query_l G b f)))
    (ha : direction_l ω A F G a) (hb : direction_l ω A F G b) : direction_l ω A G F c := by
  intro f hf hc
  apply (hF f hf).mpr
  rintro ⟨ha₀, hb₀⟩
  exact (hG f hf).mp hc ⟨ha f hf ha₀, hb f hf hb₀⟩

theorem nand_polarity_l {ω A F G e t p q a b c : carrier_l ℳ} (het : e ≠ t)
    (hp : PowerlessLevyEntry.opposite_l e t p q)
    (hF : ∀ f, (∃ m, member_l ℳ m ω ∧ map_l f m A) → (query_l F c f ↔ ¬(query_l F a f ∧ query_l F b f)))
    (hG : ∀ f, (∃ m, member_l ℳ m ω ∧ map_l f m A) → (query_l G c f ↔ ¬(query_l G a f ∧ query_l G b f)))
    (ha : polarity_l ω A F G e t q a) (hb : polarity_l ω A F G e t q b) : polarity_l ω A F G e t p c := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact sigma_l het (nand_l hF hG (ha.2 rfl) (hb.2 rfl))
  · exact ⟨fun ht => (het ht.symm).elim, fun _ => nand_l hG hF (ha.1 rfl) (hb.1 rfl)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationDirection
