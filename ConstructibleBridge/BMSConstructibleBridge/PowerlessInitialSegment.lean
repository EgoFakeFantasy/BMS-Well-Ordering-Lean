import BMSConstructibleBridge.PowerlessWellOrder

/-! # 内部良序的前驱集和含端点初段 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessInitialSegment

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def predecessor_l (C A R a : carrier_l ℳ) : Prop :=
  ∀ x, member_l ℳ x C ↔ member_l ℳ x A ∧ value_l R x a

def segment_l (S A R a : carrier_l ℳ) : Prop :=
  ∀ x, member_l ℳ x S ↔ member_l ℳ x A ∧ (value_l R x a ∨ x = a)

def initial_l (D A R : carrier_l ℳ) : Prop :=
  subset_l D A ∧ ∀ x, member_l ℳ x D → ∀ y, member_l ℳ y A → value_l R y x → member_l ℳ y D

def segment_m {Γ Δ : SortContext ℒ} (S A R a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.iff (SecondOrderObjectSyntax.member_m (.bvar .here) (S.weakenBound SetTheory.SetSort.set))
    (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (A.weakenBound SetTheory.SetSort.set))
      (.disj (SecondOrderObjectSyntax.value_m (R.weakenBound SetTheory.SetSort.set)
        (.bvar .here) (a.weakenBound SetTheory.SetSort.set))
        (.equal (.bvar .here) (a.weakenBound SetTheory.SetSort.set)))))

theorem segment_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (S A R a : Term ℒ Γ Δ .set) :
    (segment_m S A R a).satisfies η ↔ segment_l (S.eval η) (A.eval η) (R.eval η) (a.eval η) := by
  simp only [segment_m, segment_l, Formula.satisfies, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem predecessor_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (A R a : carrier_l ℳ) :
    ∃ C, predecessor_l C A R a := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases R (fun _ => a), free := fun _ => A }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.fvar .here) (.fvar (.there (.there .here)))
  have h : ∀ x, φ.satisfies ((PowerlessComprehension.env_l η).pushFree x) ↔ value_l R x a := by
    intro x
    dsimp only [φ]
    rw [value_formula_l]
    rfl
  obtain ⟨C, hC⟩ := PowerlessComprehension.separation_l hℳ φ η A
  exact ⟨C, fun x => (hC x).trans (and_congr Iff.rfl (h x))⟩

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (A R a : carrier_l ℳ) :
    ∃ S, segment_l S A R a := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases R (fun _ => a), free := fun _ => A }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    .disj (SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.fvar .here) (.fvar (.there (.there .here))))
      (.equal (.fvar .here) (.fvar (.there (.there .here))))
  have h : ∀ x, φ.satisfies ((PowerlessComprehension.env_l η).pushFree x) ↔ value_l R x a ∨ x = a := by
    intro x
    simp only [φ, Formula.satisfies, value_formula_l]
    rfl
  obtain ⟨S, hS⟩ := PowerlessComprehension.separation_l hℳ φ η A
  exact ⟨S, fun x => (hS x).trans (and_congr Iff.rfl (h x))⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {S T A R a : carrier_l ℳ} (hS : segment_l S A R a) (hT : segment_l T A R a) : S = T :=
  (PowerlessTheory.ext_l hℳ).eq_of_same_members S T (fun x => (hS x).trans (hT x).symm)

theorem predecessor_initial_l {C A R a : carrier_l ℳ} (hR : wellOrder_l A R)
    (ha : member_l ℳ a A) (hC : predecessor_l C A R a) : initial_l C A R := by
  refine ⟨fun x hx => ((hC x).mp hx).1, ?_⟩
  intro x hx y hy h
  obtain ⟨hx, h₀⟩ := (hC x).mp hx
  exact (hC y).mpr ⟨hy, hR.2.1 y x a ⟨hy, hx, ha⟩ h h₀⟩

theorem initial_segment_l {S A R a : carrier_l ℳ} (hR : wellOrder_l A R)
    (ha : member_l ℳ a A) (hS : segment_l S A R a) : initial_l S A R := by
  refine ⟨fun x hx => ((hS x).mp hx).1, ?_⟩
  intro x hx y hy h
  obtain ⟨hx, h₀⟩ := (hS x).mp hx
  apply (hS y).mpr
  refine ⟨hy, Or.inl ?_⟩
  rcases h₀ with h₀ | h₀
  · exact hR.2.1 y x a ⟨hy, hx, ha⟩ h h₀
  · exact h₀ ▸ h

theorem extension_l {C S A R a : carrier_l ℳ} (ha : member_l ℳ a A)
    (hC : predecessor_l C A R a) (hS : segment_l S A R a) :
    ∀ x, member_l ℳ x S ↔ member_l ℳ x C ∨ x = a := by
  intro x
  rw [hS x, hC x]
  constructor
  · rintro ⟨hx, h | h⟩
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  · rintro (⟨hx, h⟩ | h)
    · exact ⟨hx, Or.inl h⟩
    · exact ⟨h.symm ▸ ha, Or.inr h⟩

theorem below_l {A R a x D C : carrier_l ℳ} (hR : wellOrder_l A R)
    (ha : member_l ℳ a A) (hx : member_l ℳ x A) (h : value_l R x a)
    (hD : segment_l D A R x) (hC : predecessor_l C A R a) : subset_l D C := by
  intro y hy
  obtain ⟨hy, h₀⟩ := (hD y).mp hy
  apply (hC y).mpr
  refine ⟨hy, ?_⟩
  rcases h₀ with h₀ | h₀
  · exact hR.2.1 y x a ⟨hy, hx, ha⟩ h₀ h
  · exact h₀.symm ▸ h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessInitialSegment
