import BMSConstructibleBridge.PowerlessNatural

/-!
# 内部自然数及其载体的传递性

用原纯语言的子集和传递公式实例化内部归纳，不对模型自然数作宿主归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessNaturalOrder

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def transitive_m {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.forallE .set (.imp
    (SecondOrderObjectSyntax.member_m (.bvar (.there .here))
      ((a.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set))
    (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
      (SecondOrderObjectSyntax.member_m (.bvar .here)
        ((a.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set)))))

def transitive_l (a : carrier_l ℳ) : Prop :=
  ∀ x y, member_l ℳ x a → member_l ℳ y x → member_l ℳ y a

theorem transitive_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a : Term ℒ Γ Δ .set) :
    Formula.satisfies η (transitive_m a) ↔ transitive_l (a.eval η) := by
  simp only [transitive_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound]
  rfl

theorem subset_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) :
    ∀ a, member_l ℳ a ω → ThirdOrderSemantics.subset_l a ω := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => ω, free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set] := ThirdOrderTheory.subset_m (.fvar .here) (.fvar (.there .here))
  have h : ∀ a, φ.satisfies ((PowerlessComprehension.env_l η).pushFree a) ↔
      ThirdOrderSemantics.subset_l a ω := by
    intro a
    dsimp only [φ]
    rw [subset_formula_l]
    rfl
  have h₀ := PowerlessNatural.induction_l hℳ φ η hω
    (fun e he => (h e).mpr (fun x hx => (he x hx).elim))
    (fun a b ha hb h₁ => (h b).mpr (fun x hx => by
      rcases (hb x).mp hx with h₂ | rfl
      · exact (h a).mp h₁ x h₂
      · exact ha))
  exact fun a ha => (h a).mp (h₀ a ha)

theorem omega_transitive_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) : transitive_l ω :=
  fun a b ha hb => subset_l hℳ hω a ha b hb

theorem member_transitive_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) :
    ∀ a, member_l ℳ a ω → transitive_l a := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 0 :=
    { bound := Fin.elim0, free := fun _ => ω }
  let φ : Formula ℒ [] [.set] := transitive_m (.fvar .here)
  have h : ∀ a, φ.satisfies ((PowerlessComprehension.env_l η).pushFree a) ↔ transitive_l a := by
    intro a
    dsimp only [φ]
    rw [transitive_formula_l]
    rfl
  have h₀ := PowerlessNatural.induction_l hℳ φ η hω
    (fun e he => (h e).mpr (fun x _ hx _ => (he x hx).elim))
    (fun a b _ hb h₁ => (h b).mpr (fun x y hx hy => by
      apply (hb y).mpr
      rcases (hb x).mp hx with h₂ | rfl
      · exact Or.inl ((h a).mp h₁ x y h₂ hy)
      · exact Or.inl hy))
  exact fun a ha => (h a).mp (h₀ a ha)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessNaturalOrder
