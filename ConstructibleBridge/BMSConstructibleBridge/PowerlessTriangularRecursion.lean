import BMSConstructibleBridge.PowerlessTriangularStep

/-!
# 状态递归的内部坐标不变量

对纯公式“第 n 项为 (n,t)，其中 t∈ω”作内部归纳。
投影所得三角数图因此覆盖全部内部自然数，不只覆盖标准迭代。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTriangularRecursion

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural PowerlessTriangularStep

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def iteration_l (ω e P p F : carrier_l ℳ) : Prop :=
  PowerlessOmegaRecursion.recursion_l step_m (env_l ω e P) F ω e p

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e P : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e)
    (hP : PowerlessProduct.product_l ω ω P) (p : carrier_l ℳ) : ∃ F, iteration_l ω e P p F :=
  PowerlessOmegaRecursion.exists_l hℳ step_m (env_l ω e P)
    (fun x => (PowerlessTriangularStep.exists_l hℳ hω he hP x).imp fun y hy => (step_formula_l ω e P x y).mpr hy)
    (fun x y z hy hz => PowerlessTriangularStep.unique_l hℳ hω he
      ((step_formula_l ω e P x y).mp hy) ((step_formula_l ω e P x z).mp hz)) hω he p

def coordinates_m : Formula ℒ [] [.set, .set, .set] :=
  .forallE .set (.imp (SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
    (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there (.there .here))))
      (SecondOrderObjectSyntax.ordered_m (.fvar .here) (.bvar .here) (.bvar (.there .here))))))

theorem coordinates_formula_l (η : Env ℳ [] [.set, .set, .set]) : coordinates_m.satisfies η ↔
    ∀ p, value_l (η.freeVal (.there .here)) (η.freeVal .here) p →
      ∃ t, member_l ℳ t (η.freeVal (.there (.there .here))) ∧ ordered_l (η.freeVal .here) t p := by
  simp only [coordinates_m, Formula.satisfies, value_formula_l, ordered_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

theorem coordinates_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e P p F : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e)
    (hP : PowerlessProduct.product_l ω ω P) (hp : ordered_l e e p) (hF : iteration_l ω e P p F) :
    ∀ n q, value_l F n q → ∃ t, member_l ℳ t ω ∧ ordered_l n t q := by
  obtain ⟨B, hF, h₀, h₁⟩ := hF
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases F (fun _ => ω), free := fun _ => ω }
  have h : ∀ n, coordinates_m.satisfies ((PowerlessComprehension.env_l η).pushFree n) ↔
      ∀ q, value_l F n q → ∃ t, member_l ℳ t ω ∧ ordered_l n t q := fun n => coordinates_formula_l _
  have h₂ := PowerlessNatural.induction_l hℳ coordinates_m η hω
    (fun z hz => (h z).mpr (by
      have h₃ := zero_unique_l hℳ hz he
      subst z
      intro q hq
      have h₃ := PowerlessFunction.value_unique_l hℳ hF hq h₀
      subst q
      exact ⟨e, zero_mem_l hℳ hω he, hp⟩))
    (fun n m hn hm h₃ => (h m).mpr (by
      intro q hq
      obtain ⟨x, hx, _⟩ := hF.2 n hn
      obtain ⟨t, ht, h₄⟩ := (h n).mp h₃ x hx.2
      obtain ⟨k, v, hk, hv, _, h₅⟩ := PowerlessTriangularStep.coordinates_l hℳ hω he hP hn ht h₄
        ((step_formula_l ω e P x q).mp (h₁ n m x q hn hm hx.2 hq))
      have h₆ := successor_unique_l hℳ hk hm
      subst k
      exact ⟨v, hv, h₅⟩))
  exact fun n q hq => (h n).mp (h₂ n (PowerlessFunction.value_mem_l hℳ hF hq).1) q hq

def projection_m : Formula ℒ [] [.set, .set, .set] :=
  .existsE .set (.conj
    (SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.bvar .here))
    (SecondOrderObjectSyntax.ordered_m (.fvar (.there .here)) (.fvar .here) (.bvar .here)))

theorem projection_formula_l (η : Env ℳ [] [.set, .set, .set]) : projection_m.satisfies η ↔
    ∃ p, value_l (η.freeVal (.there (.there .here))) (η.freeVal (.there .here)) p ∧
      ordered_l (η.freeVal (.there .here)) (η.freeVal .here) p := by
  simp only [projection_m, Formula.satisfies, value_formula_l, ordered_formula_l]
  rfl

theorem projection_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e P p F : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e)
    (hP : PowerlessProduct.product_l ω ω P) (hp : ordered_l e e p) (hF : iteration_l ω e P p F) :
    ∃ T, map_l T ω ω ∧ ∀ n, member_l ℳ n ω → ∀ t,
      value_l T n t ↔ ∃ q, value_l F n q ∧ ordered_l n t q := by
  have h₀ := coordinates_l hℳ hω he hP hp hF
  obtain ⟨B, hF, _⟩ := hF
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => F, free := fun _ => ω }
  have h : ∀ n t, projection_m.satisfies (((PowerlessComprehension.env_l η).pushFree n).pushFree t) ↔
      ∃ q, value_l F n q ∧ ordered_l n t q := fun n t => projection_formula_l _
  obtain ⟨T, C, hT, _, h₁⟩ := PowerlessMapping.exists_l hℳ projection_m η ω
    (fun n hn => by
      obtain ⟨q, hq, _⟩ := hF.2 n hn
      obtain ⟨t, _, ht⟩ := h₀ n q hq.2
      exact ⟨t, (h n t).mpr ⟨q, hq.2, ht⟩⟩)
    (fun n _ t v ht hv => by
      obtain ⟨q, hq, ht⟩ := (h n t).mp ht
      obtain ⟨r, hr, hv⟩ := (h n v).mp hv
      have h₂ := PowerlessFunction.value_unique_l hℳ hF hq hr
      subst r
      exact ((PowerlessBasic.ordered_eq_l hℳ ht hv).mp rfl).2)
  have h₂ : ∀ n t, value_l T n t → member_l ℳ t ω := by
    intro n t ht
    obtain ⟨q, hq, h₃⟩ := (h n t).mp ((h₁ n (PowerlessFunction.value_mem_l hℳ hT ht).1 t).mp ht)
    obtain ⟨v, hv, h₄⟩ := h₀ n q hq
    have h₅ := ((PowerlessBasic.ordered_eq_l hℳ h₃ h₄).mp rfl).2
    exact h₅.symm ▸ hv
  exact ⟨T, PowerlessFunction.range_l hℳ hT h₂, fun n hn t => (h₁ n hn t).trans (h n t)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTriangularRecursion
