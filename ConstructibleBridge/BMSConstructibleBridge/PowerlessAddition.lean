import BMSConstructibleBridge.PowerlessRecursionSyntax

/-!
# 内部自然数加法的一元迭代

在给定内部自然数 a 处起始，对集合后继作内部 ω 递归，得到 a+n。
加法的值、后继方程及其纯公式均消费同一个实际递归图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAddition

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def step_m : Formula ℒ [] [.set, .set] :=
  PowerlessNaturalStep.successor_m (.fvar (.there .here)) (.fvar .here)

def env_l (ω : carrier_l ℳ) : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 0 :=
  { bound := Fin.elim0, free := fun _ => ω }

theorem step_formula_l (ω x y : carrier_l ℳ) :
    step_m.satisfies (((PowerlessComprehension.env_l (env_l ω)).pushFree x).pushFree y) ↔ successor_l x y :=
  PowerlessNaturalStep.successor_formula_l _ _ _

def iteration_l (ω e a f : carrier_l ℳ) : Prop :=
  PowerlessOmegaRecursion.recursion_l step_m (env_l ω) f ω e a

theorem iteration_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) (a : carrier_l ℳ) :
    ∃ f, iteration_l ω e a f :=
  PowerlessOmegaRecursion.exists_l hℳ step_m (env_l ω)
    (fun x => (successor_exists_l hℳ x).imp fun y hy => (step_formula_l ω x y).mpr hy)
    (fun x y z hy hz => successor_unique_l hℳ ((step_formula_l ω x y).mp hy) ((step_formula_l ω x z).mp hz))
    hω he a

theorem iteration_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a f g : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e)
    (hf : iteration_l ω e a f) (hg : iteration_l ω e a g) : f = g :=
  PowerlessOmegaRecursion.unique_l hℳ step_m (env_l ω)
    (fun x y z hy hz => successor_unique_l hℳ ((step_formula_l ω x y).mp hy) ((step_formula_l ω x z).mp hz))
    hω he hf hg

theorem range_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a f : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) (ha : member_l ℳ a ω)
    (hf : iteration_l ω e a f) : ∀ n y, value_l f n y → member_l ℳ y ω := by
  obtain ⟨B, hf, hF, h₀⟩ := hf
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases f (fun _ => ω), free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    .forallE .set (.imp (SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there (.there .here)))))
  have h : ∀ n, φ.satisfies ((PowerlessComprehension.env_l η).pushFree n) ↔
      ∀ y, value_l f n y → member_l ℳ y ω := by
    intro n
    simp only [φ, Formula.satisfies, value_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
    rfl
  have h₁ := PowerlessNatural.induction_l hℳ φ η hω
    (fun z hz => (h z).mpr (by
      have h₂ := zero_unique_l hℳ hz he
      subst z
      intro y hy
      exact (PowerlessFunction.value_unique_l hℳ hf hy hF).symm ▸ ha))
    (fun n m hn hm h₂ => (h m).mpr (by
      intro y hy
      obtain ⟨x, hx, _⟩ := hf.2 n hn
      have h₃ := (h n).mp h₂ x hx.2
      exact successor_mem_l hℳ hω h₃ ((step_formula_l ω x y).mp (h₀ n m x y hn hm hx.2 hy))))
  exact fun n y hy => (h n).mp (h₁ n (PowerlessFunction.value_mem_l hℳ hf hy).1) y hy

def addition_l (ω e a b c : carrier_l ℳ) : Prop :=
  ∃ f, iteration_l ω e a f ∧ value_l f b c

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a b : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e)
    (ha : member_l ℳ a ω) (hb : member_l ℳ b ω) :
    ∃ c, member_l ℳ c ω ∧ addition_l ω e a b c := by
  obtain ⟨f, hf⟩ := iteration_exists_l hℳ hω he a
  obtain ⟨B, hF, h₀, h₁⟩ := hf
  have hf : iteration_l ω e a f := ⟨B, hF, h₀, h₁⟩
  obtain ⟨c, hc, _⟩ := hF.2 b hb
  exact ⟨c, range_l hℳ hω he ha hf b c hc.2, f, hf, hc.2⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a b c d : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e)
    (hc : addition_l ω e a b c) (hd : addition_l ω e a b d) : c = d := by
  obtain ⟨f, hf, hc⟩ := hc
  obtain ⟨g, hg, hd⟩ := hd
  have h := iteration_unique_l hℳ hω he hf hg
  subst g
  obtain ⟨B, hF, _⟩ := hf
  exact PowerlessFunction.value_unique_l hℳ hF hc hd

theorem zero_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a c : carrier_l ℳ} (h : addition_l ω e a e c) : c = a := by
  obtain ⟨f, ⟨B, hf, hF, _⟩, hc⟩ := h
  exact PowerlessFunction.value_unique_l hℳ hf hc hF

theorem successor_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a n m c d : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hn : member_l ℳ n ω) (hm : PowerlessNatural.successor_l n m)
    (hc : addition_l ω e a n c) (hd : addition_l ω e a m d) : PowerlessNatural.successor_l c d := by
  obtain ⟨f, hf, hc⟩ := hc
  obtain ⟨g, hg, hd⟩ := hd
  have h := iteration_unique_l hℳ hω he hf hg
  subst g
  obtain ⟨B, _, _, hF⟩ := hf
  exact (step_formula_l ω c d).mp (hF n m c d hn hm hc hd)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAddition
