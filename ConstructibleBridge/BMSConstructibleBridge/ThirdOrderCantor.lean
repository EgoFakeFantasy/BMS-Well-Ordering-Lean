import BMSConstructibleBridge.ThirdOrderSemantics
import BMSConstructibleBridge.PowerlessSeparation
import YesMetaZFC.SetTheory.Definitional.Project.FromFirstOrder

/-!
# 内部幂集不能单射回母集

对角子集由原纯公式经上游反向语法桥和实际分离公理构造。结论只需要
无幂集核心与指定母集的幂集见证，不把外部子集收集混进模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderCantor

open Logic FirstOrder ThirdOrderSemantics
open SetTheory.Definitional.Project

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def diagonal_m : FirstOrder.Formula ℒ [] [.set, .set] :=
  .neg (.existsE .set (.conj
    (SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.bvar .here) (.fvar .here))
    (SecondOrderObjectSyntax.member_m (.fvar .here) (.bvar .here))))

theorem diagonal_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (a f : carrier_l ℳ) :
    ∃ d, ∀ x, member_l ℳ x d ↔ member_l ℳ x a ∧ ¬∃ y, value_l f y x ∧ member_l ℳ x y := by
  let φ : SetTheory.Definitional.Project.UnarySchema 1 := {
    body := FromFirstOrder.translate (bound := []) (free := [.set, .set]) (depth := 2)
      (fun v => nomatch v) (fun v => v.position) diagonal_m
    freeClosed := FromFirstOrder.freeClosed _ _ _ }
  let η : SetTheory.Env (FirstOrderSemantics.reduct ℳ) 1 := { bound := fun _ => f, free := fun _ => a }
  obtain ⟨d, hd⟩ := PowerlessSeparation.exists_l hℳ φ η a
  refine ⟨d, fun x => (hd x).trans (and_congr Iff.rfl ?_)⟩
  have h := FromFirstOrder.correct (PowerlessTheory.ext_l hℳ) diagonal_m
    (fun v => nomatch v) (fun v => v.position)
    (((Env.empty (M := ℳ)).pushFree f).pushFree x) (η.push x)
    (fun v => nomatch v) (fun v => by match v with | .here => rfl | .there .here => rfl)
  refine h.trans ?_
  simp only [diagonal_m, FirstOrder.Formula.satisfies, value_formula_l]
  rfl

theorem no_injection_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a p : carrier_l ℳ} (hp : power_l a p) : ¬∃ f, map_l f p a ∧ injective_l f := by
  rintro ⟨f, hf, hF⟩
  obtain ⟨d, hd⟩ := diagonal_l hℳ a f
  have hD : subset_l d a := fun x h => ((hd x).mp h).1
  obtain ⟨x, hx, _⟩ := hf.2 d ((hp d).mpr hD)
  have h₀ : ¬member_l ℳ x d := by
    intro h
    exact ((hd x).mp h).2 ⟨d, hx.2, h⟩
  apply h₀
  apply (hd x).mpr
  refine ⟨hx.1, ?_⟩
  rintro ⟨y, hy, h⟩
  have h₁ := hF y d x hy hx.2
  exact h₀ (h₁ ▸ h)

/-- 任意本背景模型具有实际 ω 与实数对象，并在内部否定实数的可数单射。 -/
theorem uncountable_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m) :
    ∃ w p : carrier_l ℳ, omega_l w ∧ power_l w p ∧
      (¬∃ f, map_l f p w ∧ injective_l f) ∧ ∀ a, ∃ f, map_l f a p ∧ injective_l f := by
  obtain ⟨w, p, hw, hp, h⟩ := bounds_l hℳ
  exact ⟨w, p, hw, hp, no_injection_l (ThirdOrderTheory.core_l hℳ) hp, h⟩

/-- 全集规模界与 Cantor 一起排除再取一层幂集；背景并非完整 ZF。 -/
theorem power_boundary_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m) :
    ∃ w p : carrier_l ℳ, omega_l w ∧ power_l w p ∧ ¬∃ q, power_l p q := by
  obtain ⟨w, p, hw, hp, h⟩ := bounds_l hℳ
  refine ⟨w, p, hw, hp, ?_⟩
  rintro ⟨q, hq⟩
  exact no_injection_l (ThirdOrderTheory.core_l hℳ) hq (h q)

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderCantor
