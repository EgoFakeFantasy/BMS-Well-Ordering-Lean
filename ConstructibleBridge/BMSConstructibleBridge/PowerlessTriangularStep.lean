import BMSConstructibleBridge.PowerlessAdditionSyntax
import BMSConstructibleBridge.PowerlessProduct

/-!
# 三角数的内部状态算子

在 P=ω×ω 上把 (n,t) 送到 (n+1,t+(n+1))；P 外取恒等值。
后一分支只为已有集合递归接口提供总算子，不约束非法输入的算术。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTriangularStep

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural PowerlessAddition

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def step_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let φ : Formula ℒ [.set, .set, .set, .set] [.set, .set, .set, .set, .set] :=
    .conj (SecondOrderObjectSyntax.ordered_m (.bvar (.there (.there (.there .here))))
      (.bvar (.there (.there .here))) (.fvar (.there .here)))
    (.conj (PowerlessNaturalStep.successor_m (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)))
    (.conj (PowerlessAdditionSyntax.addition_m (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
      (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))))
  let ψ := SecondOrderObjectSyntax.member_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
  .disj (.conj ψ (.existsE .set (.existsE .set (.existsE .set (.existsE .set φ)))))
    (.conj (.neg ψ) (.equal (.fvar .here) (.fvar (.there .here))))

def env_l (ω e P : carrier_l ℳ) : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 3 :=
  { bound := Fin.cases P (Fin.cases e (fun _ => ω)), free := fun _ => ω }

def step_l (ω e P x y : carrier_l ℳ) : Prop :=
  (member_l ℳ x P ∧ ∃ n t m v, ordered_l n t x ∧ PowerlessNatural.successor_l n m ∧
    addition_l ω e t m v ∧ ordered_l m v y) ∨ (¬ member_l ℳ x P ∧ y = x)

theorem step_formula_l (ω e P x y : carrier_l ℳ) :
    step_m.satisfies (((PowerlessComprehension.env_l (env_l ω e P)).pushFree x).pushFree y) ↔
      step_l ω e P x y := by
  simp only [step_m, step_l, Formula.satisfies, ordered_formula_l,
    PowerlessNaturalStep.successor_formula_l, PowerlessAdditionSyntax.addition_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e P : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hP : PowerlessProduct.product_l ω ω P) (x : carrier_l ℳ) : ∃ y, step_l ω e P x y := by
  classical
  by_cases hx : member_l ℳ x P
  · obtain ⟨n, hn, t, ht, h₀⟩ := (hP x).mp hx
    obtain ⟨m, hm⟩ := successor_exists_l hℳ n
    obtain ⟨v, _, hv⟩ := PowerlessAddition.exists_l hℳ hω he ht (successor_mem_l hℳ hω hn hm)
    obtain ⟨y, hy⟩ := PowerlessBasic.ordered_exists_l hℳ m v
    exact ⟨y, Or.inl ⟨hx, n, t, m, v, h₀, hm, hv, hy⟩⟩
  · exact ⟨x, Or.inr ⟨hx, rfl⟩⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e P x y z : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hy : step_l ω e P x y) (hz : step_l ω e P x z) : y = z := by
  rcases hy with ⟨hx, n, t, m, v, h₀, hm, hv, hy⟩ | ⟨hx, hy⟩
  · rcases hz with ⟨_, a, b, c, d, h₁, hc, hd, hz⟩ | ⟨h₁, _⟩
    · obtain ⟨h₂, h₃⟩ := (PowerlessBasic.ordered_eq_l hℳ h₀ h₁).mp rfl
      subst a
      subst b
      have h₂ := successor_unique_l hℳ hm hc
      subst c
      have h₃ := PowerlessAddition.unique_l hℳ hω he hv hd
      subst d
      exact PowerlessBasic.ordered_unique_l hℳ hy hz
    · exact (h₁ hx).elim
  · rcases hz with ⟨h₁, _⟩ | ⟨_, hz⟩
    · exact (hx h₁).elim
    · exact hy.trans hz.symm

theorem coordinates_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e P n t x y : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hP : PowerlessProduct.product_l ω ω P) (hn : member_l ℳ n ω) (ht : member_l ℳ t ω)
    (hx : ordered_l n t x) (hy : step_l ω e P x y) :
    ∃ m v, PowerlessNatural.successor_l n m ∧ member_l ℳ v ω ∧ addition_l ω e t m v ∧ ordered_l m v y := by
  have hx₀ := (hP x).mpr ⟨n, hn, t, ht, hx⟩
  rcases hy with ⟨_, a, b, m, v, h₀, hm, hv, hy⟩ | ⟨h₀, _⟩
  · obtain ⟨h₁, h₂⟩ := (PowerlessBasic.ordered_eq_l hℳ hx h₀).mp rfl
    subst a
    subst b
    obtain ⟨f, hf, hF⟩ := hv
    exact ⟨m, v, hm, PowerlessAddition.range_l hℳ hω he ht hf m v hF, ⟨f, hf, hF⟩, hy⟩
  · exact (h₀ hx₀).elim

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTriangularStep
