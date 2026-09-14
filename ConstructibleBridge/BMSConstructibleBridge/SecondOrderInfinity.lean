import BMSConstructibleBridge.SecondOrderNaturalGraph
import BMSConstructibleBridge.SecondOrderGraftSemantics

/-!
# 任意二阶模型中的内部归纳集

每个模型数作为其小于关系初段的根，并把所有这些根选入一个新根。所得对象
含空对象且对 von Neumann 后继封闭；不把标准 Nat 枚举误当作模型数域的遍历。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInfinity

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderNaturalGraph

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem zero_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b) (B : SecondOrderGraph.code_l ℳ) :
    ¬SecondOrderGraph.mem_l B (code_l hℳ R hR (SecondOrderModel.zero_l ℳ)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  rintro ⟨a, h, _⟩
  exact (not_lt_of_ge (zero_le_l hℳ a)) ((hR a (SecondOrderModel.zero_l ℳ)).mp h)

theorem succ_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b)
    (n : num_l ℳ) (B : SecondOrderGraph.code_l ℳ) :
    SecondOrderGraph.mem_l B (code_l hℳ R hR (SecondOrderModel.succ_l n)) ↔
      SecondOrderGraph.mem_l B (code_l hℳ R hR n) ∨ SecondOrderGraph.eq_l B (code_l hℳ R hR n) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  constructor
  · rintro ⟨a, h, h₁⟩
    have h₂ := (lt_succ_l hℳ a n).mp ((hR a (SecondOrderModel.succ_l n)).mp h)
    rcases eq_or_lt_of_le h₂ with rfl | h₂
    · exact Or.inr h₁
    · exact Or.inl ⟨a, (hR a n).mpr h₂, h₁⟩
  · rintro (⟨a, h, h₁⟩ | h₁)
    · exact ⟨a, (hR a (SecondOrderModel.succ_l n)).mpr
        ((lt_succ_l hℳ a n).mpr (le_of_lt ((hR a n).mp h))), h₁⟩
    · exact ⟨n, (hR n (SecondOrderModel.succ_l n)).mpr ((lt_succ_l hℳ n n).mpr le_rfl), h₁⟩

/-- 完整归纳集规格；后继按成员与相等定义，没有新增对象函数符号。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) :
    ∃ W : SecondOrderGraph.code_l ℳ,
      (∃ E, (∀ B, ¬SecondOrderGraph.mem_l B E) ∧ SecondOrderGraph.mem_l E W) ∧
      ∀ A, SecondOrderGraph.mem_l A W → ∃ B, SecondOrderGraph.mem_l B W ∧
        ∀ C, SecondOrderGraph.mem_l C B ↔ SecondOrderGraph.mem_l C A ∨ SecondOrderGraph.eq_l C A := by
  obtain ⟨R, hR⟩ := relation_exists_l hℳ
  obtain ⟨P, hP⟩ := SecondOrderModel.comprehension_l hℳ .truth rfl (Env.empty (M := ℳ))
  have h₀ : ∀ n, mem_l n P := fun n => (hP n).mpr True.intro
  obtain ⟨W, hW⟩ := SecondOrderGraftSemantics.exists_l hℳ R P
    (fun n _ => SecondOrderNaturalGraph.wf_l hℳ R hR n)
  let N : num_l ℳ → SecondOrderGraph.code_l ℳ := code_l hℳ R hR
  have h₁ : ∀ B, SecondOrderGraph.mem_l B W ↔ ∃ n, SecondOrderGraph.eq_l B (N n) := by
    intro B
    refine (hW B).trans ?_
    exact ⟨fun ⟨n, _, h⟩ => ⟨n, h⟩, fun ⟨n, h⟩ => ⟨n, h₀ n, h⟩⟩
  refine ⟨W, ⟨N (SecondOrderModel.zero_l ℳ), zero_l hℳ R hR, ?_⟩, ?_⟩
  · exact (h₁ _).mpr ⟨SecondOrderModel.zero_l ℳ, SecondOrderGraph.refl_l hℳ _⟩
  · intro A h
    obtain ⟨n, h⟩ := (h₁ A).mp h
    refine ⟨N (SecondOrderModel.succ_l n), (h₁ _).mpr
      ⟨SecondOrderModel.succ_l n, SecondOrderGraph.refl_l hℳ _⟩, fun C => ?_⟩
    refine (succ_l hℳ R hR n C).trans (or_congr
      (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ C) h).symm ?_)
    exact ⟨fun h₂ => SecondOrderGraph.trans_l hℳ h₂ (SecondOrderGraph.symm_l hℳ h),
      fun h₂ => SecondOrderGraph.trans_l hℳ h₂ h⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInfinity
