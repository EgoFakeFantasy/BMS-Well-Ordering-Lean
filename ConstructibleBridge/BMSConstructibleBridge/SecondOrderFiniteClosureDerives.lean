import BMSConstructibleBridge.SecondOrderFiniteClosedCover
import BMSConstructibleBridge.PowerlessFiniteClosureMinimum

/-!
# 任意集合的最小有限子集闭包：原 Z₂ 对象推导

有限性使用商模型自己的 ω 和双射枚举。先取得实际闭合超集，再按原纯集合
公式分离最小闭包；目标是该闭句的原图翻译，不是新增符号或条件假设。
这只是相对可构造层的辅助定理，尚不包含 Def、Collection 或 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteClosureDerives

open Logic FirstOrder PowerlessFiniteClosureSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

def sentence_m : Sentence ℒ :=
  .forallE .set (.imp (SecondOrderOmegaSyntax.omega_m (.bvar .here))
    (.forallE .set (.existsE .set (closure_m (.bvar (.there (.there .here)))
      (.bvar (.there .here)) (.bvar .here)))))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (ω : SecondOrderQuotient.type_l hℳ) (hω : SecondOrderOmega.omega_l hℳ ω)
    (x : SecondOrderQuotient.type_l hℳ) :
    ∃ c, closure_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω x c := by
  obtain ⟨C⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hEq := SecondOrderOmega.unique_l hℳ hω C.omega_spec
  obtain ⟨b, hxb, hb⟩ := SecondOrderFiniteClosedCover.exists_l C x
  rw [hEq]
  exact PowerlessFiniteClosureMinimum.exists_l (SecondOrderWeakSetTheory.models_l hℳ)
    C.omega x b hxb hb

theorem sentence_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) ↔
      ∀ ω : SecondOrderQuotient.type_l hℳ, SecondOrderOmega.omega_l hℳ ω →
        ∀ x, ∃ c, closure_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω x c := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies,
    SecondOrderOmegaSyntax.omega_l, closure_formula_l, Term.eval]
  rfl

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) :=
  (sentence_formula_l hℳ).mpr (exists_l hℳ)

/-- 原 Z₂ 推导核中的真实闭句证明；不调用完整 Collection。 -/
theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m sentence_m (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteClosureDerives
