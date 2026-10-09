import BMSConstructibleBridge.PowerlessSatisfactionExistenceSyntax
import BMSConstructibleBridge.PowerlessSourceInclusion
import BMSConstructibleBridge.PowerlessRelativeFiniteElementarity

/-! # 同一有限元素性域的完整静态编码运输

八参数矩阵逐字采用原 static_m，包含完整三角递推、构造器总唯一性、
序列和合法性图规格。MemberW 到 MemberI 的运输只消费该原公式的
元素性；不要求 I 传递，不用有界检查器替代完整规格。
这里只给对象公式及语义运输，最终原 Z₂ 推导仍须完成候选源构造。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullStatic

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

abbrev context_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set]

/-- 从最深绑定槽至首槽为 ω、e、t₁、t₂、t₃、T、N、F。 -/
def matrix_m (Δ : SortContext ℒ) : Formula ℒ context_m Δ :=
  PowerlessSatisfactionExistenceSyntax.static_m
    (.bvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.bvar (.there (.there (.there (.there (.there .here))))))
    (.bvar (.there (.there (.there (.there .here)))))
    (.bvar (.there (.there (.there .here))))
    (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def family_m (Δ : SortContext ℒ) : PowerlessRelativeFiniteElementarity.family_m Δ :=
  [Sigma.mk context_m (matrix_m Δ)]

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def env_l {Δ : SortContext ℒ} (ν : Env 𝒩 [] Δ)
    (ω e t₁ t₂ t₃ T N F : carrier_l 𝒩) : Env 𝒩 context_m Δ :=
  let η₀ := ((ν.pushBound ω).pushBound e).pushBound t₁
  let η₁ := ((η₀.pushBound t₂).pushBound t₃).pushBound T
  (η₁.pushBound N).pushBound F

theorem formula_l {Δ : SortContext ℒ} (η : Env 𝒩 context_m Δ) :
    (matrix_m Δ).satisfies η ↔ PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒩)
      (η.boundVal (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (η.boundVal (.there (.there (.there (.there (.there (.there .here)))))))
      (η.boundVal (.there (.there (.there (.there (.there .here))))))
      (η.boundVal (.there (.there (.there (.there .here)))))
      (η.boundVal (.there (.there (.there .here))))
      (η.boundVal (.there (.there .here))) (η.boundVal (.there .here)) (η.boundVal .here) := by
  rw [matrix_m, PowerlessSatisfactionExistenceSyntax.static_formula_l]
  rfl

/-- 同一 I⊆W 上的完整静态包同值，无需任一成员域满足源理论。 -/
theorem model_l {Δ Ε : SortContext ℒ} {I₀ W₀ : carrier_l 𝒩}
    (hI : ∃ x, member_l 𝒩 x I₀) (hW : ∃ x, member_l 𝒩 x W₀)
    (ζ : Env 𝒩 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env (PowerlessMemberStructure.structure_l I₀ hI) [] Δ)
    (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hIW : subset_l (ℳ := 𝒩) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (ω e t₁ t₂ t₃ T N F : PowerlessMemberStructure.type_l (ℳ := 𝒩) I₀) :
    PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := PowerlessMemberStructure.structure_l W₀ hW)
      (PowerlessSourceInclusion.inclusion_l hIW ω)
      (PowerlessSourceInclusion.inclusion_l hIW e)
      (PowerlessSourceInclusion.inclusion_l hIW t₁)
      (PowerlessSourceInclusion.inclusion_l hIW t₂)
      (PowerlessSourceInclusion.inclusion_l hIW t₃)
      (PowerlessSourceInclusion.inclusion_l hIW T)
      (PowerlessSourceInclusion.inclusion_l hIW N)
      (PowerlessSourceInclusion.inclusion_l hIW F) ↔
      PowerlessSatisfactionExistenceSyntax.static_l
        (𝒩 := PowerlessMemberStructure.structure_l I₀ hI) ω e t₁ t₂ t₃ T N F := by
  let η := env_l ν ω e t₁ t₂ t₃ T N F
  let ξ := PowerlessSourceInclusion.env_l (hU := hW) hIW η
  have hEnv : PowerlessRelativization.env_l ξ = PowerlessRelativization.env_l η := by
    apply Env.ext <;> intro _ _ <;> rfl
  change (PowerlessRelativeFiniteElementarity.entry_m (matrix_m Δ) I W τ).satisfies ζ ∧ True at h
  have hReflect := (PowerlessRelativeFiniteElementarity.entry_formula_l
    (matrix_m Δ) ζ I W τ (PowerlessRelativization.env_l ν) hτ).mp h.1
      (PowerlessRelativization.env_l η) (fun _ _ => rfl)
      (fun v => hI₀.symm ▸ (η.boundVal v).property)
  rw [hI₀, hW₀] at hReflect
  have hReadW := PowerlessRelativization.formula_l (matrix_m Δ) ξ
  rw [hEnv] at hReadW
  have hRead := hReadW.symm.trans
    (hReflect.trans (PowerlessRelativization.formula_l (matrix_m Δ) η))
  exact (formula_l ξ).symm.trans (hRead.trans (formula_l η))

#print axioms formula_l
#print axioms model_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullStatic
