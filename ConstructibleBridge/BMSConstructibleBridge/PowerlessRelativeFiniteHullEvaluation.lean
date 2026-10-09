import BMSConstructibleBridge.PowerlessSatisfactionSpecification
import BMSConstructibleBridge.PowerlessSourceInclusion
import BMSConstructibleBridge.PowerlessRelativeFiniteElementarity

/-! # 同一有限元素性域的完整原 Sat 运输

保留原完整无界 Sat 规格的九个参数；并非有界检查器。两侧成员环境
由同一实际 I⊆W 的包含映射给出，原公式元素性直接比较完整规格。
本模块不假定 I 传递，也不预供 raw 与 MemberI 的满足关系对应。
W 中原规格的成立由实际共尾层绝对性取得，再由 SourceHistory 消费
这一原公式族。这里只给语义中间桥，不代替最终源存在性或 Z₂ 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullEvaluation

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

abbrev context_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set, .set]

/-- 从最深绑定槽至首槽为 ω、A、e、t₁、t₂、t₃、T、F、R。 -/
def matrix_m (Δ : SortContext ℒ) : Formula ℒ context_m Δ :=
  PowerlessSatisfactionSpecification.spec_m (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.here)))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.here))))))))
    (.bvar (.there (.there (.there (.there (.there (.here)))))))
    (.bvar (.there (.there (.there (.there (.here))))))
    (.bvar (.there (.there (.there (.here)))))
    (.bvar (.there (.there (.here))))
    (.bvar (.there (.here)))
    (.bvar (.here))

def family_m (Δ : SortContext ℒ) : PowerlessRelativeFiniteElementarity.family_m Δ :=
  [Sigma.mk context_m (matrix_m Δ)]

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 所有数据由原参数给出；不从存在命题抽取 Type 数据。 -/
def env_l {Δ : SortContext ℒ} (ν : Env 𝒩 [] Δ)
    (ω A e t₁ t₂ t₃ T F R : carrier_l 𝒩) : Env 𝒩 context_m Δ :=
  let η₀ := ((ν.pushBound ω).pushBound A).pushBound e
  let η₁ := ((η₀.pushBound t₁).pushBound t₂).pushBound t₃
  ((η₁.pushBound T).pushBound F).pushBound R

theorem formula_l {Δ : SortContext ℒ} (η : Env 𝒩 context_m Δ) :
    (matrix_m Δ).satisfies η ↔ PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒩)
      (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))
      (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.here)))))))))
      (η.boundVal (.there (.there (.there (.there (.there (.there (.here))))))))
      (η.boundVal (.there (.there (.there (.there (.there (.here)))))))
      (η.boundVal (.there (.there (.there (.there (.here))))))
      (η.boundVal (.there (.there (.there (.here)))))
      (η.boundVal (.there (.there (.here))))
      (η.boundVal (.there (.here)))
      (η.boundVal (.here)) := by
  rw [matrix_m, PowerlessSatisfactionSpecification.spec_formula_l]
  rfl

/-- 两侧完整原 Sat 同值；I/W 只作为成员域，不要求它们属于自身。 -/
theorem model_l {Δ Ε : SortContext ℒ} {I₀ W₀ : carrier_l 𝒩}
    (hI : ∃ x, member_l 𝒩 x I₀) (hW : ∃ x, member_l 𝒩 x W₀)
    (ζ : Env 𝒩 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env (PowerlessMemberStructure.structure_l I₀ hI) [] Δ)
    (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hIW : subset_l (ℳ := 𝒩) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (ω A e t₁ t₂ t₃ T F R : PowerlessMemberStructure.type_l (ℳ := 𝒩) I₀) :
    PowerlessSatisfactionSpecification.spec_l (𝒩 := PowerlessMemberStructure.structure_l W₀ hW)
      (PowerlessSourceInclusion.inclusion_l hIW ω)
      (PowerlessSourceInclusion.inclusion_l hIW A)
      (PowerlessSourceInclusion.inclusion_l hIW e)
      (PowerlessSourceInclusion.inclusion_l hIW t₁)
      (PowerlessSourceInclusion.inclusion_l hIW t₂)
      (PowerlessSourceInclusion.inclusion_l hIW t₃)
      (PowerlessSourceInclusion.inclusion_l hIW T)
      (PowerlessSourceInclusion.inclusion_l hIW F)
      (PowerlessSourceInclusion.inclusion_l hIW R) ↔
      PowerlessSatisfactionSpecification.spec_l
        (𝒩 := PowerlessMemberStructure.structure_l I₀ hI) ω A e t₁ t₂ t₃ T F R := by
  let η := env_l ν ω A e t₁ t₂ t₃ T F R
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

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullEvaluation
