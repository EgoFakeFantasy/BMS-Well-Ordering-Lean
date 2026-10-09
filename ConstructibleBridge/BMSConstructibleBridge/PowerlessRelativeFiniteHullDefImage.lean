import BMSConstructibleBridge.PowerlessMemberDefImageBounded
import BMSConstructibleBridge.PowerlessMemberBounded
import BMSConstructibleBridge.PowerlessRelativeFiniteElementarity

/-! # 同一成员域的完整 Def 像检查器

八参数矩阵保留原检查器的全部数据见证、指标覆盖和双向行覆盖。
传递外层 W 的纯 Δ₀ 绝对性与同一 I 的原公式元素性共同给出
raw 检查器和 MemberI 检查器的等价；不要求非传递 I 的绝对性。
本接口不把该检查器改称原 global_m，也不预供 I 内的可数枚举。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullDefImage

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

abbrev context_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set]

/-- 最深绑定槽至首槽为 ω、e、N、F、U、G、A、D。 -/
def matrix_m (Δ : SortContext ℒ) : Formula ℒ context_m Δ :=
  PowerlessMemberDefImageBounded.formula_m
    (.bvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.bvar (.there (.there (.there (.there (.there .here))))))
    (.bvar (.there (.there (.there (.there .here)))))
    (.bvar (.there (.there (.there .here))))
    (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def family_m (Δ : SortContext ℒ) : PowerlessRelativeFiniteElementarity.family_m Δ :=
  [Sigma.mk context_m (matrix_m Δ)]

theorem delta_l (Δ : SortContext ℒ) :
    Formula.IsDelta0 membershipLevyBound (matrix_m Δ) :=
  PowerlessMemberDefImageBounded.delta_l _ _ _ _ _ _ _ _

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def env_l {Δ : SortContext ℒ} (ν : Env 𝒩 [] Δ)
    (ω e N F U G A D : carrier_l 𝒩) : Env 𝒩 context_m Δ :=
  let η₀ := ((ν.pushBound ω).pushBound e).pushBound N
  let η₁ := ((η₀.pushBound F).pushBound U).pushBound G
  (η₁.pushBound A).pushBound D

theorem formula_l {Δ : SortContext ℒ} (η : Env 𝒩 context_m Δ) :
    (matrix_m Δ).satisfies η ↔ PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒩)
      (η.boundVal (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (η.boundVal (.there (.there (.there (.there (.there (.there .here)))))))
      (η.boundVal (.there (.there (.there (.there (.there .here))))))
      (η.boundVal (.there (.there (.there (.there .here)))))
      (η.boundVal (.there (.there (.there .here))))
      (η.boundVal (.there (.there .here))) (η.boundVal (.there .here)) (η.boundVal .here) := by
  rw [matrix_m, PowerlessMemberDefImageBounded.formula_l]
  rfl

/-- 同一 I 的反射使全部检查器见证在 I 内解释，而非只检查已有见证。 -/
theorem model_l {Δ Ε : SortContext ℒ} {I₀ W₀ : carrier_l 𝒩}
    (hI : ∃ x, member_l 𝒩 x I₀) (ζ : Env 𝒩 [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env (PowerlessMemberStructure.structure_l I₀ hI) [] Δ)
    (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, member_l 𝒩 x W₀ → ∀ y, member_l 𝒩 y x → member_l 𝒩 y W₀)
    (hIW : subset_l (ℳ := 𝒩) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (ω e N F U G A D : PowerlessMemberStructure.type_l (ℳ := 𝒩) I₀) :
    PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒩)
      ω.val e.val N.val F.val U.val G.val A.val D.val ↔
      PowerlessMemberDefImageBounded.holds_l
        (𝒩 := PowerlessMemberStructure.structure_l I₀ hI) ω e N F U G A D := by
  let η := env_l ν ω e N F U G A D
  let ξ := PowerlessRelativization.env_l η
  have hWNonempty : ∃ x, member_l 𝒩 x W₀ := by
    obtain ⟨x, hx⟩ := hI
    exact ⟨x, hIW x hx⟩
  change (PowerlessRelativeFiniteElementarity.entry_m (matrix_m Δ) I W τ).satisfies ζ ∧ True at h
  have hReflect := (PowerlessRelativeFiniteElementarity.entry_formula_l
    (matrix_m Δ) ζ I W τ (PowerlessRelativization.env_l ν) hτ).mp h.1 ξ
      (fun _ _ => rfl) (fun v => hI₀.symm ▸ (η.boundVal v).property)
  rw [hI₀, hW₀] at hReflect
  have hAbsolute := PowerlessMemberBounded.relativized_l hW hWNonempty (delta_l Δ) ξ
    (fun v => hIW _ (η.boundVal v).property) (fun v => hIW _ (ν.freeVal v).property)
  have hRaw := formula_l ξ
  have hMember := formula_l η
  exact hRaw.symm.trans (hAbsolute.symm.trans
    (hReflect.trans (PowerlessRelativization.formula_l (matrix_m Δ) η)) |>.trans hMember)

#print axioms delta_l
#print axioms formula_l
#print axioms model_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullDefImage
