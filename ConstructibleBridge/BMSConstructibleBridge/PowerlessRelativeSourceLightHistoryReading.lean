import BMSConstructibleBridge.PowerlessRelativeSourceFamilyHistory
import BMSConstructibleBridge.PowerlessMemberCollapseTransport

/-! # 同一共同族的完整轻量前史运输

实际源前史的完整 Δ₀ 矩阵由原共同族反射到非传递 MemberI，再沿
同一 H 运输并在传递 T 中读回。三个原分支及极限并的两向成员覆盖
均保留；没有按模型外部序数归纳，也不把 I 当作传递域。
目标仍是固定 D 的轻量历史。原 Def 图的完整读数由独立图运输接口
提供后才能恢复原构造历史，不能把本接口单独称为弱凝聚或终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceLightHistoryReading

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 同一实际图的零、后继与精确极限并方程共同运输。 -/
theorem history_l {I₀ W₀ T H : type_l hℳ} {Δ Ε : SortContext ℒ}
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set → Term ℒ [] Ε .set)
    (hI : ∃ x, mem_l hℳ x I₀) (hT : ∃ x, mem_l hℳ x T)
    (ν : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI)
      [] (PowerlessRelativeSourceFamilyHistory.context_m Δ))
    (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, mem_l hℳ x W₀ → ∀ y, mem_l hℳ y x → mem_l hℳ y W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m
      (PowerlessRelativeSourceFamilyHistory.family_m Δ) I W τ).satisfies ζ)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I₀ T H)
    (B₀ D₀ A₀ U₀ f : PowerlessMemberStructure.type_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) I₀)
    (B₁ D₁ A₁ U₁ g : PowerlessMemberStructure.type_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) T)
    (hB : PowerlessMemberCollapseTransport.relation_l H B₀ B₁)
    (hD : PowerlessMemberCollapseTransport.relation_l H D₀ D₁)
    (hA : PowerlessMemberCollapseTransport.relation_l H A₀ A₁)
    (hU : PowerlessMemberCollapseTransport.relation_l H U₀ U₁)
    (hfg : PowerlessMemberCollapseTransport.relation_l H f g)
    (hf : PowerlessHierarchyLightHistory.history_l hℳ B₀.val D₀.val A₀.val U₀.val f.val) :
    PowerlessHierarchyLightHistory.history_l hℳ B₁.val D₁.val A₁.val U₁.val g.val := by
  let η : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI) [.set, .set, .set, .set, .set]
      (PowerlessRelativeSourceFamilyHistory.context_m Δ) :=
    ν |>.pushBound B₀ |>.pushBound D₀ |>.pushBound A₀ |>.pushBound U₀ |>.pushBound f
  let η₀ := PowerlessRelativization.env_l η
  let φ := PowerlessRelativeFiniteHullHistory.matrix_m (PowerlessRelativeSourceFamilyHistory.context_m Δ)
  have hFamily := PowerlessRelativeSourceFamilyHistory.history_l ζ I W τ h
  change (PowerlessRelativeFiniteElementarity.entry_m
    (PowerlessRelativeFiniteHullHistory.exists_m (PowerlessRelativeSourceFamilyHistory.context_m Δ))
    I W τ).satisfies ζ ∧ (PowerlessRelativeFiniteElementarity.entry_m φ I W τ).satisfies ζ ∧ True at hFamily
  have hReflect := (PowerlessRelativeFiniteElementarity.entry_formula_l φ ζ I W τ
    (PowerlessRelativization.env_l ν) hτ).mp hFamily.2.1 η₀ (fun _ _ => rfl)
      (fun v => hI₀.symm ▸ (η.boundVal v).property)
  rw [hI₀, hW₀] at hReflect
  have hNonempty : ∃ x, mem_l hℳ x W₀ := by
    obtain ⟨x, hx⟩ := hI
    exact ⟨x, hIW x hx⟩
  have hAbsolute := PowerlessMemberBounded.relativized_l hW hNonempty
    (PowerlessRelativeFiniteHullHistory.matrix_delta_l (PowerlessRelativeSourceFamilyHistory.context_m Δ)) η₀
    (fun v => hIW _ (η.boundVal v).property) (fun v => hIW _ (ν.freeVal v).property)
  have hSource : φ.satisfies η₀ := (PowerlessHierarchyLightHistory.reading_formula_l hℳ η₀
    (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here))))
    (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).mpr hf
  have hNative := (PowerlessRelativization.formula_l φ η).mp (hReflect.mp (hAbsolute.mpr hSource))
  have hMember := (PowerlessHierarchyLightHistory.formula_l η
    (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here))))
    (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).mp hNative
  let η₁ : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI) [.set, .set, .set, .set, .set] [] :=
    Env.empty |>.pushBound B₀ |>.pushBound D₀ |>.pushBound A₀ |>.pushBound U₀ |>.pushBound f
  let ξ : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) T hT) [.set, .set, .set, .set, .set] [] :=
    Env.empty |>.pushBound B₁ |>.pushBound D₁ |>.pushBound A₁ |>.pushBound U₁ |>.pushBound g
  have hEnv : PowerlessMemberCollapseTransport.environments_related_l
      (PowerlessMemberCollapseTransport.relation_l H) η₁ ξ := by
    constructor
    · intro v
      cases v with
      | here => exact hfg
      | there v => cases v with
        | here => exact hU
        | there v => cases v with
          | here => exact hA
          | there v => cases v with
            | here => exact hD
            | there v => cases v with
              | here => exact hB
              | there v => nomatch v
    · intro v
      nomatch v
  have hSource₁ : (PowerlessRelativeFiniteHullHistory.matrix_m []).satisfies η₁ :=
    (PowerlessHierarchyLightHistory.formula_l η₁
      (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here))))
      (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).mpr hMember
  have hTarget := (PowerlessMemberCollapseTransport.member_l (hI := hI) (hT := hT)
    H hH.2.1 hH.2.2.1 hH.2.2.2.2.1 hH.2.2.2.2.2
    (PowerlessRelativeFiniteHullHistory.matrix_m []) η₁ ξ hEnv).mp hSource₁
  have hRaw := (PowerlessMemberBounded.formula_l hH.1
    (PowerlessRelativeFiniteHullHistory.matrix_delta_l []) ξ).mp hTarget
  exact (PowerlessHierarchyLightHistory.reading_formula_l hℳ (PowerlessRelativization.env_l ξ)
    (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here))))
    (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).mp hRaw

#print axioms history_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceLightHistoryReading
