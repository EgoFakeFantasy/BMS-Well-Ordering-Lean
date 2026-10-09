import BMSConstructibleBridge.PowerlessRelativeSourceFamilyHistory
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseSatisfactionFunctionReading

/-! # 原首 Ω 历史中实际满足函数的坍缩输出证书

同一原共尾编码包、实际首 Ω 层与十七式共同族给出 MemberI 的完整
静态包和全部 G 输出的原 Sat。十二槽资格由原八个静态参数、U∈I、
实际 A₀ 和逐次回溯的 R₀∈I 构造，不假设任意 raw 输出已在域中。
真实配对反射和基础闭包亦由该原共同族及实际非零极限层推出。
同一 H 固定整个实际 ω；目标所有输出的完整证书没有额外 Sat 前提。
这仍是原对象推导路线中的语义装配，不证明完整源存在或 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceSatisfactionReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 全部目标输出均由原历史装配，不再要求预供目标完整 Sat 或静态包。 -/
theorem reading_l {B U I₀ W₀ Ω T H : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ)
    {ω e t₁ t₂ t₃ P N F Q G : PowerlessRelativeClassStructure.type_l hℳ B}
    {C : SecondOrderModel.set_l ℳ}
    (hCoding : PowerlessRelativeCofinalDefCoding.spec_l
      (W := U) hBase K ω e t₁ t₂ t₃ P N F Q G C)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω.val Ω)
    (hLevel : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W₀)
    {Δ Ε : SortContext ℒ} (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set)
    (τ : Variable (PowerlessRelativeSourceFamilyHistory.context_m Δ) .set → Term ℒ [] Ε .set)
    (hI : ∃ x, mem_l hℳ x I₀) (hT : ∃ x, mem_l hℳ x T)
    (ν : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI)
      [] (PowerlessRelativeSourceFamilyHistory.context_m Δ))
    (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m
      (PowerlessRelativeSourceFamilyHistory.family_m Δ) I W τ).satisfies ζ)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I₀ T H)
    (hBound : ∀ v : Variable PowerlessRelativeFiniteHullStatic.context_m .set,
      mem_l hℳ ((PowerlessRelativeFiniteHullStatic.env_l (PowerlessRelativization.env_l ν)
        ω.val e.val t₁.val t₂.val t₃.val P.val N.val F.val).boundVal v) I₀)
    (hUI : mem_l hℳ U I₀) (hGI : mem_l hℳ G.val I₀)
    (hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I₀)
    (A₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀)
    (A₁ e₁ t₁₁ t₂₁ t₃₁ P₁ N₁ F₁ G₁ : PowerlessMemberStructure.type_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) T)
    (hA : SecondOrderFunctionObjects.value_l hℳ H A₀.val A₁.val)
    (he : SecondOrderFunctionObjects.value_l hℳ H e.val e₁.val)
    (ht₁ : SecondOrderFunctionObjects.value_l hℳ H t₁.val t₁₁.val)
    (ht₂ : SecondOrderFunctionObjects.value_l hℳ H t₂.val t₂₁.val)
    (ht₃ : SecondOrderFunctionObjects.value_l hℳ H t₃.val t₃₁.val)
    (hP : SecondOrderFunctionObjects.value_l hℳ H P.val P₁.val)
    (hN : SecondOrderFunctionObjects.value_l hℳ H N.val N₁.val)
    (hF : SecondOrderFunctionObjects.value_l hℳ H F.val F₁.val)
    (hG : SecondOrderFunctionObjects.value_l hℳ H G.val G₁.val) :
    ∀ R, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G₁.val A₁.val R →
      PowerlessRelativeMembershipCollapseEvaluation.data_l
        (𝒩 := SecondOrderQuotient.structure_l hℳ)
        K.omega A₁.val e₁.val t₁₁.val t₂₁.val t₃₁.val P₁.val N₁.val F₁.val R := by
  let ω₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨ω.val, hBound (.there (.there (.there (.there (.there (.there (.there .here)))))))⟩
  let e₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨e.val, hBound (.there (.there (.there (.there (.there (.there .here))))))⟩
  let t₁₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨t₁.val, hBound (.there (.there (.there (.there (.there .here)))))⟩
  let t₂₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨t₂.val, hBound (.there (.there (.there (.there .here))))⟩
  let t₃₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨t₃.val, hBound (.there (.there (.there .here)))⟩
  let P₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨P.val, hBound (.there (.there .here))⟩
  let N₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨N.val, hBound (.there .here)⟩
  let F₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨F.val, hBound .here⟩
  let G₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨G.val, hGI⟩
  have hω : SecondOrderOmega.omega_l hℳ ω.val := hCoding.omega_eq.symm ▸ K.omega_spec
  have hωI₀ : ∀ x, mem_l hℳ x ω.val → mem_l hℳ x I₀ :=
    fun x hx => hωI x (hCoding.omega_eq ▸ hx)
  have hTrans : PowerlessNaturalOrder.transitive_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) W₀ :=
    fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hLevel x hx y hy
  have hClosedW := PowerlessRelativeFiniteHullClosure.limit_closed_l hℳ hBase
    (PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ) hLevel
  obtain ⟨hReflect, hClosed⟩ := PowerlessRelativeSourceFamilyHistory.closure_member_l
    ζ I W τ hI₀ hW₀ hTrans hClosedW hIW h
  have hStatic := PowerlessRelativeSourceFamilyHistory.static_member_l
    hBase K hCoding hΩ hLevel ζ I W τ hI ν hτ hI₀ hW₀ hIW h hBound
  have hSat (R₀ : PowerlessMemberStructure.type_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) I₀)
      (hValue : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G.val A₀.val R₀.val) :
      PowerlessSatisfactionSpecification.spec_l
        (𝒩 := PowerlessMemberStructure.structure_l
          (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI)
        ω₀ A₀ e₀ t₁₀ t₂₀ t₃₀ P₀ F₀ R₀ := by
    have hBound' : ∀ v : Variable PowerlessRelativeFiniteHullSatisfaction.context_m .set,
        mem_l hℳ ((PowerlessRelativeFiniteHullSatCoding.env_l (PowerlessRelativization.env_l ν)
          ω.val A₀.val e.val N.val P.val U t₁.val t₂.val t₃.val F.val R₀.val).boundVal v) I₀ := by
      intro v
      match v with
      | .here => exact R₀.property
      | .there .here => exact hBound .here
      | .there (.there .here) => exact hBound (.there (.there (.there .here)))
      | .there (.there (.there .here)) => exact hBound (.there (.there (.there (.there .here))))
      | .there (.there (.there (.there .here))) =>
        exact hBound (.there (.there (.there (.there (.there .here)))))
      | .there (.there (.there (.there (.there .here)))) => exact hUI
      | .there (.there (.there (.there (.there (.there .here))))) => exact hUI
      | .there (.there (.there (.there (.there (.there (.there .here)))))) =>
        exact hBound (.there (.there .here))
      | .there (.there (.there (.there (.there (.there (.there (.there .here))))))) =>
        exact hBound (.there .here)
      | .there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) =>
        exact hBound (.there (.there (.there (.there (.there (.there .here))))))
      | .there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) =>
        exact A₀.property
      | .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) =>
        exact hBound (.there (.there (.there (.there (.there (.there (.there .here)))))))
      | .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there v))))))))))) =>
        nomatch v
    exact PowerlessRelativeSourceFamilyHistory.satisfaction_member_l
      hBase K hCoding hΩ hLevel ζ I W τ hI ν hτ hI₀ hW₀ hIW h hBound' hValue
  have hFixed := PowerlessRelativeMembershipCollapseBase.base_l hℳ ω.val I₀ T H
    (fun x hx y hy => SecondOrderOmegaTransitive.member_l hℳ hω hx hy)
    hωI₀ hH.2.1 hH.2.2.2.1 ω₀.property
  have hωT : mem_l hℳ ω.val T := by
    obtain ⟨z, hz, _⟩ := hH.2.1.2 ω.val ω₀.property
    exact (SecondOrderFunctionProperties.value_unique_l hℳ hH.2.1 hz.2 hFixed) ▸ hz.1
  let ω₁ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) T :=
    ⟨ω.val, hωT⟩
  have hRead := PowerlessRelativeMembershipCollapseSatisfactionFunctionReading.reading_l
    hI hT hH hTrans hIW hReflect hClosed
    ω₀ A₀ e₀ t₁₀ t₂₀ t₃₀ P₀ N₀ F₀ G₀ ω₁ A₁ e₁ t₁₁ t₂₁ t₃₁ P₁ N₁ F₁ G₁
    hFixed hA he ht₁ ht₂ ht₃ hP hN hF hG hω hωI₀ hStatic hSat
  intro R hValue
  have hData := hRead R hValue
  change PowerlessRelativeMembershipCollapseEvaluation.data_l
    (𝒩 := SecondOrderQuotient.structure_l hℳ)
    ω.val A₁.val e₁.val t₁₁.val t₂₁.val t₃₁.val P₁.val N₁.val F₁.val R at hData
  exact hCoding.omega_eq ▸ hData

#print axioms reading_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceSatisfactionReading
