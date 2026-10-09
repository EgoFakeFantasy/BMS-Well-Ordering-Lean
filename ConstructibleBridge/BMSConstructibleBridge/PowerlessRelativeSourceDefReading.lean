import BMSConstructibleBridge.PowerlessRelativeSourceSatisfactionReading
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseDefReading

/-! # 同一原源历史和坍缩映射的局部 Def 精确截迹

原源 Def 先由原共尾编码包和共同族变为 MemberI 的实际八槽检查器，
沿同一 H 运输到指定 U 的像 V。完整 Sat 和静态读数由实际源历史
装配，旧翻译图保持原数字坐标，全部行族因此识别为目标的原 Def。
空母集分支保留原 {∅}，不错误地替换成空输出。原 H 的递归方程
同时给出 D₁=H[D₀∩I] 的精确成员规格，不假定 U⊆I 或目标是某个层。
这里只完成具备实际资格的局部步；全层后继／极限、弱凝聚、完整源
Collection 和最终固定外部高度的无条件 Derives Z₂ 仍须继续。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceDefReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 实际源 Def 的同一像是原目标 Def，且其全部成员正是原递归截迹。 -/
theorem trace_l {B β U I₀ W₀ Ω T H : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hU : PowerlessRelativeHierarchySemantics.level_l hℳ B β U)
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
    (hUI : mem_l hℳ U I₀) (hGI : mem_l hℳ G.val I₀) (hQI : mem_l hℳ Q.val I₀)
    (hωU : mem_l hℳ ω.val U)
    (hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I₀)
    (A₀ D₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀)
    (A₁ D₁ V e₁ t₁₁ t₂₁ t₃₁ P₁ N₁ F₁ Q₁ G₁ : PowerlessMemberStructure.type_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) T)
    (hAU : mem_l hℳ A₀.val U)
    (hDef : SecondOrderMemberDef.spec_l hℳ A₀.val D₀.val)
    (hA : SecondOrderFunctionObjects.value_l hℳ H A₀.val A₁.val)
    (hD : SecondOrderFunctionObjects.value_l hℳ H D₀.val D₁.val)
    (hUV : SecondOrderFunctionObjects.value_l hℳ H U V.val)
    (he : SecondOrderFunctionObjects.value_l hℳ H e.val e₁.val)
    (ht₁ : SecondOrderFunctionObjects.value_l hℳ H t₁.val t₁₁.val)
    (ht₂ : SecondOrderFunctionObjects.value_l hℳ H t₂.val t₂₁.val)
    (ht₃ : SecondOrderFunctionObjects.value_l hℳ H t₃.val t₃₁.val)
    (hP : SecondOrderFunctionObjects.value_l hℳ H P.val P₁.val)
    (hN : SecondOrderFunctionObjects.value_l hℳ H N.val N₁.val)
    (hF : SecondOrderFunctionObjects.value_l hℳ H F.val F₁.val)
    (hQ : SecondOrderFunctionObjects.value_l hℳ H Q.val Q₁.val)
    (hG : SecondOrderFunctionObjects.value_l hℳ H G.val G₁.val) :
    SecondOrderMemberDef.spec_l hℳ A₁.val D₁.val ∧
      ∀ Z, mem_l hℳ Z D₁.val ↔ ∃ Y, mem_l hℳ Y I₀ ∧ mem_l hℳ Y D₀.val ∧
        SecondOrderFunctionObjects.value_l hℳ H Y Z := by
  let ω₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨ω.val, hBound (.there (.there (.there (.there (.there (.there (.there .here)))))))⟩
  let e₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨e.val, hBound (.there (.there (.there (.there (.there (.there .here))))))⟩
  let P₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨P.val, hBound (.there (.there .here))⟩
  let N₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨N.val, hBound (.there .here)⟩
  let F₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨F.val, hBound .here⟩
  let Q₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨Q.val, hQI⟩
  let U₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨U, hUI⟩
  let G₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨G.val, hGI⟩
  have hω : SecondOrderOmega.omega_l hℳ ω.val := hCoding.omega_eq.symm ▸ K.omega_spec
  have hωI₀ : ∀ x, mem_l hℳ x ω.val → mem_l hℳ x I₀ :=
    fun x hx => hωI x (hCoding.omega_eq ▸ hx)
  have hFixed := PowerlessRelativeMembershipCollapseBase.base_l hℳ ω.val I₀ T H
    (fun x hx y hy => SecondOrderOmegaTransitive.member_l hℳ hω hx hy)
    hωI₀ hH.2.1 hH.2.2.2.1 ω₀.property
  have hωT : mem_l hℳ ω.val T := by
    obtain ⟨z, hz, _⟩ := hH.2.1.2 ω.val ω₀.property
    exact (SecondOrderFunctionProperties.value_unique_l hℳ hH.2.1 hz.2 hFixed) ▸ hz.1
  let ω₁ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) T :=
    ⟨ω.val, hωT⟩
  have hTransW := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hLevel
  have hClosedW := PowerlessRelativeFiniteHullClosure.limit_closed_l hℳ hBase
    (PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ) hLevel
  obtain ⟨hReflect, hClosed⟩ := PowerlessRelativeSourceFamilyHistory.closure_member_l
    ζ I W τ hI₀ hW₀ (fun x y hx hy => hTransW x hx y hy) hClosedW hIW h
  let η := PowerlessRelativeFiniteHullDefImage.env_l ν ω₀ e₀ N₀ Q₀ U₀ G₀ A₀ D₀
  let ξ := PowerlessRelativeFiniteHullDefImage.env_l
    (Env.empty (M := PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) T hT)) ω₁ e₁ N₁ Q₁ V G₁ A₁ D₁
  have hη : ∀ v : Variable PowerlessRelativeFiniteHullDefImage.context_m .set,
      (η.boundVal v).val =
        (PowerlessRelativeFiniteHullDefImage.env_l (PowerlessRelativization.env_l ν)
          ω.val e.val N.val Q.val U G.val A₀.val D₀.val).boundVal v := by
    intro v
    match v with
    | .here => rfl
    | .there .here => rfl
    | .there (.there .here) => rfl
    | .there (.there (.there .here)) => rfl
    | .there (.there (.there (.there .here))) => rfl
    | .there (.there (.there (.there (.there .here)))) => rfl
    | .there (.there (.there (.there (.there (.there .here))))) => rfl
    | .there (.there (.there (.there (.there (.there (.there .here)))))) => rfl
    | .there (.there (.there (.there (.there (.there (.there (.there v))))))) => nomatch v
  have hMember := (PowerlessRelativeSourceFamilyHistory.def_member_l hBase K hLimit hU
    hωU hCoding ζ I W τ hI ν hτ hI₀ hW₀ hTransW hIW h hAU η hη).mp hDef
  have hEnv : ∀ v : Variable PowerlessRelativeFiniteHullDefImage.context_m .set,
      PowerlessMemberCollapseTransport.relation_l H (η.boundVal v) (ξ.boundVal v) := by
    intro v
    match v with
    | .here => exact hD
    | .there .here => exact hA
    | .there (.there .here) => exact hG
    | .there (.there (.there .here)) => exact hUV
    | .there (.there (.there (.there .here))) => exact hQ
    | .there (.there (.there (.there (.there .here)))) => exact hN
    | .there (.there (.there (.there (.there (.there .here))))) => exact he
    | .there (.there (.there (.there (.there (.there (.there .here)))))) => exact hFixed
    | .there (.there (.there (.there (.there (.there (.there (.there v))))))) => nomatch v
  have hImage : PowerlessMemberDefImageBounded.holds_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega e₁.val N₁.val Q₁.val V.val G₁.val A₁.val D₁.val := by
    have hRaw := (PowerlessRelativeFiniteHullDefImage.formula_l
      (PowerlessRelativization.env_l ξ)).mp
        ((PowerlessRelativeMembershipCollapseDefImage.model_l hI hT hH η ξ hEnv).mp hMember)
    change PowerlessMemberDefImageBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      ω.val e₁.val N₁.val Q₁.val V.val G₁.val A₁.val D₁.val at hRaw
    exact hCoding.omega_eq ▸ hRaw
  have hRead := PowerlessRelativeSourceSatisfactionReading.reading_l
    hBase K hCoding hΩ hLevel ζ I W τ hI hT ν hτ hI₀ hW₀ hIW h hH
    hBound hUI hGI hωI A₀ A₁ e₁ t₁₁ t₂₁ t₃₁ P₁ N₁ F₁ G₁
    hA he ht₁ ht₂ ht₃ hP hN hF hG
  have hTarget : SecondOrderMemberDef.spec_l hℳ A₁.val D₁.val := by
    rcases hImage with hEmpty | ⟨hNonempty, hRows⟩
    · exact Or.inl hEmpty
    · have hA₁ : ∃ x, mem_l hℳ x A₁.val := by
        classical
        by_contra hEmpty
        exact hNonempty (fun x hx => hEmpty ⟨x, hx⟩)
      have hImage' : PowerlessMemberDefImageBounded.holds_l
          (𝒩 := SecondOrderQuotient.structure_l hℳ)
          K.omega e₁.val N₁.val Q₁.val V.val G₁.val A₁.val D₁.val :=
        Or.inr ⟨hNonempty, hRows⟩
      obtain ⟨R, _, _, _, _, _, _, _, _, _, hValue, _, _⟩ :=
        PowerlessRelativeMembershipCollapseDefImage.rows_l hImage' hA₁
      have hStatic := (hRead R hValue).1
      obtain ⟨_, _, _, _, _, _, hPair, hValid⟩ :=
        PowerlessRelativeClassStaticCodingReading.reading_l
          (hBase := hBase) K hCoding.omega_eq hCoding.static
      have hAU' := (hH.2.2.2.2.2 A₀.val U A₁.val V.val A₀.property hUI hA hUV).mp hAU
      apply Or.inr
      exact PowerlessRelativeMembershipCollapseDefReading.nonempty_l (hℳ := hℳ) K
        (I := I₀) (W := W₀) (T := T) (H := H) (U := U) (V := V.val) hI hT hH
        (fun x y hx hy => hTransW x hx y hy) hIW hReflect hClosed
        (PowerlessRelativeFiniteHullClosure.limit_closed_l hℳ hBase hLimit hU)
        (fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hU x hx y hy)
        hUI hUV hωI (hCoding.omega_eq ▸ ω₀.property) (hCoding.omega_eq ▸ hωU)
        P₀ F₀ Q₀ P₁ F₁ Q₁ hP hF hQ hPair hValid hCoding.translation_numeric
        hCoding.legacy_translation hStatic (fun R hValue => (hRead R hValue).2)
        hAU' hImage' hA₁
  exact ⟨hTarget, hH.2.2.2.1 D₀.val D₁.val D₀.property hD⟩

#print axioms trace_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceDefReading
