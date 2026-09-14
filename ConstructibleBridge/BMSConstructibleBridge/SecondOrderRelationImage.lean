import BMSConstructibleBridge.SecondOrderOrderedLayer
import BMSConstructibleBridge.SecondOrderGraftSemantics

/-!
# 内部数关系的集合论有序对像

输入一张内部关系实数，端点仅需各自在指定旧关系的根域中。统一有序对层与
实际根选择理解给出一个真正的集合对象；不使用替换、收集或外部实数族选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelationImage

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem roots_l (hℳ : Theory.Models ℳ theory_m) (S : set_l ℳ) :
    ∃ P : set_l ℳ, ∀ r, mem_l r P ↔ ∃ a b, relation_l S a b ∧
      SecondOrderOrderedLayer.root_l a b = r := by
  let φ : Formula signature_m [] [.num, .set] :=
    .existsE .num (.existsE .num (.conj
      (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here))
      (SecondOrderOrderedLayer.formula_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))))
  have hφ : language_m φ = true := by
    change (language_m (GraphSyntax.edge_m (Γ := [.num, .num]) (Δ := [.num, .set])
      (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here)) &&
      language_m (SecondOrderOrderedLayer.formula_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))) = true
    have h := pure_language_m _ (GraphSyntax.edge_pure_m
      (Γ := [.num, .num]) (Δ := [.num, .set])
      (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here) rfl rfl rfl)
    rw [h, SecondOrderOrderedLayer.pure_m _ _ _ rfl rfl rfl]
    rfl
  obtain ⟨P, hP⟩ := comprehension_l hℳ φ hφ ((Env.empty (M := ℳ)).pushFree S)
  refine ⟨P, fun r => (hP r).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderOrderedLayer.formula_l]
  rfl

/-- 完整成员规格，包含无序对内部证书而不固定外部的有序对代表函数。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R S : set_l ℳ)
    (hS : ∀ a b, relation_l S a b → SecondOrderDomain.wf_l R a ∧ SecondOrderDomain.wf_l R b) :
    ∃ F : SecondOrderGraph.code_l ℳ, ∀ D, SecondOrderGraph.mem_l D F ↔
      ∃ a b, ∃ h : relation_l S a b, SecondOrderPairObjects.ordered_l hℳ
        (SecondOrderQuotient.mk_l hℳ ⟨R, a, (hS a b h).1⟩)
        (SecondOrderQuotient.mk_l hℳ ⟨R, b, (hS a b h).2⟩) (SecondOrderQuotient.mk_l hℳ D) := by
  obtain ⟨G, hG⟩ := SecondOrderPairLayer.exists_l hℳ R
  obtain ⟨H, hH⟩ := SecondOrderPairLayer.exists_l hℳ G
  obtain ⟨P, hP⟩ := roots_l hℳ S
  have h₀ : ∀ r, mem_l r P → SecondOrderDomain.wf_l H r := by
    intro r hr
    obtain ⟨a, b, h, rfl⟩ := (hP r).mp hr
    exact SecondOrderOrderedLayer.wf_l hℳ R G H hG hH a b (hS a b h).1 (hS a b h).2
  obtain ⟨F, hF⟩ := SecondOrderGraftSemantics.exists_l hℳ H P h₀
  refine ⟨F, fun D => (hF D).trans ?_⟩
  constructor
  · rintro ⟨r, hr, h⟩
    obtain ⟨a, b, h₁, rfl⟩ := (hP r).mp hr
    let C := SecondOrderOrderedLayer.code_l hℳ R G H hG hH a b (hS a b h₁).1 (hS a b h₁).2
    have h₂ : SecondOrderQuotient.mk_l hℳ D = SecondOrderQuotient.mk_l hℳ C :=
      (SecondOrderQuotient.eq_iff_l hℳ D C).mpr h
    refine ⟨a, b, h₁, ?_⟩
    rw [h₂]
    exact SecondOrderOrderedLayer.ordered_l hℳ R G H hG hH a b (hS a b h₁).1 (hS a b h₁).2
  · rintro ⟨a, b, h₁, h⟩
    let C := SecondOrderOrderedLayer.code_l hℳ R G H hG hH a b (hS a b h₁).1 (hS a b h₁).2
    have h₂ := SecondOrderPairObjects.ordered_unique_l hℳ h
      (SecondOrderOrderedLayer.ordered_l hℳ R G H hG hH a b (hS a b h₁).1 (hS a b h₁).2)
    exact ⟨SecondOrderOrderedLayer.root_l a b, (hP _).mpr ⟨a, b, h₁, rfl⟩,
      (SecondOrderQuotient.eq_iff_l hℳ D C).mp h₂⟩

/-- 同一构造在商对象上的完整有序对成员规格。 -/
theorem quotient_l (hℳ : Theory.Models ℳ theory_m) (R S : set_l ℳ)
    (hS : ∀ a b, relation_l S a b → SecondOrderDomain.wf_l R a ∧ SecondOrderDomain.wf_l R b) :
    ∃ f : SecondOrderQuotient.type_l hℳ, ∀ p, SecondOrderQuotient.mem_l hℳ p f ↔
      ∃ a b, ∃ h : relation_l S a b, SecondOrderPairObjects.ordered_l hℳ
        (SecondOrderQuotient.mk_l hℳ ⟨R, a, (hS a b h).1⟩)
        (SecondOrderQuotient.mk_l hℳ ⟨R, b, (hS a b h).2⟩) p := by
  obtain ⟨F, hF⟩ := exists_l hℳ R S hS
  refine ⟨SecondOrderQuotient.mk_l hℳ F, fun p => ?_⟩
  obtain ⟨P, rfl⟩ := SecondOrderQuotient.surj_l hℳ p
  exact hF P

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelationImage
