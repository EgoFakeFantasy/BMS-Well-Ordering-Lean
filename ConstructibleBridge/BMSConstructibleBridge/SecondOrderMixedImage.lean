import BMSConstructibleBridge.SecondOrderRelationImage

/-!
# 两张内部图之间的关系像

给两端不同标签后使用统一有序对像构造。端点的原图代表通过内部双模拟
接回，函数的左右对象不必使用同一关系实数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMixedImage

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def one {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .succ (.cons zero .nil)

theorem tagged_l (hℳ : Theory.Models ℳ theory_m) (S : set_l ℳ) :
    ∃ T : set_l ℳ, ∀ c d, relation_l T c d ↔ ∃ a b, relation_l S a b ∧
      c = value_l (zero_l ℳ) a ∧ d = value_l (succ_l (zero_l ℳ)) b := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .existsE .num (.existsE .num (.conj
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
      (.conj (PrimitiveFormulas.pair_m zero (.bvar (.there .here)) (.fvar .here))
        (PrimitiveFormulas.pair_m one (.bvar .here) (.fvar (.there .here))))))
  obtain ⟨T, hT⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((Env.empty (M := ℳ)).pushFree S)
  refine ⟨T, fun c d => (hT c d).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderPairing.formula_l]
  change (∃ a b, relation_l S a b ∧ value_l (zero_l ℳ) a = c ∧
    value_l (succ_l (zero_l ℳ)) b = d) ↔ _
  exact exists_congr (fun a => exists_congr (fun b => and_congr Iff.rfl (and_congr eq_comm eq_comm)))

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (X Y S : set_l ℳ)
    (hS : ∀ a b, relation_l S a b → SecondOrderDomain.wf_l X a ∧ SecondOrderDomain.wf_l Y b) :
    ∃ f : SecondOrderQuotient.type_l hℳ, ∀ p, SecondOrderQuotient.mem_l hℳ p f ↔
      ∃ a b, ∃ h : relation_l S a b, SecondOrderPairObjects.ordered_l hℳ
        (SecondOrderQuotient.mk_l hℳ ⟨X, a, (hS a b h).1⟩)
        (SecondOrderQuotient.mk_l hℳ ⟨Y, b, (hS a b h).2⟩) p := by
  obtain ⟨G, hX, hY⟩ := SecondOrderTaggedGraph.exists_l hℳ X Y
  obtain ⟨T, hT⟩ := tagged_l hℳ S
  have h₀ : ∀ c d, relation_l T c d → SecondOrderDomain.wf_l G c ∧ SecondOrderDomain.wf_l G d := by
    intro c d h
    obtain ⟨a, b, h₁, rfl, rfl⟩ := (hT c d).mp h
    exact ⟨SecondOrderTaggedDomain.wf_l hℳ (zero_l ℳ) X G hX a (hS a b h₁).1,
      SecondOrderTaggedDomain.wf_l hℳ (succ_l (zero_l ℳ)) Y G hY b (hS a b h₁).2⟩
  obtain ⟨f, hf⟩ := SecondOrderRelationImage.quotient_l hℳ G T h₀
  have h₁ (a b : num_l ℳ) (h : relation_l S a b) (c d : num_l ℳ)
      (hc : c = value_l (zero_l ℳ) a) (hd : d = value_l (succ_l (zero_l ℳ)) b)
      (h₂ : relation_l T c d) :
      SecondOrderQuotient.mk_l hℳ ⟨X, a, (hS a b h).1⟩ =
        SecondOrderQuotient.mk_l hℳ ⟨G, c, (h₀ c d h₂).1⟩ ∧
      SecondOrderQuotient.mk_l hℳ ⟨Y, b, (hS a b h).2⟩ =
        SecondOrderQuotient.mk_l hℳ ⟨G, d, (h₀ c d h₂).2⟩ := by
    subst c
    subst d
    exact ⟨(SecondOrderQuotient.eq_iff_l hℳ _ _).mpr
      (SecondOrderPairSet.tag_eq_l hℳ (zero_l ℳ) X G hX a),
      (SecondOrderQuotient.eq_iff_l hℳ _ _).mpr
        (SecondOrderPairSet.tag_eq_l hℳ (succ_l (zero_l ℳ)) Y G hY b)⟩
  refine ⟨f, fun p => (hf p).trans ?_⟩
  constructor
  · rintro ⟨c, d, h, hp⟩
    obtain ⟨a, b, h₂, hc, hd⟩ := (hT c d).mp h
    refine ⟨a, b, h₂, ?_⟩
    rw [(h₁ a b h₂ c d hc hd h).1, (h₁ a b h₂ c d hc hd h).2]
    exact hp
  · rintro ⟨a, b, h, hp⟩
    have h₂ := (hT _ _).mpr ⟨a, b, h, rfl, rfl⟩
    refine ⟨_, _, h₂, ?_⟩
    rw [← (h₁ a b h _ _ rfl rfl h₂).1, ← (h₁ a b h _ _ rfl rfl h₂).2]
    exact hp

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMixedImage
