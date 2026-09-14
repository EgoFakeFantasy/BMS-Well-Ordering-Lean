import BMSConstructibleBridge.SecondOrderIteration

/-!
# 内部图域中的成员极小节点

对同一模型中的选点实数取关系极小元。反证时用已构造的内部依赖链违反
根域公式，不将该公式升级为宿主良基性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraphMinimum

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private theorem invariant (hℳ : Theory.Models ℳ theory_m) (X P : set_l ℳ) (a : num_l ℳ)
    (hX : function_l X) (h₀ : relation_l X (zero_l ℳ) a) (ha : mem_l a P)
    (h : ∀ i b c, relation_l X i b → relation_l X (succ_l i) c → mem_l b P → mem_l c P) :
    ∀ i b, relation_l X i b → mem_l b P := by
  let φ : Formula signature_m [] [.num, .set, .set] :=
    .forallE .num (.imp
      (GraphSyntax.edge_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
      (.rel .mem (.cons (.bvar .here) (.cons (.fvar (.there (.there .here))) .nil))))
  apply induct_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree P).pushFree X)
    (fun i => ∀ b, relation_l X i b → mem_l b P) ?_ ?_ ?_
  · intro i
    simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l]
    rfl
  · intro b hb
    exact (hX (zero_l ℳ)).unique hb h₀ ▸ ha
  · intro i hi c hc
    obtain ⟨b, hb, _⟩ := hX i
    exact h i b c hb hc (hi b hb)

theorem subset_l (hℳ : Theory.Models ℳ theory_m) (R P : set_l ℳ)
    (hP : ∃ a, mem_l a P) (hR : ∀ a, mem_l a P → SecondOrderDomain.wf_l R a) :
    ∃ a, mem_l a P ∧ ∀ b, relation_l R b a → ¬mem_l b P := by
  classical
  by_contra h
  have h₁ : ∀ a, mem_l a P → ∃ b, relation_l R b a ∧ mem_l b P := by
    intro a ha
    by_contra h₂
    exact h ⟨a, ha, fun b hb hc => h₂ ⟨b, hb, hc⟩⟩
  let φ : Formula signature_m [] [.num, .num, .set, .set] :=
    .disj (.conj (.rel .mem (.cons (.fvar .here) (.cons (.fvar (.there (.there (.there .here)))) .nil)))
      (.conj (.rel .mem (.cons (.fvar (.there .here)) (.cons (.fvar (.there (.there (.there .here)))) .nil)))
        (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here))))
      (.conj (.neg (.rel .mem (.cons (.fvar .here) (.cons (.fvar (.there (.there (.there .here)))) .nil))))
        (.equal (.fvar (.there .here)) (Term.app (σ := signature_m) .zero .nil)))
  obtain ⟨S, hS⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree P).pushFree R)
  have h₂ : ∀ a b, relation_l S a b ↔
      (mem_l a P ∧ mem_l b P ∧ relation_l R b a) ∨ (¬mem_l a P ∧ b = zero_l ℳ) := by
    intro a b
    refine (hS a b).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l]
    rfl
  have h₃ : ∀ a, ∃ b, relation_l S a b := by
    intro a
    by_cases ha : mem_l a P
    · obtain ⟨b, hb, hc⟩ := h₁ a ha
      exact ⟨b, (h₂ a b).mpr (Or.inl ⟨ha, hc, hb⟩)⟩
    · exact ⟨zero_l ℳ, (h₂ a _).mpr (Or.inr ⟨ha, rfl⟩)⟩
  obtain ⟨a, ha⟩ := hP
  obtain ⟨X, hX, h₀, h₄⟩ := SecondOrderIteration.chain_l hℳ S a h₃
  have h₅ : ∀ i b, relation_l X i b → mem_l b P := by
    apply invariant hℳ X P a hX h₀ ha
    intro i b c hb hc hd
    rcases (h₂ b c).mp (h₄ i b c hb hc) with h | h
    · exact h.2.1
    · exact False.elim (h.1 hd)
  obtain ⟨i, b, c, hb, hc, h₆⟩ := hR a ha X hX h₀
  rcases (h₂ b c).mp (h₄ i b c hb hc) with h | h
  · exact h₆ h.2.2
  · exact h.1 (h₅ i b hb)

/-- 只要求选点集合与内部域有交，不要求其所有节点先验属于域。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R P : set_l ℳ) (a : num_l ℳ)
    (hR : SecondOrderDomain.wf_l R a) (ha : mem_l a P) :
    ∃ b, mem_l b P ∧ SecondOrderDomain.wf_l R b ∧ ∀ c, relation_l R c b → ¬mem_l c P := by
  let φ : Formula signature_m [] [.num, .set, .set] :=
    .conj (.rel .mem (.cons (.fvar .here) (.cons (.fvar (.there (.there .here))) .nil)))
      (GraphTranslation.domain_m (.fvar (.there .here)) (.fvar .here))
  have hφ : language_m φ = true :=
    GraphTranslation.domain_pure_m _ _ rfl rfl
  obtain ⟨Q, hQ⟩ := comprehension_l hℳ φ hφ
    (((Env.empty (M := ℳ)).pushFree P).pushFree R)
  have h₁ : ∀ b, mem_l b Q ↔ mem_l b P ∧ SecondOrderDomain.wf_l R b := by
    intro b
    refine (hQ b).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderInterpretation.domain_l]
    rfl
  obtain ⟨b, hb, h₂⟩ := subset_l hℳ R Q ⟨a, (h₁ a).mpr ⟨ha, hR⟩⟩
    (fun b hb => ((h₁ b).mp hb).2)
  have h₃ := (h₁ b).mp hb
  exact ⟨b, h₃.1, h₃.2, fun c hc hd => h₂ c hc
    ((h₁ c).mpr ⟨hd, SecondOrderDomain.child_l hℳ R b c h₃.2 hc⟩)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraphMinimum
