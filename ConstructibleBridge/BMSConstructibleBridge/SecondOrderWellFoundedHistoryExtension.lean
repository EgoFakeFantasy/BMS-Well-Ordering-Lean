import BMSConstructibleBridge.SecondOrderWellFoundedHistoryUnion

/-! # 相容历史并的一行延长

用原理解构造一张仅替换末端行的实数。严格前驱局部性使旧行与新末端行
同时满足操作方程；此步骤不需要原集合论的替换或收集公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellFoundedHistoryExtension

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderWellFoundedAgreement

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def patch_m : Formula signature_m [] [.num, .num, .num, .set, .set] :=
  .disj (.conj (.equal (.fvar .here) (.fvar (.there (.there .here))))
    (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))))
    (.conj (.neg (.equal (.fvar .here) (.fvar (.there (.there .here)))))
      (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.fvar .here) (.fvar (.there .here))))

theorem patch_exists_l (hℳ : Theory.Models ℳ theory_m) (S V : set_l ℳ) (n : num_l ℳ) :
    ∃ H, ∀ m a, relation_l H m a ↔
      (m = n ∧ relation_l V m a) ∨ (m ≠ n ∧ relation_l S m a) := by
  obtain ⟨H, hH⟩ := SecondOrderRelations.comprehension_l hℳ patch_m rfl
    ((((Env.empty (M := ℳ)).pushFree V).pushFree S).pushFree n)
  refine ⟨H, fun m a => (hH m a).trans ?_⟩
  simp only [patch_m, Formula.satisfies, SecondOrderPairing.edge_l, Term.eval]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (P : set_l ℳ → set_l ℳ → Prop) (R : set_l ℳ)
    (hWf : ∀ n, SecondOrderDomain.wf_l R n)
    (hTrans : ∀ a b c, relation_l R a b → relation_l R b c → relation_l R a c)
    (hIrrefl : ∀ n, ¬relation_l R n n) (hLocal : local_l P R) (hTotal : ∀ H, ∃ U, P H U)
    (n : num_l ℳ) (S : set_l ℳ)
    (hExist : ∀ m, relation_l R m n → ∃ H, good_l P R H m)
    (hS : ∀ m a, relation_l S m a ↔ relation_l R m n ∧ ∃ H, good_l P R H m ∧ relation_l H m a) :
    ∃ H, good_l P R H n := by
  obtain ⟨V, hV⟩ := hTotal S
  obtain ⟨H, hH⟩ := patch_exists_l hℳ S V n
  obtain ⟨W, hW⟩ := hTotal H
  have hBelow m (hm : relation_l R m n) a : relation_l H m a ↔ relation_l S m a := by
    have hmn : m ≠ n := by
      intro h
      subst m
      exact hIrrefl n hm
    rw [hH m a]
    constructor
    · rintro (⟨hm, _⟩ | ⟨_, h⟩)
      · exact False.elim (hmn hm)
      · exact h
    · intro h
      exact Or.inr ⟨hmn, h⟩
  have hEnd a : relation_l H n a ↔ relation_l V n a := by
    rw [hH n a]
    constructor
    · rintro (⟨_, h⟩ | ⟨hn, _⟩)
      · exact h
      · exact False.elim (hn rfl)
    · intro h
      exact Or.inl ⟨rfl, h⟩
  refine ⟨H, W, hW, ?_⟩
  intro m hm a
  rcases hm with hmn | hm
  · subst m
    exact (hEnd a).trans (hLocal H S W V hW hV n hBelow a).symm
  · obtain ⟨K, hK⟩ := hExist m hm
    have hAgree := SecondOrderWellFoundedHistoryUnion.agrees_l hℳ P R S
      hWf hTrans hLocal n hExist hS m hm K hK
    obtain ⟨U, hU, hKU⟩ := hK
    have hPre : ∀ b, relation_l R b m → ∀ c, relation_l H b c ↔ relation_l K b c := by
      intro b hb c
      exact (hBelow b (hTrans b m n hb hm) c).trans (hAgree b (Or.inr hb) c)
    exact (hBelow m hm a).trans ((hAgree m (Or.inl rfl) a).trans
      ((hKU m (Or.inl rfl) a).trans (hLocal H K W U hW hU m hPre a).symm))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellFoundedHistoryExtension
