import BMSConstructibleBridge.ThirdOrderSkolemLimit

/-!
# 极限级的全部内部有限参数统一落在序列某一级

归纳命题量化实际 n→C 赋值图。后继步反向分解末项，在序列的共同
严格后级合并前缀全部参数和末项。归纳运行在模型内部 ω，不只覆盖
宿主标准有限元组，也不借用 κ 内任取的更大界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSkolemParameters

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne PowerlessHierarchyStage ThirdOrderSkolemSequence

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def bounded_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ f C n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) :=
    (((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set (.imp (SecondOrderObjectSyntax.map_m (.bvar .here)
    (n.weakenBound SetTheory.SetSort.set) (C.weakenBound SetTheory.SetSort.set))
    (.existsE .set (.existsE .set (.existsE .set (.conj
      (SecondOrderObjectSyntax.value_m (w f) (.bvar (.there (.there .here))) (.bvar (.there .here))) (.conj
        (stage_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (.bvar (.there .here)) (.bvar .here))
        (SecondOrderObjectSyntax.map_m (.bvar (.there (.there (.there .here)))) (w n) (.bvar .here))))))))

theorem bounded_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ f C n : Term ℒ Γ Δ .set) :
    (bounded_m ω e T t₁ t₂ t₃ f C n).satisfies η ↔
      ∀ g, map_l g (n.eval η) (C.eval η) → ∃ i a A, value_l (f.eval η) i a ∧
        stage_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) a A ∧
        map_l g (n.eval η) A := by
  simp only [bounded_m, Formula.satisfies, map_formula_l, value_formula_l, stage_formula_l hℳ, Term.eval_weakenBound]
  rfl

theorem bounded_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U F α f ξ C : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (hf : sequence_l ω e T t₁ t₂ t₃ κ U F α f) (hξ : PowerlessOrdinalSupremum.supremum_l f ξ)
    (hC : stage_l ω e T t₁ t₂ t₃ ξ C) :
    ∀ n, member_l ℳ n ω → ∀ g, map_l g n C → ∃ i a A,
      value_l f i a ∧ stage_l ω e T t₁ t₂ t₃ a A ∧ map_l g n A := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 8 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁ (Fin.cases t₂ (Fin.cases t₃ (Fin.cases f (fun _ => C))))))), free := fun _ => U }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    bounded_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.fvar .here)
  have h : ∀ n, φ.satisfies ((PowerlessComprehension.env_l η).pushFree n) ↔
      ∀ g, map_l g n C → ∃ i a A, value_l f i a ∧ stage_l ω e T t₁ t₂ t₃ a A ∧ map_l g n A :=
    fun n => bounded_formula_l hℳ _ _ _ _ _ _ _ _ _ _
  obtain ⟨A, hA⟩ := PowerlessHierarchyStage.exists_l hℳ hω
    (PowerlessOrdinal.mem_l hκ.1 (PowerlessFunction.value_mem_l hℳ hf.1 hf.2.1).2) e T t₁ t₂ t₃
  have h₀ := PowerlessNatural.induction_l hℳ φ η hω
    (fun z hz => (h z).mpr (by
      intro g hg
      exact ⟨e, α, A, hf.2.1, hA, PowerlessFunction.range_l hℳ hg
        (fun x _ hx => (hz x (PowerlessFunction.value_mem_l hℳ hg hx).1).elim)⟩))
    (fun n m _ hm h₁ => (h m).mpr (by
      intro g hg
      obtain ⟨r, x, hr, hx, hg⟩ := PowerlessAppendGraph.decompose_l hℳ hg hm
      obtain ⟨i, a, A, hi, hA, hr⟩ := (h n).mp h₁ r hr
      obtain ⟨j, b, B, hj, hB, hx⟩ := (ThirdOrderSkolemLimit.levels_l hℳ hω hf hξ hC x).mp hx
      obtain ⟨k, hk, hik, hjk⟩ := PowerlessNaturalBounds.strict_l hℳ hω
        (PowerlessFunction.value_mem_l hℳ hf.1 hi).1 (PowerlessFunction.value_mem_l hℳ hf.1 hj).1
      obtain ⟨c, hc, _⟩ := hf.1.2 k hk
      obtain ⟨D, hD⟩ := PowerlessHierarchyStage.exists_l hℳ hω (PowerlessOrdinal.mem_l hκ.1 hc.1) e T t₁ t₂ t₃
      have hAD := PowerlessStageStructure.subset_l hℳ hω hA hD (monotone_l hℳ hω hκ hf k hk i a c hik hi hc.2)
      have hBD := PowerlessStageStructure.subset_l hℳ hω hB hD (monotone_l hℳ hω hκ hf k hk j b c hjk hj hc.2)
      exact ⟨k, c, D, hc.2, hD, PowerlessAppendGraph.map_l hℳ
        (PowerlessFunction.range_l hℳ hr (fun y v hv => hAD v (PowerlessFunction.value_mem_l hℳ hr hv).2))
        (hBD x hx) hm hg⟩))
  exact fun n hn => (h n).mp (h₀ n hn)

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSkolemParameters
