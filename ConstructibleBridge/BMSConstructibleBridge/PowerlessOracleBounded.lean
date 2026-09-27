import BMSConstructibleBridge.PowerlessOracleClosure

/-!
# 低层公式证书的有界量词构造

全称分支按实际界集合收集更新证书，不要求该界外部有限。
收集条件是原公式，所取证书须经筛选后才能合并。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOracleBounded

open Logic FirstOrder ThirdOrderSemantics PowerlessTruthOracle PowerlessOracleClosure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem witnesses_l (B : Formula ℒ [] context_m)
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n p b f i A : carrier_l ℳ}
    (h : ∀ a, member_l ℳ a A → ∃ g, PowerlessAmbientAssignments.finite_l ω g ∧
      PowerlessAssignmentUpdate.update_l f i a g ∧ accepts_l B ω e T t₁ t₂ t₃ n p b g) :
    ∃ D, certificate_l B ω e T t₁ t₂ t₃ n D ∧
      ∀ a, member_l ℳ a A → PowerlessTruthWitness.witness_l ω D p b f i a := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 11 :=
    { bound := (Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁ (Fin.cases t₂ (Fin.cases t₃ (Fin.cases n (Fin.cases p (Fin.cases b (Fin.cases f (fun _ => i))))))))))), free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    .conj (PowerlessTruthOracle.certificate_m B (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.fvar .here))
      (PowerlessTruthWitness.witness_m (.fvar (.there (.there .here))) (.fvar .here)
        (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.fvar (.there .here)))
  have hφ : ∀ a D, φ.satisfies (((PowerlessComprehension.env_l η).pushFree a).pushFree D) ↔
      certificate_l B ω e T t₁ t₂ t₃ n D ∧ PowerlessTruthWitness.witness_l ω D p b f i a := by
    intro a D
    simp only [φ, Formula.satisfies, certificate_formula_l B hℳ, PowerlessTruthWitness.witness_formula_l]
    rfl
  obtain ⟨E, hE, h₀⟩ := family_l B hℳ φ η (A := A)
    (fun a ha => by
      obtain ⟨g, hg, hfg, D, hD, he⟩ := h a ha
      exact ⟨D, (hφ a D).mpr ⟨hD, g, hg, hfg, he⟩⟩)
    (fun a D hD => ((hφ a D).mp hD).1)
  refine ⟨E, hE, fun a ha => ?_⟩
  obtain ⟨D, hD, h₁⟩ := h₀ a ha
  exact PowerlessTruthMonotone.witness_l hD ((hφ a D).mp h₁).2

theorem positive_l (B : Formula ℒ [] context_m)
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n i j b c f z a g : carrier_l ℳ}
    (hc : member_l ℳ c ω) (hC : PowerlessBoundedCode.code_l ω e T t₂ t₃ i j b c)
    (hi : PowerlessAmbientAssignments.slot_l ω f i) (hz : value_l f j z)
    (ha : member_l ℳ a z) (hg : PowerlessAmbientAssignments.finite_l ω g)
    (hfg : PowerlessAssignmentUpdate.update_l f i a g)
    (h : accepts_l B ω e T t₁ t₂ t₃ n e b g) :
    accepts_l B ω e T t₁ t₂ t₃ n e c f := by
  obtain ⟨D, hD, hb⟩ := h
  obtain ⟨E, _, hE, he⟩ := adjoin_l B hℳ hD hc
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, j, b, hC,
      Or.inl ⟨rfl, hi, z, hz, a, ha, g, hg, hfg, hb⟩⟩))))
  exact ⟨E, hE, he⟩

/-- 槽位非法或界槽无值的退化情形保持原负规则，而非添加合法性假设。 -/
theorem negative_l (B : Formula ℒ [] context_m)
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n i j b c f : carrier_l ℳ}
    (hc : member_l ℳ c ω) (hC : PowerlessBoundedCode.code_l ω e T t₂ t₃ i j b c)
    (hf : PowerlessAmbientAssignments.finite_l ω f)
    (h : ¬PowerlessAmbientAssignments.slot_l ω f i ∨
      ∀ z, value_l f j z → ∀ a, member_l ℳ a z → ∃ g,
        PowerlessAmbientAssignments.finite_l ω g ∧ PowerlessAssignmentUpdate.update_l f i a g ∧
          accepts_l B ω e T t₁ t₂ t₃ n t₁ b g) :
    accepts_l B ω e T t₁ t₂ t₃ n t₁ c f := by
  classical
  have h₀ : ∃ D, certificate_l B ω e T t₁ t₂ t₃ n D ∧
      PowerlessTruthBounded.negative_l ω D t₁ b f i j := by
    rcases h with hi | h
    · obtain ⟨D, hD⟩ := PowerlessBasic.empty_l hℳ
      exact ⟨D, fun r hr => (hD r hr).elim, hf, Or.inl hi⟩
    · by_cases hz : ∃ z, value_l f j z
      · obtain ⟨z, hz⟩ := hz
        obtain ⟨D, hD, h₁⟩ := witnesses_l B hℳ (h z hz)
        refine ⟨D, hD, hf, Or.inr ?_⟩
        intro y hy a ha
        obtain ⟨k, A, _, hf₀⟩ := hf
        have hzy := PowerlessFunction.value_unique_l hℳ hf₀ hz hy
        exact h₁ a (hzy.symm ▸ ha)
      · obtain ⟨D, hD⟩ := PowerlessBasic.empty_l hℳ
        exact ⟨D, fun r hr => (hD r hr).elim, hf,
          Or.inr (fun z hZ => (hz ⟨z, hZ⟩).elim)⟩
  obtain ⟨D, hD, h₁⟩ := h₀
  obtain ⟨E, _, hE, he⟩ := adjoin_l B hℳ hD hc
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, j, b, hC, Or.inr ⟨rfl, h₁⟩⟩))))
  exact ⟨E, hE, he⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOracleBounded

