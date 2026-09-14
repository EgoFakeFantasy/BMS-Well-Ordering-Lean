import BMSConstructibleBridge.PowerlessTruthStep

/-!
# 局部真值规则对候选记录集的单调性

只扩大可读取的记录，保留原代码、实际赋值及全部量词 guard。
本结论对任意结构成立，不要求整个候选集可靠或小层满足完整核心。
这不意味着任意加入的新记录都已经满足证书条件。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthMonotone

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem witness_l {ω D E p b f i a : carrier_l ℳ} (hDE : subset_l D E)
    (h : PowerlessTruthWitness.witness_l ω D p b f i a) :
    PowerlessTruthWitness.witness_l ω E p b f i a := by
  obtain ⟨g, hg, hu, he⟩ := h
  exact ⟨g, hg, hu, PowerlessTruthRecord.monotone_l hDE he⟩

theorem nand_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e t D E p a b f : Term ℒ Γ Δ .set) (hDE : subset_l (D.eval η) (E.eval η))
    (h : (PowerlessTruthNand.rule_m ω e t D p a b f).satisfies η) :
    (PowerlessTruthNand.rule_m ω e t E p a b f).satisfies η := by
  obtain ⟨hf, h⟩ := (PowerlessTruthNand.rule_formula_l η ω e t D p a b f).mp h
  apply (PowerlessTruthNand.rule_formula_l η ω e t E p a b f).mpr
  refine ⟨hf, ?_⟩
  rcases h with ⟨hp, ha | hb⟩ | ⟨hp, ha, hb⟩
  · exact Or.inl ⟨hp, Or.inl (PowerlessTruthRecord.monotone_l hDE ha)⟩
  · exact Or.inl ⟨hp, Or.inr (PowerlessTruthRecord.monotone_l hDE hb)⟩
  · exact Or.inr ⟨hp, PowerlessTruthRecord.monotone_l hDE ha, PowerlessTruthRecord.monotone_l hDE hb⟩

theorem bounded_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e t D E p b f i j : Term ℒ Γ Δ .set) (hDE : subset_l (D.eval η) (E.eval η))
    (h : (PowerlessTruthBounded.rule_m ω e t D p b f i j).satisfies η) :
    (PowerlessTruthBounded.rule_m ω e t E p b f i j).satisfies η := by
  change
    (p.eval η = e.eval η ∧ (PowerlessTruthBounded.positive_m ω D e b f i j).satisfies η) ∨
    (p.eval η = t.eval η ∧ (PowerlessTruthBounded.negative_m ω D t b f i j).satisfies η) at h
  change
    (p.eval η = e.eval η ∧ (PowerlessTruthBounded.positive_m ω E e b f i j).satisfies η) ∨
    (p.eval η = t.eval η ∧ (PowerlessTruthBounded.negative_m ω E t b f i j).satisfies η)
  rcases h with ⟨hp, h⟩ | ⟨hp, h⟩
  · obtain ⟨hf, z, hz, a, ha, hg⟩ := (PowerlessTruthBounded.positive_formula_l η ω D e b f i j).mp h
    exact Or.inl ⟨hp, (PowerlessTruthBounded.positive_formula_l η ω E e b f i j).mpr
      ⟨hf, z, hz, a, ha, witness_l hDE hg⟩⟩
  · obtain ⟨hf, h⟩ := (PowerlessTruthBounded.negative_formula_l η ω D t b f i j).mp h
    apply Or.inr
    refine ⟨hp, (PowerlessTruthBounded.negative_formula_l η ω E t b f i j).mpr ⟨hf, ?_⟩⟩
    exact h.imp id (fun h z hz a ha => witness_l hDE (h z hz a ha))

theorem exists_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e D E f i b : Term ℒ Γ Δ .set) (hDE : subset_l (D.eval η) (E.eval η))
    (h : (PowerlessTruthExists.rule_m ω e D f i b).satisfies η) :
    (PowerlessTruthExists.rule_m ω e E f i b).satisfies η := by
  let q (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  change (PowerlessAmbientAssignments.slot_m ω f i).satisfies η ∧
    ∃ a g : carrier_l ℳ,
      (PowerlessAmbientAssignments.finite_m (q ω) (.bvar .here)).satisfies ((η.pushBound a).pushBound g) ∧
      (PowerlessAssignmentUpdate.update_m (q f) (q i) (.bvar (.there .here)) (.bvar .here)).satisfies
        ((η.pushBound a).pushBound g) ∧
      (PowerlessTruthRecord.entry_m (q D) (q e) (q b) (.bvar .here)).satisfies
        ((η.pushBound a).pushBound g) at h
  change (PowerlessAmbientAssignments.slot_m ω f i).satisfies η ∧
    ∃ a g : carrier_l ℳ,
      (PowerlessAmbientAssignments.finite_m (q ω) (.bvar .here)).satisfies ((η.pushBound a).pushBound g) ∧
      (PowerlessAssignmentUpdate.update_m (q f) (q i) (.bvar (.there .here)) (.bvar .here)).satisfies
        ((η.pushBound a).pushBound g) ∧
      (PowerlessTruthRecord.entry_m (q E) (q e) (q b) (.bvar .here)).satisfies
        ((η.pushBound a).pushBound g)
  obtain ⟨hf, a, g, hg, hu, he⟩ := h
  refine ⟨hf, a, g, hg, hu, ?_⟩
  rw [PowerlessTruthRecord.entry_formula_l] at he ⊢
  simp only [q, Term.eval_weakenBound] at he ⊢
  exact PowerlessTruthRecord.monotone_l hDE he

theorem step_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (w z V s₁ s₂ s₃ D E p c f : Term ℒ Γ Δ .set)
    (hDE : subset_l (D.eval η) (E.eval η))
    (h : (PowerlessTruthStep.step_m w z V s₁ s₂ s₃ D p c f).satisfies η) :
    (PowerlessTruthStep.step_m w z V s₁ s₂ s₃ E p c f).satisfies η := by
  let q (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let r (s : Term ℒ Γ Δ .set) := (q s).weakenBound SetTheory.SetSort.set
  change
    ((PowerlessBoundedCertificate.recognizes_m w z V s₁ s₂ s₃ c).satisfies η ∧
      (PowerlessTruthBase.rule_m w z V s₁ s₂ s₃ p c f).satisfies η) ∨
    (∃ a b : carrier_l ℳ,
      (PowerlessFormulaConstructor.constructor_m (q w) (q z) (q V) (q s₂)
        (.bvar (.there .here)) (.bvar .here) (q c)).satisfies ((η.pushBound a).pushBound b) ∧
      (PowerlessTruthNand.rule_m (q w) (q z) (q s₁) (q D) (q p)
        (.bvar (.there .here)) (.bvar .here) (q f)).satisfies ((η.pushBound a).pushBound b)) ∨
    (p.eval η = z.eval η ∧ ∃ i b : carrier_l ℳ,
      (PowerlessFormulaConstructor.constructor_m (q w) (q z) (q V) (q s₃)
        (.bvar (.there .here)) (.bvar .here) (q c)).satisfies ((η.pushBound i).pushBound b) ∧
      (PowerlessTruthExists.rule_m (q w) (q z) (q D) (q f)
        (.bvar (.there .here)) (.bvar .here)).satisfies ((η.pushBound i).pushBound b)) ∨
    (∃ i j b : carrier_l ℳ,
      (PowerlessBoundedCode.code_m (r w) (r z) (r V) (r s₂) (r s₃)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here) (r c)).satisfies
          (((η.pushBound i).pushBound j).pushBound b) ∧
      (PowerlessTruthBounded.rule_m (r w) (r z) (r s₁) (r D) (r p)
        (.bvar .here) (r f) (.bvar (.there (.there .here))) (.bvar (.there .here))).satisfies
          (((η.pushBound i).pushBound j).pushBound b)) at h
  change
    ((PowerlessBoundedCertificate.recognizes_m w z V s₁ s₂ s₃ c).satisfies η ∧
      (PowerlessTruthBase.rule_m w z V s₁ s₂ s₃ p c f).satisfies η) ∨
    (∃ a b : carrier_l ℳ,
      (PowerlessFormulaConstructor.constructor_m (q w) (q z) (q V) (q s₂)
        (.bvar (.there .here)) (.bvar .here) (q c)).satisfies ((η.pushBound a).pushBound b) ∧
      (PowerlessTruthNand.rule_m (q w) (q z) (q s₁) (q E) (q p)
        (.bvar (.there .here)) (.bvar .here) (q f)).satisfies ((η.pushBound a).pushBound b)) ∨
    (p.eval η = z.eval η ∧ ∃ i b : carrier_l ℳ,
      (PowerlessFormulaConstructor.constructor_m (q w) (q z) (q V) (q s₃)
        (.bvar (.there .here)) (.bvar .here) (q c)).satisfies ((η.pushBound i).pushBound b) ∧
      (PowerlessTruthExists.rule_m (q w) (q z) (q E) (q f)
        (.bvar (.there .here)) (.bvar .here)).satisfies ((η.pushBound i).pushBound b)) ∨
    (∃ i j b : carrier_l ℳ,
      (PowerlessBoundedCode.code_m (r w) (r z) (r V) (r s₂) (r s₃)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here) (r c)).satisfies
          (((η.pushBound i).pushBound j).pushBound b) ∧
      (PowerlessTruthBounded.rule_m (r w) (r z) (r s₁) (r E) (r p)
        (.bvar .here) (r f) (.bvar (.there (.there .here))) (.bvar (.there .here))).satisfies
          (((η.pushBound i).pushBound j).pushBound b))
  rcases h with ⟨hc, hf⟩ | ⟨a, b, hc, hf⟩ | ⟨hp, i, b, hc, hf⟩ | ⟨i, j, b, hc, hf⟩
  · exact Or.inl ⟨hc, hf⟩
  · refine Or.inr (Or.inl ⟨a, b, hc, ?_⟩)
    exact nand_l ((η.pushBound a).pushBound b) (q w) (q z) (q s₁) (q D) (q E) (q p)
      (.bvar (.there .here)) (.bvar .here) (q f)
      (by simpa only [q, Term.eval_weakenBound] using hDE) hf
  · refine Or.inr (Or.inr (Or.inl ⟨hp, i, b, hc, ?_⟩))
    exact exists_l ((η.pushBound i).pushBound b) (q w) (q z) (q D) (q E) (q f)
      (.bvar (.there .here)) (.bvar .here)
      (by simpa only [q, Term.eval_weakenBound] using hDE) hf
  · refine Or.inr (Or.inr (Or.inr ⟨i, j, b, hc, ?_⟩))
    exact bounded_l (((η.pushBound i).pushBound j).pushBound b)
      (r w) (r z) (r s₁) (r D) (r E) (r p) (.bvar .here) (r f)
      (.bvar (.there (.there .here))) (.bvar (.there .here))
      (by simpa only [r, q, Term.eval_weakenBound] using hDE) hf

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthMonotone
