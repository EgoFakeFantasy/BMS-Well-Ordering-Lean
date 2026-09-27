import BMSConstructibleBridge.PowerlessTruthCertificateUnion
import BMSConstructibleBridge.PowerlessCollect

/-!
# 原检查公式的实际集合闭包

值语义逐项保留原局部规则，不以含全局求值器的可靠性谓词替代检查。
在无幂集核心模型中构造任意集合族的并与父记录添入；尚不声称这些
构造位于给定小层，也不假设小层满足完整核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthClosure

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def step_l (ω e T t₁ t₂ t₃ D p c f : carrier_l ℳ) : Prop :=
  (PowerlessBoundedCertificate.recognizes_l ω e T t₁ t₂ t₃ c ∧
    PowerlessAmbientAssignments.finite_l ω f ∧
      ((p = e ∧ PowerlessBoundedTruth.truth_l ω e T t₁ t₂ t₃ c f) ∨
        (p = t₁ ∧ ¬PowerlessBoundedTruth.truth_l ω e T t₁ t₂ t₃ c f))) ∨
  (∃ a b, PowerlessFormulaConstructor.constructor_l ω e T t₂ a b c ∧
    PowerlessAmbientAssignments.finite_l ω f ∧ PowerlessTruthNand.branch_l e t₁ D p a b f) ∨
  (p = e ∧ ∃ i b, PowerlessFormulaConstructor.constructor_l ω e T t₃ i b c ∧
    PowerlessAmbientAssignments.slot_l ω f i ∧ ∃ a,
      PowerlessTruthWitness.witness_l ω D e b f i a) ∨
  ∃ i j b, PowerlessBoundedCode.code_l ω e T t₂ t₃ i j b c ∧
    ((p = e ∧ PowerlessTruthBounded.positive_l ω D e b f i j) ∨
      (p = t₁ ∧ PowerlessTruthBounded.negative_l ω D t₁ b f i j))

theorem step_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e T t₁ t₂ t₃ D p c f : Term ℒ Γ Δ .set) :
    (PowerlessTruthStep.step_m ω e T t₁ t₂ t₃ D p c f).satisfies η ↔
      step_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (D.eval η) (p.eval η) (c.eval η) (f.eval η) := by
  simp only [PowerlessTruthStep.step_m, step_l, Formula.satisfies,
    PowerlessBoundedCertificate.recognizes_formula_l, PowerlessTruthBase.rule_m,
    PowerlessAmbientAssignments.finite_formula_l, PowerlessBoundedTruth.truth_formula_l hℳ,
    PowerlessFormulaConstructor.constructor_formula_l, PowerlessTruthNand.rule_formula_l,
    PowerlessTruthExists.rule_m, PowerlessAmbientExistential.exists_m,
    PowerlessAmbientAssignments.slot_formula_l, PowerlessTruthWitness.witness_l,
    PowerlessAssignmentUpdate.update_formula_l, PowerlessTruthRecord.entry_formula_l,
    PowerlessBoundedCode.code_formula_l, PowerlessTruthBounded.rule_m,
    PowerlessTruthBounded.positive_formula_l, PowerlessTruthBounded.negative_formula_l,
    Term.eval_weakenBound]
  rfl

def certificate_l (ω e T t₁ t₂ t₃ D : carrier_l ℳ) : Prop :=
  ∀ r, member_l ℳ r D → ∃ p c f, PowerlessTruthRecord.record_l p c f r ∧
    member_l ℳ c ω ∧ step_l ω e T t₁ t₂ t₃ D p c f

theorem certificate_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ D : Term ℒ Γ Δ .set) :
    (PowerlessTruthCertificate.certificate_m ω e T t₁ t₂ t₃ D).satisfies η ↔
      certificate_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η)
        (t₂.eval η) (t₃.eval η) (D.eval η) := by
  simp only [PowerlessTruthCertificate.certificate_m, certificate_l, Formula.satisfies,
    PowerlessTruthRecord.record_formula_l, step_formula_l hℳ,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def accepts_l (ω e T t₁ t₂ t₃ p c f : carrier_l ℳ) : Prop :=
  ∃ D, certificate_l ω e T t₁ t₂ t₃ D ∧ PowerlessTruthRecord.entry_l D p c f

theorem accepts_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ p c f : Term ℒ Γ Δ .set) :
    (PowerlessTruthCertificate.accepts_m ω e T t₁ t₂ t₃ p c f).satisfies η ↔
      accepts_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (p.eval η) (c.eval η) (f.eval η) := by
  simp only [PowerlessTruthCertificate.accepts_m, accepts_l, Formula.satisfies,
    certificate_formula_l hℳ, PowerlessTruthRecord.entry_formula_l, Term.eval_weakenBound]
  rfl

theorem monotone_l {ω e T t₁ t₂ t₃ D E p c f : carrier_l ℳ}
    (hDE : subset_l D E) (h : step_l ω e T t₁ t₂ t₃ D p c f) :
      step_l ω e T t₁ t₂ t₃ E p c f := by
  rcases h with h | ⟨a, b, hc, hf, h⟩ | ⟨hp, i, b, hc, hi, a, h⟩ | ⟨i, j, b, hc, h⟩
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨a, b, hc, hf, ?_⟩)
    rcases h with ⟨hp, ha | hb⟩ | ⟨hp, ha, hb⟩
    · exact Or.inl ⟨hp, Or.inl (PowerlessTruthRecord.monotone_l hDE ha)⟩
    · exact Or.inl ⟨hp, Or.inr (PowerlessTruthRecord.monotone_l hDE hb)⟩
    · exact Or.inr ⟨hp, PowerlessTruthRecord.monotone_l hDE ha,
        PowerlessTruthRecord.monotone_l hDE hb⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hp, i, b, hc, hi, a, PowerlessTruthMonotone.witness_l hDE h⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨i, j, b, hc, ?_⟩))
    rcases h with ⟨hp, hi, z, hz, a, ha, h⟩ | ⟨hp, hf, hi | h⟩
    · exact Or.inl ⟨hp, hi, z, hz, a, ha, PowerlessTruthMonotone.witness_l hDE h⟩
    · exact Or.inr ⟨hp, hf, Or.inl hi⟩
    · exact Or.inr ⟨hp, hf, Or.inr (fun z hz a ha =>
        PowerlessTruthMonotone.witness_l hDE (h z hz a ha))⟩

theorem union_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ A : carrier_l ℳ}
    (hA : ∀ D, member_l ℳ D A → certificate_l ω e T t₁ t₂ t₃ D) :
    ∃ E, (∀ r, member_l ℳ r E ↔ ∃ D, member_l ℳ D A ∧ member_l ℳ r D) ∧
      certificate_l ω e T t₁ t₂ t₃ E := by
  obtain ⟨E, hE⟩ := PowerlessBasic.union_l hℳ A
  refine ⟨E, hE, ?_⟩
  intro r hr
  obtain ⟨D, hD, hr⟩ := (hE r).mp hr
  obtain ⟨p, c, f, h₁, h₂, h₃⟩ := hA D hD r hr
  exact ⟨p, c, f, h₁, h₂, monotone_l (fun r hr => (hE r).mpr ⟨D, hD, hr⟩) h₃⟩

theorem adjoin_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ D p c f : carrier_l ℳ}
    (hD : certificate_l ω e T t₁ t₂ t₃ D) (hc : member_l ℳ c ω)
    (h : step_l ω e T t₁ t₂ t₃ D p c f) :
    ∃ E, subset_l D E ∧ certificate_l ω e T t₁ t₂ t₃ E ∧
      PowerlessTruthRecord.entry_l E p c f := by
  obtain ⟨s, hs⟩ := PowerlessBasic.ordered_exists_l hℳ c f
  obtain ⟨E, hE⟩ := PowerlessAppendGraph.exists_l hℳ D p s
  have hDE : subset_l D E := fun r hr => (hE r).mpr (Or.inl hr)
  refine ⟨E, hDE, ?_, ?_⟩
  · intro r hr
    rcases (hE r).mp hr with hr | hr
    · obtain ⟨q, b, g, h₁, h₂, h₃⟩ := hD r hr
      exact ⟨q, b, g, h₁, h₂, monotone_l hDE h₃⟩
    · exact ⟨p, c, f, ⟨s, hs, hr⟩, hc, monotone_l hDE h⟩
  · obtain ⟨r, hr⟩ := PowerlessBasic.ordered_exists_l hℳ p s
    exact ⟨r, (hE r).mpr (Or.inr hr), s, hs, hr⟩

/-- 原有界识别与有符号有界真值给出实际初始接受证书。 -/
theorem base_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ p c f : carrier_l ℳ} (hc : member_l ℳ c ω)
    (hB : PowerlessBoundedCertificate.recognizes_l ω e T t₁ t₂ t₃ c)
    (hf : PowerlessAmbientAssignments.finite_l ω f)
    (h : (p = e ∧ PowerlessBoundedTruth.truth_l ω e T t₁ t₂ t₃ c f) ∨
      (p = t₁ ∧ ¬PowerlessBoundedTruth.truth_l ω e T t₁ t₂ t₃ c f)) :
    accepts_l ω e T t₁ t₂ t₃ p c f := by
  obtain ⟨D, hD⟩ := PowerlessBasic.empty_l hℳ
  obtain ⟨E, _, hE, hr⟩ := adjoin_l hℳ (D := D)
    (fun r hr => (hD r hr).elim) hc (Or.inl ⟨hB, hf, h⟩)
  exact ⟨E, hE, hr⟩

/-- 对指定记录集合收集真实检查证书，再合为一个覆盖全部记录的证书。 -/
theorem collect_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ A : carrier_l ℳ}
    (h : ∀ r, member_l ℳ r A → ∃ D, certificate_l ω e T t₁ t₂ t₃ D ∧ member_l ℳ r D) :
    ∃ E, certificate_l ω e T t₁ t₂ t₃ E ∧ subset_l A E := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 6 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T
        (Fin.cases t₁ (Fin.cases t₂ (fun _ => t₃))))), free := fun _ => ω }
  let ψ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
    PowerlessTruthCertificate.certificate_m (.fvar (.there .here))
      (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here))))))) (.fvar .here)
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    .conj (PowerlessTruthCertificate.certificate_m
      (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.fvar .here))
      (SecondOrderObjectSyntax.member_m (.fvar (.there .here)) (.fvar .here))
  have hψ : ∀ D, ψ.satisfies ((PowerlessComprehension.env_l η).pushFree D) ↔
      certificate_l ω e T t₁ t₂ t₃ D := by
    intro D
    exact certificate_formula_l hℳ _ _ _ _ _ _ _ _
  have hφ : ∀ r D, φ.satisfies (((PowerlessComprehension.env_l η).pushFree r).pushFree D) ↔
      certificate_l ω e T t₁ t₂ t₃ D ∧ member_l ℳ r D := by
    intro r D
    simp only [φ, Formula.satisfies, certificate_formula_l hℳ,
      SecondOrderObjectSyntax.member_m, Arguments.eval]
    rfl
  obtain ⟨B, hB⟩ := PowerlessCollect.exists_l hℳ φ η A (fun r hr => by
    obtain ⟨D, hD⟩ := h r hr
    exact ⟨D, (hφ r D).mpr hD⟩)
  obtain ⟨C, hC⟩ := PowerlessComprehension.separation_l hℳ ψ η B
  obtain ⟨E, hE, h₀⟩ := union_l hℳ (A := C)
    (fun D hD => (hψ D).mp ((hC D).mp hD).2)
  refine ⟨E, h₀, ?_⟩
  intro r hr
  obtain ⟨D, hD, h₁⟩ := hB r hr
  obtain ⟨h₂, h₃⟩ := (hφ r D).mp h₁
  exact (hE r).mpr ⟨D, (hC D).mpr ⟨hD, (hψ D).mpr h₂⟩, h₃⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthClosure
