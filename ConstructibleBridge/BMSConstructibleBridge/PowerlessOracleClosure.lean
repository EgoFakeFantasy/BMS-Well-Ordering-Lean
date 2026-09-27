import BMSConstructibleBridge.PowerlessTruthOracle
import BMSConstructibleBridge.PowerlessTruthClosure

/-!
# 低层公式证书的实际集合构造

调用条件仍是固定原公式。并与添入只使用局部规则单调性，
不假定调用条件可靠；可靠性另由 PowerlessTruthOracle.sound_l 提供。
这里的集合存在使用完整无幂集核心，尚未迁移到指定小层。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOracleClosure

open Logic FirstOrder ThirdOrderSemantics PowerlessTruthOracle

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def step_l (B : Formula ℒ [] context_m) (ω e T t₁ t₂ t₃ n D p c f : carrier_l ℳ) : Prop :=
  B.satisfies (env_l ω e T t₁ t₂ t₃ n p c f) ∨
    PowerlessTruthClosure.step_l ω e T t₁ t₂ t₃ D p c f

def certificate_l (B : Formula ℒ [] context_m) (ω e T t₁ t₂ t₃ n D : carrier_l ℳ) : Prop :=
  ∀ r, member_l ℳ r D → ∃ p c f, PowerlessTruthRecord.record_l p c f r ∧
    member_l ℳ c ω ∧ step_l B ω e T t₁ t₂ t₃ n D p c f

theorem certificate_formula_l (B : Formula ℒ [] context_m)
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ n D : Term ℒ Γ Δ .set) :
    (PowerlessTruthOracle.certificate_m B ω e T t₁ t₂ t₃ n D).satisfies η ↔
      certificate_l B (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η)
        (t₂.eval η) (t₃.eval η) (n.eval η) (D.eval η) := by
  simp only [PowerlessTruthOracle.certificate_m, certificate_l, step_l, Formula.satisfies,
    PowerlessTruthRecord.record_formula_l, PowerlessTruthClosure.step_formula_l hℳ,
    instance_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def accepts_l (B : Formula ℒ [] context_m) (ω e T t₁ t₂ t₃ n p c f : carrier_l ℳ) : Prop :=
  ∃ D, certificate_l B ω e T t₁ t₂ t₃ n D ∧ PowerlessTruthRecord.entry_l D p c f

theorem accepts_formula_l (B : Formula ℒ [] context_m)
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ n p c f : Term ℒ Γ Δ .set) :
    (PowerlessTruthOracle.accepts_m B ω e T t₁ t₂ t₃ n p c f).satisfies η ↔
      accepts_l B (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (n.eval η) (p.eval η) (c.eval η) (f.eval η) := by
  simp only [PowerlessTruthOracle.accepts_m, accepts_l, Formula.satisfies,
    certificate_formula_l B hℳ, PowerlessTruthRecord.entry_formula_l, Term.eval_weakenBound]
  rfl

theorem monotone_l (B : Formula ℒ [] context_m) {ω e T t₁ t₂ t₃ n D E p c f : carrier_l ℳ}
    (hDE : subset_l D E) (h : step_l B ω e T t₁ t₂ t₃ n D p c f) :
    step_l B ω e T t₁ t₂ t₃ n E p c f :=
  h.imp id (PowerlessTruthClosure.monotone_l hDE)

theorem union_l (B : Formula ℒ [] context_m) (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n A : carrier_l ℳ}
    (hA : ∀ D, member_l ℳ D A → certificate_l B ω e T t₁ t₂ t₃ n D) :
    ∃ E, (∀ r, member_l ℳ r E ↔ ∃ D, member_l ℳ D A ∧ member_l ℳ r D) ∧
      certificate_l B ω e T t₁ t₂ t₃ n E := by
  obtain ⟨E, hE⟩ := PowerlessBasic.union_l hℳ A
  refine ⟨E, hE, ?_⟩
  intro r hr
  obtain ⟨D, hD, hr⟩ := (hE r).mp hr
  obtain ⟨p, c, f, h₁, h₂, h₃⟩ := hA D hD r hr
  exact ⟨p, c, f, h₁, h₂, monotone_l B (fun r hr => (hE r).mpr ⟨D, hD, hr⟩) h₃⟩

theorem adjoin_l (B : Formula ℒ [] context_m) (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n D p c f : carrier_l ℳ}
    (hD : certificate_l B ω e T t₁ t₂ t₃ n D) (hc : member_l ℳ c ω)
    (h : step_l B ω e T t₁ t₂ t₃ n D p c f) :
    ∃ E, subset_l D E ∧ certificate_l B ω e T t₁ t₂ t₃ n E ∧
      PowerlessTruthRecord.entry_l E p c f := by
  obtain ⟨s, hs⟩ := PowerlessBasic.ordered_exists_l hℳ c f
  obtain ⟨E, hE⟩ := PowerlessAppendGraph.exists_l hℳ D p s
  have hDE : subset_l D E := fun r hr => (hE r).mpr (Or.inl hr)
  refine ⟨E, hDE, ?_, ?_⟩
  · intro r hr
    rcases (hE r).mp hr with hr | hr
    · obtain ⟨q, b, g, h₁, h₂, h₃⟩ := hD r hr
      exact ⟨q, b, g, h₁, h₂, monotone_l B hDE h₃⟩
    · exact ⟨p, c, f, ⟨s, hs, hr⟩, hc, monotone_l B hDE h⟩
  · obtain ⟨r, hr⟩ := PowerlessBasic.ordered_exists_l hℳ p s
    exact ⟨r, (hE r).mpr (Or.inr hr), s, hs, hr⟩

/-- 低层原公式成立即可构造单记录证书，不把该调用的可靠性当作集合存在前提。 -/
theorem base_l (B : Formula ℒ [] context_m)
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n p c f : carrier_l ℳ} (hc : member_l ℳ c ω)
    (h : B.satisfies (env_l ω e T t₁ t₂ t₃ n p c f)) :
    accepts_l B ω e T t₁ t₂ t₃ n p c f := by
  obtain ⟨D, hD⟩ := PowerlessBasic.empty_l hℳ
  obtain ⟨E, _, hE, hr⟩ := adjoin_l B hℳ (D := D)
    (fun r hr => (hD r hr).elim) hc (Or.inl h)
  exact ⟨E, hE, hr⟩

/-- 收集公式包含 B 的实际替换，不包含外部真值谓词。 -/
theorem collect_l (B : Formula ℒ [] context_m)
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n A : carrier_l ℳ}
    (h : ∀ r, member_l ℳ r A →
      ∃ D, certificate_l B ω e T t₁ t₂ t₃ n D ∧ member_l ℳ r D) :
    ∃ E, certificate_l B ω e T t₁ t₂ t₃ n E ∧ subset_l A E := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 7 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T
        (Fin.cases t₁ (Fin.cases t₂ (Fin.cases t₃ (fun _ => n)))))), free := fun _ => ω }
  let ψ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    PowerlessTruthOracle.certificate_m B (.fvar (.there .here))
      (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.fvar .here)
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    .conj (PowerlessTruthOracle.certificate_m B (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.fvar .here))
      (SecondOrderObjectSyntax.member_m (.fvar (.there .here)) (.fvar .here))
  have hψ : ∀ D, ψ.satisfies ((PowerlessComprehension.env_l η).pushFree D) ↔
      certificate_l B ω e T t₁ t₂ t₃ n D := by
    intro D
    exact certificate_formula_l B hℳ _ _ _ _ _ _ _ _ _
  have hφ : ∀ r D, φ.satisfies (((PowerlessComprehension.env_l η).pushFree r).pushFree D) ↔
      certificate_l B ω e T t₁ t₂ t₃ n D ∧ member_l ℳ r D := by
    intro r D
    simp only [φ, Formula.satisfies, certificate_formula_l B hℳ,
      SecondOrderObjectSyntax.member_m, Arguments.eval]
    rfl
  obtain ⟨K, hK⟩ := PowerlessCollect.exists_l hℳ φ η A (fun r hr => by
    obtain ⟨D, hD⟩ := h r hr
    exact ⟨D, (hφ r D).mpr hD⟩)
  obtain ⟨C, hC⟩ := PowerlessComprehension.separation_l hℳ ψ η K
  obtain ⟨E, hE, h₀⟩ := union_l B hℳ (A := C)
    (fun D hD => (hψ D).mp ((hC D).mp hD).2)
  refine ⟨E, h₀, ?_⟩
  intro r hr
  obtain ⟨D, hD, h₁⟩ := hK r hr
  obtain ⟨h₂, h₃⟩ := (hφ r D).mp h₁
  exact (hE r).mpr ⟨D, (hC D).mpr ⟨hD, (hψ D).mpr h₂⟩, h₃⟩

theorem merge_l (B : Formula ℒ [] context_m)
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n D E : carrier_l ℳ}
    (hD : certificate_l B ω e T t₁ t₂ t₃ n D)
    (hE : certificate_l B ω e T t₁ t₂ t₃ n E) :
    ∃ K, certificate_l B ω e T t₁ t₂ t₃ n K ∧ subset_l D K ∧ subset_l E K := by
  obtain ⟨A, hA⟩ := PowerlessBasic.pairing_l hℳ D E
  obtain ⟨K, hK, h₀⟩ := union_l B hℳ (A := A) (fun F hF => by
    rcases (hA F).mp hF with rfl | rfl
    · exact hD
    · exact hE)
  exact ⟨K, h₀, fun r hr => (hK r).mpr ⟨D, (hA D).mpr (Or.inl rfl), hr⟩,
    fun r hr => (hK r).mpr ⟨E, (hA E).mpr (Or.inr rfl), hr⟩⟩

/-- 同层与非规则的接受闭包；两条正子记录先合并为一个实际证书。 -/
theorem nand_l (B : Formula ℒ [] context_m)
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n p a b c f : carrier_l ℳ}
    (hc : member_l ℳ c ω)
    (hC : PowerlessFormulaConstructor.constructor_l ω e T t₂ a b c)
    (hf : PowerlessAmbientAssignments.finite_l ω f)
    (h : (p = e ∧ (accepts_l B ω e T t₁ t₂ t₃ n t₁ a f ∨
        accepts_l B ω e T t₁ t₂ t₃ n t₁ b f)) ∨
      (p = t₁ ∧ accepts_l B ω e T t₁ t₂ t₃ n e a f ∧
        accepts_l B ω e T t₁ t₂ t₃ n e b f)) :
    accepts_l B ω e T t₁ t₂ t₃ n p c f := by
  rcases h with ⟨rfl, h | h⟩ | ⟨rfl, ha, hb⟩
  · obtain ⟨D, hD, ha⟩ := h
    obtain ⟨E, _, hE, he⟩ := adjoin_l B hℳ hD hc
      (Or.inr (Or.inr (Or.inl ⟨a, b, hC, hf, Or.inl ⟨rfl, Or.inl ha⟩⟩)))
    exact ⟨E, hE, he⟩
  · obtain ⟨D, hD, hb⟩ := h
    obtain ⟨E, _, hE, he⟩ := adjoin_l B hℳ hD hc
      (Or.inr (Or.inr (Or.inl ⟨a, b, hC, hf, Or.inl ⟨rfl, Or.inr hb⟩⟩)))
    exact ⟨E, hE, he⟩
  · obtain ⟨D, hD, ha⟩ := ha
    obtain ⟨E, hE, hb⟩ := hb
    obtain ⟨K, hK, hDK, hEK⟩ := merge_l B hℳ hD hE
    obtain ⟨F, _, hF, he⟩ := adjoin_l B hℳ hK hc
      (Or.inr (Or.inr (Or.inl ⟨a, b, hC, hf, Or.inr ⟨rfl,
        PowerlessTruthRecord.monotone_l hDK ha, PowerlessTruthRecord.monotone_l hEK hb⟩⟩)))
    exact ⟨F, hF, he⟩

theorem exists_l (B : Formula ℒ [] context_m)
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n i b c f a g : carrier_l ℳ}
    (hc : member_l ℳ c ω)
    (hC : PowerlessFormulaConstructor.constructor_l ω e T t₃ i b c)
    (hi : PowerlessAmbientAssignments.slot_l ω f i)
    (hg : PowerlessAmbientAssignments.finite_l ω g)
    (hfg : PowerlessAssignmentUpdate.update_l f i a g)
    (h : accepts_l B ω e T t₁ t₂ t₃ n e b g) :
    accepts_l B ω e T t₁ t₂ t₃ n e c f := by
  obtain ⟨D, hD, hb⟩ := h
  obtain ⟨E, _, hE, he⟩ := adjoin_l B hℳ hD hc
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, i, b, hC, hi, a, g, hg, hfg, hb⟩))))
  exact ⟨E, hE, he⟩


/-- 按任意原公式收集证书族，并保留各输入对应的证书子集。 -/
theorem family_l (B : Formula ℒ [] context_m)
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    {ω e T t₁ t₂ t₃ n A : carrier_l ℳ}
    (h : ∀ x, member_l ℳ x A →
      ∃ D, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree D))
    (hφ : ∀ x D, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree D) →
      certificate_l B ω e T t₁ t₂ t₃ n D) :
    ∃ E, certificate_l B ω e T t₁ t₂ t₃ n E ∧
      ∀ x, member_l ℳ x A → ∃ D, subset_l D E ∧
        φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree D) := by
  let θ : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 7 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T
        (Fin.cases t₁ (Fin.cases t₂ (Fin.cases t₃ (fun _ => n)))))), free := fun _ => ω }
  let ψ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    PowerlessTruthOracle.certificate_m B (.fvar (.there .here))
      (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.fvar .here)
  have hψ : ∀ D, ψ.satisfies ((PowerlessComprehension.env_l θ).pushFree D) ↔
      certificate_l B ω e T t₁ t₂ t₃ n D := by
    intro D
    exact certificate_formula_l B hℳ _ _ _ _ _ _ _ _ _
  obtain ⟨K, hK⟩ := PowerlessCollect.exists_l hℳ φ η A h
  obtain ⟨C, hC⟩ := PowerlessComprehension.separation_l hℳ ψ θ K
  obtain ⟨E, hE, h₀⟩ := union_l B hℳ (A := C)
    (fun D hD => (hψ D).mp ((hC D).mp hD).2)
  refine ⟨E, h₀, ?_⟩
  intro x hx
  obtain ⟨D, hD, h₁⟩ := hK x hx
  exact ⟨D, fun r hr => (hE r).mpr
    ⟨D, (hC D).mpr ⟨hD, (hψ D).mpr (hφ x D h₁)⟩, hr⟩, h₁⟩


/-- 原检查证书无需改变其记录集合，就能进入允许低层调用的检查器。 -/
theorem original_l (B : Formula ℒ [] context_m)
    {ω e T t₁ t₂ t₃ n p c f : carrier_l ℳ}
    (h : PowerlessTruthClosure.accepts_l ω e T t₁ t₂ t₃ p c f) :
    accepts_l B ω e T t₁ t₂ t₃ n p c f := by
  obtain ⟨D, hD, he⟩ := h
  refine ⟨D, ?_, he⟩
  intro r hr
  obtain ⟨q, b, g, h₀, h₁, h₂⟩ := hD r hr
  exact ⟨q, b, g, h₀, h₁, Or.inr h₂⟩


end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOracleClosure
