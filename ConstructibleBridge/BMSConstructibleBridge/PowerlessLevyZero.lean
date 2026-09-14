import BMSConstructibleBridge.PowerlessLevyCertificateClosure
import BMSConstructibleBridge.PowerlessOrdinalInduction
import BMSConstructibleBridge.PowerlessOmegaOrdinal

/-!
# 内部第零层恰好是有界识别类

沿实际公式码作纯公式内部归纳。零层子判断仍在零层，无界存在分支
被 0∉0 排除；因此非标准有限证书也不能通过循环得到伪零层公式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyZero

open Logic FirstOrder ThirdOrderSemantics PowerlessLevyEntry PowerlessLevyCertificate

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def zero_l (ω e T t₁ t₂ t₃ D c : carrier_l ℳ) : Prop :=
  ∀ p, entry_l ω e T D c e p → PowerlessBoundedCertificate.recognizes_l ω e T t₁ t₂ t₃ c

def zero_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ D c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .forallE .set (.imp (entry_m (w ω) (w e) (w T) (w D) (w c) (w e) (.bvar .here))
    (PowerlessBoundedCertificate.recognizes_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w c)))

theorem zero_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ D c : Term ℒ Γ Δ .set) :
    (zero_m ω e T t₁ t₂ t₃ D c).satisfies η ↔
      zero_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (D.eval η) (c.eval η) := by
  simp only [zero_m, zero_l, Formula.satisfies, entry_formula_l,
    PowerlessBoundedCertificate.recognizes_formula_l, Term.eval_weakenBound]
  rfl

theorem sound_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ D : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hD : certificate_l ω e T t₁ t₂ t₃ D) :
    ∀ c, member_l ℳ c ω → zero_l ω e T t₁ t₂ t₃ D c := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 7 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁
        (Fin.cases t₂ (Fin.cases t₃ (fun _ => D)))))), free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    zero_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.fvar .here)
  have h : ∀ c, φ.satisfies ((PowerlessComprehension.env_l η).pushFree c) ↔ zero_l ω e T t₁ t₂ t₃ D c := by
    intro c
    rw [zero_formula_l]
    rfl
  have hE : ∀ m, subset_l m e → m = e := fun m hm =>
    (PowerlessTheory.ext_l hℳ).eq_of_same_members m e (fun x => ⟨hm x, fun hx => (he x hx).elim⟩)
  have h₀ := PowerlessOrdinalInduction.induction_l hℳ φ η (PowerlessOmegaOrdinal.ordinal_l hℳ hω)
    (fun c _ h₁ => (h c).mpr (by
      intro p hp
      rcases (hD.2 c e p hp).2 with hc | ⟨a, b, k, l, q, _, hk, hl, ha, hb, hc⟩ |
        ⟨i, j, b, m, hm, hb, hc⟩ | ⟨_, hn, _⟩ | ⟨m, _, hm, _⟩
      · exact hc
      · have hk₀ := hE k hk
        have hl₀ := hE l hl
        subst k
        subst l
        obtain ⟨ha₀, hb₀⟩ := PowerlessFormulaConstructor.bounds_l hℳ hω he hT hc
        exact PowerlessBoundedCertificateClosure.nand_l hℳ hω he hT
          ((h a).mp (h₁ a ha₀) q ha) ((h b).mp (h₁ b hb₀) q hb) hc
      · have hm₀ := hE m hm
        subst m
        exact PowerlessBoundedCertificateClosure.bounded_l hℳ hω he hT
          ((h b).mp (h₁ b (PowerlessBoundedCode.bounds_l hℳ hω he hT hc).2.2) p hb) hc
      · exact (he e hn).elim
      · exact (he m hm).elim))
  exact fun c hc => (h c).mp (h₀ c hc)

theorem class_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c p : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (h : PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c e p) :
    PowerlessBoundedCertificate.recognizes_l ω e T t₁ t₂ t₃ c := by
  obtain ⟨D, hD, hc⟩ := h
  exact sound_l hℳ hω he hT hD c (PowerlessLevyEntry.natural_l hc).1 p hc

theorem exact_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c p : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hp : member_l ℳ p ω) (hP : polarity_l e t₁ p) :
    PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c e p ↔
      PowerlessBoundedCertificate.recognizes_l ω e T t₁ t₂ t₃ c := by
  exact ⟨class_l hℳ hω he hT, PowerlessLevyCertificateClosure.base_l hℳ hω he hT
    (PowerlessNatural.zero_mem_l hℳ hω he) hp hP⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyZero
