import BMSConstructibleBridge.PowerlessLevyAgreement
import BMSConstructibleBridge.PowerlessLevyLocalAgreement

/-!
# 由实际低层一致性推出内部证书的极性保持

一般结论显式消费较低层查询一致性，沿实际公式码作原纯公式内部归纳。
同码升层分支由低层前提处理，不偷换成外部有限树或假定全初等性。
第一层实例的低层前提由已证零层绝对性给出。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevySound

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationDirection
open PowerlessLevyEntry (entry_l entry_m entry_formula_l)
open PowerlessLevyCertificate (certificate_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def property_l (ω e T t₁ A F G D N c : carrier_l ℳ) : Prop :=
  ∀ n p, subset_l n N → entry_l ω e T D c n p → polarity_l ω A F G e t₁ p c

def property_m {Γ Δ : SortContext ℒ} (ω e T t₁ A F G D N c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set (.forallE .set (.imp (ThirdOrderTheory.subset_m (.bvar (.there .here)) (w N))
    (.imp (entry_m (w ω) (w e) (w T) (w D) (w c) (.bvar (.there .here)) (.bvar .here))
      (polarity_m (w ω) (w A) (w F) (w G) (w e) (w t₁) (.bvar .here) (w c)))))

theorem property_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e T t₁ A F G D N c : Term ℒ Γ Δ .set) :
    (property_m ω e T t₁ A F G D N c).satisfies η ↔
      property_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η)
        (A.eval η) (F.eval η) (G.eval η) (D.eval η) (N.eval η) (c.eval η) := by
  simp only [property_m, property_l, Formula.satisfies, subset_formula_l,
    entry_formula_l, polarity_formula_l, Term.eval_weakenBound]
  rfl

variable (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ A U S R F G : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hAU : subset_l A U) (hA : PowerlessNaturalOrder.transitive_l A)
  (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m U)
  (hR : ∀ f, member_l ℳ f R ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A)
  (hF : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F)
  (hG : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ R G)

include hℳ hω ht hT hAU hA hS hR hF hG

theorem sound_l {D N : carrier_l ℳ} (hD : certificate_l ω e T t₁ t₂ t₃ D)
    (hL : PowerlessLevyAgreement.lower_l ω e T t₁ t₂ t₃ A F G N) :
    ∀ c, member_l ℳ c ω → property_l ω e T t₁ A F G D N c := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 9 :=
    { bound := (Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁ (Fin.cases A (Fin.cases F (Fin.cases G (Fin.cases D (fun _ => N))))))))), free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    property_m (.fvar (.there .here))
      (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
      (.fvar .here)
  have h : ∀ c, φ.satisfies ((PowerlessComprehension.env_l η).pushFree c) ↔
      property_l ω e T t₁ A F G D N c := by
    intro c
    rw [property_formula_l]
    rfl
  have h₀ := PowerlessOrdinalInduction.induction_l hℳ φ η (PowerlessOmegaOrdinal.ordinal_l hℳ hω)
    (fun c _ h₁ => (h c).mpr (by
      intro n p hn hc
      rcases (hD.2 c n p hc).2 with hC | ⟨a, b, k, l, q, hp, hk, hl, ha, hb, hC⟩ |
        ⟨i, j, b, m, hm, hb, hC⟩ | ⟨hp, _, i, b, m, q, hb, hm, hC⟩ | ⟨m, q, hm, hC⟩
      · exact PowerlessEvaluationDirection.agreement_l
          (PowerlessBoundedCertificateSound.recognizes_l hℳ hω ht hT hAU hA hS hR hF hG hC)
      · obtain ⟨ha₀, hb₀⟩ := PowerlessFormulaConstructor.bounds_l hℳ hω ht.1 hT hC
        exact PowerlessLevyLocalAgreement.nand_l hℳ hω ht hT hAU hS hR hF hG hp hC
          ((h a).mp (h₁ a ha₀) k q (fun x hx => hn x (hk x hx)) ha)
          ((h b).mp (h₁ b hb₀) l q (fun x hx => hn x (hl x hx)) hb)
      · exact PowerlessLevyLocalAgreement.bounded_l hℳ hω ht hT hAU hS hR hF hG hA hC
          ((h b).mp (h₁ b (PowerlessBoundedCode.bounds_l hℳ hω ht.1 hT hC).2.2)
            m p (fun x hx => hn x (hm x hx)) hb)
      · subst p
        have hb₀ : direction_l ω A G F b := by
          rcases hm with ⟨hq, hm⟩ | ⟨hq, hm⟩
          · subst q
            exact ((h b).mp (h₁ b (PowerlessFormulaConstructor.bounds_l hℳ hω ht.1 hT hC).2)
              m e (fun x hx => hn x (hm x hx)) hb).1 rfl
          · subst q
            exact fun f hf hx => (hL m (hn m hm) b t₁ ⟨D, hD, hb⟩ f hf).mpr hx
        exact PowerlessEvaluationDirection.sigma_l (PowerlessEvaluationTags.distinct_l hℳ ht).1
          (PowerlessLevyLocalAgreement.existential_l hℳ hω ht hT hAU hS hR hF hG hC hb₀)
      · exact PowerlessEvaluationDirection.agreement_l (hL m (hn m hm) c q ⟨D, hD, hC⟩)))
  exact fun c hc => (h c).mp (h₀ c hc)

theorem class_l {N c p : carrier_l ℳ}
    (hL : PowerlessLevyAgreement.lower_l ω e T t₁ t₂ t₃ A F G N)
    (hc : PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c N p) :
    polarity_l ω A F G e t₁ p c := by
  obtain ⟨D, hD, hc⟩ := hc
  exact sound_l hℳ hω ht hT hAU hA hS hR hF hG hD hL c
    (PowerlessLevyEntry.natural_l hc).1 N p (fun _ hx => hx) hc

theorem first_l {c p : carrier_l ℳ}
    (hc : PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c t₁ p) :
    polarity_l ω A F G e t₁ p c :=
  class_l hℳ hω ht hT hAU hA hS hR hF hG
    (PowerlessLevyAgreement.lower_one_l hℳ hω ht hT hAU hA hS hR hF hG) hc

theorem sigma_l {c : carrier_l ℳ}
    (hc : PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c t₁ e) : direction_l ω A G F c :=
  (first_l hℳ hω ht hT hAU hA hS hR hF hG hc).1 rfl

theorem pi_l {c : carrier_l ℳ}
    (hc : PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c t₁ t₁) : direction_l ω A F G c :=
  (first_l hℳ hω ht hT hAU hA hS hR hF hG hc).2 rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevySound
