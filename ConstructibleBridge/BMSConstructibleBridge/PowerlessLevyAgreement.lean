import BMSConstructibleBridge.PowerlessLevyZero
import BMSConstructibleBridge.PowerlessBoundedCertificateSound

/-!
# 同一内部层号及其以下的查询一致关系

关系明确量化实际分类证书和实际赋值图，层号 n 是对象参数。
零层由传递子域绝对性证明；一般低层一致性是后续升层定理的显式前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyAgreement

open Logic FirstOrder ThirdOrderSemantics PowerlessLevyCertificate

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def agreement_l (ω e T t₁ t₂ t₃ A F G n : carrier_l ℳ) : Prop :=
  ∀ c p, class_l ω e T t₁ t₂ t₃ c n p → PowerlessEvaluationAgreement.point_l ω A F G c

def agreement_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ A F G n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set (.forallE .set (.imp
    (class_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (.bvar (.there .here)) (w n) (.bvar .here))
    (PowerlessEvaluationAgreement.point_m (w ω) (w A) (w F) (w G) (.bvar (.there .here)))))

theorem agreement_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ A F G n : Term ℒ Γ Δ .set) :
    (agreement_m ω e T t₁ t₂ t₃ A F G n).satisfies η ↔
      agreement_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (A.eval η) (F.eval η) (G.eval η) (n.eval η) := by
  simp only [agreement_m, agreement_l, Formula.satisfies, class_formula_l,
    PowerlessEvaluationAgreement.point_formula_l, Term.eval_weakenBound]
  rfl

def lower_l (ω e T t₁ t₂ t₃ A F G n : carrier_l ℳ) : Prop :=
  ∀ m, member_l ℳ m n → agreement_l ω e T t₁ t₂ t₃ A F G m

def lower_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ A F G n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (w n))
    (agreement_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w A) (w F) (w G) (.bvar .here)))

theorem lower_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ A F G n : Term ℒ Γ Δ .set) :
    (lower_m ω e T t₁ t₂ t₃ A F G n).satisfies η ↔
      lower_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (A.eval η) (F.eval η) (G.eval η) (n.eval η) := by
  simp only [lower_m, lower_l, Formula.satisfies, agreement_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem full_l {ω e T t₁ t₂ t₃ A F G n : carrier_l ℳ}
    (h : PowerlessEvaluationAgreement.agreement_l ω A F G) : agreement_l ω e T t₁ t₂ t₃ A F G n :=
  fun c _ hc => h c (PowerlessLevyCertificate.natural_l hc).1

theorem monotone_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ A F G m n : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hn : member_l ℳ n ω) (hmn : subset_l m n) (h : agreement_l ω e T t₁ t₂ t₃ A F G n) :
    agreement_l ω e T t₁ t₂ t₃ A F G m :=
  fun c p hc => h c p (PowerlessLevyCertificateClosure.monotone_l hℳ hω he hT hn hmn hc)

theorem lower_of_agreement_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ A F G n : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hn : member_l ℳ n ω) (h : agreement_l ω e T t₁ t₂ t₃ A F G n) :
    lower_l ω e T t₁ t₂ t₃ A F G n := by
  intro m hm
  exact monotone_l hℳ hω he hT hn
    (fun x hx => PowerlessNaturalOrder.member_transitive_l hℳ hω n hn m x hm hx) h

theorem zero_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ A U S R F G : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hAU : subset_l A U) (hA : PowerlessNaturalOrder.transitive_l A)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m U)
    (hR : ∀ f, member_l ℳ f R ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F)
    (hG : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ R G) :
    agreement_l ω e T t₁ t₂ t₃ A F G e :=
  fun _ _ hc => PowerlessBoundedCertificateSound.recognizes_l hℳ hω ht hT hAU hA hS hR hF hG
    (PowerlessLevyZero.class_l hℳ hω ht.1 hT hc)

theorem lower_one_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ A U S R F G : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hAU : subset_l A U) (hA : PowerlessNaturalOrder.transitive_l A)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m U)
    (hR : ∀ f, member_l ℳ f R ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F)
    (hG : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ R G) :
    lower_l ω e T t₁ t₂ t₃ A F G t₁ := by
  intro m hm
  rcases (ht.2.1 m).mp hm with hm | rfl
  · exact (ht.1 m hm).elim
  · exact zero_l hℳ hω ht hT hAU hA hS hR hF hG

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyAgreement
