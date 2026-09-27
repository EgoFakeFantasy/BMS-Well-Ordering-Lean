import BMSConstructibleBridge.PowerlessPartialTruthFinite
import BMSConstructibleBridge.PowerlessLevyAgreementAbsolute
import BMSConstructibleBridge.PowerlessStageAdditionIteration

/-!
# 不携带当前层求值图的有限层一致公式

下域及其求值图是具名参数；当前域真值使用原部分真值公式。
当前域的完整求值图只出现在正确性结论中，不进入源公式参数。
分类码与赋值仍量化全部内部对象。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAmbientAgreement

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def agreement_l (k : Nat) (ω e T t₁ t₂ t₃ n A F : carrier_l ℳ) : Prop :=
  ∀ c p, PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c n p →
    ∀ f, (∃ j, member_l ℳ j ω ∧ map_l f j A) →
      (PowerlessTruthSign.sign_l e t₁ F p c f ↔
        (PowerlessPartialTruth.formula_m k).satisfies (PowerlessTruthOracle.env_l ω e T t₁ t₂ t₃ n p c f))

def agreement_m (k : Nat) {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ n A F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (t : Term ℒ Γ Δ .set) :=
    (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let r (t : Term ℒ Γ Δ .set) := (q t).weakenBound SetTheory.SetSort.set
  .forallE .set (.forallE .set (.imp
    (PowerlessLevyCertificate.class_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃)
      (.bvar (.there .here)) (q n) (.bvar .here))
    (.forallE .set (.imp
      (.existsE .set (.conj
        (SecondOrderObjectSyntax.member_m (.bvar .here) ((r ω).weakenBound SetTheory.SetSort.set))
        (SecondOrderObjectSyntax.map_m (.bvar (.there .here)) (.bvar .here)
          ((r A).weakenBound SetTheory.SetSort.set))))
      (.iff (PowerlessTruthSign.sign_m (r e) (r t₁) (r F)
        (.bvar (.there .here)) (.bvar (.there (.there .here))) (.bvar .here))
        (PowerlessTruthOracle.instance_m (PowerlessPartialTruth.formula_m k)
          (r ω) (r e) (r T) (r t₁) (r t₂) (r t₃) (r n)
          (.bvar (.there .here)) (.bvar (.there (.there .here))) (.bvar .here)))))))

theorem agreement_formula_l (k : Nat) {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e T t₁ t₂ t₃ n A F : Term ℒ Γ Δ .set) :
    (agreement_m k ω e T t₁ t₂ t₃ n A F).satisfies η ↔
      agreement_l k (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (n.eval η) (A.eval η) (F.eval η) := by
  simp only [agreement_m, agreement_l, Formula.satisfies, PowerlessLevyCertificate.class_formula_l,
    PowerlessTruthSign.sign_formula_l, PowerlessTruthOracle.instance_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, map_formula_l, Term.eval_weakenBound]
  rfl

theorem absolute_l {U δ R H : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n A F : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
    (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
    (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m)
    (h₀ : Theory.Models (structure_l U hU₀) PowerlessTruthIntroduction.theory_m)
    (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)
    (k : Nat) (hn : PowerlessNumeral.numeral_l e.val k n.val)
    (hS : ∀ j, j < k → Theory.Models (structure_l U hU₀)
      (PowerlessOracleIntroduction.theory_m
        (PowerlessPartialTruthIntroduction.oracle_m (PowerlessPartialTruth.formula_m j)))) :
    agreement_l k (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ n A F ↔
      PowerlessLevyAgreement.agreement_l ω.val e.val T.val t₁.val t₂.val t₃.val A.val F.val H n.val := by
  classical
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hωδ₀ : subset_l ω.val δ := fun a ha => PowerlessOrdinal.transitive_l hδ.1 ω.val a hωδ ha
  have hI : ∀ x, member_l ℳ x ω.val → ∀ G,
      PowerlessAddition.iteration_l ω.val e.val x G → member_l ℳ G U :=
    fun _ hx _ hG => PowerlessStageAdditionIteration.limit_l hℳ hω ht hT hU hωδ hδ hx hG
  have hD := PowerlessStageFiniteSubsets.finite_l hℳ hω ht hT hU hδ hωδ₀
  have hC (c p : type_l U) :=
    PowerlessLevyCertificateAbsolute.class_l (hB := hU₀)
      (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) (c := c) (n := n) (p := p)
      hℳ hUT hω ht.1 hT hI hD
  have hF (p c f : type_l U) :
      PowerlessTruthSign.sign_l (ℳ := structure_l U hU₀) e t₁ F p c f ↔
        PowerlessTruthSign.sign_l e.val t₁.val F.val p.val c.val f.val := by
    have hE (a b : type_l U) : a = b ↔ a.val = b.val :=
      ⟨fun h => congrArg (fun x : type_l U => x.val) h, Subtype.ext⟩
    exact or_congr (and_congr (hE p e) (PowerlessValueAbsolute.query_l hUT))
      (and_congr (hE p t₁) (not_congr (PowerlessValueAbsolute.query_l hUT)))
  have hB (p c f : type_l U)
      (hc : PowerlessLevyCertificate.class_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val n.val p.val)
      (hf : ∃ j, member_l ℳ j ω.val ∧ map_l f.val j A.val) :=
    PowerlessPartialTruthFinite.source_l (hU₀ := hU₀) hℳ hω ht hT hU hδ hωδ h𝒩 h₀ hR hH k hS n hn p c f hc (by
      obtain ⟨j, hj, hf⟩ := hf
      exact ⟨j, hj, PowerlessFunction.range_l hℳ hf
        (fun _ a ha => hUT A.val a A.property (PowerlessFunction.value_mem_l hℳ hf ha).2)⟩)
  constructor
  · intro h c p hc f hf
    obtain ⟨hcω, _, hpω, hp⟩ := PowerlessLevyCertificate.natural_l hc
    obtain ⟨j, hj, hf⟩ := hf
    have hfU : member_l ℳ f U := PowerlessStageFiniteGraphs.finite_l hℳ hω ht hT hU hδ hωδ₀ j hj f
      (PowerlessFunction.range_l hℳ hf
        (fun _ a ha => hUT A.val a A.property (PowerlessFunction.value_mem_l hℳ hf ha).2))
    let c₀ : type_l U := ⟨c, hUT ω.val c ω.property hcω⟩
    let p₀ : type_l U := ⟨p, hUT ω.val p ω.property hpω⟩
    let f₀ : type_l U := ⟨f, hfU⟩
    have h₁ := h c₀ p₀ ((hC c₀ p₀).mpr hc) f₀
      ⟨⟨j, hUT ω.val j ω.property hj⟩, hj, (PowerlessSourceGraphAbsolute.map_l hUT).mpr hf⟩
    have h₂ := (hF p₀ c₀ f₀).symm.trans (h₁.trans (hB p₀ c₀ f₀ hc ⟨j, hj, hf⟩))
    have het := (PowerlessEvaluationTags.distinct_l hℳ ht).1
    change PowerlessTruthSign.sign_l e.val t₁.val F.val p c f ↔
      PowerlessTruthSign.sign_l e.val t₁.val H p c f at h₂
    rcases hp with rfl | rfl
    · simpa only [PowerlessTruthSign.positive_l het] using h₂
    · have h₃ : ¬PowerlessEvaluationClause.query_l F.val c f ↔ ¬PowerlessEvaluationClause.query_l H c f := by
        simpa only [PowerlessTruthSign.negative_l het] using h₂
      exact not_iff_not.mp h₃
  · intro h c p hc f hf
    have hc₀ := (hC c p).mp hc
    obtain ⟨j, hj, hf⟩ := hf
    have hf₀ : ∃ j, member_l ℳ j ω.val ∧ map_l f.val j A.val :=
      ⟨j.val, hj, (PowerlessSourceGraphAbsolute.map_l hUT).mp hf⟩
    have h₁ := h c.val p.val hc₀ f.val hf₀
    have h₂ : PowerlessTruthSign.sign_l e.val t₁.val F.val p.val c.val f.val ↔
        PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val :=
      or_congr (and_congr Iff.rfl h₁) (and_congr Iff.rfl (not_congr h₁))
    exact (hF p c f).trans (h₂.trans (hB p c f hc₀ hf₀).symm)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAmbientAgreement
