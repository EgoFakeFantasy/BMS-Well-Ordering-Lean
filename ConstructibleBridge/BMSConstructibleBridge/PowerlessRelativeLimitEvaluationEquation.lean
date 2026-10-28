import BMSConstructibleBridge.PowerlessFiniteEvaluationEquation
import BMSConstructibleBridge.PowerlessRelativeLimitEvaluationFiniteHistoryDerives

/-! # 消去有限历史前提的内部求值方程

固定非零极限层中的静态参数后，全部内部编号都有覆盖它的有限历史。
全体 C 值序列集 Q 单独量化，不要求 Q∈C；方程不再要求调用者给出历史。
结论仍是原四分支规则，完整良构码的语义对应另行证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationEquation

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def conclusion_m {Γ Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up t))
  .forallE .set <| .imp (PowerlessFiniteSequencesSyntax.spec_m (up ω) (up C) (.bvar .here)) <|
    membershipLevyBound.boundedForall (up ω) <| .forallE .set <|
      let Q : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
      let n : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
      let f : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
      .iff (PowerlessFiniteEvaluationQuery.formula_m (w C) (w ω) (w e) (w N) (w T) (w A) (w S)
        (w t₁) (w t₂) (w t₃) Q n f)
        (.conj (SecondOrderObjectSyntax.member_m f (w S))
          (PowerlessFiniteEvaluationClause.formula_m (w C) (w ω) (w e) (w N) (w T) (w A) (w S)
            (w t₁) (w t₂) (w t₃) Q n f))

theorem conclusion_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (C ω e N T A S t₁ t₂ t₃ : Term ℒ Γ Δ .set) :
    (conclusion_m C ω e N T A S t₁ t₂ t₃).satisfies η ↔
      ∀ Q, PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) (ω.eval η) (C.eval η) Q →
        ∀ n, member_l 𝒩 n (ω.eval η) → ∀ f,
          (PowerlessFiniteEvaluationQuery.holds_l (C.eval η) (ω.eval η) (e.eval η) (N.eval η)
            (T.eval η) (A.eval η) (S.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) Q n f ↔
            member_l 𝒩 f (S.eval η) ∧
              PowerlessFiniteEvaluationClause.holds_l (C.eval η) (ω.eval η) (e.eval η) (N.eval η)
                (T.eval η) (A.eval η) (S.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) Q n f) := by
  simp only [conclusion_m, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessFiniteSequencesSyntax.spec_formula_l,
    PowerlessFiniteEvaluationQuery.formula_l, PowerlessFiniteEvaluationClause.formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 三个绑定变量依次为基集、极限序数与层；共享实际有限历史的全部前提。 -/
def guarded_m {Δ : SortContext ℒ} (ω e N T A S : Term ℒ [] Δ .set)
    (φ : Formula ℒ [.set, .set, .set] Δ) : Formula ℒ [] Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let B : Term ℒ [.set, .set, .set] Δ .set := .bvar (.there (.there .here))
    let β : Term ℒ [.set, .set, .set] Δ .set := .bvar (.there .here)
    let C : Term ℒ [.set, .set, .set] Δ .set := .bvar .here
    let w (t : Term ℒ [] Δ .set) := up (up (up t))
    .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β C) <|
        .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
          .imp (parameters_m Δ C (fun v => .fvar v)) <|
            .imp (SecondOrderObjectSyntax.member_m (w S) C) <|
              .imp (SecondOrderOmegaSyntax.omega_m (w ω)) <|
                .imp (SecondOrderObjectSyntax.member_m (w ω) C) <|
                  .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (up (w e))))) <|
                    .imp (PowerlessFiniteSequencesSyntax.spec_m (w ω) (w ω) (w N)) <|
                      .imp (SecondOrderObjectSyntax.map_m (w T) (w ω) (w ω)) <|
                        .imp (PowerlessFiniteSequencesSyntax.spec_m (w ω) (w A) (w S)) <|
                          .imp (PowerlessRelativeClassConstructorBounds.bounds_m (w ω) (w e) (w T)) <|
                            φ

def schema_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let w (t : Term ℒ [] Δ .set) := up (up (up t))
  guarded_m ω e N T A S
    (conclusion_m (.bvar .here) (w ω) (w e) (w N) (w T) (w A) (w S) (w t₁) (w t₂) (w t₃))

def sentence_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω e N T A S t₁ t₂ t₃)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    (sentence_m ω e N T A S t₁ t₂ t₃).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η B β C hBase hC hLimit hParams hSC hω hωC he hN hT hS hBounds
  let ξ := ((η.pushBound B).pushBound β).pushBound C
  let w (t : Term ℒ [] Δ .set) := up (up (up t))
  have hHist := ((_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeLimitEvaluationFiniteHistoryDerives.models_l hℳ ω e N T A S t₁ t₂ t₃))
      η B β C hBase hC hLimit hParams hSC hω hωC he hN hT hS
  have hHist' := (PowerlessRelativeLimitEvaluationFiniteHistoryDerives.conclusion_formula_l ξ
    (.bvar .here) (w ω) (w e) (w T) (w A) (w S) (w t₁) (w t₂) (w t₃)).mp hHist
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ ξ
    (.bvar (.there (.there .here)))).mp hBase
  have hC' := (PowerlessRelativeHierarchySemantics.level_formula_l K ξ
    (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).mp hC
  have hLimit' := (PowerlessRelativeHierarchySemantics.limit_formula_l
    (hℳ := hℳ) ξ (.bvar (.there .here))).mp hLimit
  have hω' := (omega_formula_l ξ (w ω)).mp hω
  have hN' := (PowerlessFiniteSequencesSyntax.spec_formula_l ξ (w ω) (w ω) (w N)).mp hN
  have hT' := (map_formula_l ξ (w T) (w ω) (w ω)).mp hT
  have hS' := (PowerlessFiniteSequencesSyntax.spec_formula_l ξ (w ω) (w A) (w S)).mp hS
  have hBounds' := (PowerlessRelativeClassConstructorBounds.bounds_formula_l ξ (w ω) (w e) (w T)).mp hBounds
  have hωC' : mem_l hℳ ((w ω).eval ξ) C := hωC
  simp only [ξ, w, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]
    at hHist' hω' hN' hT' hS' hBounds' hωC'
  have he' : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) (e.eval η) := by
    simpa only [PowerlessNatural.zero_l, ThirdOrderSemantics.member_l, Formula.satisfies,
      SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here] using he
  have hωEq := SecondOrderOmega.unique_l hℳ hω' K.omega_spec
  apply (conclusion_formula_l ξ (.bvar .here) (w ω) (w e) (w N) (w T) (w A) (w S) (w t₁) (w t₂) (w t₃)).mpr
  simp only [ξ, w, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]
  intro Q hQ n hn f
  obtain ⟨r, hr, hSucc⟩ := K.omega_spec.1.2 n (hωEq ▸ hn)
  obtain ⟨F, _, hF⟩ := hHist' r (hωEq.symm ▸ hr)
  rw [hωEq] at hN' hT' hS' hBounds' hωC' hQ hF ⊢
  exact PowerlessFiniteEvaluationEquation.equation_l K hBase' hLimit' hC' hωC' he' hN' hT' hS' hQ hr hF
    ((hSucc n).mpr (Or.inr rfl)) (fun t a b h => hBounds' t a b n h)

theorem derives_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω e N T A S t₁ t₂ t₃)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω e N T A S t₁ t₂ t₃)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationEquation
