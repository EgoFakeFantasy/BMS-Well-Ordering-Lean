import BMSConstructibleBridge.PowerlessEvaluationCompare
import BMSConstructibleBridge.PowerlessEvaluationRecursion
import BMSConstructibleBridge.PowerlessOrdinalInduction

/-!
# 见证闭包子域与原域的全内部求值一致性

比较命题量化子域的全部内部有限赋值，先给出原纯公式，再沿模型内部
ω 的隶属关系归纳。原子、联结词和存在分支全部消费同一实际求值方程。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationAgreement

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationClause

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def point_l (ω A F G n : carrier_l ℳ) : Prop :=
  ∀ f, (∃ m, ThirdOrderSemantics.member_l ℳ m ω ∧ map_l f m A) → (query_l F n f ↔ query_l G n f)

def point_m {Γ Δ : SortContext ℒ} (ω A F G n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
  .forallE .set (.imp (.existsE .set (.conj
    (SecondOrderObjectSyntax.member_m (.bvar .here) ((w ω).weakenBound SetTheory.SetSort.set))
    (SecondOrderObjectSyntax.map_m (.bvar (.there .here)) (.bvar .here) ((w A).weakenBound SetTheory.SetSort.set))))
    (.iff (query_m (w F) (w n) (.bvar .here)) (query_m (w G) (w n) (.bvar .here))))

theorem point_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω A F G n : Term ℒ Γ Δ .set) :
    (point_m ω A F G n).satisfies η ↔ point_l (ω.eval η) (A.eval η) (F.eval η) (G.eval η) (n.eval η) := by
  simp only [point_m, point_l, Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval,
    map_formula_l, query_formula_l, Term.eval_weakenBound]
  rfl

def agreement_l (ω A F G : carrier_l ℳ) : Prop :=
  ∀ n, ThirdOrderSemantics.member_l ℳ n ω → point_l ω A F G n

theorem interpolate_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A B F G H : carrier_l ℳ} (hAB : subset_l A B)
    (hA : agreement_l ω A F G) (hB : agreement_l ω B F H) : agreement_l ω A H G := by
  intro n hn f hf
  obtain ⟨m, hm, hf⟩ := hf
  have h := PowerlessFunction.range_l hℳ hf
    (fun _ y hy => hAB y (PowerlessFunction.value_mem_l hℳ hf hy).2)
  exact (hB n hn f ⟨m, hm, h⟩).symm.trans (hA n hn f ⟨m, hm, hf⟩)

def agreement_m {Γ Δ : SortContext ℒ} (ω A F G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
  .forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (w ω))
    (point_m (w ω) (w A) (w F) (w G) (.bvar .here)))

theorem agreement_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω A F G : Term ℒ Γ Δ .set) :
    (agreement_m ω A F G).satisfies η ↔ agreement_l (ω.eval η) (A.eval η) (F.eval η) (G.eval η) := by
  simp only [agreement_m, agreement_l, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, point_formula_l, Term.eval_weakenBound]
  rfl

theorem of_closure_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A U t₁ t₂ t₃ S R F G : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hAU : subset_l A U) (hC : PowerlessWitnessClosure.closure_l ω U F A A)
    (hS : ∀ f, ThirdOrderSemantics.member_l ℳ f S ↔ ∃ m, ThirdOrderSemantics.member_l ℳ m ω ∧ map_l f m U)
    (hR : ∀ f, ThirdOrderSemantics.member_l ℳ f R ↔ ∃ m, ThirdOrderSemantics.member_l ℳ m ω ∧ map_l f m A)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F)
    (hG : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ R G) : agreement_l ω A F G := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 4 :=
    { bound := Fin.cases ω (Fin.cases A (Fin.cases F (fun _ => G))), free := fun _ => U }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    point_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar .here)
  have h : ∀ n, φ.satisfies ((PowerlessComprehension.env_l η).pushFree n) ↔ point_l ω A F G n :=
    fun n => point_formula_l _ _ _ _ _ _
  have h₀ := PowerlessOrdinalInduction.induction_l hℳ φ η (PowerlessOmegaOrdinal.ordinal_l hℳ hω)
    (fun n hn h₁ => (h n).mpr (by
      intro f hf
      obtain ⟨m, hm, hf⟩ := hf
      have h₂ : ∃ m, ThirdOrderSemantics.member_l ℳ m ω ∧ map_l f m A := ⟨m, hm, hf⟩
      have hf₀ := PowerlessFunction.range_l hℳ hf (fun _ y hy => hAU y (PowerlessFunction.value_mem_l hℳ hf hy).2)
      calc
        query_l F n f ↔ PowerlessEvaluationClause.clause_l ω e T U t₁ t₂ t₃ F n f :=
          (PowerlessEvaluationRecursion.equation_l hℳ hω he hT hF hn f).trans (and_iff_right ((hS f).mpr ⟨m, hm, hf₀⟩))
        _ ↔ PowerlessEvaluationClause.clause_l ω e T A t₁ t₂ t₃ G n f :=
          PowerlessEvaluationCompare.clause_l hℳ hω he hT hAU hC h₂ (fun k hk => (h k).mp (h₁ k hk))
        _ ↔ query_l G n f :=
          ((PowerlessEvaluationRecursion.equation_l hℳ hω he hT hG hn f).trans (and_iff_right ((hR f).mpr h₂))).symm))
  exact fun n hn => (h n).mp (h₀ n hn)

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A U t₁ t₂ t₃ S F : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hAU : subset_l A U) (hC : PowerlessWitnessClosure.closure_l ω U F A A)
    (hS : ∀ f, ThirdOrderSemantics.member_l ℳ f S ↔ ∃ m, ThirdOrderSemantics.member_l ℳ m ω ∧ map_l f m U)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F) :
    ∃ R G, (∀ f, ThirdOrderSemantics.member_l ℳ f R ↔ ∃ m, ThirdOrderSemantics.member_l ℳ m ω ∧ map_l f m A) ∧
      PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ R G ∧ agreement_l ω A F G := by
  obtain ⟨R, G, hR, hG, _⟩ := PowerlessEvaluationRecursion.exists_l hℳ hω he hT A t₁ t₂ t₃
  exact ⟨R, G, hR, hG, of_closure_l hℳ hω he hT hAU hC hS hR hF hG⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationAgreement
