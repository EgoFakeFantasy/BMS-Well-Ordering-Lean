import BMSConstructibleBridge.PowerlessSourceWitnessSequence

/-!
# 层次类中见证的无全域覆盖闭包

把见证属于某个实际层写入原公式。其局部覆盖由定义推出，
不要求环境模型的每个对象都属于该层次。结论仍使用完整无幂集核心，
且只关闭指定公式的层次内见证，不宣称全部公式初等性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceWitnessDomain

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def domain_l (ω e T t₁ t₂ t₃ y : carrier_l ℳ) : Prop :=
  ∃ γ U, stage_l ω e T t₁ t₂ t₃ γ U ∧ member_l ℳ y U

def domain_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ y : Term ℒ Γ Δ .set) :
    Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) :=
    (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.existsE .set (.conj
    (stage_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (.bvar (.there .here)) (.bvar .here))
    (SecondOrderObjectSyntax.member_m (q y) (.bvar .here))))

theorem domain_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ y : Term ℒ Γ Δ .set) :
    (domain_m ω e T t₁ t₂ t₃ y).satisfies η ↔
      domain_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (y.eval η) := by
  simp only [domain_m, domain_l, Formula.satisfies, stage_formula_l hℳ,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def restrict_m {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) : Formula ℒ [] (.set :: .set :: Γ) :=
  let q (s : Term ℒ [] Γ .set) :=
    (s.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set
  .conj φ (domain_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (.fvar .here))

theorem restrict_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ)) (η : Env ℳ [] Γ)
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) (x y : carrier_l ℳ) :
    (restrict_m φ ω e T t₁ t₂ t₃).satisfies ((η.pushFree x).pushFree y) ↔
      φ.satisfies ((η.pushFree x).pushFree y) ∧
        domain_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) y := by
  simp only [restrict_m, Formula.satisfies, domain_formula_l hℳ, Term.eval_weakenFree]
  rfl

/-- 层次内的存在见证在更高真极限层中关闭；没有全域覆盖前提。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) (α : carrier_l ℳ)
    (hω : omega_l (ω.eval (PowerlessComprehension.env_l η)))
    (he : PowerlessNatural.zero_l (e.eval (PowerlessComprehension.env_l η)))
    (hα : PowerlessOrdinal.ordinal_l α) :
    ∃ δ U, PowerlessStagePair.limit_l δ ∧ member_l ℳ α δ ∧
      stage_l (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
        (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
        (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) δ U ∧
      ∀ x, member_l ℳ x U →
        (∃ y, domain_l (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
          (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
          (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) y ∧
          φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y)) →
        ∃ y, member_l ℳ y U ∧
          φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) := by
  let ρ := PowerlessComprehension.env_l η
  let ψ := restrict_m φ ω e T t₁ t₂ t₃
  obtain ⟨f, hf⟩ := PowerlessSourceWitnessSequence.exists_l hℳ ψ η ω e T t₁ t₂ t₃ α hω he hα
    (fun x y h => ((restrict_formula_l hℳ φ ρ ω e T t₁ t₂ t₃ x y).mp h).2)
  obtain ⟨δ, U, hδ, hαδ, hU, h⟩ := PowerlessSourceWitnessSequence.limit_l hℳ hω hf
  refine ⟨δ, U, hδ, hαδ, hU, ?_⟩
  rintro x hx ⟨y, hy, hφ⟩
  obtain ⟨z, hz, hψ⟩ := h x hx
    ⟨y, (restrict_formula_l hℳ φ ρ ω e T t₁ t₂ t₃ x y).mpr ⟨hφ, hy⟩⟩
  exact ⟨z, hz, ((restrict_formula_l hℳ φ ρ ω e T t₁ t₂ t₃ x z).mp hψ).1⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceWitnessDomain
