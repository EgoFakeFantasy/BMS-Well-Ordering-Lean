import BMSConstructibleBridge.PowerlessSourceClass
import BMSConstructibleBridge.PowerlessOmegaOrdinal

/-!
# 实际层次类的原公式语义

类域为某个实际层的成员；先证明其非空，再将给定的类内参数环境
提升到实际子类型结构。原公式量词相对化的域解释在这里完全由
层次域公式的语义推出，不保留一个任意域解释前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyClass

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem nonempty_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T) :
    ∃ x, PowerlessSourceWitnessDomain.domain_l ω e T t₁ t₂ t₃ x := by
  have hω₀ := PowerlessOmegaOrdinal.ordinal_l hℳ hω
  obtain ⟨β, hβ⟩ := PowerlessNatural.successor_exists_l hℳ ω
  obtain ⟨A, hA⟩ := PowerlessHierarchyStage.exists_l hℳ hω hω₀ e T t₁ t₂ t₃
  obtain ⟨B, hB⟩ := PowerlessHierarchyStage.exists_l hℳ hω
    (PowerlessOrdinalOrder.successor_l hℳ hω₀ hβ) e T t₁ t₂ t₃
  exact ⟨A, β, B, hB, PowerlessStageStructure.member_l hℳ hω ht hT hA hB
    ((hβ ω).mpr (Or.inr rfl))⟩

def domain_m {Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: Δ) :=
  PowerlessSourceWitnessDomain.domain_m
    (ω.weakenFree SetTheory.SetSort.set) (e.weakenFree SetTheory.SetSort.set)
    (T.weakenFree SetTheory.SetSort.set) (t₁.weakenFree SetTheory.SetSort.set)
    (t₂.weakenFree SetTheory.SetSort.set) (t₃.weakenFree SetTheory.SetSort.set) (.fvar .here)

theorem domain_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Δ : SortContext ℒ} (η : Env ℳ [] Δ) (ω e T t₁ t₂ t₃ : Term ℒ [] Δ .set) (x : carrier_l ℳ) :
    (domain_m ω e T t₁ t₂ t₃).satisfies (η.pushFree x) ↔
      PowerlessSourceWitnessDomain.domain_l
        (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) x := by
  simp only [domain_m, PowerlessSourceWitnessDomain.domain_formula_l hℳ, Term.eval_weakenFree]
  rfl

/-- 环境中的所有变量都确实属于类时，才将它提升为类结构环境。 -/
def lift_l {P : carrier_l ℳ → Prop} (hP : ∃ x, P x) {Γ Δ : SortContext ℒ}
    (η : Env ℳ Γ Δ) (hη : ∀ t : Term ℒ Γ Δ .set, P (t.eval η)) :
    Env (PowerlessSourceClass.structure_l P hP) Γ Δ where
  boundVal {s} v := by
    cases s
    exact ⟨η.boundVal v, hη (.bvar v)⟩
  freeVal {s} v := by
    cases s
    exact ⟨η.freeVal v, hη (.fvar v)⟩

theorem env_l {P : carrier_l ℳ → Prop} (hP : ∃ x, P x) {Γ Δ : SortContext ℒ}
    (η : Env ℳ Γ Δ) (hη : ∀ t : Term ℒ Γ Δ .set, P (t.eval η)) :
    PowerlessSourceClass.env_l (lift_l hP η hη) = η := by
  apply Env.ext <;> intro s v <;> cases s <;> rfl

theorem lift_env_l {P : carrier_l ℳ → Prop} {hP : ∃ x, P x} {Γ Δ : SortContext ℒ}
    (η : Env (PowerlessSourceClass.structure_l P hP) Γ Δ)
    (hη : ∀ t : Term ℒ Γ Δ .set, P (t.eval (PowerlessSourceClass.env_l η))) :
    lift_l hP (PowerlessSourceClass.env_l η) hη = η := by
  apply Env.ext <;> intro s v <;> cases s <;> apply Subtype.ext <;> rfl

/-- 真实层次域的解释已消去；类内环境条件只约束实际自由、绑定变量。 -/
theorem formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (η : Env ℳ Γ Δ)
    (ω e T t₁ t₂ t₃ : Term ℒ [] Δ .set)
    (hω : omega_l (ω.eval (PowerlessSourceClass.free_l η)))
    (ht : PowerlessEvaluationTags.tags_l (e.eval (PowerlessSourceClass.free_l η))
      (t₁.eval (PowerlessSourceClass.free_l η)) (t₂.eval (PowerlessSourceClass.free_l η))
      (t₃.eval (PowerlessSourceClass.free_l η)))
    (hT : PowerlessTriangular.triangular_l (ω.eval (PowerlessSourceClass.free_l η))
      (e.eval (PowerlessSourceClass.free_l η)) (T.eval (PowerlessSourceClass.free_l η)))
    (hη : ∀ t : Term ℒ Γ Δ .set, PowerlessSourceWitnessDomain.domain_l
      (ω.eval (PowerlessSourceClass.free_l η)) (e.eval (PowerlessSourceClass.free_l η))
      (T.eval (PowerlessSourceClass.free_l η)) (t₁.eval (PowerlessSourceClass.free_l η))
      (t₂.eval (PowerlessSourceClass.free_l η)) (t₃.eval (PowerlessSourceClass.free_l η)) (t.eval η)) :
    (PowerlessSourceClass.form_m (domain_m ω e T t₁ t₂ t₃) φ).satisfies η ↔
      φ.satisfies (lift_l (nonempty_l hℳ hω ht hT) η hη) := by
  have h := PowerlessSourceClass.formula_l (domain_m ω e T t₁ t₂ t₃) φ
    (lift_l (nonempty_l hℳ hω ht hT) η hη) (by
      intro x
      rw [env_l]
      exact domain_formula_l hℳ _ ω e T t₁ t₂ t₃ x)
  rw [env_l] at h
  exact h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyClass
