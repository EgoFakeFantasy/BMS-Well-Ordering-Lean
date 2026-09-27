import BMSConstructibleBridge.PowerlessSourceReflection
import BMSConstructibleBridge.PowerlessSourceCoverage

/-!
# 层次类内的原公式分离

以实际有限反射层解释指定原公式，再在该层的真实后继中
用原源覆盖构造子集。所得子集确实属于层次类，不把环境
中的分离存在性当作类内存在性；不假设类已经满足核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassSeparation

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem relation_l (U : carrier_l ℳ) (hU : ∃ x, member_l ℳ x U) :
    (PowerlessSourceClass.structure_l (fun x => member_l ℳ x U) hU).relInterp =
      (PowerlessMemberStructure.structure_l U hU).relInterp := by
  funext r v
  match r, v with
  | .membership, .cons x (.cons y .nil) => rfl

theorem structure_l (U : carrier_l ℳ) (hU : ∃ x, member_l ℳ x U) :
    PowerlessSourceClass.structure_l (fun x => member_l ℳ x U) hU =
      PowerlessMemberStructure.structure_l U hU := by
  unfold PowerlessSourceClass.structure_l PowerlessMemberStructure.structure_l
  congr 1
  exact relation_l U hU

/-- 任意指定原公式的类相对化子集，实际属于层次类。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [.set] Δ)
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Δ.length)
    (ω e T t₁ t₂ t₃ A : Term ℒ [] Δ .set)
    (hω : omega_l (ω.eval (PowerlessComprehension.env_l η)))
    (ht : PowerlessEvaluationTags.tags_l (e.eval (PowerlessComprehension.env_l η))
      (t₁.eval (PowerlessComprehension.env_l η)) (t₂.eval (PowerlessComprehension.env_l η))
      (t₃.eval (PowerlessComprehension.env_l η)))
    (hT : PowerlessTriangular.triangular_l (ω.eval (PowerlessComprehension.env_l η))
      (e.eval (PowerlessComprehension.env_l η)) (T.eval (PowerlessComprehension.env_l η)))
    (hη : ∀ v : Variable Δ .set, PowerlessSourceWitnessDomain.domain_l
      (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
      (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
      (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η))
      ((PowerlessComprehension.env_l η).freeVal v)) :
    ∃ B, PowerlessSourceWitnessDomain.domain_l
      (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
      (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
      (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) B ∧
      ∀ x, member_l ℳ x B ↔ member_l ℳ x (A.eval (PowerlessComprehension.env_l η)) ∧
        (PowerlessSourceClass.form_m (PowerlessHierarchyClass.domain_m ω e T t₁ t₂ t₃) φ).satisfies
          ((PowerlessComprehension.env_l η).pushBound x) := by
  let ρ := PowerlessComprehension.env_l η
  let D := PowerlessHierarchyClass.domain_m ω e T t₁ t₂ t₃
  let ψ : Formula ℒ [.set] Δ :=
    .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (A.weakenBound SetTheory.SetSort.set)) φ
  obtain ⟨δ, U, hU₀, hδ, _, hU, h₀, h₁⟩ := PowerlessSourceReflection.exists_l hℳ ψ η
    ω e T t₁ t₂ t₃ (ω.eval ρ) hω ht hT (PowerlessOmegaOrdinal.ordinal_l hℳ hω) hη
  have hρ : ∀ t : Term ℒ [] Δ .set, member_l ℳ (t.eval ρ) U := by
    intro t
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact h₀ v
    | .app f _ => nomatch f
  let θ := PowerlessHierarchyClass.lift_l hU₀ ρ hρ
  have h₂ (x : carrier_l ℳ) (hx : member_l ℳ x U) :
      ψ.satisfies (θ.pushBound ⟨x, hx⟩) ↔
        member_l ℳ x (A.eval ρ) ∧ (PowerlessSourceClass.form_m D φ).satisfies (ρ.pushBound x) := by
    let ξ := θ.pushBound (sort := SetTheory.SetSort.set) ⟨x, hx⟩
    have hξ : PowerlessSourceClass.env_l ξ = ρ.pushBound x := by
      exact (PowerlessSourceClass.push_l θ ⟨x, hx⟩).trans
        (congrArg (fun ζ : Env ℳ [] Δ => ζ.pushBound (sort := SetTheory.SetSort.set) x)
          (PowerlessHierarchyClass.env_l hU₀ ρ hρ))
    have h₃ := h₁ (PowerlessSourceClass.env_l ξ) (by rw [hξ]; rfl) (by
      intro t
      rw [PowerlessSourceClass.term_l]
      exact (t.eval ξ).property)
    rw [PowerlessHierarchyClass.lift_env_l, hξ] at h₃
    have h₄ : (PowerlessSourceClass.form_m D ψ).satisfies (ρ.pushBound x) ↔
        member_l ℳ x (A.eval ρ) ∧ (PowerlessSourceClass.form_m D φ).satisfies (ρ.pushBound x) := by
      change (member_l ℳ x ((A.weakenBound SetTheory.SetSort.set).eval (ρ.pushBound x)) ∧
        (PowerlessSourceClass.form_m D φ).satisfies (ρ.pushBound x)) ↔ _
      rw [Term.eval_weakenBound]
    exact h₃.symm.trans h₄
  obtain ⟨γ, hγ⟩ := PowerlessNatural.successor_exists_l hℳ δ
  obtain ⟨C, hC⟩ := PowerlessHierarchyStage.exists_l hℳ hω
    (PowerlessOrdinalOrder.successor_l hℳ hδ.1 hγ)
    (e.eval ρ) (T.eval ρ) (t₁.eval ρ) (t₂.eval ρ) (t₃.eval ρ)
  have h₅ := PowerlessSourceCoverage.operator_l hℳ hω ht hT (hA := hU₀)
    (PowerlessStageStructure.successor_l hℳ hω ht hT hU hC hγ) ψ
  unfold PowerlessMemberStructure.structure_l at h₅
  have hR := relation_l U hU₀
  dsimp only [PowerlessMemberStructure.structure_l] at hR
  rw [← hR] at h₅
  obtain ⟨B, hB, h₅⟩ := h₅ θ
  refine ⟨B, ⟨γ, C, hC, hB⟩, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨hx, hψ⟩ := (h₅ x).mp hx
    exact (h₂ x hx).mp hψ
  · intro hx
    have hxU := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
      (A.eval ρ) x (hρ A) hx.1
    exact (h₅ x).mpr ⟨hxU, (h₂ x hxU).mpr hx⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassSeparation
