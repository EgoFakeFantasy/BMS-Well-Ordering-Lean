import BMSConstructibleBridge.PowerlessClassSeparation
import BMSConstructibleBridge.PowerlessClassCollection
import BMSConstructibleBridge.PowerlessSourcePadding

/-!
# 实际层次类的完整原公式分离与收集

任意原绑定／自由参数环境先保留见证槽并打开参数，再加入
已证属于类的固定编码参数。相对化公式的环境真值与类结构
中的原公式逐步对应，不要求类先满足任一核心模式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassComprehension

open Logic FirstOrder ThirdOrderSemantics PowerlessSourceWitnessDomain PowerlessSourcePadding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessSourceClass.structure_l
  PowerlessSourceClass.type_l SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  {hP : ∃ x, domain_l ω e T t₁ t₂ t₃ x}

include hℳ hω ht hT

theorem separation_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ (.set :: Γ) Δ)
    (η : Env (PowerlessSourceClass.structure_l (domain_l ω e T t₁ t₂ t₃) hP) Γ Δ)
    (A : PowerlessSourceClass.type_l (domain_l ω e T t₁ t₂ t₃)) :
    ∃ B : PowerlessSourceClass.type_l (domain_l ω e T t₁ t₂ t₃),
      ∀ x : PowerlessSourceClass.type_l (domain_l ω e T t₁ t₂ t₃),
        member_l ℳ x.val B.val ↔ member_l ℳ x.val A.val ∧ φ.satisfies (η.pushBound x) := by
  let P := domain_l ω e T t₁ t₂ t₃
  have q := PowerlessClassBasic.parameters_l hℳ hω ht hT
  let a : PowerlessSourceClass.type_l P := ⟨ω, q.1⟩
  let b : PowerlessSourceClass.type_l P := ⟨e, q.2.1⟩
  let c : PowerlessSourceClass.type_l P := ⟨T, q.2.2.1⟩
  let d : PowerlessSourceClass.type_l P := ⟨t₁, q.2.2.2.1⟩
  let f : PowerlessSourceClass.type_l P := ⟨t₂, q.2.2.2.2.1⟩
  let g : PowerlessSourceClass.type_l P := ⟨t₃, q.2.2.2.2.2⟩
  let ρ := PowerlessSourceOpening.env_l η
  let ξ := env_l ρ a b c d f g A
  let ψ := form_m (PowerlessSourceParameters.unary_m φ)
  let D := PowerlessHierarchyClass.domain_m
    (omega_m (Δ := List.replicate Γ.length .set ++ Δ)) zero_m triangle_m tag₁_m tag₂_m tag₃_m
  obtain ⟨ζ, hζ⟩ := PowerlessSourceParameters.env_exists_l (PowerlessSourceClass.env_l ξ)
  have hω₀ : omega_l (omega_m.eval (PowerlessComprehension.env_l ζ)) := by rw [hζ]; exact hω
  have ht₀ : PowerlessEvaluationTags.tags_l (zero_m.eval (PowerlessComprehension.env_l ζ))
      (tag₁_m.eval (PowerlessComprehension.env_l ζ)) (tag₂_m.eval (PowerlessComprehension.env_l ζ))
      (tag₃_m.eval (PowerlessComprehension.env_l ζ)) := by rw [hζ]; exact ht
  have hT₀ : PowerlessTriangular.triangular_l (omega_m.eval (PowerlessComprehension.env_l ζ))
      (zero_m.eval (PowerlessComprehension.env_l ζ)) (triangle_m.eval (PowerlessComprehension.env_l ζ)) := by
    rw [hζ]; exact hT
  have hφ (x : PowerlessSourceClass.type_l P) :
      (PowerlessSourceClass.form_m D ψ).satisfies ((PowerlessSourceClass.env_l ξ).pushBound x.val) ↔
        φ.satisfies (η.pushBound x) := by
    have h := PowerlessSourceClass.formula_l D ψ (ξ.pushBound x) (fun y =>
      PowerlessHierarchyClass.domain_formula_l hℳ _ omega_m zero_m triangle_m tag₁_m tag₂_m tag₃_m y)
    rw [PowerlessSourceClass.push_l] at h
    have h₀ := formula_l (PowerlessSourceParameters.unary_m φ) (ρ.pushBound x) a b c d f g A
    rw [push_l] at h₀
    exact h.trans (h₀.trans (PowerlessSourceParameters.unary_l φ η x))
  obtain ⟨B, hB, h⟩ := PowerlessClassSeparation.exists_l hℳ ψ ζ
    omega_m zero_m triangle_m tag₁_m tag₂_m tag₃_m set_m hω₀ ht₀ hT₀ (by
      intro v
      rw [hζ]
      exact (ξ.freeVal v).property)
  rw [hζ] at hB h
  refine ⟨⟨B, hB⟩, fun x => ?_⟩
  exact (h x.val).trans (and_congr Iff.rfl (hφ x))

theorem collection_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ (.set :: .set :: Γ) Δ)
    (η : Env (PowerlessSourceClass.structure_l (domain_l ω e T t₁ t₂ t₃) hP) Γ Δ)
    (A : PowerlessSourceClass.type_l (domain_l ω e T t₁ t₂ t₃))
    (h : ∀ x : PowerlessSourceClass.type_l (domain_l ω e T t₁ t₂ t₃), member_l ℳ x.val A.val →
      ∃ y : PowerlessSourceClass.type_l (domain_l ω e T t₁ t₂ t₃),
        φ.satisfies ((η.pushBound x).pushBound y)) :
    ∃ B : PowerlessSourceClass.type_l (domain_l ω e T t₁ t₂ t₃),
      ∀ x : PowerlessSourceClass.type_l (domain_l ω e T t₁ t₂ t₃), member_l ℳ x.val A.val →
        ∃ y : PowerlessSourceClass.type_l (domain_l ω e T t₁ t₂ t₃),
          member_l ℳ y.val B.val ∧ φ.satisfies ((η.pushBound x).pushBound y) := by
  let P := domain_l ω e T t₁ t₂ t₃
  have q := PowerlessClassBasic.parameters_l hℳ hω ht hT
  let a : PowerlessSourceClass.type_l P := ⟨ω, q.1⟩
  let b : PowerlessSourceClass.type_l P := ⟨e, q.2.1⟩
  let c : PowerlessSourceClass.type_l P := ⟨T, q.2.2.1⟩
  let d : PowerlessSourceClass.type_l P := ⟨t₁, q.2.2.2.1⟩
  let f : PowerlessSourceClass.type_l P := ⟨t₂, q.2.2.2.2.1⟩
  let g : PowerlessSourceClass.type_l P := ⟨t₃, q.2.2.2.2.2⟩
  let ρ := PowerlessSourceOpening.env_l η
  let ξ := env_l ρ a b c d f g A
  let ψ := form_m (PowerlessSourceParameters.binary_m φ)
  let D := PowerlessHierarchyClass.domain_m
    (omega_m (Δ := List.replicate Γ.length .set ++ Δ)) zero_m triangle_m tag₁_m tag₂_m tag₃_m
  obtain ⟨ζ, hζ⟩ := PowerlessSourceParameters.env_exists_l (PowerlessSourceClass.env_l ξ)
  have hω₀ : omega_l (omega_m.eval (PowerlessComprehension.env_l ζ)) := by rw [hζ]; exact hω
  have ht₀ : PowerlessEvaluationTags.tags_l (zero_m.eval (PowerlessComprehension.env_l ζ))
      (tag₁_m.eval (PowerlessComprehension.env_l ζ)) (tag₂_m.eval (PowerlessComprehension.env_l ζ))
      (tag₃_m.eval (PowerlessComprehension.env_l ζ)) := by rw [hζ]; exact ht
  have hT₀ : PowerlessTriangular.triangular_l (omega_m.eval (PowerlessComprehension.env_l ζ))
      (zero_m.eval (PowerlessComprehension.env_l ζ)) (triangle_m.eval (PowerlessComprehension.env_l ζ)) := by
    rw [hζ]; exact hT
  have hφ (x y : PowerlessSourceClass.type_l P) :
      (PowerlessSourceClass.form_m D ψ).satisfies (((PowerlessSourceClass.env_l ξ).pushBound x.val).pushBound y.val) ↔
        φ.satisfies ((η.pushBound x).pushBound y) := by
    have h₀ := PowerlessSourceClass.formula_l D ψ ((ξ.pushBound x).pushBound y) (fun z =>
      PowerlessHierarchyClass.domain_formula_l hℳ _ omega_m zero_m triangle_m tag₁_m tag₂_m tag₃_m z)
    rw [PowerlessSourceClass.push_l, PowerlessSourceClass.push_l] at h₀
    have h₁ := formula_l (PowerlessSourceParameters.binary_m φ) ((ρ.pushBound x).pushBound y) a b c d f g A
    rw [push_l, push_l] at h₁
    exact h₀.trans (h₁.trans (PowerlessSourceParameters.binary_l φ η x y))
  obtain ⟨B, hB, h₀⟩ := PowerlessClassCollection.exists_l hℳ ψ ζ
    omega_m zero_m triangle_m tag₁_m tag₂_m tag₃_m A.val hω₀ ht₀ hT₀ (by
      rw [hζ]
      exact A.property)
  rw [hζ] at hB h₀
  refine ⟨⟨B, hB⟩, ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := h x hx
  obtain ⟨z, hzB, hz, hψ⟩ := h₀ x.val hx ⟨y.val, y.property, (hφ x y).mpr hy⟩
  exact ⟨⟨z, hz⟩, hzB, (hφ x ⟨z, hz⟩).mp hψ⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassComprehension

