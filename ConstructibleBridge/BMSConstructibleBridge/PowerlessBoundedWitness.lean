import BMSConstructibleBridge.PowerlessSeparation
import BMSConstructibleBridge.PowerlessComprehension
import BMSConstructibleBridge.PowerlessOrdinalCollection
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure

/-!
# 容器已给定时的像与序数见证界

`PowerlessOrdinalCollection.witnesses_l` 的唯一 Collection 用法是 `partial_l` 造见证集合；
其余步骤（序数筛选、并、后继求界）本就只用 Separation 与 Union。
本模块把这一点精确分开：见证已被一个实际容器容纳时，像集合与共同序数界都不消费 Collection。
它不声称这样的容器在裸无幂集核心内总存在，也不替代原 `witnesses_l`。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedWitness

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 见证已落在容器内时，只对有见证的输入得到见证集合；只用分离。 -/
theorem partial_of_container_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (A D : carrier_l ℳ)
    (hb : ∀ x, member_l ℳ x A → ∀ y,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) → member_l ℳ y D) :
    ∃ B, ∀ x, member_l ℳ x A →
      (∃ y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y)) →
      ∃ y, member_l ℳ y B ∧
        φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) := by
  obtain ⟨B, hB⟩ := PowerlessSeparation.exists_l hℳ
    (PowerlessComprehension.binary_m φ).imageMembership (η.push A) D
  refine ⟨B, fun x hx h => ?_⟩
  obtain ⟨y, hy⟩ := h
  have hmem : ∃ input, member_l ℳ input A ∧
      (PowerlessComprehension.binary_m φ).denote η input y :=
    ⟨x, hx, (PowerlessComprehension.binary_l hℳ φ η x y).mpr hy⟩
  exact ⟨y, (hB y).mpr ⟨hb x hx y hy,
      SetTheory.Definitional.Project.Formula.satisfies_imageMembership_iff
        η (PowerlessComprehension.binary_m φ) A y |>.mpr hmem⟩, hy⟩

/-- 容器内的像本身：成员条件与 `PowerlessComprehension.image_l` 同形，
但不要求函数性，也不消费 Collection。 -/
theorem image_of_container_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (A D : carrier_l ℳ)
    (hb : ∀ x, member_l ℳ x A → ∀ y,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) → member_l ℳ y D) :
    ∃ C, ∀ y, member_l ℳ y C ↔
      ∃ x, member_l ℳ x A ∧
        φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) := by
  obtain ⟨C, hC⟩ := PowerlessSeparation.exists_l hℳ
    (PowerlessComprehension.binary_m φ).imageMembership (η.push A) D
  have hI : ∀ y, (∃ x, member_l ℳ x A ∧
        (PowerlessComprehension.binary_m φ).denote η x y) ↔
      ∃ x, member_l ℳ x A ∧
        φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) :=
    fun y => exists_congr fun x => and_congr Iff.rfl (PowerlessComprehension.binary_l hℳ φ η x y)
  have hJ : ∀ y, (∃ x, member_l ℳ x A ∧
        (PowerlessComprehension.binary_m φ).denote η x y) ↔
      SetTheory.Definitional.Project.Formula.satisfies ((η.push A).push y)
        (PowerlessComprehension.binary_m φ).imageMembership.body :=
    fun y => (SetTheory.Definitional.Project.Formula.satisfies_imageMembership_iff
      η (PowerlessComprehension.binary_m φ) A y).symm
  refine ⟨C, fun y => ⟨fun hy => (hI y).mp ((hJ y).mpr ((hC y).mp hy).2), fun hy => ?_⟩⟩
  obtain ⟨x, hx, hy'⟩ := hy
  exact (hC y).mpr ⟨hb x hx y hy', (hJ y).mp ((hI y).mpr ⟨x, hx, hy'⟩)⟩

/-- 见证已被容器容纳时，原公式的序数见证有共同实际序数界；这一形式不使用 Collection。 -/
theorem bound_of_container_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (A D : carrier_l ℳ)
    (hb : ∀ x, member_l ℳ x A → ∀ α,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree α) → member_l ℳ α D)
    (hD : ∀ α, member_l ℳ α D → PowerlessOrdinal.ordinal_l α) :
    ∃ β, PowerlessOrdinal.ordinal_l β ∧ ∀ x, member_l ℳ x A →
      (∃ α, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree α)) →
      ∃ α, member_l ℳ α β ∧
        φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree α) := by
  obtain ⟨B, hB⟩ := partial_of_container_l hℳ φ η A D hb
  let θ : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 0 :=
    { bound := Fin.elim0, free := fun _ => B }
  let ψ : Formula ℒ [] [.set] := PowerlessOrdinal.ordinal_m (.fvar .here)
  have hψ : ∀ α, ψ.satisfies ((PowerlessComprehension.env_l θ).pushFree α) ↔
      PowerlessOrdinal.ordinal_l α := fun α => PowerlessOrdinal.ordinal_formula_l hℳ _ _
  obtain ⟨C, hC⟩ := PowerlessComprehension.separation_l hℳ ψ θ B
  obtain ⟨β, hβ, h₀⟩ := PowerlessOrdinalCollection.bound_l hℳ
    (fun α hα => (hψ α).mp ((hC α).mp hα).2)
  refine ⟨β, hβ, fun x hx h => ?_⟩
  obtain ⟨α, hα, h₁⟩ := hB x hx h
  exact ⟨α, h₀ α ((hC α).mpr ⟨hα, (hψ α).mpr (hD α (hb x hx α h₁))⟩), h₁⟩

#print axioms partial_of_container_l
#print axioms image_of_container_l
#print axioms bound_of_container_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedWitness
