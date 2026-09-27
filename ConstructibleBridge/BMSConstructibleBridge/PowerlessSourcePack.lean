import BMSConstructibleBridge.PowerlessSourceWitnessDomain
import BMSConstructibleBridge.PowerlessStageGraphClosure

/-!
# 原公式两个输入的实际有序对编码

只合并两个输入，输出见证和其余自由参数保持不变。
有序对存在性及极限层闭包由现有集合构造给出；
坐标唯一性保证解码不会把原请求换成另一个请求。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourcePack

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def binding_m {Γ : SortContext ℒ} :
    Substitution ℒ [] (.set :: .set :: .set :: Γ) [.set, .set] (.set :: .set :: Γ) :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => .fvar .here
    | .there .here => .bvar (.there .here)
    | .there (.there .here) => .bvar .here
    | .there (.there (.there v)) => .fvar (.there (.there v)))

theorem binding_formula_l {Γ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ)) (η : Env ℳ [] Γ)
    (p y x z : carrier_l ℳ) :
    (φ.substitute binding_m).satisfies
      ((((η.pushFree p).pushFree y).pushBound x).pushBound z) ↔
        φ.satisfies (((η.pushFree z).pushFree x).pushFree y) := by
  rw [Formula.satisfies_substitute]
  apply Iff.of_eq
  congr 1
  apply Env.ext
  · intro _ v
    nomatch v
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v => cases v <;> rfl

def pair_m {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Γ)) :
    Formula ℒ [] (.set :: .set :: Γ) :=
  .existsE .set (.existsE .set (.conj
    (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.fvar (.there .here)))
    (φ.substitute binding_m)))

theorem formula_l {Γ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ)) (η : Env ℳ [] Γ) (p y : carrier_l ℳ) :
    (pair_m φ).satisfies ((η.pushFree p).pushFree y) ↔
      ∃ x z, ordered_l x z p ∧ φ.satisfies (((η.pushFree z).pushFree x).pushFree y) := by
  simp only [pair_m, Formula.satisfies, ordered_formula_l, binding_formula_l]
  rfl

theorem pair_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) {Γ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ)) (η : Env ℳ [] Γ)
    {p x z : carrier_l ℳ} (hp : ordered_l x z p) (y : carrier_l ℳ) :
    (pair_m φ).satisfies ((η.pushFree p).pushFree y) ↔
      φ.satisfies (((η.pushFree z).pushFree x).pushFree y) := by
  rw [formula_l]
  constructor
  · rintro ⟨a, b, hab, hφ⟩
    obtain ⟨rfl, rfl⟩ := (PowerlessBasic.ordered_eq_l hℳ hab hp).mp rfl
    exact hφ
  · intro hφ
    exact ⟨x, z, hp, hφ⟩

/-- 任意对封闭集合的单请求闭包传输为两个输入的闭包。 -/
theorem closure_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) {Γ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ)) (η : Env ℳ [] Γ)
    (P : carrier_l ℳ → Prop) (A : carrier_l ℳ)
    (hA : ∀ a b p, member_l ℳ a A → member_l ℳ b A → ordered_l a b p → member_l ℳ p A)
    (h : ∀ p, member_l ℳ p A →
      (∃ y, P y ∧ (pair_m φ).satisfies ((η.pushFree p).pushFree y)) →
        ∃ y, member_l ℳ y A ∧ (pair_m φ).satisfies ((η.pushFree p).pushFree y)) :
    ∀ x z, member_l ℳ x A → member_l ℳ z A →
      (∃ y, P y ∧ φ.satisfies (((η.pushFree z).pushFree x).pushFree y)) →
        ∃ y, member_l ℳ y A ∧ φ.satisfies (((η.pushFree z).pushFree x).pushFree y) := by
  rintro x z hx hz ⟨y, hy, hφ⟩
  obtain ⟨p, hp⟩ := PowerlessBasic.ordered_exists_l hℳ x z
  obtain ⟨v, hv, hψ⟩ := h p (hA x z p hx hz hp) ⟨y, hy, (pair_l hℳ φ η hp y).mpr hφ⟩
  exact ⟨v, hv, (pair_l hℳ φ η hp v).mp hψ⟩

/-- 实际更高极限层对两个输入的层次内见证关闭，不假设参数码存在。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) (α : carrier_l ℳ)
    (hω : omega_l (ω.eval (PowerlessComprehension.env_l η)))
    (ht : PowerlessEvaluationTags.tags_l (e.eval (PowerlessComprehension.env_l η))
      (t₁.eval (PowerlessComprehension.env_l η)) (t₂.eval (PowerlessComprehension.env_l η))
      (t₃.eval (PowerlessComprehension.env_l η)))
    (hT : PowerlessTriangular.triangular_l (ω.eval (PowerlessComprehension.env_l η))
      (e.eval (PowerlessComprehension.env_l η)) (T.eval (PowerlessComprehension.env_l η)))
    (hα : PowerlessOrdinal.ordinal_l α) :
    ∃ δ U, PowerlessStagePair.limit_l δ ∧ member_l ℳ α δ ∧
      stage_l (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
        (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
        (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) δ U ∧
      ∀ x z, member_l ℳ x U → member_l ℳ z U →
        (∃ y, PowerlessSourceWitnessDomain.domain_l
          (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
          (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
          (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) y ∧
          φ.satisfies ((((PowerlessComprehension.env_l η).pushFree z).pushFree x).pushFree y)) →
        ∃ y, member_l ℳ y U ∧
          φ.satisfies ((((PowerlessComprehension.env_l η).pushFree z).pushFree x).pushFree y) := by
  let ρ := PowerlessComprehension.env_l η
  obtain ⟨δ, U, hδ, hαδ, hU, h⟩ := PowerlessSourceWitnessDomain.exists_l hℳ (pair_m φ) η
    ω e T t₁ t₂ t₃ α hω ht.1 hα
  exact ⟨δ, U, hδ, hαδ, hU, closure_l hℳ φ ρ _ U
    (fun a b p ha hb hp => PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hU hδ ha hb hp) h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourcePack
