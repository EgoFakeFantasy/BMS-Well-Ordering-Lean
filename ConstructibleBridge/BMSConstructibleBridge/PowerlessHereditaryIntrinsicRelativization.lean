import BMSConstructibleBridge.PowerlessHereditaryClassInternals
import BMSConstructibleBridge.PowerlessHereditaryStructure

/-! # 在实际 Class 中表达遗传域的逐公式真值

纯隶属 ℒ，背景原 Z₂。遗传谓词采用 Class 内的可数传递包络公式，
而非把 raw Class 定义再次搬进自身。逐公式语义对应使用实际
Hereditary 子模型，允许非标准内部 ω，不假定两种模型真值自动相同。

此翻译是后续原分离模式的中间工具；它本身不是完整源理论或最终
固定高度 BMS 良序的对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryIntrinsicRelativization

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l
  PowerlessHereditaryStructure.structure_l PowerlessHereditaryStructure.type_l

universe u

def formula_m {Γ Δ : SortContext ℒ} : Formula ℒ Γ Δ → Formula ℒ Γ Δ
  | .falsum => .falsum
  | .truth => .truth
  | .rel r a => .rel r a
  | .equal s t => .equal s t
  | .neg φ => .neg (formula_m φ)
  | .conj φ ψ => .conj (formula_m φ) (formula_m ψ)
  | .disj φ ψ => .disj (formula_m φ) (formula_m ψ)
  | .imp φ ψ => .imp (formula_m φ) (formula_m ψ)
  | .iff φ ψ => .iff (formula_m φ) (formula_m ψ)
  | .forallE .set φ => .forallE .set (.imp
      (PowerlessHereditaryClassInternals.envelope_m (.bvar .here)) (formula_m φ))
  | .existsE .set φ => .existsE .set (.conj
      (PowerlessHereditaryClassInternals.envelope_m (.bvar .here)) (formula_m φ))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "𝒩₁" => PowerlessHereditaryStructure.structure_l hℳ B hBase

include hBase in
def lift_l (x : PowerlessHereditaryStructure.type_l hℳ B) :
    PowerlessRelativeClassStructure.type_l hℳ B :=
  ⟨x.val, PowerlessHereditaryClass.contained_l hℳ hBase x.property⟩

def env_l {Γ Δ : SortContext ℒ} (η : Env 𝒩₁ Γ Δ) : Env 𝒩₀ Γ Δ where
  boundVal {s} v := match s with | .set => lift_l (hBase := hBase) (η.boundVal v)
  freeVal {s} v := match s with | .set => lift_l (hBase := hBase) (η.freeVal v)

theorem term_l {Γ Δ : SortContext ℒ} (η : Env 𝒩₁ Γ Δ) (t : Term ℒ Γ Δ .set) :
    t.eval (env_l η) = lift_l (hBase := hBase) (t.eval η) := by
  match t with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app f _ => nomatch f

theorem push_l {Γ Δ : SortContext ℒ} (η : Env 𝒩₁ Γ Δ)
    (x : PowerlessHereditaryStructure.type_l hℳ B) :
    env_l (η.pushBound (sort := SetTheory.SetSort.set) x) =
      (env_l η).pushBound (sort := SetTheory.SetSort.set) (lift_l (hBase := hBase) x) := by
  apply Env.ext
  · intro s v; cases s; cases v <;> rfl
  · intro s v; cases s; rfl

theorem predicate_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒩₀ Γ Δ)
    (t : Term ℒ Γ Δ .set) :
    (PowerlessHereditaryClassInternals.envelope_m t).satisfies η ↔
      PowerlessHereditaryClass.member_l hℳ B (t.eval η).val :=
  (PowerlessHereditaryClassInternals.envelope_formula_l η t).trans
    (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) (t.eval η)).symm

theorem formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (η : Env 𝒩₁ Γ Δ) :
    (formula_m φ).satisfies (env_l η) ↔ φ.satisfies η := by
  match φ with
  | .falsum => rfl
  | .truth => rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
      change mem_l hℳ (s.eval (env_l η)).val (t.eval (env_l η)).val ↔
        mem_l hℳ (s.eval η).val (t.eval η).val
      rw [term_l, term_l]
      rfl
  | .equal (sort := SetTheory.SetSort.set) s t =>
      change s.eval (env_l η) = t.eval (env_l η) ↔ s.eval η = t.eval η
      rw [term_l, term_l]
      exact ⟨fun h => Subtype.ext (show (s.eval η).val = (t.eval η).val from
          congrArg (fun x : PowerlessRelativeClassStructure.type_l hℳ B => x.val) h),
        fun h => congrArg (lift_l (hBase := hBase)) h⟩
  | .neg φ => exact not_congr (formula_l φ η)
  | .conj φ ψ => exact and_congr (formula_l φ η) (formula_l ψ η)
  | .disj φ ψ => exact or_congr (formula_l φ η) (formula_l ψ η)
  | .imp φ ψ => exact imp_congr (formula_l φ η) (formula_l ψ η)
  | .iff φ ψ => exact iff_congr (formula_l φ η) (formula_l ψ η)
  | .forallE .set φ =>
      change (∀ x : PowerlessRelativeClassStructure.type_l hℳ B,
        (PowerlessHereditaryClassInternals.envelope_m (.bvar .here)).satisfies
          ((env_l η).pushBound x) →
        (formula_m φ).satisfies ((env_l η).pushBound x)) ↔
        ∀ x : PowerlessHereditaryStructure.type_l hℳ B, φ.satisfies (η.pushBound x)
      have h (x : PowerlessHereditaryStructure.type_l hℳ B) := formula_l φ (η.pushBound x)
      simp only [push_l] at h
      constructor
      · intro hφ x
        exact (h x).mp (hφ (lift_l (hBase := hBase) x)
          ((predicate_formula_l _ (.bvar .here)).mpr x.property))
      · intro hφ x hx
        let y : PowerlessHereditaryStructure.type_l hℳ B :=
          ⟨x.val, (predicate_formula_l _ (.bvar .here)).mp hx⟩
        have hxy : lift_l (hBase := hBase) y = x := Subtype.ext rfl
        exact hxy ▸ (h y).mpr (hφ y)
  | .existsE .set φ =>
      change (∃ x : PowerlessRelativeClassStructure.type_l hℳ B,
        (PowerlessHereditaryClassInternals.envelope_m (.bvar .here)).satisfies
          ((env_l η).pushBound x) ∧
        (formula_m φ).satisfies ((env_l η).pushBound x)) ↔
        ∃ x : PowerlessHereditaryStructure.type_l hℳ B, φ.satisfies (η.pushBound x)
      have h (x : PowerlessHereditaryStructure.type_l hℳ B) := formula_l φ (η.pushBound x)
      simp only [push_l] at h
      constructor
      · rintro ⟨x, hx, hφ⟩
        let y : PowerlessHereditaryStructure.type_l hℳ B :=
          ⟨x.val, (predicate_formula_l _ (.bvar .here)).mp hx⟩
        have hxy : lift_l (hBase := hBase) y = x := Subtype.ext rfl
        exact ⟨y, (h y).mp (hxy.symm ▸ hφ)⟩
      · rintro ⟨x, hx⟩
        exact ⟨lift_l (hBase := hBase) x,
          (predicate_formula_l _ (.bvar .here)).mpr x.property, (h x).mpr hx⟩

#print axioms predicate_formula_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryIntrinsicRelativization
