import BMSConstructibleBridge.PowerlessRelationalParameterReading

/-! # 求值域内的全参数量化

关闭且只关闭参数前缀，槽项和数码保持不变。成员环境以显式子类型包装
构造；往返通过有限值列完成，不抽取 Type 层选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalParameterContext

open Logic FirstOrder ThirdOrderSemantics
open _root_.YesMetaZFC.Automation
open RelationalTranslation (valuesAssignment)
open PrefixQuantification (entry_m weaken_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

def parameters_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    (slots : Variable Δ .set → Term ℒ Γ Θ .set) (ω A G c N : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  PrefixQuantification.forall_m Δ <|
    .imp (PowerlessRelationalParameterSyntax.bounded_m (fun v => entry_m v) (weaken_m Δ A))
      (PowerlessRelationalParameterReading.reading_m φ (fun v => weaken_m Δ (slots v))
        (fun v => entry_m v) (weaken_m Δ ω) (weaken_m Δ A) (weaken_m Δ G) (weaken_m Δ c) (weaken_m Δ N))

theorem parameters_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ρ : Env 𝒩 Γ Θ)
    (slots : Variable Δ .set → Term ℒ Γ Θ .set) (ω A G c N : Term ℒ Γ Θ .set)
    {D : carrier_l 𝒩} (hD : ∃ a, member_l 𝒩 a D) (hA : A.eval ρ = D) :
    (parameters_m φ slots ω A G c N).satisfies ρ ↔
      ∀ η : Env (PowerlessMemberStructure.structure_l D hD) [] Δ,
        PowerlessRelationalParameterReading.spec_l φ (PowerlessRelationalParameterSyntax.env_l ρ slots)
          (ω.eval ρ) D (G.eval ρ) (c.eval ρ) (N.eval ρ) η := by
  have hRead (xs : Values 𝒩.Carrier Δ)
      (η : Env (PowerlessMemberStructure.structure_l D hD) [] Δ)
      (hParams : ∀ v, valuesAssignment xs v = (η.freeVal v).val) :
      (PowerlessRelationalParameterReading.reading_m φ (fun v => weaken_m Δ (slots v))
        (fun v => entry_m v) (weaken_m Δ ω) (weaken_m Δ A) (weaken_m Δ G) (weaken_m Δ c) (weaken_m Δ N)).satisfies
          (PrefixQuantification.env_l ρ xs) ↔
        PowerlessRelationalParameterReading.spec_l φ (PowerlessRelationalParameterSyntax.env_l ρ slots)
          (ω.eval ρ) D (G.eval ρ) (c.eval ρ) (N.eval ρ) η := by
    have hSlots : PowerlessRelationalParameterSyntax.env_l (PrefixQuantification.env_l ρ xs)
        (fun v => weaken_m Δ (slots v)) = PowerlessRelationalParameterSyntax.env_l ρ slots := by
      apply Env.ext
      · intro s v
        nomatch v
      · intro s v
        cases s
        exact PrefixQuantification.weaken_l ρ xs (slots v)
    have h := PowerlessRelationalParameterReading.environment_formula_l φ (PrefixQuantification.env_l ρ xs)
      (fun v => weaken_m Δ (slots v)) (fun v => entry_m v)
      (weaken_m Δ ω) (weaken_m Δ A) (weaken_m Δ G) (weaken_m Δ c) (weaken_m Δ N) η
      ((PrefixQuantification.weaken_l ρ xs A).trans hA) (by
        intro v
        simpa only [PrefixQuantification.entry_l] using hParams v)
    simpa only [hSlots, PrefixQuantification.weaken_l] using h
  rw [parameters_m, PrefixQuantification.forall_formula_l]
  simp only [Formula.satisfies, PowerlessRelationalParameterSyntax.bounded_values_l,
    PrefixQuantification.entry_l, PrefixQuantification.weaken_l, hA]
  constructor
  · intro h η
    let xs := ModelClosure.valuesOfAssignment
      (ℳ := 𝒩) (fun {s} (v : Variable Δ s) => match s with | .set => (η.freeVal v).val)
    have hParams (v : Variable Δ .set) : valuesAssignment xs v = (η.freeVal v).val :=
      ModelClosure.assignment_values _ v
    apply (hRead xs η hParams).mp
    apply h xs
    intro v
    rw [hParams v]
    exact (η.freeVal v).property
  · intro h xs hxs
    let η : Env (PowerlessMemberStructure.structure_l D hD) [] Δ :=
      { boundVal := fun v => nomatch v
        freeVal := fun {s} v => match s with | .set => ⟨valuesAssignment xs v, hxs v⟩ }
    exact (hRead xs η (fun _ => rfl)).mpr (h η)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalParameterContext
