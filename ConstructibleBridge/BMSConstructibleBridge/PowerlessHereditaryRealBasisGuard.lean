import BMSConstructibleBridge.PowerlessHereditaryRealBasis
import BMSConstructibleBridge.PowerlessHereditaryAmbientBaseGuard

/-! # 每个实际实数参数的遗传基底与环境初始良序

纯隶属 ℒ，背景原 Z₂。给定实际 R⊆ω，构造精确 B=ω∪{R}，
并构造实际遗传初始良序图 P₀。传递性、非空性、类内枚举及整张
良序图资格均在证明内消去，不把它们留给固定高度候选的调用端。

公开出口为原核 Derives；后续原算子呈现、层次与下降仍须接线。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRealBasisGuard

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {ω R : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω) (hR : ∀ x, mem_l hℳ x R → mem_l hℳ x ω) :
    ∃ B P₀, (∀ x, mem_l hℳ x B ↔ mem_l hℳ x ω ∨ x = R) ∧
      PowerlessHereditaryClass.member_l hℳ B R ∧
        PowerlessHereditaryClass.member_l hℳ B ω ∧
          PowerlessHereditaryClass.member_l hℳ B B ∧
            PowerlessHereditaryClass.member_l hℳ B P₀ ∧
              SecondOrderCanonicalLevelDerives.guard_l B P₀ := by
  obtain ⟨B, hSpec, hRHC, hωHC, hBHC⟩ :=
    PowerlessHereditaryRealBasis.coverage_l hℳ ω R hω hR
  have hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B := by
    intro x hx y hy
    apply (hSpec y).mpr
    rcases (hSpec x).mp hx with hxω | rfl
    · exact Or.inl (SecondOrderOmegaTransitive.member_l hℳ hω hxω hy)
    · exact Or.inl (hR y hy)
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  obtain ⟨P₀, hP₀, hGuard⟩ := PowerlessHereditaryAmbientBaseGuard.exists_l K hBase hω hBHC
    ⟨R, (hSpec R).mpr (Or.inr rfl)⟩
  exact ⟨B, P₀, hSpec, hRHC, hωHC, hBHC, hP₀, hGuard⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def conclusion_m {Γ Δ : SortContext ℒ} (ω R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <|
    let B := .bvar (.there .here)
    let P₀ := .bvar .here
    .conj (PowerlessRealSeed.spec_m (up₂ ω) (up₂ R) B) <|
      .conj (PowerlessHereditaryClass.formula_m B (up₂ R)) <|
        .conj (PowerlessHereditaryClass.formula_m B (up₂ ω)) <|
          .conj (PowerlessHereditaryClass.formula_m B B) <|
            .conj (PowerlessHereditaryClass.formula_m B P₀)
              (SecondOrderCanonicalLevelDerives.guard_m B P₀)

def schema_m {Δ : SortContext ℒ} (ω R : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (ThirdOrderTheory.subset_m R ω) (conclusion_m ω R)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω R : Term ℒ [] Δ .set) :
    (Metatheory.Formula.forall_close (schema_m ω R)).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, conclusion_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    ThirdOrderSemantics.subset_formula_l, PowerlessRealSeed.spec_formula_l,
    PowerlessHereditaryClass.formula_l K, SecondOrderCanonicalLevelDerives.guard_formula_l,
    up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hω hR
  exact exists_l h𝒩 hω hR

theorem derives_m {Δ : SortContext ℒ} (ω R : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (Metatheory.Formula.forall_close (schema_m ω R))) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 ω R)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRealBasisGuard
