import BMSConstructibleBridge.PowerlessClassProgramSameDiagram
import BMSConstructibleBridge.PowerlessRelativeClassProgramNumberSyntaxReading

/-! # 同一原数码求值图的实际 Class 资格

纯隶属 ℒ，背景原 Z₂。采用实际旧数码 AST 和同一 U；求值同值和
输出资格在证明内由已验证的原 AST 读数产生，不保留 hRead/hOutputs。
分离来自实际有限凝聚程序，不预供 ClassA 或完整源理论。
原求值程序参数以 ᵥ 标记，分离程序采用另一套实际种子／码域；
先固定原 U 与求值元数据，再为分离扩大种子，不要求原 U 或原
常量种子进入其自身的传递闭包。仍保留分离程序构造守卫、参数界及
原算子对应；本文件为语义接线，不宣称最终良序 Derives 已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramNumberDiagram

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderCanonicalLevelDerives (guard_l)
open PowerlessDefinableMembershipDiagram (spec_l)
open PowerlessRelativeClassProgramRequestReading (parameters_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def mapped_m {Θ Γ : SortContext ℒ} (σ : VariableSubstitution ℒ Θ [] Γ)
    (t : Term ℒ [] Θ .set) : Term ℒ [] Γ .set := t.substitute (parameters_m σ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

theorem class_l (K : source_coding_l hℳ) {Γ Θ : SortContext ℒ}
    (ζ : Env 𝒱 [] Γ)
    (σ : VariableSubstitution ℒ Θ [] Γ)
    (bᵥ Cᵥ ωᵥ Qᵥ eᵥ t₀ᵥ t₁ᵥ t₂ᵥ aᵥ : Term ℒ [] Θ .set)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ [] Γ .set)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K (r₁.eval ζ) (r₂.eval ζ)
      (r₃.eval ζ) (Pair.eval ζ) (Valid.eval ζ))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval ζ))
    (hGuard : guard_l (B.eval ζ) (P₀.eval ζ))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ζ) (C.eval ζ))
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ζ) (ω.eval ζ))
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ζ) (Q.eval ζ))
    (hG : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ζ) (G.eval ζ))
    (h₀ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ζ) (t₀.eval ζ))
    (h₁ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ζ) (t₁.eval ζ))
    (h₂ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ζ) (t₂.eval ζ))
    (hMap : map_l (ℳ := 𝒱) (G.eval ζ) (ω.eval ζ) (C.eval ζ))
    (hOnto : ∀ x, ε x (C.eval ζ) → ∃ n, ε n (ω.eval ζ) ∧ value_l (ℳ := 𝒱) (G.eval ζ) n x)
    (he : ∀ x, ¬ε x (e.eval ζ))
    (ha : PowerlessRelativeFiniteProgramStep.record_l (e.eval ζ) (e.eval ζ) (e.eval ζ) (a.eval ζ))
    (ht : t₀.eval ζ ≠ t₁.eval ζ ∧ t₀.eval ζ ≠ t₂.eval ζ ∧ t₁.eval ζ ≠ t₂.eval ζ)
    (hAlphabet : ∀ q, ε q (Q.eval ζ) ↔ PowerlessRelativeFiniteProgramAlphabet.instruction_l
      (C.eval ζ) (ω.eval ζ) (t₀.eval ζ) (t₁.eval ζ) (t₂.eval ζ) q)
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l (B.eval ζ) (ω.eval ζ) (Q.eval ζ) (S.eval ζ) (P.eval ζ))
    (hBC : ε (B.eval ζ) (C.eval ζ)) (hs : ε (s.eval ζ) (C.eval ζ)) (htC : ε (t.eval ζ) (C.eval ζ))
    (hst : s.eval ζ ≠ t.eval ζ)
    (hD : ∀ x, ε x (D.eval ζ) → ∀ z, ε z x → ε z (D.eval ζ))
    (hDC : ∀ x, ε x (D.eval ζ) → ε x (C.eval ζ)) (hDC₀ : ε (D.eval ζ) (C.eval ζ))
    (hBD : ε (B.eval ζ) (D.eval ζ)) (hωD : ε (ω.eval ζ) (D.eval ζ))
    (φ : Formula ℒ [] (.set :: .set :: Θ))
    (χ : Env (PowerlessRelativeClassStructure.structure_l hℳ (B.eval ζ)
      (fun x hx z hz => hGuard.2.1 x z hx hz)) [] Θ)
    (hσ : ∀ v : Variable Θ .set, (σ v).eval ζ = (χ.freeVal v).val)
    (ψ : Formula ℒ [] (.set :: .set :: Γ))
    (hOperator : ∀ n y : PowerlessRelativeClassStructure.type_l hℳ (B.eval ζ),
      ψ.satisfies ((ζ.pushFree n.val).pushFree y.val) ↔ φ.satisfies ((χ.pushFree n).pushFree y))
    (hb : (mapped_m σ bᵥ).eval ζ = B.eval ζ)
    (hωSame : (mapped_m σ ωᵥ).eval ζ = ω.eval ζ)
    (U : PowerlessRelativeClassStructure.type_l hℳ (B.eval ζ))
    (hUD : ε U.val (D.eval ζ))
    (X : PowerlessRelativeClassStructure.type_l hℳ (B.eval ζ))
    (hProduct : ∀ p : PowerlessRelativeClassStructure.type_l hℳ (B.eval ζ),
      ε p.val X.val ↔ ∃ n m : PowerlessRelativeClassStructure.type_l hℳ (B.eval ζ),
        ε n.val (ω.eval ζ) ∧ ε m.val (ω.eval ζ) ∧
          ordered_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ (B.eval ζ)
            (fun x hx z hz => hGuard.2.1 x z hx hz)) n m p)
    (hXD : ε X.val (D.eval ζ)) (hParams : ∀ v : Variable Θ .set, ε (χ.freeVal v).val (D.eval ζ))
    (A : SecondOrderQuotient.type_l hℳ)
    (hA : spec_l (PowerlessRelativeFiniteProgramNumberEvaluation.number_m ψ
      (up (mapped_m σ bᵥ)) (up (mapped_m σ Cᵥ)) (up (mapped_m σ ωᵥ)) (up (mapped_m σ Qᵥ))
      (up (mapped_m σ eᵥ)) (up (mapped_m σ t₀ᵥ)) (up (mapped_m σ t₁ᵥ)) (up (mapped_m σ t₂ᵥ))
      (up (mapped_m σ aᵥ)) (.bvar .here)) (ζ.pushFree U.val) ((mapped_m σ ωᵥ).eval ζ) A) :
    PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ζ) A := by
  let θ := PowerlessFiniteProgramNumberEvaluationSyntax.number_m φ
    (up bᵥ) (up Cᵥ) (up ωᵥ) (up Qᵥ) (up eᵥ) (up t₀ᵥ) (up t₁ᵥ) (up t₂ᵥ) (up aᵥ) (.bvar .here)
  let θRaw := PowerlessRelativeFiniteProgramNumberEvaluation.number_m ψ
    (up (mapped_m σ bᵥ)) (up (mapped_m σ Cᵥ)) (up (mapped_m σ ωᵥ)) (up (mapped_m σ Qᵥ))
    (up (mapped_m σ eᵥ)) (up (mapped_m σ t₀ᵥ)) (up (mapped_m σ t₁ᵥ)) (up (mapped_m σ t₂ᵥ))
    (up (mapped_m σ aᵥ)) (.bvar .here)
  have hParams' : ∀ v : Variable (.set :: Θ) .set,
      ε (((χ.pushFree U).freeVal v).val) (D.eval ζ) := by
    intro v
    cases v with
    | here => exact hUD
    | there v => exact hParams v
  have hbᵥ : (bᵥ.eval χ).val = B.eval ζ :=
    (PowerlessRelativeClassProgramExecutionReading.term_l χ ζ σ hσ bᵥ).symm.trans hb
  have hA' : spec_l θRaw (ζ.pushFree U.val) (ω.eval ζ) A := by
    rw [← hωSame]
    exact hA
  apply PowerlessClassProgramSameDiagram.class_l K ζ
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D
    hCoding hω hGuard hC hωC hQ hG h₀ h₁ h₂ hMap hOnto he ha ht hAlphabet
    hDomain hBC hs htC hst hD hDC hDC₀ hBD hωD θ (χ.pushFree U) X hProduct hXD hParams'
    θRaw (ζ.pushFree U.val) ?_ ?_ A hA'
  · intro n y
    exact (PowerlessRelativeClassProgramNumberSyntaxReading.reading_l K φ ψ χ ζ σ hσ hOperator
      bᵥ Cᵥ ωᵥ Qᵥ eᵥ t₀ᵥ t₁ᵥ t₂ᵥ aᵥ hbᵥ U n y).symm
  · intro n y hy
    exact PowerlessRelativeClassProgramNumberSyntaxReading.raw_output_class_l
      (hBase := fun x hx z hz => hGuard.2.1 x z hx hz) K ψ ζ
      (mapped_m σ bᵥ) (mapped_m σ Cᵥ) (mapped_m σ ωᵥ) (mapped_m σ Qᵥ)
      (mapped_m σ eᵥ) (mapped_m σ t₀ᵥ) (mapped_m σ t₁ᵥ) (mapped_m σ t₂ᵥ) (mapped_m σ aᵥ)
      hb U.val n.val y hy

#print axioms class_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramNumberDiagram
