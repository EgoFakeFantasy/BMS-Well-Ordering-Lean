import BMSConstructibleBridge.PowerlessClassProgramDefinableDiagram

/-! # 实际原程序分离取得同一个规范数码图的 Class 资格

純隶属 ℒ，背景原 Z₂。由真实分离构造图，再用完整求值同值认同
原 raw 规范图 A；不从逐点输出资格推断无限图存在。
原构造守卫与求值对应仍显式保留，后者由同一数码 AST 读数消去；
本模块为语义接线，最终对象句的可推导性不能仅由它冒称完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramSameDiagram

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderCanonicalLevelDerives (guard_l)
open PowerlessDefinableMembershipDiagram (spec_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

theorem class_l (K : source_coding_l hℳ) {Δ Θ Λ : SortContext ℒ}
    (η : Env 𝒱 [] Δ)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D : Term ℒ [] Δ .set)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K (r₁.eval η) (r₂.eval η)
      (r₃.eval η) (Pair.eval η) (Valid.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
    (hGuard : guard_l (B.eval η) (P₀.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (ω.eval η))
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (hG : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (G.eval η))
    (h₀ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t₀.eval η))
    (h₁ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t₁.eval η))
    (h₂ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t₂.eval η))
    (hMap : map_l (ℳ := 𝒱) (G.eval η) (ω.eval η) (C.eval η))
    (hOnto : ∀ x, ε x (C.eval η) → ∃ n, ε n (ω.eval η) ∧ value_l (ℳ := 𝒱) (G.eval η) n x)
    (he : ∀ x, ¬ε x (e.eval η))
    (ha : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (ht : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hAlphabet : ∀ q, ε q (Q.eval η) ↔ PowerlessRelativeFiniteProgramAlphabet.instruction_l
      (C.eval η) (ω.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l (B.eval η) (ω.eval η) (Q.eval η) (S.eval η) (P.eval η))
    (hBC : ε (B.eval η) (C.eval η)) (hs : ε (s.eval η) (C.eval η)) (htC : ε (t.eval η) (C.eval η))
    (hst : s.eval η ≠ t.eval η)
    (hD : ∀ x, ε x (D.eval η) → ∀ z, ε z x → ε z (D.eval η))
    (hDC : ∀ x, ε x (D.eval η) → ε x (C.eval η)) (hDC₀ : ε (D.eval η) (C.eval η))
    (hBD : ε (B.eval η) (D.eval η)) (hωD : ε (ω.eval η) (D.eval η))
    (φ : Formula ℒ [] (.set :: .set :: Θ))
    (χ : Env (PowerlessRelativeClassStructure.structure_l hℳ (B.eval η)
      (fun x hx z hz => hGuard.2.1 x z hx hz)) [] Θ)
    (X : PowerlessRelativeClassStructure.type_l hℳ (B.eval η))
    (hProduct : ∀ p : PowerlessRelativeClassStructure.type_l hℳ (B.eval η),
      ε p.val X.val ↔ ∃ n m : PowerlessRelativeClassStructure.type_l hℳ (B.eval η),
        ε n.val (ω.eval η) ∧ ε m.val (ω.eval η) ∧
          ordered_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ (B.eval η)
            (fun x hx z hz => hGuard.2.1 x z hx hz)) n m p)
    (hXD : ε X.val (D.eval η)) (hParams : ∀ v : Variable Θ .set, ε (χ.freeVal v).val (D.eval η))
    (ψ : Formula ℒ [] (.set :: .set :: Λ)) (ξ : Env 𝒱 [] Λ)
    (hRead : ∀ n y : PowerlessRelativeClassStructure.type_l hℳ (B.eval η),
      ψ.satisfies ((ξ.pushFree n.val).pushFree y.val) ↔ φ.satisfies ((χ.pushFree n).pushFree y))
    (hOutputs : ∀ (n : PowerlessRelativeClassStructure.type_l hℳ (B.eval η)) y,
      ψ.satisfies ((ξ.pushFree n.val).pushFree y) →
        PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y)
    (A : SecondOrderQuotient.type_l hℳ) (hA : spec_l ψ ξ (ω.eval η) A) :
    PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) A := by
  obtain ⟨Z, hZ⟩ := PowerlessClassProgramDefinableDiagram.exists_l K η
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D
    hCoding hω hGuard hC hωC hQ hG h₀ h₁ h₂ hMap hOnto he ha ht hAlphabet
    hDomain hBC hs htC hst hD hDC hDC₀ hBD hωD φ χ X hProduct hXD hParams
  have hEqual := PowerlessRelativeClassDefinableDiagramReading.same_l
    (hBase := fun x hx z hz => hGuard.2.1 x z hx hz) φ ψ χ ξ hRead hOutputs
    ⟨ω.eval η, hωC⟩ Z A hA hZ
  exact hEqual ▸ Z.property

#print axioms class_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramSameDiagram
