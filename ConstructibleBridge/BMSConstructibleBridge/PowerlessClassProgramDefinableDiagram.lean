import BMSConstructibleBridge.PowerlessClassProgramSeparation
import BMSConstructibleBridge.PowerlessRelativeClassRelation
import BMSConstructibleBridge.PowerlessRelativeClassDefinableDiagramReading

/-! # 实际原程序分离得到的类内数码隶属图

纯隶属 ℒ，背景原 Z₂。任意求值公式允许无界输出，只在给定
类内数码积上分离原隶属边。所用分离来自实际有限凝聚程序，
不预供反射真值、同构或 Class 图。原种子／枚举／参数界仍保留；
这一步不是最终无条件 Class 分离或 BMS 良序证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramDefinableDiagram

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
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

theorem exists_l (K : source_coding_l hℳ) {Δ Θ : SortContext ℒ}
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
    (hXD : ε X.val (D.eval η)) (hParams : ∀ v : Variable Θ .set, ε (χ.freeVal v).val (D.eval η)) :
    ∃ Z : PowerlessRelativeClassStructure.type_l hℳ (B.eval η),
      spec_l φ χ ⟨ω.eval η, hωC⟩ Z := by
  let O : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨ω.eval η, hωC⟩
  let ψ := PowerlessRelativeClassRelation.body_m (PowerlessDefinableMembershipDiagram.relation_m φ)
  let ξ := (χ.pushFree (sort := SetTheory.SetSort.set) O).pushFree (sort := SetTheory.SetSort.set) O
  have hParams' : ∀ v : Variable (.set :: .set :: Θ) .set, ε (ξ.freeVal v).val (D.eval η) := by
    intro v
    cases v with
    | here => exact hωD
    | there v => cases v with
      | here => exact hωD
      | there v => exact hParams v
  obtain ⟨Z, hZ⟩ := PowerlessClassProgramSeparation.exists_l K η
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D
    hCoding hω hGuard hC hωC hQ hG h₀ h₁ h₂ hMap hOnto he ha ht hAlphabet
    hDomain hBC hs htC hst hD hDC hDC₀ hBD hωD ψ ξ X hXD hParams'
  refine ⟨Z, fun p => ?_⟩
  have hBody := PowerlessRelativeClassRelation.body_formula_l
    (PowerlessDefinableMembershipDiagram.relation_m φ) χ O O p
  constructor
  · intro hp
    obtain ⟨_hpX, hpψ⟩ := (hZ p).mp hp
    obtain ⟨n, m, hn, hm, hPair, hEdge⟩ := hBody.mp hpψ
    exact ⟨n, m, hn, hm, (PowerlessDefinableMembershipDiagram.relation_formula_l φ χ n m).mp hEdge, hPair⟩
  · rintro ⟨n, m, hn, hm, hEdge, hPair⟩
    exact (hZ p).mpr ⟨(hProduct p).mpr ⟨n, m, hn, hm, hPair⟩,
      hBody.mpr ⟨n, m, hn, hm, hPair,
        (PowerlessDefinableMembershipDiagram.relation_formula_l φ χ n m).mpr hEdge⟩⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramDefinableDiagram
