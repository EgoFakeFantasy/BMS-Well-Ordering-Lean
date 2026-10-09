import BMSConstructibleBridge.PowerlessClassProgramCondensation
import BMSConstructibleBridge.PowerlessClassWholeCollapseSeparation

/-! # 实际凝聚程序消去有限反射分离的中间前提

原自由参数公式全部绑定后加入同一有限族；已有原 Z₂ 凝聚构造给
同一数码图、实际 T/H、TClass 及种子固定。原程序请求规格恢复该
绑定公式的同一闭包，再取得实际 Class 分离见证。不预供 hCapture、
同构、TClass 或真值对应。原种子枚举及构造守卫仍明确保留。
这里只分离原公式的 Class 真值；raw 求值与 Class 求值的认同须另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramSeparation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderCanonicalLevelDerives (guard_l)
open PowerlessDefinableMembershipIsomorphism (image_l)
open PowerlessRelativeFiniteProgramNumberEvaluation (number_m)
open PowerlessRelativeFiniteProgramEnumeratedCollapse (reading_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) :=
  v.weakenBound SetTheory.SetSort.set
private def parameters_m {Δ : SortContext ℒ} : VariableSubstitution ℒ [] [] Δ :=
  fun v => nomatch v

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

/-- 同一实际程序构造全部所需反射资源，不要求原复杂公式是 Δ₀。 -/
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
    (ψ : Formula ℒ [] (.set :: Θ))
    (χ : Env (PowerlessRelativeClassStructure.structure_l hℳ (B.eval η)
      (fun x hx z hz => hGuard.2.1 x z hx hz)) [] Θ)
    (X : PowerlessRelativeClassStructure.type_l hℳ (B.eval η))
    (hXD : ε X.val (D.eval η)) (hParams : ∀ v : Variable Θ .set, ε (χ.freeVal v).val (D.eval η)) :
    ∃ Y : PowerlessRelativeClassStructure.type_l hℳ (B.eval η),
      ∀ x : PowerlessRelativeClassStructure.type_l hℳ (B.eval η),
        ε x.val Y.val ↔ ε x.val X.val ∧ ψ.satisfies (χ.pushFree x) := by
  let Φ : PowerlessClassFiniteElementarity.family_m [] :=
    [Sigma.mk (.set :: Θ) (PowerlessSourceFreeBinding.formula_m ψ)]
  let Λ := PowerlessClassFiniteElementarity.requests_m (PowerlessClassProgramCondensation.family_m Φ)
  let Ψ := PowerlessClassProgramFiniteRequests.family_m Λ B parameters_m
  let φ := PowerlessClassProgramHull.operator_m Ψ ω e r₁ r₂ r₃ Pair Valid B P₀ s t
  obtain ⟨U, _hUC, hU, hUOnto, _A, T, H, _hA, _hField, _hCollapse, hIso,
      ⟨hFixed, _hFixed₀⟩, hTargetClass, _hStage⟩ :=
    PowerlessClassProgramCondensation.witnesses_l K Φ η
      ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D
      hCoding hω hGuard hC hωC hQ hG h₀ h₁ h₂ hMap hOnto he ha ht hAlphabet
      hDomain hBC hs htC hst hD hDC hDC₀ hBD hωD
  let θ := number_m φ (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂)
    (up a) (.bvar .here)
  have hImage (x : Raw) : image_l θ (η.pushFree U) (ω.eval η) x ↔
      PowerlessRelativeFiniteProgramVirtualClosure.image_l false φ η (B.eval η) (C.eval η)
        (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (P.eval η) x := by
    simpa only [image_l, θ, reading_l K, member_l, SecondOrderQuotient.structure_l,
      PowerlessRelativeFiniteProgramVirtualClosure.image_l] using
        PowerlessRelativeFiniteProgramNumberEvaluation.range_l φ η hU hUOnto x
  obtain ⟨_, hClass, _, _, _, _⟩ := PowerlessClassProgramHull.closure_l K Ψ η
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t
      hCoding hω hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC
  have hBase : ∀ x, ε x (B.eval η) → ∀ z, ε z x → ε z (B.eval η) :=
    fun x hx z hz => hGuard.2.1 x z hx hz
  have hP : ∃ x, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) x :=
    ⟨B.eval η, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  let ξ : Env (PowerlessSourceClass.structure_l (ℳ := 𝒱)
      (PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η)) hP) [] [] := Env.empty
  have hAll := PowerlessClassProgramFiniteRequests.requests_l K Λ parameters_m η
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a S P s t
      hCoding hω hGuard hC hωC hQ he ha ht hAlphabet hDomain hBC hs htC hst ξ
        (fun v => nomatch v)
  have hPredicate : (fun x : carrier_l (PowerlessSourceClass.structure_l (ℳ := 𝒱)
      (PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η)) hP) =>
        image_l θ (η.pushFree U) (ω.eval η) x.val) =
      (fun x => PowerlessClassProgramFiniteRequests.image_l Λ parameters_m η
        ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a P s t x.val) := by
    funext x
    exact propext (hImage x.val)
  rw [← hPredicate] at hAll
  have hCapture : PowerlessSourcePredicateRequests.closed_l
      (PowerlessSourceRequests.requests_m .truth (PowerlessSourceFreeBinding.formula_m ψ)) ξ
      (fun x => image_l θ (η.pushFree U) (ω.eval η) x.val) :=
    PowerlessSourcePredicateRequests.subset_l (fun q hq => List.mem_flatMap.mpr
      ⟨Sigma.mk (.set :: Θ) (PowerlessSourceFreeBinding.formula_m ψ),
        List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self), hq⟩) hAll
  exact PowerlessClassWholeCollapseSeparation.exists_l (hBase := hBase) (hP := hP)
    θ (η.pushFree U) (ω.eval η) T H (D.eval η) ψ χ X hIso hTargetClass
    (fun x hx => hClass x ((hImage x).mp hx)) hD hFixed hXD hParams hCapture

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramSeparation
