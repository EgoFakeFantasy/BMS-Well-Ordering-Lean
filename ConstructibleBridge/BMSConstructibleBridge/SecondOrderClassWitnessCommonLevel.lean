import BMSConstructibleBridge.SecondOrderCanonicalHereditaryCollection
import BMSConstructibleBridge.SecondOrderCodedOrdinalFamilyBound
import BMSConstructibleBridge.PowerlessHereditaryOrdinalCountability
import BMSConstructibleBridge.PowerlessRelativeWitnessLeastStage
import BMSConstructibleBridge.PowerlessSourceOpening

/-! # 全类可数分支中的实际见证共同层

对每个内部自然数的类内见证，取同一实际请求的最小出现阶段。
全类可数条件使这些阶段具有遗传包络，从而可由已证规范族构造
精确收集，再取严格共同序数界。输出层包含每个请求的某个见证；
不假定源 Collection，也不声称该层已经反射全部所需公式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderClassWitnessCommonLevel

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeHierarchySemantics (level_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 阶段首槽、原输入次槽；原请求及其参数未被替换为宿主谓词。 -/
def rank_request_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: .set :: Δ) :=
  PowerlessSourceOpening.form_m
    (PowerlessRelativeWitnessLeastStage.rank_m φ (B.weakenFree SetTheory.SetSort.set)
      (.bvar (.here : Variable ([.set] : SortContext ℒ) .set)))

theorem rank_request_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B : Term ℒ [] Δ .set) (x a : SecondOrderQuotient.type_l hℳ) :
    (rank_request_m φ B).satisfies ((η.pushFree x).pushFree a) ↔
      PowerlessRelativeWitnessLeastStage.rank_l φ (η.pushFree x) (B.eval η) a := by
  have hEnv : PowerlessSourceOpening.env_l (η.pushFree (sort := SetTheory.SetSort.set) x) = η.pushFree x := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v
      cases s
      rfl
  have hOpen := PowerlessSourceOpening.witness_l
    (PowerlessRelativeWitnessLeastStage.rank_m φ (B.weakenFree SetTheory.SetSort.set)
      (.bvar (.here : Variable ([.set] : SortContext ℒ) .set))) (η.pushFree x) a
  rw [hEnv] at hOpen
  refine hOpen.trans ?_
  have hSlot : ((η.pushFree (sort := SetTheory.SetSort.set) x).pushBound a).boundVal
      (.here : Variable ([.set] : SortContext ℒ) .set) = a := rfl
  simpa only [PowerlessBMSQuotientSubsetImageDerives.parameters_pushBound_l,
    PowerlessBMSQuotientSubsetImageDerives.parameters_empty_l, Term.eval_weakenFree, Term.eval,
    hSlot] using
    PowerlessRelativeWitnessLeastStage.rank_formula_l K φ ((η.pushFree x).pushBound a)
      (B.weakenFree SetTheory.SetSort.set) (.bvar .here)

theorem exists_l (K : source_coding_l hℳ) {t₁ t₂ t₃ Pair Valid P₀ S : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B : Term ℒ [] Δ .set) (hGuard : SecondOrderCanonicalLevelDerives.guard_l (B.eval η) P₀)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hAll : ∀ a, SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a →
      PowerlessRelativeOrdinalCutoff.countable_l (B.eval η) K.omega a)
    (hSome : ∀ x, mem_l hℳ x K.omega → ∃ y,
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y ∧ φ.satisfies ((η.pushFree x).pushFree y)) :
    ∃ δ L : SecondOrderQuotient.type_l hℳ,
      SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) δ ∧
      PowerlessHereditaryClass.member_l hℳ (B.eval η) δ ∧ level_l hℳ (B.eval η) δ L ∧
      ∀ x, mem_l hℳ x K.omega → ∃ y, mem_l hℳ y L ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  have hBase x hx y hy := hGuard.2.1 x y hx hy
  have hRank (x : SecondOrderQuotient.type_l hℳ) (hx : mem_l hℳ x K.omega) : ∃ a,
      PowerlessHereditaryClass.member_l hℳ (B.eval η) a ∧
        (rank_request_m φ B).satisfies ((η.pushFree x).pushFree a) := by
    have hSome' : ∃ y, PowerlessRelativeClassCorrespondence.member_l hℳ
        ((B.weakenFree SetTheory.SetSort.set).eval (η.pushFree x)) y ∧
        φ.satisfies ((η.pushFree x).pushFree y) := by
      simpa only [Term.eval_weakenFree] using hSome x hx
    obtain ⟨a, ha⟩ := PowerlessRelativeWitnessLeastStage.exists_l K φ (η.pushFree x)
      (B.weakenFree SetTheory.SetSort.set) hSome'
    simp only [Term.eval_weakenFree] at ha
    have haOrd := PowerlessRelativeWitnessLeastStage.ordinal_l ha.1
    exact ⟨a, (PowerlessHereditaryOrdinalCountability.ordinal_iff_l (hBase := hBase) K K.omega_spec haOrd).mp
      (hAll a haOrd), (rank_request_formula_l K φ η B x a).mpr ha⟩
  obtain ⟨C, hSound, hCover⟩ := SecondOrderCanonicalHereditaryCollection.range_l K hCoding hGuard hS
    (rank_request_m φ B) η hRank
  have hCOrd (a : SecondOrderQuotient.type_l hℳ) (ha : mem_l hℳ a C) :
      SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a := by
    obtain ⟨n, _, hRequest⟩ := hSound a ha
    exact PowerlessRelativeWitnessLeastStage.ordinal_l
      ((rank_request_formula_l K φ η B (numberCode_l K n).val a).mp hRequest).1
  obtain ⟨δ, hδOrd, hBound⟩ := SecondOrderCodedOrdinalFamilyBound.set_bound_l hCOrd
  obtain ⟨L, hL⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hδOrd
  refine ⟨δ, L, hδOrd,
    (PowerlessHereditaryOrdinalCountability.ordinal_iff_l (hBase := hBase) K K.omega_spec hδOrd).mp
      (hAll δ hδOrd), hL, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x, hx⟩
  have hn' : (numberCode_l K n).val = x := congrArg Subtype.val hn
  obtain ⟨a, haC, _, hRequest⟩ := hCover n
  have ha := (rank_request_formula_l K φ η B (numberCode_l K n).val a).mp hRequest
  rw [hn'] at ha
  obtain ⟨D, hD, y, hyD, hφ⟩ := ha.1
  exact ⟨y, PowerlessRelativeLevelClosure.subset_l hℳ hBase (hBound a haC) hD hL y hyD, hφ⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderClassWitnessCommonLevel
