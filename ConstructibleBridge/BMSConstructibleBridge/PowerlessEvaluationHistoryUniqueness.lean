import BMSConstructibleBridge.PowerlessEvaluationFiniteHistory
import BMSConstructibleBridge.PowerlessRelativeLimitEvaluationStep
import BMSConstructibleBridge.SecondOrderSeparationAxiom

/-! # 原 Z₂ 中原严格前史求值的唯一性

分离共同定义域上的分歧集合，用原商正则性取得一个没有更早分歧的索引。
该点两份精确前史相同，原求值列的外延唯一性排除分歧。定义域可以不是
自然数初段；不把原商正则性替换为宿主良基性，也不要求 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationHistoryUniqueness

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def difference_m : Formula ℒ [] [.set, .set, .set] :=
  let k : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let F : Term ℒ [] [.set, .set, .set] .set := .fvar (.there .here)
  let G : Term ℒ [] [.set, .set, .set] .set := .fvar (.there (.there .here))
  .existsE .set <| .existsE .set <| .conj
    (SecondOrderObjectSyntax.value_m (up (up F)) (up (up k)) (.bvar (.there .here))) <|
    .conj (SecondOrderObjectSyntax.value_m (up (up G)) (up (up k)) (.bvar .here))
      (.neg (.equal (.bvar (.there .here)) (.bvar .here)))

def difference_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (F G k : carrier_l 𝒩) : Prop :=
  ∃ Y Z, value_l (ℳ := 𝒩) F k Y ∧ value_l (ℳ := 𝒩) G k Z ∧ Y ≠ Z

theorem difference_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (F G k : carrier_l 𝒩) :
    difference_m.satisfies (((Env.empty.pushFree G).pushFree F).pushFree k) ↔ difference_l F G k := by
  simp only [difference_m, difference_l, Formula.satisfies, value_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem value_agrees_l {F G n C D x : type_l hℳ}
    (hF : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) F n C)
    (hG : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) G n D)
    (h : ¬ difference_l (𝒩 := SecondOrderQuotient.structure_l hℳ) F G x) (Y : type_l hℳ) :
    value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F x Y ↔
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G x Y := by
  constructor
  · intro hY
    obtain ⟨Z, hZ, _⟩ := hG.2 x (SecondOrderFunctionProperties.value_mem_l hℳ hF hY).1
    have hYZ : Y = Z := by
      by_contra hYZ
      exact h ⟨Y, Z, hY, hZ.2, hYZ⟩
    exact hYZ.symm ▸ hZ.2
  · intro hY
    obtain ⟨Z, hZ, _⟩ := hF.2 x (SecondOrderFunctionProperties.value_mem_l hℳ hG hY).1
    have hZY : Z = Y := by
      by_contra hZY
      exact h ⟨Z, Y, hZ.2, hY, hZY⟩
    exact hZY ▸ hZ.2

theorem unique_l {ω e T A t₁ t₂ t₃ S F G n : type_l hℳ}
    (hF : PowerlessEvaluationPrefix.prefix_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω e T A t₁ t₂ t₃ S F n)
    (hG : PowerlessEvaluationPrefix.prefix_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω e T A t₁ t₂ t₃ S G n) : F = G := by
  obtain ⟨C, hF, hFStep⟩ := hF
  obtain ⟨D, hG, hGStep⟩ := hG
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set] := (Env.empty.pushFree G).pushFree F
  obtain ⟨P, hP⟩ := (SecondOrderSeparationAxiom.schema_l hℳ difference_m η).mp
    (SecondOrderSeparationAxiom.models_l hℳ difference_m η) n
  have hRead (k : type_l hℳ) : mem_l hℳ k P ↔ mem_l hℳ k n ∧
      difference_l (𝒩 := SecondOrderQuotient.structure_l hℳ) F G k :=
    (hP k).trans (and_congr Iff.rfl
      (difference_formula_l (𝒩 := SecondOrderQuotient.structure_l hℳ) F G k))
  have hEmpty (k : type_l hℳ) : ¬ mem_l hℳ k P := by
    intro hkP
    have hFoundation := SecondOrderFoundation.models_l hℳ
    change ∀ P : type_l hℳ, (∃ k, mem_l hℳ k P) → ∃ k, mem_l hℳ k P ∧
      ∀ x, mem_l hℳ x k → ¬ mem_l hℳ x P at hFoundation
    obtain ⟨a, haP, hMinimal⟩ := hFoundation P ⟨k, hkP⟩
    obtain ⟨_, Y, Z, hY, hZ, hYZ⟩ := (hRead a).mp haP
    have hSame (x : type_l hℳ) (hx : mem_l hℳ x a) (W : type_l hℳ) :
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F x W ↔
          value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G x W := by
      apply value_agrees_l hF hG
      rintro ⟨V, W, hFV, hGW, hVW⟩
      have hxN := (SecondOrderFunctionProperties.value_mem_l hℳ hF hFV).1
      exact hMinimal x hx ((hRead x).mpr ⟨hxN, V, W, hFV, hGW, hVW⟩)
    obtain ⟨H, hHistoryF, hStepY⟩ := hFStep a Y hY
    obtain ⟨J, hHistoryG, hStepZ⟩ := hGStep a Z hZ
    have hHistoryG' := (PowerlessRelativeLimitHistory.congr_l hSame).mp hHistoryF
    have hHJ := PowerlessRelativeLimitHistory.unique_l hHistoryG' hHistoryG
    exact hYZ (PowerlessRelativeLimitEvaluationStep.unique_l (hHJ ▸ hStepY) hStepZ)
  apply PowerlessBMSQuotientRecursion.map_ext_l (hM := hℳ) hF hG
  intro x Y
  apply value_agrees_l hF hG
  rintro ⟨V, W, hFV, hGW, hVW⟩
  exact hEmpty x ((hRead x).mpr ⟨(SecondOrderFunctionProperties.value_mem_l hℳ hF hFV).1,
    V, W, hFV, hGW, hVW⟩)

def schema_m {Δ : SortContext ℒ} (C D ω e T A S t₁ t₂ t₃ F G n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessEvaluationFiniteHistory.formula_m C ω e T A t₁ t₂ t₃ S F n) <|
    .imp (PowerlessEvaluationFiniteHistory.formula_m D ω e T A t₁ t₂ t₃ S G n) (.equal F G)

def sentence_m {Δ : SortContext ℒ} (C D ω e T A S t₁ t₂ t₃ F G n : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m C D ω e T A S t₁ t₂ t₃ F G n)

theorem derives_m {Δ : SortContext ℒ} (C D ω e T A S t₁ t₂ t₃ F G n : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m C D ω e T A S t₁ t₂ t₃ F G n)) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hF hG
  exact unique_l (PowerlessEvaluationFiniteHistory.original_l
    ((PowerlessEvaluationFiniteHistory.formula_l η C ω e T A t₁ t₂ t₃ S F n).mp hF))
    (PowerlessEvaluationFiniteHistory.original_l
      ((PowerlessEvaluationFiniteHistory.formula_l η D ω e T A t₁ t₂ t₃ S G n).mp hG))

#print axioms unique_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationHistoryUniqueness
