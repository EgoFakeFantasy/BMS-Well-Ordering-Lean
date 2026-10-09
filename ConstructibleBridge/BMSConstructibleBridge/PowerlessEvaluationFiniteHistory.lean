import BMSConstructibleBridge.PowerlessRelativeLimitHistory
import BMSConstructibleBridge.PowerlessEvaluationPrefix
import BMSConstructibleBridge.SecondOrderNaturalCases

/-! # 原求值算子的内部有限历史与单步延拓

保留原全对象求值列和精确严格前史，另外显式固定列值域 C。新列在末端
加入时，旧索引的前史完全不变，故不需预先证明三角配数的子码界。
这一步尚未构造全部内部长度，也没有假定 C 或整类满足 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationFiniteHistory

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def trace_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (C ω e T A t₁ t₂ t₃ S F n : carrier_l 𝒩) : Prop :=
  map_l (ℳ := 𝒩) F n C ∧ ∀ k Y, value_l (ℳ := 𝒩) F k Y → ∃ H,
    PowerlessOrdinalRecursion.history_l H F k ∧ PowerlessEvaluationStep.step_l ω e T A t₁ t₂ t₃ S H k Y

def formula_m {Γ Δ : SortContext ℒ} (C ω e T A t₁ t₂ t₃ S F n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up t))
  .conj (SecondOrderObjectSyntax.map_m F n C) <| .forallE .set <| .forallE .set <|
    .imp (SecondOrderObjectSyntax.value_m (up (up F)) (.bvar (.there .here)) (.bvar .here)) <|
      .existsE .set <| .conj
        (PowerlessRelativeLimitHistory.formula_m (.bvar .here) (w F) (.bvar (.there (.there .here))))
        (PowerlessEvaluationStep.step_m (w ω) (w e) (w T) (w A) (w t₁) (w t₂) (w t₃) (w S)
          (.bvar .here) (.bvar (.there (.there .here))) (.bvar (.there .here)))

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (C ω e T A t₁ t₂ t₃ S F n : Term ℒ Γ Δ .set) :
    (formula_m C ω e T A t₁ t₂ t₃ S F n).satisfies η ↔
      trace_l (C.eval η) (ω.eval η) (e.eval η) (T.eval η) (A.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (S.eval η) (F.eval η) (n.eval η) := by
  simp only [formula_m, trace_l, Formula.satisfies, map_formula_l, value_formula_l,
    PowerlessRelativeLimitHistory.formula_l, PowerlessEvaluationStep.step_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem original_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {C ω e T A t₁ t₂ t₃ S F n : carrier_l 𝒩}
    (hF : trace_l C ω e T A t₁ t₂ t₃ S F n) :
    PowerlessEvaluationPrefix.prefix_l ω e T A t₁ t₂ t₃ S F n := ⟨C, hF⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem empty_l {C ω e T A t₁ t₂ t₃ S z : type_l hℳ}
    (hz : ∀ x, ¬ mem_l hℳ x z) :
    trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ) C ω e T A t₁ t₂ t₃ S z z := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp; exact (hz p hp).elim
  · intro x hx; exact (hz x hx).elim
  · rintro k Y ⟨p, hp, _⟩; exact (hz p hp).elim

theorem extension_l {C ω e T A t₁ t₂ t₃ S F G n m Y : type_l hℳ}
    (hF : trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ) C ω e T A t₁ t₂ t₃ S F n)
    (hG : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) G m C)
    (hm : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) n m)
    (hRead : ∀ x y, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G x y ↔
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F x y ∨ x = n ∧ y = Y)
    (hY : PowerlessEvaluationStep.step_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      ω e T A t₁ t₂ t₃ S F n Y) :
    trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ) C ω e T A t₁ t₂ t₃ S G m := by
  have hSame (k : type_l hℳ) (hk : mem_l hℳ k n ∨ k = n) (x : type_l hℳ)
      (hx : mem_l hℳ x k) (y : type_l hℳ) :
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F x y ↔
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G x y := by
    constructor
    · intro hxy; exact (hRead x y).mpr (Or.inl hxy)
    · intro hxy
      rcases (hRead x y).mp hxy with hxy | ⟨hxn, _⟩
      · exact hxy
      · subst x
        rcases hk with hk | rfl
        · exact (SecondOrderNaturalCases.asymmetry_l hℳ hk hx).elim
        · exact (SecondOrderNaturalCases.asymmetry_l hℳ hx hx).elim
  refine ⟨hG, fun k Z hZ => ?_⟩
  have hk := (hm k).mp (SecondOrderFunctionProperties.value_mem_l hℳ hG hZ).1
  rcases hk with hk | rfl
  · have hOld : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F k Z := by
      rcases (hRead k Z).mp hZ with hOld | ⟨hkn, _⟩
      · exact hOld
      · exact (SecondOrderNaturalCases.asymmetry_l hℳ (hkn ▸ hk) (hkn ▸ hk)).elim
    obtain ⟨H, hHistory, hStep⟩ := hF.2 k Z hOld
    exact ⟨H, (PowerlessRelativeLimitHistory.congr_l (hSame k (Or.inl hk))).mp hHistory, hStep⟩
  · have hZY : Z = Y := by
      rcases (hRead k Z).mp hZ with hOld | ⟨_, hZY⟩
      · have hnn := (SecondOrderFunctionProperties.value_mem_l hℳ hF.1 hOld).1
        exact (SecondOrderNaturalCases.asymmetry_l hℳ hnn hnn).elim
      · exact hZY
    subst Z
    exact ⟨F, (PowerlessRelativeLimitHistory.congr_l (hSame k (Or.inr rfl))).mp
      (PowerlessRelativeLimitHistory.self_l hF.1), hY⟩

#print axioms formula_l
#print axioms extension_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationFiniteHistory
