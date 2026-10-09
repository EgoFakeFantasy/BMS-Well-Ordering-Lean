import BMSConstructibleBridge.PowerlessRelativeLimitHistory
import BMSConstructibleBridge.PowerlessPairBounded

/-! # 精确前史的纯 Δ₀ 检查

显式要求 H⊆F，并在原图 F 中筛选首坐标属于 n、次坐标属于陪域 C 的对。
由原商坐标唯一性及原图的陪域界，得到原无界前史关系的双向等价。
没有把逐值相同误当作集合成员相同；不要求 H、F 已属于相对类。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHistoryBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (H F n C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ := .conj
  (membershipLevyBound.boundedForall H (SecondOrderObjectSyntax.member_m (.bvar .here) (up F)))
  (membershipLevyBound.boundedForall F <| .iff
    (SecondOrderObjectSyntax.member_m (.bvar .here) (up H)) <|
    membershipLevyBound.boundedExists (up n) <|
      membershipLevyBound.boundedExists (up (up C)) <|
        PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here))))

theorem delta_l {Γ Δ : SortContext ℒ} (H F n C : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m H F n C) :=
  .conj (.bounded_forall H (.rel _ _))
    (.bounded_forall F (.iff (.rel _ _) (.bounded_exists (up n)
      (.bounded_exists (up (up C)) (PowerlessPairBounded.ordered_delta_l _ _ _)))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (H F n C : carrier_l 𝒩) : Prop :=
  (∀ p, member_l 𝒩 p H → member_l 𝒩 p F) ∧ ∀ p, member_l 𝒩 p F →
    (member_l 𝒩 p H ↔ ∃ x, member_l 𝒩 x n ∧ ∃ y, member_l 𝒩 y C ∧ ordered_l (ℳ := 𝒩) x y p)

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (H F n C : Term ℒ Γ Δ .set) :
    (formula_m H F n C).satisfies η ↔ holds_l (H.eval η) (F.eval η) (n.eval η) (C.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessPairBounded.ordered_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem history_iff_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {H F n A C : type_l hℳ}
    (hF : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) F A C) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) H F n C ↔
      PowerlessOrdinalRecursion.history_l (ℳ := SecondOrderQuotient.structure_l hℳ) H F n := by
  constructor
  · rintro ⟨hSubset, hRead⟩ p
    constructor
    · intro hp
      have hpF := hSubset p hp
      obtain ⟨x, hx, y, _, hPair⟩ := (hRead p hpF).mp hp
      exact ⟨x, y, hPair, hx, p, hpF, hPair⟩
    · rintro ⟨x, y, hPair, hx, hValue⟩
      obtain ⟨q, hq, hPair'⟩ := hValue
      have hpF := (SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair) ▸ hq
      have hy := (SecondOrderFunctionProperties.value_mem_l hℳ hF ⟨p, hpF, hPair⟩).2
      exact (hRead p hpF).mpr ⟨x, hx, y, hy, hPair⟩
  · intro hHistory
    constructor
    · intro p hp
      obtain ⟨_, _, hPair, _, q, hq, hPair'⟩ := (hHistory p).mp hp
      exact (SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair) ▸ hq
    · intro p hpF
      constructor
      · intro hp
        obtain ⟨x, y, hPair, hx, hValue⟩ := (hHistory p).mp hp
        exact ⟨x, hx, y, (SecondOrderFunctionProperties.value_mem_l hℳ hF hValue).2, hPair⟩
      · rintro ⟨x, hx, y, _, hPair⟩
        exact (hHistory p).mpr ⟨x, y, hPair, hx, p, hpF, hPair⟩

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let H : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let F : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let n : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let A : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let C : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  .imp (SecondOrderObjectSyntax.map_m F A C) <|
    .iff (formula_m H F n C) (PowerlessRelativeLimitHistory.formula_m H F n)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hF
  have hF' := (map_formula_l η _ _ _).mp hF
  exact (formula_l η _ _ _ _).trans
    ((history_iff_l hℳ hF').trans (PowerlessRelativeLimitHistory.formula_l η _ _ _).symm)

#print axioms delta_l
#print axioms history_iff_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHistoryBounded
