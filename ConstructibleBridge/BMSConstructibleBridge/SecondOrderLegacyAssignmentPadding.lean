import BMSConstructibleBridge.SecondOrderLegacyAssignmentReversal

/-! # 原赋值反转后的内部尾槽填充

给定默认数值 z，反转读数在目标长度 L 内保留，原长度以外的槽统一填 z。
图理解和内部有限图编码产生实际数码，不从宿主列表或外部有限性取码。
当 l < L 时，原头部前插恰好对应同一目标长度中的槽 l 更新。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyAssignmentPadding

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel SecondOrderNumbers
open SecondOrderSequenceSyntax (read_l)
open SecondOrderAssignmentSyntax (valid_l extension_l)
open SecondOrderLegacyAssignmentReversal (reversed_l reversed_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) := t.weakenBound sort_m.num

def padded_l (E : set_l ℳ) (c l L z r x : num_l ℳ) : Prop :=
  SecondOrderOrder.lt_l r L ∧
    (reversed_l E c l r x ∨ ¬SecondOrderOrder.lt_l r l ∧ x = z)

def padded_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (c l L z r x : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .conj (PrimitiveFormulas.lt_m r L) <|
    .disj (reversed_m E c l r x) (.conj (.neg (PrimitiveFormulas.lt_m r l)) (.equal x z))

theorem padded_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) (c l L z r x : Term signature_m Γ Δ .num) :
    (padded_m E c l L z r x).satisfies η ↔
      padded_l (E.eval η) (c.eval η) (l.eval η) (L.eval η) (z.eval η) (r.eval η) (x.eval η) := by
  simp only [padded_m, padded_l, Formula.satisfies, SecondOrderOrder.formula_l,
    SecondOrderLegacyAssignmentReversal.reversed_formula_l]

theorem prefix_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} {c l L z r x : num_l ℳ}
    (hLength : l = L ∨ SecondOrderOrder.lt_l l L) (hr : SecondOrderOrder.lt_l r l) :
    padded_l E c l L z r x ↔ reversed_l E c l r x := by
  have hrL : SecondOrderOrder.lt_l r L := hLength.elim (fun h => h ▸ hr)
    (fun h => SecondOrderOrder.trans_l hℳ hr h)
  simp only [padded_l, hrL, hr, not_true_eq_false, false_and, or_false, true_and]

theorem total_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} {c l L z r : num_l ℳ}
    (hc : valid_l E c l) (hr : SecondOrderOrder.lt_l r L) : ∃! x, padded_l E c l L z r x := by
  classical
  by_cases hrl : SecondOrderOrder.lt_l r l
  · obtain ⟨x, hx, hUnique⟩ := SecondOrderLegacyAssignmentReversal.total_l hℳ hc hrl
    refine ⟨x, ⟨hr, Or.inl hx⟩, ?_⟩
    intro y hy
    rcases hy.2 with hRev | hTail
    · exact hUnique y hRev
    · exact False.elim (hTail.1 hrl)
  · refine ⟨z, ⟨hr, Or.inr ⟨hrl, rfl⟩⟩, ?_⟩
    intro y hy
    rcases hy.2 with ⟨i, hi, _⟩ | hTail
    · exact False.elim (hrl (SecondOrderLegacyAssignmentReversal.bounds_l hℳ hi).2)
    · exact hTail.2

/-- 指定默认值的完整填充码；目标长度可以是任意内部数。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) {c l : num_l ℳ} (hc : valid_l E c l)
    (L z : num_l ℳ) :
    ∃ d, valid_l E d L ∧ ∀ r x, read_l E d r x ↔ padded_l E c l L z r x := by
  let φ : Formula signature_m [] [.num, .num, .set, .num, .num, .num, .num] := padded_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar .here) (.fvar (.there .here))
  let η : Env ℳ [] [.set, .num, .num, .num, .num] :=
    ((((Env.empty.pushFree z).pushFree L).pushFree l).pushFree c).pushFree E
  obtain ⟨H, hH⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl) η
  have hGraph (r x : num_l ℳ) : SecondOrderPairing.relation_l H r x ↔ padded_l E c l L z r x :=
    (hH r x).trans (padded_formula_l _ _ _ _ _ _ _ _)
  have hTotal r (hr : SecondOrderOrder.lt_l r L) : ∃! x, SecondOrderPairing.relation_l H r x := by
    obtain ⟨x, hx, hUnique⟩ := total_l hℳ hc hr
    exact ⟨x, (hGraph r x).mpr hx, fun y hy => hUnique y ((hGraph r y).mp hy)⟩
  obtain ⟨d, hd⟩ := SecondOrderSequenceCode.exists_l hℳ hE H L hTotal
  have hRead (r x : num_l ℳ) : read_l E d r x ↔ padded_l E c l L z r x := by
    refine (SecondOrderSequenceSyntax.read_eq_l hE d r x).trans
      ((hd r x).trans ((and_congr Iff.rfl (hGraph r x)).trans ?_))
    exact ⟨And.right, fun h => ⟨h.1, h⟩⟩
  refine ⟨d, ⟨?_, ?_⟩, hRead⟩
  · intro r hr
    obtain ⟨x, hx, hUnique⟩ := total_l hℳ hc hr
    exact ⟨x, (hRead r x).mpr hx, fun y hy => hUnique y ((hRead r y).mp hy)⟩
  · exact fun r x hx => ((hRead r x).mp hx).1

/-- 同一目标长度的填充把头部前插精确变成槽 l 的更新。 -/
theorem prepend_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} {c l d x L z r y : num_l ℳ}
    (hd : extension_l E c l d x) (hLength : SecondOrderOrder.lt_l l L) :
    padded_l E d (succ_l l) L z r y ↔
      (r = l ∧ y = x) ∨ r ≠ l ∧ padded_l E c l L z r y := by
  classical
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  by_cases hrl : r = l
  · subst r
    have hSucc : SecondOrderOrder.lt_l l (succ_l l) :=
      (SecondOrderNaturalGraph.lt_succ_l hℳ l l).mpr le_rfl
    have hOld : ¬reversed_l E c l l y := by
      rintro ⟨i, hi, _⟩
      exact SecondOrderOrder.irrefl_l hℳ l (SecondOrderLegacyAssignmentReversal.bounds_l hℳ hi).2
    simp only [padded_l, SecondOrderLegacyAssignmentReversal.prepend_l hℳ hd,
      hLength, hSucc, hOld, not_true_eq_false, false_and, or_false, true_and,
      ne_eq, eq_self]
  · have hLt : SecondOrderOrder.lt_l r (succ_l l) ↔ SecondOrderOrder.lt_l r l := by
      change r < succ_l l ↔ r < l
      rw [SecondOrderNaturalGraph.lt_succ_l hℳ]
      exact ⟨fun h => lt_of_le_of_ne h hrl, le_of_lt⟩
    simp only [padded_l, SecondOrderLegacyAssignmentReversal.prepend_l hℳ hd,
      ne_eq, hrl, false_and, false_or, not_false_eq_true, true_and, hLt]

def specification_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (c l L z d : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .conj (SecondOrderAssignmentSyntax.formula_m E d L) <|
    .forallE .num <| .forallE .num <|
      .iff (SecondOrderSequenceSyntax.formula_m (up (up E)) (up (up d))
        (.bvar (.there .here)) (.bvar .here))
        (padded_m (up (up E)) (up (up c)) (up (up l)) (up (up L)) (up (up z))
          (.bvar (.there .here)) (.bvar .here))

theorem specification_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) (c l L z d : Term signature_m Γ Δ .num) :
    (specification_m E c l L z d).satisfies η ↔
      valid_l (E.eval η) (d.eval η) (L.eval η) ∧ ∀ r x,
        read_l (E.eval η) (d.eval η) r x ↔
          padded_l (E.eval η) (c.eval η) (l.eval η) (L.eval η) (z.eval η) r x := by
  simp only [specification_m, Formula.satisfies, SecondOrderAssignmentSyntax.raw_l,
    SecondOrderSequenceSyntax.raw_l, padded_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula signature_m [] [.set, .num, .num, .num, .num] :=
  let E : Term signature_m [] [.set, .num, .num, .num, .num] .set := .fvar .here
  let c : Term signature_m [] [.set, .num, .num, .num, .num] .num := .fvar (.there .here)
  let l : Term signature_m [] [.set, .num, .num, .num, .num] .num := .fvar (.there (.there .here))
  let L : Term signature_m [] [.set, .num, .num, .num, .num] .num := .fvar (.there (.there (.there .here)))
  let z : Term signature_m [] [.set, .num, .num, .num, .num] .num := .fvar (.there (.there (.there (.there .here))))
  .imp (SecondOrderMemberDefArithmetic.powers_m E) <|
    .imp (SecondOrderAssignmentSyntax.formula_m E c l) <|
      .existsE .num <| specification_m (up E) (up c) (up l) (up L) (up z) (.bvar .here)

def sentence_m : Sentence signature_m := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ theory_m) : sentence_m.TrueIn ℳ := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderMemberDefArithmetic.powers_formula_l,
    SecondOrderAssignmentSyntax.raw_l, specification_formula_l, up, Term.eval_weakenBound, Term.eval]
  exact fun hE hc => exists_l hℳ hE hc _ _

theorem derives_m : Derives theory_m [] sentence_m :=
  SecondOrderCompleteness.derives_m (fun _ hℳ => models_l hℳ)

#print axioms prepend_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyAssignmentPadding
