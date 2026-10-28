import BMSConstructibleBridge.SecondOrderRelatedAssignments

/-!
# 任意内部有限赋值沿全域数值关系换代表

先用内部最小元将关系纤维单值化，再对读取图作实际理解和有限数码编码。
长度覆盖非标准内部数；不对长度使用宿主 Nat 归纳，也不在 Type 中选择代表。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAssignmentTransport

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderAssignmentSyntax (valid_l)
open SecondOrderSequenceSyntax (read_l)
open SecondOrderRelatedAssignments (related_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem exists_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (K : set_l ℳ)
    (hK : ∀ x, ∃ y, relation_l K x y) (c l : num_l ℳ) (hc : valid_l E c l) :
    ∃ d, valid_l E d l ∧ related_l E K c d := by
  obtain ⟨F, hF, hFK⟩ := SecondOrderMinimum.choice_l hℳ K hK
  let φ : Formula signature_m [] [.num, .num, .set, .set, .num] :=
    .existsE .num (.conj
      (SecondOrderSequenceSyntax.formula_m (.fvar (.there (.there .here)))
        (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.bvar .here))
      (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.bvar .here) (.fvar (.there .here))))
  obtain ⟨H, hH₀⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((((Env.empty (M := ℳ)).pushFree c).pushFree F).pushFree E)
  have hH i y : relation_l H i y ↔ ∃ x, read_l E c i x ∧ relation_l F x y := by
    refine (hH₀ i y).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderSequenceSyntax.raw_l, SecondOrderPairing.edge_l]
    rfl
  have hFunction i (hi : SecondOrderOrder.lt_l i l) : ∃! y, relation_l H i y := by
    obtain ⟨x, hx, hX⟩ := hc.1 i hi
    obtain ⟨y, hy, hY⟩ := hF x
    refine ⟨y, (hH i y).mpr ⟨x, hx, hy⟩, ?_⟩
    intro z hz
    obtain ⟨w, hw, hwz⟩ := (hH i z).mp hz
    have hwx := hX w hw
    exact hY z (hwx ▸ hwz)
  obtain ⟨d, hd, hRead⟩ := SecondOrderAssignment.encode_l hℳ hE H l hFunction
  refine ⟨d, (SecondOrderAssignmentCongruence.valid_iff_l hE d l).mpr hd, ?_⟩
  intro i x y hx hy
  have hy' := (hRead i y).mp ((SecondOrderSequenceSyntax.read_eq_l hE d i y).mp hy)
  obtain ⟨w, hw, hwy⟩ := (hH i y).mp hy'.2
  obtain ⟨z, _, hU⟩ := hc.1 i (hc.2 i x hx)
  have hwx : w = x := (hU w hw).trans (hU x hx).symm
  exact hFK x y (hwx ▸ hwy)

theorem exists_reverse_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (K : set_l ℳ)
    (hK : ∀ y, ∃ x, relation_l K x y) (d l : num_l ℳ) (hd : valid_l E d l) :
    ∃ c, valid_l E c l ∧ related_l E K c d := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  obtain ⟨K', hK'⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((Env.empty (M := ℳ)).pushFree K)
  have hSwap y x : relation_l K' y x ↔ relation_l K x y := by
    refine (hK' y x).trans ?_
    exact SecondOrderPairing.edge_l _ _ _ _
  obtain ⟨c, hc, h⟩ := exists_l hℳ hE K'
    (fun y => by obtain ⟨x, hx⟩ := hK y; exact ⟨x, (hSwap y x).mpr hx⟩) d l hd
  exact ⟨c, hc, fun i x y hx hy => (hSwap y x).mp (h i y x hy hx)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAssignmentTransport
