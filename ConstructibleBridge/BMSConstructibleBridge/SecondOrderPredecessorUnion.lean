import BMSConstructibleBridge.SecondOrderPredecessorTaggedGraph
import BMSConstructibleBridge.SecondOrderCanonicalGraft

/-! # 前驱历史的唯一原图并集

每行以零为根，选出该根的全部子节点，再拼接新根。完整边规格只消费前驱
行，任意原历史都有唯一输出；这里不预设历史行良基，也不假设集合收集。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPredecessorUnion

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def selected_l (R H : set_l ℳ) (n c : num_l ℳ) : Prop :=
  ∃ i a, relation_l R i n ∧ value_l i a = c ∧ relation_l H i (value_l a (zero_l ℳ))

def selector_m : Formula signature_m [] [.num, .set, .set, .num] :=
  .existsE .num <| .existsE .num <| .existsE .num <|
    .conj (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))) <|
    .conj (PrimitiveFormulas.pair_m (.bvar (.there (.there .here)))
      (.bvar (.there .here)) (.fvar .here)) <|
    .conj (PrimitiveFormulas.pair_m (.bvar (.there .here))
      (Term.app (σ := signature_m) .zero .nil) (.bvar .here))
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar (.there (.there .here))) (.bvar .here))

theorem selector_pure_m : language_m selector_m = true := pure_language_m _ rfl

theorem selector_formula_l (R H : set_l ℳ) (n c : num_l ℳ) :
    Formula.satisfies
      (((((Env.empty (M := ℳ)).pushFree n).pushFree H).pushFree R).pushFree c)
      selector_m ↔ selected_l R H n c := by
  simp only [selector_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l]
  change (∃ i a t, relation_l R i n ∧ value_l i a = c ∧
    value_l a (zero_l ℳ) = t ∧ relation_l H i t) ↔ _
  constructor
  · rintro ⟨i, a, t, hi, ha, ht, h⟩
    exact ⟨i, a, hi, ha, ht.symm ▸ h⟩
  · rintro ⟨i, a, hi, ha, h⟩
    exact ⟨i, a, value_l a (zero_l ℳ), hi, ha, rfl, h⟩

structure spec_l (R H : set_l ℳ) (n : num_l ℳ) (G P W : set_l ℳ) : Prop where
  graph : SecondOrderPredecessorTaggedGraph.spec_l R H n G
  selection : ∀ c, mem_l c P ↔ selected_l R H n c
  graft : SecondOrderGraft.spec_l G P W

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R H : set_l ℳ) (n : num_l ℳ) :
    ∃ G P W : set_l ℳ, spec_l R H n G P W := by
  obtain ⟨G, hG, _⟩ := SecondOrderPredecessorTaggedGraph.exists_l hℳ R H n
  obtain ⟨P, hP⟩ := comprehension_l hℳ selector_m selector_pure_m
    ((((Env.empty (M := ℳ)).pushFree n).pushFree H).pushFree R)
  obtain ⟨W, hW, _⟩ := SecondOrderCanonicalGraft.exists_l hℳ G P
  exact ⟨G, P, W, hG, fun c => (hP c).trans (selector_formula_l R H n c), hW⟩

theorem local_l (hℳ : Theory.Models ℳ theory_m) {R H K G G' P P' W W' : set_l ℳ}
    {n : num_l ℳ} (hW : spec_l R H n G P W) (hW' : spec_l R K n G' P' W')
    (h : ∀ i, relation_l R i n → ∀ t, relation_l H i t ↔ relation_l K i t) : W = W' := by
  have hG : G = G' := SecondOrderPredecessorTaggedGraph.local_l hℳ hW.graph hW'.graph h
  have hP : P = P' := by
    apply ext_l hℳ P P'
    intro c
    rw [hW.selection, hW'.selection]
    constructor
    · rintro ⟨i, a, hi, ha, ht⟩
      exact ⟨i, a, hi, ha, (h i hi _).mp ht⟩
    · rintro ⟨i, a, hi, ha, ht⟩
      exact ⟨i, a, hi, ha, (h i hi _).mpr ht⟩
  subst G'
  subst P'
  exact SecondOrderCanonicalGraft.unique_l hℳ hW.graft hW'.graft

def output_l (R H : set_l ℳ) (n : num_l ℳ) (W : set_l ℳ) : Prop :=
  ∃ G P, spec_l R H n G P W

theorem output_exists_l (hℳ : Theory.Models ℳ theory_m) (R H : set_l ℳ) (n : num_l ℳ) :
    ∃! W : set_l ℳ, output_l R H n W := by
  obtain ⟨G, P, W, hW⟩ := exists_l hℳ R H n
  refine ⟨W, ⟨G, P, hW⟩, ?_⟩
  rintro W' ⟨G', P', hW'⟩
  exact local_l hℳ hW' hW (fun _ _ _ => Iff.rfl)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPredecessorUnion
