import BMSConstructibleBridge.SecondOrderTaggedDomain
import BMSConstructibleBridge.SecondOrderSections

/-! # 仅由前驱历史构造的带标号图

对象语言是原双排序算术签名，背景是原 Z₂。实际理解公式同时限制整张图的
所有边，而非仅限制选根集合。因此相同前驱历史给出相同原图，未来行没有
任何影响。良基保持只对已给出的前驱行证明；这里不假定外部标准性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPredecessorTaggedGraph

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def edge_l (R H : set_l ℳ) (n c d : num_l ℳ) : Prop :=
  ∃ i a b, relation_l R i n ∧ value_l i a = c ∧ value_l i b = d ∧
    relation_l H i (value_l a b)

def spec_l (R H : set_l ℳ) (n : num_l ℳ) (G : set_l ℳ) : Prop :=
  ∀ c d, relation_l G c d ↔ edge_l R H n c d

def formula_m : Formula signature_m [] [.num, .num, .set, .set, .num] :=
  .existsE .num <| .existsE .num <| .existsE .num <| .existsE .num <|
    .conj (GraphSyntax.edge_m (.fvar (.there (.there .here)))
      (.bvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))) <|
    .conj (PrimitiveFormulas.pair_m (.bvar (.there (.there (.there .here))))
      (.bvar (.there (.there .here))) (.fvar .here)) <|
    .conj (PrimitiveFormulas.pair_m (.bvar (.there (.there (.there .here))))
      (.bvar (.there .here)) (.fvar (.there .here))) <|
    .conj (PrimitiveFormulas.pair_m (.bvar (.there (.there .here)))
      (.bvar (.there .here)) (.bvar .here))
      (GraphSyntax.edge_m (.fvar (.there (.there (.there .here))))
        (.bvar (.there (.there (.there .here)))) (.bvar .here))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem formula_l (R H : set_l ℳ) (n c d : num_l ℳ) :
    Formula.satisfies
      ((((((Env.empty (M := ℳ)).pushFree n).pushFree H).pushFree R).pushFree d).pushFree c)
      formula_m ↔ edge_l R H n c d := by
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l]
  change (∃ i a b t, relation_l R i n ∧ value_l i a = c ∧ value_l i b = d ∧
    value_l a b = t ∧ relation_l H i t) ↔ _
  constructor
  · rintro ⟨i, a, b, t, hi, ha, hb, ht, h⟩
    exact ⟨i, a, b, hi, ha, hb, ht.symm ▸ h⟩
  · rintro ⟨i, a, b, hi, ha, hb, h⟩
    exact ⟨i, a, b, value_l a b, hi, ha, hb, rfl, h⟩

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {R H G K : set_l ℳ} {n : num_l ℳ}
    (hG : spec_l R H n G) (hK : spec_l R H n K) : G = K :=
  SecondOrderRelations.ext_l hℳ G K (fun c d => (hG c d).trans (hK c d).symm)

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R H : set_l ℳ) (n : num_l ℳ) :
    ∃! G : set_l ℳ, spec_l R H n G := by
  obtain ⟨G, hG⟩ := SecondOrderRelations.comprehension_l hℳ formula_m pure_m
    ((((Env.empty (M := ℳ)).pushFree n).pushFree H).pushFree R)
  have hSpec : spec_l R H n G := fun c d => (hG c d).trans (formula_l R H n c d)
  exact ⟨G, hSpec, fun K hK => unique_l hℳ hK hSpec⟩

theorem local_l (hℳ : Theory.Models ℳ theory_m) {R H K G G' : set_l ℳ} {n : num_l ℳ}
    (hG : spec_l R H n G) (hG' : spec_l R K n G')
    (h : ∀ i, relation_l R i n → ∀ t, relation_l H i t ↔ relation_l K i t) : G = G' := by
  apply SecondOrderRelations.ext_l hℳ G G'
  intro c d
  rw [hG, hG']
  constructor
  · rintro ⟨i, a, b, hi, ha, hb, ht⟩
    exact ⟨i, a, b, hi, ha, hb, (h i hi _).mp ht⟩
  · rintro ⟨i, a, b, hi, ha, hb, ht⟩
    exact ⟨i, a, b, hi, ha, hb, (h i hi _).mpr ht⟩

theorem fiber_l (hℳ : Theory.Models ℳ theory_m) {R H G W : set_l ℳ} {n i : num_l ℳ}
    (hG : spec_l R H n G) (hi : relation_l R i n) (hW : SecondOrderSections.spec_l H i W) :
    SecondOrderTaggedGraph.fiber_l i W G := by
  intro c b
  rw [hG]
  constructor
  · rintro ⟨j, a, e, _, ha, hb, ht⟩
    obtain ⟨hji, heb⟩ := SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hb
    subst j
    subst e
    exact ⟨a, ha.symm, (hW _).mpr ht⟩
  · rintro ⟨a, rfl, ht⟩
    exact ⟨i, a, b, hi, rfl, rfl, (hW _).mp ht⟩

theorem wf_l (hℳ : Theory.Models ℳ theory_m) {R H G W : set_l ℳ} {n i a : num_l ℳ}
    (hG : spec_l R H n G) (hi : relation_l R i n) (hW : SecondOrderSections.spec_l H i W)
    (hw : SecondOrderDomain.wf_l W a) : SecondOrderDomain.wf_l G (value_l i a) :=
  SecondOrderTaggedDomain.wf_l hℳ i W G (fiber_l hℳ hG hi hW) a hw

#print axioms local_l
#print axioms wf_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPredecessorTaggedGraph
