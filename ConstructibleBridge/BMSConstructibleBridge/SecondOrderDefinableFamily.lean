import BMSConstructibleBridge.SecondOrderSourceAssignment

/-!
# 由公式和参数数码索引的内部子集族

一个内部实数同时收集全部求值切片。索引编码公式、赋值长度和赋值数码；
本模块构造数域子集族，还未把它与集合论中的 Def 对象或旧语法编码等同。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableFamily

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderAssignmentSyntax (valid_l extension_l)

set_option autoImplicit false

universe u v

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} {𝒩 : FirstOrder.Structure.{0, 0, 0, v} ℒ}

noncomputable def index_l (p l c : num_l ℳ) : num_l ℳ := value_l p (value_l l c)

def row_l (E D T : set_l ℳ) (i x : num_l ℳ) : Prop :=
  mem_l x D ∧ ∃ p l c, index_l p l c = i ∧ valid_l E c l ∧
    ∃ d, extension_l E c l d x ∧ relation_l T p (value_l (succ_l l) d)

def formula_m : Formula signature_m [] [.num, .num, .set, .set, .set] :=
  .conj (.rel .mem (.cons (.fvar (.there .here)) (.cons (.fvar (.there (.there (.there .here)))) .nil))) <|
    .existsE .num <| .existsE .num <| .existsE .num <| .existsE .num <| .existsE .num <| .existsE .num <|
      .conj (PrimitiveFormulas.pair_m (.bvar (.there (.there (.there (.there .here)))))
        (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))) <|
      .conj (PrimitiveFormulas.pair_m (.bvar (.there (.there (.there (.there (.there .here))))))
        (.bvar (.there (.there .here))) (.fvar .here)) <|
      .conj (SecondOrderAssignmentSyntax.formula_m (.fvar (.there (.there .here)))
        (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there .here)))))) <|
      .conj (SecondOrderAssignmentSyntax.extension_m (.fvar (.there (.there .here)))
        (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there .here)))))
        (.bvar (.there .here)) (.fvar (.there .here))) <|
      .conj (PrimitiveFormulas.pair_m
        (Term.app (σ := signature_m) .succ (.cons (.bvar (.there (.there (.there (.there .here))))) .nil))
        (.bvar (.there .here)) (.bvar .here)) <|
      GraphSyntax.edge_m (.fvar (.there (.there (.there (.there .here)))))
        (.bvar (.there (.there (.there (.there (.there .here)))))) (.bvar .here)

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem formula_l (η : Env ℳ [] [.num, .num, .set, .set, .set]) : Formula.satisfies η formula_m ↔
    row_l (η.freeVal (.there (.there .here))) (η.freeVal (.there (.there (.there .here))))
      (η.freeVal (.there (.there (.there (.there .here))))) (η.freeVal .here) (η.freeVal (.there .here)) := by
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderAssignmentSyntax.raw_l, SecondOrderAssignmentSyntax.extension_formula_l, SecondOrderPairing.edge_l]
  let E := η.freeVal (.there (.there .here))
  let D := η.freeVal (.there (.there (.there .here)))
  let T := η.freeVal (.there (.there (.there (.there .here))))
  let i := η.freeVal .here
  let x := η.freeVal (.there .here)
  change (mem_l x D ∧ ∃ p l c u d a, value_l l c = u ∧ value_l p u = i ∧ valid_l E c l ∧
    extension_l E c l d x ∧ value_l (succ_l l) d = a ∧ relation_l T p a) ↔ _
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨p, l, c, u, d, a, rfl, hi, hc, hd, rfl, hT⟩
    exact ⟨p, l, c, hi, hc, d, hd, hT⟩
  · rintro ⟨p, l, c, hi, hc, d, hd, hT⟩
    exact ⟨p, l, c, _, d, _, rfl, hi, hc, hd, rfl, hT⟩

def spec_l (E D T F : set_l ℳ) : Prop := ∀ i x, relation_l F i x ↔ row_l E D T i x

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (E D T : set_l ℳ) : ∃! F, spec_l E D T F := by
  obtain ⟨F, hF⟩ := SecondOrderRelations.comprehension_l hℳ formula_m pure_m
    ((((Env.empty (M := ℳ)).pushFree T).pushFree D).pushFree E)
  have h : spec_l E D T F := fun i x => (hF i x).trans (formula_l _)
  exact ⟨F, h, fun G hG => SecondOrderRelations.ext_l hℳ G F (fun i x => (hG i x).trans (h i x).symm)⟩

theorem index_injective_l (hℳ : Theory.Models ℳ theory_m) (p l c q m d : num_l ℳ)
    (h : index_l p l c = index_l q m d) : p = q ∧ l = m ∧ c = d := by
  obtain ⟨hp, h⟩ := SecondOrderPairingBounds.injective_l hℳ p (value_l l c) q (value_l m d) h
  exact ⟨hp, SecondOrderPairingBounds.injective_l hℳ l c m d h⟩

theorem row_index_l (hℳ : Theory.Models ℳ theory_m) (E D T F : set_l ℳ) (hF : spec_l E D T F)
    (p l c x : num_l ℳ) : relation_l F (index_l p l c) x ↔ mem_l x D ∧ valid_l E c l ∧
      ∃ d, extension_l E c l d x ∧ relation_l T p (value_l (succ_l l) d) := by
  refine (hF _ x).trans ?_
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨q, m, e, h, hc, hd⟩
    obtain ⟨rfl, rfl, rfl⟩ := index_injective_l hℳ q m e p l c h
    exact ⟨hc, hd⟩
  · rintro ⟨hc, hd⟩
    exact ⟨p, l, c, rfl, hc, hd⟩

theorem slice_l (hℳ : Theory.Models ℳ theory_m) (E D T F : set_l ℳ) (hF : spec_l E D T F)
    (i : num_l ℳ) : ∃ X : set_l ℳ, ∀ x, mem_l x X ↔ row_l E D T i x := by
  obtain ⟨X, hX⟩ := SecondOrderSections.exists_l hℳ F i
  exact ⟨X, fun x => (hX x).trans (hF i x)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableFamily
