import BMSConstructibleBridge.SecondOrderTriangularFormulaLength

/-! # 原内部合法性递归的同值唯一性

背景是原 Z₂，语句量化实际内部自然数及两个原二阶关系。强归纳用于
明确给出的算术公式，不依赖模型自然数的外部良基性。唯一性只认同
全部关系读值，不把含任意非编码元素的二阶对象误认作相等。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularFormulaAgreement

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderTriangularFormulaSyntax (spec_l spec_m spec_formula_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m} (t : Term signature_m Γ Δ s) :=
  t.weakenBound sort_m.num

def agreement_m {Γ Δ : SortContext signature_m}
    (V W : Term signature_m Γ Δ .set) (n : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .forallE .num <| .iff (GraphSyntax.edge_m (up V) (up n) (.bvar .here))
    (GraphSyntax.edge_m (up W) (up n) (.bvar .here))

theorem agreement_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (V W : Term signature_m Γ Δ .set) (n : Term signature_m Γ Δ .num) :
    (agreement_m V W n).satisfies η ↔
      ∀ l, relation_l (V.eval η) (n.eval η) l ↔ relation_l (W.eval η) (n.eval η) l := by
  simp only [agreement_m, Formula.satisfies, SecondOrderPairing.edge_l, up,
    Term.eval_weakenBound, Term.eval]
  rfl

theorem values_l (hℳ : Theory.Models ℳ theory_m) {V W : set_l ℳ}
    (hV : spec_l V) (hW : spec_l W) :
    ∀ n l, relation_l V n l ↔ relation_l W n l := by
  let φ : Formula signature_m [] [.num, .set, .set] :=
    agreement_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  have hφ : language_m φ = true := pure_language_m _ rfl
  apply SecondOrderListInduction.strong_induct_l hℳ φ hφ
    (Env.empty.pushFree W |>.pushFree V)
    (fun n => ∀ l, relation_l V n l ↔ relation_l W n l)
    (fun _ => agreement_formula_l _ _ _ _) ?_
  intro n ih
  have hTransfer {X Y : set_l ℳ} (hX : spec_l X) (hY : spec_l Y)
      (hChildren : ∀ k, SecondOrderOrder.lt_l k n → ∀ l, relation_l X k l → relation_l Y k l)
      (l : num_l ℳ) (hn : relation_l X n l) : relation_l Y n l := by
    apply (hY n l).mpr
    rcases (hX n l).mp hn with hZero | ⟨a, b, hCases⟩
    · exact Or.inl hZero
    · refine Or.inr ⟨a, b, ?_⟩
      rcases hCases with hAtomic | ⟨hNand, ha, hb⟩ | ⟨hExists, ha, hb⟩
      · exact Or.inl hAtomic
      · obtain ⟨han, hbn⟩ := SecondOrderTriangularConstructor.bounds_l hℳ hNand
        exact Or.inr (Or.inl ⟨hNand, hChildren a han l ha, hChildren b hbn l hb⟩)
      · exact Or.inr (Or.inr ⟨hExists, ha,
          hChildren b (SecondOrderTriangularConstructor.bounds_l hℳ hExists).2 l hb⟩)
  intro l
  exact ⟨hTransfer hV hW (fun k hk l => (ih k hk l).mp) l,
    hTransfer hW hV (fun k hk l => (ih k hk l).mpr) l⟩

def sentence_m : Sentence signature_m :=
  .forallE .set <| .forallE .set <|
    .imp (spec_m (.bvar (.there .here))) <| .imp (spec_m (.bvar .here)) <|
      .forallE .num <| agreement_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, spec_formula_l,
    agreement_formula_l, Term.eval]
  exact fun V W hV hW => values_l hℳ hV hW

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularFormulaAgreement
