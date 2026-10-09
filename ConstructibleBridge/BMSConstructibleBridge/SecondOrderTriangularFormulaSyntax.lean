import BMSConstructibleBridge.SecondOrderTriangularConstructor
import BMSConstructibleBridge.SecondOrderRecursiveRelation
import BMSConstructibleBridge.SecondOrderEvaluationRule

/-! # 三角编码及显式变量槽的内部合法性

零是假公式；标签 0/1 为成员/相等，2 为 NAND，3 为存在量词。存在量词
在指定槽更新赋值，不增加长度；原子及该槽必须小于赋值长度。递归仅读取
严格较小的公式码，覆盖原模型全部内部数，不解码为宿主 AST。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularFormulaSyntax

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderEvaluationRule (numeral_l)
open SecondOrderTriangularConstructor (constructor_l constructor_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m} (t : Term signature_m Γ Δ s) :=
  t.weakenBound sort_m.num

def cases_l (V : set_l ℳ) (n l a b : num_l ℳ) : Prop :=
  ((constructor_l (numeral_l ℳ 0) a b n ∨ constructor_l (numeral_l ℳ 1) a b n) ∧
      SecondOrderOrder.lt_l a l ∧ SecondOrderOrder.lt_l b l) ∨
    (constructor_l (numeral_l ℳ 2) a b n ∧ relation_l V a l ∧ relation_l V b l) ∨
    (constructor_l (numeral_l ℳ 3) a b n ∧ SecondOrderOrder.lt_l a l ∧ relation_l V b l)

def cases_m {Γ Δ : SortContext signature_m} (V : Term signature_m Γ Δ .set)
    (n l a b : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .disj (.conj (.disj (constructor_m (numeral_m 0) a b n) (constructor_m (numeral_m 1) a b n))
    (.conj (PrimitiveFormulas.lt_m a l) (PrimitiveFormulas.lt_m b l)))
    (.disj (.conj (constructor_m (numeral_m 2) a b n)
      (.conj (GraphSyntax.edge_m V a l) (GraphSyntax.edge_m V b l)))
      (.conj (constructor_m (numeral_m 3) a b n)
        (.conj (PrimitiveFormulas.lt_m a l) (GraphSyntax.edge_m V b l))))

def rule_l (V : set_l ℳ) (n l : num_l ℳ) : Prop :=
  n = zero_l ℳ ∨ ∃ a b, cases_l V n l a b

def rule_m {Γ Δ : SortContext signature_m} (V : Term signature_m Γ Δ .set)
    (n l : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .disj (.equal n (numeral_m 0)) <| .existsE .num <| .existsE .num <|
    cases_m (up (up V)) (up (up n)) (up (up l)) (.bvar (.there .here)) (.bvar .here)

def formula_m : Formula signature_m [] [.num, .num, .set] :=
  rule_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem cases_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (V : Term signature_m Γ Δ .set) (n l a b : Term signature_m Γ Δ .num) :
    (cases_m V n l a b).satisfies η ↔ cases_l (V.eval η) (n.eval η) (l.eval η) (a.eval η) (b.eval η) := by
  simp only [cases_m, cases_l, Formula.satisfies, SecondOrderTriangularConstructor.formula_l,
    SecondOrderOrder.formula_l, SecondOrderPairing.edge_l]
  rfl

theorem rule_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (V : Term signature_m Γ Δ .set) (n l : Term signature_m Γ Δ .num) :
    (rule_m V n l).satisfies η ↔ rule_l (V.eval η) (n.eval η) (l.eval η) := by
  simp only [rule_m, rule_l, Formula.satisfies, cases_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem local_l (hℳ : Theory.Models ℳ theory_m) (X Y : set_l ℳ) (n l : num_l ℳ)
    (h : SecondOrderInitialAgreement.agree_l X Y n) : rule_l X n l ↔ rule_l Y n l := by
  apply or_congr Iff.rfl
  apply exists_congr
  intro a
  apply exists_congr
  intro b
  apply or_congr Iff.rfl
  apply or_congr
  · apply and_congr_right
    intro hn
    obtain ⟨ha, hb⟩ := SecondOrderTriangularConstructor.bounds_l hℳ hn
    exact and_congr (h a ha l) (h b hb l)
  · apply and_congr_right
    intro hn
    exact and_congr Iff.rfl (h b (SecondOrderTriangularConstructor.bounds_l hℳ hn).2 l)

def spec_l (V : set_l ℳ) : Prop := ∀ n l, relation_l V n l ↔ rule_l V n l

def spec_m {Γ Δ : SortContext signature_m} (V : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .forallE .num <| .forallE .num <| .iff
    (GraphSyntax.edge_m (up (up V)) (.bvar (.there .here)) (.bvar .here))
    (rule_m (up (up V)) (.bvar (.there .here)) (.bvar .here))

theorem spec_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (V : Term signature_m Γ Δ .set) :
    (spec_m V).satisfies η ↔ spec_l (V.eval η) := by
  simp only [spec_m, spec_l, Formula.satisfies, SecondOrderPairing.edge_l, rule_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) : ∃! V : set_l ℳ, spec_l V := by
  have h (V : set_l ℳ) (n l : num_l ℳ) :
      SecondOrderRecursiveRelation.rule_l formula_m Env.empty V n l ↔ rule_l V n l :=
    rule_formula_l _ _ _ _
  obtain ⟨V, hV, hU⟩ := SecondOrderRecursiveRelation.exists_l hℳ formula_m pure_m Env.empty
    (fun X Y n hn l => (h X n l).trans ((local_l hℳ X Y n l hn).trans (h Y n l).symm))
  exact ⟨V, fun n l => (hV n l).trans (h V n l),
    fun W hW => hU W (fun n l => (hW n l).trans (h W n l).symm)⟩

def sentence_m : Sentence signature_m := Metatheory.Formula.forall_close
  (SecondOrderRankedRecursionTheorem.fixed_m (SecondOrderRecursiveRelation.operator_m formula_m))

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  rw [SecondOrderRankedRecursionTheorem.fixed_l]
  have hη : SecondOrderSetIterationTheorem.parameters_l η = Env.empty := by
    apply Env.ext <;> intro s v <;> nomatch v
  rw [hη]
  have h (V : set_l ℳ) (n l : num_l ℳ) :
      SecondOrderRecursiveRelation.rule_l formula_m Env.empty V n l ↔ rule_l V n l :=
    rule_formula_l _ _ _ _
  obtain ⟨V, hV, hU⟩ := exists_l hℳ
  refine ⟨V, (SecondOrderRecursiveRelation.operator_l formula_m Env.empty V V).mpr
    (fun n l => (hV n l).trans (h V n l).symm), ?_⟩
  intro W hW a
  have hWV : W = V := hU W (fun n l =>
    ((SecondOrderRecursiveRelation.operator_l formula_m Env.empty W W).mp hW n l).trans (h W n l))
  exact hWV ▸ Iff.rfl

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularFormulaSyntax
