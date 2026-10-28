import BMSConstructibleBridge.SecondOrderEvaluationFixedPoint

/-!
# 全内部数码的纯集合公式合法性

以原求值器同一节点编码构造合法性关系：零为假公式，标签 0/1 为相等/成员，
2/3/4 为否定/合取/存在。第二坐标为当前变量槽数，存在量词增加一个槽。
原编号递归给出模型内全部码的唯一合法性关系，不能把宿主 AST 枚举当作它。
此处尚不声明精确 Def 或与另一套 quotation 相等。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInternalFormulaSyntax

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) : Term signature_m (.num :: Γ) Δ s :=
  t.weakenBound sort_m.num

private def succ_m {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons t .nil)

def atomic_l (p l : num_l ℳ) : Prop :=
  ∃ i j, value_l i j = p ∧ SecondOrderOrder.lt_l i l ∧ SecondOrderOrder.lt_l j l

def atomic_m {Γ Δ : SortContext signature_m} (p l : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj
    (PrimitiveFormulas.pair_m (.bvar (.there .here)) (.bvar .here) (up (up p)))
    (.conj (PrimitiveFormulas.lt_m (.bvar (.there .here)) (up (up l)))
      (PrimitiveFormulas.lt_m (.bvar .here) (up (up l))))))

def binary_m {Γ Δ : SortContext signature_m} (V : Term signature_m Γ Δ .set)
    (p l : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj
    (PrimitiveFormulas.pair_m (.bvar (.there .here)) (.bvar .here) (up (up p)))
    (.conj (GraphSyntax.edge_m (up (up V)) (.bvar (.there .here)) (up (up l)))
      (GraphSyntax.edge_m (up (up V)) (.bvar .here) (up (up l))))))

def cases_l (V : set_l ℳ) (l t p : num_l ℳ) : Prop :=
  ((t = numeral_l ℳ 0 ∨ t = numeral_l ℳ 1) ∧ atomic_l p l) ∨
    (t = numeral_l ℳ 2 ∧ relation_l V p l) ∨
    (t = numeral_l ℳ 3 ∧ SecondOrderEvaluationRule.conjunction_l V p l) ∨
    (t = numeral_l ℳ 4 ∧ relation_l V p (succ_l l))

def cases_m {Γ Δ : SortContext signature_m} (V : Term signature_m Γ Δ .set)
    (l t p : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .disj (.conj (.disj (.equal t (numeral_m 0)) (.equal t (numeral_m 1))) (atomic_m p l))
    (.disj (.conj (.equal t (numeral_m 2)) (GraphSyntax.edge_m V p l))
      (.disj (.conj (.equal t (numeral_m 3)) (binary_m V p l))
        (.conj (.equal t (numeral_m 4)) (GraphSyntax.edge_m V p (succ_m l)))))

def rule_l (V : set_l ℳ) (n l : num_l ℳ) : Prop :=
  n = zero_l ℳ ∨ ∃ t p, SecondOrderFormulaCode.node_l t p = n ∧ cases_l V l t p

def rule_m {Γ Δ : SortContext signature_m} (V : Term signature_m Γ Δ .set)
    (n l : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .disj (.equal n (numeral_m 0)) (.existsE .num (.existsE .num (.conj
    (SecondOrderFormulaCode.formula_m (.bvar (.there .here)) (.bvar .here) (up (up n)))
    (cases_m (up (up V)) (up (up l)) (.bvar (.there .here)) (.bvar .here)))))

def formula_m : Formula signature_m [] [.num, .num, .set] :=
  rule_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem atomic_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (p l : Term signature_m Γ Δ .num) : (atomic_m p l).satisfies η ↔
      atomic_l (p.eval η) (l.eval η) := by
  simp only [atomic_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderOrder.formula_l, up, Term.eval, Term.eval_weakenBound]
  rfl

theorem binary_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (V : Term signature_m Γ Δ .set) (p l : Term signature_m Γ Δ .num) :
    (binary_m V p l).satisfies η ↔
      SecondOrderEvaluationRule.conjunction_l (V.eval η) (p.eval η) (l.eval η) := by
  simp only [binary_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l, up, Term.eval, Term.eval_weakenBound]
  rfl

theorem cases_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (V : Term signature_m Γ Δ .set) (l t p : Term signature_m Γ Δ .num) :
    (cases_m V l t p).satisfies η ↔ cases_l (V.eval η) (l.eval η) (t.eval η) (p.eval η) := by
  simp only [cases_m, Formula.satisfies, atomic_formula_l, binary_formula_l,
    SecondOrderPairing.edge_l, succ_m, Term.eval]
  rfl

theorem rule_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (V : Term signature_m Γ Δ .set) (n l : Term signature_m Γ Δ .num) :
    (rule_m V n l).satisfies η ↔ rule_l (V.eval η) (n.eval η) (l.eval η) := by
  simp only [rule_m, Formula.satisfies, SecondOrderFormulaCode.formula_l,
    cases_formula_l, up, Term.eval, Term.eval_weakenBound]
  rfl

theorem local_l (hℳ : Theory.Models ℳ theory_m) (X Y : set_l ℳ) (n l : num_l ℳ)
    (h : SecondOrderInitialAgreement.agree_l X Y n) : rule_l X n l ↔ rule_l Y n l := by
  apply or_congr Iff.rfl
  apply exists_congr
  intro t
  apply exists_congr
  intro p
  apply and_congr_right
  intro hp
  have hp₀ := (SecondOrderFormulaCode.bounds_l hℳ t p).2
  rw [hp] at hp₀
  exact or_congr Iff.rfl (or_congr (and_congr Iff.rfl (h p hp₀ l))
    (or_congr (and_congr Iff.rfl
      (SecondOrderEvaluationFixedPoint.conjunction_local_l hℳ X Y n t p l h hp))
      (and_congr Iff.rfl (h p hp₀ (succ_l l)))))

def spec_l (V : set_l ℳ) : Prop := ∀ n l, relation_l V n l ↔ rule_l V n l

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

/-- 合法性关系的存在与唯一性在原 Z₂ 推导核中成立，无局部性或递归假设残留。 -/
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

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInternalFormulaSyntax
