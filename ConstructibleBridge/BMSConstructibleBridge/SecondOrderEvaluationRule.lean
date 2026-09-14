import BMSConstructibleBridge.SecondOrderAssignmentSyntax
import BMSConstructibleBridge.SecondOrderFormulaCode

/-!
# 内部集合语言求值的一步规则

节点标签 0、1、2、3、4 分别表示相等、成员、否定、合取、存在量词。
状态数编码赋值长度和赋值码。零节点、未知标签及无效赋值的输出为假。
这是完整布尔量词基的一步规则；此处尚不声明源语法对应或最终满足关系。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationRule

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderSequenceSyntax SecondOrderAssignmentSyntax

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 首三参数用于递归，后四参数为幂图、量词域、相等图和成员图。 -/
abbrev context_m : SortContext signature_m := [.num, .num, .set, .set, .set, .set, .set]

private def up {Γ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ context_m s) : Term signature_m (.num :: Γ) context_m s :=
  t.weakenBound sort_m.num

private def succ {Γ : SortContext signature_m} (t : Term signature_m Γ context_m .num) :
    Term signature_m Γ context_m .num := Term.app (σ := signature_m) .succ (.cons t .nil)

private theorem succ_eval_l {Γ : SortContext signature_m} (η : Env ℳ Γ context_m)
    (t : Term signature_m Γ context_m .num) : (succ t).eval η = succ_l (t.eval η) := rfl

private def E {Γ : SortContext signature_m} : Term signature_m Γ context_m .set :=
  .fvar (.there (.there (.there .here)))

private def D {Γ : SortContext signature_m} : Term signature_m Γ context_m .set :=
  .fvar (.there (.there (.there (.there .here))))

private def T {Γ : SortContext signature_m} : Term signature_m Γ context_m .set :=
  .fvar (.there (.there .here))

def atomic_m {Γ : SortContext signature_m} (Q : Term signature_m Γ context_m .set)
    (c p : Term signature_m Γ context_m .num) : Formula signature_m Γ context_m :=
  .existsE .num <| .existsE .num <| .existsE .num <| .existsE .num <|
    .conj (PrimitiveFormulas.pair_m (.bvar (.there (.there (.there .here))))
      (.bvar (.there (.there .here))) (up (up (up (up p))))) <|
      .conj (SecondOrderSequenceSyntax.formula_m E (up (up (up (up c))))
        (.bvar (.there (.there (.there .here)))) (.bvar (.there .here))) <|
        .conj (SecondOrderSequenceSyntax.formula_m E (up (up (up (up c))))
          (.bvar (.there (.there .here))) (.bvar .here)) <|
          GraphSyntax.edge_m (up (up (up (up Q)))) (.bvar (.there .here)) (.bvar .here)

def conjunction_m {Γ : SortContext signature_m} (p s : Term signature_m Γ context_m .num) :
    Formula signature_m Γ context_m :=
  .existsE .num <| .existsE .num <|
    .conj (PrimitiveFormulas.pair_m (.bvar (.there .here)) (.bvar .here) (up (up p))) <|
      .conj (GraphSyntax.edge_m T (.bvar (.there .here)) (up (up s)))
        (GraphSyntax.edge_m T (.bvar .here) (up (up s)))

def existential_m {Γ : SortContext signature_m} (n c p : Term signature_m Γ context_m .num) :
    Formula signature_m Γ context_m :=
  .existsE .num <| .existsE .num <| .existsE .num <|
    .conj (.rel .mem (.cons (.bvar (.there (.there .here))) (.cons D .nil))) <|
      .conj (extension_m E (up (up (up c))) (up (up (up n)))
        (.bvar (.there .here)) (.bvar (.there (.there .here)))) <|
        .conj (PrimitiveFormulas.pair_m (succ (up (up (up n)))) (.bvar (.there .here)) (.bvar .here))
          (GraphSyntax.edge_m T (up (up (up p))) (.bvar .here))

private def cases_m {Γ : SortContext signature_m} (n c t p : Term signature_m Γ context_m .num) :
    Formula signature_m Γ context_m :=
  .disj (.conj (.equal t (numeral_m 0))
    (atomic_m (.fvar (.there (.there (.there (.there (.there .here)))))) c p)) <|
    .disj (.conj (.equal t (numeral_m 1))
      (atomic_m (.fvar (.there (.there (.there (.there (.there (.there .here))))))) c p)) <|
      .disj (.conj (.equal t (numeral_m 2)) (.neg (GraphSyntax.edge_m T p (.fvar (.there .here))))) <|
        .disj (.conj (.equal t (numeral_m 3)) (conjunction_m p (.fvar (.there .here))))
          (.conj (.equal t (numeral_m 4)) (existential_m n c p))

def formula_m : Formula signature_m [] context_m :=
  .existsE .num <| .existsE .num <|
    .conj (PrimitiveFormulas.pair_m (.bvar (.there .here)) (.bvar .here) (.fvar (.there .here))) <|
      .conj (SecondOrderAssignmentSyntax.formula_m E (.bvar .here) (.bvar (.there .here))) <|
        .existsE .num <| .existsE .num <|
          .conj (SecondOrderFormulaCode.formula_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))
            (cases_m (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
              (.bvar (.there .here)) (.bvar .here))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

def atomic_l (E Q : set_l ℳ) (c p : num_l ℳ) : Prop :=
  ∃ i j x y, value_l i j = p ∧ read_l E c i x ∧ read_l E c j y ∧ relation_l Q x y

def conjunction_l (T : set_l ℳ) (p s : num_l ℳ) : Prop :=
  ∃ i j, value_l i j = p ∧ relation_l T i s ∧ relation_l T j s

def existential_l (E D T : set_l ℳ) (n c p : num_l ℳ) : Prop :=
  ∃ x d a, mem_l x D ∧ extension_l E c n d x ∧ value_l (succ_l n) d = a ∧ relation_l T p a

def numeral_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m) (k : Nat) : num_l ℳ :=
  Term.eval (Env.empty (M := ℳ)) (numeral_m k)

def cases_l (E D Q R T : set_l ℳ) (l c t p s : num_l ℳ) : Prop :=
    (t = numeral_l ℳ 0 ∧ atomic_l E Q c p) ∨
      (t = numeral_l ℳ 1 ∧ atomic_l E R c p) ∨
      (t = numeral_l ℳ 2 ∧ ¬ relation_l T p s) ∨
      (t = numeral_l ℳ 3 ∧ conjunction_l T p s) ∨
      (t = numeral_l ℳ 4 ∧ existential_l E D T l c p)

def rule_l (E D Q R T : set_l ℳ) (n s : num_l ℳ) : Prop :=
  ∃ l c, value_l l c = s ∧ valid_l E c l ∧ ∃ t p, SecondOrderFormulaCode.node_l t p = n ∧
    cases_l E D Q R T l c t p s

theorem atomic_formula_l {Γ : SortContext signature_m} (η : Env ℳ Γ context_m)
    (Q : Term signature_m Γ context_m .set) (c p : Term signature_m Γ context_m .num) :
    Formula.satisfies η (atomic_m Q c p) ↔
      atomic_l (η.freeVal (.there (.there (.there .here)))) (Q.eval η) (c.eval η) (p.eval η) := by
  simp only [atomic_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderSequenceSyntax.raw_l, SecondOrderPairing.edge_l, up, Term.eval_weakenBound]
  rfl

theorem conjunction_formula_l {Γ : SortContext signature_m} (η : Env ℳ Γ context_m)
    (p s : Term signature_m Γ context_m .num) :
    Formula.satisfies η (conjunction_m p s) ↔
      conjunction_l (η.freeVal (.there (.there .here))) (p.eval η) (s.eval η) := by
  simp only [conjunction_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l, up, Term.eval_weakenBound]
  rfl

theorem existential_formula_l {Γ : SortContext signature_m} (η : Env ℳ Γ context_m)
    (n c p : Term signature_m Γ context_m .num) :
    Formula.satisfies η (existential_m n c p) ↔ existential_l
      (η.freeVal (.there (.there (.there .here)))) (η.freeVal (.there (.there (.there (.there .here)))))
      (η.freeVal (.there (.there .here))) (n.eval η) (c.eval η) (p.eval η) := by
  simp only [existential_m, Formula.satisfies, extension_formula_l, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l, succ_eval_l, up, Term.eval_weakenBound]
  rfl

theorem formula_l (η : Env ℳ [] context_m) : Formula.satisfies η formula_m ↔
    rule_l (η.freeVal (.there (.there (.there .here))))
      (η.freeVal (.there (.there (.there (.there .here)))))
      (η.freeVal (.there (.there (.there (.there (.there .here))))))
      (η.freeVal (.there (.there (.there (.there (.there (.there .here)))))))
      (η.freeVal (.there (.there .here))) (η.freeVal .here) (η.freeVal (.there .here)) := by
  simp only [formula_m, cases_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderAssignmentSyntax.raw_l, SecondOrderFormulaCode.formula_l,
    atomic_formula_l, conjunction_formula_l, existential_formula_l, SecondOrderPairing.edge_l]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationRule
