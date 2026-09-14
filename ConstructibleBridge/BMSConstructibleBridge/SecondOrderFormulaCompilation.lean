import BMSConstructibleBridge.SecondOrderEvaluationEquations

/-!
# 上游纯集合语法到内部求值码

直接递归上游有类型公式，不另造语法核。绑定变量在前、自由变量随后，新增
量词统一前插一位。此处是任意模型中的数码解释，不宣称已有 PRA 的编码程序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFormulaCompilation

open Logic FirstOrder SecondOrderSyntax SecondOrderModel
open SecondOrderPairing (value_l)
open SecondOrderEvaluationRule (numeral_l)
open SecondOrderEvaluationEquations (node_l)

set_option autoImplicit false

universe u

noncomputable def term_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m) {Γ Δ : SortContext ℒ} :
    Term ℒ Γ Δ .set → num_l ℳ
  | .bvar v => numeral_l ℳ v.index
  | .fvar v => numeral_l ℳ (Γ.length + v.index)
  | .app f _ => nomatch f

noncomputable def negation_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (p : num_l ℳ) : num_l ℳ :=
  node_l 2 p

noncomputable def conjunction_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (p q : num_l ℳ) : num_l ℳ :=
  node_l 3 (value_l p q)

noncomputable def disjunction_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (p q : num_l ℳ) : num_l ℳ :=
  negation_l (conjunction_l (negation_l p) (negation_l q))

noncomputable def implication_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (p q : num_l ℳ) : num_l ℳ :=
  negation_l (conjunction_l p (negation_l q))

noncomputable def biconditional_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (p q : num_l ℳ) : num_l ℳ :=
  conjunction_l (implication_l p q) (implication_l q p)

noncomputable def existential_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (p : num_l ℳ) : num_l ℳ :=
  node_l 4 p

noncomputable def universal_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (p : num_l ℳ) : num_l ℳ :=
  negation_l (existential_l (negation_l p))

noncomputable def formula_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m) {Γ Δ : SortContext ℒ} :
    Formula ℒ Γ Δ → num_l ℳ
  | .falsum => zero_l ℳ
  | .truth => negation_l (zero_l ℳ)
  | .rel .membership (.cons s (.cons t .nil)) => node_l 1 (value_l (term_l ℳ s) (term_l ℳ t))
  | .equal (sort := .set) s t => node_l 0 (value_l (term_l ℳ s) (term_l ℳ t))
  | .neg φ => negation_l (formula_l ℳ φ)
  | .conj φ ψ => conjunction_l (formula_l ℳ φ) (formula_l ℳ ψ)
  | .disj φ ψ => disjunction_l (formula_l ℳ φ) (formula_l ℳ ψ)
  | .imp φ ψ => implication_l (formula_l ℳ φ) (formula_l ℳ ψ)
  | .iff φ ψ => biconditional_l (formula_l ℳ φ) (formula_l ℳ ψ)
  | .forallE .set φ => universal_l (formula_l ℳ φ)
  | .existsE .set φ => existential_l (formula_l ℳ φ)

theorem term_weaken_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m) {Γ Δ : SortContext ℒ}
    (t : Term ℒ Γ Δ .set) : term_l ℳ (t.weakenBound SetTheory.SetSort.set) = succ_l (term_l ℳ t) := by
  match t with
  | .bvar v => rfl
  | .fvar v =>
      change numeral_l ℳ (Γ.length + 1 + v.index) = numeral_l ℳ (Γ.length + v.index + 1)
      congr 1
      omega
  | .app f _ => nomatch f

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFormulaCompilation
