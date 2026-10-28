import BMSConstructibleBridge.SecondOrderInternalFormulaSyntax
import BMSConstructibleBridge.SecondOrderSourceAssignment

/-!
# 原纯集合公式编译后的内部合法性

已有实际赋值的界外无边性质给出全部变量位置界，再逐源公式证明编译码合法。
这一 AST 归纳只负责外部公式的编译正确性；全内部合法性关系的存在已由模型
内编号递归单独证明，不由此归纳替代。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInternalFormulaCompilation

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderInternalFormulaSyntax (spec_l cases_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false

universe u v

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {𝒩 : FirstOrder.Structure.{0, 0, 0, v} ℒ}

theorem node_l {V : set_l ℳ} (hV : spec_l V) (t p l : num_l ℳ)
    (h : cases_l V l t p) : relation_l V (SecondOrderFormulaCode.node_l t p) l :=
  (hV _ _).mpr (Or.inr ⟨t, p, rfl, h⟩)

theorem falsum_l {V : set_l ℳ} (hV : spec_l V) (l : num_l ℳ) :
    relation_l V (zero_l ℳ) l := (hV _ _).mpr (Or.inl rfl)

theorem negation_l {V : set_l ℳ} (hV : spec_l V) {p l : num_l ℳ}
    (hp : relation_l V p l) : relation_l V (SecondOrderFormulaCompilation.negation_l p) l :=
  node_l hV _ _ _ (Or.inr (Or.inl ⟨rfl, hp⟩))

theorem conjunction_l {V : set_l ℳ} (hV : spec_l V) {p q l : num_l ℳ}
    (hp : relation_l V p l) (hq : relation_l V q l) :
    relation_l V (SecondOrderFormulaCompilation.conjunction_l p q) l :=
  node_l hV _ _ _ (Or.inr (Or.inr (Or.inl ⟨rfl, p, q, rfl, hp, hq⟩)))

theorem existential_l {V : set_l ℳ} (hV : spec_l V) {p l : num_l ℳ}
    (hp : relation_l V p (succ_l l)) :
    relation_l V (SecondOrderFormulaCompilation.existential_l p) l :=
  node_l hV _ _ _ (Or.inr (Or.inr (Or.inr ⟨rfl, hp⟩)))

theorem terms_extend_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ} (l : num_l ℳ)
    (h : ∀ t : Term ℒ Γ Δ .set, SecondOrderOrder.lt_l (SecondOrderFormulaCompilation.term_l ℳ t) l) :
    ∀ t : Term ℒ (.set :: Γ) Δ .set,
      SecondOrderOrder.lt_l (SecondOrderFormulaCompilation.term_l ℳ t) (succ_l l) := by
  intro t
  match t with
  | .bvar .here => exact SecondOrderOrder.zero_succ_l hℳ l
  | .bvar (.there w) =>
      exact (SecondOrderOrder.succ_iff_l hℳ _ l).mpr (h (.bvar w))
  | .fvar w =>
      change SecondOrderOrder.lt_l
        (SecondOrderFormulaCompilation.term_l ℳ
          ((.fvar w : Term ℒ Γ Δ .set).weakenBound SetTheory.SetSort.set)) (succ_l l)
      rw [SecondOrderFormulaCompilation.term_weaken_l]
      exact (SecondOrderOrder.succ_iff_l hℳ _ l).mpr (h (.fvar w))
  | .app f _ => nomatch f

theorem formula_l (hℳ : Theory.Models ℳ theory_m) {V : set_l ℳ} (hV : spec_l V)
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (l : num_l ℳ)
    (h : ∀ t : Term ℒ Γ Δ .set, SecondOrderOrder.lt_l (SecondOrderFormulaCompilation.term_l ℳ t) l) :
    relation_l V (SecondOrderFormulaCompilation.formula_l ℳ φ) l := by
  match φ with
  | .falsum => exact falsum_l hV l
  | .truth => exact negation_l hV (falsum_l hV l)
  | .rel .membership (.cons s (.cons t .nil)) =>
      exact node_l hV _ _ _ (Or.inl ⟨Or.inr rfl, _, _, rfl, h s, h t⟩)
  | .equal (sort := .set) s t =>
      exact node_l hV _ _ _ (Or.inl ⟨Or.inl rfl, _, _, rfl, h s, h t⟩)
  | .neg φ => exact negation_l hV (formula_l hℳ hV φ l h)
  | .conj φ ψ => exact conjunction_l hV (formula_l hℳ hV φ l h) (formula_l hℳ hV ψ l h)
  | .disj φ ψ =>
      exact negation_l hV
        (conjunction_l hV (negation_l hV (formula_l hℳ hV φ l h))
          (negation_l hV (formula_l hℳ hV ψ l h)))
  | .imp φ ψ =>
      exact negation_l hV
        (conjunction_l hV (formula_l hℳ hV φ l h) (negation_l hV (formula_l hℳ hV ψ l h)))
  | .iff φ ψ =>
      exact conjunction_l hV
        (negation_l hV (conjunction_l hV (formula_l hℳ hV φ l h)
          (negation_l hV (formula_l hℳ hV ψ l h))))
        (negation_l hV (conjunction_l hV (formula_l hℳ hV ψ l h)
          (negation_l hV (formula_l hℳ hV φ l h))))
  | .forallE .set φ =>
      exact negation_l hV (existential_l hV
        (negation_l hV (formula_l hℳ hV φ (succ_l l) (terms_extend_l hℳ l h))))
  | .existsE .set φ =>
      exact existential_l hV
        (formula_l hℳ hV φ (succ_l l) (terms_extend_l hℳ l h))
termination_by φ.size
decreasing_by all_goals simp only [Formula.size]; omega

theorem assignment_l (hℳ : Theory.Models ℳ theory_m) {V E D : set_l ℳ}
    (hV : spec_l V) (f : num_l ℳ → 𝒩.Carrier .set) {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) {l c : num_l ℳ} (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (hη : SecondOrderSourceEnvironment.represents_l f η E D c) (φ : Formula ℒ Γ Δ) :
    relation_l V (SecondOrderFormulaCompilation.formula_l ℳ φ) l := by
  apply formula_l hℳ hV φ l
  intro t
  obtain ⟨y, hy, _⟩ := hη t
  exact hc.2 _ y hy

theorem extension_l (hℳ : Theory.Models ℳ theory_m) {V E D : set_l ℳ}
    (hV : spec_l V) (f : num_l ℳ → 𝒩.Carrier .set) {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) {l c : num_l ℳ} (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (hη : SecondOrderSourceEnvironment.represents_l f η E D c) (φ : Formula ℒ (.set :: Γ) Δ) :
    relation_l V (SecondOrderFormulaCompilation.formula_l ℳ φ) (succ_l l) := by
  apply formula_l hℳ hV φ (succ_l l)
  apply terms_extend_l hℳ l
  intro t
  obtain ⟨y, hy, _⟩ := hη t
  exact hc.2 _ y hy

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInternalFormulaCompilation
