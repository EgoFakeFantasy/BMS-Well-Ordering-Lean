import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionIndexCanonical

/-! # 规范全槽指标规格的纯对象公式

保留全部内部序列、辅助比较和最终图无垃圾条款；自由参数仍是原集合项。
逐公式对应对任意纯集合结构成立。本文件只提供 AST 和语义对应，
不以此代替规范后继的正式可推导性或最终 BMS 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalIndexSyntax

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderObjectSyntax (member_m value_m ordered_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def product_m {Γ Δ : SortContext ℒ} (X Y Z : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up Z))
    (PowerlessRelativeClassProduct.body_m (up X) (up Y) (.bvar .here))

theorem product_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (X Y Z : Term ℒ Γ Δ .set) :
    (product_m X Y Z).satisfies η ↔
      PowerlessRelativeClassSatisfactionIndexCanonical.product_l (X.eval η) (Y.eval η) (Z.eval η) := by
  simp only [product_m, PowerlessRelativeClassSatisfactionIndexCanonical.product_l, Formula.satisfies,
    PowerlessRelativeClassProduct.body_formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def proper_m {Γ Δ : SortContext ℒ} (R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up R)) <|
    .existsE .set <| .existsE .set <|
      ordered_m (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here)))

theorem proper_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (R : Term ℒ Γ Δ .set) :
    (proper_m R).satisfies η ↔ PowerlessRelativeClassSatisfactionIndexCanonical.proper_l (R.eval η) := by
  simp only [proper_m, PowerlessRelativeClassSatisfactionIndexCanonical.proper_l, Formula.satisfies,
    ordered_formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def omegaRead_m {Γ Δ : SortContext ℒ} (ω N : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    .iff (value_m (up (up N)) (.bvar (.there .here)) (.bvar .here)) <|
      .conj (member_m (.bvar (.there .here)) (up (up ω))) <|
        .conj (member_m (.bvar .here) (up (up ω))) (member_m (.bvar (.there .here)) (.bvar .here))

theorem omegaRead_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω N : Term ℒ Γ Δ .set) :
    (omegaRead_m ω N).satisfies η ↔ ∀ x y, value_l (N.eval η) x y ↔
      member_l ℳ₀ x (ω.eval η) ∧ member_l ℳ₀ y (ω.eval η) ∧ member_l ℳ₀ x y := by
  simp only [omegaRead_m, Formula.satisfies, value_formula_l, member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def shortlexRead_m {Γ Δ : SortContext ℒ} (ω A P T : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    .iff (value_m (up (up T)) (.bvar (.there .here)) (.bvar .here))
      (PowerlessRelativeClassSequenceOrderGraph.shortlex_m
        (up (up ω)) (up (up A)) (up (up P)) (.bvar (.there .here)) (.bvar .here))

theorem shortlexRead_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω A P T : Term ℒ Γ Δ .set) :
    (shortlexRead_m ω A P T).satisfies η ↔ ∀ f g, value_l (T.eval η) f g ↔
      PowerlessRelativeClassSequenceOrderGraph.shortlex_l (ω.eval η) (A.eval η) (P.eval η) f g := by
  simp only [shortlexRead_m, Formula.satisfies, value_formula_l,
    PowerlessRelativeClassSequenceOrderGraph.shortlex_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def lexRead_m {Γ Δ : SortContext ℒ} (X Y R S K : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    .iff (value_m (up (up K)) (.bvar (.there .here)) (.bvar .here))
      (PowerlessRelativeClassLexicographicWellOrder.lex_m
        (up (up X)) (up (up Y)) (up (up R)) (up (up S)) (.bvar (.there .here)) (.bvar .here))

theorem lexRead_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (X Y R S K : Term ℒ Γ Δ .set) :
    (lexRead_m X Y R S K).satisfies η ↔ ∀ p q, value_l (K.eval η) p q ↔
      PowerlessRelativeClassLexicographicWellOrder.lex_l (X.eval η) (Y.eval η) (R.eval η) (S.eval η) p q := by
  simp only [lexRead_m, Formula.satisfies, value_formula_l,
    PowerlessRelativeClassLexicographicWellOrder.lex_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def spec_m {Γ Δ : SortContext ℒ} (ω A P S I J U : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up t))
  .conj (PowerlessFiniteSequencesSyntax.spec_m ω A S) <|
    .conj (product_m ω S I) <| .conj (product_m ω I J) <| .conj (proper_m U) <|
      .existsE .set <| .existsE .set <| .existsE .set <|
        .conj (omegaRead_m (w ω) (.bvar (.there (.there .here)))) <|
          .conj (shortlexRead_m (w ω) (w A) (w P) (.bvar (.there .here))) <|
            .conj (lexRead_m (w ω) (w S) (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
              (lexRead_m (w ω) (w I) (.bvar (.there (.there .here))) (.bvar .here) (w U))

theorem spec_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω A P S I J U : Term ℒ Γ Δ .set) :
    (spec_m ω A P S I J U).satisfies η ↔ PowerlessRelativeClassSatisfactionIndexCanonical.spec_l
      (ω.eval η) (A.eval η) (P.eval η) (S.eval η) (I.eval η) (J.eval η) (U.eval η) := by
  simp only [spec_m, PowerlessRelativeClassSatisfactionIndexCanonical.spec_l, Formula.satisfies,
    PowerlessFiniteSequencesSyntax.spec_formula_l, product_formula_l, proper_formula_l,
    omegaRead_formula_l, shortlexRead_formula_l, lexRead_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalIndexSyntax
