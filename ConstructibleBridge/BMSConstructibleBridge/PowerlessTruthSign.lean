import BMSConstructibleBridge.PowerlessTruthRecord
import BMSConstructibleBridge.PowerlessEvaluationEquations

/-!
# 真值方向与记录集合的可靠性

标记 e 表示真，t 表示假。它与 Lévy 极性的匹配由上层规则另行核验。
这里的完整求值图 H 只服务于正确性陈述，不是待构造分类器的参数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthSign

open Logic FirstOrder ThirdOrderSemantics
open PowerlessEvaluationClause (query_l query_m query_formula_l)
open PowerlessTruthRecord (entry_l entry_m entry_formula_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def sign_l (e t H p c f : carrier_l ℳ) : Prop :=
  (p = e ∧ query_l H c f) ∨ (p = t ∧ ¬ query_l H c f)

def sign_m {Γ Δ : SortContext ℒ} (e t H p c f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (.equal p e) (query_m H c f)) (.conj (.equal p t) (.neg (query_m H c f)))

theorem sign_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (e t H p c f : Term ℒ Γ Δ .set) :
    (sign_m e t H p c f).satisfies η ↔
      sign_l (e.eval η) (t.eval η) (H.eval η) (p.eval η) (c.eval η) (f.eval η) := by
  simp only [sign_m, sign_l, Formula.satisfies, query_formula_l]

theorem positive_l {e t H c f : carrier_l ℳ} (het : e ≠ t) :
    sign_l e t H e c f ↔ query_l H c f := by
  simp only [sign_l, het, true_and, false_and, or_false]

theorem negative_l {e t H c f : carrier_l ℳ} (het : e ≠ t) :
    sign_l e t H t c f ↔ ¬ query_l H c f := by
  simp only [sign_l, Ne.symm het, true_and, false_and, false_or]

/-- 与非为真只需一个假子式；与非为假需要两个真子式。 -/
theorem nand_l {e t H p a b c f : carrier_l ℳ} (het : e ≠ t)
    (hc : query_l H c f ↔ ¬ (query_l H a f ∧ query_l H b f)) :
    sign_l e t H p c f ↔
      (p = e ∧ (sign_l e t H t a f ∨ sign_l e t H t b f)) ∨
        (p = t ∧ sign_l e t H e a f ∧ sign_l e t H e b f) := by
  classical
  rw [positive_l het, positive_l het, negative_l het, negative_l het]
  simp only [sign_l, hc]
  tauto

def valid_l (e t H D : carrier_l ℳ) : Prop :=
  ∀ p c f, entry_l D p c f → sign_l e t H p c f

def valid_m {Γ Δ : SortContext ℒ} (e t H D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := ((s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set <| .forallE .set <| .forallE .set <|
    .imp (entry_m (q D) (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
      (sign_m (q e) (q t) (q H) (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))

theorem valid_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (e t H D : Term ℒ Γ Δ .set) :
    (valid_m e t H D).satisfies η ↔ valid_l (e.eval η) (t.eval η) (H.eval η) (D.eval η) := by
  simp only [valid_m, valid_l, Formula.satisfies, entry_formula_l, sign_formula_l, Term.eval_weakenBound]
  rfl

theorem subset_l {e t H D E : carrier_l ℳ} (hDE : ThirdOrderSemantics.subset_l D E)
    (hE : valid_l e t H E) : valid_l e t H D :=
  fun p c f h => hE p c f (PowerlessTruthRecord.monotone_l hDE h)

/-- 集合多个分支的并保持真值可靠性，不要求分支族或记录集有限。 -/
theorem union_l {e t H A D : carrier_l ℳ}
    (hD : ∀ r, member_l ℳ r D ↔ ∃ E, member_l ℳ E A ∧ member_l ℳ r E)
    (hA : ∀ E, member_l ℳ E A → valid_l e t H E) : valid_l e t H D := by
  rintro p c f ⟨r, hr, h⟩
  obtain ⟨E, hE, hr⟩ := (hD r).mp hr
  exact hA E hE p c f ⟨r, hr, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthSign
