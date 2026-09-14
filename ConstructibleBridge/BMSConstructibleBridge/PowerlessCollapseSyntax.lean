import BMSConstructibleBridge.PowerlessInitialSegment
import BMSConstructibleBridge.PowerlessFunction

/-! # 内部良序坍缩的纯语言公式 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCollapseSyntax

open Logic FirstOrder ThirdOrderSemantics PowerlessInitialSegment

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def collapse_l (f D R : carrier_l ℳ) : Prop :=
  ∀ x y, value_l f x y → ∀ z, member_l ℳ z y ↔
    ∃ k, member_l ℳ k D ∧ value_l R k x ∧ value_l f k z

def collapse_m {Γ Δ : SortContext ℒ} (f D R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let f₂ := (f.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let f₄ := (f₂.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let D₂ := (D.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let D₄ := (D₂.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let R₂ := (R.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let R₄ := (R₂.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set (.forallE .set (.imp
    (SecondOrderObjectSyntax.value_m f₂ (.bvar (.there .here)) (.bvar .here))
    (.forallE .set (.iff (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
      (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) D₄)
        (.conj (SecondOrderObjectSyntax.value_m R₄ (.bvar .here) (.bvar (.there (.there (.there .here)))))
          (SecondOrderObjectSyntax.value_m f₄ (.bvar .here) (.bvar (.there .here))))))))))

theorem collapse_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f D R : Term ℒ Γ Δ .set) :
    (collapse_m f D R).satisfies η ↔ collapse_l (f.eval η) (D.eval η) (R.eval η) := by
  simp only [collapse_m, collapse_l, Formula.satisfies, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

/-- 在含端点 x 的初段上给出完整坍缩图；自由变量为 f、x、R、A。 -/
def stage_m : Formula ℒ [] [.set, .set, .set, .set] :=
  .existsE .set (.existsE .set (.conj
    (segment_m (.bvar (.there .here)) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there .here))) (.fvar (.there .here)))
    (.conj (SecondOrderObjectSyntax.map_m (.fvar .here) (.bvar (.there .here)) (.bvar .here))
      (collapse_m (.fvar .here) (.bvar (.there .here)) (.fvar (.there (.there .here)))))))

def stage_l (f x R A : carrier_l ℳ) : Prop :=
  ∃ D B, segment_l D A R x ∧ map_l f D B ∧ collapse_l f D R

theorem stage_formula_l (η : Env ℳ [] [.set, .set, .set, .set]) : stage_m.satisfies η ↔
    stage_l (η.freeVal .here) (η.freeVal (.there .here))
      (η.freeVal (.there (.there .here))) (η.freeVal (.there (.there (.there .here)))) := by
  simp only [stage_m, stage_l, Formula.satisfies, segment_formula_l, map_formula_l, collapse_formula_l]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCollapseSyntax
