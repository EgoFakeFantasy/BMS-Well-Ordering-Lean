import BMSConstructibleBridge.ExternalDelta0Translation
import BMSConstructibleBridge.StageStructure

/-!
# 把固定公式有界地相对化到已命名的可构造层

若 `θ < top`，则集合 `L_θ` 本身属于 `L_top`。因此任意固定外部成员公式都可
把全部量词限制到这个显式集合，得到一个真正的 `Delta0` 公式；在 `L_top` 中
求值该公式，恰等价于在内层结构 `L_θ` 中求值原公式。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/-- 任意固定外部公式相对化后得到真正的有界公式。 -/
def stageRelativizedDelta_l {arity : Nat} (formula : FOFormula arity) :
    Delta0Formula (arity + 1) :=
  Delta0Formula.relativize formula

/-- 内层赋值连同它的层集合一起提升到外层载体。 -/
noncomputable def stageRelativizedOuterAssignment_l
    {θ top : Ordinal.{u}} (hθtop : θ < top) {arity : Nat}
    (assignment : Tuple (StageCarrier θ) arity) :
    Tuple (StageCarrier top) (arity + 1) :=
  tupleCons ⟨LStageZF θ, LStageZF_mem_of_lt hθtop⟩
    (fun index => lStageInclusion hθtop.le (assignment index))

/-- 提升赋值去掉子类型证明后，只是在原赋值前加入 `L_θ`。 -/
theorem stageRelativizedOuterAssignment_value_l
    {θ top : Ordinal.{u}} (hθtop : θ < top) {arity : Nat}
    (assignment : Tuple (StageCarrier θ) arity) :
    Delta0Formula.val
        (stageRelativizedOuterAssignment_l hθtop assignment) =
      tupleCons (LStageZF θ) (Delta0Formula.val assignment) := by
  funext position
  refine Fin.cases ?_ (fun index => ?_) position
  · rfl
  · rfl

/--
层相对化的通用语义桥。该定理不要求原公式具有任何 Lévy 复杂度；复杂度已经
由显式的 `L_θ` 界吸收到 `Delta0Formula.relativize` 中。
-/
theorem satisfiesIn_stageRelativizedFormula_iff_l
    {θ top : Ordinal.{u}} (hθtop : θ < top) {arity : Nat}
    (formula : FOFormula arity)
    (assignment : Tuple (StageCarrier θ) arity) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (stageRelativizedDelta_l formula).toFO
        (tupleCons (LStageZF θ) (Delta0Formula.val assignment)) ↔
      Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u}) formula
        (Delta0Formula.val assignment) := by
  let outerAssignment : Tuple (StageCarrier top) (arity + 1) :=
    stageRelativizedOuterAssignment_l hθtop assignment
  have hOuter := Constructible.Model.satisfies_stageCarrier_iff_satisfiesIn
    (stageRelativizedDelta_l formula).toFO outerAssignment
  rw [Delta0Formula.satisfies_toFO] at hOuter
  have hOuterValue :
      (fun index => (outerAssignment index).1) =
        tupleCons (LStageZF θ) (Delta0Formula.val assignment) := by
    exact stageRelativizedOuterAssignment_value_l hθtop assignment
  rw [hOuterValue] at hOuter
  have hAbsolute := Delta0Formula.satisfies_absolute
    (LStageZF_isTransitive top) (stageRelativizedDelta_l formula)
    outerAssignment
  rw [stageRelativizedOuterAssignment_value_l] at hAbsolute
  have hRelativized := Delta0Formula.satisfies_relativize
    (LStageZF θ) formula assignment
  have hInner := Constructible.Model.satisfies_stageCarrier_iff_satisfiesIn
    formula assignment
  change FOFormula.Satisfies
      (fun left right : StageCarrier θ => left.1 ∈ right.1)
      formula assignment ↔
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u}) formula
      (Delta0Formula.val assignment) at hInner
  exact hOuter.symm.trans <| hAbsolute.trans <|
    hRelativized.trans hInner

/-- 相对化公式翻译到原生成员语言后仍是 `Delta0`。 -/
theorem translatedStageRelativizedFormula_isDelta0_l
    {arity : Nat} (formula : FOFormula arity) :
    Logic.FirstOrder.Formula.IsDelta0 StabilityFrame.membershipLevyBound
      (translateExternalFormula (stageRelativizedDelta_l formula).toFO) :=
  translateExternalDelta0_isDelta0_l (stageRelativizedDelta_l formula)

end YesMetaZFC.BMS.ConstructibleBridge
