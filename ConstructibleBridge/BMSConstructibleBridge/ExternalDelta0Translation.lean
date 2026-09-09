import BMSConstructibleBridge.ExternalLevyHierarchy
import ConstructibleUniverse.SetTheory.ZFC.Constructible.Delta0

/-!
# 保持真正有界量词的翻译

外部 `Delta0Formula` 的量词自带集合界。翻译后，新变量位于 bound 零号，旧的
界变量严格位于正编号，因此该界不含新变量。这一事实让外部的有界公式直接
取得原生 `IsDelta0` 证书，不必把有界量词当成额外的 Lévy 层。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

open Logic FirstOrder
open StabilityFrame
open Constructible

/-- 去掉有界标记与变量重命名交换。 -/
theorem externalDelta0_toFO_rename_l {arity targetArity : Nat}
    (φ : Delta0Formula arity) (rename : Fin arity → Fin targetArity) :
    (φ.rename rename).toFO = φ.toFO.rename rename := by
  induction φ generalizing targetArity with
  | mem left right => rfl
  | eq left right => rfl
  | neg φ ih => simp only [Delta0Formula.rename, Delta0Formula.toFO,
      FOFormula.rename, ih]
  | conj φ ψ ihφ ihψ => simp only [Delta0Formula.rename, Delta0Formula.toFO,
      FOFormula.rename, ihφ, ihψ]
  | boundedEx index φ ih =>
      simp only [Delta0Formula.rename, Delta0Formula.toFO, FOFormula.boundedEx,
        FOFormula.rename, ih, FOFormula.liftRename, Delta0Formula.liftRename,
        Fin.lastCases_last, Fin.lastCases_castSucc]

/-- 外部有界公式经同一语法翻译后仍为原生 Delta0。 -/
theorem translateExternalDelta0_isDelta0_l {arity : Nat}
    (φ : Delta0Formula arity) :
    FirstOrder.Formula.IsDelta0 membershipLevyBound
      (translateExternalFormula φ.toFO) := by
  induction φ with
  | mem left right => exact .rel _ _
  | eq left right => exact .equal _ _
  | neg φ ih => exact .neg ih
  | conj φ ψ ihφ ihψ => exact .conj ihφ ihψ
  | boundedEx index φ ih =>
      simp only [Delta0Formula.toFO, FOFormula.boundedEx,
        translateExternalFormula, externalBoundVariable_last,
        externalBoundVariable_castSucc]
      exact FirstOrder.Formula.IsDelta0.bounded_exists
        (.bvar (externalBoundVariable index)) ih

/-- 有界公式可放入每一有限 Sigma 层。 -/
theorem translateExternalDelta0_isSigmaFinite_l {arity : Nat}
    (level : Nat) (φ : Delta0Formula arity) :
    FirstOrder.Formula.IsSigmaFinite membershipLevyBound level
      (translateExternalFormula φ.toFO) :=
  .delta0 (translateExternalDelta0_isDelta0_l φ)

/-- 有界公式也可放入每一有限 Pi 层。 -/
theorem translateExternalDelta0_isPiFinite_l {arity : Nat}
    (level : Nat) (φ : Delta0Formula arity) :
    FirstOrder.Formula.IsPiFinite membershipLevyBound level
      (translateExternalFormula φ.toFO) :=
  .delta0 (translateExternalDelta0_isDelta0_l φ)

/-- 有界语法与原生翻译之间的直接满足关系等价。 -/
theorem satisfies_translateExternalDelta0_iff_l
    {α : Ordinal} {hNonempty : Nonempty (StageCarrier α)}
    {arity : Nat} (φ : Delta0Formula arity)
    (env : FirstOrder.Env (lStageStructure α hNonempty)
      (externalBoundContext arity) []) :
    FirstOrder.Formula.satisfies env (translateExternalFormula φ.toFO) ↔
      Delta0Formula.Satisfies
        (fun left right : StageCarrier α => left.1 ∈ right.1)
        φ (externalBoundTuple env) := by
  rw [satisfies_translateExternalFormula_iff, Delta0Formula.satisfies_toFO]

/-- 旧外部片段的 Pi 零层不含任何以无界存在量词为根的公式。 -/
theorem not_externalPiZero_exists_l {arity : Nat} (φ : FOFormula (arity + 1)) :
    ¬ ExternalIsPiFinite 0 (.ex φ) := by
  intro hφ
  cases hφ

/-- 因此该片段也不接受零层的否定存在式，即使这个存在量词有集合界。 -/
theorem not_externalSigmaZero_neg_exists_l {arity : Nat}
    (φ : FOFormula (arity + 1)) :
    ¬ ExternalIsSigmaFinite 0 (.neg (.ex φ)) := by
  intro hφ
  cases hφ with
  | neg hBody => exact not_externalPiZero_exists_l φ hBody

/-- 用真正的有界量词给出旧外部片段与原生分类的句法区别。 -/
def externalBoundedNegationExample_l : Delta0Formula 1 :=
  .neg (.boundedEx 0 (.mem 1 0))

/-- 此例属于原生 Delta0，但不属于旧外部 Sigma 零层；不能省略层级兼容证明。 -/
theorem externalFiniteFragment_not_nativeDelta0_l :
    FirstOrder.Formula.IsDelta0 membershipLevyBound
      (translateExternalFormula externalBoundedNegationExample_l.toFO) ∧
    ¬ ExternalIsSigmaFinite 0 externalBoundedNegationExample_l.toFO := by
  constructor
  · exact translateExternalDelta0_isDelta0_l _
  · exact not_externalSigmaZero_neg_exists_l _

end YesMetaZFC.BMS.ConstructibleBridge
