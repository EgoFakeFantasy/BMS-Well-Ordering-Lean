import BMSConstructibleBridge.StabilitySemantics
import BMSConstructibleBridge.ExternalExistentialClosure
import BMSConstructibleBridge.StageElementarity
import BMSConstructibleBridge.StageOrdinalDelta
import YesMetaZFC.BMS.OrdinalReflectionSyntax
import ConstructibleUniverse.SetTheory.ZFC.Constructible.Condensation

/-!
# Hunter 有限反射图的固定元数编译

本模块把一次 `FiniteReflectionInput` 中实际为真的有限关系编译为一个外部成员公式。
源层只保留下方参数；上方有限族在目标层充当存在见证，反射后成为所需图像。
所有坐标由 `Fin` 内在约束，随后整个公式一次性翻译到新版 YesMetaZFC 的 bound
上下文，因而不存在旧自由变量编号的越界分支。
-/

universe u

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open Constructible
open StabilityFrame

/-- 有限反射矩阵中下方参数的坐标。 -/
def finiteReflectionLowerCoordinate_l {lowerCount upperCount : Nat}
    (index : Fin lowerCount) : Fin (lowerCount + upperCount) :=
  Fin.castAdd upperCount index

/-- 有限反射矩阵中候选图像的坐标。 -/
def finiteReflectionImageCoordinate_l {lowerCount upperCount : Nat}
    (index : Fin upperCount) : Fin (lowerCount + upperCount) :=
  Fin.natAdd lowerCount index

/-- 非空上下文中的恒真有界公式。 -/
def externalTruthAt_l {arity : Nat} (default : Fin arity) : FOFormula arity :=
  .eq default default

/-- `Fin count` 索引的右结合有限合取；末尾附加一个恒真原子。 -/
def externalConjunctionFin_l {arity : Nat} (default : Fin arity) :
    {count : Nat} → (Fin count → FOFormula arity) → FOFormula arity
  | 0, _ => externalTruthAt_l default
  | count + 1, formula =>
      .conj (formula (Fin.last count))
        (externalConjunctionFin_l default
          (fun index => formula index.castSucc))

@[simp]
theorem satisfies_externalTruthAt_l {Carrier : Type u}
    (membership : Carrier → Carrier → Prop) {arity : Nat}
    (default : Fin arity) (assignment : Tuple Carrier arity) :
    FOFormula.Satisfies membership (externalTruthAt_l default) assignment :=
  rfl

@[simp]
theorem satisfies_externalConjunctionFin_l {Carrier : Type u}
    (membership : Carrier → Carrier → Prop) {arity count : Nat}
    (default : Fin arity) (formula : Fin count → FOFormula arity)
    (assignment : Tuple Carrier arity) :
    FOFormula.Satisfies membership
        (externalConjunctionFin_l default formula) assignment ↔
      ∀ index, FOFormula.Satisfies membership (formula index) assignment := by
  induction count with
  | zero =>
      constructor
      · intro _ index
        exact Fin.elim0 index
      · intro _
        exact satisfies_externalTruthAt_l membership default assignment
  | succ count ih =>
      simp only [externalConjunctionFin_l, FOFormula.Satisfies, ih]
      constructor
      · rintro ⟨hLast, hPrior⟩ index
        refine Fin.lastCases hLast (fun prior => hPrior prior) index
      · intro hAll
        exact ⟨hAll (Fin.last count), fun prior => hAll prior.castSucc⟩

/-- 按元层真值选入一个关系原子；未选中时放入恒真式。 -/
noncomputable def externalSelect_l {arity : Nat} (default : Fin arity)
    (condition : Prop) (formula : FOFormula arity) : FOFormula arity := by
  classical
  exact if condition then formula else externalTruthAt_l default

@[simp]
theorem satisfies_externalSelect_l {Carrier : Type u}
    (membership : Carrier → Carrier → Prop) {arity : Nat}
    (default : Fin arity) (condition : Prop) (formula : FOFormula arity)
    (assignment : Tuple Carrier arity) :
    FOFormula.Satisfies membership
        (externalSelect_l default condition formula) assignment ↔
      (condition → FOFormula.Satisfies membership formula assignment) := by
  classical
  by_cases hCondition : condition
  · simp [externalSelect_l, hCondition]
  · simp [externalSelect_l, hCondition]

/-- 把二元稳定公式放到有限反射矩阵的两个指定坐标。 -/
def stableBetweenAt_l {arity : Nat}
    (formula : FOFormula 2) (left right : Fin arity) : FOFormula arity :=
  formula.rename ![left, right]

/-- 把一元 ambient 稳定公式放到有限反射矩阵的指定坐标。 -/
def stableToUniverseAt_l {arity : Nat}
    (formula : FOFormula 1) (value : Fin arity) : FOFormula arity :=
  formula.rename ![value]

/-- 恒真原子属于每个真正有界的外部 `Sigma` 层。 -/
theorem externalTruthAt_isSigmaFinite_l {arity level : Nat}
    (default : Fin arity) :
    ExternalBoundedIsSigmaFinite_l level (externalTruthAt_l default) := by
  exact .delta0 (.eq default default)

/-- 有限合取保持真正有界的外部 `Sigma` 层。 -/
theorem externalConjunctionFin_isSigmaFinite_l
    {arity count level : Nat} (default : Fin arity)
    (formula : Fin count → FOFormula arity)
    (hFormula : ∀ index,
      ExternalBoundedIsSigmaFinite_l level (formula index)) :
    ExternalBoundedIsSigmaFinite_l level
      (externalConjunctionFin_l default formula) := by
  induction count with
  | zero => exact externalTruthAt_isSigmaFinite_l default
  | succ count ih =>
      exact .conj (hFormula (Fin.last count))
        (ih (fun index => formula index.castSucc)
          (fun index => hFormula index.castSucc))

/-- 按元层真值选取关系原子不改变其 `Sigma` 层级。 -/
theorem externalSelect_isSigmaFinite_l {arity level : Nat}
    (default : Fin arity) (condition : Prop) (formula : FOFormula arity)
    (hFormula : ExternalBoundedIsSigmaFinite_l level formula) :
    ExternalBoundedIsSigmaFinite_l level
      (externalSelect_l default condition formula) := by
  classical
  by_cases hCondition : condition
  · simpa [externalSelect_l, hCondition] using hFormula
  · simpa [externalSelect_l, hCondition] using
      externalTruthAt_isSigmaFinite_l (level := level) default

/-- 二元稳定公式的坐标重命名保持其 `Sigma` 层级。 -/
theorem stableBetweenAt_isSigmaFinite_l
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop))
    {arity reflectionLevel : Nat} (level : Nat) (left right : Fin arity) :
    ExternalBoundedIsSigmaFinite_l
      (stageStabilityLevyLevel_l reflectionLevel)
      (stableBetweenAt_l (data.stableBetweenFormula level) left right) := by
  exact (data.stableBetween_isSigmaFinite reflectionLevel level).rename
    ![left, right]

/-- 一元 ambient 稳定公式的坐标重命名保持其 `Sigma` 层级。 -/
theorem stableToUniverseAt_isSigmaFinite_l
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop))
    {arity reflectionLevel : Nat} (level : Nat)
    (hLevel : level < reflectionLevel) (value : Fin arity) :
    ExternalBoundedIsSigmaFinite_l
      (stageStabilityLevyLevel_l reflectionLevel)
      (stableToUniverseAt_l (data.stableToUniverseFormula level) value) := by
  exact (data.stableToUniverse_isSigmaFinite reflectionLevel level hLevel).rename
    ![value]

/-- 二元稳定公式放入坐标后的精确语义。 -/
theorem satisfies_stableBetweenAt_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop))
    {arity : Nat} (assignment : Tuple (StageCarrier top) arity)
    (level : Nat) (left right : Fin arity)
    (hLeft : (assignment left).1.IsOrdinal)
    (hRight : (assignment right).1.IsOrdinal) :
    FOFormula.Satisfies
        (fun first second : StageCarrier top => first.1 ∈ second.1)
        (stableBetweenAt_l (data.stableBetweenFormula level) left right)
        assignment ↔
      stageStableLt level (assignment left).1.rank
        (assignment right).1.rank := by
  rw [stableBetweenAt_l, FOFormula.satisfies_rename]
  have hTuple :
      (fun index => assignment (![left, right] index)) =
        ![assignment left, assignment right] := by
    funext index
    fin_cases index <;> rfl
  rw [hTuple]
  exact data.satisfies_stableBetween_iff hTop hOmega level hLeft hRight

/-- 一元 ambient 稳定公式放入坐标后的精确语义。 -/
theorem satisfies_stableToUniverseAt_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop))
    {arity : Nat} (assignment : Tuple (StageCarrier top) arity)
    (level : Nat) (value : Fin arity)
    (hValue : (assignment value).1.IsOrdinal) :
    FOFormula.Satisfies
        (fun first second : StageCarrier top => first.1 ∈ second.1)
        (stableToUniverseAt_l (data.stableToUniverseFormula level) value)
        assignment ↔
      stageStableLt level (assignment value).1.rank top := by
  rw [stableToUniverseAt_l, FOFormula.satisfies_rename]
  have hTuple :
      (fun index => assignment (![value] index)) = ![assignment value] := by
    funext index
    fin_cases index
    rfl
  rw [hTuple]
  exact data.satisfies_stableToUniverse_iff hTop hOmega level hValue

/-- 候选图像都是序数。 -/
def finiteReflectionOrdinalBlock_l {lowerCount upperCount : Nat}
    (default : Fin (lowerCount + upperCount)) :
    FOFormula (lowerCount + upperCount) :=
  externalConjunctionFin_l default fun upperIndex =>
    finiteReflectionIsOrdinalDelta_l.toFO.rename
      ![finiteReflectionImageCoordinate_l upperIndex]

/-- “候选图像是序数”块属于任意外部 `Sigma` 层。 -/
theorem finiteReflectionOrdinalBlock_isSigmaFinite_l
    {lowerCount upperCount level : Nat}
    (default : Fin (lowerCount + upperCount)) :
    ExternalBoundedIsSigmaFinite_l level
      (finiteReflectionOrdinalBlock_l default) := by
  apply externalConjunctionFin_isSigmaFinite_l
  intro upperIndex
  rw [← externalDelta0_toFO_rename_l]
  exact .delta0
    (finiteReflectionIsOrdinalDelta_l.rename
      ![finiteReflectionImageCoordinate_l upperIndex])

/-- “候选图像是序数”块的精确语义。 -/
theorem satisfies_finiteReflectionOrdinalBlock_iff_l
    {top : Ordinal.{u}} {lowerCount upperCount : Nat}
    (default : Fin (lowerCount + upperCount))
    (assignment : Tuple (StageCarrier top) (lowerCount + upperCount)) :
    FOFormula.Satisfies
        (fun first second : StageCarrier top => first.1 ∈ second.1)
        (finiteReflectionOrdinalBlock_l default) assignment ↔
      ∀ upperIndex,
        (assignment (finiteReflectionImageCoordinate_l upperIndex)).1.IsOrdinal := by
  rw [finiteReflectionOrdinalBlock_l,
    satisfies_externalConjunctionFin_l]
  constructor
  · intro hBlock upperIndex
    have hFormula := hBlock upperIndex
    rw [FOFormula.satisfies_rename,
      finiteReflectionIsOrdinalDelta_toFO_l] at hFormula
    rw [Constructible.Model.satisfies_stageCarrier_iff_satisfiesIn]
      at hFormula
    have hTuple :
        (fun index : Fin 1 =>
          (assignment (![
            finiteReflectionImageCoordinate_l upperIndex] index)).1) =
          ![(assignment
            (finiteReflectionImageCoordinate_l upperIndex)).1] := by
      funext index
      fin_cases index
      rfl
    rw [hTuple,
      Constructible.MostowskiCollapse.CondensationHull.satisfiesIn_isOrdinal_iff
      (Constructible.LStageZF_isTransitive top)
      (assignment (finiteReflectionImageCoordinate_l upperIndex)).1
      (assignment (finiteReflectionImageCoordinate_l upperIndex)).2]
      at hFormula
    exact hFormula
  · intro hOrdinal upperIndex
    rw [FOFormula.satisfies_rename,
      finiteReflectionIsOrdinalDelta_toFO_l]
    rw [Constructible.Model.satisfies_stageCarrier_iff_satisfiesIn]
    have hTuple :
        (fun index : Fin 1 =>
          (assignment (![
            finiteReflectionImageCoordinate_l upperIndex] index)).1) =
          ![(assignment
            (finiteReflectionImageCoordinate_l upperIndex)).1] := by
      funext index
      fin_cases index
      rfl
    rw [hTuple,
      Constructible.MostowskiCollapse.CondensationHull.satisfiesIn_isOrdinal_iff
      (Constructible.LStageZF_isTransitive top)
      (assignment (finiteReflectionImageCoordinate_l upperIndex)).1
      (assignment (finiteReflectionImageCoordinate_l upperIndex)).2]
    exact hOrdinal upperIndex

/-- 每个候选图像严格高于全部下方参数。 -/
def finiteReflectionLowerOrderBlock_l {lowerCount upperCount : Nat}
    (default : Fin (lowerCount + upperCount)) :
    FOFormula (lowerCount + upperCount) :=
  externalConjunctionFin_l default fun lowerIndex =>
    externalConjunctionFin_l default fun upperIndex =>
      .mem (finiteReflectionLowerCoordinate_l lowerIndex)
        (finiteReflectionImageCoordinate_l upperIndex)

/-- “图像高于下方参数”块属于任意外部 `Sigma` 层。 -/
theorem finiteReflectionLowerOrderBlock_isSigmaFinite_l
    {lowerCount upperCount level : Nat}
    (default : Fin (lowerCount + upperCount)) :
    ExternalBoundedIsSigmaFinite_l level
      (finiteReflectionLowerOrderBlock_l default) := by
  apply externalConjunctionFin_isSigmaFinite_l
  intro lowerIndex
  apply externalConjunctionFin_isSigmaFinite_l
  intro upperIndex
  exact .delta0 (.mem
    (finiteReflectionLowerCoordinate_l lowerIndex)
    (finiteReflectionImageCoordinate_l upperIndex))

/-- “图像高于下方参数”块的精确语义。 -/
theorem satisfies_finiteReflectionLowerOrderBlock_iff_l
    {top : Ordinal.{u}} {lowerCount upperCount : Nat}
    (default : Fin (lowerCount + upperCount))
    (assignment : Tuple (StageCarrier top) (lowerCount + upperCount)) :
    FOFormula.Satisfies
        (fun first second : StageCarrier top => first.1 ∈ second.1)
        (finiteReflectionLowerOrderBlock_l default) assignment ↔
      ∀ lowerIndex upperIndex,
        (assignment (finiteReflectionLowerCoordinate_l lowerIndex)).1 ∈
          (assignment (finiteReflectionImageCoordinate_l upperIndex)).1 := by
  simp only [finiteReflectionLowerOrderBlock_l,
    satisfies_externalConjunctionFin_l, FOFormula.Satisfies]

/-- 保留下方参数到原上方族之间全部实际稳定关系。 -/
noncomputable def finiteReflectionLowerStabilityBlock_l
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop))
    (default : Fin (lowerCount + upperCount)) :
    FOFormula (lowerCount + upperCount) :=
  externalConjunctionFin_l default fun lowerIndex =>
    externalConjunctionFin_l default fun upperIndex =>
      externalConjunctionFin_l default fun level : Fin input.stabilityCutoff =>
        externalSelect_l default
          (stageStableLt level (input.lower lowerIndex) (input.upper upperIndex))
          (stableBetweenAt_l (data.stableBetweenFormula level)
            (finiteReflectionLowerCoordinate_l lowerIndex)
            (finiteReflectionImageCoordinate_l upperIndex))

/-- 下方参数到上方族的稳定关系块具有反射所需复杂度。 -/
theorem finiteReflectionLowerStabilityBlock_isSigmaFinite_l
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop))
    (default : Fin (lowerCount + upperCount)) :
    ExternalBoundedIsSigmaFinite_l
      (stageStabilityLevyLevel_l input.level)
      (finiteReflectionLowerStabilityBlock_l
        (input := input) data default) := by
  apply externalConjunctionFin_isSigmaFinite_l
  intro lowerIndex
  apply externalConjunctionFin_isSigmaFinite_l
  intro upperIndex
  apply externalConjunctionFin_isSigmaFinite_l
  intro level
  apply externalSelect_isSigmaFinite_l
  exact stableBetweenAt_isSigmaFinite_l data level _ _

/-- 下方参数到上方族的稳定关系块的精确语义。 -/
theorem satisfies_finiteReflectionLowerStabilityBlock_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop))
    (default : Fin (lowerCount + upperCount))
    (assignment : Tuple (StageCarrier top) (lowerCount + upperCount))
    (hLowerOrdinal : ∀ lowerIndex,
      (assignment (finiteReflectionLowerCoordinate_l lowerIndex)).1.IsOrdinal)
    (hImageOrdinal : ∀ upperIndex,
      (assignment (finiteReflectionImageCoordinate_l upperIndex)).1.IsOrdinal) :
    FOFormula.Satisfies
        (fun first second : StageCarrier top => first.1 ∈ second.1)
        (finiteReflectionLowerStabilityBlock_l
          (input := input) data default) assignment ↔
      ∀ lowerIndex upperIndex (level : Fin input.stabilityCutoff),
        stageStableLt level (input.lower lowerIndex) (input.upper upperIndex) →
          stageStableLt level
            (assignment
              (finiteReflectionLowerCoordinate_l lowerIndex)).1.rank
            (assignment
              (finiteReflectionImageCoordinate_l upperIndex)).1.rank := by
  simp only [finiteReflectionLowerStabilityBlock_l,
    satisfies_externalConjunctionFin_l, satisfies_externalSelect_l]
  constructor
  · intro hBlock lowerIndex upperIndex level hStable
    have hFormula := hBlock lowerIndex upperIndex level hStable
    exact (satisfies_stableBetweenAt_iff_l hTop hOmega data assignment level
      _ _ (hLowerOrdinal lowerIndex) (hImageOrdinal upperIndex)).mp hFormula
  · intro hBlock lowerIndex upperIndex level hStable
    apply (satisfies_stableBetweenAt_iff_l hTop hOmega data assignment level
      _ _ (hLowerOrdinal lowerIndex) (hImageOrdinal upperIndex)).mpr
    exact hBlock lowerIndex upperIndex level hStable

/-- 保留原上方族的全部实际严格序关系。 -/
noncomputable def finiteReflectionUpperOrderBlock_l
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (default : Fin (lowerCount + upperCount)) :
    FOFormula (lowerCount + upperCount) :=
  externalConjunctionFin_l default fun left =>
    externalConjunctionFin_l default fun right =>
      externalSelect_l default (input.upper left < input.upper right)
        (.mem (finiteReflectionImageCoordinate_l left)
          (finiteReflectionImageCoordinate_l right))

/-- 上方族严格序关系块属于任意外部 `Sigma` 层。 -/
theorem finiteReflectionUpperOrderBlock_isSigmaFinite_l
    {lowerCount upperCount level : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (default : Fin (lowerCount + upperCount)) :
    ExternalBoundedIsSigmaFinite_l level
      (finiteReflectionUpperOrderBlock_l (input := input) default) := by
  apply externalConjunctionFin_isSigmaFinite_l
  intro left
  apply externalConjunctionFin_isSigmaFinite_l
  intro right
  apply externalSelect_isSigmaFinite_l
  exact .delta0 (.mem
    (@finiteReflectionImageCoordinate_l lowerCount upperCount left)
    (@finiteReflectionImageCoordinate_l lowerCount upperCount right))

/-- 上方族严格序关系块的精确语义。 -/
theorem satisfies_finiteReflectionUpperOrderBlock_iff_l
    {top : Ordinal.{u}} {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (default : Fin (lowerCount + upperCount))
    (assignment : Tuple (StageCarrier top) (lowerCount + upperCount)) :
    FOFormula.Satisfies
        (fun first second : StageCarrier top => first.1 ∈ second.1)
        (finiteReflectionUpperOrderBlock_l (input := input) default)
        assignment ↔
      ∀ left right, input.upper left < input.upper right →
        (assignment (finiteReflectionImageCoordinate_l left)).1 ∈
          (assignment (finiteReflectionImageCoordinate_l right)).1 := by
  simp only [finiteReflectionUpperOrderBlock_l,
    satisfies_externalConjunctionFin_l, satisfies_externalSelect_l,
    FOFormula.Satisfies]

/-- 保留原上方族内部的全部实际稳定关系。 -/
noncomputable def finiteReflectionUpperStabilityBlock_l
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (data : ConstructibleStabilityFormulaData stageStableLt)
    (default : Fin (lowerCount + upperCount)) :
    FOFormula (lowerCount + upperCount) :=
  externalConjunctionFin_l default fun left =>
    externalConjunctionFin_l default fun right =>
      externalConjunctionFin_l default fun level : Fin input.stabilityCutoff =>
        externalSelect_l default
          (stageStableLt level (input.upper left) (input.upper right))
          (stableBetweenAt_l (data.stableBetweenFormula level)
            (finiteReflectionImageCoordinate_l left)
            (finiteReflectionImageCoordinate_l right))

/-- 上方族内部稳定关系块具有反射所需复杂度。 -/
theorem finiteReflectionUpperStabilityBlock_isSigmaFinite_l
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (data : ConstructibleStabilityFormulaData stageStableLt)
    (default : Fin (lowerCount + upperCount)) :
    ExternalBoundedIsSigmaFinite_l
      (stageStabilityLevyLevel_l input.level)
      (finiteReflectionUpperStabilityBlock_l
        (input := input) data default) := by
  apply externalConjunctionFin_isSigmaFinite_l
  intro left
  apply externalConjunctionFin_isSigmaFinite_l
  intro right
  apply externalConjunctionFin_isSigmaFinite_l
  intro level
  apply externalSelect_isSigmaFinite_l
  exact stableBetweenAt_isSigmaFinite_l data level _ _

/-- 上方族内部稳定关系块的精确语义。 -/
theorem satisfies_finiteReflectionUpperStabilityBlock_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop))
    (default : Fin (lowerCount + upperCount))
    (assignment : Tuple (StageCarrier top) (lowerCount + upperCount))
    (hImageOrdinal : ∀ upperIndex,
      (assignment (finiteReflectionImageCoordinate_l upperIndex)).1.IsOrdinal) :
    FOFormula.Satisfies
        (fun first second : StageCarrier top => first.1 ∈ second.1)
        (finiteReflectionUpperStabilityBlock_l
          (input := input) data default) assignment ↔
      ∀ left right (level : Fin input.stabilityCutoff),
        stageStableLt level (input.upper left) (input.upper right) →
          stageStableLt level
            (assignment (finiteReflectionImageCoordinate_l left)).1.rank
            (assignment (finiteReflectionImageCoordinate_l right)).1.rank := by
  simp only [finiteReflectionUpperStabilityBlock_l,
    satisfies_externalConjunctionFin_l, satisfies_externalSelect_l]
  constructor
  · intro hBlock left right level hStable
    have hFormula := hBlock left right level hStable
    exact (satisfies_stableBetweenAt_iff_l hTop hOmega data assignment level
      _ _ (hImageOrdinal left) (hImageOrdinal right)).mp hFormula
  · intro hBlock left right level hStable
    apply (satisfies_stableBetweenAt_iff_l hTop hOmega data assignment level
      _ _ (hImageOrdinal left) (hImageOrdinal right)).mpr
    exact hBlock left right level hStable

/-- 把上方族到目标层的低阶稳定关系反射成图像到当前宇宙的关系。 -/
noncomputable def finiteReflectionAmbientBlock_l
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (data : ConstructibleStabilityFormulaData stageStableLt)
    (default : Fin (lowerCount + upperCount)) :
    FOFormula (lowerCount + upperCount) :=
  externalConjunctionFin_l default fun upperIndex =>
    externalConjunctionFin_l default fun level : Fin input.level =>
      externalSelect_l default
        (stageStableLt level (input.upper upperIndex) input.upperBound)
        (stableToUniverseAt_l (data.stableToUniverseFormula level)
          (finiteReflectionImageCoordinate_l upperIndex))

/-- 上方族到 ambient 层的低阶稳定关系块具有反射所需复杂度。 -/
theorem finiteReflectionAmbientBlock_isSigmaFinite_l
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (data : ConstructibleStabilityFormulaData stageStableLt)
    (default : Fin (lowerCount + upperCount)) :
    ExternalBoundedIsSigmaFinite_l
      (stageStabilityLevyLevel_l input.level)
      (finiteReflectionAmbientBlock_l (input := input) data default) := by
  apply externalConjunctionFin_isSigmaFinite_l
  intro upperIndex
  apply externalConjunctionFin_isSigmaFinite_l
  intro level
  apply externalSelect_isSigmaFinite_l
  exact stableToUniverseAt_isSigmaFinite_l data level level.isLt _

/-- 上方族到 ambient 层的稳定关系块的精确语义。 -/
theorem satisfies_finiteReflectionAmbientBlock_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop))
    (default : Fin (lowerCount + upperCount))
    (assignment : Tuple (StageCarrier top) (lowerCount + upperCount))
    (hImageOrdinal : ∀ upperIndex,
      (assignment (finiteReflectionImageCoordinate_l upperIndex)).1.IsOrdinal) :
    FOFormula.Satisfies
        (fun first second : StageCarrier top => first.1 ∈ second.1)
        (finiteReflectionAmbientBlock_l (input := input) data default)
        assignment ↔
      ∀ upperIndex (level : Fin input.level),
        stageStableLt level (input.upper upperIndex) input.upperBound →
          stageStableLt level
            (assignment (finiteReflectionImageCoordinate_l upperIndex)).1.rank
            top := by
  simp only [finiteReflectionAmbientBlock_l,
    satisfies_externalConjunctionFin_l, satisfies_externalSelect_l]
  constructor
  · intro hBlock upperIndex level hStable
    have hFormula := hBlock upperIndex level hStable
    exact (satisfies_stableToUniverseAt_iff_l hTop hOmega data assignment level
      _ (hImageOrdinal upperIndex)).mp hFormula
  · intro hBlock upperIndex level hStable
    apply (satisfies_stableToUniverseAt_iff_l hTop hOmega data assignment level
      _ (hImageOrdinal upperIndex)).mpr
    exact hBlock upperIndex level hStable

/-- 六块关系事实组成的有限反射矩阵。 -/
noncomputable def finiteReflectionMatrix_l
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (data : ConstructibleStabilityFormulaData stageStableLt)
    (hUpper : 0 < upperCount) : FOFormula (lowerCount + upperCount) :=
  let default : Fin (lowerCount + upperCount) :=
    @finiteReflectionImageCoordinate_l lowerCount upperCount
      (⟨0, hUpper⟩ : Fin upperCount)
  .conj (finiteReflectionOrdinalBlock_l default)
    (.conj (finiteReflectionLowerOrderBlock_l default)
      (.conj (finiteReflectionLowerStabilityBlock_l
          (input := input) data default)
        (.conj (finiteReflectionUpperOrderBlock_l
            (input := input) default)
          (.conj (finiteReflectionUpperStabilityBlock_l
              (input := input) data default)
            (finiteReflectionAmbientBlock_l
              (input := input) data default)))))

/-- 关闭全部候选图像坐标，仅留下下方参数。 -/
noncomputable def finiteReflectionFormula_l
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (data : ConstructibleStabilityFormulaData stageStableLt)
    (hUpper : 0 < upperCount) : FOFormula lowerCount :=
  externalExistentialClosure_l upperCount
    (finiteReflectionMatrix_l (input := input) data hUpper)

/-- 六块矩阵语义的逐项、可审计表述。 -/
structure FiniteReflectionMatrixFacts_l
    {lowerCount upperCount : Nat}
    (input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount)
    (top : Ordinal.{u})
    (assignment : Tuple (StageCarrier top) (lowerCount + upperCount)) : Prop where
  image_isOrdinal : ∀ upperIndex,
    (assignment (finiteReflectionImageCoordinate_l upperIndex)).1.IsOrdinal
  lower_mem_image : ∀ lowerIndex upperIndex,
    (assignment (finiteReflectionLowerCoordinate_l lowerIndex)).1 ∈
      (assignment (finiteReflectionImageCoordinate_l upperIndex)).1
  preserves_lower_stableLt : ∀ lowerIndex upperIndex
      (level : Fin input.stabilityCutoff),
    stageStableLt level (input.lower lowerIndex) (input.upper upperIndex) →
      stageStableLt level
        (assignment (finiteReflectionLowerCoordinate_l lowerIndex)).1.rank
        (assignment (finiteReflectionImageCoordinate_l upperIndex)).1.rank
  preserves_upper_lt : ∀ left right,
    input.upper left < input.upper right →
      (assignment (finiteReflectionImageCoordinate_l left)).1 ∈
        (assignment (finiteReflectionImageCoordinate_l right)).1
  preserves_upper_stableLt : ∀ left right
      (level : Fin input.stabilityCutoff),
    stageStableLt level (input.upper left) (input.upper right) →
      stageStableLt level
        (assignment (finiteReflectionImageCoordinate_l left)).1.rank
        (assignment (finiteReflectionImageCoordinate_l right)).1.rank
  reflects_to_top : ∀ upperIndex (level : Fin input.level),
    stageStableLt level (input.upper upperIndex) input.upperBound →
      stageStableLt level
        (assignment (finiteReflectionImageCoordinate_l upperIndex)).1.rank top

/-- 有限反射矩阵满足当且仅当六块关系事实逐项成立。 -/
theorem satisfies_finiteReflectionMatrix_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop))
    (hUpper : 0 < upperCount)
    (assignment : Tuple (StageCarrier top) (lowerCount + upperCount))
    (hLowerOrdinal : ∀ lowerIndex,
      (assignment (finiteReflectionLowerCoordinate_l lowerIndex)).1.IsOrdinal) :
    FOFormula.Satisfies
        (fun first second : StageCarrier top => first.1 ∈ second.1)
        (finiteReflectionMatrix_l (input := input) data hUpper) assignment ↔
      FiniteReflectionMatrixFacts_l input top assignment := by
  let default : Fin (lowerCount + upperCount) :=
    @finiteReflectionImageCoordinate_l lowerCount upperCount
      (⟨0, hUpper⟩ : Fin upperCount)
  simp only [finiteReflectionMatrix_l, FOFormula.Satisfies]
  rw [satisfies_finiteReflectionOrdinalBlock_iff_l]
  constructor
  · rintro ⟨hOrdinal, hLowerOrder, hLowerStable,
      hUpperOrder, hUpperStable, hAmbient⟩
    rw [satisfies_finiteReflectionLowerOrderBlock_iff_l] at hLowerOrder
    rw [satisfies_finiteReflectionLowerStabilityBlock_iff_l
      hTop hOmega data default assignment hLowerOrdinal hOrdinal]
      at hLowerStable
    rw [satisfies_finiteReflectionUpperOrderBlock_iff_l] at hUpperOrder
    rw [satisfies_finiteReflectionUpperStabilityBlock_iff_l
      hTop hOmega data default assignment hOrdinal] at hUpperStable
    rw [satisfies_finiteReflectionAmbientBlock_iff_l
      hTop hOmega data default assignment hOrdinal] at hAmbient
    exact ⟨hOrdinal, hLowerOrder, hLowerStable,
      hUpperOrder, hUpperStable, hAmbient⟩
  · intro hFacts
    refine ⟨hFacts.image_isOrdinal, ?_⟩
    rw [satisfies_finiteReflectionLowerOrderBlock_iff_l]
    refine ⟨hFacts.lower_mem_image, ?_⟩
    rw [satisfies_finiteReflectionLowerStabilityBlock_iff_l
      hTop hOmega data default assignment hLowerOrdinal hFacts.image_isOrdinal]
    refine ⟨hFacts.preserves_lower_stableLt, ?_⟩
    rw [satisfies_finiteReflectionUpperOrderBlock_iff_l]
    refine ⟨hFacts.preserves_upper_lt, ?_⟩
    rw [satisfies_finiteReflectionUpperStabilityBlock_iff_l
      hTop hOmega data default assignment hFacts.image_isOrdinal]
    refine ⟨hFacts.preserves_upper_stableLt, ?_⟩
    rw [satisfies_finiteReflectionAmbientBlock_iff_l
      hTop hOmega data default assignment hFacts.image_isOrdinal]
    exact hFacts.reflects_to_top

/-- 六块有限关系图整体具有 `Sigma_(input.level+1)` 复杂度。 -/
theorem finiteReflectionMatrix_isSigmaFinite_l
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (data : ConstructibleStabilityFormulaData stageStableLt)
    (hUpper : 0 < upperCount) :
    ExternalBoundedIsSigmaFinite_l
      (stageStabilityLevyLevel_l input.level)
      (finiteReflectionMatrix_l (input := input) data hUpper) := by
  unfold finiteReflectionMatrix_l
  repeat' apply ExternalBoundedIsSigmaFinite_l.conj
  · exact finiteReflectionOrdinalBlock_isSigmaFinite_l _
  · exact finiteReflectionLowerOrderBlock_isSigmaFinite_l _
  · exact finiteReflectionLowerStabilityBlock_isSigmaFinite_l data _
  · exact finiteReflectionUpperOrderBlock_isSigmaFinite_l _
  · exact finiteReflectionUpperStabilityBlock_isSigmaFinite_l data _
  · exact finiteReflectionAmbientBlock_isSigmaFinite_l data _

/-- 关闭图像坐标后，内在翻译可直接交给 `OrdinalElementarityWitness`。 -/
theorem finiteReflectionFormula_isSigmaFinite_l
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (data : ConstructibleStabilityFormulaData stageStableLt)
    (hUpper : 0 < upperCount) :
    Logic.FirstOrder.Formula.IsSigmaFinite membershipLevyBound
      (stageStabilityLevyLevel_l input.level)
      (translateExternalFormula
        (finiteReflectionFormula_l (input := input) data hUpper)) := by
  apply translateExternalExistentialClosure_isSigmaFinite_l
  exact (finiteReflectionMatrix_isSigmaFinite_l data hUpper).translate

/-- 外部公式本身也保留同一复杂度，供 `stageStableLt` 的初等性直接消费。 -/
theorem finiteReflectionFormula_external_isSigmaFinite_l
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput constructibleStabilityFrame
      lowerCount upperCount}
    (data : ConstructibleStabilityFormulaData stageStableLt)
    (hUpper : 0 < upperCount) :
    ExternalBoundedIsSigmaFinite_l
      (stageStabilityLevyLevel_l input.level)
      (finiteReflectionFormula_l (input := input) data hUpper) := by
  apply externalExistentialClosure_isSigmaFinite_l
  exact finiteReflectionMatrix_isSigmaFinite_l data hUpper

end ConstructibleBridge
end BMS
end YesMetaZFC
