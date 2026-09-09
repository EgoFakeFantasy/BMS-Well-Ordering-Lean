import YesMetaZFC.BMS.Reference

/-!
# BM4 合法数组

本文件把 Stage 0 的布尔规格提升为携带证明的对象。计算仍通过 `BMSArray` 完成，
定理接口则使用 `RectangularArray` 与 `ValidArray` 排除非数学输入。
-/

namespace YesMetaZFC
namespace BMS

/-- 纸面“array”的最低要求：所有列等高。 -/
structure RectangularArray where
  raw : BMSArray
  rectangular_eq : rectangular raw = true
deriving Repr

/-- BM4 闭包中采用的规范数组：矩形且已删除底部全零行。 -/
structure ValidArray extends RectangularArray where
  trimmed_eq : trimZeroRows raw = raw
deriving Repr

namespace RectangularArray

instance : Coe RectangularArray BMSArray := ⟨RectangularArray.raw⟩

@[ext]
theorem ext {left right : RectangularArray} (hRaw : left.raw = right.raw) :
    left = right := by
  cases left
  cases right
  simp_all

def columnCount (array : RectangularArray) : Nat :=
  BMS.columnCount array.raw

def entry? (array : RectangularArray) (column row : Nat) : Option Nat :=
  BMS.entry? array.raw column row

end RectangularArray

namespace ValidArray

instance : Coe ValidArray BMSArray := ⟨fun array => array.raw⟩

@[ext]
theorem ext {left right : ValidArray} (hRaw : left.raw = right.raw) :
    left = right := by
  cases left with
  | mk leftRectangular leftTrimmed =>
      cases right with
      | mk rightRectangular rightTrimmed =>
          have hRectangular : leftRectangular = rightRectangular :=
            RectangularArray.ext hRaw
          subst rightRectangular
          rfl

theorem normalized_eq (array : ValidArray) : normalized array.raw = true := by
  simp [normalized, array.rectangular_eq, array.trimmed_eq]

def columnCount (array : ValidArray) : Nat :=
  BMS.columnCount array.raw

def entry? (array : ValidArray) (column row : Nat) : Option Nat :=
  BMS.entry? array.raw column row

/-- 已有合法数组可以无损忘掉“已 trim”的证明。 -/
def toRectangular (array : ValidArray) : RectangularArray :=
  array.toRectangularArray

end ValidArray

/-- 布尔合法性检查成功时生成证明对象。 -/
def certify? (array : BMSArray) : Option ValidArray :=
  if hRectangular : rectangular array = true then
    if hTrimmed : trimZeroRows array = array then
      some ⟨⟨array, hRectangular⟩, hTrimmed⟩
    else
      none
  else
    none

@[simp]
theorem certify?_isSome_iff (array : BMSArray) :
    (certify? array).isSome = true ↔ normalized array = true := by
  by_cases hRectangular : rectangular array = true
  · by_cases hTrimmed : trimZeroRows array = array
    · simp [certify?, hRectangular, hTrimmed, normalized]
    · simp [certify?, hRectangular, hTrimmed, normalized]
  · simp [certify?, hRectangular, normalized]

theorem raw_of_certify?_eq_some {array : BMSArray} {certified : ValidArray}
    (hCertified : certify? array = some certified) :
    certified.raw = array := by
  unfold certify? at hCertified
  split at hCertified
  next hRectangular =>
    split at hCertified
    next hTrimmed =>
      simp only [Option.some.injEq] at hCertified
      subst certified
      rfl
    next => simp at hCertified
  next => simp at hCertified

end BMS
end YesMetaZFC
