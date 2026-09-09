import Lean.Elab.Tactic.Omega

/-!
# BM4 可执行参考规格

本文件固定 Hunter 论文 Definition 1.1 的计算含义。这里的 `BMSArray` 是“列的列表”，
每一列从第 `0` 行开始列出。参考实现刻意采用普通 `List`，便于生成回归测试；Stage 1
会在它之上增加合法性证明与面向定理的封装。
-/

namespace YesMetaZFC
namespace BMS

/-- BM4 数组：外层列表按从左到右排列列，内层列表按从上到下排列行。 -/
abbrev BMSArray := List (List Nat)

/-- 数组的列数。 -/
def columnCount (array : BMSArray) : Nat := array.length

/-- 第 `column` 列第 `row` 行的值。 -/
def entry? (array : BMSArray) (column row : Nat) : Option Nat :=
  array[column]?.bind (fun values => values[row]?)

/-- 所有列是否等高。 -/
def rectangular : BMSArray → Bool
  | [] => true
  | first :: rest => rest.all (fun column => column.length == first.length)

/-- 一列中最后一个非零坐标之后的长度。 -/
private def supportHeightAux : List Nat → Nat → Nat → Nat
  | [], _, result => result
  | value :: rest, index, result =>
      supportHeightAux rest (index + 1) (if value == 0 then result else index + 1)

/-- 从列表尾部递归计算的等价高度，只用于证明 `supportHeightAux` 的规格。 -/
private def relativeSupport : List Nat → Nat
  | [] => 0
  | value :: rest =>
      match relativeSupport rest with
      | 0 => if value == 0 then 0 else 1
      | height + 1 => height + 2

private theorem supportHeightAux_eq_relative (column : List Nat) (index result : Nat)
    (hResult : result ≤ index) :
    supportHeightAux column index result =
      if relativeSupport column = 0 then result else index + relativeSupport column := by
  induction column generalizing index result with
  | nil => simp [supportHeightAux, relativeSupport]
  | cons value rest ih =>
      have hNext : (if value == 0 then result else index + 1) ≤ index + 1 := by
        split <;> omega
      rw [supportHeightAux, ih (index + 1)
        (if value == 0 then result else index + 1) hNext]
      cases hTail : relativeSupport rest with
      | zero =>
          by_cases hValue : value = 0
          · simp [relativeSupport, hTail, hValue]
          · simp [relativeSupport, hTail, hValue]
      | succ height =>
          simp [relativeSupport, hTail]
          omega

private theorem relativeSupport_take_of_le (column : List Nat) (count : Nat)
    (hBound : relativeSupport column ≤ count) :
    relativeSupport (column.take count) = relativeSupport column := by
  induction column generalizing count with
  | nil => simp [relativeSupport]
  | cons value rest ih =>
      cases count with
      | zero =>
          have hZero : relativeSupport (value :: rest) = 0 := Nat.eq_zero_of_le_zero hBound
          simpa only [List.take_zero, relativeSupport] using hZero.symm
      | succ count =>
          cases hTail : relativeSupport rest with
          | zero =>
              have hTaken := ih count (by simp [hTail])
              simp [relativeSupport, hTail, hTaken]
          | succ height =>
              have hTailBound : height + 1 ≤ count := by
                simp [relativeSupport, hTail] at hBound
                omega
              have hTaken := ih count (by simpa [hTail] using hTailBound)
              simp [relativeSupport, hTail, hTaken]

private theorem row_lt_relativeSupport_of_getElem?_eq_some
    (column : List Nat) (row value : Nat)
    (hValue : column[row]? = some value) (hNonzero : value ≠ 0) :
    row < relativeSupport column := by
  induction column generalizing row with
  | nil => simp at hValue
  | cons head rest ih =>
      cases row with
      | zero =>
          simp at hValue
          subst head
          cases hTail : relativeSupport rest with
          | zero => simp [relativeSupport, hTail, hNonzero]
          | succ height => simp [relativeSupport, hTail]
      | succ row =>
          simp only [List.getElem?_cons_succ] at hValue
          have hTailLt := ih row hValue
          cases hTail : relativeSupport rest with
          | zero => simp [hTail] at hTailLt
          | succ height =>
              simp [relativeSupport, hTail]
              omega

def supportHeight (column : List Nat) : Nat :=
  supportHeightAux column 0 0

theorem supportHeight_eq_relativeSupport (column : List Nat) :
    supportHeight column = relativeSupport column := by
  unfold supportHeight
  rw [supportHeightAux_eq_relative column 0 0 (Nat.le_refl 0)]
  by_cases hZero : relativeSupport column = 0 <;> simp [hZero]

theorem supportHeight_le_length (column : List Nat) :
    supportHeight column ≤ column.length := by
  rw [supportHeight_eq_relativeSupport]
  induction column with
  | nil => simp [relativeSupport]
  | cons value rest ih =>
      cases hTail : relativeSupport rest with
      | zero =>
          by_cases hValue : value = 0 <;> simp [relativeSupport, hTail, hValue]
      | succ height =>
          simp [relativeSupport, hTail] at ih ⊢
          omega

theorem supportHeight_take_of_le (column : List Nat) (count : Nat)
    (hBound : supportHeight column ≤ count) :
    supportHeight (column.take count) = supportHeight column := by
  simp only [supportHeight_eq_relativeSupport] at hBound ⊢
  exact relativeSupport_take_of_le column count hBound

theorem row_lt_supportHeight_of_getElem?_eq_some
    (column : List Nat) (row value : Nat)
    (hValue : column[row]? = some value) (hNonzero : value ≠ 0) :
    row < supportHeight column := by
  rw [supportHeight_eq_relativeSupport]
  exact row_lt_relativeSupport_of_getElem?_eq_some column row value hValue hNonzero

theorem supportHeight_replicate_zero (count : Nat) :
    supportHeight (List.replicate count 0) = 0 := by
  rw [supportHeight_eq_relativeSupport]
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, relativeSupport, ih]

theorem supportHeight_replicate_one (count : Nat) :
    supportHeight (List.replicate count 1) = count := by
  rw [supportHeight_eq_relativeSupport]
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, relativeSupport, ih]
      cases count <;> rfl

/-- 在列底部附加一个零，不改变该列的支撑高度。 -/
theorem supportHeight_append_zero (column : List Nat) :
    supportHeight (column ++ [0]) = supportHeight column := by
  simp only [supportHeight_eq_relativeSupport]
  induction column with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.cons_append, relativeSupport]
      rw [ih]

/-- 删除底部全零行后应保留的行数。 -/
def trimHeight (array : BMSArray) : Nat :=
  array.foldl (fun result column => max result (supportHeight column)) 0

/-- 删除所有列共同的底部全零行。 -/
def trimZeroRows (array : BMSArray) : BMSArray :=
  array.map (fun column => column.take (trimHeight array))

/-- Stage 0 的规范数组判定：矩形且已删除底部全零行。 -/
def normalized (array : BMSArray) : Bool :=
  rectangular array && trimZeroRows array == array

/-- 从 `bound - 1` 向下寻找满足谓词的最大自然数。 -/
def greatestBelow? : Nat → (Nat → Bool) → Option Nat
  | 0, _ => none
  | bound + 1, predicate =>
      if predicate bound then some bound else greatestBelow? bound predicate

/-- 在至多 `fuel` 步内反复取 parent，结果从直接 parent 开始。 -/
def ancestorChain (parentFunction : Nat → Option Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | current, fuel + 1 =>
      match parentFunction current with
      | none => []
      | some parent => parent :: ancestorChain parentFunction parent fuel

/--
`parent array m i` 是第 `i` 列的 `m`-parent。定义按行号递归；在第 `m+1` 行，
候选列还必须是目标列的严格 `m`-ancestor。
-/
def parent : Nat → BMSArray → Nat → Option Nat
  | 0, array, target =>
      if target < array.length then
        greatestBelow? target (fun candidate =>
          match entry? array candidate 0, entry? array target 0 with
          | some left, some right => left < right
          | _, _ => false)
      else
        none
  | row + 1, array, target =>
      if target < array.length then
        let lowerAncestors := ancestorChain (parent row array) target target
        greatestBelow? target (fun candidate =>
          lowerAncestors.contains candidate &&
            match entry? array candidate (row + 1), entry? array target (row + 1) with
            | some left, some right => left < right
            | _, _ => false)
      else
        none

/-- 第 `ancestor` 列是否是第 `target` 列的严格 `row`-ancestor。 -/
def isAncestor (array : BMSArray) (row ancestor target : Nat) : Bool :=
  (ancestorChain (parent row array) target target).contains ancestor

/-- 最后一列存在 parent 的最大行号。 -/
def maximalParentRow (array : BMSArray) : Option Nat :=
  match array.length with
  | 0 => none
  | lastColumn + 1 =>
      let height := array[lastColumn]?.map List.length |>.getD 0
      greatestBelow? height (fun row => (parent row array lastColumn).isSome)

/-- 从 `start` 开始取至多 `count` 列。 -/
def slice (array : BMSArray) (start count : Nat) : BMSArray :=
  (array.drop start).take count

/-- `B₀` 中某个坐标是否在本次 expansion 中上升。 -/
def ascending (array : BMSArray) (m₀ parentColumn localColumn row : Nat) : Bool :=
  row < m₀ && (localColumn == 0 || isAncestor array row parentColumn (parentColumn + localColumn))

/-- 生成 `B₀` 的第 `copyNumber` 个副本。 -/
def copyBlock (array block : BMSArray) (m₀ parentColumn copyNumber : Nat)
    (lastColumn : List Nat) : BMSArray :=
  let firstColumn := block.head?.getD []
  block.mapIdx fun localColumn column =>
    column.mapIdx fun row value =>
      if ascending array m₀ parentColumn localColumn row then
        match firstColumn[row]?, lastColumn[row]? with
        | some firstValue, some lastValue =>
            value + copyNumber * (lastValue - firstValue)
        | _, _ => value
      else
        value

/-- Definition 1.1 中删除底部全零行之前的 expansion。 -/
def expandRaw (array : BMSArray) (index : Nat) : BMSArray :=
  match array.length with
  | 0 => []
  | lastIndex + 1 =>
      let lastColumn := array[lastIndex]?.getD []
      match maximalParentRow array with
      | none => array.take lastIndex
      | some m₀ =>
          match parent m₀ array lastIndex with
          | none => array.take lastIndex
          | some parentColumn =>
              let goodPart := array.take parentColumn
              let badPart := slice array parentColumn (lastIndex - parentColumn)
              let copies := (List.range (index + 1)).flatMap fun copyNumber =>
                copyBlock array badPart m₀ parentColumn copyNumber lastColumn
              goodPart ++ copies

/-- BM4 expansion `A[index]`。 -/
def expand (array : BMSArray) (index : Nat) : BMSArray :=
  trimZeroRows (expandRaw array index)

/-- 高度为 `height` 的 BM4 初始数组。 -/
def seed (height : Nat) : BMSArray :=
  [List.replicate height 0, List.replicate height 1]

/-- 自然数列的字典序比较，真前缀较小。 -/
def compareColumn : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | left :: leftRest, right :: rightRest =>
      match compare left right with
      | .eq => compareColumn leftRest rightRest
      | result => result

/-- 数组按列进行字典序比较，列本身也按字典序比较。 -/
def compareArray : BMSArray → BMSArray → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | left :: leftRest, right :: rightRest =>
      match compareColumn left right with
      | .eq => compareArray leftRest rightRest
      | result => result

end BMS
end YesMetaZFC
