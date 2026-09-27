import YesMetaZFC.BMS.ExpansionOrder
import BMSConstructibleBridge.FiniteHeight
import Mathlib.Logic.Relation

/-!
# 有限 expansion 轨迹的规范前缀比较

本模块用“规范前缀”`prefix_l` 替代对 `Acc Step` 的调用，比较同一根数组沿有限指标列展开的
终点。规范前缀裁剪零行，因此两端可以处在不同高度；它恰好等价于有限次零号 expansion。
这里不假设完整 BMS 的良基性、可比性或任何全局 `wellOrder` 出口，也不使用旧
`expansionPath_endpoints_comparable_of_accessible`。全部归纳都在宿主层自然数与列表长度上进行，
是宿主层陈述，不是 Z₂ 内部推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.FinitePathComparison

open StabilityFrame HeightDescent

set_option autoImplicit false

/-- 规范前缀：`A` 的全部列恰好是 `B` 前若干列的规范形。
列数相同的两端必相等，因此这一关系比未裁剪的原始前缀更强。 -/
def prefix_l (A B : ValidArray) : Prop :=
  A.raw.length ≤ B.raw.length ∧
    A.raw = trimZeroRows (B.raw.take A.raw.length)

theorem prefix_refl_l (A : ValidArray) : prefix_l A A :=
  ⟨Nat.le_refl _, by
    rw [List.take_length]
    exact A.trimmed_eq.symm⟩

theorem prefix_trans_l {A B C : ValidArray}
    (hAB : prefix_l A B) (hBC : prefix_l B C) : prefix_l A C := by
  have hLength := hAB.1
  have hUpper := hBC.1
  refine ⟨by omega,
    hAB.2.trans (by rw [hBC.2, trimZeroRows_take_trimZeroRows, List.take_take,
      Nat.min_eq_left hLength])⟩

/-- 规范前缀由精确次数的零号 expansion 达到。 -/
theorem eq_zeroIterate_of_prefix_l {A B : ValidArray} (hPrefix : prefix_l A B) :
    zeroIterate (B.raw.length - A.raw.length) B = A := by
  obtain ⟨hLength, hRaw⟩ := hPrefix
  apply ValidArray.ext
  rw [raw_zeroIterate,
    show B.raw.length - (B.raw.length - A.raw.length) = A.raw.length from by omega]
  exact hRaw.symm

/-- 合法次数的零号迭代结果都是原数组的规范前缀。 -/
theorem prefix_zeroIterate_l {B : ValidArray} (count : Nat)
    (hCount : count ≤ B.raw.length) : prefix_l (zeroIterate count B) B := by
  have hLength : (zeroIterate count B).raw.length = B.raw.length - count :=
    length_zeroIterate count B
  refine ⟨by omega, by rw [hLength]; exact raw_zeroIterate count B⟩

/-- 列数相同的规范前缀就是相等。 -/
theorem eq_of_prefix_l {A B : ValidArray} (hPrefix : prefix_l A B)
    (hReverse : B.raw.length ≤ A.raw.length) : A = B := by
  have hEqual : A.raw.length = B.raw.length :=
    Nat.le_antisymm hPrefix.1 hReverse
  apply ValidArray.ext
  rw [hPrefix.2, hEqual, List.take_length, B.trimmed_eq]

/-- 列数真减小的规范前缀给出严格下降。 -/
theorem strictDescent_of_prefix_l {A B : ValidArray} (hPrefix : prefix_l A B)
    (hLength : A.raw.length < B.raw.length) : StrictDescent A B := by
  rw [← eq_zeroIterate_of_prefix_l hPrefix]
  exact zeroIterate_strictDescent (by omega) (Nat.sub_le _ _)

/-- 有限次零号 expansion 给出实际 expansion 路径。 -/
theorem expansionPath_zeroIterate_l (count : Nat) {array : ValidArray}
    (hCount : count ≤ array.raw.length) :
    ExpansionPath array (zeroIterate count array) := by
  induction count with
  | zero => exact .refl _
  | succ count ih =>
      refine .trans (ih (by omega)) (.single ⟨0, ?_⟩)
      exact zeroIterate_succ_eq_expand count array

/-- 规范前缀总是给出从大到小的实际路径。 -/
theorem expansionPath_of_prefix_l {A B : ValidArray} (hPrefix : prefix_l A B) :
    ExpansionPath B A := by
  rw [← eq_zeroIterate_of_prefix_l hPrefix]
  exact expansionPath_zeroIterate_l _ (Nat.sub_le _ _)

/-- 端点不超过起点：规范前缀落在原生成顺序里。 -/
theorem descentOrEqual_of_prefix_l {A B : ValidArray} (hPrefix : prefix_l A B) :
    GeneratedDescentOrEqual A B := by
  rcases Nat.eq_or_lt_of_le hPrefix.1 with hEqual | hLess
  · exact Or.inl (eq_of_prefix_l hPrefix (Nat.le_of_eq hEqual.symm))
  · exact Or.inr (strictDescent_of_prefix_l hPrefix hLess)

/-- 同一根数组的相邻两个 expansion 之间是规范前缀。 -/
theorem prefix_expand_succ_l {array : ValidArray} (context : ExpansionContext array)
    (index : Nat) : prefix_l (array.expand index) (array.expand (index + 1)) := by
  have hBlock : context.blockLength ≤ (array.expand (index + 1)).raw.length := by
    rw [context.length_expand]
    rw [show index + 1 + 1 = (index + 1) + 1 from by omega, Nat.add_mul]
    omega
  have hPrefix := prefix_zeroIterate_l context.blockLength hBlock
  rw [context.zeroIterate_expand_succ index] at hPrefix
  exact hPrefix

/-- 同一根数组的 expansion 对索引在规范前缀意义下单调。 -/
theorem prefix_expand_l (array : ValidArray) {smallerIndex largerIndex : Nat}
    (hIndices : smallerIndex ≤ largerIndex) :
    prefix_l (array.expand smallerIndex) (array.expand largerIndex) := by
  cases hMaximal : maximalParentRow array.raw with
  | some maximalRow =>
      let context := Classical.choice
        (exists_expansionContext_of_maximalParentRow_eq_some hMaximal)
      obtain ⟨difference, rfl⟩ := Nat.exists_eq_add_of_le hIndices
      clear hIndices
      induction difference with
      | zero => exact prefix_refl_l _
      | succ difference ih =>
          exact prefix_trans_l ih (prefix_expand_succ_l context (smallerIndex + difference))
  | none =>
      have hEqual : array.expand smallerIndex = array.expand largerIndex := by
        apply ValidArray.ext
        simp [ValidArray.raw_expand, BMS.expand, expandRaw, hMaximal]
      rw [hEqual]
      exact prefix_refl_l _

/-- 屏障：列数仍严格更少时，规范前缀在任意一次 expansion 后保持。 -/
theorem prefix_expand_of_prefix_l {A B : ValidArray} (hPrefix : prefix_l A B)
    (hLength : A.raw.length < B.raw.length) (index : Nat) :
    prefix_l A (B.expand index) := by
  have hZero : prefix_l A (B.expand 0) := by
    refine ⟨by rw [ValidArray.length_expand_zero]; omega,
      hPrefix.2.trans (by rw [ValidArray.raw_expand_zero, trimZeroRows_take_trimZeroRows,
        List.take_take, Nat.min_eq_left (by omega)])⟩
  exact prefix_trans_l hZero (prefix_expand_l B (Nat.zero_le index))

/-- 沿实际指标列展开：`run_l` 按列表顺序逐次 expansion。 -/
def run_l (array : ValidArray) (indices : List Nat) : ValidArray :=
  indices.foldl (fun accumulated index => accumulated.expand index) array

@[simp]
theorem run_l_nil (array : ValidArray) : run_l array [] = array := rfl

@[simp]
theorem run_l_cons (array : ValidArray) (index : Nat) (indices : List Nat) :
    run_l (array.expand index) indices = run_l array (index :: indices) := rfl

theorem run_l_append {array : ValidArray} (first second : List Nat) :
    run_l array (first ++ second) = run_l (run_l array first) second := by
  induction first generalizing array with
  | nil => rfl
  | cons index indices ih => exact ih

/-- 屏障在整条有限轨迹上的形式：或者前缀保持，或者轨迹已穿过 `A`，
此时第二个终点恰是 `A` 沿 `s` 的某个后缀的展开。 -/
theorem prefix_run_l {A B : ValidArray} (hPrefix : prefix_l A B) (s : List Nat) :
    prefix_l A (run_l B s) ∨
      ∃ before after : List Nat, s = before ++ after ∧ run_l A after = run_l B s := by
  induction s generalizing A B with
  | nil => exact Or.inl hPrefix
  | cons index indices ih =>
      rcases Nat.eq_or_lt_of_le hPrefix.1 with hEqual | hLess
      · refine Or.inr ⟨[], index :: indices, by simp, ?_⟩
        exact congrArg (fun value => run_l value (index :: indices))
          (eq_of_prefix_l hPrefix (Nat.le_of_eq hEqual.symm))
      · refine (ih (prefix_expand_of_prefix_l hPrefix hLess index)).imp ?_ ?_
        · exact fun hP => hP
        · exact fun ⟨before, after, hEq, hRun⟩ =>
            ⟨index :: before, after, by rw [List.cons_append, hEq], hRun⟩

/-- 任意有限轨迹都是实际 expansion 路径。 -/
theorem expansionPath_run_l (array : ValidArray) (s : List Nat) :
    ExpansionPath array (run_l array s) := by
  induction s generalizing array with
  | nil => exact .refl _
  | cons index indices ih =>
      exact (ExpansionPath.single ⟨index, rfl⟩).trans (ih (array.expand index))

@[simp]
theorem run_l_singleton (array : ValidArray) (index : Nat) :
    run_l array [index] = array.expand index := rfl

/-- 三歧性交换两端。 -/
private theorem symm_trichotomy_l {α : Type} {r : α → α → Prop} {first second : α}
    (h : first = second ∨ r first second ∨ r second first) :
    second = first ∨ r second first ∨ r first second := by
  rcases h with hEqual | hFirst | hSecond
  · exact Or.inl hEqual.symm
  · exact Or.inr (Or.inr hFirst)
  · exact Or.inr (Or.inl hSecond)

/-- 同根数组沿两条有限轨迹的终点可三歧比较。归纳只在轨迹长度和上进行，
不对 `Step` 归纳，也不消费 `Acc Step` 假设。 -/
theorem run_trichotomy_l : ∀ bound : Nat, ∀ (array : ValidArray)
    (first second : List Nat), first.length + second.length ≤ bound →
    run_l array first = run_l array second ∨
      StrictDescent (run_l array first) (run_l array second) ∨
        StrictDescent (run_l array second) (run_l array first) := by
  intro bound
  induction bound with
  | zero =>
      intro array first second hLength
      rcases first with _ | ⟨_, _⟩
      · rcases second with _ | ⟨_, _⟩
        · exact Or.inl rfl
        · simp only [List.length_nil, List.length_cons] at hLength
          omega
      · simp only [List.length_cons] at hLength
        omega
  | succ bound ih =>
      intro array first second hLength
      cases first with
      | nil =>
          rw [run_l_nil]
          rcases descentOrEqual_of_expansionPath (expansionPath_run_l array second) with
            hEqual | hDescent
          · exact Or.inl hEqual.symm
          · exact Or.inr (Or.inr hDescent)
      | cons firstIndex firstTail =>
          cases second with
          | nil =>
              rw [run_l_nil]
              rcases descentOrEqual_of_expansionPath
                  (expansionPath_run_l array (firstIndex :: firstTail)) with
                hEqual | hDescent
              · exact Or.inl hEqual
              · exact Or.inr (Or.inl hDescent)
          | cons secondIndex secondTail =>
              have hLeft : run_l array (firstIndex :: firstTail) =
                  run_l (array.expand firstIndex) firstTail := rfl
              have hRight : run_l array (secondIndex :: secondTail) =
                  run_l (array.expand secondIndex) secondTail := rfl
              rw [hLeft, hRight]
              simp only [List.length_cons] at hLength
              rcases Nat.le_total firstIndex secondIndex with hLess | hGreater
              · have hPrefix : prefix_l (array.expand firstIndex)
                    (array.expand secondIndex) := prefix_expand_l array hLess
                rcases prefix_run_l hPrefix secondTail with hKept | hCrossed
                · rcases descentOrEqual_of_expansionPath
                      (ExpansionPath.trans (expansionPath_of_prefix_l hKept)
                        (expansionPath_run_l (array.expand firstIndex) firstTail)) with
                    hEqual | hDescent
                  · exact Or.inl hEqual
                  · exact Or.inr (Or.inl hDescent)
                · obtain ⟨before, after, hEq, hRun⟩ := hCrossed
                  have hLen : secondTail.length = before.length + after.length := by
                    rw [hEq, List.length_append]
                  have hBound : firstTail.length + after.length ≤ bound := by omega
                  rw [← hRun]
                  exact ih (array.expand firstIndex) firstTail after hBound
              · have hPrefix : prefix_l (array.expand secondIndex)
                    (array.expand firstIndex) := prefix_expand_l array hGreater
                rcases prefix_run_l hPrefix firstTail with hKept | hCrossed
                · rcases descentOrEqual_of_expansionPath
                      (ExpansionPath.trans (expansionPath_of_prefix_l hKept)
                        (expansionPath_run_l (array.expand secondIndex) secondTail)) with
                    hEqual | hDescent
                  · exact Or.inl hEqual.symm
                  · exact Or.inr (Or.inr hDescent)
                · obtain ⟨before, after, hEq, hRun⟩ := hCrossed
                  have hLen : firstTail.length = before.length + after.length := by
                    rw [hEq, List.length_append]
                  have hBound : secondTail.length + after.length ≤ bound := by omega
                  rw [← hRun]
                  exact symm_trichotomy_l
                    (ih (array.expand secondIndex) secondTail after hBound)

/-- 任意有限 expansion 路径恰好由一条实际指标轨迹实现。 -/
theorem exists_run_l_of_expansionPath {larger smaller : ValidArray}
    (path : ExpansionPath larger smaller) :
    ∃ indices : List Nat, run_l larger indices = smaller := by
  induction path with
  | refl => exact ⟨[], rfl⟩
  | tail pathToMiddle last ih =>
      obtain ⟨indices, hRun⟩ := ih
      obtain ⟨index, hEdge⟩ := last
      refine ⟨indices ++ [index], by
        rw [run_l_append, hRun, run_l_singleton]
        exact hEdge.symm⟩

/-- 同一起点的两条有限 expansion 路径终点三歧可比，不需要起点的可及性。 -/
theorem expansionPath_endpoints_comparable_l
    {larger first second : ValidArray}
    (pathFirst : ExpansionPath larger first) (pathSecond : ExpansionPath larger second) :
    first = second ∨ StrictDescent first second ∨ StrictDescent second first := by
  obtain ⟨firstIndices, hFirst⟩ := exists_run_l_of_expansionPath pathFirst
  obtain ⟨secondIndices, hSecond⟩ := exists_run_l_of_expansionPath pathSecond
  have hBound := run_trichotomy_l (firstIndices.length + secondIndices.length)
    larger firstIndices secondIndices (Nat.le_refl _)
  rw [hFirst, hSecond] at hBound
  exact hBound

/-- 任意两个生成数组三歧可比：先把两条 seed 轨迹接到较高的 seed，再消费上面的
同根可比性。这里既不使用起点的 `Acc Step`，也不使用旧的可及性出口。 -/
theorem generated_comparable_l (first second : GeneratedArray) :
    first = second ∨ GeneratedStrictDescent first second ∨
      GeneratedStrictDescent second first := by
  rcases generated_iff_seed_path.mp first.2 with ⟨n, p⟩
  rcases generated_iff_seed_path.mp second.2 with ⟨m, q⟩
  have p₀ : ExpansionPath (validSeed (max n m)) (validSeed n) :=
    RepresentationDescentSystem.expansionPath_validSeed_of_le (Nat.le_max_left _ _)
  have q₀ : ExpansionPath (validSeed (max n m)) (validSeed m) :=
    RepresentationDescentSystem.expansionPath_validSeed_of_le (Nat.le_max_right _ _)
  rcases expansionPath_endpoints_comparable_l (p₀.trans p) (q₀.trans q) with
    hEqual | hDescent | hReverse
  · exact Or.inl (Subtype.ext hEqual)
  · exact Or.inr (Or.inl (RepresentationDescentSystem.generatedStrictDescent_of_strictDescent
      second.2 hDescent))
  · exact Or.inr (Or.inr (RepresentationDescentSystem.generatedStrictDescent_of_strictDescent
      first.2 hReverse))

/-- 当前高度有界载体上的原严格下降限制。 -/
def boundedDescent_l (N : Nat) (a b : FiniteHeight.carrier_l N) : Prop :=
  GeneratedStrictDescent a.1 b.1

/-- 有限生成下降不会离开有界载体：较大端点高度不超过 `N` 时，路径上每个中间点
也不超过 `N`，因此整条下降可以逐点搬进 `FiniteHeight.carrier_l N`。 -/
theorem transGen_bounded_l {N : Nat} {larger : GeneratedArray}
    (hLarger : height_l larger.1 ≤ N) (smaller : GeneratedArray)
    (h : GeneratedStrictDescent smaller larger) :
    ∃ hSmaller : height_l smaller.1 ≤ N,
      Relation.TransGen (FiniteHeight.step_l N) ⟨smaller, hSmaller⟩ ⟨larger, hLarger⟩ := by
  refine Relation.TransGen.head_induction_on
      (motive := fun a _ => ∃ hA : height_l a.1 ≤ N,
        Relation.TransGen (FiniteHeight.step_l N) ⟨a, hA⟩ ⟨larger, hLarger⟩) h ?single ?head
  · intro smaller step
    have hSmaller : height_l smaller.1 ≤ N := Nat.le_trans (step_le_l step) hLarger
    exact ⟨hSmaller, Relation.TransGen.single
      (show FiniteHeight.step_l N ⟨smaller, hSmaller⟩ ⟨larger, hLarger⟩ from step)⟩
  · intro smaller middle step _ ih
    obtain ⟨hMiddle, hRest⟩ := ih
    have hSmaller : height_l smaller.1 ≤ N := Nat.le_trans (step_le_l step) hMiddle
    exact ⟨hSmaller, Relation.TransGen.head
      (show FiniteHeight.step_l N ⟨smaller, hSmaller⟩ ⟨middle, hMiddle⟩ from step) hRest⟩

/-- 有界一步良基性给出有界载体上严格下降的良基性；不假设全局一步良基。 -/
theorem bounded_wf_l (N : Nat) (hStep : WellFounded (FiniteHeight.step_l N)) :
    WellFounded (boundedDescent_l N) :=
  Subrelation.wf (q := boundedDescent_l N)
    (r := Relation.TransGen (FiniteHeight.step_l N))
    (fun {a b} hDescent => (transGen_bounded_l b.2 a.1 hDescent).2)
    hStep.transGen

theorem bounded_transitive_l {N : Nat}
    {first second third : FiniteHeight.carrier_l N}
    (hFirst : boundedDescent_l N first second)
    (hSecond : boundedDescent_l N second third) :
    boundedDescent_l N first third := Relation.TransGen.trans hFirst hSecond

theorem bounded_trichotomy_l (N : Nat)
    (first second : FiniteHeight.carrier_l N) :
    first = second ∨ boundedDescent_l N first second ∨
      boundedDescent_l N second first := by
  rcases generated_comparable_l first.1 second.1 with hEqual | hDescent | hReverse
  · exact Or.inl (Subtype.ext hEqual)
  · exact Or.inr (Or.inl hDescent)
  · exact Or.inr (Or.inr hReverse)

/-- 条件出口：只假设有界载体上的一步良基，即得当前高度不超过 `N` 的严格良序。 -/
theorem bounded_wellOrder_l (N : Nat) (hStep : WellFounded (FiniteHeight.step_l N)) :
    StrictWellOrder (FiniteHeight.carrier_l N) (boundedDescent_l N) :=
  ⟨bounded_wf_l N hStep, bounded_transitive_l, bounded_trichotomy_l N⟩

/-- 同一出口的逐高度层形式：只需要 `N` 以下每个高度层的一步良基性。 -/
theorem bounded_wellOrder_of_fibers_l (N : Nat)
    (h : ∀ n, n ≤ N → WellFounded (HeightDescent.step_l n)) :
    StrictWellOrder (FiniteHeight.carrier_l N) (boundedDescent_l N) :=
  bounded_wellOrder_l N ((FiniteHeight.wf_iff_l N).mpr h)

end YesMetaZFC.BMS.ConstructibleBridge.FinitePathComparison
