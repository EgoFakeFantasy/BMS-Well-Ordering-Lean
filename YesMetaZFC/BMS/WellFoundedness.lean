import YesMetaZFC.BMS.FiniteReflection
import YesMetaZFC.BMS.ExpansionOrder

/-!
# 由稳定表示下降推出 BM4 良基性

本文件形式化 Hunter Theorem 2.7 的最后一个、与具体序数模型无关的部分：只要每个
seed 有有界稳定表示，并且每个非平凡 expansion 都能把表示上界严格下推，BM4 的
一步关系就在生成数组上良基。证明直接沿标签上界的 accessibility 归纳，无需选择
“最小表示”，因而避开不必要的全局选择。
-/

namespace YesMetaZFC
namespace BMS

universe u

namespace StabilityFrame

/-- 生成数组组成的证明携带子类型。 -/
abbrev GeneratedArray := {array : ValidArray // Generated array}

/-- 生成数组上的一步 expansion 关系。 -/
def GeneratedStep (smaller larger : GeneratedArray) : Prop :=
  Step smaller.1 larger.1

/-- 生成数组上的非空有限 expansion 下降。 -/
def GeneratedStrictDescent (smaller larger : GeneratedArray) : Prop :=
  Relation.TransGen GeneratedStep smaller larger

/-- 本项目使用的 strict well-order 接口。良基性已蕴含非自反性。 -/
structure StrictWellOrder (Carrier : Type) (relation : Carrier → Carrier → Prop) :
    Prop where
  wellFounded : WellFounded relation
  transitive : ∀ {first second third},
    relation first second → relation second third → relation first third
  trichotomy : ∀ first second,
    first = second ∨ relation first second ∨ relation second first

/-- Stage 4 实际消费的稳定表示下降接口。 -/
structure RepresentationDescentSystem {Label : Type u}
    (frame : StabilityFrame Label) where
  seed_bounded : ∀ height,
    ∃ bound, ∃ representation : StableRepresentation frame (validSeed height),
      representation.BoundedBy bound
  expand_bounded : ∀ {array : ValidArray} (index : Nat)
      {bound : Label} (representation : StableRepresentation frame array),
    representation.BoundedBy bound →
    array.expand index ≠ array →
      ∃ smallerBound,
        frame.lt smallerBound bound ∧
          ∃ expandedRepresentation :
              StableRepresentation frame (array.expand index),
            expandedRepresentation.BoundedBy smallerBound

namespace RepresentationDescentSystem

/-- 每个生成数组都有某个有界稳定表示。 -/
theorem exists_bounded_of_generated {Label : Type u}
    {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame)
    {array : ValidArray} (hGenerated : Generated array) :
    ∃ bound, ∃ representation : StableRepresentation frame array,
      representation.BoundedBy bound := by
  induction hGenerated with
  | seed height => exact system.seed_bounded height
  | @expand array hGenerated index ih =>
      rcases ih with ⟨bound, representation, hBounded⟩
      by_cases hEqual : array.expand index = array
      · rw [hEqual]
        exact ⟨bound, representation, hBounded⟩
      · rcases system.expand_bounded index representation hBounded hEqual with
          ⟨smallerBound, _, expandedRepresentation, hExpandedBounded⟩
        exact ⟨smallerBound, expandedRepresentation, hExpandedBounded⟩

/-- 标签上界可达时，任何由它界定的生成数组对 `Step` 都可达。 -/
theorem accessible_of_bounded {Label : Type u}
    {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) :
    ∀ {bound : Label}, Acc frame.lt bound →
      ∀ {array : ValidArray}, Generated array →
        ∀ representation : StableRepresentation frame array,
          representation.BoundedBy bound → Acc Step array := by
  intro bound hAccessible
  induction hAccessible with
  | intro bound hPredecessor ih =>
      intro array hGenerated representation hBounded
      apply Acc.intro array
      intro smaller hStep
      rcases hStep.1 with ⟨index, hExpanded⟩
      subst smaller
      rcases system.expand_bounded index representation hBounded hStep.2 with
        ⟨smallerBound, hSmallerBound, expandedRepresentation,
          hExpandedBounded⟩
      exact ih smallerBound hSmallerBound
        (generated_of_step hGenerated hStep) expandedRepresentation
        hExpandedBounded

/-- Hunter Theorem 2.7 的良基性结论。 -/
theorem step_wellFoundedOn_generated {Label : Type u}
    {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) :
    WellFounded GeneratedStep := by
  constructor
  intro array
  rcases system.exists_bounded_of_generated array.2 with
    ⟨bound, representation, hBounded⟩
  have hAccessible := system.accessible_of_bounded
    (frame.lt_wellFounded.apply bound) array.2 representation hBounded
  exact InvImage.accessible Subtype.val hAccessible

private theorem no_infinite_chain_from_accessible
    {Carrier : Type} {relation : Carrier → Carrier → Prop}
    {start : Carrier} (hAccessible : Acc relation start) :
    ¬ ∃ chain : Nat → Carrier,
      chain 0 = start ∧
        ∀ index, relation (chain (index + 1)) (chain index) := by
  induction hAccessible with
  | intro current hPredecessor ih =>
      rintro ⟨chain, hStart, hDescend⟩
      have hFirst : relation (chain 1) current := by
        rw [← hStart]
        simpa using hDescend 0
      apply ih (chain 1) hFirst
      refine ⟨fun index => chain (index + 1), rfl, ?_⟩
      intro index
      simpa [Nat.add_assoc] using hDescend (index + 1)

/-- 等价的“没有无限下降链”接口。 -/
theorem no_infinite_step_chain {Label : Type u}
    {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) :
    ¬ ∃ chain : Nat → {array : ValidArray // Generated array},
      ∀ index, Step (chain (index + 1)).1 (chain index).1 := by
  intro hChain
  rcases hChain with ⟨chain, hStep⟩
  have hWellFounded := system.step_wellFoundedOn_generated
  exact no_infinite_chain_from_accessible
    (hWellFounded.apply (chain 0)) ⟨chain, rfl, hStep⟩

/-- 非空有限 expansion 下降同样良基。 -/
theorem strictDescent_wellFoundedOn_generated {Label : Type u}
    {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) :
    WellFounded GeneratedStrictDescent := by
  exact system.step_wellFoundedOn_generated.transGen

/-- 非空有限下降关系具有传递性。 -/
theorem generatedStrictDescent_transitive :
    ∀ {first second third : GeneratedArray},
      GeneratedStrictDescent first second →
      GeneratedStrictDescent second third →
      GeneratedStrictDescent first third := by
  intro first second third hFirst hSecond
  exact Relation.TransGen.trans hFirst hSecond

/-- 原数组上的严格下降可提升为生成子类型上的严格下降。 -/
theorem generatedStrictDescent_of_strictDescent
    {smaller larger : ValidArray} (hGenerated : Generated larger)
    (descent : StrictDescent smaller larger) :
    GeneratedStrictDescent
      ⟨smaller, strictDescent_generated hGenerated descent⟩
      ⟨larger, hGenerated⟩ := by
  induction descent generalizing hGenerated with
  | single step =>
      exact Relation.TransGen.single step
  | tail prior step ih =>
      have hMiddle := strictDescent_generated hGenerated prior
      have hPrior := ih hGenerated
      have hLast : GeneratedStrictDescent
          ⟨_, generated_of_step hMiddle step⟩ ⟨_, hMiddle⟩ :=
        Relation.TransGen.single step
      exact generatedStrictDescent_transitive hLast hPrior

/-- 较高 seed 到较低 seed 存在一条有限 expansion 路径。 -/
theorem expansionPath_validSeed_of_le {lowerHeight upperHeight : Nat}
    (hHeight : lowerHeight ≤ upperHeight) :
    ExpansionPath (validSeed upperHeight) (validSeed lowerHeight) := by
  rcases Nat.lt_or_eq_of_le hHeight with hStrict | hEqual
  · exact expansionPath_of_strictDescent
      (validSeed_strictDescent hStrict)
  · subst upperHeight
    exact .refl _

/--
表示下降系统使任意两个生成数组可比。两条生成路径先提升到共同的最高 seed，
再在该 seed 的 accessibility 证明上使用有限路径链性。
-/
theorem generated_comparable {Label : Type u}
    {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame)
    (first second : GeneratedArray) :
    first = second ∨ GeneratedStrictDescent first second ∨
      GeneratedStrictDescent second first := by
  rcases generated_iff_seed_path.mp first.2 with
    ⟨firstHeight, hFirstPath⟩
  rcases generated_iff_seed_path.mp second.2 with
    ⟨secondHeight, hSecondPath⟩
  let commonHeight := max firstHeight secondHeight
  have hFirstSeedPath : ExpansionPath (validSeed commonHeight)
      (validSeed firstHeight) :=
    expansionPath_validSeed_of_le (Nat.le_max_left _ _)
  have hSecondSeedPath : ExpansionPath (validSeed commonHeight)
      (validSeed secondHeight) :=
    expansionPath_validSeed_of_le (Nat.le_max_right _ _)
  rcases system.seed_bounded commonHeight with
    ⟨bound, representation, hBounded⟩
  have hAccessible : Acc Step (validSeed commonHeight) :=
    system.accessible_of_bounded (frame.lt_wellFounded.apply bound)
      (.seed commonHeight) representation hBounded
  have hComparable := expansionPath_endpoints_comparable_of_accessible
    hAccessible (hFirstSeedPath.trans hFirstPath)
      (hSecondSeedPath.trans hSecondPath)
  rcases hComparable with hEqual | hOrdered
  · exact Or.inl (Subtype.ext hEqual)
  · rcases hOrdered with hFirstSecond | hSecondFirst
    · right
      left
      simpa only using generatedStrictDescent_of_strictDescent
        second.2 hFirstSecond
    · right
      right
      simpa only using generatedStrictDescent_of_strictDescent
        first.2 hSecondFirst

/-- Stage 4 总结论：生成数组上的非空有限下降是 strict well-order。 -/
theorem strictWellOrder_generated {Label : Type u}
    {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) :
    StrictWellOrder GeneratedArray GeneratedStrictDescent where
  wellFounded := system.strictDescent_wellFoundedOn_generated
  transitive := generatedStrictDescent_transitive
  trichotomy := system.generated_comparable

end RepresentationDescentSystem
end StabilityFrame
end BMS
end YesMetaZFC
