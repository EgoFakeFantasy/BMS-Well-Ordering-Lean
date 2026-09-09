import YesMetaZFC.BMS.OrdinalReflectionSyntax
import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookFiniteReflectionL
import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareStageHistoryBounds

/-!
# Constructible levels as YesMetaZFC membership structures

本模块是 BM4 组合证明与具体 `ZFSet` 可构造层级之间的内核检查边界。它把每个
`L_α` 载体装备为新版 YesMetaZFC 的内在纯成员结构，并证明层包含是 Lévy 嵌入；
初等性不作为嵌入字段偷渡。
-/

open Set

universe u

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open Logic FirstOrder

abbrev StageCarrier (α : Ordinal.{u}) :=
  Constructible.Model.StageCarrier α

/-- `L_alpha` 的纯成员关系 Tarski 结构；非空性作为显式参数保留。 -/
abbrev lStageStructure (α : Ordinal.{u})
    (hNonempty : Nonempty (StageCarrier α)) :
    FirstOrder.Structure.{0, 0, 0, u + 1} SetTheory.signature where
  Carrier := fun _ => StageCarrier α
  nonempty := fun _ => hNonempty
  funcInterp := fun symbol => nomatch symbol
  relInterp := fun relation arguments =>
    match relation, arguments with
    | SetTheory.RelationSymbol.membership,
        .cons left (.cons right .nil) => left.1 ∈ right.1

/-- `L_alpha` 结构中的二元成员关系就是底层 `ZFSet` 成员关系。 -/
@[simp]
theorem lStageStructure_membership_iff (α : Ordinal.{u})
    (hNonempty : Nonempty (StageCarrier α))
    (left right : StageCarrier α) :
    (lStageStructure α hNonempty).relInterp
        SetTheory.RelationSymbol.membership
        (.cons left (.cons right .nil)) ↔
      left.1 ∈ right.1 :=
  Iff.rfl

/-- 可构造层包含在子类型载体上的映射。 -/
def lStageInclusion {α β : Ordinal.{u}} (hαβ : α ≤ β) :
    StageCarrier α → StageCarrier β :=
  fun value => ⟨value.1, Constructible.LStageZF_mono hαβ value.2⟩

/-- 层包含保持并反映成员关系，且像对成员关系向下封闭。 -/
def lStageLevyEmbedding {α β : Ordinal.{u}}
    (sourceNonempty : Nonempty (StageCarrier α))
    (targetNonempty : Nonempty (StageCarrier β))
    (hαβ : α ≤ β) :
    Formula.LevyEmbedding StabilityFrame.membershipLevyBound
      (lStageStructure α sourceNonempty)
      (lStageStructure β targetNonempty) where
  map := fun sort => match sort with
    | .set => lStageInclusion hαβ
  map_injective := by
    intro sort left right hEqual
    cases sort
    change lStageInclusion hαβ left = lStageInclusion hαβ right at hEqual
    exact Subtype.ext
      (congrArg (fun value : StageCarrier β => value.1) hEqual)
  function_eq := fun function => nomatch function
  relation_iff := by
    intro relation arguments
    cases relation
    cases arguments with
    | cons left tail =>
        cases tail with
        | cons right rest => cases rest; rfl
  bounded_preimage := by
    intro boundValue targetValue hMembership
    simp only [StabilityFrame.membershipLevyBound,
      Formula.LevyBound.Holds, lStageStructure, lStageInclusion] at hMembership
    have hTargetα : targetValue.1 ∈ Constructible.LStageZF α :=
      (Constructible.LStageZF_isTransitive α).mem_trans
        hMembership boundValue.2
    exact ⟨⟨targetValue.1, hTargetα⟩, Subtype.ext rfl⟩

/-- 具体包含 `L_α ⊆ L_β` 的有限 `Sigma` 初等性。 -/
def StageSigmaElementaryAt (level : Nat) (α β : Ordinal.{u}) : Prop :=
  ∃ (sourceNonempty : Nonempty (StageCarrier α))
      (targetNonempty : Nonempty (StageCarrier β))
      (hαβ : α ≤ β),
    Formula.IsSigmaFiniteElementaryAt
      (lStageLevyEmbedding sourceNonempty targetNonempty hαβ) level

/-- 把严格低于层高的元语言序数编码为该可构造层中的 von Neumann 序数。 -/
noncomputable def encodeStageOrdinal_l (top ordinal : Ordinal.{u})
    (hOrdinalTop : ordinal < top) : StageCarrier top :=
  ⟨ordinal.toZFSet,
    Constructible.ordinal_toZFSet_mem_LStageZF_of_lt hOrdinalTop⟩

/-- 规范序数编码的底层集合就是 `ordinal.toZFSet`。 -/
@[simp]
theorem encodeStageOrdinal_value_l (top ordinal : Ordinal.{u})
    (hOrdinalTop : ordinal < top) :
    (encodeStageOrdinal_l top ordinal hOrdinalTop).1 = ordinal.toZFSet :=
  rfl

/-- 规范序数编码确实满足 von Neumann 序数谓词。 -/
theorem encodeStageOrdinal_isOrdinal_l (top ordinal : Ordinal.{u})
    (hOrdinalTop : ordinal < top) :
    (encodeStageOrdinal_l top ordinal hOrdinalTop).1.IsOrdinal := by
  exact ZFSet.isOrdinal_toZFSet ordinal

/-- 规范序数编码按 rank 解码回原序数。 -/
@[simp]
theorem encodeStageOrdinal_rank_l (top ordinal : Ordinal.{u})
    (hOrdinalTop : ordinal < top) :
    (encodeStageOrdinal_l top ordinal hOrdinalTop).1.rank = ordinal := by
  apply Ordinal.toZFSet_injective
  exact (ZFSet.isOrdinal_toZFSet ordinal).toZFSet_rank_eq

/-- 任意层内序数的 rank 严格低于该层索引。 -/
theorem stageOrdinal_rank_lt_l {top : Ordinal.{u}}
    (value : StageCarrier top) (hOrdinal : value.1.IsOrdinal) :
    value.1.rank < top := by
  exact (Constructible.ordinal_stage_invariants top).1 hOrdinal value.2

/-- 层内两个序数的成员关系等价于其 rank 的严格序。 -/
theorem stageOrdinal_mem_iff_rank_lt_l {top : Ordinal.{u}}
    (left right : StageCarrier top)
    (hLeft : left.1.IsOrdinal) (hRight : right.1.IsOrdinal) :
    left.1 ∈ right.1 ↔ left.1.rank < right.1.rank := by
  constructor
  · intro hMembership
    apply Ordinal.toZFSet_mem_toZFSet_iff.mp
    simpa only [hLeft.toZFSet_rank_eq, hRight.toZFSet_rank_eq] using
      hMembership
  · intro hRanks
    have hMembership := Ordinal.toZFSet_mem_toZFSet_iff.mpr hRanks
    simpa only [hLeft.toZFSet_rank_eq, hRight.toZFSet_rank_eq] using
      hMembership

/-- 层包含保持严格低于源层界的规范序数编码。 -/
theorem lStageInclusion_encodeStageOrdinal_l
    {source target ordinal : Ordinal.{u}}
    (hSourceTarget : source ≤ target) (hOrdinalSource : ordinal < source) :
    lStageInclusion hSourceTarget
        (encodeStageOrdinal_l source ordinal hOrdinalSource) =
      encodeStageOrdinal_l target ordinal
        (hOrdinalSource.trans_le hSourceTarget) := by
  exact Subtype.ext rfl

end ConstructibleBridge
end BMS
end YesMetaZFC
