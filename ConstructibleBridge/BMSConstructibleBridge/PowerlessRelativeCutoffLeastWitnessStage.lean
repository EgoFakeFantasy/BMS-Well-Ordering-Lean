import BMSConstructibleBridge.PowerlessRelativeWitnessLeastStage
import BMSConstructibleBridge.PowerlessRelativeCutoffLimit
import BMSConstructibleBridge.PowerlessRelativeLimitClosure

/-! # 截断域中合格见证的唯一最小出现阶段

对象语言是纯集合语言 ℒ，背景是原二阶算术模型的实际商结构。对任意
固定外部公式 χ(y,参数)，若在实际截断层 W 中有合格见证，则 χ 的最小
出现阶段唯一且严格低于 Ω。这里允许任意实际参数环境和任意实际基底 B；
证明内部只把 B 加入自由参数槽，不把 χ 换成任意宿主谓词。

本文件是原对象推导所需的模型语义中间引理：存在性始终留在 Prop，
不选择 Type 层见证函数，不断言最小阶段的统一 Class 图、共同界或
Collection，也不提供对所有内部公式码的统一真值断言。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffLeastWitnessStage

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- 保留见证的自由头槽，在其后加入基底参数，再接原自由参数。 -/
private def witnessLift_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: Δ) [] (.set :: .set :: Δ)
  | _, .here => .fvar .here
  | _, .there v => .fvar (.there (.there v))

/-- 真正的极限截断域内，每个固定公式的合格见证有唯一的最小出现阶段。
`hω` 是既有截断极限定理所需的实际 ω 守卫；`first_l` 本身不包含它。 -/
theorem exists_l (K : source_coding_l hℳ) {B ω Ω W : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : level_l hℳ B Ω W) {Δ : SortContext ℒ}
    (χ : Formula ℒ [] (.set :: Δ)) (η : Env RawModel [] Δ)
    (hWitness : ∃ y, mem_l hℳ y W ∧ χ.satisfies (η.pushFree y)) :
    ∃! α, mem_l hℳ α Ω ∧
      PowerlessRelativeWitnessLeastStage.rank_l χ η B α := by
  have hLimit := PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ
  have hWClass := PowerlessRelativeLevelClosure.class_l hℳ hBase hW
  obtain ⟨y, hyW, hχ⟩ := hWitness
  have hyClass := PowerlessRelativeClassCorrespondence.transitive_l
    hℳ hBase hWClass hyW
  -- 既有极小阶段接口把 B 表示成项；加入一个真实参数便可容纳任意 raw B。
  let χ' : Formula ℒ [] (.set :: .set :: Δ) :=
    χ.substitute (.map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
      witnessLift_m)
  let η' : Env RawModel [] (.set :: Δ) := η.pushFree B
  have hRead (z : type_l hℳ) :
      χ'.satisfies (η'.pushFree z) ↔ χ.satisfies (η.pushFree z) := by
    dsimp only [χ', η']
    rw [Formula.satisfies_substitute]
    apply Iff.of_eq
    apply congrArg (fun ρ => χ.satisfies ρ)
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases v <;> rfl
  have hRank (α : type_l hℳ) :
      PowerlessRelativeWitnessLeastStage.rank_l χ' η' B α ↔
        PowerlessRelativeWitnessLeastStage.rank_l χ η B α := by
    simp only [PowerlessRelativeWitnessLeastStage.rank_l,
      PowerlessRelativeWitnessLeastStage.occurs_l, hRead]
  have hSome : ∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z ∧
      χ'.satisfies (η'.pushFree z) := ⟨y, hyClass, (hRead y).mpr hχ⟩
  obtain ⟨α, hα'⟩ := PowerlessRelativeWitnessLeastStage.exists_l K χ' η'
    (.fvar .here : Term ℒ [] (.set :: Δ) .set) hSome
  change PowerlessRelativeWitnessLeastStage.rank_l χ' η' B α at hα'
  have hα := (hRank α).mp hα'
  -- 先下降所给实际见证，再比较最小阶段；不需要枚举或共同历史界。
  obtain ⟨β, C, hβΩ, hC, hyC⟩ :=
    (PowerlessRelativeLimitClosure.value_l hℳ hBase hLimit hW y).mp hyW
  have hOccursβ : PowerlessRelativeWitnessLeastStage.occurs_l χ η B β :=
    ⟨C, hC, y, hyC, hχ⟩
  have hαΩ : mem_l hℳ α Ω := by
    rcases PowerlessRelativeWitnessLeastStage.bound_l hα hOccursβ with hEq | hαβ
    · exact hEq.symm ▸ hβΩ
    · exact hΩ.1.transitive β hβΩ α hαβ
  exact ⟨α, ⟨hαΩ, hα⟩,
    fun β hβ => PowerlessRelativeWitnessLeastStage.unique_l hβ.2 hα⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffLeastWitnessStage
