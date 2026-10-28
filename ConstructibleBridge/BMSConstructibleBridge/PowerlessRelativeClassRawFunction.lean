import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation
import BMSConstructibleBridge.PowerlessRelativeClassBounded
import BMSConstructibleBridge.PowerlessRelativeClassValueCoordinates

/-! # 有界矩阵的实际 Class 函数：全原商接口

原 num/set 的 SecondOrderArithmetic.theory_m 是背景，矩阵保留纯隶属
ℒ 的 AST 和实际 Class 参数环境。输入是固定 Class 域／陪域上的全 raw
总性与唯一性；原 Δ₀ 构图给实际 Class 函数，并恢复所有 raw 坐标的读数。
陪域界是明确前提，不以逐点存在暗推统一界，也不抽取 Type 选择函数。

本通用语义辅助供统一 Def 等对象模式装配使用；不是超限递归、完整
Collection 或 BMS 终局的替代，正式对象推导由调用端封装。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRawFunction

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ
local notation "ClassModel" => structure_l hℳ B hBase

/-- 自由变量延伸与环境下推交换；不展开未知依赖变量的值。 -/
theorem env_pushFree_l {Γ Δ : SortContext ℒ} (η : Env ClassModel Γ Δ) (x : type_l hℳ B) :
    PowerlessRelativeClassRelativization.env_l (η.pushFree (sort := SetTheory.SetSort.set) x) =
      (PowerlessRelativeClassRelativization.env_l η).pushFree (sort := SetTheory.SetSort.set) x.val := by
  apply Env.ext
  · intro s v
    cases s
    rfl
  · intro s v
    cases s
    cases v <;> rfl

/-- 固定实际陪域内的 raw 单值关系给出实际 Class 图及全部 raw 读数。 -/
theorem exists_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env ClassModel [] Δ)
    (X Y : type_l hℳ B)
    (hTotal : ∀ x : SecondOrderQuotient.type_l hℳ, mem_l hℳ x X.val →
      ∃! y : SecondOrderQuotient.type_l hℳ, mem_l hℳ y Y.val ∧
        φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree x)) :
    ∃ G : type_l hℳ B, map_l (ℳ := RawModel) G.val X.val Y.val ∧
      ∀ x y : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := RawModel) G.val x y ↔ mem_l hℳ x X.val ∧ mem_l hℳ y Y.val ∧
          φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree x) := by
  have hRead (x y : type_l hℳ B) :
      φ.satisfies ((η.pushFree y).pushFree x) ↔
        φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y.val).pushFree x.val) := by
    simpa only [env_pushFree_l] using
      PowerlessRelativeClassBounded.formula_l hφ ((η.pushFree y).pushFree x)
  have hTotal' (x : type_l hℳ B) (hx : mem_l hℳ x.val X.val) :
      ∃! y : type_l hℳ B, mem_l hℳ y.val Y.val ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
    obtain ⟨y, ⟨hy, hxy⟩, hUnique⟩ := hTotal x.val hx
    let y' : type_l hℳ B := ⟨y,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩
    refine ⟨y', ⟨hy, (hRead x y').mpr hxy⟩, ?_⟩
    intro z hz
    exact Subtype.ext (hUnique z.val ⟨hz.1, (hRead x z).mp hz.2⟩)
  obtain ⟨G, hG, hValue⟩ := PowerlessRelativeClassFunctionRelation.exists_l hφ η X Y hTotal'
  have hClassRead (x y : type_l hℳ B) :=
    (PowerlessRelativeClassFunctionAbsolute.value_l G x y).symm.trans
      ((hValue x y).trans (and_congr Iff.rfl (and_congr Iff.rfl (hRead x y))))
  refine ⟨G, (PowerlessRelativeClassFunctionAbsolute.map_l G X Y).mp hG, ?_⟩
  intro x y
  constructor
  · intro hValueRaw
    obtain ⟨hx, hy⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase G hValueRaw
    exact (hClassRead ⟨x, hx⟩ ⟨y, hy⟩).mp hValueRaw
  · rintro ⟨hx, hy, hxy⟩
    let x' : type_l hℳ B := ⟨x,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hx⟩
    let y' : type_l hℳ B := ⟨y,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩
    exact (hClassRead x' y').mpr ⟨hx, hy, hxy⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRawFunction
