import BMSConstructibleBridge.BoundedExternalStageElementarity
import BMSConstructibleBridge.StageStructure
import BMSConstructibleBridge.StageStabilityComplexity
import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareStageHistoryBounds

/-!
# 可构造层的有限 Lévy 初等关系

本模块把 Hunter 的 `α <_n β` 具体定义为严格层增长加上
`L_α ≺_{Σ_(stageStabilityLevyLevel_l n)} L_β`。更新后的 YesMetaZFC 使用内在类型化语法；具体可构造
层级以保留真正有界量词的外部有限 Levy 分类为规范接口；该接口已经与新版
YesMetaZFC 的内在类型化分类证明等价，因而不会把无界存在量词误算作零层。
-/

universe u

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open Logic FirstOrder
open StabilityFrame

/-- 较高层的有限 `Sigma` 初等性蕴含每个较低层的初等性。 -/
theorem stageSigmaElementaryAt_mono
    {lowerLevel upperLevel : Nat} {α β : Ordinal.{u}}
    (hLevels : lowerLevel ≤ upperLevel)
    (hElementary :
      BoundedExternalStageSigmaElementaryAt_l upperLevel α β) :
    BoundedExternalStageSigmaElementaryAt_l lowerLevel α β :=
  BoundedExternalStageSigmaElementaryAt_mono_l hLevels hElementary

/-- 有限 `Sigma` 初等的可构造层包含关系具有传递性。 -/
theorem stageSigmaElementaryAt_trans
    {level : Nat} {α β γ : Ordinal.{u}}
    (hαβ : BoundedExternalStageSigmaElementaryAt_l level α β)
    (hβγ : BoundedExternalStageSigmaElementaryAt_l level β γ) :
    BoundedExternalStageSigmaElementaryAt_l level α γ :=
  BoundedExternalStageSigmaElementaryAt_trans_l hαβ hβγ

/--
Hunter 稳定关系：下端点已经越过 `omega`，层严格增长，且层包含对重编号后的
有限 `Sigma` 公式初等，并且两端都是后继极限。显式保留下端点界与极限性
保证局部 `L`-阶段求值器在两端都具有无条件精确语义；这也是对象语言稳定公式
的自然定义域。
-/
def stageStableLt (level : Nat) (α β : Ordinal.{u}) : Prop :=
  Ordinal.omega0 < α ∧
    α < β ∧
      BoundedExternalStageSigmaElementaryAt_l
        (stageStabilityLevyLevel_l level) α β ∧
      Order.IsSuccLimit α ∧ Order.IsSuccLimit β

/-- 稳定关系蕴含普通序数严格序。 -/
theorem stageStableLt_lt {level : Nat} {α β : Ordinal.{u}}
    (hStable : stageStableLt level α β) : α < β :=
  hStable.2.1

/-- 稳定对的下端点严格越过内部可构造层求值器所需的 `omega`。 -/
theorem stageStableLt_omega_lt_left {level : Nat} {α β : Ordinal.{u}}
    (hStable : stageStableLt level α β) : Ordinal.omega0 < α :=
  hStable.1

/-- 稳定对的上端点也严格越过 `omega`。 -/
theorem stageStableLt_omega_lt_right {level : Nat} {α β : Ordinal.{u}}
    (hStable : stageStableLt level α β) : Ordinal.omega0 < β :=
  hStable.1.trans hStable.2.1

/-- 稳定关系保存的有限 `Sigma` 层初等性。 -/
theorem stageStableLt_elementary {level : Nat} {α β : Ordinal.{u}}
    (hStable : stageStableLt level α β) :
    BoundedExternalStageSigmaElementaryAt_l
      (stageStabilityLevyLevel_l level) α β :=
  hStable.2.2.1

/-- 稳定对的下端点是后继极限。 -/
theorem stageStableLt_left_isSuccLimit {level : Nat} {α β : Ordinal.{u}}
    (hStable : stageStableLt level α β) : Order.IsSuccLimit α :=
  hStable.2.2.2.1

/-- 稳定对的上端点是后继极限。 -/
theorem stageStableLt_right_isSuccLimit {level : Nat} {α β : Ordinal.{u}}
    (hStable : stageStableLt level α β) : Order.IsSuccLimit β :=
  hStable.2.2.2.2

/-- 稳定对下层包含全部十三个规范阶段求值器参数。 -/
theorem stageStableLt_fixedParameters_mem_left
    {level : Nat} {α β : Ordinal.{u}}
    (hStable : stageStableLt level α β) :
    ∀ index : Fin 13,
      (Constructible.Model.stageHistoryFixedParameters.{u} index).1 ∈
        Constructible.LStageZF α :=
  Constructible.Model.stageHistoryFixedParameters_mem_LStageZF_of_omega_lt
    (stageStableLt_omega_lt_left hStable)

/-- 稳定对上层包含全部十三个规范阶段求值器参数。 -/
theorem stageStableLt_fixedParameters_mem_right
    {level : Nat} {α β : Ordinal.{u}}
    (hStable : stageStableLt level α β) :
    ∀ index : Fin 13,
      (Constructible.Model.stageHistoryFixedParameters.{u} index).1 ∈
        Constructible.LStageZF β :=
  Constructible.Model.stageHistoryFixedParameters_mem_LStageZF_of_omega_lt
    (stageStableLt_omega_lt_right hStable)

/-- 稳定关系对公式级别向下单调。 -/
theorem stageStableLt_levelMonotone
    {lowerLevel upperLevel : Nat} {α β : Ordinal.{u}}
    (hLevels : lowerLevel ≤ upperLevel)
    (hStable : stageStableLt upperLevel α β) :
    stageStableLt lowerLevel α β := by
  refine ⟨hStable.1, hStable.2.1,
    stageSigmaElementaryAt_mono ?_ (stageStableLt_elementary hStable),
    stageStableLt_left_isSuccLimit hStable,
    stageStableLt_right_isSuccLimit hStable⟩
  exact stageStabilityLevyLevel_mono_l hLevels

/-- 每个固定稳定层的关系具有传递性。 -/
theorem stageStableLt_trans
    {level : Nat} {α β γ : Ordinal.{u}}
    (hαβ : stageStableLt level α β)
    (hβγ : stageStableLt level β γ) :
  stageStableLt level α γ :=
  ⟨hαβ.1, hαβ.2.1.trans hβγ.2.1,
    stageSigmaElementaryAt_trans
      (stageStableLt_elementary hαβ) (stageStableLt_elementary hβγ),
    stageStableLt_left_isSuccLimit hαβ,
    stageStableLt_right_isSuccLimit hβγ⟩

/-- 论文稳定序数所使用的具体 `Ordinal` 框架。 -/
def constructibleStabilityFrame : StabilityFrame Ordinal.{u} :=
  { lt := (· < ·)
    stableLt := stageStableLt
    lt_wellFounded := Ordinal.lt_wf
    stableLt_lt := stageStableLt_lt }

/-- 具体框架的稳定层级向下单调。 -/
theorem constructibleStabilityFrame_levelMonotone :
    constructibleStabilityFrame.LevelMonotone := by
  intro lowerLevel upperLevel α β hLevels hStable
  change stageStableLt upperLevel α β at hStable
  change stageStableLt lowerLevel α β
  exact stageStableLt_levelMonotone hLevels hStable

end ConstructibleBridge
end BMS
end YesMetaZFC
