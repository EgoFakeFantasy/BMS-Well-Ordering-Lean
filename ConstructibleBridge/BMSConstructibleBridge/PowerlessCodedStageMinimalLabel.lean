import BMSConstructibleBridge.PowerlessCodedDiagram
import BMSConstructibleBridge.PowerlessComprehension
import BMSConstructibleBridge.PowerlessOrdinalMinimum

/-!
# 编码好标签条件的内部最小反例标签

把原 BMS 论证里的“取最小反例标签”一步接到实际对象语言：不合适性写成
`PowerlessCodedDiagram.condition_m` 的否定，故它只是重约化语法里的一个 ℒ 公式，
层内分离与序数最小元直接可用，不引入外部良基性或标准性。
八项系统参数与统一数码越过候选槽读取同一环境，因此在整个最小化过程中固定不变；
重标号长度 q 不出现在本节。结论只给出 ∈-最小不合适标签的存在与唯一，
其以下标签全部合适；不从最小性反推该标签自身合适，那一步仍属后续的真实展开下降。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStageMinimalLabel

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 八个参数自由槽。按 `Env.pushFree` 的压入约定，最后压入者落在零号槽。 -/
abbrev octet_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set]

/-- 槽位读取器：`p₀` 读最后压入的求值长度码 N，`p₇` 读最先压入的 ω。 -/
def p₀ : Term ℒ [] octet_m .set := .fvar .here

def p₁ : Term ℒ [] octet_m .set := .fvar (.there .here)

def p₂ : Term ℒ [] octet_m .set := .fvar (.there (.there .here))

def p₃ : Term ℒ [] octet_m .set := .fvar (.there (.there (.there .here)))

def p₄ : Term ℒ [] octet_m .set := .fvar (.there (.there (.there (.there .here))))

def p₅ : Term ℒ [] octet_m .set := .fvar (.there (.there (.there (.there (.there .here)))))

def p₆ : Term ℒ [] octet_m .set :=
  .fvar (.there (.there (.there (.there (.there (.there .here))))))

def p₇ : Term ℒ [] octet_m .set :=
  .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))

/-- 候选标签即零号自由槽。 -/
abbrev label_slot_m : Term ℒ [] (.set :: octet_m) .set := .fvar .here

/-- 八项参数越过候选槽读取原环境。 -/
abbrev wp₇ : Term ℒ [] (.set :: octet_m) .set := p₇.weakenFree SetTheory.SetSort.set

abbrev wp₆ : Term ℒ [] (.set :: octet_m) .set := p₆.weakenFree SetTheory.SetSort.set

abbrev wp₅ : Term ℒ [] (.set :: octet_m) .set := p₅.weakenFree SetTheory.SetSort.set

abbrev wp₄ : Term ℒ [] (.set :: octet_m) .set := p₄.weakenFree SetTheory.SetSort.set

abbrev wp₃ : Term ℒ [] (.set :: octet_m) .set := p₃.weakenFree SetTheory.SetSort.set

abbrev wp₂ : Term ℒ [] (.set :: octet_m) .set := p₂.weakenFree SetTheory.SetSort.set

abbrev wp₁ : Term ℒ [] (.set :: octet_m) .set := p₁.weakenFree SetTheory.SetSort.set

abbrev wp₀ : Term ℒ [] (.set :: octet_m) .set := p₀.weakenFree SetTheory.SetSort.set

/-- 固定八项参数下，标签合适当且仅当它是 ω 之上的极限层号且编码核心在该标签成立。 -/
def good_env_l (η : Env ℳ [] octet_m) (α : carrier_l ℳ) : Prop :=
  PowerlessCodedDiagram.good_l (p₇.eval η) (p₆.eval η) (p₅.eval η) (p₄.eval η) (p₃.eval η)
    (p₂.eval η) (p₁.eval η) (p₀.eval η) α

/-- 候选标签占零号自由槽，八项参数越过它读取原环境。 -/
def good_label_m : Formula ℒ [] (.set :: octet_m) :=
  PowerlessCodedDiagram.condition_m p₇ p₆ p₅ p₄ p₃ p₂ p₁ p₀

def bad_label_m : Formula ℒ [] (.set :: octet_m) := .neg good_label_m

/-- 不合适序数标签：本身不合适，且其以下全部合适。 -/
def minimal_bad_l (η : Env ℳ [] octet_m) (α : carrier_l ℳ) : Prop :=
  PowerlessOrdinal.ordinal_l α ∧ ¬good_env_l η α ∧
    ∀ β, member_l ℳ β α → good_env_l η β

theorem eval_label_l (η : Env ℳ [] octet_m) (α : carrier_l ℳ) :
    label_slot_m.eval (η.pushFree α) = α := by
  simp [Term.eval, Env.pushFree, Assignment.push]

theorem good_label_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (η : Env ℳ [] octet_m) (α : carrier_l ℳ) :
    good_label_m.satisfies (η.pushFree α) ↔ good_env_l η α := by
  simpa only [good_label_m, PowerlessCodedDiagram.condition_m, good_env_l,
    Term.eval_weakenFree, eval_label_l] using
      (PowerlessCodedDiagram.good_formula_l hℳ (η.pushFree α)
        wp₇ wp₆ wp₅ wp₄ wp₃ wp₂ wp₁ wp₀ label_slot_m)

theorem bad_label_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (η : Env ℳ [] octet_m) (α : carrier_l ℳ) :
    bad_label_m.satisfies (η.pushFree α) ↔ ¬good_env_l η α := by
  show (¬good_label_m.satisfies (η.pushFree α)) ↔ ¬good_env_l η α
  exact Iff.not (good_label_formula_l hℳ η α)

/-- 最小不合适标签与 `PowerlessOrdinalMinimum.minimum_l` 逐字同一，故复用其唯一性。 -/
theorem minimal_bad_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (η : Env ℳ [] octet_m) (α : carrier_l ℳ) :
    minimal_bad_l η α ↔ PowerlessOrdinalMinimum.minimum_l bad_label_m η α := by
  constructor
  · rintro ⟨hord, hbad, hbelow⟩
    exact ⟨hord, (bad_label_formula_l hℳ η α).mpr hbad, fun β hβ hb =>
      absurd (hbelow β hβ) ((bad_label_formula_l hℳ η β).mp hb)⟩
  · rintro ⟨hord, hsat, hnot⟩
    refine ⟨hord, (bad_label_formula_l hℳ η α).mp hsat, fun β hβ => ?_⟩
    exact Classical.byContradiction fun hn =>
      hnot β hβ ((bad_label_formula_l hℳ η β).mpr hn)

/-- 只要存在不合适的序数标签，实际就有 ∈-最小的不合适标签，其以下全部标签合适。
分离与最小元均取内部分离得到的实际集合，不按宿主有限列表枚举标签。 -/
theorem exists_minimal_bad_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ)
      octet_m.length)
    (h : ∃ α, PowerlessOrdinal.ordinal_l α ∧
      ¬good_env_l (PowerlessComprehension.env_l η) α) :
    ∃ α, minimal_bad_l (PowerlessComprehension.env_l η) α := by
  obtain ⟨α, hα, hbad⟩ := h
  obtain ⟨γ, hmin⟩ := PowerlessOrdinalMinimum.exists_l hℳ bad_label_m η
    ⟨α, hα, (bad_label_formula_l hℳ (PowerlessComprehension.env_l η) α).mpr hbad⟩
  exact ⟨γ, (minimal_bad_formula_l hℳ (PowerlessComprehension.env_l η) γ).mpr hmin⟩

/-- 环境固定时最小不合适标签唯一。 -/
theorem minimal_bad_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (η : Env ℳ [] octet_m) {α β : carrier_l ℳ}
    (hα : minimal_bad_l η α) (hβ : minimal_bad_l η β) : α = β := by
  have h₁ := (minimal_bad_formula_l hℳ η α).mp hα
  have h₂ := (minimal_bad_formula_l hℳ η β).mp hβ
  exact PowerlessOrdinalMinimum.unique_l hℳ h₁ h₂

#print axioms good_label_formula_l
#print axioms exists_minimal_bad_l
#print axioms minimal_bad_unique_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStageMinimalLabel
