import BMSConstructibleBridge.PowerlessCodedStageTheory
import BMSConstructibleBridge.PowerlessStabilitySupport

/-!
# 编码好标签条件作为共同见证矩阵的固定条目

§16 条目 4 的语法半：`holds_m` 的九个参数全部改成环境槽，公式正文固定不变，
指定的有限支持 Ξ = StabilitySupport.basis_m k 只经 `code_l` 换成两个自然数码。
因此同一份 AST 可以对任意标签与任意见证码求值，矩阵不展开 Ξ。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStageEntry

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure
open PowerlessCodedStageTheory

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 六个层参数、两个见证码与一个标签，共九个集合槽。 -/
abbrev context_m : SortContext ℒ :=
  [.set, .set, .set, .set, .set, .set, .set, .set, .set]

/-- 按 ω,e,T,t₁,t₂,t₃,c,N,标签 的顺序压入，最后压入者为零号槽。 -/
def env_l (ω e T t₁ t₂ t₃ c N α : carrier_l ℳ) : Env ℳ [] context_m :=
  ((((((((Env.empty.pushFree ω).pushFree e).pushFree T).pushFree t₁).pushFree t₂).pushFree t₃).pushFree c).pushFree N).pushFree α

def label_slot : Term ℒ [] context_m .set := .fvar .here

def length_slot : Term ℒ [] context_m .set := .fvar (.there .here)

def code_slot : Term ℒ [] context_m .set := .fvar (.there (.there .here))

def tag₃_slot : Term ℒ [] context_m .set := .fvar (.there (.there (.there .here)))

def tag₂_slot : Term ℒ [] context_m .set :=
  .fvar (.there (.there (.there (.there .here))))

def tag₁_slot : Term ℒ [] context_m .set :=
  .fvar (.there (.there (.there (.there (.there .here)))))

def triangle_slot : Term ℒ [] context_m .set :=
  .fvar (.there (.there (.there (.there (.there (.there .here))))))

def zero_slot : Term ℒ [] context_m .set :=
  .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))

def omega_slot : Term ℒ [] context_m .set :=
  .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))

/-- 固定条目：好标签条件只读九个环境槽，正文不含 Ξ 的枚举。 -/
def coded_m : Formula ℒ [] context_m :=
  holds_m omega_slot zero_slot triangle_slot tag₁_slot tag₂_slot tag₃_slot
    code_slot length_slot label_slot

theorem coded_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (ω e T t₁ t₂ t₃ c N α : carrier_l ℳ) :
    coded_m.satisfies (env_l ω e T t₁ t₂ t₃ c N α) ↔ holds_l ω e T t₁ t₂ t₃ c N α :=
  holds_formula_l hℳ (env_l ω e T t₁ t₂ t₃ c N α) omega_slot zero_slot triangle_slot
    tag₁_slot tag₂_slot tag₃_slot code_slot length_slot label_slot

/-- 条目实际可充当矩阵行：对 Ξ = StabilitySupport.basis_m k，存在两个内部自然数码，
使固定 AST 条件在该环境中的真值恰等价于该标签的层满足 Ξ。 -/
theorem coded_entry_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T) (k : Nat)
    {α A S F : carrier_l ℳ} (hA₀ : ∃ x, member_l ℳ x A)
    (hA : PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F) :
    ∃ c N : carrier_l ℳ, member_l ℳ c ω ∧ member_l ℳ N ω ∧
      (coded_m.satisfies (env_l ω e T t₁ t₂ t₃ c N α) ↔
        Theory.Models (structure_l A hA₀) (Theory.ofList (PowerlessStabilitySupport.basis_m k))) := by
  obtain ⟨c, N, hc, hN, h⟩ :=
    PowerlessCodedStageTheory.code_l hℳ hω ht hT (PowerlessStabilitySupport.basis_m k)
  exact ⟨c, N, hc, hN, (coded_formula_l hℳ ω e T t₁ t₂ t₃ c N α).trans (h hA₀ hA)⟩

#print axioms coded_formula_l
#print axioms coded_entry_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStageEntry
