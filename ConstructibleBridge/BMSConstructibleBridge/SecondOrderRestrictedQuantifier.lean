import BMSConstructibleBridge.SecondOrderRealRestriction
import BMSConstructibleBridge.FixedHeightPureFormula

/-!
# 任务31：算术矩阵的集合量词限制与原固定高度目标反例保持

任务30 的算术绝对性 `sat_arithmetic_l` 只覆盖检查器 `arithmetic_m = true` 的公式，其集合量词
分支恰被检查器判假并在归纳里消去。本模块补齐**最外层单个集合量词**的处理：在任务30 的
`restrict_l ℳ P hP`（同一内部数域、缩到 `{X // P X}` 实数域）上，先证 `env_l` 与 `.set` 端
`pushBound`（`Subtype` 见证）交换，再对**原** `Formula signature_m (.set :: Γ) Δ` 且
`arithmetic_m φ = true` 证明

* `restrict ⊨ η (∀set φ) ↔ ∀ X : set_l ℳ, P X → ℳ ⊨ (env_l η).pushBound X φ`；
* `restrict ⊨ η (∃set φ) ↔ ∃ X : set_l ℳ, P X ∧ ℳ ⊨ (env_l η).pushBound X φ`。

由此得到两个方向的不对称出口：

* **全称真值向下传输**：若原结构对**全部** `X` 满足 `φ`，则限制结构满足 `∀set φ`（限制结构
  只在 `{X // P X}` 上量化，量域更小，故全称更易成立）。
* **反例保持**：给定具体 `X` 及 `hX : P X`，若它在原结构中是 `φ` 的反例，则该反例沿**同一
  `Subtype` 见证** `⟨X, hX⟩` 保持在限制结构中，使限制结构满足 `∃set ¬φ`。这只是“保留同一
  `P X` 见证的反例传输”，与“原全称→限制全称”的向下传输方向相互独立；限制结构满足全称并
  **不能**反向无条件反射为原结构满足全称：原结构可能有落在 `P` 之外的反例。

最后把上述结果**实例到原** `FixedHeightPureFormula.compiled_matrix_m cH cE` 的实际 AST：复用
`compiled_matrix_pure` 与任务30 的 `pure_impl_arithmetic_l` 得到算术性，同一 `cH` / `cE`、
同一自由高度上界 `N`（在环境 `η` 中）、给定下降实数 `X`，即得单见证矩阵对应 `compiled_point_l`、
全称限制对应与反例保持。不重写候选矩阵，不改变编译器、背景理论或最终目标。

约束（遵 task/31 brief 与广场 #1596）：`ℳ` 任意，不假定 `Theory.Models`；不宣称限制结构满足
`Z₂` 理解公理；不加入 `P` 的理解封闭/选择假设来包装终局；不对集合量词偷用全射；全称只作
单向下传，不宣称双向反射。本任务不构成本项目最终良序／保守传输闭合。不提交／推送／同步；
`LEAN_NUM_THREADS = 1` 唯一串行，由 Codex 单目标编译。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRestrictedQuantifier

open Logic FirstOrder SecondOrderSyntax SecondOrderModel SecondOrderRealRestriction

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
variable {P : set_l ℳ → Prop} {hP : Nonempty {X // P X}}

/-! ## 环境提升与集合端 pushBound 交换 -/

/-- 在**实数（`set`）绑定端**，环境提升与 `pushBound` 交换：`set` 上包含为 `Subtype.val`，
故提升后压入落回原载体的见证值。与任务30 的 `env_l_pushBound_l`（`num` 端）互补。 -/
theorem env_l_pushBound_set_l {Γ Δ : SortContext signature_m}
    (η : Env (restrict_l ℳ P hP) Γ Δ)
    (v : (restrict_l ℳ P hP).Carrier sort_m.set) :
    env_l P hP (η.pushBound v) = (env_l P hP η).pushBound v.val := by
  refine Env.ext (fun entry => ?_) (fun entry => ?_)
  · cases entry with
    | here => rfl
    | there e => rfl
  · rfl

/-! ## 单个集合量词的矩阵对应 -/

/-- 主体 `φ`（其上下文以 `.set` 为首）在限制结构与原结构上，沿同一 `Subtype` 见证 `⟨X, hX⟩`
逐点绝对：限制结构中把 `⟨X, hX⟩` 压入绑定端满足 `φ`，当且仅当原结构把落回值 `X` 压入提升
环境的绑定端满足 `φ`。直接由算术绝对性 `sat_arithmetic_l` 与 `env_l_pushBound_set_l` 合成。 -/
theorem sat_pushBound_set_l {Γ Δ : SortContext signature_m}
    (φ : Formula signature_m (sort_m.set :: Γ) Δ) (hφ : arithmetic_m φ = true)
    (η : Env (restrict_l ℳ P hP) Γ Δ)
    (X : set_l ℳ) (hX : P X) :
    Formula.satisfies (M := restrict_l ℳ P hP)
        (@Env.pushBound signature_m (restrict_l ℳ P hP) Γ Δ sort_m.set η (Subtype.mk X hX)) φ ↔
      Formula.satisfies (M := ℳ) ((env_l P hP η).pushBound X) φ := by
  have := sat_arithmetic_l φ hφ
      (@Env.pushBound signature_m (restrict_l ℳ P hP) Γ Δ sort_m.set η (Subtype.mk X hX))
  rw [env_l_pushBound_set_l (P := P) (hP := hP) η (Subtype.mk X hX)] at this
  exact this

/-- **全称集合量词限制**：限制结构的 `∀set φ` 恰量化在 `{X // P X}` 上，逐点等价于
“原结构中每个满足 `P` 的 `X` 都满足 `φ`”。 -/
theorem sat_forallSet_l {Γ Δ : SortContext signature_m}
    (φ : Formula signature_m (sort_m.set :: Γ) Δ) :
    arithmetic_m φ = true →
      (η : Env (restrict_l ℳ P hP) Γ Δ) →
        Formula.satisfies (M := restrict_l ℳ P hP) η (.forallE sort_m.set φ) ↔
          ∀ X : set_l ℳ, P X →
            Formula.satisfies (M := ℳ) ((env_l P hP η).pushBound X) φ := by
  intro hφ η
  simp only [Formula.satisfies]
  constructor
  · intro h X hX
    rw [← sat_pushBound_set_l φ hφ η X hX]
    exact h (Subtype.mk X hX)
  · intro h v
    cases v with
    | mk X hX =>
        rw [sat_pushBound_set_l φ hφ η X hX]
        exact h X hX

/-- **存在集合量词限制**：限制结构的 `∃set φ` 恰在 `{X // P X}` 上取见证，逐点等价于
“存在满足 `P` 的原载体 `X` 使原结构满足 `φ`”。 -/
theorem sat_existsSet_l {Γ Δ : SortContext signature_m}
    (φ : Formula signature_m (sort_m.set :: Γ) Δ) :
    arithmetic_m φ = true →
      (η : Env (restrict_l ℳ P hP) Γ Δ) →
        Formula.satisfies (M := restrict_l ℳ P hP) η (.existsE sort_m.set φ) ↔
          ∃ X : set_l ℳ, P X ∧
            Formula.satisfies (M := ℳ) ((env_l P hP η).pushBound X) φ := by
  intro hφ η
  simp only [Formula.satisfies]
  constructor
  · rintro ⟨v, hv⟩
    cases v with
    | mk X hX =>
        exact ⟨X, hX, by rw [← sat_pushBound_set_l φ hφ η X hX]; exact hv⟩
  · rintro ⟨X, hX, hX2⟩
    exact ⟨(Subtype.mk X hX), by rw [sat_pushBound_set_l φ hφ η X hX]; exact hX2⟩

/-! ## 单向下传与反例保持（非双向反射） -/

/-- **全称真值向下传输**：原结构对**全部** `X` 满足 `φ`（即 `ℳ ⊨ env_l η (∀set φ)`）时，
限制结构满足 `∀set φ`。方向是限制结构量化域更小，故全称更容易成立。 -/
theorem forallSet_transport_l {Γ Δ : SortContext signature_m}
    (φ : Formula signature_m (sort_m.set :: Γ) Δ) (hφ : arithmetic_m φ = true)
    (η : Env (restrict_l ℳ P hP) Γ Δ)
    (h : Formula.satisfies (M := ℳ) (env_l P hP η) (.forallE sort_m.set φ)) :
    Formula.satisfies (M := restrict_l ℳ P hP) η (.forallE sort_m.set φ) := by
  rw [sat_forallSet_l φ hφ η]
  simp only [Formula.satisfies] at h
  intro X _hX
  exact h X

/-- **反例保持**：给定具体 `X` 及 `hX : P X`，若 `X` 在原结构上是 `φ` 的反例
（`¬ ℳ ⊨ (env_l η).pushBound X φ`），则限制结构在**同一 `Subtype` 见证** `⟨X, hX⟩` 下满足
`∃set ¬φ`。这是“保留同一 `P X` 见证的反例传输”，独立于 `forallSet_transport_l` 的
（原∀→限制∀）向下传输方向；限制结构满足全称**不能**无条件反射回原结构满足全称。 -/
theorem counterexampleSet_preserved_l {Γ Δ : SortContext signature_m}
    (φ : Formula signature_m (sort_m.set :: Γ) Δ) (hφ : arithmetic_m φ = true)
    (η : Env (restrict_l ℳ P hP) Γ Δ)
    (X : set_l ℳ) (hX : P X)
    (hc : ¬ Formula.satisfies (M := ℳ) ((env_l P hP η).pushBound X) φ) :
    Formula.satisfies (M := restrict_l ℳ P hP) η
      (.existsE sort_m.set (.neg φ)) := by
  rw [sat_existsSet_l (.neg φ) (by simpa [arithmetic_m] using hφ) η]
  refine ⟨X, hX, ?_⟩
  simp only [Formula.satisfies]
  exact hc

/-! ## 实例到原固定高度目标矩阵 compiled_matrix_m -/

open FixedHeightPureFormula

/-- 原编译矩阵具有算术性：由任务30 的 `pure_impl_arithmetic_l` 从 `compiled_matrix_pure` 直接
得到，不重写候选矩阵。 -/
theorem compiled_arithmetic_m (cH cE : PrimitiveProgram.code_m) :
    arithmetic_m (compiled_matrix_m cH cE) = true :=
  pure_impl_arithmetic_l (compiled_matrix_m cH cE) (compiled_matrix_pure cH cE)

/-- **单见证矩阵对应**：对同一 `cH` / `cE`、承载当前高度上界 `N` 的自由环境 `η` 及给定下降实数
见证 `⟨X, hX⟩`，直接复用 `sat_pushBound_set_l` 得到限制结构在 `η.pushBound ⟨X, hX⟩` 与原结构在
`(env_l η).pushBound X` 上满足**实际** `compiled_matrix_m cH cE` 的逐点 iff，不改 AST。 -/
theorem compiled_point_l (cH cE : PrimitiveProgram.code_m)
    (η : Env (restrict_l ℳ P hP) [] [sort_m.num])
    (X : set_l ℳ) (hX : P X) :
    Formula.satisfies (M := restrict_l ℳ P hP)
        (@Env.pushBound signature_m (restrict_l ℳ P hP) [] [sort_m.num] sort_m.set η
          (Subtype.mk X hX))
        (compiled_matrix_m cH cE) ↔
      Formula.satisfies (M := ℳ) ((env_l P hP η).pushBound X) (compiled_matrix_m cH cE) :=
  sat_pushBound_set_l (compiled_matrix_m cH cE) (compiled_arithmetic_m cH cE) η X hX

/-- **全称矩阵限制**：限制结构的 `∀set (compiled_matrix_m cH cE)` 逐点等价于“每个满足 `P` 的
下降实数 `X` 在原结构满足矩阵”（这是全称限制，逐见证对应另见 `compiled_point_l`）。 -/
theorem compiled_matrix_correspondence_l (cH cE : PrimitiveProgram.code_m)
    (η : Env (restrict_l ℳ P hP) [] [sort_m.num]) :
    Formula.satisfies (M := restrict_l ℳ P hP) η
        (.forallE sort_m.set (compiled_matrix_m cH cE)) ↔
      ∀ X : set_l ℳ, P X →
        Formula.satisfies (M := ℳ) ((env_l P hP η).pushBound X) (compiled_matrix_m cH cE) :=
  sat_forallSet_l (compiled_matrix_m cH cE) (compiled_arithmetic_m cH cE) η

/-- **原全称真值向限制结构传输**（实例）：原结构对所有下降实数满足 `compiled_matrix_m cH cE`
时，限制结构满足其 `∀set`。 -/
theorem compiled_forall_transport_l (cH cE : PrimitiveProgram.code_m)
    (η : Env (restrict_l ℳ P hP) [] [sort_m.num])
    (h : Formula.satisfies (M := ℳ) (env_l P hP η)
        (.forallE sort_m.set (compiled_matrix_m cH cE))) :
    Formula.satisfies (M := restrict_l ℳ P hP) η
      (.forallE sort_m.set (compiled_matrix_m cH cE)) :=
  forallSet_transport_l (compiled_matrix_m cH cE) (compiled_arithmetic_m cH cE) η h

/-- **全称反例保持**（实例）：给定具体下降实数 `X` 与 `hX : P X`，若它是原结构中编译矩阵
`compiled_matrix_m cH cE` 的反例，则限制结构在同一 `Subtype` 见证下满足 `∃set ¬` 矩阵。 -/
theorem compiled_counterexample_preserved_l (cH cE : PrimitiveProgram.code_m)
    (η : Env (restrict_l ℳ P hP) [] [sort_m.num])
    (X : set_l ℳ) (hX : P X)
    (hc : ¬ Formula.satisfies (M := ℳ) ((env_l P hP η).pushBound X)
        (compiled_matrix_m cH cE)) :
    Formula.satisfies (M := restrict_l ℳ P hP) η
      (.existsE sort_m.set (.neg (compiled_matrix_m cH cE))) :=
  counterexampleSet_preserved_l (compiled_matrix_m cH cE) (compiled_arithmetic_m cH cE)
    η X hX hc

/-! ## 公理审计

所有公共声明只引入构造性内容，不得有 `sorryAx` 或新公理。审计置于命名空间内、`end` 之前，
使各出口名可解析。 -/

#print axioms env_l_pushBound_set_l
#print axioms sat_pushBound_set_l
#print axioms sat_forallSet_l
#print axioms sat_existsSet_l
#print axioms forallSet_transport_l
#print axioms counterexampleSet_preserved_l
#print axioms compiled_arithmetic_m
#print axioms compiled_point_l
#print axioms compiled_matrix_correspondence_l
#print axioms compiled_forall_transport_l
#print axioms compiled_counterexample_preserved_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRestrictedQuantifier
