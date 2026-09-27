import BMSConstructibleBridge.SecondOrderArithmetic
import BMSConstructibleBridge.SecondOrderRealRestriction
import BMSConstructibleBridge.SecondOrderRestrictedQuantifier

/-!
# 任务32：原九条基础公理沿同数域实数子域限制结构向下保持

任务30 构造了保留同一任意内部数域、把实数域缩到 `{X // P X}` 的限制结构
`restrict_l ℳ P hP`，并给出算术矩阵绝对性 `sat_arithmetic_l`；任务31 补齐了最外层
单个集合量词的向下传输。本模块**真正证明**原 `SecondOrderArithmetic.sentence_m k`
的九种 `base_m` 基础公理沿该限制结构向下保持，逐 `k` 得到出口

```
(sentence_m k).TrueIn ℳ → (sentence_m k).TrueIn (restrict_l ℳ P hP)。
```

分支策略：
* 七条数域公理（nonzero、injective、predecessor、add_zero、add_succ、mul_zero、
  mul_succ）只含数量词与数等式，`arithmetic_m = true`，直接由任务30 的算术绝对性
  配合 `env_l` 把限制侧空环境提升为原侧空环境下传；
* `induction` 最外层是单个 `∀set`，其主体为算术矩阵，复用任务31 的
  `forallSet_transport_l`；
* `extensionality` 含集合等式，**不**满足 `arithmetic_m`，改用原外延性假设与
  `Subtype.ext`（把限制结构中的 `mem` 通过 `restrict_mem_l` 落回原隶属）。

约束（遵 task32 brief）：`P` 只要求实数域非空（`hP`），不加入理解封闭或选择公理；
本文件只消去固定的九条基础公理义务，**不**声称限制结构满足 `theory_m`、满足任意
二阶正文的理解模式，或构成完整 `Z₂` 模型；不重做已验收的 24–31，不改其文件、聚合根、
配置、工具链或冻结原资源；不提交／推送／同步；`LEAN_NUM_THREADS = 1` 唯一串行，由
Codex 单目标 `--wfail` 编译。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRestrictedBase

open Logic FirstOrder SecondOrderSyntax SecondOrderModel SecondOrderRealRestriction
open SecondOrderArithmetic SecondOrderRestrictedQuantifier

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
variable {P : set_l ℳ → Prop} {hP : Nonempty {X // P X}}

/-- 本模块私有成员关系糖，逐字复用 `SecondOrderArithmetic` 中私有的构造，供外延分支的
`simp` 展开使用；不改动源文件、不引入新的对象符号。 -/
private def mem {Γ Δ : SortContext signature_m}
    (n : Term signature_m Γ Δ .num) (X : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  Formula.rel (σ := signature_m) .mem (.cons n (.cons X .nil))

/-! ## 环境提升把限制侧空环境映射为原侧空环境 -/

/-- `env_l` 把限制结构的空环境提升为原结构的空环境：空上下文无变量，按 `Env.ext`
  两端对不存在的变量索引 `nomatch` 消去。 -/
theorem env_l_empty_l :
    env_l P hP (Env.empty (M := restrict_l ℳ P hP)) = Env.empty (M := ℳ) := by
  apply Env.ext
  · intro s v
    exact nomatch v
  · intro s v
    exact nomatch v

/-! ## 算术闭句的向下保持 -/

/-- 算术闭句（`arithmetic_m = true`）的 `TrueIn` 沿限制结构向下保持：由任务30 的
  算术绝对性 `sat_arithmetic_l` 在空环境上取反向，并用 `env_l_empty_l` 把限制侧空环境
  的提升识别为原侧空环境。 -/
theorem arith_trueIn_l (φ : Sentence signature_m) (hφ : arithmetic_m φ = true)
    (h : φ.TrueIn ℳ) : φ.TrueIn (restrict_l ℳ P hP) := by
  have h₂ : Formula.satisfies (M := ℳ)
      (env_l P hP (Env.empty (M := restrict_l ℳ P hP))) φ := by
    rw [env_l_empty_l]
    exact h
  exact (sat_arithmetic_l φ hφ (Env.empty (M := restrict_l ℳ P hP))).mpr h₂

/-! ## 逐公理下传：七条数域公理 -/

/-- 非零：`succ n ≠ 0` 在限制结构保持。 -/
theorem nonzero_l (h : (sentence_m .nonzero).TrueIn ℳ) :
    (sentence_m .nonzero).TrueIn (restrict_l ℳ P hP) :=
  arith_trueIn_l _ (by decide) h

/-- 后继单射在限制结构保持。 -/
theorem injective_l (h : (sentence_m .injective).TrueIn ℳ) :
    (sentence_m .injective).TrueIn (restrict_l ℳ P hP) :=
  arith_trueIn_l _ (by decide) h

/-- 前驱存在在限制结构保持。 -/
theorem predecessor_l (h : (sentence_m .predecessor).TrueIn ℳ) :
    (sentence_m .predecessor).TrueIn (restrict_l ℳ P hP) :=
  arith_trueIn_l _ (by decide) h

/-- 加法零元在限制结构保持。 -/
theorem add_zero_l (h : (sentence_m .add_zero).TrueIn ℳ) :
    (sentence_m .add_zero).TrueIn (restrict_l ℳ P hP) :=
  arith_trueIn_l _ (by decide) h

/-- 加法后继方程在限制结构保持。 -/
theorem add_succ_l (h : (sentence_m .add_succ).TrueIn ℳ) :
    (sentence_m .add_succ).TrueIn (restrict_l ℳ P hP) :=
  arith_trueIn_l _ (by decide) h

/-- 乘法零元在限制结构保持。 -/
theorem mul_zero_l (h : (sentence_m .mul_zero).TrueIn ℳ) :
    (sentence_m .mul_zero).TrueIn (restrict_l ℳ P hP) :=
  arith_trueIn_l _ (by decide) h

/-- 乘法后继方程在限制结构保持。 -/
theorem mul_succ_l (h : (sentence_m .mul_succ).TrueIn ℳ) :
    (sentence_m .mul_succ).TrueIn (restrict_l ℳ P hP) :=
  arith_trueIn_l _ (by decide) h

/-! ## 逐公理下传：集合归纳（最外单个 `∀set`，主体算术） -/

/-- 集合归纳公理最外层 `∀set` 之下的真正主体：`X` 含 `0` 且对任意 `n` 封闭于后继，
  则含任意 `n`。用原始签名构造子与本模块私有 `mem` 书写，故 `arithmetic_m = true`
  且可被 `simp` 展开。 -/
private def ind_body : Formula signature_m [.set] [] :=
  .imp (.conj (mem (Term.app (σ := signature_m) .zero .nil) (.bvar .here))
      (.forallE .num (.imp (mem (.bvar .here) (.bvar (.there .here)))
        (mem (Term.app (σ := signature_m) .succ (.cons (.bvar .here) .nil))
          (.bvar (.there .here))))))
    (.forallE .num (mem (.bvar .here) (.bvar (.there .here))))

/-- `sentence_m .induction` 逐字等于对 `ind_body` 加最外层 `∀set`（定义一致，含原始
  私有的 `zero`/`succ` 糖与本模块 `mem`）。 -/
private theorem ind_eq : sentence_m .induction = .forallE sort_m.set ind_body := rfl

/-- 集合归纳公理向下保持：主体 `ind_body` 为算术矩阵，复用任务31 的
  `forallSet_transport_l`，在限制结构空环境上把原全称真值下传；`ind_eq` 使结论与
  `sentence_m .induction` 定义一致。 -/
theorem induction_l (h : (sentence_m .induction).TrueIn ℳ) :
    (sentence_m .induction).TrueIn (restrict_l ℳ P hP) := by
  have h₂ : Formula.satisfies (M := ℳ)
      (env_l P hP (Env.empty (M := restrict_l ℳ P hP))) (sentence_m .induction) := by
    rw [env_l_empty_l]
    exact h
  have key : Formula.satisfies (M := restrict_l ℳ P hP)
      (Env.empty (M := restrict_l ℳ P hP)) (sentence_m .induction) :=
    forallSet_transport_l ind_body (by decide) (Env.empty (M := restrict_l ℳ P hP)) h₂
  exact key

/-! ## 逐公理下传：集合外延（含集合等式，不走 arithmetic_m） -/

/-- 外延公理在最外层两个 `∀set` 之下的算术前件：`∀num, mem n A ↔ mem n B`，其中 `A`
  为外层集合（索引 `.there .there .here`）、`B` 为内层集合（索引 `.there .here`）。用本
  模块私有 `mem` 书写，便于 `simp` 消去。 -/
private def ext_ant : Formula signature_m [.set, .set] [] :=
  .forallE .num (.iff (mem (.bvar .here) (.bvar (.there (.there .here))))
    (mem (.bvar .here) (.bvar (.there .here))))

/-- 外延公理的集合等式后件：`A = B`（外层 = 内层）。 -/
private def ext_con : Formula signature_m [.set, .set] [] :=
  .equal (.bvar (.there .here)) (.bvar .here)

/-- 外延公理两个 `∀set` 之下的整体蕴涵式。 -/
private def ext_imp : Formula signature_m [.set, .set] [] := .imp ext_ant ext_con

/-- `sentence_m .extensionality` 逐字等于双层 `∀set` 加本模块书写的 `ext_imp`；两侧按
  定义一致（`mem` 与源文件的私有糖均为同一 `Formula.rel .mem`）。 -/
private theorem ext_eq :
    sentence_m .extensionality = .forallE sort_m.set (.forallE sort_m.set ext_imp) := rfl

/-- 集合外延公理向下保持：主体含集合等式，故不属于 `arithmetic_m`；改用原结构上的
  外延性假设 `h`，把限制结构中的 `mem` 经 `restrict_mem_l` 落回原隶属，得到
  `Subtype.val` 相等，再由 `Subtype.ext` 提升为 `{X // P X}` 上的相等。 -/
theorem extensionality_l (h : (sentence_m .extensionality).TrueIn ℳ) :
    (sentence_m .extensionality).TrueIn (restrict_l ℳ P hP) := by
  rw [Formula.TrueIn] at h ⊢
  rw [ext_eq] at h ⊢
  simp only [Formula.satisfies, ext_imp, ext_ant, ext_con, mem, Term.eval,
    Arguments.eval] at h ⊢
  change ∀ (X Y : {X : set_l ℳ // P X}),
      (∀ n : num_l ℳ, mem_l n X.val ↔ mem_l n Y.val) → X = Y
  change ∀ (X Y : set_l ℳ), (∀ n : num_l ℳ, mem_l n X ↔ mem_l n Y) → X = Y at h
  intro X Y hpre
  exact Subtype.ext (h X.val Y.val hpre)

/-! ## 统一出口：九条基础公理逐 `k` 下传 -/

/-- 原九条 `base_m` 基础公理沿 `restrict_l ℳ P hP` 向下保持：对任意 `k`，若
  `sentence_m k` 在原结构成立，则在限制结构成立。这里只逐分支消去固定基础公理的
  具体义务，**不**声称限制结构满足 `theory_m`。 -/
theorem base_axiom_l (k : base_m) (h : (sentence_m k).TrueIn ℳ) :
    (sentence_m k).TrueIn (restrict_l ℳ P hP) := by
  cases k
  · exact nonzero_l h
  · exact injective_l h
  · exact predecessor_l h
  · exact add_zero_l h
  · exact add_succ_l h
  · exact mul_zero_l h
  · exact mul_succ_l h
  · exact extensionality_l h
  · exact induction_l h

/-- 从原 `ℳ` 满足 `theory_m` 推出九条基础公理实例在限制结构中成立。仅消费
  `hℳ` 的 `axiom_m.base` 分支；不涉及任意二阶正文的理解公理，故不构成
  `restrict_l ℳ P hP` 满足 `theory_m`。 -/
theorem base_axioms_of_models_l (hℳ : Theory.Models ℳ theory_m) (k : base_m) :
    (sentence_m k).TrueIn (restrict_l ℳ P hP) :=
  base_axiom_l k (hℳ _ (axiom_m.base k))

/-! ## 公理审计

所有公共声明只引入构造性内容，不得有 `sorryAx` 或新公理。审计置于命名空间内、
`end` 之前，使各出口名可解析。 -/

#print axioms env_l_empty_l
#print axioms arith_trueIn_l
#print axioms nonzero_l
#print axioms injective_l
#print axioms predecessor_l
#print axioms add_zero_l
#print axioms add_succ_l
#print axioms mul_zero_l
#print axioms mul_succ_l
#print axioms induction_l
#print axioms extensionality_l
#print axioms base_axiom_l
#print axioms base_axioms_of_models_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRestrictedBase
