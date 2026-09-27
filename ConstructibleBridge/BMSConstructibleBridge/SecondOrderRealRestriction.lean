import BMSConstructibleBridge.SecondOrderSyntax
import BMSConstructibleBridge.SecondOrderModel

/-!
# 任务30：同数域、缩实数域的限制结构与算术/纯矩阵绝对性

为未来“给定下降实数的保守传输”真正构造一个**保留同一任意内部数域、缩小实数域**的
两排序结构 `restrict_l ℳ P hP`，沿逐 sort 包含（`num` 取恒等、`set` 取 `Subtype.val`）
给出环境提升 `env_l`，并证明两类矩阵在限制结构与原结构之间**逐点绝对**：

检查点1（真实结构 + 项/环境基础）：`restrict_l` 的 `num` 载体逐点等于原 `num_l ℳ`，
`set` 载体为 `{X // P X}`；五条函数（零、后继、加、乘、配对）在纯 `.num` 参数列上直接
复制原解释，`mem` 忘掉 `Subtype` 证据落回原隶属，`start`/`step` 在 `.num` 参数列上复制。
`embed_l`/`env_l` 给出逐 sort 包含与提升；本文件进一步证明全部项与参数列求值沿包含一致
（`eval_embed_l` / `args_embed_l`），及数量词分支的 `env_l` 与 `pushBound` 交换。

检查点2（算术/纯公式绝对性）：对**原** `Formula signature_m Γ Δ` 按其实际 AST 归纳，
若 `SecondOrderSyntax.arithmetic_m φ = true` 则 `restrict ⊨ η φ ↔ ℳ ⊨ env_l η φ`。算术检查器
禁止集合量词与集合等式（其分支在归纳里由 `hφ` 直接矛盾消去），但允许全部关系；因原
`start`/`step` 解释按 `.num` 域逐点复制、数量词域在 `num` 上**真的完全相同**，故成立。另证
`pure_m φ = true → arithmetic_m φ = true`，给纯矩阵绝对性。

约束（遵 task/30 brief）：`ℳ` 任意，不假定 `Theory.Models`；不假定 `P` 内部可定义或可选/可
收集；不宣称限制结构自动满足 `Z₂` 理解公理；不对集合量词偷用全射，也不宣称整个
`forall-set` 闭句双向绝对。本任务不构成本项目最终良序/保守传输闭合。不提交／推送／同步；
`LEAN_NUM_THREADS = 1` 唯一串行。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRealRestriction

open Logic FirstOrder SecondOrderSyntax SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
variable {P : set_l ℳ → Prop} {hP : Nonempty {X // P X}}

/-! ## 检查点1：真实限制结构与逐 sort 环境提升 -/

/-- 限制结构 `restrict_l ℳ P hP`：数域与原 `ℳ` 逐点相同，实数域缩到子类型 `{X // P X}`。
零、后继、加、乘、配对五函数在纯 `.num` 参数列上直接复用原解释；`mem` 取
`Subtype.val` 落回原隶属；`start`/`step` 在 `.num` 参数列上复用原关系。 -/
def restrict_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m)
    (P : set_l ℳ → Prop) (hP : Nonempty {X // P X}) :
    FirstOrder.Structure.{0, 0, 0, u} signature_m where
  Carrier
    | .num => num_l ℳ
    | .set => Subtype P
  nonempty
    | .num => ℳ.nonempty .num
    | .set => hP
  funcInterp
    | .zero, .nil => ℳ.funcInterp .zero .nil
    | .succ, .cons n .nil => ℳ.funcInterp .succ (.cons n .nil)
    | .add, .cons n (.cons m .nil) => ℳ.funcInterp .add (.cons n (.cons m .nil))
    | .mul, .cons n (.cons m .nil) => ℳ.funcInterp .mul (.cons n (.cons m .nil))
    | .pair, .cons n (.cons m .nil) => ℳ.funcInterp .pair (.cons n (.cons m .nil))
  relInterp
    | .mem, .cons n (.cons X .nil) => ℳ.relInterp .mem (.cons n (.cons X.val .nil))
    | .start, .cons n (.cons a .nil) => ℳ.relInterp .start (.cons n (.cons a .nil))
    | .step, .cons b (.cons a (.cons k .nil) ) =>
        ℳ.relInterp .step (.cons b (.cons a (.cons k .nil)) )

/-- 限制结构仍保留原数域：`.num` 载体逐点等于 `num_l ℳ`。 -/
theorem restrict_carrier_num_l (P : set_l ℳ → Prop) (hP : Nonempty {X // P X}) :
    (restrict_l ℳ P hP).Carrier sort_m.num = num_l ℳ := rfl

/-- 限制结构的实数域恰为 `{X // P X}`。 -/
theorem restrict_carrier_set_l (P : set_l ℳ → Prop) (hP : Nonempty {X // P X}) :
    (restrict_l ℳ P hP).Carrier sort_m.set = Subtype P := rfl

/-- 逐 sort 包含：`num` 上恒等，`set` 上取 `Subtype.val` 落回原载体。 -/
def embed_l (P : set_l ℳ → Prop) (hP : Nonempty {X // P X}) :
    (sort : sort_m) → (restrict_l ℳ P hP).Carrier sort → ℳ.Carrier sort
  | .num, x => x
  | .set, X => X.val

/-- 数域上包含为恒等。 -/
theorem embed_l_num_l (P : set_l ℳ → Prop) (hP : Nonempty {X // P X})
    (x : (restrict_l ℳ P hP).Carrier sort_m.num) : embed_l P hP sort_m.num x = x := rfl

/-- 把限制结构上的环境提升到原结构：逐变量套 `embed_l`。 -/
def env_l {Γ Δ : SortContext signature_m} (P : set_l ℳ → Prop) (hP : Nonempty {X // P X})
    (η : Env (restrict_l ℳ P hP) Γ Δ) : Env ℳ Γ Δ where
  boundVal := fun v => embed_l P hP _ (η.boundVal v)
  freeVal := fun v => embed_l P hP _ (η.freeVal v)

/-- 在数域绑定端，环境提升与 `pushBound` 交换：`num` 上包含是恒等，故提升后压入同值。 -/
theorem env_l_pushBound_l {Γ Δ : SortContext signature_m}
    (η : Env (restrict_l ℳ P hP) Γ Δ) (v : (restrict_l ℳ P hP).Carrier sort_m.num) :
    env_l P hP (η.pushBound v) = (env_l P hP η).pushBound v := by
  refine Env.ext (fun entry => ?_) (fun entry => ?_)
  · cases entry with
    | here => rfl
    | there e => rfl
  · rfl

/-! ## 关系解释的逐点保持

限制结构在三条原关系上与原结构逐点对应，是检查点1“真实结构”的可审计出口。 -/

/-- `mem` 沿包含落回原隶属关系。 -/
theorem restrict_mem_l (P : set_l ℳ → Prop) (hP : Nonempty {X // P X})
    (n : num_l ℳ) (X : {x : set_l ℳ // P x}) :
    (restrict_l ℳ P hP).relInterp rel_m.mem (.cons n (.cons X .nil) ) ↔
        ℳ.relInterp rel_m.mem (.cons n (.cons X.val .nil)) := Iff.rfl

/-- `start` 在 `.num` 参数列上按原数域复制。 -/
theorem restrict_start_l (P : set_l ℳ → Prop) (hP : Nonempty {X // P X})
    (n a : num_l ℳ) :
    (restrict_l ℳ P hP).relInterp rel_m.start (.cons n (.cons a .nil) ) ↔
        ℳ.relInterp rel_m.start (.cons n (.cons a .nil)) := Iff.rfl

/-- `step` 在 `.num` 参数列上按原数域复制。 -/
theorem restrict_step_l (P : set_l ℳ → Prop) (hP : Nonempty {X // P X})
    (b a k : num_l ℳ) :
    (restrict_l ℳ P hP).relInterp rel_m.step (.cons b (.cons a (.cons k .nil)) ) ↔
        ℳ.relInterp rel_m.step (.cons b (.cons a (.cons k .nil)) ) := Iff.rfl

/-! ## 检查点2 前置：函数/关系解释沿包含的逐点相等 -/

/-- 五个函数在限制结构上的解释，与原结构在 `embed_l` 逐点映射后的参数列上取值相同。
函数定义域全为 `.num`、值域恒 `.num`，故 `embed_l` 在其上是恒等；逐函数、逐参数列
构造子展开后为定义相等。 -/
theorem funcInterp_embed_l (f : func_m)
    (xs : Values (restrict_l ℳ P hP).Carrier (signature_m.funcDomain f)) :
    ℳ.funcInterp f (Values.map (embed_l P hP) xs) =
        embed_l P hP _ ((restrict_l ℳ P hP).funcInterp f xs) := by
  cases f
  · cases xs; rfl
  · cases xs with | cons n r => cases r; rfl
  · cases xs with | cons n r => cases r with | cons m r => cases r; rfl
  · cases xs with | cons n r => cases r with | cons m r => cases r; rfl
  · cases xs with | cons n r => cases r with | cons m r => cases r; rfl

/-- 三条关系在限制结构上的解释，与原结构在 `embed_l` 映射后的参数列上真值相同。
`mem` 忘掉 `Subtype` 证据；`start`/`step` 定义域全为 `.num`，包含为恒等。 -/
theorem relInterp_embed_l (r : rel_m)
    (xs : Values (restrict_l ℳ P hP).Carrier (signature_m.relDomain r)) :
    (restrict_l ℳ P hP).relInterp r xs ↔
        ℳ.relInterp r (Values.map (embed_l P hP) xs) := by
  cases r
  · cases xs with | cons n x => cases x with | cons X x => cases x; exact Iff.rfl
  · cases xs with | cons n x => cases x with | cons a x => cases x; exact Iff.rfl
  · cases xs with | cons b x => cases x with | cons a x => cases x with
      | cons k x => cases x; exact Iff.rfl

/-! ## 项与参数列求值沿包含一致（对原 `Term`/`Arguments` 互归纳） -/

mutual

/-- 任意项在限制结构上的求值，沿 `embed_l` 与原结构上提升环境的求值逐点一致。
变量端由 `env_l` 定义直接成立；函数端由 `funcInterp_embed_l` 与参数列 IH 合成。 -/
theorem eval_embed_l {Γ Δ : SortContext signature_m}
    (η : Env (restrict_l ℳ P hP) Γ Δ) :
    {s : sort_m} → (t : Term signature_m Γ Δ s) →
      embed_l P hP s (Term.eval η t) = Term.eval (env_l P hP η) t
  | _, .bvar _ => rfl
  | _, .fvar _ => rfl
  | _, .app f args => by
      simp only [Term.eval]
      rw [← args_embed_l η args]
      exact (funcInterp_embed_l f _).symm

/-- 任意参数列在限制结构上的逐项求值，经 `embed_l` 映射后与原结构提升环境的求值相等。
`nil` 端定义相等；`cons` 端由首项 `eval_embed_l` 与余下列 IH 逐点合成。 -/
theorem args_embed_l {Γ Δ : SortContext signature_m}
    (η : Env (restrict_l ℳ P hP) Γ Δ) :
    {sorts : List sort_m} → (args : Arguments signature_m Γ Δ sorts) →
      Values.map (embed_l P hP) (Arguments.eval η args) = Arguments.eval (env_l P hP η) args
  | _, .nil => rfl
  | s :: _, .cons t rest => by
      simp only [Arguments.eval, Values.map_cons]
      rw [eval_embed_l η t, args_embed_l η rest]

end

/-! ## 算术矩阵绝对性 -/

/-- 对**原** `Formula signature_m Γ Δ` 按实际 AST 归纳：算术矩阵检查通过时，限制结构与原
结构在同一提升环境上逐点满足同一公式。集合量词与集合等式由 `arithmetic_m = false` 排除，
其归纳分支由 `hφ` 矛盾消去；数量词域在 `num` 上真的相同，由 `env_l_pushBound_l` 交换后套
归纳假设。关系端复用 `relInterp_embed_l`，等式端复用 `eval_embed_l`。 -/
theorem sat_arithmetic_l {Γ Δ : SortContext signature_m}
    (φ : Formula signature_m Γ Δ) :
    arithmetic_m φ = true →
      (η : Env (restrict_l ℳ P hP) Γ Δ) →
        Formula.satisfies (M := restrict_l ℳ P hP) η φ ↔
          Formula.satisfies (M := ℳ) (env_l P hP η) φ := by
  induction φ with
  | falsum | truth => intro _ η; simp only [Formula.satisfies]
  | rel _ _ =>
      intro _ η
      simp only [Formula.satisfies]
      rw [← args_embed_l η _]
      exact relInterp_embed_l _ _
  | @equal Γ Δ sort s t =>
      cases sort with
      | num =>
          intro _ η
          simp only [Formula.satisfies]
          have hs : Term.eval (env_l P hP η) s = Term.eval η s := (eval_embed_l η s).symm
          have ht : Term.eval (env_l P hP η) t = Term.eval η t := (eval_embed_l η t).symm
          rw [hs, ht]
          exact Iff.rfl
      | set =>
          intro hφ _η
          exact absurd hφ (by simp [arithmetic_m])
  | neg ψ ih =>
      intro hφ η
      simp only [Formula.satisfies]
      rw [ih hφ η]
  | conj ψ₁ ψ₂ ih₁ ih₂ | disj ψ₁ ψ₂ ih₁ ih₂ | imp ψ₁ ψ₂ ih₁ ih₂ | iff ψ₁ ψ₂ ih₁ ih₂ =>
      intro hφ η
      obtain ⟨h₁, h₂⟩ := by simpa [arithmetic_m] using hφ
      simp only [Formula.satisfies, ih₁ h₁ η, ih₂ h₂ η]
  | forallE sort ψ ih =>
      cases sort with
      | num =>
          intro hφ η
          simp only [Formula.satisfies]
          constructor
          · intro h v
            have := ih hφ (η.pushBound v)
            rw [env_l_pushBound_l (P := P) (hP := hP) η v] at this
            exact this.mp (h v)
          · intro h v
            have := ih hφ (η.pushBound v)
            rw [env_l_pushBound_l (P := P) (hP := hP) η v] at this
            exact this.mpr (h v)
      | set =>
          intro hφ _η
          exact absurd hφ (by simp [arithmetic_m])
  | existsE sort ψ ih =>
      cases sort with
      | num =>
          intro hφ η
          simp only [Formula.satisfies]
          constructor
          · rintro ⟨v, hv⟩
            have := ih hφ (η.pushBound v)
            rw [env_l_pushBound_l (P := P) (hP := hP) η v] at this
            exact ⟨v, this.mp hv⟩
          · rintro ⟨v, hv⟩
            have := ih hφ (η.pushBound v)
            rw [env_l_pushBound_l (P := P) (hP := hP) η v] at this
            exact ⟨v, this.mpr hv⟩
      | set =>
          intro hφ _η
          exact absurd hφ (by simp [arithmetic_m])

/-! ## 纯矩阵绝对性 -/

/-- 纯算术检查蕴含算术矩阵检查：`pure_m` 拒绝的集合等式、集合量词恰使 `arithmetic_m` 取假；
`pure_m` 额外拒绝的 `start`/`step`/`pair` 在 `arithmetic_m` 下本就允许，故不影响该蕴含。
按原 AST 归纳，纯集合量词与纯集合等式分支由 `hφ` 矛盾消去。 -/
theorem pure_impl_arithmetic_l {Γ Δ : SortContext signature_m}
    (φ : Formula signature_m Γ Δ) : pure_m φ = true → arithmetic_m φ = true := by
  induction φ with
  | falsum | truth | rel _ _ => intro _; rfl
  | @equal Γ Δ sort s t =>
      cases sort with
      | num => intro _; rfl
      | set => intro hφ; exact absurd hφ (by simp [pure_m])
  | neg ψ ih =>
      intro hφ; exact ih (by simpa [pure_m] using hφ)
  | forallE sort ψ ih =>
      cases sort with
      | num => intro hφ; exact ih (by simpa [pure_m] using hφ)
      | set => intro hφ; exact absurd hφ (by simp [pure_m])
  | existsE sort ψ ih =>
      cases sort with
      | num => intro hφ; exact ih (by simpa [pure_m] using hφ)
      | set => intro hφ; exact absurd hφ (by simp [pure_m])
  | conj ψ₁ ψ₂ ih₁ ih₂ | disj ψ₁ ψ₂ ih₁ ih₂ | imp ψ₁ ψ₂ ih₁ ih₂ | iff ψ₁ ψ₂ ih₁ ih₂ =>
      intro hφ
      obtain ⟨h₁, h₂⟩ := by simpa [pure_m] using hφ
      simpa [arithmetic_m] using ⟨ih₁ h₁, ih₂ h₂⟩

/-- 纯矩阵绝对性：`pure_m φ = true` 时限制结构与原结构在同一提升环境上逐点满足同一 φ。
直接由 `pure_impl_arithmetic_l` 与算术绝对性合成，不改检查器定义。 -/
theorem sat_pure_l {Γ Δ : SortContext signature_m}
    (φ : Formula signature_m Γ Δ) :
    pure_m φ = true →
      (η : Env (restrict_l ℳ P hP) Γ Δ) →
        Formula.satisfies (M := restrict_l ℳ P hP) η φ ↔
          Formula.satisfies (M := ℳ) (env_l P hP η) φ := by
  intro hφ
  exact sat_arithmetic_l φ (pure_impl_arithmetic_l φ hφ)

/-! ## 公理审计

两检查点只引入构造性内容，不得有 `sorryAx` 或新公理。 -/
#print axioms restrict_l
#print axioms restrict_carrier_num_l
#print axioms restrict_carrier_set_l
#print axioms embed_l
#print axioms embed_l_num_l
#print axioms env_l
#print axioms env_l_pushBound_l
#print axioms restrict_mem_l
#print axioms restrict_start_l
#print axioms restrict_step_l
#print axioms funcInterp_embed_l
#print axioms relInterp_embed_l
#print axioms eval_embed_l
#print axioms args_embed_l
#print axioms sat_arithmetic_l
#print axioms pure_impl_arithmetic_l
#print axioms sat_pure_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRealRestriction
