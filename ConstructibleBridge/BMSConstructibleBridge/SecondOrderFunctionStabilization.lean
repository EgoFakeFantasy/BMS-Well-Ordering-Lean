import BMSConstructibleBridge.SecondOrderFunctionMinimum
import BMSConstructibleBridge.SecondOrderModel
import BMSConstructibleBridge.SecondOrderNumbers
import BMSConstructibleBridge.SecondOrderAlgebra
import BMSConstructibleBridge.GraphSyntax

/-!
# 非增内部函数的轨道稳定化

值域最小元在 `SecondOrderFunctionMinimum` 只提供“下一步不严格更小”。本模块用实际
`∃ k, v + k = j` 公式对内部燃料做 `SecondOrderModel.induct_l` 归纳，得到从最小元位置
出发、任意内部偏移轨道上的值都 `≤ j`；再与最小元性质夹出等值。全部归纳在模型内部
数上进行，不假设宿主标准性，也不对非标准数域引入外部良序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionStabilization

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderNumbers SecondOrderPairing SecondOrderFunctions
open SecondOrderFunctionMinimum (minimum_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 除归纳变量外的自由槽 `[W, a, j]`；`pushFree` 反序装入，故 `W` 在头部。 -/
private abbrev Δ : SortContext signature_m := [.set, .num, .num]

/-- 归纳变量的完整自由上下文 `[d, W, a, j]`。 -/
private abbrev Φ : SortContext signature_m := .num :: Δ

/-- 把一个项推深一层数绑定；用于在量词内部复用自由槽访问器。 -/
private def sh {Γ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Φ s) : Term signature_m (.num :: Γ) Φ s :=
  t.weakenBound sort_m.num

private def addT {Γ : SortContext signature_m} (s t : Term signature_m Γ Φ .num) :
    Term signature_m Γ Φ .num :=
  Term.app (σ := signature_m) .add (.cons s (.cons t .nil))

/-- 自由槽 `d`：归纳变量。 -/
private def sd {Γ : SortContext signature_m} : Term signature_m Γ Φ .num := .fvar .here

/-- 自由槽 `W`：内部全函数实数。 -/
private def sW {Γ : SortContext signature_m} : Term signature_m Γ Φ .set :=
  .fvar (.there .here)

/-- 自由槽 `a`：最小元出现的位置。 -/
private def sa {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there .here))

/-- 自由槽 `j`：值域最小值。 -/
private def sj {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there (.there .here)))

/-- `v + k = j`：内层绑定变量是 `k`，外层绑定变量是 `v`。 -/
private def le_body : Formula signature_m [.num, .num] Φ :=
  .equal (addT (.bvar (.there .here)) (.bvar .here)) (sh (sh (sj (Γ := []))))

/-- 轨道上一步的值不超过最小元：`W @ (a + d) = v → ∃ k, v + k = j`。 -/
private def tail_body : Formula signature_m [.num] Φ :=
  .imp (GraphSyntax.edge_m (sW (Γ := [.num])) (addT (sh (sa (Γ := []))) (sh (sd (Γ := []))))
      (.bvar .here))
    (.existsE .num le_body)

/-- 实际轨道界公式：唯一外层量词绑定轨道值 `v`。 -/
def tail_le_m : Formula signature_m [] Φ := .forallE .num tail_body

/-- 轨道界公式只用加、相等、成员边与数量词。 -/
theorem tail_le_language_m : language_m tail_le_m = true := pure_language_m _ rfl

/-- 把 `j, a, W` 依次装入环境；归纳变量由 `pushFree` 追加在头部。 -/
private def envSlots (W : set_l ℳ) (a j : num_l ℳ) : Env ℳ [] Δ :=
  let η₀ := Env.pushFree (Env.empty (M := ℳ)) j
  let η₁ := Env.pushFree η₀ a
  Env.pushFree η₁ W

/-- 实际公式的解释逐值等于轨道界性质。 -/
theorem tail_le_syntax_l (W : set_l ℳ) (a j d : num_l ℳ) :
    Formula.satisfies (Env.pushFree (envSlots W a j) d) tail_le_m ↔
      ∀ v, relation_l W (add_l a d) v → ∃ k, add_l v k = j := by
  simp only [tail_le_m, tail_body, le_body, addT, sh, sd, sW, sa, sj, envSlots,
    Formula.satisfies, SecondOrderPairing.edge_l, Term.eval, Arguments.eval,
    Env.pushBound, Env.pushFree, Assignment.push]
  rfl

/-- 从最小元位置出发的任意内部轨道值都不超过最小元。归纳只走该公式自身的绑定变量，
偏移、位置与全部轨道值都取模型内部元素，不使用宿主 `Nat` 归纳。 -/
private theorem orbit_le_l (hℳ : Theory.Models ℳ theory_m) {W : set_l ℳ} (hW : function_l W)
    {a j : num_l ℳ} (haj : relation_l W a j)
    (hstep : ∀ i u v, relation_l W i u → relation_l W (succ_l i) v →
      SecondOrderOrder.lt_l v u ∨ v = u)
    {d v : num_l ℳ} (hv : relation_l W (add_l a d) v) : ∃ k, add_l v k = j := by
  refine induct_l hℳ tail_le_m tail_le_language_m (envSlots W a j)
    (fun e => ∀ v, relation_l W (add_l a e) v → ∃ k, add_l v k = j)
    (tail_le_syntax_l W a j) ?_ ?_ d v hv
  · intro w hw
    rw [add_zero_l hℳ] at hw
    obtain ⟨m, hm, hu⟩ := hW a
    have hwv : w = j := (hu w hw).trans (hu j haj).symm
    exact ⟨zero_l ℳ, (add_zero_l hℳ w).trans hwv⟩
  · intro ih ihyp w hw
    rw [add_succ_l hℳ] at hw
    obtain ⟨u, hu, _⟩ := hW (add_l a ih)
    obtain ⟨k, hk⟩ := ihyp u hu
    rcases hstep (add_l a ih) u w hu hw with hlt | heq
    · obtain ⟨e, rfl⟩ := hlt
      exact ⟨add_l (succ_l e) k, (add_assoc_l hℳ w (succ_l e) k).symm.trans hk⟩
    · exact ⟨k, by rw [heq]; exact hk⟩

/-- 非增内部函数在值域最小元位置之后恒等于该最小值：轨道上每个值既 `≤ j`（`orbit_le_l`）
又不严格小于 `j`（值域最小性），故逐值等于 `j`。结论排除“每条轨迹的秩沿轨道严格下降
但最终不恒定”之类的内部形状；不宣称非标准数域在宿主意义下良基。 -/
theorem stabilize_l (hℳ : Theory.Models ℳ theory_m) {W : set_l ℳ} (hW : function_l W)
    (hstep : ∀ i u v, relation_l W i u → relation_l W (succ_l i) v →
      SecondOrderOrder.lt_l v u ∨ v = u) :
    ∃ a j, relation_l W a j ∧ ∀ d v, relation_l W (add_l a d) v → v = j := by
  obtain ⟨a, j, haj, hmin⟩ := minimum_l hℳ hW
  refine ⟨a, j, haj, fun d v hv => ?_⟩
  obtain ⟨k, hk⟩ := orbit_le_l hℳ hW haj hstep hv
  rcases predecessor_l hℳ k with rfl | ⟨e, rfl⟩
  · rw [add_zero_l hℳ] at hk
    exact hk
  · exact absurd ⟨e, hk⟩ (hmin _ v hv)

#print axioms tail_le_m
#print axioms tail_le_syntax_l
#print axioms stabilize_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionStabilization
