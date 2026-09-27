import BMSConstructibleBridge.SecondOrderProgramAncestorBudget
import BMSConstructibleBridge.SecondOrderProgramAncestorStep
import BMSConstructibleBridge.SecondOrderProgramAncestorTransition
import BMSConstructibleBridge.SecondOrderProgramUniformParent
import BMSConstructibleBridge.SecondOrderProgramIteration
import BMSConstructibleBridge.SecondOrderProgramListIteration
import BMSConstructibleBridge.SecondOrderProgramListLength
import BMSConstructibleBridge.SecondOrderProgramLength
import BMSConstructibleBridge.SecondOrderProgramListShift
import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.SecondOrderNumbers
import BMSConstructibleBridge.SecondOrderProgramAncestorChain
import BMSConstructibleBridge.SecondOrderProgramAncestorStability
import BMSConstructibleBridge.SecondOrderProgramAncestorMembership
import BMSConstructibleBridge.SecondOrderProgramListReverse
import BMSConstructibleBridge.SecondOrderProgramListReverseEntries
import BMSConstructibleBridge.SecondOrderProgramListFold
import BMSConstructibleBridge.SecondOrderProgramListContains
import BMSConstructibleBridge.SecondOrderProgramReverseConsequences

/-!
# 祖先链在列号平移下的同步（阶段 A4 的归纳公式层）

`SecondOrderProgramAncestorIterationCongruence` 的共同状态公式只能处理「两侧同列号、
同累计码」的情形：它把公共列与公共累计器直接写进 `state_m`，因此无法表达本模块需要的
平移对应——平坦侧累计器内嵌的是 `A + col` 形列号，与局侧码并不相等。

本模块改用**逐位置**的链表对应作为不变量。链的成员测试经
`SecondOrderProgramAncestorMembership.member_nonzero_l` 已归约为
「链输出长度 + 查表图在真实长度内逐位置取值」，故只需

  两侧迭代状态同燃料、当前列号相差同一内部偏移 `A`、两累计器等长，
  且 `lookup v s = A + q ↔ lookup u s = q` 对全部内部位置成立。

元素本身是普通列号，所以 `A + q` 可纯语言写出；不需要在码层定义「把码里每个列号加 `A`」
的同态，也不引入共轭程序图或新的程序码。

父查询的平移对应作为显式前提 `hpp` 消费（由 `SecondOrderProgramParentRelocation` 的
三条搬运结论装配），本模块不对行号作外层归纳：真正的行归纳属后续装配模块。偏移 `A`、
块宽 `w`、起始列 `j`、燃料与全部列号都可取模型内部非标准元素；不使用宿主 `Nat` 归纳、
不要求外部标准性或矩形性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentRelocationAncestor

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramIteration
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramAncestorTransition (step_none_l step_some_l)
open SecondOrderProgramAncestorBudget (state_m state_syntax_l)
open SecondOrderProgramListShift (output_m output_syntax_l length_cons_l)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLength (length_zero_l)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListLookup (lookup_m lookup_cons_zero_l lookup_cons_succ_l)
open SecondOrderProgramAncestorChain (chain_m chain_rel_l)
open SecondOrderProgramAncestorStability (chain_ge_l)
open SecondOrderProgramAncestorMembership (member_m member_nonzero_l)
open SecondOrderProgramListReverse (reverse_m reverse_step_m)
open SecondOrderProgramListReverseEntries (reverse_length_l)
open SecondOrderProgramListFold (fold_m)
open SecondOrderProgramReverseConsequences (lookup_l index_exists_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 除燃料外的自由槽：`[参数状态, 局侧状态, 偏移, 块宽, 平坦初态, 局侧初态,
平坦迭代图, 局侧迭代图, 长度图, 查表图]`。 -/
private abbrev Δ : SortContext signature_m :=
  [.num, .num, .num, .num, .num, .num, .set, .set, .set, .set]

/-- 归纳变量在头部的完整自由上下文 `[fuel, X, Y, A, w, s₁, s₂, R, U, L, E]`。 -/
private abbrev Φ : SortContext signature_m := .num :: Δ

private def addT {Γ : SortContext signature_m} (s t : Term signature_m Γ Φ .num) :
    Term signature_m Γ Φ .num :=
  Term.app (σ := signature_m) .add (.cons s (.cons t .nil))

/-- 自由槽 `fuel`。 -/
private def sf {Γ : SortContext signature_m} : Term signature_m Γ Φ .num := .fvar .here

/-- 自由槽 `X`：平坦侧的外层参数状态。 -/
private def sX {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there .here)

/-- 自由槽 `Y`：局侧的外层参数状态。 -/
private def sY {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there .here))

/-- 自由槽 `A`：内部列偏移。 -/
private def sA {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there (.there .here)))

/-- 自由槽 `w`：块宽，用于维持当前列不越出本块。 -/
private def sw {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there (.there (.there .here))))

/-- 自由槽 `s₁`：平坦侧迭代初态。 -/
private def sS1 {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there (.there (.there (.there .here)))))

/-- 自由槽 `s₂`：局侧迭代初态。 -/
private def sS2 {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  .fvar (.there (.there (.there (.there (.there (.there .here))))))

/-- 自由槽 `R`：平坦侧迭代图。 -/
private def sR {Γ : SortContext signature_m} : Term signature_m Γ Φ .set :=
  .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))

/-- 自由槽 `U`：局侧迭代图。 -/
private def sU {Γ : SortContext signature_m} : Term signature_m Γ Φ .set :=
  .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))

/-- 自由槽 `L`：内部长度图。 -/
private def sL {Γ : SortContext signature_m} : Term signature_m Γ Φ .set :=
  .fvar
    (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))

/-- 自由槽 `E`：内部查表图。 -/
private def sE {Γ : SortContext signature_m} : Term signature_m Γ Φ .set :=
  .fvar
    (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there
      .here))))))))))

/-- 实际共同状态：两侧同燃料状态的当前列相差 `A`，两累计器等长且逐位置平移对应。
绑定顺序（外层到内层）为 `a, b, col, len, u, v`。 -/
def coupled_shift_l (X Y A w s₁ s₂ : num_l ℳ) (R U L E : set_l ℳ) (n : num_l ℳ) : Prop :=
  ∃ a b col len u v,
    relation_l R (value_l s₁ n) a ∧ value_l X (value_l (add_l A col) v) = a ∧
      relation_l U (value_l s₂ n) b ∧ value_l Y (value_l col u) = b ∧
        relation_l L v len ∧ relation_l L u len ∧
          SecondOrderOrder.lt_l col w ∧
            ∀ s q, SecondOrderOrder.lt_l s len →
              (relation_l E (value_l v s) (add_l A q) ↔ relation_l E (value_l u s) q)

/-- 六层存在量词内部的绑定上下文 `[a, b, col, len, u, v]`（内层优先，`.bvar .here = v`）。 -/
private abbrev Γ6 : SortContext signature_m := [.num, .num, .num, .num, .num, .num]

/-- 再绑定内部位置与元素列号后的上下文 `[q, s, v, u, len, col, b, a]`。 -/
private abbrev Γ8 : SortContext signature_m := [.num, .num, .num, .num, .num, .num, .num, .num]

private def bv_v : Term signature_m Γ6 Φ .num := .bvar .here

private def bv_u : Term signature_m Γ6 Φ .num := .bvar (.there .here)

private def bv_len : Term signature_m Γ6 Φ .num := .bvar (.there (.there .here))

private def bv_col : Term signature_m Γ6 Φ .num :=
  .bvar (.there (.there (.there .here)))

private def bv_b : Term signature_m Γ6 Φ .num :=
  .bvar (.there (.there (.there (.there .here))))

private def bv_a : Term signature_m Γ6 Φ .num :=
  .bvar (.there (.there (.there (.there (.there .here)))))

private def pv_q : Term signature_m Γ8 Φ .num := .bvar .here

private def pv_s : Term signature_m Γ8 Φ .num := .bvar (.there .here)

private def pv_v : Term signature_m Γ8 Φ .num := .bvar (.there (.there .here))

private def pv_u : Term signature_m Γ8 Φ .num := .bvar (.there (.there (.there .here)))

private def pv_len : Term signature_m Γ8 Φ .num :=
  .bvar (.there (.there (.there (.there .here))))

/-- 平坦侧迭代图在第 `fuel` 步的输出就是共同状态码。 -/
private def conj1 : Formula signature_m Γ6 Φ := output_m sR sS1 sf bv_a

/-- 该输出码分解为 `pair X (pair (A + col) v)`。 -/
private def conj2 : Formula signature_m Γ6 Φ := state_m sX (addT sA bv_col) bv_v bv_a

/-- 局侧迭代图在第 `fuel` 步的输出就是局侧共同状态码。 -/
private def conj3 : Formula signature_m Γ6 Φ := output_m sU sS2 sf bv_b

/-- 局侧输出码分解为 `pair Y (pair col u)`，与平坦侧共用当前列 `col`。 -/
private def conj4 : Formula signature_m Γ6 Φ := state_m sY bv_col bv_u bv_b

/-- 平坦侧累计表的内部长度。 -/
private def conj5 : Formula signature_m Γ6 Φ := GraphSyntax.edge_m sL bv_v bv_len

/-- 局侧累计表有同一内部长度。 -/
private def conj6 : Formula signature_m Γ6 Φ := GraphSyntax.edge_m sL bv_u bv_len

/-- 当前列不越出本块，保证下一步仍可消费父查询的平移对应。 -/
private def conj7 : Formula signature_m Γ6 Φ := PrimitiveFormulas.lt_m bv_col sw

/-- 真实长度内两累计表逐位置相差同一偏移 `A`。 -/
private def pos_f : Formula signature_m Γ8 Φ :=
  .imp (PrimitiveFormulas.lt_m pv_s pv_len)
    (.iff (output_m sE pv_v pv_s (addT sA pv_q)) (output_m sE pv_u pv_s pv_q))

private def conj8 : Formula signature_m Γ6 Φ := .forallE .num (.forallE .num pos_f)

/-- 八条合取的正文。 -/
private def coupled_shift_body : Formula signature_m Γ6 Φ :=
  .conj conj1 (.conj conj2 (.conj conj3 (.conj conj4 (.conj conj5 (.conj conj6 (.conj conj7 conj8))))))

/-- 归纳正文：六层存在量词绑定共同状态、当前列、两累计表与共同长度。 -/
def coupled_shift_m : Formula signature_m [] Φ :=
  .existsE .num
    (.existsE .num
      (.existsE .num
        (.existsE .num (.existsE .num (.existsE .num coupled_shift_body)))))

/-- 共同状态公式只用零、后继、加、配对、成员边与数量词。 -/
theorem coupled_shift_language_m : language_m coupled_shift_m = true := pure_language_m _ rfl

/-- 把十个自由槽依次装入环境；归纳变量由 `pushFree` 追加在头部。 -/
private def envSlots (R U L E : set_l ℳ) (X Y A w s₁ s₂ : num_l ℳ) : Env ℳ [] Δ :=
  let η₀ := Env.pushFree (Env.empty (M := ℳ)) E
  let η₁ := Env.pushFree η₀ L
  let η₂ := Env.pushFree η₁ U
  let η₃ := Env.pushFree η₂ R
  let η₄ := Env.pushFree η₃ s₂
  let η₅ := Env.pushFree η₄ s₁
  let η₆ := Env.pushFree η₅ w
  let η₇ := Env.pushFree η₆ A
  let η₈ := Env.pushFree η₇ Y
  Env.pushFree η₈ X

/-- 实际公式的解释逐字等于所需的平移共同状态。 -/
theorem coupled_shift_syntax_l (X Y A w s₁ s₂ : num_l ℳ) (R U L E : set_l ℳ) (n : num_l ℳ) :
    Formula.satisfies (Env.pushFree (envSlots R U L E X Y A w s₁ s₂) n) coupled_shift_m ↔
      coupled_shift_l X Y A w s₁ s₂ R U L E n := by
  simp only [coupled_shift_m, coupled_shift_l, coupled_shift_body, conj1, conj2, conj3, conj4,
    conj5, conj6, conj7, conj8, pos_f, bv_v, bv_u, bv_len, bv_col, bv_b, bv_a, pv_q, pv_s, pv_v,
    pv_u, pv_len, envSlots, Formula.satisfies, state_syntax_l,
    output_syntax_l, SecondOrderPairing.edge_l, SecondOrderOrder.formula_l,
    SecondOrderOrder.lt_l, addT, sf, sX, sY, sA, sw, sS1, sS2, sR, sU, sL, sE, Term.eval,
    Arguments.eval, Env.pushBound, Env.pushFree, Assignment.push]
  rfl

/-- 平坦侧的原起始状态：当前列带内部偏移 `A`，累计器为空码。 -/
noncomputable def flat_start_l (X A j : num_l ℳ) : num_l ℳ :=
  value_l X (value_l (add_l A j) (zero_l ℳ))

/-- 局侧的原起始状态：当前列为 `j`，累计器为空码。 -/
noncomputable def local_start_l (Y j : num_l ℳ) : num_l ℳ := value_l Y (value_l j (zero_l ℳ))

/-- 界内父查询的平移对应与局侧严格下降一起，使两个原迭代图在任意内部燃料下保持
同偏移当前列、等长累计表与逐位置平移对应。归纳只走实际公式 `coupled_shift_m`，
偏移、块宽、起始列、燃料与全部列号均可取模型内部非标准元素；不使用宿主 `Nat` 归纳。 -/
theorem common_state_shift_l (hℳ : Theory.Models ℳ theory_m) (c d : code_m)
    {C D R U L E : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) (hD : graph_semantics_l (graph_m d) D)
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hU : graph_semantics_l (graph_m (repeat_m (step_m d))) U)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (X Y A w j : num_l ℳ) (hj : SecondOrderOrder.lt_l j w)
    (hdown : ∀ k p, relation_l D (value_l Y k) (succ_l p) → SecondOrderOrder.lt_l p k)
    (hpp : ∀ k z, SecondOrderOrder.lt_l k w →
      (relation_l C (value_l X (add_l A k)) z ↔
        (z = zero_l ℳ ∧ relation_l D (value_l Y k) (zero_l ℳ)) ∨
          ∃ q, z = succ_l (add_l A q) ∧ relation_l D (value_l Y k) (succ_l q)))
    (n : num_l ℳ) :
    coupled_shift_l X Y A w (flat_start_l X A j) (local_start_l Y j) R U L E n := by
  letI := order_l hℳ
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (step_m c)
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ (step_m d)
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  apply induct_l hℳ coupled_shift_m coupled_shift_language_m
    (envSlots R U L E X Y A w (flat_start_l X A j) (local_start_l Y j))
    (fun n => coupled_shift_l X Y A w (flat_start_l X A j) (local_start_l Y j) R U L E n)
    (coupled_shift_syntax_l X Y A w (flat_start_l X A j) (local_start_l Y j) R U L E) ?_ ?_ n
  · exact ⟨flat_start_l X A j, local_start_l Y j, j, zero_l ℳ, zero_l ℳ, zero_l ℳ,
      (repeat_zero_l hℳ (step_m c) hR _ _).mpr rfl, rfl,
      (repeat_zero_l hℳ (step_m d) hU _ _).mpr rfl, rfl,
      (length_rel_l hℳ hL hI _ _).mpr ((length_zero_l hℳ hI _).mpr rfl),
      (length_rel_l hℳ hL hI _ _).mpr ((length_zero_l hℳ hI _).mpr rfl),
      hj, fun s q hs => False.elim ((not_lt_of_ge (zero_le_l hℳ s)) hs)⟩
  · rintro f ⟨a, b, col, len, u, v, hr, he, hu, he', hlv, hlu, hcol, hpos⟩
    subst a
    subst b
    obtain ⟨q, hq, _⟩ := function_of_semantics_l hℳ d hD (value_l Y col)
    rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
    · have hnone : relation_l C (value_l X (add_l A col)) (zero_l ℳ) :=
          (hpp col (zero_l ℳ) hcol).mpr (Or.inl ⟨rfl, hq⟩)
      exact ⟨value_l X (value_l (add_l A col) v), value_l Y (value_l col u), col, len, u, v,
        (repeat_succ_l hℳ (step_m c) hR hS _ f _).mpr
          ⟨_, hr, (step_none_l hℳ c hS hC hnone v _).mpr rfl⟩, rfl,
        (repeat_succ_l hℳ (step_m d) hU hT _ f _).mpr
          ⟨_, hu, (step_none_l hℳ d hT hD hq u _).mpr rfl⟩, rfl, hlv, hlu, hcol, hpos⟩
    · have hCq : relation_l C (value_l X (add_l A col)) (succ_l (add_l A p)) :=
          (hpp col _ hcol).mpr (Or.inr ⟨p, rfl, hq⟩)
      have hpc : p < w := lt_trans (hdown col p hq) hcol
      exact ⟨value_l X (value_l (add_l A p) (succ_l (value_l (add_l A p) v))),
          value_l Y (value_l p (succ_l (value_l p u))), p, succ_l len, succ_l (value_l p u),
          succ_l (value_l (add_l A p) v),
        (repeat_succ_l hℳ (step_m c) hR hS _ f _).mpr
          ⟨_, hr, (step_some_l hℳ c hS hC hCq v _).mpr rfl⟩, rfl,
        (repeat_succ_l hℳ (step_m d) hU hT _ f _).mpr
          ⟨_, hu, (step_some_l hℳ d hT hD hq u _).mpr rfl⟩, rfl,
        (length_rel_l hℳ hL hI _ _).mpr
          ((length_cons_l hℳ hI (add_l A p) v len).mpr ((length_rel_l hℳ hL hI _ _).mp hlv)),
        (length_rel_l hℳ hL hI _ _).mpr
          ((length_cons_l hℳ hI p u len).mpr ((length_rel_l hℳ hL hI _ _).mp hlu)),
        hpc,
        fun s q hs => by
          rcases predecessor_l hℳ s with rfl | ⟨i, rfl⟩
          · exact (lookup_cons_zero_l hℳ hE (add_l A p) v (add_l A q)).trans
              ((SecondOrderNumbers.add_cancel_l hℳ A p q).trans
                (lookup_cons_zero_l hℳ hE p u q).symm)
          · exact (lookup_cons_succ_l hℳ hE (add_l A p) v i (add_l A q)).trans
              ((hpos i q ((SecondOrderOrder.succ_iff_l hℳ i len).mp hs)).trans
                (lookup_cons_succ_l hℳ hE p u i q).symm)⟩

/-- 段内列偏移不把内部列号推低：`j = K + j ∨ j < K + j`，供局侧燃料裁剪。 -/
private theorem le_add_left_l (hℳ : Theory.Models ℳ theory_m) (K j : num_l ℳ) :
    j = add_l K j ∨ SecondOrderOrder.lt_l j (add_l K j) := by
  rcases predecessor_l hℳ K with rfl | ⟨k, rfl⟩
  · exact Or.inl ((SecondOrderNumbers.zero_add_l hℳ j).symm)
  · exact Or.inr ⟨k, by
      rw [add_succ_l hℳ, SecondOrderNumbers.succ_add_l hℳ, SecondOrderNumbers.add_comm_l hℳ]⟩

/-- 状态码 `pair a (pair b c)` 的反配对累计器坐标就是 `c`，含内部非标准分量。 -/
private theorem acc_two_l (hℳ : Theory.Models ℳ theory_m) (a b c : num_l ℳ) :
    (SecondOrderUnpairing.value_l hℳ
        (SecondOrderUnpairing.value_l hℳ (value_l a (value_l b c))).2).2 = c := by
  rw [SecondOrderUnpairing.unpair_l, SecondOrderUnpairing.unpair_l]

/-- 祖先成员测试在内部列平移下的同步：平坦侧 parent 图 `C₁` 在列 `K + k` 上的输出
是局侧 `C₂` 在列 `k` 上输出的同一平移编码，于是两个原成员程序对平移候选列给出相同
真值。两侧的燃料都是各自的目标列，局侧链由 `chain_ge_l` 从共同燃料 `K + j` 裁回 `j`；
全程不做宿主 `Nat` 归纳、不要求外部标准性、不假定矩形性。 -/
theorem ancestor_shift_l (hℳ : Theory.Models ℳ theory_m) (c d : code_m)
    {A₁ A₂ C₁ C₂ : set_l ℳ} (hA₁ : graph_semantics_l (graph_m (chain_m c)) A₁)
    (hA₂ : graph_semantics_l (graph_m (chain_m d)) A₂)
    (hC₁ : graph_semantics_l (graph_m c) C₁) (hC₂ : graph_semantics_l (graph_m d) C₂)
    {R₁ R₂ T L E : set_l ℳ}
    (hR₁ : graph_semantics_l (graph_m (repeat_m (step_m c))) R₁)
    (hR₂ : graph_semantics_l (graph_m (repeat_m (step_m d))) R₂)
    (hT : graph_semantics_l (graph_m reverse_m) T)
    (hL : graph_semantics_l (graph_m length_m) L) (hE : graph_semantics_l (graph_m lookup_m) E)
    {B₁ B₂ : set_l ℳ} (hB₁ : graph_semantics_l (graph_m (member_m c)) B₁)
    (hB₂ : graph_semantics_l (graph_m (member_m d)) B₂)
    (P Q K w j : num_l ℳ) (hj : SecondOrderOrder.lt_l j w)
    (hdown : ∀ k p, relation_l C₂ (value_l Q k) (succ_l p) → SecondOrderOrder.lt_l p k)
    (hpp : ∀ k z, SecondOrderOrder.lt_l k w →
      (relation_l C₁ (value_l P (add_l K k)) z ↔
        (z = zero_l ℳ ∧ relation_l C₂ (value_l Q k) (zero_l ℳ)) ∨
          ∃ q, z = succ_l (add_l K q) ∧ relation_l C₂ (value_l Q k) (succ_l q)))
    (q : num_l ℳ) :
    ¬relation_l B₁ (value_l (value_l P (add_l K j)) (add_l K q)) (zero_l ℳ) ↔
      ¬relation_l B₂ (value_l (value_l Q j) q) (zero_l ℳ) := by
  letI := order_l hℳ
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (fold_m reverse_step_m)
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨a, b, col, len, u, v, h1, h2, h3, h4, hlv, hlu, hcol, hpos⟩ :=
    common_state_shift_l hℳ c d hC₁ hC₂ hR₁ hR₂ hL hE P Q K w j hj hdown hpp (add_l K j)
  -- 同一燃料下两侧迭代输出码，其累计器坐标由共同状态给出。
  have h1' : relation_l R₁ (value_l (flat_start_l P K j) (add_l K j))
      (value_l P (value_l (add_l K col) v)) := by rw [h2]; exact h1
  have h3' : relation_l R₂ (value_l (local_start_l Q j) (add_l K j))
      (value_l Q (value_l col u)) := by rw [h4]; exact h3
  obtain ⟨y_v, hy_v, _⟩ := function_of_semantics_l hℳ reverse_m hT v
  obtain ⟨y_u, hy_u, _⟩ := function_of_semantics_l hℳ reverse_m hT u
  have hlen_v : relation_l L y_v len := reverse_length_l hℳ hT hF hL hI v y_v len hy_v hlv
  have hlen_u : relation_l L y_u len := reverse_length_l hℳ hT hF hL hI u y_u len hy_u hlu
  -- 平坦侧链的输出就是 `y_v`，其目标列本身就是 `K + j`；局侧链再由稳定性裁回 `j`。
  have hchain₁ : relation_l A₁ (value_l (value_l P (add_l K j)) (add_l K j)) y_v :=
    (chain_rel_l hℳ c hA₁ hR₁ hT P (add_l K j) (add_l K j) y_v).mpr
      ⟨value_l P (value_l (add_l K col) v), h1', by
        rw [acc_two_l hℳ P (add_l K col) v]; exact hy_v⟩
  have hchain₂ : relation_l A₂ (value_l (value_l Q j) j) y_u := by
    have hfuel : relation_l A₂ (value_l (value_l Q j) (add_l K j)) y_u :=
      (chain_rel_l hℳ d hA₂ hR₂ hT Q j (add_l K j) y_u).mpr
        ⟨value_l Q (value_l col u), h3', by rw [acc_two_l hℳ Q col u]; exact hy_u⟩
    exact (chain_ge_l hℳ d hA₂ hC₂ Q j (add_l K j) y_u hdown
      (le_add_left_l hℳ K j)).mp hfuel
  -- 逐位置平移对应从两个累计表传到各自的原反转输出。
  have pos_rev : ∀ s : num_l ℳ, SecondOrderOrder.lt_l s len →
      (relation_l E (value_l y_v s) (add_l K q) ↔ relation_l E (value_l y_u s) q) := by
    intro s hs
    obtain ⟨k, hk, hkl⟩ := index_exists_l hℳ hs
    exact ((lookup_l hℳ hT hL hE hy_v hlv hk (add_l K q)).trans
      (hpos k q hkl)).trans (lookup_l hℳ hT hL hE hy_u hlu hk q).symm
  have hB₁ : ¬relation_l B₁ (value_l (value_l P (add_l K j)) (add_l K q)) (zero_l ℳ) ↔
      ∃ s, SecondOrderOrder.lt_l s len ∧ relation_l E (value_l y_v s) (add_l K q) :=
    member_nonzero_l hℳ c hB₁ hA₁ hL hE hchain₁ hlen_v (add_l K q)
  have hB₂ : ¬relation_l B₂ (value_l (value_l Q j) q) (zero_l ℳ) ↔
      ∃ s, SecondOrderOrder.lt_l s len ∧ relation_l E (value_l y_u s) q :=
    member_nonzero_l hℳ d hB₂ hA₂ hL hE hchain₂ hlen_u q
  exact hB₁.trans ((exists_congr fun s => and_congr_right (pos_rev s)).trans hB₂.symm)

#print axioms le_add_left_l
#print axioms acc_two_l
#print axioms ancestor_shift_l
#print axioms flat_start_l
#print axioms local_start_l
#print axioms coupled_shift_l
#print axioms coupled_shift_m
#print axioms coupled_shift_language_m
#print axioms coupled_shift_syntax_l
#print axioms common_state_shift_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentRelocationAncestor
