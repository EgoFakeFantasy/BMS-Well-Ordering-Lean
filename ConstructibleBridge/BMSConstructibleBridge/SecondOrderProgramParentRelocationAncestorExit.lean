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
# 父链出段后的祖先成员同步（阶段 A5 后继步的祖先半边）

`SecondOrderProgramParentRelocationAncestor` 的共同状态把两侧当前列钉成 `A + col`，因此其
步例需要父查询平移对应的 none↔none 支：局部父缺项当且仅当平坦父缺项。该支对第 `k≥1`
份副本为假——坏块内部列 `j` 的局部父可以为 none，而更早副本中条目更小的列仍使平坦父
落在 `[0, K)`，于是平坦链先于局链离开本块段。

本模块改用弱化父对应 `hpp : C(X@(K+k)) = succ (K+q) ↔ D(Y@k) = succ q`（只在段内成立，由
`SecondOrderProgramCopiesBlockParentShift.reloc_ge_m` 给出），并把共同状态的列条件换成二分：
当前平坦列 `colf` 要么已低于偏移 `K`（此时局侧必已冻结），要么仍等于 `K + coll`。两侧累计
表不再要求逐位置对齐，只要求**值集合**在偏移下互相覆盖：

  平坦累计表里形如 `K + p` 的值，恰好是局侧累计表里的值。

平坦链离开段后新追加的列全部 `< K`（父列严格下降），故永不形如 `K + p`，两条覆盖条件在
冻结与出段两种演化下都保持；链成员测试只关心值是否出现、不关心位置，于是出段尾巴被自动
忽略。据此得到段内祖先成员在列平移下的同步，供按行归纳把 `¬M` 半边喂给
`parent_some_congr_l`。偏移、块宽、起始列、燃料与全部列号均可取模型内部非标准元素；
不使用宿主 `Nat` 归纳、不要求外部标准性或矩形性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentRelocationAncestorExit

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
open SecondOrderProgramReverseConsequences (lookup_l index_exists_l index_symm_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 除燃料外的自由槽：`[平坦参数状态, 局侧参数状态, 偏移, 块宽, 平坦初态, 局侧初态,
平坦迭代图, 局侧迭代图, 局侧父图, 长度图, 查表图]`。 -/
private abbrev Δ : SortContext signature_m :=
  [.num, .num, .num, .num, .num, .num, .set, .set, .set, .set, .set]

/-- 归纳变量在头部的完整自由上下文 `[fuel, X, Y, A, w, s₁, s₂, R, U, D, L, E]`。 -/
private abbrev Φ : SortContext signature_m := .num :: Δ

private def addT {Γ : SortContext signature_m} (s t : Term signature_m Γ Φ .num) :
    Term signature_m Γ Φ .num :=
  Term.app (σ := signature_m) .add (.cons s (.cons t .nil))

private def zeroT {Γ : SortContext signature_m} : Term signature_m Γ Φ .num :=
  Term.app (σ := signature_m) .zero .nil

/-- 把一个项推深一层数绑定；用于复用外层访问器。 -/
private def sh {Γ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Φ s) : Term signature_m (.num :: Γ) Φ s :=
  t.weakenBound sort_m.num

/-- 自由槽 `fuel`。 -/
private def sf {Γ : SortContext signature_m} : Term signature_m Γ Φ .num  := .fvar .here

/-- 自由槽 `X`：平坦侧外层参数状态。 -/
private def sX {Γ : SortContext signature_m} : Term signature_m Γ Φ .num  := .fvar (.there .here)

/-- 自由槽 `Y`：局侧外层参数状态。 -/
private def sY {Γ : SortContext signature_m} : Term signature_m Γ Φ .num  := .fvar (.there (.there .here))

/-- 自由槽 `A`：内部列偏移 `K`。 -/
private def sA {Γ : SortContext signature_m} : Term signature_m Γ Φ .num  := .fvar (.there (.there (.there .here)))

/-- 自由槽 `w`：块宽。 -/
private def sw {Γ : SortContext signature_m} : Term signature_m Γ Φ .num  := .fvar (.there (.there (.there (.there .here))))

/-- 自由槽 `s₁`：平坦侧迭代初态。 -/
private def sS1 {Γ : SortContext signature_m} : Term signature_m Γ Φ .num  := .fvar (.there (.there (.there (.there (.there .here)))))

/-- 自由槽 `s₂`：局侧迭代初态。 -/
private def sS2 {Γ : SortContext signature_m} : Term signature_m Γ Φ .num  := .fvar (.there (.there (.there (.there (.there (.there .here))))))

/-- 自由槽 `R`：平坦侧迭代图。 -/
private def sR {Γ : SortContext signature_m} : Term signature_m Γ Φ .set  := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))

/-- 自由槽 `U`：局侧迭代图。 -/
private def sU {Γ : SortContext signature_m} : Term signature_m Γ Φ .set  := .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))

/-- 自由槽 `D`：局侧父图，用于表达出段后局侧已冻结。 -/
private def sD {Γ : SortContext signature_m} : Term signature_m Γ Φ .set  := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))

/-- 自由槽 `L`：内部长度图。 -/
private def sL {Γ : SortContext signature_m} : Term signature_m Γ Φ .set  := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))

/-- 自由槽 `E`：内部查表图。 -/
private def sE {Γ : SortContext signature_m} : Term signature_m Γ Φ .set  := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))

/-- 实际出段共同状态：两侧同燃料，平坦当前列要么已低于偏移（此时局侧父缺项、状态冻结），
要么仍等于 `A + coll`；两累计表长度各自独立，只要求值集合在偏移 `A` 下互相覆盖。
绑定顺序（外层到内层）为 `a, b, colf, coll, lenf, lenl, u, v`。 -/
def exit_state_l (X Y A w s₁ s₂ : num_l ℳ) (R U D L E : set_l ℳ) (n : num_l ℳ) : Prop :=
  ∃ a b colf coll lenf lenl u v,
    relation_l R (value_l s₁ n) a ∧ value_l X (value_l colf v) = a ∧
      relation_l U (value_l s₂ n) b ∧ value_l Y (value_l coll u) = b ∧
        relation_l L v lenf ∧ relation_l L u lenl ∧
          ((SecondOrderOrder.lt_l colf A ∧
              relation_l D (value_l Y coll) (zero_l ℳ)) ∨
            (SecondOrderOrder.lt_l coll w ∧ colf = add_l A coll)) ∧
            (∀ p, (∃ s, SecondOrderOrder.lt_l s lenf ∧
                relation_l E (value_l v s) (add_l A p)) →
              (∃ t, SecondOrderOrder.lt_l t lenl ∧ relation_l E (value_l u t) p)) ∧
              (∀ p, (∃ t, SecondOrderOrder.lt_l t lenl ∧ relation_l E (value_l u t) p) →
                (∃ s, SecondOrderOrder.lt_l s lenf ∧
                  relation_l E (value_l v s) (add_l A p)))

/-- 八层绑定后的上下文，内层优先顺序为 `v, u, lenl, lenf, coll, colf, b, a`。 -/
private abbrev Γ8 : SortContext signature_m :=
  [.num, .num, .num, .num, .num, .num, .num, .num]

private def bv_a : Term signature_m Γ8 Φ .num  := .bvar (.there (.there (.there (.there (.there (.there (.there .here)))))))

private def bv_b : Term signature_m Γ8 Φ .num  := .bvar (.there (.there (.there (.there (.there (.there .here))))))

private def bv_colf : Term signature_m Γ8 Φ .num  := .bvar (.there (.there (.there (.there (.there .here)))))

private def bv_coll : Term signature_m Γ8 Φ .num  := .bvar (.there (.there (.there (.there .here))))

private def bv_lenf : Term signature_m Γ8 Φ .num  := .bvar (.there (.there (.there .here)))

private def bv_lenl : Term signature_m Γ8 Φ .num  := .bvar (.there (.there .here))

private def bv_u : Term signature_m Γ8 Φ .num  := .bvar (.there .here)

private def bv_v : Term signature_m Γ8 Φ .num  := .bvar .here

/-- 候选列 `p` 所在的一层绑定上下文。 -/
private abbrev Γ9 : SortContext signature_m := .num :: Γ8

private def bv_p : Term signature_m Γ9 Φ .num := .bvar .here

/-- 平坦侧存在形如 `A + p` 的值：`∃ s, s < lenf ∧ E (v@s) = A + p`。 -/
private def ex_flat : Formula signature_m Γ9 Φ :=
  .existsE .num (.conj
    (PrimitiveFormulas.lt_m (.bvar .here) (sh (sh bv_lenf)))
    (output_m (sh sE) (sh (sh bv_v)) (.bvar .here) (addT (sh sA) (sh bv_p))))

/-- 局侧存在同一候选列：`∃ t, t < lenl ∧ E (u@t) = p`。 -/
private def ex_local : Formula signature_m Γ9 Φ :=
  .existsE .num (.conj
    (PrimitiveFormulas.lt_m (.bvar .here) (sh (sh bv_lenl)))
    (output_m (sh sE) (sh (sh bv_u)) (.bvar .here) (sh bv_p)))

private def cc1 : Formula signature_m Γ8 Φ := output_m sR sS1 sf bv_a

private def cc2 : Formula signature_m Γ8 Φ := state_m sX bv_colf bv_v bv_a

private def cc3 : Formula signature_m Γ8 Φ := output_m sU sS2 sf bv_b

private def cc4 : Formula signature_m Γ8 Φ := state_m sY bv_coll bv_u bv_b

private def cc5 : Formula signature_m Γ8 Φ := GraphSyntax.edge_m sL bv_v bv_lenf

private def cc6 : Formula signature_m Γ8 Φ := GraphSyntax.edge_m sL bv_u bv_lenl

/-- 列二分：平坦当前列已低于偏移且局侧父缺项，或仍在段内等于 `A + coll`。 -/
private def cc7 : Formula signature_m Γ8 Φ :=
  .disj (.conj (PrimitiveFormulas.lt_m bv_colf sA) (output_m sD sY bv_coll zeroT))
    (.conj (PrimitiveFormulas.lt_m bv_coll sw) (.equal bv_colf (addT sA bv_coll)))

/-- 两条值集合覆盖条件。 -/
private def cc8 : Formula signature_m Γ8 Φ := .forallE .num (.imp ex_flat ex_local)

private def cc9 : Formula signature_m Γ8 Φ := .forallE .num (.imp ex_local ex_flat)

private def exit_body : Formula signature_m Γ8 Φ :=
  .conj cc1 (.conj cc2 (.conj cc3 (.conj cc4 (.conj cc5 (.conj cc6 (.conj cc7
    (.conj cc8 cc9)))))))

/-- 归纳正文：八层存在量词装入两侧状态码、两当前列、两累计表长度与两累计表。 -/
def exit_state_m : Formula signature_m [] Φ :=
  .existsE .num (.existsE .num (.existsE .num (.existsE .num (.existsE .num (.existsE .num (.existsE .num (.existsE .num (exit_body))))))))

/-- 出段共同状态只用零、加、配对、成员边与数量词。 -/
theorem exit_state_language_m : language_m exit_state_m = true := pure_language_m _ rfl

/-- 把十一个自由槽依次装入环境；归纳变量由 `pushFree` 追加在头部。 -/
private def envSlots (R U D L E : set_l ℳ) (X Y A w s₁ s₂ : num_l ℳ) : Env ℳ [] Δ :=
  let η₀ := Env.pushFree (Env.empty (M := ℳ)) E
  let η₁ := Env.pushFree η₀ L
  let η₂ := Env.pushFree η₁ D
  let η₃ := Env.pushFree η₂ U
  let η₄ := Env.pushFree η₃ R
  let η₅ := Env.pushFree η₄ s₂
  let η₆ := Env.pushFree η₅ s₁
  let η₇ := Env.pushFree η₆ w
  let η₈ := Env.pushFree η₇ A
  let η₉ := Env.pushFree η₈ Y
  Env.pushFree η₉ X

/-- 实际公式的解释逐值等于所需的出段共同状态。 -/
theorem exit_state_syntax_l (X Y A w s₁ s₂ : num_l ℳ) (R U D L E : set_l ℳ) (n : num_l ℳ) :
    Formula.satisfies
      (Env.pushFree (envSlots R U D L E X Y A w s₁ s₂) n) exit_state_m ↔
      exit_state_l X Y A w s₁ s₂ R U D L E n := by
  simp only [exit_state_l, exit_state_m, exit_body, cc1, cc2, cc3, cc4, cc5, cc6, cc7, cc8, cc9,
    ex_flat, ex_local, bv_v, bv_u, bv_lenl, bv_lenf, bv_coll, bv_colf, bv_b, bv_a, bv_p,
    addT, zeroT, sh, sf, sX, sY, sA, sw, sS1, sS2, sR, sU, sD, sL, sE, envSlots,
    Formula.satisfies, state_syntax_l, output_syntax_l, SecondOrderPairing.edge_l,
    SecondOrderOrder.formula_l, Term.eval, Arguments.eval, Env.pushBound, Env.pushFree,
    Assignment.push]
  rfl

/-- 平坦侧原起始状态：当前列带内部偏移 `A`，累计器为空码。 -/
noncomputable def flat_start_l (X A j : num_l ℳ) : num_l ℳ :=
  value_l X (value_l (add_l A j) (zero_l ℳ))

/-- 局侧原起始状态：当前列为 `j`，累计器为空码。 -/
noncomputable def local_start_l (Y j : num_l ℳ) : num_l ℳ := value_l Y (value_l j (zero_l ℳ))

/-- 平坦侧新追加一个低于偏移的列、局侧不动时，两条值集合覆盖条件保持：新列不可能写成
`A + p`，旧条目的对应按位搬到后继下标。 -/
private theorem cons_low_corr (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {A i v u lenf lenl : num_l ℳ} (hi : SecondOrderOrder.lt_l i A)
    (h8 : ∀ p, (∃ s, SecondOrderOrder.lt_l s lenf ∧
        relation_l E (value_l v s) (add_l A p)) →
      (∃ t, SecondOrderOrder.lt_l t lenl ∧ relation_l E (value_l u t) p))
    (h9 : ∀ p, (∃ t, SecondOrderOrder.lt_l t lenl ∧ relation_l E (value_l u t) p) →
      (∃ s, SecondOrderOrder.lt_l s lenf ∧ relation_l E (value_l v s) (add_l A p))) :
    letI := order_l hℳ
    (∀ p, (∃ s, SecondOrderOrder.lt_l s (succ_l lenf) ∧
        relation_l E (value_l (succ_l (value_l i v)) s) (add_l A p)) →
      (∃ t, SecondOrderOrder.lt_l t lenl ∧ relation_l E (value_l u t) p)) ∧
      (∀ p, (∃ t, SecondOrderOrder.lt_l t lenl ∧ relation_l E (value_l u t) p) →
        (∃ s, SecondOrderOrder.lt_l s (succ_l lenf) ∧
          relation_l E (value_l (succ_l (value_l i v)) s) (add_l A p))) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  constructor
  · intro p ⟨s, hs, hmem⟩
    rcases predecessor_l hℳ s with rfl | ⟨t, rfl⟩
    · have hi' : i = add_l A p := (lookup_cons_zero_l hℳ hE i v (add_l A p)).mp hmem
      have hle : A ≤ add_l A p := (le_iff_l hℳ _ _).mpr ⟨p, rfl⟩
      exact absurd ((hi'.symm ▸ hi : add_l A p < A)) (not_lt_of_ge hle)
    · obtain ⟨t, ht, hmem'⟩ :=
        h8 p ⟨t, SecondOrderOrder.succ_iff_l hℳ t lenf |>.mp hs, (lookup_cons_succ_l hℳ hE i v t _).mp hmem⟩
      exact ⟨t, ht, hmem'⟩
  · intro p hp
    obtain ⟨s, hs, hmem⟩ := h9 p hp
    exact ⟨succ_l s, SecondOrderOrder.succ_iff_l hℳ s lenf |>.mpr hs,
      (lookup_cons_succ_l hℳ hE i v s _).mpr hmem⟩

/-- 两侧同时新追加平移的一对列 `A + q` 与 `q` 时，两条值集合覆盖条件保持：新值互为见证，
旧条目按后继下标搬移。 -/
private theorem cons_shift_corr (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {A q v u lenf lenl : num_l ℳ}
    (h8 : ∀ p, (∃ s, SecondOrderOrder.lt_l s lenf ∧
        relation_l E (value_l v s) (add_l A p)) →
      (∃ t, SecondOrderOrder.lt_l t lenl ∧ relation_l E (value_l u t) p))
    (h9 : ∀ p, (∃ t, SecondOrderOrder.lt_l t lenl ∧ relation_l E (value_l u t) p) →
      (∃ s, SecondOrderOrder.lt_l s lenf ∧ relation_l E (value_l v s) (add_l A p))) :
    letI := order_l hℳ
    (∀ p, (∃ s, SecondOrderOrder.lt_l s (succ_l lenf) ∧
        relation_l E (value_l (succ_l (value_l (add_l A q) v)) s) (add_l A p)) →
      (∃ t, SecondOrderOrder.lt_l t (succ_l lenl) ∧
        relation_l E (value_l (succ_l (value_l q u)) t) p)) ∧
      (∀ p, (∃ t, SecondOrderOrder.lt_l t (succ_l lenl) ∧
          relation_l E (value_l (succ_l (value_l q u)) t) p) →
        (∃ s, SecondOrderOrder.lt_l s (succ_l lenf) ∧
          relation_l E (value_l (succ_l (value_l (add_l A q) v)) s) (add_l A p))) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  constructor
  · intro p ⟨s, hs, hmem⟩
    rcases predecessor_l hℳ s with rfl | ⟨t, rfl⟩
    · have h : add_l A q = add_l A p :=
        (lookup_cons_zero_l hℳ hE (add_l A q) v (add_l A p)).mp hmem
      refine ⟨zero_l ℳ, SecondOrderOrder.zero_succ_l hℳ lenl,
        (lookup_cons_zero_l hℳ hE q u p).mpr ?_⟩
      exact (SecondOrderNumbers.add_cancel_l hℳ A q p).mp h
    · obtain ⟨t, ht, hut⟩ := h8 p ⟨t, SecondOrderOrder.succ_iff_l hℳ t lenf |>.mp hs,
        (lookup_cons_succ_l hℳ hE (add_l A q) v t _).mp hmem⟩
      exact ⟨succ_l t, SecondOrderOrder.succ_iff_l hℳ t lenl |>.mpr ht,
        (lookup_cons_succ_l hℳ hE q u t _).mpr hut⟩
  · intro p ⟨t, ht, hut⟩
    rcases predecessor_l hℳ t with rfl | ⟨s, rfl⟩
    · have h : q = p := (lookup_cons_zero_l hℳ hE q u p).mp hut
      refine ⟨zero_l ℳ, SecondOrderOrder.zero_succ_l hℳ lenf,
        (lookup_cons_zero_l hℳ hE (add_l A q) v (add_l A p)).mpr ?_⟩
      exact h ▸ rfl
    · obtain ⟨s, hs, hmem⟩ := h9 p ⟨s, SecondOrderOrder.succ_iff_l hℳ s lenl |>.mp ht,
        (lookup_cons_succ_l hℳ hE q u s _).mp hut⟩
      exact ⟨succ_l s, SecondOrderOrder.succ_iff_l hℳ s lenf |>.mpr hs,
        (lookup_cons_succ_l hℳ hE (add_l A q) v s _).mpr hmem⟩

/-- 段内 some↔some 对应与局侧父缺项夹住平坦侧后继：其父列必严格低于偏移。否则平坦后继可写成
`A + q`，段内对应就把局侧父拉成 `succ q`，与缺项矛盾。 -/
private theorem below_offset_l (hℳ : Theory.Models ℳ theory_m) (d : code_m)
    {C D : set_l ℳ} (hD : graph_semantics_l (graph_m d) D)
    (X Y A w coll i : num_l ℳ) (hcolw : SecondOrderOrder.lt_l coll w)
    (hz : relation_l C (value_l X (add_l A coll)) (succ_l i))
    (hq : relation_l D (value_l Y coll) (zero_l ℳ))
    (hpp : ∀ k q, SecondOrderOrder.lt_l k w →
      (relation_l C (value_l X (add_l A k)) (succ_l (add_l A q)) ↔
        relation_l D (value_l Y k) (succ_l q))) :
    SecondOrderOrder.lt_l i A := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  have hnc : ¬∃ q, add_l A q = i := by
    rintro ⟨q, hqi⟩
    have hzq : relation_l C (value_l X (add_l A coll)) (succ_l (add_l A q)) := by
      rw [hqi]
      exact hz
    exact absurd (function_value_unique_l (function_of_semantics_l hℳ d hD) hq
      ((hpp coll q hcolw).mp hzq)).symm (nonzero_l hℳ q)
  rcases SecondOrderOrder.trichotomy_l hℳ i A with hit | heq | hgt
  · exact hit
  · exact absurd ⟨zero_l ℳ, (add_zero_l hℳ A).trans heq.symm⟩ hnc
  · obtain ⟨k, hk⟩ := hgt
    exact absurd ⟨succ_l k, hk⟩ hnc

/-- 出段共同状态在一步演化下保持。局侧父为后继时，弱化对应强制平坦父也平移，两侧同步追加
`A + p` 与 `p`；局侧父缺项时，平坦父要么也缺项（整体冻结），要么落到低于偏移的列（转入出段
模式，此后新追加列由严格下降永不再达到 `A + p`）。只用段内 some↔some 对应，不消费 none↔none。
-/
private theorem exit_step_l (hℳ : Theory.Models ℳ theory_m) (c d : code_m)
    {C D R U L E : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) (hD : graph_semantics_l (graph_m d) D)
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hU : graph_semantics_l (graph_m (repeat_m (step_m d))) U)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (X Y A w j : num_l ℳ)
    (hdownx : ∀ k p, relation_l C (value_l X k) (succ_l p) → SecondOrderOrder.lt_l p k)
    (hdowny : ∀ k p, relation_l D (value_l Y k) (succ_l p) → SecondOrderOrder.lt_l p k)
    (hpp : ∀ k q, SecondOrderOrder.lt_l k w →
      (relation_l C (value_l X (add_l A k)) (succ_l (add_l A q)) ↔
        relation_l D (value_l Y k) (succ_l q)))
    (f : num_l ℳ)
    (h : exit_state_l X Y A w (flat_start_l X A j) (local_start_l Y j) R U D L E f) :
    exit_state_l X Y A w (flat_start_l X A j) (local_start_l Y j) R U D L E (succ_l f) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (step_m c)
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ (step_m d)
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨a, b, colf, coll, lenf, lenl, u, v, hr, hxe, hu, hye, hlf, hll, hstat, h8, h9⟩ := h
  subst a
  subst b
  have hCf := function_of_semantics_l hℳ c hC
  have hDf := function_of_semantics_l hℳ d hD
  obtain ⟨q, hq, _⟩ := hDf (value_l Y coll)
  obtain ⟨z, hz, _⟩ := hCf (value_l X colf)
  have hstepY0 (hnone : relation_l D (value_l Y coll) (zero_l ℳ)) :
      relation_l U (value_l (local_start_l Y j) (succ_l f)) (value_l Y (value_l coll u)) :=
    (repeat_succ_l hℳ (step_m d) hU hT _ f _).mpr
      ⟨_, hu, (step_none_l hℳ d hT hD hnone u _).mpr rfl⟩
  rcases hstat with ⟨hltA, hnoneY⟩ | ⟨hcolw, rfl⟩
  · -- 已出段：局侧继续冻结，平坦侧只把更低列追加进自己的累计表。
    rcases predecessor_l hℳ z with rfl | ⟨i, rfl⟩
    · exact ⟨value_l X (value_l colf v), value_l Y (value_l coll u), colf, coll, lenf, lenl, u, v,
        (repeat_succ_l hℳ (step_m c) hR hS _ f _).mpr
          ⟨_, hr, (step_none_l hℳ c hS hC hz v _).mpr rfl⟩, rfl, hstepY0 hnoneY, rfl,
        hlf, hll, Or.inl ⟨hltA, hnoneY⟩, h8, h9⟩
    · have hlt : SecondOrderOrder.lt_l i A :=
        SecondOrderOrder.trans_l hℳ (hdownx colf i hz) hltA
      obtain ⟨h8', h9'⟩ := cons_low_corr hℳ hE hlt h8 h9
      exact ⟨value_l X (value_l i (succ_l (value_l i v))), value_l Y (value_l coll u), i, coll,
        succ_l lenf, lenl, u, succ_l (value_l i v),
        (repeat_succ_l hℳ (step_m c) hR hS _ f _).mpr
          ⟨_, hr, (step_some_l hℳ c hS hC hz v _).mpr rfl⟩, rfl, hstepY0 hnoneY, rfl,
        (length_rel_l hℳ hL hI _ _).mpr
          ((length_cons_l hℳ hI i v lenf).mpr ((length_rel_l hℳ hL hI _ _).mp hlf)),
        hll, Or.inl ⟨hlt, hnoneY⟩, h8', h9'⟩
  · -- 仍在段内：平坦当前列等于 `A + coll`。
    rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
    · -- 局侧缺项：段内对应把平坦父夹到偏移之下，两侧各自处理。
      rcases predecessor_l hℳ z with rfl | ⟨i, rfl⟩
      · exact ⟨value_l X (value_l (add_l A coll) v), value_l Y (value_l coll u), add_l A coll,
          coll, lenf, lenl, u, v,
          (repeat_succ_l hℳ (step_m c) hR hS _ f _).mpr
            ⟨_, hr, (step_none_l hℳ c hS hC hz v _).mpr rfl⟩, rfl, hstepY0 hq, rfl,
          hlf, hll, Or.inr ⟨hcolw, rfl⟩, h8, h9⟩
      · have hlt : SecondOrderOrder.lt_l i A :=
          below_offset_l hℳ d hD X Y A w coll i hcolw hz hq hpp
        obtain ⟨h8', h9'⟩ := cons_low_corr hℳ hE hlt h8 h9
        exact ⟨value_l X (value_l i (succ_l (value_l i v))), value_l Y (value_l coll u), i, coll,
          succ_l lenf, lenl, u, succ_l (value_l i v),
          (repeat_succ_l hℳ (step_m c) hR hS _ f _).mpr
            ⟨_, hr, (step_some_l hℳ c hS hC hz v _).mpr rfl⟩, rfl, hstepY0 hq, rfl,
          (length_rel_l hℳ hL hI _ _).mpr
            ((length_cons_l hℳ hI i v lenf).mpr ((length_rel_l hℳ hL hI _ _).mp hlf)),
          hll, Or.inl ⟨hlt, hq⟩, h8', h9'⟩
    · -- 局侧后继：段内对应给出平坦侧同一平移后继，两侧同步追加入累计表。
      have hp : relation_l D (value_l Y coll) (succ_l p) := hq
      have hx2 : relation_l C (value_l X (add_l A coll)) (succ_l (add_l A p)) :=
        (hpp coll p hcolw).mpr hp
      rcases predecessor_l hℳ z with rfl | ⟨i, rfl⟩
      · exact absurd (function_value_unique_l hCf hz hx2).symm (nonzero_l hℳ (add_l A p))
      · have hi : i = add_l A p := injective_l hℳ (function_value_unique_l hCf hz hx2)
        subst hi
        have hlt : SecondOrderOrder.lt_l p w :=
          SecondOrderOrder.trans_l hℳ (hdowny coll p hp) hcolw
        obtain ⟨h8', h9'⟩ := cons_shift_corr hℳ hE h8 h9
        exact ⟨value_l X (value_l (add_l A p) (succ_l (value_l (add_l A p) v))),
            value_l Y (value_l p (succ_l (value_l p u))), add_l A p, p, succ_l lenf, succ_l lenl,
            succ_l (value_l p u), succ_l (value_l (add_l A p) v),
          (repeat_succ_l hℳ (step_m c) hR hS _ f _).mpr
            ⟨_, hr, (step_some_l hℳ c hS hC hx2 v _).mpr rfl⟩, rfl,
            (repeat_succ_l hℳ (step_m d) hU hT _ f _).mpr
              ⟨_, hu, (step_some_l hℳ d hT hD hp u _).mpr rfl⟩, rfl,
          (length_rel_l hℳ hL hI _ _).mpr
            ((length_cons_l hℳ hI (add_l A p) v lenf).mpr
              ((length_rel_l hℳ hL hI _ _).mp hlf)),
            (length_rel_l hℳ hL hI _ _).mpr
              ((length_cons_l hℳ hI p u lenl).mpr ((length_rel_l hℳ hL hI _ _).mp hll)),
          Or.inr ⟨hlt, rfl⟩, h8', h9'⟩

/-- 两侧同燃料下，弱化段内对应与两侧严格下降把出段共同状态保持到任意内部燃料。归纳只走实际
公式 `exit_state_m`；偏移、块宽、起始列、燃料与全部列号均可取模型内部非标准元素，不使用宿主
`Nat` 归纳，也不要求外部标准性或矩形性。 -/
theorem common_state_exit_l (hℳ : Theory.Models ℳ theory_m) (c d : code_m)
    {C D R U L E : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) (hD : graph_semantics_l (graph_m d) D)
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hU : graph_semantics_l (graph_m (repeat_m (step_m d))) U)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (X Y A w j : num_l ℳ) (hj : SecondOrderOrder.lt_l j w)
    (hdownx : ∀ k p, relation_l C (value_l X k) (succ_l p) → SecondOrderOrder.lt_l p k)
    (hdowny : ∀ k p, relation_l D (value_l Y k) (succ_l p) → SecondOrderOrder.lt_l p k)
    (hpp : ∀ k q, SecondOrderOrder.lt_l k w →
      (relation_l C (value_l X (add_l A k)) (succ_l (add_l A q)) ↔
        relation_l D (value_l Y k) (succ_l q)))
    (n : num_l ℳ) :
    exit_state_l X Y A w (flat_start_l X A j) (local_start_l Y j) R U D L E n := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  apply induct_l hℳ exit_state_m exit_state_language_m
    (envSlots R U D L E X Y A w (flat_start_l X A j) (local_start_l Y j))
    (fun n => exit_state_l X Y A w (flat_start_l X A j) (local_start_l Y j) R U D L E n)
    (exit_state_syntax_l X Y A w (flat_start_l X A j) (local_start_l Y j) R U D L E) ?_ ?_ n
  · exact ⟨flat_start_l X A j, local_start_l Y j, add_l A j, j, zero_l ℳ, zero_l ℳ, zero_l ℳ,
      zero_l ℳ, (repeat_zero_l hℳ (step_m c) hR _ _).mpr rfl, rfl,
      (repeat_zero_l hℳ (step_m d) hU _ _).mpr rfl, rfl,
      (length_rel_l hℳ hL hI _ _).mpr ((length_zero_l hℳ hI _).mpr rfl),
      (length_rel_l hℳ hL hI _ _).mpr ((length_zero_l hℳ hI _).mpr rfl), Or.inr ⟨hj, rfl⟩,
      fun p ⟨s, hs, _⟩ => False.elim ((not_lt_of_ge (zero_le_l hℳ s)) hs),
      fun p ⟨t, ht, _⟩ => False.elim ((not_lt_of_ge (zero_le_l hℳ t)) ht)⟩
  · exact fun f h => exit_step_l hℳ c d hC hD hR hU hL hE X Y A w j hdownx hdowny hpp f h

/-- 原反转不改变累计表的值集合：界内位置上的取值在反转前后互为见证，越界补零不作为成员参与。 -/
theorem reverse_exists_l (hℳ : Theory.Models ℳ theory_m) {T L E : set_l ℳ}
    (hT : graph_semantics_l (graph_m reverse_m) T)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n : num_l ℳ}
    (hy : relation_l T x y) (hx : relation_l L x n) (_hn : relation_l L y n) (w : num_l ℳ) :
    (∃ s, SecondOrderOrder.lt_l s n ∧ relation_l E (value_l y s) w) ↔
      (∃ s, SecondOrderOrder.lt_l s n ∧ relation_l E (value_l x s) w) := by
  letI := order_l hℳ
  constructor
  · rintro ⟨s, hs, hmem⟩
    obtain ⟨k, hkn, hkn'⟩ := index_exists_l hℳ hs
    exact ⟨k, hkn', (lookup_l hℳ hT hL hE hy hx hkn w).mp hmem⟩
  · rintro ⟨k, hk, hmem⟩
    obtain ⟨s, hks, hks'⟩ := index_exists_l hℳ hk
    exact ⟨s, hks',
      (lookup_l hℳ hT hL hE hy hx (index_symm_l hℳ hks) w).mpr hmem⟩

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

/-- 出段后的祖先成员同步：平坦侧父图 `C` 在列 `K + k` 上只在段内与局侧 `D` 平移对应，出段后
两侧累计表只共享偏移等价的价值集合；链成员测试只看值是否出现，于是尾巴与顺序都不影响真值。
两侧燃料同为 `K + j`，局侧链由 `chain_ge_l` 裁回 `j`。全程不做宿主 `Nat` 归纳、不要求外部标准
性、不假定矩形性，也不消费段内 none↔none 对应。 -/
theorem ancestor_exit_sync_l (hℳ : Theory.Models ℳ theory_m) (c d : code_m)
    {C D R U L E : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) (hD : graph_semantics_l (graph_m d) D)
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hU : graph_semantics_l (graph_m (repeat_m (step_m d))) U)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {A₁ A₂ T : set_l ℳ} (hA₁ : graph_semantics_l (graph_m (chain_m c)) A₁)
    (hA₂ : graph_semantics_l (graph_m (chain_m d)) A₂)
    (hT : graph_semantics_l (graph_m reverse_m) T)
    {B₁ B₂ : set_l ℳ} (hB₁ : graph_semantics_l (graph_m (member_m c)) B₁)
    (hB₂ : graph_semantics_l (graph_m (member_m d)) B₂)
    (P Q K w j : num_l ℳ) (hj : SecondOrderOrder.lt_l j w)
    (hdownx : ∀ k p, relation_l C (value_l P k) (succ_l p) → SecondOrderOrder.lt_l p k)
    (hdowny : ∀ k p, relation_l D (value_l Q k) (succ_l p) → SecondOrderOrder.lt_l p k)
    (hpp : ∀ k q, SecondOrderOrder.lt_l k w →
      (relation_l C (value_l P (add_l K k)) (succ_l (add_l K q)) ↔
        relation_l D (value_l Q k) (succ_l q)))
    (q : num_l ℳ) :
    ¬relation_l B₁ (value_l (value_l P (add_l K j)) (add_l K q)) (zero_l ℳ) ↔
      ¬relation_l B₂ (value_l (value_l Q j) q) (zero_l ℳ) := by
  letI := order_l hℳ
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (fold_m reverse_step_m)
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨a, b, colf, coll, lenf, lenl, u, v, h1, h2, h3, h4, hlf, hll, hstat, h8, h9⟩ :=
    common_state_exit_l hℳ c d hC hD hR hU hL hE P Q K w j hj hdownx hdowny hpp (add_l K j)
  -- 同一燃料下两侧迭代输出码，其累计器坐标由出段共同状态给出。
  have h1' : relation_l R (value_l (flat_start_l P K j) (add_l K j))
      (value_l P (value_l colf v)) := by rw [h2]; exact h1
  have h3' : relation_l U (value_l (local_start_l Q j) (add_l K j))
      (value_l Q (value_l coll u)) := by rw [h4]; exact h3
  obtain ⟨y_v, hy_v, _⟩ := function_of_semantics_l hℳ reverse_m hT v
  obtain ⟨y_u, hy_u, _⟩ := function_of_semantics_l hℳ reverse_m hT u
  have hlen_v : relation_l L y_v lenf :=
    reverse_length_l hℳ hT hF hL hI v y_v lenf hy_v hlf
  have hlen_u : relation_l L y_u lenl :=
    reverse_length_l hℳ hT hF hL hI u y_u lenl hy_u hll
  -- 平坦侧链的输出就是 `y_v`，其目标列本身是 `K + j`；局侧链再由稳定性裁回 `j`。
  have hchain₁ : relation_l A₁ (value_l (value_l P (add_l K j)) (add_l K j)) y_v :=
    (chain_rel_l hℳ c hA₁ hR hT P (add_l K j) (add_l K j) y_v).mpr
      ⟨value_l P (value_l colf v), h1', by
        rw [acc_two_l hℳ P colf v]; exact hy_v⟩
  have hchain₂ : relation_l A₂ (value_l (value_l Q j) j) y_u := by
    have hfuel : relation_l A₂ (value_l (value_l Q j) (add_l K j)) y_u :=
      (chain_rel_l hℳ d hA₂ hU hT Q j (add_l K j) y_u).mpr
        ⟨value_l Q (value_l coll u), h3', by rw [acc_two_l hℳ Q coll u]; exact hy_u⟩
    exact (chain_ge_l hℳ d hA₂ hD Q j (add_l K j) y_u hdowny
      (le_add_left_l hℳ K j)).mp hfuel
  have hflat : (∃ s, SecondOrderOrder.lt_l s lenf ∧ relation_l E (value_l y_v s) (add_l K q)) ↔
      (∃ t, SecondOrderOrder.lt_l t lenl ∧ relation_l E (value_l y_u t) q) := by
    constructor
    · rintro ⟨s, hs, hmem⟩
      obtain ⟨s', hs', hmem'⟩ := (reverse_exists_l hℳ hT hL hE hy_v hlf hlen_v _).mp
        ⟨s, hs, hmem⟩
      obtain ⟨t, ht, hut⟩ := h8 q ⟨s', hs', hmem'⟩
      exact (reverse_exists_l hℳ hT hL hE hy_u hll hlen_u _).mpr ⟨t, ht, hut⟩
    · rintro ⟨t, ht, hut⟩
      obtain ⟨t', ht', hut'⟩ := (reverse_exists_l hℳ hT hL hE hy_u hll hlen_u _).mp ⟨t, ht, hut⟩
      obtain ⟨s, hs, hmem⟩ := h9 q ⟨t', ht', hut'⟩
      exact (reverse_exists_l hℳ hT hL hE hy_v hlf hlen_v _).mpr ⟨s, hs, hmem⟩
  have hB₁ : ¬relation_l B₁ (value_l (value_l P (add_l K j)) (add_l K q)) (zero_l ℳ) ↔
      ∃ s, SecondOrderOrder.lt_l s lenf ∧ relation_l E (value_l y_v s) (add_l K q) :=
    member_nonzero_l hℳ c hB₁ hA₁ hL hE hchain₁ hlen_v (add_l K q)
  have hB₂ : ¬relation_l B₂ (value_l (value_l Q j) q) (zero_l ℳ) ↔
      ∃ t, SecondOrderOrder.lt_l t lenl ∧ relation_l E (value_l y_u t) q :=
    member_nonzero_l hℳ d hB₂ hA₂ hL hE hchain₂ hlen_u q
  exact hB₁.trans (hflat.trans hB₂.symm)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentRelocationAncestorExit
