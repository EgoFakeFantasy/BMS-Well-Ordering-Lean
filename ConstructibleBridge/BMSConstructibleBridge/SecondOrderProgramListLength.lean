import BMSConstructibleBridge.SecondOrderProgramListIteration
import BMSConstructibleBridge.SecondOrderMinimum

/-!
# 原尾码迭代的内部长度图

长度定义为同一个原 `iterate_m` 图首次输出零的步数。归零上界已经由实际公式归纳
证明；最小步数由模型内部最小元原理产生。随后用实际理解公式收集整个长度图，
因此没有假定任意外部函数都属于模型的实数域。

这里交付内部最小归零步的图、总唯一性、原码上界和零长度判据。长度的显式
七构造程序及任意模型正确性见 `SecondOrderProgramLength`，完整生成数组解码见
`SecondOrderProgramGeneratedDecode`；固定外部高度对象推导见
`SecondOrderHereditaryBMSWellOrder`。本模块只提供关系图这一中间结果。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListLength

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramListIteration SecondOrderProgramListCode
open PrimitiveProgram (graph_m eval_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-! ## 标准端的原列表身份核验；不用于推出非标准内部规格 -/

/-- 原程序的标准步进确实取一次尾码。 -/
theorem iterate_step_eval_l (x k v : Nat) :
    eval_l iterate_step_m (Nat.pair x (Nat.pair k v)) = eval_l tail_m v := by
  change eval_l tail_m ((Nat.pair x (Nat.pair k v)).unpair.2.unpair.2) = _
  rw [Nat.unpair_pair, Nat.unpair_pair]

/-- 原列表编码上的迭代对应同一个列表的 `drop`，不是另选编码。 -/
theorem iterate_encode_l (s : List Nat) (k : Nat) :
    eval_l iterate_m (Nat.pair (Encodable.encode s) k) = Encodable.encode (s.drop k) := by
  rw [iterate_m, PrimitiveProgram.prec_l]
  induction k with
  | zero => exact PrimitiveProgram.id_l (Encodable.encode s)
  | succ k ih =>
      simp only [PrimitiveHistory.run_l] at ih ⊢
      rw [iterate_step_eval_l, ih, tail_encode_l, List.tail_drop]

/-- 标准端的归零条件恰为达到原列表长度。 -/
theorem stops_encode_l (s : List Nat) (k : Nat) :
    eval_l iterate_m (Nat.pair (Encodable.encode s) k) = 0 ↔ s.length ≤ k := by
  rw [iterate_encode_l]
  have hzero : (0 : Nat) = Encodable.encode ([] : List Nat) := rfl
  rw [hzero, Encodable.encode_injective.eq_iff, List.drop_eq_nil_iff]

/-- 实际归零公式：在原图 `I` 中，输入 `pair x k` 的输出为零。 -/
def stops_m {Γ Δ : SortContext signature_m} (I : Term signature_m Γ Δ .set)
    (x k : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.conj
    (PrimitiveFormulas.pair_m (x.weakenBound sort_m.num) (k.weakenBound sort_m.num) (.bvar .here))
    (GraphSyntax.edge_m (I.weakenBound sort_m.num) (.bvar .here) (numeral_m 0)))

/-- 模板解释为原图的同一条边；存在的配对值不改变输入编码。 -/
theorem stops_syntax_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (I : Term signature_m Γ Δ .set) (x k : Term signature_m Γ Δ .num) :
    Formula.satisfies η (stops_m I x k) ↔
      relation_l (I.eval η) (value_l (x.eval η) (k.eval η)) (zero_l ℳ) := by
  simp only [stops_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l, Term.eval_weakenBound]
  change (∃ q, value_l (x.eval η) (k.eval η) = q ∧
    relation_l (I.eval η) q (zero_l ℳ)) ↔ _
  simp only [exists_eq_left']

/-- 内部长度的语义规格；量词遍历所有内部步数。 -/
def length_spec_l (I : set_l ℳ) (x k : num_l ℳ) : Prop :=
  relation_l I (value_l x k) (zero_l ℳ) ∧
    ∀ j, SecondOrderOrder.lt_l j k → ¬relation_l I (value_l x j) (zero_l ℳ)

/-- 固定输入的所有归零步形成模型内部集合。此处未要求 `I` 是程序图。 -/
theorem stops_set_l (hℳ : Theory.Models ℳ theory_m) (I : set_l ℳ) (x : num_l ℳ) :
    ∃ S : set_l ℳ, ∀ k, mem_l k S ↔ relation_l I (value_l x k) (zero_l ℳ) := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    stops_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  obtain ⟨S, hS⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree I).pushFree x)
  exact ⟨S, fun k => (hS k).trans (stops_syntax_l _ _ _ _)⟩

/-- 每个内部码确有唯一最小归零步；没有对模型数域作外部良基选择。 -/
theorem length_exists_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) (x : num_l ℳ) :
    ∃! k, length_spec_l I x k := by
  obtain ⟨S, hS⟩ := stops_set_l hℳ I x
  obtain ⟨k, hk, hmin⟩ := SecondOrderMinimum.exists_l hℳ S
    ⟨x, (hS x).mpr ((terminates_l hℳ hI x (zero_l ℳ)).mpr rfl)⟩
  have hspec : length_spec_l I x k :=
    ⟨(hS k).mp hk, fun j hj h => hmin j hj ((hS j).mpr h)⟩
  refine ⟨k, hspec, ?_⟩
  intro j hj
  rcases SecondOrderOrder.trichotomy_l hℳ j k with h | h | h
  · exact False.elim (hspec.2 j h hj.1)
  · exact h
  · exact False.elim (hj.2 k h hspec.1)

/-- 最小归零步不超过原输入码；上界也是任意模型内部数。 -/
theorem length_bound_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) {x k : num_l ℳ}
    (hk : length_spec_l I x k) :
    letI := order_l hℳ
    k ≤ x := by
  letI := order_l hℳ
  exact le_of_not_gt (fun h => hk.2 x h ((terminates_l hℳ hI x (zero_l ℳ)).mpr rfl))

/-- 最小归零步为零当且仅当输入本来就是空码。 -/
theorem length_zero_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) (x : num_l ℳ) :
    length_spec_l I x (zero_l ℳ) ↔ x = zero_l ℳ := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  constructor
  · intro h
    exact (iterate_zero_l hℳ hI x (zero_l ℳ)).mp h.1
  · intro h
    refine ⟨(iterate_zero_l hℳ hI x (zero_l ℳ)).mpr h, ?_⟩
    intro j hj
    exact False.elim ((not_lt_of_ge (zero_le_l hℳ j)) hj)

/-- 长度图的实际理解正文，自由槽为 `[x, k, I]`。 -/
def length_m : Formula signature_m [] [.num, .num, .set] :=
  .conj
    (stops_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here)))
    (.forallE .num (.imp
      (PrimitiveFormulas.lt_m (.bvar .here) (.fvar (.there .here)))
      (.neg (stops_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar .here)))))

/-- 长度图正文属于原纯二阶算术语言。 -/
theorem length_language_m : language_m length_m = true := pure_language_m _ rfl

/-- 理解正文逐点对应上面的最小步数规格。 -/
theorem length_syntax_l (I : set_l ℳ) (x k : num_l ℳ) :
    Formula.satisfies ((((Env.empty (M := ℳ)).pushFree I).pushFree k).pushFree x)
      length_m ↔ length_spec_l I x k := by
  simp only [length_m, Formula.satisfies, stops_syntax_l, SecondOrderOrder.formula_l]
  rfl

/-- 模型内部存在长度的全函数图，且每条边与原图的最小归零步双向等价。 -/
theorem length_graph_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) :
    ∃ L : set_l ℳ, function_l L ∧
      ∀ x k, relation_l L x k ↔ length_spec_l I x k := by
  obtain ⟨L, hL⟩ := SecondOrderRelations.comprehension_l hℳ length_m length_language_m
    ((Env.empty (M := ℳ)).pushFree I)
  have hspec : ∀ x k, relation_l L x k ↔ length_spec_l I x k :=
    fun x k => (hL x k).trans (length_syntax_l I x k)
  refine ⟨L, ?_, hspec⟩
  intro x
  obtain ⟨k, hk, hu⟩ := length_exists_l hℳ hI x
  exact ⟨k, (hspec x k).mpr hk, fun j hj => hu j ((hspec x j).mp hj)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListLength
