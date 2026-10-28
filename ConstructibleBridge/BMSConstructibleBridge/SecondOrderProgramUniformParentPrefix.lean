import BMSConstructibleBridge.SecondOrderProgramParentPrefixStep

/-!
# 任意内部行的前缀父关系与祖先关系

实际纯公式只说前缀内每个父查询逐输出一致。原内部归纳消费已证零行和后继行，
因此不将行号假定为外部标准自然数；原祖先对应只需界内父查询，不需要补齐前缀外。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentPrefix

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramListShift (output_m output_syntax_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 同一统一父图在数组x、行r、列t上的实际输出模板。 -/
def at_row_m {Γ Δ : SortContext signature_m} (P : Term signature_m Γ Δ .set)
    (x r t q : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.conj
    (PrimitiveFormulas.pair_m (x.weakenBound sort_m.num) (r.weakenBound sort_m.num) (.bvar .here))
    (output_m (P.weakenBound sort_m.num) (.bvar .here) (t.weakenBound sort_m.num) (q.weakenBound sort_m.num)))

/-- 双层原配对精确解释为同一数组及行的父查询，不增加新原语。 -/
theorem at_row_syntax_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (P : Term signature_m Γ Δ .set) (x r t q : Term signature_m Γ Δ .num) :
    Formula.satisfies η (at_row_m P x r t q) ↔
      relation_l (P.eval η) (value_l (value_l (x.eval η) (r.eval η)) (t.eval η)) (q.eval η) := by
  simp only [at_row_m, Formula.satisfies, SecondOrderPairing.formula_l, output_syntax_l,
    Term.eval_weakenBound]
  change (∃ a, value_l (x.eval η) (r.eval η) = a ∧
    relation_l (P.eval η) (value_l a (t.eval η)) (q.eval η)) ↔ _
  simp only [exists_eq_left']

/-- 自由槽[r,x,z,b,P]，对全部界内列t及输出q量化。 -/
def prefix_m : Formula signature_m [] [.num, .num, .num, .num, .set] :=
  .forallE .num (.imp (PrimitiveFormulas.lt_m (.bvar .here) (.fvar (.there (.there (.there .here)))))
    (.forallE .num (.iff
      (at_row_m (.fvar (.there (.there (.there (.there .here)))))
        (.fvar (.there .here)) (.fvar .here) (.bvar (.there .here)) (.bvar .here))
      (at_row_m (.fvar (.there (.there (.there (.there .here)))))
        (.fvar (.there (.there .here))) (.fvar .here) (.bvar (.there .here)) (.bvar .here)))))

/-- 前缀父查询的一致性公式属于原纯语言。 -/
theorem prefix_language_m : language_m prefix_m = true := pure_language_m _ rfl

/-- 真实归纳公式保留两个原数组码和全部内部界内查询。 -/
theorem prefix_syntax_l (P : set_l ℳ) (x z b r : num_l ℳ) :
    Formula.satisfies ((((((Env.empty (M := ℳ)).pushFree P).pushFree b).pushFree z).pushFree x).pushFree r)
      prefix_m ↔ ∀ t, SecondOrderOrder.lt_l t b → ∀ q,
        relation_l P (value_l (value_l x r) t) q ↔ relation_l P (value_l (value_l z r) t) q := by
  simp only [prefix_m, Formula.satisfies, SecondOrderOrder.formula_l, at_row_syntax_l]
  rfl

/-- 任意内部行上，具有共同前缀entry的两个数组在前缀内逐父查询一致。 -/
theorem parent_congr_l (hℳ : Theory.Models ℳ theory_m) {P L J : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x z n m b : num_l ℳ}
    (hx : relation_l L x n) (hz : relation_l L z m)
    (hbx : b = n ∨ SecondOrderOrder.lt_l b n) (hbz : b = m ∨ SecondOrderOrder.lt_l b m)
    (hentry : ∀ j, SecondOrderOrder.lt_l j b → ∀ r v,
      relation_l J (value_l x (value_l j r)) v ↔ relation_l J (value_l z (value_l j r)) v)
    (r : num_l ℳ) : ∀ t, SecondOrderOrder.lt_l t b → ∀ q,
    relation_l P (value_l (value_l x r) t) q ↔ relation_l P (value_l (value_l z r) t) q := by
  apply induct_l hℳ prefix_m prefix_language_m
    (((((Env.empty (M := ℳ)).pushFree P).pushFree b).pushFree z).pushFree x)
    (fun r => ∀ t, SecondOrderOrder.lt_l t b → ∀ q,
      relation_l P (value_l (value_l x r) t) q ↔ relation_l P (value_l (value_l z r) t) q)
    (prefix_syntax_l P x z b) ?_ ?_ r
  · intro t ht q
    exact SecondOrderProgramParentPrefixStep.zero_congr_l hℳ hP hL hJ hx hz hbx hbz
      (fun j hj v => hentry j hj (zero_l ℳ) v) ht q
  · intro r ih t ht q
    exact SecondOrderProgramParentPrefixStep.succ_congr_l hℳ hP hL hJ hx hz hbx hbz r
      (fun j hj v => hentry j hj (succ_l r) v) ih ht q

/-- 同一前缀内的实际祖先成员程序逐值一致，保留原统一父程序与内部行参数。 -/
theorem member_congr_l (hℳ : Theory.Models ℳ theory_m) {M L J : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x z n m b : num_l ℳ}
    (hx : relation_l L x n) (hz : relation_l L z m)
    (hbx : b = n ∨ SecondOrderOrder.lt_l b n) (hbz : b = m ∨ SecondOrderOrder.lt_l b m)
    (hentry : ∀ j, SecondOrderOrder.lt_l j b → ∀ r v,
      relation_l J (value_l x (value_l j r)) v ↔ relation_l J (value_l z (value_l j r)) v)
    (r : num_l ℳ) {t : num_l ℳ} (ht : SecondOrderOrder.lt_l t b) (i q : num_l ℳ) :
    relation_l M (value_l (value_l (value_l x r) t) i) q ↔
      relation_l M (value_l (value_l (value_l z r) t) i) q := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  exact SecondOrderProgramAncestorPrefixCongruence.member_congr_l hℳ parent_m parent_m hP hP hM hM
    (value_l x r) (value_l z r) b
    (fun _ _ hp => SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hp)
    (parent_congr_l hℳ hP hL hJ hx hz hbx hbz hentry r) ht i q

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentPrefix
