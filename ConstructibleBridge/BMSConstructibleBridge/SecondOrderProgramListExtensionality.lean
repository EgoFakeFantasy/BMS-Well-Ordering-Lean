import BMSConstructibleBridge.SecondOrderListInduction
import BMSConstructibleBridge.SecondOrderProgramListLookup

/-!
# 原内部列表码由长度与有效条目决定

相同真实长度及全部有效内部位置的相同读值，足以推出原码相等。必须保留长度：
越界补零使不同长度的全零列表逐点读取相同。证明使用真实公式的内部列表归纳，
不假定这些内部码可以外部解码为标准有限列表。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListExtensionality

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLength (length_zero_l)
open SecondOrderProgramListShift (output_m output_syntax_l length_cons_l)
open SecondOrderProgramListLookup (lookup_m lookup_cons_zero_l lookup_cons_succ_l)
open SecondOrderProgramLength (length_m length_rel_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 在指定内部长度内，同一读取图将源码的每个值也赋给目标码。 -/
def entries_l (E : set_l ℳ) (x y n : num_l ℳ) : Prop :=
  ∀ i, SecondOrderOrder.lt_l i n → ∀ z, relation_l E (value_l x i) z → relation_l E (value_l y i) z

/-- 有效位置读值相同的实际模板，保持长度与两个列表码参数。 -/
def entries_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (x y n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num (.imp (PrimitiveFormulas.lt_m (.bvar .here) (n.weakenBound sort_m.num))
    (.forallE .num (.imp
      (output_m ((E.weakenBound sort_m.num).weakenBound sort_m.num)
        ((x.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here)) (.bvar .here))
      (output_m ((E.weakenBound sort_m.num).weakenBound sort_m.num)
        ((y.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here)) (.bvar .here)))))

/-- 模板解释精确对应原有效下标读值蕴含。 -/
theorem entries_syntax_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) (x y n : Term signature_m Γ Δ .num) :
    Formula.satisfies η (entries_m E x y n) ↔ entries_l (E.eval η) (x.eval η) (y.eval η) (n.eval η) := by
  simp only [entries_m, entries_l, Formula.satisfies, SecondOrderOrder.formula_l,
    output_syntax_l, Term.eval_weakenBound]
  rfl

/-- 自由槽[x,L,E]；对另一码y及共同内部长度n量化，不固定归纳步的尾长。 -/
def extensionality_m : Formula signature_m [] [.num, .set, .set] :=
  .forallE .num (.forallE .num (.imp
    (GraphSyntax.edge_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
    (.imp (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here))
      (.imp (entries_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar (.there .here)) (.bvar .here))
        (.equal (.fvar .here) (.bvar (.there .here)))))))

/-- 原归纳允许该实际列表外延性正文。 -/
theorem extensionality_language_m : language_m extensionality_m = true := pure_language_m _ rfl

/-- 外延性公式与归纳性质的逐模型对应。 -/
theorem extensionality_syntax_l (L E : set_l ℳ) (x : num_l ℳ) :
    Formula.satisfies ((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree x) extensionality_m ↔
      ∀ y n, relation_l L x n → relation_l L y n → entries_l E x y n → x = y := by
  simp only [extensionality_m, Formula.satisfies, SecondOrderPairing.edge_l, entries_syntax_l]
  rfl

/-- 同一真实长度与有效位置读值决定唯一原列表码，覆盖全部非标准内部长度。 -/
theorem extensionality_l (hℳ : Theory.Models ℳ theory_m) {L E : set_l ℳ}
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n : num_l ℳ}
    (hx : relation_l L x n) (hy : relation_l L y n) (he : entries_l E x y n) : x = y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  have hLf := function_of_semantics_l hℳ length_m hL
  have h00 : relation_l L (zero_l ℳ) (zero_l ℳ) :=
    (length_rel_l hℳ hL hI _ _).mpr ((length_zero_l hℳ hI _).mpr rfl)
  have key : ∀ x : num_l ℳ, ∀ y n, relation_l L x n → relation_l L y n →
      entries_l E x y n → x = y := by
    apply SecondOrderListInduction.list_induct_l hℳ extensionality_m extensionality_language_m
      (((Env.empty (M := ℳ)).pushFree E).pushFree L)
      (fun x => ∀ y n, relation_l L x n → relation_l L y n → entries_l E x y n → x = y)
      (extensionality_syntax_l L E)
    · intro y n hx hy _
      have hn := function_value_unique_l hLf hx h00
      subst n
      exact ((length_zero_l hℳ hI y).mp ((length_rel_l hℳ hL hI _ _).mp hy)).symm
    · intro a t ih y n hx hy he
      obtain ⟨m, hm, _⟩ := hLf t
      have hcons : relation_l L (succ_l (value_l a t)) (succ_l m) :=
        (length_rel_l hℳ hL hI _ _).mpr
          ((length_cons_l hℳ hI a t m).mpr ((length_rel_l hℳ hL hI _ _).mp hm))
      have hn := function_value_unique_l hLf hx hcons
      subst n
      rcases predecessor_l hℳ y with rfl | ⟨p, rfl⟩
      · exact False.elim (nonzero_l hℳ m (function_value_unique_l hLf hy h00))
      · obtain ⟨b, u, rfl⟩ := SecondOrderUnpairing.surjective_l hℳ p
        have hu : relation_l L u m := (length_rel_l hℳ hL hI _ _).mpr
          ((length_cons_l hℳ hI b u m).mp ((length_rel_l hℳ hL hI _ _).mp hy))
        have hba : b = a := (lookup_cons_zero_l hℳ hE b u a).mp
          (he (zero_l ℳ) (SecondOrderOrder.zero_succ_l hℳ m) a
            ((lookup_cons_zero_l hℳ hE a t a).mpr rfl))
        subst b
        apply congrArg (fun v => succ_l (value_l a v))
        apply ih u m hm hu
        intro i hi z hz
        exact (lookup_cons_succ_l hℳ hE a u i z).mp
          (he (succ_l i) ((SecondOrderOrder.succ_iff_l hℳ i m).mpr hi) z
            ((lookup_cons_succ_l hℳ hE a t i z).mpr hz))
  exact key x y n hx hy he

#print axioms entries_l
#print axioms entries_m
#print axioms entries_syntax_l
#print axioms extensionality_m
#print axioms extensionality_language_m
#print axioms extensionality_syntax_l
#print axioms extensionality_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListExtensionality
