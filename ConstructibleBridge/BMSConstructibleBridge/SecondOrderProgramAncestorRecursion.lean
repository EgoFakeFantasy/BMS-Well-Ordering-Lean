import BMSConstructibleBridge.SecondOrderProgramAncestorClosure
import BMSConstructibleBridge.SecondOrderProgramAncestorClosedSet

/-!
# 原祖先成员关系的传递性与父节点递推

理解公理收集的是真实成员程序的非零查询，不另造传递闭包。
祖先集合的父查询封闭性与封闭集合的最小性相结合，给出直接父成员、
祖先传递性及精确递推式；所有列号和查询均为任意模型内部自然数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorRecursion

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramArithmetic (function_of_semantics_l)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramAncestorClosure (member_closed_l)
open SecondOrderProgramAncestorClosedSet (member_mem_l)
open SecondOrderProgramListShift (output_m output_syntax_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 同一实际成员图上的双层配对查询，不展开原程序的编译公式。 -/
def ancestor_m {Γ Δ : SortContext signature_m} (M : Term signature_m Γ Δ .set)
    (x b i : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.conj
    (PrimitiveFormulas.pair_m (x.weakenBound sort_m.num) (b.weakenBound sort_m.num) (.bvar .here))
    (.neg (output_m (M.weakenBound sort_m.num) (.bvar .here) (i.weakenBound sort_m.num)
      (Term.app (σ := signature_m) .zero .nil))))

theorem ancestor_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (M : Term signature_m Γ Δ .set) (x b i : Term signature_m Γ Δ .num) :
    (ancestor_m M x b i).satisfies η ↔
      ¬relation_l (M.eval η) (value_l (value_l (x.eval η) (b.eval η)) (i.eval η)) (zero_l ℳ) := by
  simp only [ancestor_m, Formula.satisfies, SecondOrderPairing.formula_l,
    output_syntax_l, Term.eval_weakenBound]
  change (∃ q, value_l (x.eval η) (b.eval η) = q ∧
    ¬relation_l (M.eval η) (value_l q (i.eval η)) (zero_l ℳ)) ↔ _
  simp only [exists_eq_left']

/-- 只收集实际二元查询的非零输出，不要求图已满足程序规格。 -/
theorem set_exists_l (hℳ : Theory.Models ℳ theory_m) (M : set_l ℳ) (u : num_l ℳ) :
    ∃ S : set_l ℳ, ∀ i, mem_l i S ↔
      ¬relation_l M (value_l u i) (zero_l ℳ) := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .neg (output_m (.fvar (.there (.there .here))) (.fvar (.there .here))
      (.fvar .here) (Term.app (σ := signature_m) .zero .nil))
  obtain ⟨S, hS⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree M).pushFree u)
  refine ⟨S, fun i => (hS i).trans ?_⟩
  simp only [φ, Formula.satisfies, output_syntax_l]
  rfl

private theorem root_set_exists_l (hℳ : Theory.Models ℳ theory_m)
    (M : set_l ℳ) (u p : num_l ℳ) :
    ∃ S : set_l ℳ, ∀ i, mem_l i S ↔
      i = p ∨ ¬relation_l M (value_l u i) (zero_l ℳ) := by
  let φ : Formula signature_m [] [.num, .num, .num, .set] :=
    .disj (.equal (.fvar .here) (.fvar (.there .here)))
      (.neg (output_m (.fvar (.there (.there (.there .here))))
        (.fvar (.there (.there .here))) (.fvar .here)
        (Term.app (σ := signature_m) .zero .nil)))
  obtain ⟨S, hS⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    ((((Env.empty (M := ℳ)).pushFree M).pushFree u).pushFree p)
  refine ⟨S, fun i => (hS i).trans ?_⟩
  simp only [φ, Formula.satisfies, output_syntax_l]
  rfl

/-- 实际父查询返回的列必为原成员程序接受的祖先。 -/
theorem parent_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {M C : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m c)) M)
    (hC : graph_semantics_l (graph_m c) C) {x b p : num_l ℳ}
    (hparent : ∀ t p, relation_l C (value_l x t) (succ_l p) → SecondOrderOrder.lt_l p t)
    (hp : relation_l C (value_l x b) (succ_l p)) :
    ¬relation_l M (value_l (value_l x b) p) (zero_l ℳ) :=
  member_closed_l hℳ c hM hC hparent (Or.inl rfl) hp

/-- 祖先的祖先仍由同一原成员程序接受；理解所得集合负责内部闭包。 -/
theorem trans_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {M C : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m c)) M)
    (hC : graph_semantics_l (graph_m c) C) {x b p i : num_l ℳ}
    (hparent : ∀ t p, relation_l C (value_l x t) (succ_l p) → SecondOrderOrder.lt_l p t)
    (hp : ¬relation_l M (value_l (value_l x b) p) (zero_l ℳ))
    (hi : ¬relation_l M (value_l (value_l x p) i) (zero_l ℳ)) :
    ¬relation_l M (value_l (value_l x b) i) (zero_l ℳ) := by
  obtain ⟨S, hS⟩ := set_exists_l hℳ M (value_l x b)
  apply (hS i).mp
  apply member_mem_l hℳ c hM hC (S := S) (b := p) ?_ hi
  intro t q ht hq
  apply (hS q).mpr
  apply member_closed_l hℳ c hM hC hparent (Or.inr ?_) hq
  rcases ht with rfl | ht
  · exact hp
  · exact (hS t).mp ht

/-- 父节点为p时，原祖先集合恰为p与p的原祖先集合之并。 -/
theorem member_some_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {M C : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m c)) M)
    (hC : graph_semantics_l (graph_m c) C) {x b p i : num_l ℳ}
    (hparent : ∀ t p, relation_l C (value_l x t) (succ_l p) → SecondOrderOrder.lt_l p t)
    (hp : relation_l C (value_l x b) (succ_l p)) :
    ¬relation_l M (value_l (value_l x b) i) (zero_l ℳ) ↔
      i = p ∨ ¬relation_l M (value_l (value_l x p) i) (zero_l ℳ) := by
  constructor
  · intro hi
    obtain ⟨S, hS⟩ := root_set_exists_l hℳ M (value_l x p) p
    apply (hS i).mp
    apply member_mem_l hℳ c hM hC (S := S) ?_ hi
    intro t q ht hq
    apply (hS q).mpr
    rcases ht with rfl | ht
    · exact Or.inl (SecondOrderModel.injective_l hℳ
        (function_value_unique_l (function_of_semantics_l hℳ c hC) hq hp))
    · exact Or.inr (member_closed_l hℳ c hM hC hparent ((hS t).mp ht) hq)
  · rintro (rfl | hi)
    · exact parent_l hℳ c hM hC hparent hp
    · exact trans_l hℳ c hM hC hparent (parent_l hℳ c hM hC hparent hp) hi

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorRecursion
