import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseBase
import BMSConstructibleBridge.PowerlessRelativeFiniteHullAssignments

/-! # 成员塌缩固定基集上的真实函数图

对象语言为纯隶属 ℒ，背景和正式出口均为原 Z₂。传递 B⊆I 的逐点
固定性来自既有原公式集合归纳；I 的真实无序对闭包再保证 Kuratowski
对及其全部编码成员留在 I。因此属于 I、定义域包含于 B、值域属于 B
的实际函数图逐点固定。证明读取同一 H 的真实图，不抽取 Type 函数。

本结论可用于固定捕获在 I 中的原自然数编码图，但不自动声称所有
编码参数已经属于 I，也不替代原 Def 在成员结构中的绝对性证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseGraphs

open Logic FirstOrder SecondOrderObjectSyntax
open PowerlessRelativeMembershipCollapseInjectivity (recursive_l recursive_m recursive_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ

/-- 同一源对象的全部真实成员留在 I 且逐点固定时，该对象也被固定。 -/
theorem image_fixed_l {I T H A : Raw}
    (hH : SecondOrderFunctionObjects.map_l hℳ H I T) (hRec : recursive_l hℳ I H)
    (hAI : SecondOrderQuotient.mem_l hℳ A I)
    (hMembers : ∀ x, SecondOrderQuotient.mem_l hℳ x A →
      SecondOrderQuotient.mem_l hℳ x I ∧ SecondOrderFunctionObjects.value_l hℳ H x x) :
    SecondOrderFunctionObjects.value_l hℳ H A A := by
  obtain ⟨u, hu, _⟩ := hH.2 A hAI
  have huA : u = A := by
    apply SecondOrderQuotient.ext_l hℳ u A
    intro z
    constructor
    · intro hzu
      obtain ⟨x, _, hxA, hxz⟩ := (hRec A u hAI hu.2 z).mp hzu
      have hzx := SecondOrderFunctionProperties.value_unique_l hℳ hH hxz (hMembers x hxA).2
      exact hzx.symm ▸ hxA
    · intro hzA
      exact (hRec A u hAI hu.2 z).mpr ⟨z, (hMembers z hzA).1, hzA, (hMembers z hzA).2⟩
  exact huA ▸ hu.2

/-- 无序对固定使用真实闭包，而不是非传递 I 内的局部配对判定。 -/
theorem pair_l {I T H a b p : Raw}
    (hH : SecondOrderFunctionObjects.map_l hℳ H I T) (hRec : recursive_l hℳ I H)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) I)
    (ha : SecondOrderQuotient.mem_l hℳ a I) (hb : SecondOrderQuotient.mem_l hℳ b I)
    (hFixA : SecondOrderFunctionObjects.value_l hℳ H a a)
    (hFixB : SecondOrderFunctionObjects.value_l hℳ H b b)
    (hp : SecondOrderPairObjects.pair_l hℳ a b p) :
    SecondOrderFunctionObjects.value_l hℳ H p p := by
  apply image_fixed_l hH hRec (hClosed.1 a b p ha hb hp)
  intro z hz
  rcases (hp z).mp hz with rfl | rfl
  · exact ⟨ha, hFixA⟩
  · exact ⟨hb, hFixB⟩

theorem ordered_l {I T H a b p : Raw}
    (hH : SecondOrderFunctionObjects.map_l hℳ H I T) (hRec : recursive_l hℳ I H)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) I)
    (ha : SecondOrderQuotient.mem_l hℳ a I) (hb : SecondOrderQuotient.mem_l hℳ b I)
    (hFixA : SecondOrderFunctionObjects.value_l hℳ H a a)
    (hFixB : SecondOrderFunctionObjects.value_l hℳ H b b)
    (hp : SecondOrderPairObjects.ordered_l hℳ a b p) :
    SecondOrderFunctionObjects.value_l hℳ H p p := by
  obtain ⟨s, t, hs, ht, hp⟩ := hp
  exact pair_l hH hRec hClosed (hClosed.1 a a s ha ha hs) (hClosed.1 a b t ha hb ht)
    (pair_l hH hRec hClosed ha ha hFixA hFixA hs)
    (pair_l hH hRec hClosed ha hb hFixA hFixB ht) hp

/-- 真实函数图的全部成员都是固定基集元素的有序对。 -/
theorem graph_l {B I T H A F : Raw}
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B)
    (hBI : ∀ x, SecondOrderQuotient.mem_l hℳ x B → SecondOrderQuotient.mem_l hℳ x I)
    (hH : SecondOrderFunctionObjects.map_l hℳ H I T) (hRec : recursive_l hℳ I H)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) I)
    (hFI : SecondOrderQuotient.mem_l hℳ F I)
    (hAB : ∀ x, SecondOrderQuotient.mem_l hℳ x A → SecondOrderQuotient.mem_l hℳ x B)
    (hF : SecondOrderFunctionObjects.map_l hℳ F A B) :
    SecondOrderFunctionObjects.value_l hℳ H F F := by
  have hFix := PowerlessRelativeMembershipCollapseBase.fixed_l hℳ B I T H hBase hBI hH hRec
  apply image_fixed_l hH hRec hFI
  intro p hp
  obtain ⟨a, b, ha, hb, hPair⟩ := hF.1 p hp
  have haB := hAB a ha
  exact ⟨PowerlessRelativeFiniteHullAssignments.ordered_l hClosed.1 (hBI a haB) (hBI b hb) hPair,
    ordered_l hH hRec hClosed (hBI a haB) (hBI b hb) (hFix a haB) (hFix b hb) hPair⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def graph_m {Γ Δ : SortContext ℒ} (B I H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let A := .bvar (.there .here)
    let F := .bvar .here
    .imp (member_m F (up (up I))) <|
      .imp (ThirdOrderTheory.subset_m A (up (up B))) <|
        .imp (map_m F A (up (up B))) (value_m (up (up H)) F F)

theorem graph_formula_l {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (B I H : Term ℒ Γ Δ .set) :
    (graph_m B I H).satisfies η ↔ ∀ A F,
      SecondOrderQuotient.mem_l hℳ F (I.eval η) →
      (∀ x, SecondOrderQuotient.mem_l hℳ x A → SecondOrderQuotient.mem_l hℳ x (B.eval η)) →
      SecondOrderFunctionObjects.map_l hℳ F A (B.eval η) →
      SecondOrderFunctionObjects.value_l hℳ (H.eval η) F F := by
  simp only [graph_m, Formula.satisfies, ThirdOrderSemantics.subset_formula_l,
    ThirdOrderSemantics.subset_l, ThirdOrderSemantics.member_l,
    SecondOrderObjectSyntax.map_l, SecondOrderObjectSyntax.value_l, member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval, SecondOrderQuotient.structure_l]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let I := .fvar (.there .here)
  let T := .fvar (.there (.there .here))
  let H := .fvar (.there (.there (.there .here)))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (ThirdOrderTheory.subset_m B I) <| .imp (map_m H I T) <|
      .imp (recursive_m I H) <| .imp (PowerlessRelativeFiniteHullAssignments.closed_m I)
        (graph_m B I H)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    ThirdOrderSemantics.subset_formula_l, ThirdOrderSemantics.subset_l,
    ThirdOrderSemantics.member_l, SecondOrderObjectSyntax.map_l, recursive_formula_l,
    PowerlessRelativeFiniteHullAssignments.closed_formula_l, graph_formula_l,
    Term.eval, SecondOrderQuotient.structure_l]
  exact fun hBase hBI hH hRec hClosed _ _ hFI hAB hF => graph_l hBase hBI hH hRec hClosed hFI hAB hF

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms image_fixed_l
#print axioms graph_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseGraphs
