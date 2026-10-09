import BMSConstructibleBridge.PowerlessRelativeLevelClosure
import BMSConstructibleBridge.PowerlessHierarchyLightHistoryUnique
import BMSConstructibleBridge.PowerlessRelativeCofinalDefGraph
import BMSConstructibleBridge.SecondOrderFunctionRestriction

/-! # 较早指标的真实原层次前史存在

纯隶属 ℒ 对象结论经原图翻译回到原 Z₂ Derives。实际 U=Lβ[B]
自带原完整历史见证；对 A∈β 限制该同一图，以层单调性证明全部
输出属于 U。零、后继及精确极限并均保留，再用 D:U→U 的完整
原 Def 读数把同一 f 认作轻量历史。没有预供历史或宿主递归。

只证明 raw 图的实际存在及陪域界，不证明 f∈U、f∈外层 W 或
Class 身份；这些仍需严格预算界，不能由函数值域界直接推出。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLayerHistoryPrefix

open Logic FirstOrder SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l history_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem prefix_l {B β U A : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hU : level_l hℳ B β U) (hAβ : mem_l hℳ A β) :
    ∃ f : type_l hℳ, history_l hℳ B A f U := by
  have hβ := PowerlessRelativeLevelClosure.ordinal_l hℳ hU
  have hA : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) A := by
    apply SetTheory.Structure.IsOrdinal.mem hβ
    exact hAβ
  obtain ⟨C, F, R, hC, hβC, hF, _hFU⟩ := hU
  have hAβSub x (hx : mem_l hℳ x A) : mem_l hℳ x β := hβ.transitive A hAβ x hx
  have hAC x (hx : mem_l hℳ x A) : mem_l hℳ x C :=
    hC.transitive β hβC x (hAβSub x hx)
  obtain ⟨f, hf, hRead⟩ := SecondOrderFunctionRestriction.exists_l hℳ hF.1 hAC
  have hRange a c (hac : SecondOrderFunctionObjects.value_l hℳ f a c) : mem_l hℳ c U := by
    obtain ⟨ha, hFc⟩ := (hRead a c).mp hac
    have hc : level_l hℳ B a c := ⟨C, F, R, hC, hAC a ha, hF, hFc⟩
    exact PowerlessRelativeLevelClosure.members_l hℳ hBase (hAβSub a ha) hc
      ⟨C, F, R, hC, hβC, hF, _hFU⟩
  have hfU : SecondOrderFunctionObjects.map_l hℳ f A U := by
    constructor
    · intro p hp
      obtain ⟨a, c, ha, _hcR, hPair⟩ := hf.1 p hp
      exact ⟨a, c, ha, hRange a c ⟨p, hp, hPair⟩, hPair⟩
    · intro a ha
      obtain ⟨c, hc, _hUnique⟩ := hf.2 a ha
      exact ⟨c, ⟨hRange a c hc.2, hc.2⟩,
        fun y hy => SecondOrderFunctionProperties.value_unique_l hℳ hf hy.2 hc.2⟩
  refine ⟨f, hfU, ?_⟩
  rintro a c ⟨ha, hac⟩
  have hStep := hF.2 a c ⟨hAC a ha, ((hRead a c).mp hac).2⟩
  rcases hStep with hZero | hSuccessor | hLimit
  · exact Or.inl hZero
  · obtain ⟨b, d, hb, hd, hDef⟩ := hSuccessor
    exact Or.inr (Or.inl ⟨b, d, hb, (hRead b d).mpr
      ⟨hA.transitive a ha b ((hb b).mpr (Or.inr rfl)), hd⟩, hDef⟩)
  · obtain ⟨hLimit, hUnion⟩ := hLimit
    refine Or.inr (Or.inr ⟨hLimit, fun x => (hUnion x).trans ?_⟩)
    constructor
    · rintro ⟨b, d, hb, hd, hxd⟩
      exact ⟨b, d, hb, (hRead b d).mpr ⟨hA.transitive a ha b hb, hd⟩, hxd⟩
    · rintro ⟨b, d, hb, hd, hxd⟩
      exact ⟨b, d, hb, ((hRead b d).mp hd).2, hxd⟩

theorem exists_l {B β U A D : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hU : level_l hℳ B β U) (hAβ : mem_l hℳ A β)
    (hD : PowerlessRelativeCofinalDefGraph.graph_l U D) :
    ∃ f : type_l hℳ, history_l hℳ B A f U ∧
      PowerlessHierarchyLightHistory.history_l hℳ B D A U f := by
  obtain ⟨f, hf⟩ := prefix_l hBase hU hAβ
  exact ⟨f, hf, PowerlessHierarchyLightHistoryUnique.from_original_l hℳ hD.2 (fun _ h => h) hf⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def result_m {Γ Δ : SortContext ℒ} (B A U D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj
    (PowerlessRelativeHierarchySyntax.history_m (up B) (up A) (.bvar .here) (up U))
    (PowerlessHierarchyLightHistory.formula_m (up B) (up D) (up A) (up U) (.bvar .here))

theorem result_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B A U D : Term ℒ Γ Δ .set) :
    (result_m B A U D).satisfies η ↔ ∃ f : type_l hℳ,
      history_l hℳ (B.eval η) (A.eval η) f (U.eval η) ∧
        PowerlessHierarchyLightHistory.history_l hℳ
          (B.eval η) (D.eval η) (A.eval η) (U.eval η) f := by
  simp only [result_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.history_formula_l K,
    PowerlessHierarchyLightHistory.reading_formula_l hℳ, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let β := .fvar (.there .here)
  let U := .fvar (.there (.there .here))
  let A := .fvar (.there (.there (.there .here)))
  let D := .fvar (.there (.there (.there (.there .here))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B β U) <|
      .imp (member_m A β) <| .imp (PowerlessRelativeCofinalDefGraph.graph_m U D) (result_m B A U D)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeCofinalDefGraph.graph_formula_l K, result_formula_l K,
    member_m, Arguments.eval, Term.eval, SecondOrderQuotient.structure_l]
  exact fun hBase hU hAβ hD => exists_l hBase hU hAβ hD

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms prefix_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLayerHistoryPrefix
