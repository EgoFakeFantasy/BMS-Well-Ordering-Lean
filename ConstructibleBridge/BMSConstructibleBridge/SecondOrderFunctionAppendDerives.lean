import BMSConstructibleBridge.SecondOrderFunctionAppend
import BMSConstructibleBridge.SecondOrderUnion
import BMSConstructibleBridge.SecondOrderAxioms
import BMSConstructibleBridge.SecondOrderObjectSyntax
import BMSConstructibleBridge.ThirdOrderSemantics
import YesMetaZFC.Automation.ModelClosure

/-! # 单点函数延拓的实际对象构造及原 Z₂ 推导

对有限历史延长一步时，显式扩大定义域与陪域，并以配对、并集生成同一
延拓图。无需原 PowerlessTheory 的 Collection，不假定无限历史集合存在。
全部 raw Value 坐标保留精确读数，供内部有限历史归纳使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionAppendDerives

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m map_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

theorem adjoin_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (A c : type_l hℳ) :
    ∃ S, ∀ x, mem_l hℳ x S ↔ mem_l hℳ x A ∨ x = c := by
  obtain ⟨U, hU⟩ := SecondOrderPairObjects.pair_exists_l hℳ c c
  obtain ⟨P, hP⟩ := SecondOrderPairObjects.pair_exists_l hℳ A U
  have hUnion := SecondOrderUnion.models_l hℳ
  change ∀ a : type_l hℳ, ∃ S, ∀ x,
    mem_l hℳ x S ↔ ∃ Y, mem_l hℳ Y a ∧ mem_l hℳ x Y at hUnion
  obtain ⟨S, hS⟩ := hUnion P
  refine ⟨S, fun x => (hS x).trans ?_⟩
  constructor
  · rintro ⟨Y, hY, hxY⟩
    rcases (hP Y).mp hY with rfl | rfl
    · exact Or.inl hxY
    · rcases (hU x).mp hxY with hx | hx
      · exact Or.inr hx
      · exact Or.inr hx
  · rintro (hx | hxc)
    · exact ⟨A, (hP A).mpr (Or.inl rfl), hx⟩
    · exact ⟨U, (hP U).mpr (Or.inr rfl), (hU x).mpr (Or.inl hxc)⟩

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {f A D c : type_l hℳ} (d : type_l hℳ)
    (hf : SecondOrderFunctionObjects.map_l hℳ f A D) (hc : ¬mem_l hℳ c A) :
    ∃ S E g, (∀ x, mem_l hℳ x S ↔ mem_l hℳ x A ∨ x = c) ∧
      (∀ y, mem_l hℳ y E ↔ mem_l hℳ y D ∨ y = d) ∧
      SecondOrderFunctionObjects.map_l hℳ g S E ∧
      ∀ x y, SecondOrderFunctionObjects.value_l hℳ g x y ↔
        SecondOrderFunctionObjects.value_l hℳ f x y ∨ x = c ∧ y = d := by
  obtain ⟨S, hS⟩ := adjoin_l hℳ A c
  obtain ⟨E, hE⟩ := adjoin_l hℳ D d
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ c d
  obtain ⟨g, hg⟩ := adjoin_l hℳ f p
  have hfE : SecondOrderFunctionObjects.map_l hℳ f A E := by
    constructor
    · intro q hq
      obtain ⟨x, y, hx, hy, hxy⟩ := hf.1 q hq
      exact ⟨x, y, hx, (hE y).mpr (Or.inl hy), hxy⟩
    · intro x hx
      obtain ⟨y, hy, hUnique⟩ := hf.2 x hx
      refine ⟨y, ⟨(hE y).mpr (Or.inl hy.1), hy.2⟩, ?_⟩
      intro z hz
      exact hUnique z ⟨(SecondOrderFunctionProperties.value_mem_l hℳ hf hz.2).2, hz.2⟩
  exact ⟨S, E, g, hS, hE,
    SecondOrderFunctionAppend.map_l hℳ hfE hc ((hE d).mpr (Or.inr rfl)) hS hp hg,
    SecondOrderFunctionAppend.value_l hℳ hp hg⟩

def adjoin_m {Γ Δ : SortContext ℒ} (A c S : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up S))
    (.disj (member_m (.bvar .here) (up A)) (.equal (.bvar .here) (up c)))

def reading_m {Γ Δ : SortContext ℒ} (f c d g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let x := .bvar (.there .here)
    let y := .bvar .here
    .iff (value_m (up₂ g) x y)
      (.disj (value_m (up₂ f) x y) (.conj (.equal x (up₂ c)) (.equal y (up₂ d))))

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let f : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let A := .fvar (.there .here)
  let D := .fvar (.there (.there .here))
  let c := .fvar (.there (.there (.there .here)))
  let d := .fvar (.there (.there (.there (.there .here))))
  .imp (map_m f A D) <| .imp (.neg (member_m c A)) <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      let S := .bvar (.there (.there .here))
      let E := .bvar (.there .here)
      let g := .bvar .here
      .conj (adjoin_m (up₃ A) (up₃ c) S) <|
        .conj (adjoin_m (up₃ D) (up₃ d) E) <|
          .conj (map_m g S E) (reading_m (up₃ f) (up₃ c) (up₃ d) g)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, adjoin_m, reading_m, Formula.satisfies, map_formula_l, value_formula_l,
    member_m, Arguments.eval, up₃, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hf hc
  exact exists_l hℳ _ hf hc

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms adjoin_l
#print axioms exists_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionAppendDerives
