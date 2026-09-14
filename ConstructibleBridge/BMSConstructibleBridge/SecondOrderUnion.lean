import BMSConstructibleBridge.SecondOrderGraftSemantics
import BMSConstructibleBridge.SecondOrderAxioms

/-!
# 任意模型中的并集及其对象公理

用实际理解选出母根的孙节点，再复用已证拼接域和成员规格。跨图成员的反向
匹配由内部双模拟完成，不能只验证与母集使用同一关系实数的特殊元素。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderUnion

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing GraphTranslation

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ) :
    ∃ U : SecondOrderGraph.code_l ℳ, ∀ B,
      SecondOrderGraph.mem_l B U ↔ ∃ C, SecondOrderGraph.mem_l C A ∧ SecondOrderGraph.mem_l B C := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .existsE .num (.conj
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar .here) (.fvar (.there .here)))
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar .here)))
  obtain ⟨P, hP⟩ := SecondOrderModel.comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree A.real).pushFree A.root)
  have h₀ : ∀ c, mem_l c P ↔ ∃ b, relation_l A.real b A.root ∧ relation_l A.real c b := by
    intro c
    refine (hP c).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l]
    rfl
  have h₁ : ∀ c, mem_l c P → SecondOrderDomain.wf_l A.real c := by
    intro c h
    obtain ⟨b, hb, hc⟩ := (h₀ c).mp h
    exact SecondOrderDomain.child_l hℳ A.real b c
      (SecondOrderDomain.child_l hℳ A.real A.root b A.wf hb) hc
  obtain ⟨U, hU⟩ := SecondOrderGraftSemantics.exists_l hℳ A.real P h₁
  refine ⟨U, fun B => (hU B).trans ?_⟩
  constructor
  · rintro ⟨c, hc, h₂⟩
    obtain ⟨b, hb, hc⟩ := (h₀ c).mp hc
    exact ⟨SecondOrderGraph.child_l hℳ A b hb, SecondOrderGraph.child_mem_l hℳ A b hb, c, hc, h₂⟩
  · rintro ⟨C, ⟨b, hb, h₂⟩, ⟨d, hd, h₃⟩⟩
    obtain ⟨c, hc, h₄⟩ := (SecondOrderBisimulation.match_l C.real A.real C.root b h₂).1 d hd
    exact ⟨c, (h₀ c).mpr ⟨b, hb, hc⟩,
      SecondOrderBisimulation.trans_l hℳ B.real C.real A.real B.root d c h₃ h₄⟩

private def member {Γ Δ : SortContext ℒ} (s t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .rel .membership (.cons s (.cons t .nil))

/-- 纯隶属语言中的完整并集公理。 -/
def formula_m : Sentence ℒ :=
  .forallE .set <| .existsE .set <| .forallE .set <|
    .iff (member (.bvar .here) (.bvar (.there .here)))
      (.existsE .set (.conj (member (.bvar .here) (.bvar (.there (.there (.there .here)))))
        (member (.bvar (.there .here)) (.bvar .here))))

theorem models_l (hℳ : Theory.Models ℳ theory_m) :
    formula_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  change ∀ a : SecondOrderQuotient.type_l hℳ, ∃ u, ∀ b,
    SecondOrderQuotient.mem_l hℳ b u ↔
      ∃ c, SecondOrderQuotient.mem_l hℳ c a ∧ SecondOrderQuotient.mem_l hℳ b c
  intro a
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨U, hU⟩ := exists_l hℳ A
  refine ⟨SecondOrderQuotient.mk_l hℳ U, fun b => ?_⟩
  obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ b
  refine (hU B).trans ?_
  constructor
  · rintro ⟨C, h, h₁⟩
    exact ⟨SecondOrderQuotient.mk_l hℳ C, h, h₁⟩
  · rintro ⟨c, h, h₁⟩
    obtain ⟨C, rfl⟩ := SecondOrderQuotient.surj_l hℳ c
    exact ⟨C, h, h₁⟩

theorem derives_m : Derives theory_m [] (form_m formula_m) :=
  SecondOrderAxioms.interpretation_m formula_m (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderUnion
