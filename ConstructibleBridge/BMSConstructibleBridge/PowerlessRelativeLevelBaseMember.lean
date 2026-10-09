import BMSConstructibleBridge.PowerlessRelativeOrdinalCoverage

/-! # 非零相对层包含基对象

对象语言为原纯隶属 ℒ，背景为原 Z₂。先读实际历史的零阶段，再用
内部序数三歧性与严格层单调性证明基对象属于每个非零层。这里不要求
Collection、外部良基或可数性；最终闭句回到原对象推导核。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLevelBaseMember

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mk_l mem_l)
open PowerlessRelativeHierarchySemantics (empty_l level_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem zero_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {B e C : type_l hℳ} (he : empty_l hℳ e) (hC : level_l hℳ B e C) : C = B := by
  obtain ⟨A, F, R, _, heA, hF, hFC⟩ := hC
  rcases hF.2 e C ⟨heA, hFC⟩ with ⟨_, h⟩ | ⟨b, d, hSucc, _, _⟩ | ⟨hLimit, _⟩
  · exact h
  · exact False.elim (he b ((hSucc b).mpr (Or.inr rfl)))
  · obtain ⟨x, hx⟩ := hLimit.1
    exact False.elim (he x hx)

/-- 零阶段自身并非含有 B；严格晚于零的实际层才含有 B。 -/
theorem member_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {B a C : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hC : level_l hℳ B a C) (hNonempty : ∃ x, mem_l hℳ x a) : mem_l hℳ B C := by
  obtain ⟨E, hE, hEmpty⟩ := SecondOrderOrdinalSuccessor.empty_exists_l hℳ
  have he : empty_l hℳ (mk_l hℳ E) := by
    intro x
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact hEmpty X
  have hea : mem_l hℳ (mk_l hℳ E) a := by
    rcases SecondOrderOrdinalComparison.compare_l hℳ hE
      (PowerlessRelativeLevelClosure.ordinal_l hℳ hC) with h | h | h
    · obtain ⟨x, hx⟩ := hNonempty
      exact False.elim (he x (h.symm ▸ hx))
    · exact h
    · exact False.elim (he a h)
  obtain ⟨D, hD⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hE
  have hDB := zero_l hℳ he hD
  exact hDB ▸ PowerlessRelativeLevelClosure.members_l hℳ hBase hea hD hC

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let a := .fvar (.there .here)
  let C := .fvar (.there (.there .here))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B a C) <|
      .imp (.existsE .set <| SecondOrderObjectSyntax.member_m (.bvar .here)
        (a.weakenBound SetTheory.SetSort.set)) (SecondOrderObjectSyntax.member_m B C)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval]
  intro η hBase hC hNonempty
  exact member_l hℳ hBase hC hNonempty

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms zero_l
#print axioms member_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLevelBaseMember
