import BMSConstructibleBridge.SecondOrderMemberDefFiniteAssignment
import BMSConstructibleBridge.SecondOrderMemberFiniteFunctionAssignment
import BMSConstructibleBridge.PowerlessMemberDefDerives
import BMSConstructibleBridge.PowerlessFiniteClosureSyntax

/-! # 任意内部有限子集的固定 Def 层界

任意原商中的有限集合，只要包含于母集，就属于母集的实际 Def。
有限双射、非标准长度、全部商成员和空母集分支均保留；没有较早极限层、
Collection 或完整源模型假设。原纯集合闭句的图翻译最后取得原 Z₂ 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefFiniteSubsets

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l mk_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem member_l (K : source_coding_l hℳ) {X D Y : type_l hℳ}
    (hDef : SecondOrderMemberDef.spec_l hℳ X D)
    (hFinite : PowerlessFiniteClosureSyntax.finite_l (ℳ := 𝒱) K.omega Y)
    (hYX : ∀ y, mem_l hℳ y Y → mem_l hℳ y X) : mem_l hℳ Y D := by
  rcases hDef with ⟨hEmpty, hPair⟩ | hDef
  · have hEq : Y = X := SecondOrderQuotient.ext_l hℳ Y X (fun y =>
      iff_of_false (fun hy => hEmpty y (hYX y hy)) (hEmpty y))
    exact hEq.symm ▸ (hPair X).mpr (Or.inl rfl)
  · obtain ⟨A, a, ha, V, E, P, Q, R, T, F, H, hAX, h, hHD⟩ := hDef
    obtain ⟨n, hn, f, hf, hCover, _⟩ := hFinite
    obtain ⟨l, hl⟩ := numberCode_surjective_l K ⟨n, hn⟩
    have hl' : (numberCode_l K l).val = n := congrArg Subtype.val hl
    rw [← hl'] at hf hCover
    have hYA : ∀ y, mem_l hℳ y Y → mem_l hℳ y (mk_l hℳ A) := by
      intro y hy
      rw [hAX]
      exact hYX y hy
    obtain ⟨c, hc, hRead⟩ := SecondOrderMemberFiniteFunctionAssignment.range_l K A a ha
      h.powers l hf hCover hYA
    have hYH := SecondOrderMemberDefFiniteAssignment.member_l K h l c hc hRead
    exact hHD ▸ hYH

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let X := .fvar (.there .here)
  let D := .fvar (.there (.there .here))
  .imp (SecondOrderOmegaSyntax.omega_m ω) (.imp (PowerlessMemberDefSyntax.global_m X D)
    (.forallE .set (.imp
      (PowerlessFiniteClosureSyntax.finite_m (ω.weakenBound SetTheory.SetSort.set) (.bvar .here))
      (.imp (PowerlessFiniteClosureSyntax.subset_m (.bvar .here) (X.weakenBound SetTheory.SetSort.set))
        (SecondOrderObjectSyntax.member_m (.bvar .here) (D.weakenBound SetTheory.SetSort.set))))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l hℳ,
    PowerlessMemberDefDerives.formula_l K, PowerlessFiniteClosureSyntax.finite_formula_l,
    PowerlessFiniteClosureSyntax.subset_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval, Term.eval_weakenBound]
  intro hω hDef Y hFinite hYX
  have hEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  rw [hEq] at hFinite
  exact member_l K hDef hFinite hYX

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms member_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefFiniteSubsets
