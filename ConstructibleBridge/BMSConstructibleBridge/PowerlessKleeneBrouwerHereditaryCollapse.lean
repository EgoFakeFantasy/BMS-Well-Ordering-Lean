import BMSConstructibleBridge.PowerlessKleeneBrouwerNumericIndex
import BMSConstructibleBridge.PowerlessRelationalCollapseNumericOrderedHereditary

/-! # 同根覆盖数码坍缩的同一原值遗传资格

纯隶属 ℒ，原 Z₂。前驱优先 Class J 在证明内真实构造，再接既有原预算坍缩
及内部数码枚举，取得给定原 H 的同一输出 X 的遗传资格。没有把输出换成
另外选择的代表，也不预供 Class H/T/J、序型坍缩或统一预算。
原 H 存在及同根路径覆盖 I 仍须由实际根码证明，不能据此宣称完整解码闭包。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerHereditaryCollapse

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem hereditary_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ) {B ω I A z r T H x X : Raw}
    (hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ b, mem_l hℳ b I → mem_l hℳ b ω)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hA : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hZero : PowerlessNatural.zero_l (ℳ := 𝒱) z) (hz : mem_l hℳ z ω) (hr : mem_l hℳ r I)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hCover : PowerlessKleeneBrouwerNumericIndex.cover_l ω I A z r)
    (hValue : value_l (ℳ := 𝒱) H x X) : PowerlessHereditaryClass.member_l hℳ B X := by
  obtain ⟨J, hJClass, hRelation, hJ, hExtends⟩ :=
    PowerlessKleeneBrouwerNumericIndex.exists_l hBase hω hSub hI hA hZero hz hr hH hCover
  exact PowerlessRelationalCollapseNumericOrderedHereditary.hereditary_l K hBase hω hSub hA hI
    hJClass hRelation hJ hExtends hH hValue

def schema_m {Δ : SortContext ℒ} (B ω I A z r T H x X : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (ThirdOrderTheory.subset_m I ω) <| .imp (PowerlessRelativeHierarchySyntax.class_m B I) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B A) <|
        .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (up z)))) <|
          .imp (SecondOrderObjectSyntax.member_m z ω) <| .imp (SecondOrderObjectSyntax.member_m r I) <|
            .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
              .imp (PowerlessKleeneBrouwerNumericIndex.cover_m ω I A z r) <|
                .imp (PowerlessValueBounded.formula_m H x X) (PowerlessHereditaryClass.formula_m B X)

def sentence_m {Δ : SortContext ℒ} (B ω I A z r T H x X : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω I A z r T H x X)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω I A z r T H x X : Term ℒ [] Δ .set) : (sentence_m B ω I A z r T H x X).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, ThirdOrderSemantics.subset_formula_l, subset_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderObjectSyntax.member_m, Arguments.eval,
    SecondOrderCollapseSyntax.formula_l, PowerlessKleeneBrouwerNumericIndex.cover_formula_l,
    PowerlessValueBounded.formula_l, PowerlessHereditaryClass.formula_l K,
    up, Term.eval_weakenBound, Term.eval]
  exact hereditary_l K

theorem derives_m {Δ : SortContext ℒ} (B ω I A z r T H x X : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B ω I A z r T H x X)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B ω I A z r T H x X)

#print axioms hereditary_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerHereditaryCollapse
