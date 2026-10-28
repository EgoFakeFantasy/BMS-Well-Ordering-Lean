import BMSConstructibleBridge.PowerlessRelationalCollapseOutput
import BMSConstructibleBridge.PowerlessRelativeLimitFunctionRange

/-! # 指定极限层内的原关系坍缩值

纯隶属 ℒ，原 Z₂。A/E/G/x 均已落在给定非零极限层 L 时，
原递归值 y 是 G 的实际值域上的 Δ₀ 切片，故仍属于同一 L。
全图 H、原陪域 T 与局部陪域 C 不充当分离参数。
这加强了仅得 Class 身份的单步结果，未假定无限前驱族已有共同预算。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseLimitOutput

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem output_l {B β L A I E T H C G x y : Raw}
    (hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hL : PowerlessRelativeHierarchySemantics.level_l hℳ B β L)
    (hAL : mem_l hℳ A L) (hEL : mem_l hℳ E L)
    (hGL : mem_l hℳ G L) (hxL : mem_l hℳ x L)
    (hC : ∀ a, mem_l hℳ a C → ∀ b, mem_l hℳ b a → mem_l hℳ b C)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hG : PowerlessRelationalCollapsePartial.partial_l A I E C G)
    (hCover : ∀ a, mem_l hℳ a I → SecondOrderFunctionObjects.value_l hℳ A a x → mem_l hℳ a E)
    (hxI : mem_l hℳ x I) (hxy : SecondOrderFunctionObjects.value_l hℳ H x y) :
    mem_l hℳ y L := by
  obtain ⟨R, hRL, hR⟩ := PowerlessRelativeLimitFunctionRange.exists_l hBase hLimit hL
    hEL hGL (q := C) (by exact hG.2.2.1)
  let η : Env 𝒱 [] [.set, .set, .set, .set] :=
    Env.empty |>.pushFree A |>.pushFree G |>.pushFree E |>.pushFree x
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := PowerlessRelationalCollapseOutput.body_m
    (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there .here)) (.fvar .here)
  have hφ : Formula.IsDelta0 membershipLevyBound φ :=
    PowerlessRelationalCollapseOutput.body_delta_m _ _ _ _ _
  have hBody z : φ.satisfies (η.pushFree z) ↔
      ∃ a, mem_l hℳ a E ∧ SecondOrderFunctionObjects.value_l hℳ A a x ∧
        SecondOrderFunctionObjects.value_l hℳ G a z :=
    PowerlessRelationalCollapseOutput.body_formula_l (η.pushFree z) _ _ _ _ _
  obtain ⟨Y, hYL, hY⟩ := PowerlessRelativeLimitDeltaSeparation.exists_l hBase hLimit hL hφ η hRL (by
    intro s v
    cases v with
    | here => exact hxL
    | there v => cases v with
      | here => exact hEL
      | there v => cases v with
        | here => exact hGL
        | there v => cases v with
          | here => exact hAL
          | there v => nomatch v)
  have hEq : y = Y := by
    apply SecondOrderQuotient.ext_l hℳ
    intro z
    constructor
    · intro hzy
      obtain ⟨a, haI, hax, haz⟩ := (hH.2.2.2 x y hxI hxy z).mp hzy
      have haE := hCover a haI hax
      have hGaz := (PowerlessRelationalCollapsePartial.value_l hH hC hG haE).mpr haz
      exact (hY z).mpr ⟨(hR z).mpr ⟨a, hGaz⟩, (hBody z).mpr ⟨a, haE, hax, hGaz⟩⟩
    · intro hzY
      obtain ⟨a, haE, hax, haz⟩ := (hBody z).mp ((hY z).mp hzY).2
      exact (hH.2.2.2 x y hxI hxy z).mpr ⟨a, hG.1 a haE, hax,
        (PowerlessRelationalCollapsePartial.value_l hH hC hG haE).mp haz⟩
  exact hEq.symm ▸ hYL

def schema_m {Δ : SortContext ℒ}
    (B β L A I E T H C G x y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β L) <|
        .imp (member_m A L) <| .imp (member_m E L) <| .imp (member_m G L) <| .imp (member_m x L) <|
          .imp (PowerlessRelativeHierarchyDerives.transitive_m C) <|
            .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
              .imp (PowerlessRelationalCollapsePartial.partial_m A I E C G) <|
                .imp (PowerlessRelationalCollapseOutput.covered_m A I E x) <| .imp (member_m x I) <|
                  .imp (SecondOrderObjectSyntax.value_m H x y) (member_m y L)

def sentence_m {Δ : SortContext ℒ}
    (B β L A I E T H C G x y : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β L A I E T H C G x y)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β L A I E T H C G x y : Term ℒ [] Δ .set) :
    (sentence_m B β L A I E T H C G x y).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K, SecondOrderCollapseSyntax.formula_l,
    PowerlessRelationalCollapsePartial.formula_l, PowerlessRelationalCollapseOutput.covered_formula_l,
    SecondOrderObjectSyntax.value_l, member_m, Arguments.eval]
  exact fun hBase hLimit hL hA hE hG hx hC hH hPartial hCover hxI hxy =>
    output_l hBase hLimit hL hA hE hG hx hC hH hPartial hCover hxI hxy

theorem derives_m {Δ : SortContext ℒ}
    (B β L A I E T H C G x y : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B β L A I E T H C G x y)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B β L A I E T H C G x y)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseLimitOutput
