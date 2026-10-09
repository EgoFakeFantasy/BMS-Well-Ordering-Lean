import BMSConstructibleBridge.PowerlessCanonicalOrderLightHistoryUnique
import BMSConstructibleBridge.SecondOrderAxioms

/-! # 有界规范序前史唯一性的原 Z₂ 推导

对象句使用纯隶属 ℒ AST，再经既有 GraphTranslation 回到原 num/set
语言及原 Derives 核。守卫精确保留实际 F/G 映射、内部序数和两母界的
有限赋值覆盖；不加入 Class 可数性、Collection 或任何前史存在公理。

这只是确定性条件句，不证明 Class 长前史存在，也不冒充原 BMS 闭句。
最终存在性装配必须从实际极限层与预算归纳消去这里的覆盖守卫。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderLightHistoryDerives

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def coverage_m {Γ Δ : SortContext ℒ} (C W ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall W <| .forallE .set <| .imp
    (PowerlessFiniteSequencesSyntax.sequence_m (up (up ω)) (.bvar (.there .here)) (.bvar .here))
    (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up C)))

theorem coverage_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (C W ω : Term ℒ Γ Δ .set) :
    (coverage_m C W ω).satisfies η ↔ ∀ A, member_l 𝒩 A (W.eval η) → ∀ f,
      PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒩) (ω.eval η) A f →
        member_l 𝒩 f (C.eval η) := by
  simp only [coverage_m, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessFiniteSequencesSyntax.sequence_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def uniqueness_m {Γ Δ : SortContext ℒ}
    (C C' W ω F G P₀ α δ g g' : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (PowerlessMapBounded.formula_m F δ W) <|
    .imp (PowerlessMapBounded.formula_m G W W) <|
      .imp (coverage_m C W ω) <| .imp (coverage_m C' W ω) <|
        .imp (PowerlessRelativeHierarchySyntax.ordinal_m α) <|
          .imp (PowerlessCanonicalOrderLightHistory.formula_m C W ω F G P₀ α g) <|
            .imp (PowerlessCanonicalOrderLightHistory.formula_m C' W ω F G P₀ α g')
              (.equal g g')

private abbrev parameters_m : SortContext ℒ :=
  [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set]

/-- 自由槽依次为 g、g'、C、C'、W、ω、F、G、P₀、α、δ。 -/
def schema_m : Formula ℒ [] parameters_m :=
  let g : Term ℒ [] parameters_m .set := .fvar .here
  let g' := .fvar (.there .here)
  let C := .fvar (.there (.there .here))
  let C' := .fvar (.there (.there (.there .here)))
  let W := .fvar (.there (.there (.there (.there .here))))
  let ω := .fvar (.there (.there (.there (.there (.there .here)))))
  let F := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let G := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let P₀ := .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let α := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
  let δ := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
  uniqueness_m C C' W ω F G P₀ α δ g g'

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, uniqueness_m, Formula.satisfies,
    PowerlessMapBounded.formula_l, coverage_formula_l,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessCanonicalOrderLightHistory.formula_l, Term.eval]
  intro η hF hG hCoverage hCoverage' hα hg hg'
  exact PowerlessCanonicalOrderLightHistoryUnique.unique_l hℳ hF hG hCoverage hCoverage' hα hg hg'

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms coverage_formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderLightHistoryDerives
