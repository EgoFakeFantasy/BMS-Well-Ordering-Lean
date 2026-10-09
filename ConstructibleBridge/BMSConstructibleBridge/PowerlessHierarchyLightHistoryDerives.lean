import BMSConstructibleBridge.PowerlessHierarchyLightHistoryUnique
import BMSConstructibleBridge.PowerlessMemberDefDerives

/-! # 轻量前史有界化及图唯一性的原 Z₂ 推导

对象语言为纯隶属 ℒ，经既有 GraphTranslation 回到原 num/set 语言；
背景仍为 SecondOrderArithmetic.theory_m，正式出口为原 Derives。
read_m 对全部 raw 参数读取原 global_m，不把 Def 换成另一种关系。

陪域 C⊆W 时，已有原前史与纯 Δ₀ 检查器等价；两张同域轻量前史
实际相等，允许不同陪域。这里没有存在性结论，不假定图属于 Class，
不添加 Collection、模型外部良基或 Type 层选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def read_m {Γ Δ : SortContext ℒ} (W D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .iff
    (SecondOrderObjectSyntax.value_m (up (up D)) (.bvar (.there .here)) (.bvar .here))
    (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up (up W)))
      (PowerlessMemberDefSyntax.global_m (.bvar (.there .here)) (.bvar .here)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem read_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (W D : Term ℒ Γ Δ .set) :
    (read_m W D).satisfies η ↔
      ∀ A H : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) (D.eval η) A H ↔
          SecondOrderQuotient.mem_l hℳ A (W.eval η) ∧ SecondOrderMemberDef.spec_l hℳ A H := by
  simp only [read_m, Formula.satisfies, value_formula_l,
    PowerlessMemberDefDerives.formula_l K, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 自由槽依次为 f、C、α、D、W、B。 -/
def equivalence_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
  let f : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar .here
  let C := .fvar (.there .here)
  let α := .fvar (.there (.there .here))
  let D := .fvar (.there (.there (.there .here)))
  let W := .fvar (.there (.there (.there (.there .here))))
  let B := .fvar (.there (.there (.there (.there (.there .here)))))
  .imp (read_m W D) <| .imp (ThirdOrderTheory.subset_m C W) <| .iff
    (PowerlessHierarchyLightHistory.formula_m B D α C f)
    (PowerlessRelativeHierarchySyntax.history_m B α f C)

def equivalence_sentence_m : Sentence ℒ := Metatheory.Formula.forall_close equivalence_m

theorem equivalence_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    equivalence_sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [equivalence_m, Formula.satisfies, read_formula_l K,
    subset_formula_l, PowerlessHierarchyLightHistory.reading_formula_l hℳ,
    PowerlessRelativeHierarchySemantics.history_formula_l K, Term.eval]
  intro η hRead hCW
  exact PowerlessHierarchyLightHistoryUnique.iff_original_l hℳ hRead hCW

theorem equivalence_derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m equivalence_sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => equivalence_models_l hℳ)

/-- 自由槽依次为 f、g、R、C、α、D、W、B。 -/
def uniqueness_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
  let f : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let g := .fvar (.there .here)
  let R := .fvar (.there (.there .here))
  let C := .fvar (.there (.there (.there .here)))
  let α := .fvar (.there (.there (.there (.there .here))))
  let D := .fvar (.there (.there (.there (.there (.there .here)))))
  let W := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let B := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  .imp (read_m W D) <| .imp (PowerlessRelativeHierarchySyntax.ordinal_m α) <|
    .imp (PowerlessHierarchyLightHistory.formula_m B D α R f) <|
      .imp (PowerlessHierarchyLightHistory.formula_m B D α C g) (.equal f g)

def uniqueness_sentence_m : Sentence ℒ := Metatheory.Formula.forall_close uniqueness_m

theorem uniqueness_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    uniqueness_sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [uniqueness_m, Formula.satisfies, read_formula_l K,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessHierarchyLightHistory.reading_formula_l hℳ, Term.eval]
  intro η hRead hα hf hg
  exact PowerlessHierarchyLightHistoryUnique.unique_l hℳ hRead hα hf hg

theorem uniqueness_derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m uniqueness_sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => uniqueness_models_l hℳ)

#print axioms read_formula_l
#print axioms equivalence_derives_m
#print axioms uniqueness_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryDerives
