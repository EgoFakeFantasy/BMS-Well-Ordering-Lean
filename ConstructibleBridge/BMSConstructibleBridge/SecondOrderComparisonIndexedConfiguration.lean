import BMSConstructibleBridge.SecondOrderComparisonNativeConfiguration

/-! # 规范历史所需的纯集合配置

忘去根表示、数码代表和枚举，只保留实际序数、层次与指标图。
这一有限合取有纯对象公式，可用于内部归纳、分离和历史证书；
由原配置投影取得它不需要任何新的集合存在或选择假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonIndexedConfiguration

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderObjectSyntax (member_m value_m map_m)
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def onto_m {Γ Δ : SortContext ℒ} (J I A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up A)) <|
    .existsE .set <| .conj (member_m (.bvar .here) (up₂ I))
      (value_m (up₂ J) (.bvar .here) (.bvar (.there .here)))

def composition_m {Γ Δ : SortContext ℒ} (J F T : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    .iff (value_m (up₂ T) (.bvar (.there .here)) (.bvar .here)) <|
      .existsE .set <| .conj (value_m (up (up₂ J)) (.bvar (.there (.there .here))) (.bvar .here))
        (value_m (up (up₂ F)) (.bvar .here) (.bvar (.there .here)))

def configuration_m {Γ Δ : SortContext ℒ} (ω B A F r I J T : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.ordinal_m A) <|
    .conj (map_m J I A) <| .conj (onto_m J I A) <|
      .conj (ThirdOrderTheory.subset_m I ω) <|
        .conj (PowerlessRelativeHierarchySyntax.history_m B A F r) <|
          .conj (map_m T I r) (composition_m J F T)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "v" => SecondOrderQuotient.mk_l hℳ

structure configuration_l (ω B A F r I J T : type_l hℳ) : Prop where
  ordinal : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) A
  indexMap : map_l (ℳ := 𝒱) J I A
  indexOnto : ∀ a, mem_l hℳ a A → ∃ i, mem_l hℳ i I ∧ value_l (ℳ := 𝒱) J i a
  indexSubset : subset_l (ℳ := 𝒱) I ω
  hierarchy : PowerlessRelativeHierarchySemantics.history_l hℳ B A F r
  layerMap : map_l (ℳ := 𝒱) T I r
  layerRead : ∀ i X, value_l (ℳ := 𝒱) T i X ↔ ∃ a, value_l (ℳ := 𝒱) J i a ∧ value_l (ℳ := 𝒱) F a X

theorem onto_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (J I A : Term ℒ Γ Δ .set) :
    (onto_m J I A).satisfies η ↔ ∀ a, mem_l hℳ a (A.eval η) →
      ∃ i, mem_l hℳ i (I.eval η) ∧ value_l (ℳ := 𝒱) (J.eval η) i a := by
  simp only [onto_m, Formula.satisfies, member_m, value_formula_l, up₂, up,
    Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

theorem composition_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (J F T : Term ℒ Γ Δ .set) :
    (composition_m J F T).satisfies η ↔ ∀ i X,
      value_l (ℳ := 𝒱) (T.eval η) i X ↔ ∃ a,
        value_l (ℳ := 𝒱) (J.eval η) i a ∧ value_l (ℳ := 𝒱) (F.eval η) a X := by
  simp only [composition_m, Formula.satisfies, value_formula_l, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem configuration_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (ω B A F r I J T : Term ℒ Γ Δ .set) :
    (configuration_m ω B A F r I J T).satisfies η ↔
      configuration_l (ω.eval η) (B.eval η) (A.eval η) (F.eval η) (r.eval η)
        (I.eval η) (J.eval η) (T.eval η) := by
  simp only [configuration_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    map_formula_l, onto_formula_l, subset_formula_l, PowerlessRelativeHierarchySemantics.history_formula_l K,
    composition_formula_l]
  exact ⟨fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩,
    fun h => ⟨h.ordinal, h.indexMap, h.indexOnto, h.indexSubset, h.hierarchy, h.layerMap, h.layerRead⟩⟩

theorem of_native_l {K : source_coding_l hℳ} {p : SecondOrderComparisonNativeRow.parameters_l ℳ}
    {A : SecondOrderGraph.code_l ℳ} {B F r : type_l hℳ} {Root Index Prec : SecondOrderModel.set_l ℳ}
    (h : SecondOrderComparisonNativeConfiguration.configuration_l K p A B F r Root Index Prec) :
    configuration_l K.omega B (v A) F r (v p.I) (v p.J) (v p.T) :=
  ⟨h.ordinal, h.indexMap, h.indexOnto, h.indexSubset, h.hierarchy, h.layerMap, h.layerRead⟩

#print axioms configuration_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonIndexedConfiguration
