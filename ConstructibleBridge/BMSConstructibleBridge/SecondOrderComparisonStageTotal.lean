import BMSConstructibleBridge.SecondOrderComparisonStageSyntax

/-! # 原层次方程给出全部比较行的总唯一性

零／后继／极限分类来自实际层次历史；指标函数和层函数只用于读出已有值。
比较历史可以任意，因此这里不假定它已经良序或相容。编码包记录的每项
都是原模型已构造的图规格，没有增加 Collection 或 Type 层选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonStageTotal

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderComparisonStageSyntax (branch_l output_l)
open PowerlessRelativeHierarchySemantics (empty_l successor_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

/-- 固定编码包的真实规格，只收集 Prop 证据。 -/
structure coding_l (K : source_coding_l hℳ) (t₁ t₂ t₃ Pair Valid : type_l hℳ) : Prop where
  one : t₁ = PowerlessFormulaValidityReading.code_l K (SecondOrderEvaluationRule.numeral_l ℳ 1)
  two : t₂ = PowerlessFormulaValidityReading.code_l K (SecondOrderEvaluationRule.numeral_l ℳ 2)
  three : t₃ = PowerlessFormulaValidityReading.code_l K (SecondOrderEvaluationRule.numeral_l ℳ 3)
  pairMap : map_l (ℳ := 𝒱) Pair K.omega K.omega
  pair : PowerlessBMSQuotientPairingBounds.spec_l K Pair
  valid : ∃ V : SecondOrderModel.set_l ℳ, SecondOrderTriangularFormulaSyntax.spec_l V ∧
    ∀ c N, value_l (ℳ := 𝒱) Valid c N ↔ PowerlessRelationalCodeValidity.valid_l K V c N

theorem encoded_unique_l (K : source_coding_l hℳ) {f P X Y : type_l hℳ}
    (hX : SecondOrderComparisonEncodeSyntax.encoded_l (𝒩 := 𝒱) K.omega (zero_l K) X f P)
    (hY : SecondOrderComparisonEncodeSyntax.encoded_l (𝒩 := 𝒱) K.omega (zero_l K) Y f P) : X = Y := by
  let X' : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega := ⟨X, SecondOrderComparisonEncodeSyntax.guard_l hX⟩
  let Y' : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega := ⟨Y, SecondOrderComparisonEncodeSyntax.guard_l hY⟩
  obtain ⟨R, hR⟩ := PowerlessBMSQuotientReals.trace_exists_l K X'
  obtain ⟨S, hS⟩ := PowerlessBMSQuotientReals.trace_exists_l K Y'
  have hSR := SecondOrderComparisonReal.unique_l K
    ((SecondOrderComparisonEncodeSyntax.reading_l K Y' S hS f P).mp hY)
    ((SecondOrderComparisonEncodeSyntax.reading_l K X' R hR f P).mp hX)
  exact congrArg Subtype.val (PowerlessBMSQuotientReals.representative_unique_l K hR (hSR ▸ hS))

theorem encoded_exists_unique_l (K : source_coding_l hℳ) (f P : type_l hℳ) :
    ∃! W : type_l hℳ, SecondOrderComparisonEncodeSyntax.encoded_l (𝒩 := 𝒱) K.omega (zero_l K) W f P := by
  obtain ⟨R, hR, _⟩ := SecondOrderComparisonReal.exists_unique_l K f P
  obtain ⟨W, hW⟩ := representative_exists_l K R
  exact ⟨W.val, (SecondOrderComparisonEncodeSyntax.reading_l K W R hW f P).mpr hR,
    fun X hX => encoded_unique_l K hX ((SecondOrderComparisonEncodeSyntax.reading_l K W R hW f P).mpr hR)⟩

private theorem limit_unique_l (K : source_coding_l hℳ) {D T G f X Y : type_l hℳ}
    (hX : SecondOrderComparisonLimitSyntax.output_l (𝒩 := 𝒱) K.omega (zero_l K) D T G f X)
    (hY : SecondOrderComparisonLimitSyntax.output_l (𝒩 := 𝒱) K.omega (zero_l K) D T G f Y) : X = Y := by
  obtain ⟨P, hP, hX⟩ := hX
  obtain ⟨Q, hQ, hY⟩ := hY
  have hQP := SecondOrderWellOrderCoherentUnion.graph_unique_l hQ hP
  subst Q
  exact encoded_unique_l K hX hY

/-- 同一实际阶段的分支互斥，且每个分支的输出唯一。 -/
theorem branch_unique_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid I A J T G r q f P₀ a C X Y : type_l hℳ}
    (hCoding : coding_l K t₁ t₂ t₃ Pair Valid)
    (ha : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a)
    (hJ : map_l (ℳ := 𝒱) J I A) (hInject : injective_l (ℳ := 𝒱) J)
    (hI : subset_l (ℳ := 𝒱) I K.omega) (hT : map_l (ℳ := 𝒱) T I r)
    (hG : map_l (ℳ := 𝒱) G K.omega q)
    (hX : branch_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid J T G P₀ f a C X)
    (hY : branch_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid J T G P₀ f a C Y) : X = Y := by
  rcases hX with ⟨hEmpty, hX⟩ | ⟨b, j, U, hb, hjb, hjU, hX⟩ | ⟨hLimit, D, hD, hX⟩
  · rcases hY with ⟨_, hY⟩ | ⟨b, _, _, hb, _, _, _⟩ | ⟨hLimit, _⟩
    · exact encoded_unique_l K hX hY
    · exact False.elim (hEmpty b (PowerlessRelativeHierarchyStep.successor_member_l hℳ hb))
    · obtain ⟨b, hb⟩ := hLimit.1
      exact False.elim (hEmpty b hb)
  · rcases hY with ⟨hEmpty, _⟩ | ⟨c, k, V, hc, hkc, hkV, hY⟩ | ⟨hLimit, _⟩
    · exact False.elim (hEmpty b (PowerlessRelativeHierarchyStep.successor_member_l hℳ hb))
    · have hbc := PowerlessRelativeHierarchyStep.successor_unique_l hℳ ha hb hc
      subst c
      have hjk := hInject j k b hjb hkc
      subst k
      have hUV := SecondOrderFunctionLaws.value_unique_l hℳ hT hjU hkV
      subst V
      obtain ⟨V, hV, hValid⟩ := hCoding.valid
      obtain ⟨W, _, hOnly⟩ := SecondOrderComparisonSuccessorSyntax.exists_unique_l
        (A := U) (G := G) (i := j) (D := C) (f := f) K hCoding.one hCoding.two hCoding.three
        hCoding.pairMap hCoding.pair hV hValid hG (hI j (SecondOrderFunctionLaws.value_mem_l hℳ hJ hjb).1)
      exact (hOnly X hX).trans (hOnly Y hY).symm
    · exact False.elim (PowerlessRelativeHierarchyStep.successor_not_limit_l hℳ ha hb hLimit)
  · rcases hY with ⟨hEmpty, _⟩ | ⟨b, _, _, hb, _, _, _⟩ | ⟨_, E, hE, hY⟩
    · obtain ⟨b, hb⟩ := hLimit.1
      exact False.elim (hEmpty b hb)
    · exact False.elim (PowerlessRelativeHierarchyStep.successor_not_limit_l hℳ ha hb hLimit)
    · have hED : E = D := SecondOrderQuotient.ext_l hℳ E D (fun i => (hE i).trans (hD i).symm)
      subst E
      exact limit_unique_l K hX hY

/-- 实际层次历史直接提供每个合法指标的输出存在性。 -/
theorem exists_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid I A J T G B F r q f P₀ : type_l hℳ}
    (hCoding : coding_l K t₁ t₂ t₃ Pair Valid)
    (hA : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) A)
    (hJ : map_l (ℳ := 𝒱) J I A)
    (hOnto : ∀ a, mem_l hℳ a A → ∃ i, mem_l hℳ i I ∧ value_l (ℳ := 𝒱) J i a)
    (hI : subset_l (ℳ := 𝒱) I K.omega) (hG : map_l (ℳ := 𝒱) G K.omega q)
    (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B A F r)
    (hT : ∀ i X, value_l (ℳ := 𝒱) T i X ↔ ∃ a, value_l (ℳ := 𝒱) J i a ∧ value_l (ℳ := 𝒱) F a X)
    (i : type_l hℳ) : ∃ W, output_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid I J T G P₀ f i W := by
  classical
  by_cases hi : mem_l hℳ i I
  · obtain ⟨a, ⟨ha, hia⟩, _⟩ := hJ.2 i hi
    obtain ⟨C, ⟨_, haC⟩, _⟩ := hF.1.2 a ha
    have hiC := (hT i C).mpr ⟨a, hia, haC⟩
    rcases hF.2 a C ⟨ha, haC⟩ with ⟨hEmpty, _⟩ | ⟨b, U, hb, hbU, _⟩ | ⟨hLimit, hUnion⟩
    · obtain ⟨W, hW, _⟩ := encoded_exists_unique_l K f P₀
      exact ⟨W, Or.inl ⟨hi, a, C, hia, hiC, Or.inl ⟨hEmpty, hW⟩⟩⟩
    · have hbA := hA.transitive a ha b (PowerlessRelativeHierarchyStep.successor_member_l hℳ hb)
      obtain ⟨j, hj, hjb⟩ := hOnto b hbA
      have hjU := (hT j U).mpr ⟨b, hjb, hbU⟩
      obtain ⟨V, hV, hValid⟩ := hCoding.valid
      obtain ⟨W, hW, _⟩ := SecondOrderComparisonSuccessorSyntax.exists_unique_l
        (A := U) (G := G) (i := j) (D := C) (f := f) K hCoding.one hCoding.two hCoding.three
        hCoding.pairMap hCoding.pair hV hValid hG (hI j hj)
      exact ⟨W, Or.inl ⟨hi, a, C, hia, hiC, Or.inr (Or.inl ⟨b, j, U, hb, hjb, hjU, hW⟩)⟩⟩
    · obtain ⟨D, _, hD⟩ := SecondOrderStageLayerFunction.predecessor_exists_l (δ := a) hJ
      have haA : subset_l (ℳ := 𝒱) a A := by
        intro b hb
        exact hA.transitive a ha b hb
      have hCover := SecondOrderStageLayerFunction.limit_cover_l hJ hOnto haA hD hT hUnion
      obtain ⟨W, hW, _⟩ := SecondOrderComparisonLimitSyntax.exists_unique_l (G := G) (f := f) K hCover
      exact ⟨W, Or.inl ⟨hi, a, C, hia, hiC, Or.inr (Or.inr ⟨hLimit, D, hD, hW⟩)⟩⟩
  · exact ⟨zero_l K, Or.inr ⟨hi, rfl⟩⟩

/-- 原始任意候选历史下的全部指标总唯一性。 -/
theorem exists_unique_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid I A J T G B F r q f P₀ : type_l hℳ}
    (hCoding : coding_l K t₁ t₂ t₃ Pair Valid)
    (hA : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) A)
    (hJ : map_l (ℳ := 𝒱) J I A) (hInject : injective_l (ℳ := 𝒱) J)
    (hOnto : ∀ a, mem_l hℳ a A → ∃ i, mem_l hℳ i I ∧ value_l (ℳ := 𝒱) J i a)
    (hI : subset_l (ℳ := 𝒱) I K.omega) (hTMap : map_l (ℳ := 𝒱) T I r)
    (hG : map_l (ℳ := 𝒱) G K.omega q)
    (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B A F r)
    (hT : ∀ i X, value_l (ℳ := 𝒱) T i X ↔ ∃ a, value_l (ℳ := 𝒱) J i a ∧ value_l (ℳ := 𝒱) F a X)
    (i : type_l hℳ) : ∃! W, output_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid I J T G P₀ f i W := by
  obtain ⟨W, hW⟩ := exists_l K hCoding hA hJ hOnto hI hG hF hT i
  refine ⟨W, hW, ?_⟩
  intro X hX
  rcases hX with ⟨hi, a, C, hia, hiC, hX⟩ | ⟨hi, rfl⟩
  · rcases hW with ⟨_, b, D, hib, hiD, hW⟩ | ⟨hn, _⟩
    · have hab := SecondOrderFunctionLaws.value_unique_l hℳ hJ hia hib
      subst b
      have hCD := SecondOrderFunctionLaws.value_unique_l hℳ hTMap hiC hiD
      subst D
      have ha : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a := by
        apply SetTheory.Structure.IsOrdinal.mem hA
        exact (SecondOrderFunctionLaws.value_mem_l hℳ hJ hia).2
      exact branch_unique_l K hCoding ha hJ hInject hI hTMap hG hX hW
    · exact False.elim (hn hi)
  · rcases hW with ⟨hm, _⟩ | ⟨_, hW⟩
    · exact False.elim (hi hm)
    · exact hW.symm

theorem guard_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid I J T G P₀ f i W : type_l hℳ}
    (h : output_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid I J T G P₀ f i W) :
    subset_l (ℳ := 𝒱) W K.omega := by
  rcases h with ⟨_, a, C, _, _, h⟩ | ⟨_, rfl⟩
  · rcases h with ⟨_, h⟩ | ⟨b, j, U, _, _, _, h⟩ | ⟨_, D, _, P, _, h⟩
    · exact SecondOrderComparisonEncodeSyntax.guard_l h
    · exact SecondOrderComparisonSuccessorSyntax.guard_l K h
    · exact SecondOrderComparisonEncodeSyntax.guard_l h
  · intro x hx
    exact False.elim (PowerlessBMSQuotientSuccessor.zero_l K x hx)

#print axioms exists_unique_l
#print axioms guard_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonStageTotal
