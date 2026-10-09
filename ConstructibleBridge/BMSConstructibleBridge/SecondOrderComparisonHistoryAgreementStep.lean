import BMSConstructibleBridge.SecondOrderComparisonCanonicalSyntax
import BMSConstructibleBridge.SecondOrderComparisonIndexedConfiguration
import BMSConstructibleBridge.PowerlessRelativeHierarchyAgreement

/-! # 不同阶段编号与枚举下的规范比较：局部一致性步骤

通过实际序数值读取比较图，而不比较两边的编号或枚举坐标。共同层值由
既有层次唯一性取得；后继使用完整规范步骤唯一性，极限逐边搬运实际前驱。
本文件的前驱一致性将由后续纯公式内部归纳提供。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonHistoryAgreementStep

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderWellOrderCoherentUnion (edge_l graph_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def read_m {Γ Δ : SortContext ℒ} (J T G a X P : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (SecondOrderObjectSyntax.value_m (up J) (.bvar .here) (up a)) <|
    .conj (SecondOrderObjectSyntax.value_m (up T) (.bvar .here) (up X))
      (SecondOrderObjectSyntax.value_m (up G) (.bvar .here) (up P))

def read_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (J T G a X P : carrier_l 𝒩) : Prop :=
  ∃ i, value_l (ℳ := 𝒩) J i a ∧ value_l (ℳ := 𝒩) T i X ∧ value_l (ℳ := 𝒩) G i P

theorem read_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (J T G a X P : Term ℒ Γ Δ .set) :
    (read_m J T G a X P).satisfies η ↔
      read_l (J.eval η) (T.eval η) (G.eval η) (a.eval η) (X.eval η) (P.eval η) := by
  simp only [read_m, read_l, Formula.satisfies, value_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

variable {K : source_coding_l hℳ}
  {A A' B F F' r r' I I' J J' T T' G G' q q' t₁ t₂ t₃ Pair Valid P₀ : type_l hℳ}

private theorem level_l
    (h : SecondOrderComparisonIndexedConfiguration.configuration_l K.omega B A F r I J T)
    {a X P : type_l hℳ} (hRead : read_l (𝒩 := 𝒱) J T G a X P) :
    PowerlessRelativeHierarchySemantics.level_l hℳ B a X := by
  obtain ⟨i, hia, hiX, _⟩ := hRead
  obtain ⟨b, hib, hbX⟩ := (h.layerRead i X).mp hiX
  have hba := SecondOrderFunctionLaws.value_unique_l hℳ h.indexMap hib hia
  exact ⟨A, F, r, h.ordinal, (SecondOrderFunctionLaws.value_mem_l hℳ h.indexMap hia).2,
    h.hierarchy, hba ▸ hbX⟩

theorem layer_equal_l
    (h : SecondOrderComparisonIndexedConfiguration.configuration_l K.omega B A F r I J T)
    (h' : SecondOrderComparisonIndexedConfiguration.configuration_l K.omega B A' F' r' I' J' T')
    {a X P Y Q : type_l hℳ}
    (hRead : read_l (𝒩 := 𝒱) J T G a X P)
    (hRead' : read_l (𝒩 := 𝒱) J' T' G' a Y Q) : X = Y :=
  PowerlessRelativeHierarchyAgreement.level_unique_l hℳ (level_l h hRead) (level_l h' hRead')

private theorem edge_forward_l
    (h : SecondOrderComparisonIndexedConfiguration.configuration_l K.omega B A F r I J T)
    (h' : SecondOrderComparisonIndexedConfiguration.configuration_l K.omega B A' F' r' I' J' T')
    (hG' : map_l (ℳ := 𝒱) G' K.omega q') {a D D' : type_l hℳ} (ha' : mem_l hℳ a A')
    (hD : SecondOrderStageLayerFunction.predecessor_l a J D)
    (hD' : SecondOrderStageLayerFunction.predecessor_l a J' D')
    (hPast : ∀ b, mem_l hℳ b a → ∀ X P Y Q,
      read_l (𝒩 := 𝒱) J T G b X P →
      read_l (𝒩 := 𝒱) J' T' G' b Y Q → P = Q)
    {x y : type_l hℳ} (hxy : edge_l (ℳ₀ := 𝒱) D T G x y) :
    edge_l (ℳ₀ := 𝒱) D' T' G' x y := by
  obtain ⟨i, X, P, hi, hx, hy, hxy⟩ := hxy
  obtain ⟨b, hib, hb⟩ := (hD i).mp hi.1
  obtain ⟨j, hj, hjb⟩ := h'.indexOnto b (h'.ordinal.transitive a ha' b hb)
  obtain ⟨Y, ⟨_, hjY⟩, _⟩ := h'.layerMap.2 j hj
  obtain ⟨Q, ⟨_, hjQ⟩, _⟩ := hG'.2 j (h'.indexSubset j hj)
  have hRead : read_l (𝒩 := 𝒱) J T G b X P := ⟨i, hib, hi.2.1, hi.2.2⟩
  have hRead' : read_l (𝒩 := 𝒱) J' T' G' b Y Q := ⟨j, hjb, hjY, hjQ⟩
  have hXY := layer_equal_l h h' hRead hRead'
  have hPQ := hPast b hb X P Y Q hRead hRead'
  subst Y
  subst Q
  exact ⟨j, X, P, ⟨(hD' j).mpr ⟨b, hjb, hb⟩, hjY, hjQ⟩, hx, hy, hxy⟩

theorem limit_equal_l
    (h : SecondOrderComparisonIndexedConfiguration.configuration_l K.omega B A F r I J T)
    (h' : SecondOrderComparisonIndexedConfiguration.configuration_l K.omega B A' F' r' I' J' T')
    (hG : map_l (ℳ := 𝒱) G K.omega q) (hG' : map_l (ℳ := 𝒱) G' K.omega q')
    {a D D' P Q : type_l hℳ} (ha : mem_l hℳ a A) (ha' : mem_l hℳ a A')
    (hD : SecondOrderStageLayerFunction.predecessor_l a J D)
    (hD' : SecondOrderStageLayerFunction.predecessor_l a J' D')
    (hPast : ∀ b, mem_l hℳ b a → ∀ X P Y Q,
      read_l (𝒩 := 𝒱) J T G b X P →
      read_l (𝒩 := 𝒱) J' T' G' b Y Q → P = Q)
    (hP : graph_l (ℳ₀ := 𝒱) D T G P) (hQ : graph_l (ℳ₀ := 𝒱) D' T' G' Q) : P = Q := by
  apply SecondOrderQuotient.ext_l hℳ
  intro z
  change member_l 𝒱 z P ↔ member_l 𝒱 z Q
  rw [hP z, hQ z]
  apply exists_congr
  intro x
  apply exists_congr
  intro y
  apply and_congr _ Iff.rfl
  exact ⟨edge_forward_l h h' hG' ha' hD hD' hPast,
    edge_forward_l h' h hG ha hD' hD
      (fun b hb X P Y Q hRead hRead' => (hPast b hb Y Q X P hRead' hRead).symm)⟩

set_option maxHeartbeats 1000000 in
theorem step_l
    (h : SecondOrderComparisonIndexedConfiguration.configuration_l K.omega B A F r I J T)
    (h' : SecondOrderComparisonIndexedConfiguration.configuration_l K.omega B A' F' r' I' J' T')
    (hG : map_l (ℳ := 𝒱) G K.omega q) (hG' : map_l (ℳ := 𝒱) G' K.omega q')
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    {a X P Y Q : type_l hℳ} (ha : mem_l hℳ a A) (ha' : mem_l hℳ a A')
    (hRead : read_l (𝒩 := 𝒱) J T G a X P)
    (hRead' : read_l (𝒩 := 𝒱) J' T' G' a Y Q)
    (hPast : ∀ b, mem_l hℳ b a → ∀ X P Y Q,
      read_l (𝒩 := 𝒱) J T G b X P →
      read_l (𝒩 := 𝒱) J' T' G' b Y Q → P = Q)
    (hP : SecondOrderComparisonCanonicalSyntax.branch_l K.omega (zero_l K)
      t₁ t₂ t₃ Pair Valid J T G P₀ a X P)
    (hQ : SecondOrderComparisonCanonicalSyntax.branch_l K.omega (zero_l K)
      t₁ t₂ t₃ Pair Valid J' T' G' P₀ a Y Q) : P = Q := by
  have hXY := layer_equal_l h h' hRead hRead'
  subst Y
  have hα : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a := by
    apply SetTheory.Structure.IsOrdinal.mem h.ordinal
    exact ha
  rcases hP with ⟨hEmpty, hP⟩ | ⟨b, j, Y, R, hb, hjb, hjY, hjR, hStep⟩ | ⟨hLimit, D, hD, hGraph⟩
  · rcases hQ with ⟨_, hQ⟩ | ⟨b, _, _, _, hb, _⟩ | ⟨hLimit, _⟩
    · exact hP.trans hQ.symm
    · exact False.elim (hEmpty b (PowerlessRelativeHierarchyStep.successor_member_l hℳ hb))
    · obtain ⟨b, hb⟩ := hLimit.1
      exact False.elim (hEmpty b hb)
  · rcases hQ with ⟨hEmpty, _⟩ | ⟨c, k, Z, S, hc, hkc, hkZ, hkS, hStep'⟩ | ⟨hLimit, _⟩
    · exact False.elim (hEmpty b (PowerlessRelativeHierarchyStep.successor_member_l hℳ hb))
    · have hcb := PowerlessRelativeHierarchyStep.successor_unique_l hℳ hα hc hb
      subst c
      have hR : read_l (𝒩 := 𝒱) J T G b Y R := ⟨j, hjb, hjY, hjR⟩
      have hS : read_l (𝒩 := 𝒱) J' T' G' b Z S := ⟨k, hkc, hkZ, hkS⟩
      have hYZ := layer_equal_l h h' hR hS
      have hRS := hPast b (PowerlessRelativeHierarchyStep.successor_member_l hℳ hb) Y R Z S hR hS
      subst Z
      subst S
      rw [hCoding.one, hCoding.two, hCoding.three] at hStep
      rw [hCoding.one, hCoding.two, hCoding.three] at hStep'
      obtain ⟨V, hV, hValidRead⟩ := hCoding.valid
      exact SecondOrderCanonicalOrderUniform.unique_l K rfl rfl rfl rfl rfl
        hCoding.pairMap hCoding.pair hV hValidRead hStep hStep'
    · exact False.elim (PowerlessRelativeHierarchyStep.successor_not_limit_l hℳ hα hb hLimit)
  · rcases hQ with ⟨hEmpty, _⟩ | ⟨b, _, _, _, hb, _⟩ | ⟨_, D', hD', hGraph'⟩
    · obtain ⟨b, hb⟩ := hLimit.1
      exact False.elim (hEmpty b hb)
    · exact False.elim (PowerlessRelativeHierarchyStep.successor_not_limit_l hℳ hα hb hLimit)
    · exact limit_equal_l h h' hG hG' ha ha' hD hD' hPast hGraph hGraph'

#print axioms step_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonHistoryAgreementStep
