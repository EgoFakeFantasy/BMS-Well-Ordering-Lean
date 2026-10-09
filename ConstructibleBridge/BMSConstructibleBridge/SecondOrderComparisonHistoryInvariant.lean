import BMSConstructibleBridge.SecondOrderComparisonBranchInvariant
import BMSConstructibleBridge.SecondOrderComparisonHistoryRealization

/-! # 唯一实际递归历史的全部阶段良序与初段不变量

原二阶递归实数先统一为同一解码 G；在原商模型内，用实际不变量公式
分离和正则性归纳。每行的三分支归纳步直接消费原正文，不将归纳步
或整段历史相容性留作前提。本结论仍是最终 BMS 对象推导的中间成果。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonHistoryInvariant

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderComparisonNativeRow (parameters_l environment_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "v" => SecondOrderQuotient.mk_l hℳ
private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

set_option maxHeartbeats 1000000 in
theorem realize_l (K : source_coding_l hℳ) (p : parameters_l ℳ)
    {A : SecondOrderGraph.code_l ℳ} {B F r : type_l hℳ}
    {Root Index Prec S : SecondOrderModel.set_l ℳ}
    (hConfig : SecondOrderComparisonNativeConfiguration.configuration_l K p A B F r Root Index Prec)
    (hSupport : SecondOrderComparisonStaticSupport.support_l K B r (v p.C) (v p.f) (v p.P₀))
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hRows : ∀ n W, SecondOrderSections.spec_l S n W →
      SecondOrderComparisonNativeRow.formula_m.satisfies
        ((((environment_l K p).pushFree S).pushFree n).pushFree W)) :
    ∃ E : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega, ∃ q G,
      setRel_l K E S ∧
      SecondOrderComparisonHistoryDerives.history_l (𝒩 := 𝒱)
        K.omega (zero_l K) E.val (v p.f) (v p.C) q G ∧
      (∀ a, mem_l hℳ a (v A) →
        SecondOrderComparisonInvariant.at_l (𝒩 := 𝒱) (v p.I) (v p.J) (v p.T) G a) ∧
      SecondOrderComparisonCanonicalSyntax.history_l K.omega (zero_l K)
        (v p.t₁) (v p.t₂) (v p.t₃) (v p.Pair) (v p.Valid) (v p.I) (v p.J) (v p.T) G (v p.P₀) (v A) := by
  obtain ⟨E, q, G, hE, hG, hOutputs⟩ := SecondOrderComparisonHistoryRealization.exists_l
    K p hConfig.omega hConfig.zero S hRows
  have hStep (a : type_l hℳ) (ha : mem_l hℳ a (v A))
      (hIH : ∀ b, mem_l hℳ b a →
        SecondOrderComparisonInvariant.at_l (𝒩 := 𝒱) (v p.I) (v p.J) (v p.T) G b) :
      SecondOrderComparisonInvariant.at_l (𝒩 := 𝒱) (v p.I) (v p.J) (v p.T) G a ∧
      SecondOrderComparisonCanonicalSyntax.at_l K.omega (zero_l K)
        (v p.t₁) (v p.t₂) (v p.t₃) (v p.Pair) (v p.Valid) (v p.I) (v p.J) (v p.T) G (v p.P₀) a := by
    have hRow i X Q (hi : SecondOrderWellOrderCoherentUnion.stage_l (ℳ₀ := 𝒱) (v p.I) (v p.T) G i X Q ∧
        value_l (ℳ := 𝒱) (v p.J) i a) :
        wellOrder_l (ℳ := 𝒱) X Q ∧ (∀ j Y R,
          SecondOrderWellOrderCoherentUnion.stage_l (ℳ₀ := 𝒱) (v p.I) (v p.T) G j Y R →
          (∃ b, value_l (ℳ := 𝒱) (v p.J) j b ∧ mem_l hℳ b a) →
          SecondOrderWellOrderCoherentUnion.extension_l (ℳ₀ := 𝒱) Y R X Q) ∧
        SecondOrderComparisonCanonicalSyntax.branch_l K.omega (zero_l K)
          (v p.t₁) (v p.t₂) (v p.t₃) (v p.Pair) (v p.Valid) (v p.J) (v p.T) G (v p.P₀) a X Q := by
      obtain ⟨n, _, hiCode, _⟩ := (hConfig.indexRead i a).mp hi.2
      subst i
      obtain ⟨W, hW, hQ⟩ := (SecondOrderComparisonHistoryStageLocal.decoded_read_l
        K E S hE hG n Q).mp hi.1.2.2
      obtain ⟨U, hU, hOutput⟩ := hOutputs n W hW
      rcases hOutput with ⟨_, a', X', hna', hnX', hBranch⟩ | ⟨hnI, _⟩
      · have hEqA := SecondOrderFunctionLaws.value_unique_l hℳ hConfig.indexMap hna' hi.2
        have hEqX := SecondOrderFunctionLaws.value_unique_l hℳ hConfig.layerMap hnX' hi.1.2.1
        rw [hEqA, hEqX] at hBranch
        exact SecondOrderComparisonBranchInvariant.row_l K p hConfig hSupport hBase hG.1 ha hi.1 hi.2
          hIH U W hU hBranch hQ
      · exact False.elim (hnI hi.1.1)
    exact ⟨fun i X Q hi => ⟨(hRow i X Q hi).1,
      fun j Y R hj => (hRow i X Q hi).2.1 j Y R hj.1 hj.2⟩,
      fun i X Q hi => (hRow i X Q hi).2.2⟩
  have hInvariant := SecondOrderComparisonInvariant.induction_l (hℳ := hℳ)
    (fun a ha b hb => hConfig.ordinal.transitive a ha b hb) (fun a ha ih => (hStep a ha ih).1)
  exact ⟨E, q, G, hE, hG, hInvariant,
    fun a ha => (hStep a ha (fun b hb => hInvariant b (hConfig.ordinal.transitive a ha b hb))).2⟩

/-- 配置中的实际内部递归填满行方程，不添加未来历史守卫。 -/
theorem exists_l (K : source_coding_l hℳ) (p : parameters_l ℳ)
    {A : SecondOrderGraph.code_l ℳ} {B F r : type_l hℳ}
    {Root Index Prec : SecondOrderModel.set_l ℳ}
    (hConfig : SecondOrderComparisonNativeConfiguration.configuration_l K p A B F r Root Index Prec)
    (hSupport : SecondOrderComparisonStaticSupport.support_l K B r (v p.C) (v p.f) (v p.P₀))
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    ∃ S : SecondOrderModel.set_l ℳ, ∃ E : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega, ∃ q G N,
      SecondOrderComparisonNativeRecursion.relation_l K p S S ∧ setRel_l K E S ∧
      SecondOrderComparisonHistoryDerives.history_l (𝒩 := 𝒱)
        K.omega (zero_l K) E.val (v p.f) (v p.C) q G ∧
      (∀ a, mem_l hℳ a (v A) →
        SecondOrderComparisonInvariant.at_l (𝒩 := 𝒱) (v p.I) (v p.J) (v p.T) G a) ∧
      wellOrder_l (ℳ := 𝒱) (v p.I) N ∧
      (∀ i X P, SecondOrderWellOrderCoherentUnion.stage_l (ℳ₀ := 𝒱) (v p.I) (v p.T) G i X P →
        wellOrder_l (ℳ := 𝒱) X P) ∧
      SecondOrderWellOrderCoherentUnion.coherent_l (ℳ₀ := 𝒱) (v p.I) N (v p.T) G ∧
      SecondOrderComparisonCanonicalSyntax.history_l K.omega (zero_l K)
        (v p.t₁) (v p.t₂) (v p.t₃) (v p.Pair) (v p.Valid) (v p.I) (v p.J) (v p.T) G (v p.P₀) (v A) := by
  obtain ⟨S, ⟨hRecursion, hRows⟩, _⟩ := SecondOrderComparisonNativeConfiguration.history_exists_l K p hConfig
  obtain ⟨E, q, G, hE, hG, hInvariant, hCanonical⟩ := realize_l K p hConfig hSupport hBase
    (fun n W hW => (hRows n W).mp hW)
  obtain ⟨N, hN, hNRead⟩ := SecondOrderStageIndexOrder.exists_l
    (hℳ := hℳ) hConfig.ordinal hConfig.indexMap hConfig.indexInjective
  refine ⟨S, E, q, G, N, hRecursion, hE, hG, hInvariant, hN, ?_, ?_, hCanonical⟩
  · intro i X P hi
    obtain ⟨a, ⟨ha, hia⟩, _⟩ := hConfig.indexMap.2 i hi.1
    exact (hInvariant a ha i X P ⟨hi, hia⟩).1
  · intro i j X P Y Q hi hj hij
    obtain ⟨a, b, hia, hjb, hab⟩ := (hNRead i j hi.1 hj.1).mp hij
    have hb := (SecondOrderFunctionLaws.value_mem_l hℳ hConfig.indexMap hjb).2
    exact (hInvariant b hb j Y Q ⟨hj, hjb⟩).2 i X P ⟨hi, a, hia, hab⟩

#print axioms realize_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonHistoryInvariant
