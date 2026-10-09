import BMSConstructibleBridge.SecondOrderBoundedCanonicalWitness
import BMSConstructibleBridge.PowerlessBMSQuotientSubsetFunction

/-! # 无共同层界的规范实数见证族

所有输出只需是同一 ω 的子集，不要求属于同一个相对层。先按规范类序
最小化实际请求，再复用子集有界值域和函数图构造；统一成员关系由原
二阶理解直接产生。所得对象目前只保证在环境商中，未证明属于相对类。
因此这不是构造子域的完整选择模式或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalRealWitness

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderCanonicalClassMinimum (minimum_l)
open SecondOrderCanonicalLevelDerives (guard_l)
open SecondOrderCanonicalWitnessSyntax (output_m output_formula_l support_env_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

variable (K : source_coding_l hℳ) {t₁ t₂ t₃ Pair Valid B P₀ : type_l hℳ}
  (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
  (hGuard : guard_l B P₀)

include hCoding hGuard in
/-- 输出的子集界取 ω，而非某个尚未构造的共同层。 -/
theorem range_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ)
    (hSome : ∀ x, mem_l hℳ x K.omega → ∃ y,
      PowerlessRelativeClassCorrespondence.member_l hℳ B y ∧
        φ.satisfies ((η.pushFree x).pushFree y))
    (hReal : ∀ x y, mem_l hℳ x K.omega → φ.satisfies ((η.pushFree x).pushFree y) →
      ∀ z, mem_l hℳ z y → mem_l hℳ z K.omega) :
    ∃ b g : type_l hℳ,
      (∀ y, mem_l hℳ y b ↔ ∃ x, mem_l hℳ x K.omega ∧
        minimum_l φ (η.pushFree x) K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ y) ∧
      map_l (ℳ := 𝒱) g K.omega b ∧ ∀ x y, value_l (ℳ := 𝒱) g x y ↔
        mem_l hℳ x K.omega ∧
          minimum_l φ (η.pushFree x) K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ y := by
  let ξ := support_env_l η K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀
  have hRead x y := output_formula_l K φ η K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ x y
  obtain ⟨b, g, hb, hg, hValue⟩ := PowerlessBMSQuotientSubsetFunction.exists_l K
    (output_m φ) ξ K.omega
    (fun n => by
      obtain ⟨y, hy, _⟩ := SecondOrderCanonicalClassMinimum.exists_unique_l K hCoding hGuard
        φ (η.pushFree (numberCode_l K n).val) (hSome _ (numberCode_l K n).property)
      exact ⟨y, (hRead _ y).mpr hy⟩)
    (fun n y z hy hz => SecondOrderBoundedCanonicalWitness.unique_l K hCoding hGuard φ η
      ((hRead _ y).mp hy) ((hRead _ z).mp hz))
    (fun n y hy => hReal (numberCode_l K n).val y (numberCode_l K n).property
      ((hRead _ y).mp hy).2.1)
  refine ⟨b, g, ?_, hg, fun x y => (hValue x y).trans (and_congr Iff.rfl (hRead x y))⟩
  intro y
  refine (hb y).trans ?_
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨(numberCode_l K n).val, (numberCode_l K n).property, (hRead _ y).mp hn⟩
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x, hx⟩
    have hn' : (numberCode_l K n).val = x := congrArg Subtype.val hn
    exact ⟨n, (hRead _ y).mpr (hn'.symm ▸ hxy)⟩

include hCoding hGuard in
/-- 一张原模型实数读取所有内部数索引的规范见证，不抽取 Type 选择函数。 -/
theorem real_family_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ)
    (hSome : ∀ x, mem_l hℳ x K.omega → ∃ y,
      PowerlessRelativeClassCorrespondence.member_l hℳ B y ∧
        φ.satisfies ((η.pushFree x).pushFree y))
    (hReal : ∀ x y, mem_l hℳ x K.omega → φ.satisfies ((η.pushFree x).pushFree y) →
      ∀ z, mem_l hℳ z y → mem_l hℳ z K.omega) :
    ∃ F : SecondOrderModel.set_l ℳ, ∀ n, ∃! y : type_l hℳ,
      minimum_l φ (η.pushFree (numberCode_l K n).val)
        K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ y ∧
      (∀ z, mem_l hℳ z y → mem_l hℳ z K.omega) ∧ ∀ m,
      SecondOrderPairing.relation_l F n m ↔ mem_l hℳ (numberCode_l K m).val y := by
  let ξ := support_env_l η K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀
  let ψ := PowerlessBMSQuotientSubsetImage.membership_m (output_m φ)
  obtain ⟨F, hF⟩ := SecondOrderGraphFormulaRelation.exists_l hℳ ψ ξ K.less K.less
  have hRead n m : SecondOrderPairing.relation_l F n m ↔ ∃ y,
      minimum_l φ (η.pushFree (numberCode_l K n).val)
        K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ y ∧
        mem_l hℳ (numberCode_l K m).val y := by
    refine (hF n m (SecondOrderNaturalGraph.wf_l hℳ K.less K.less_spec n)
      (SecondOrderNaturalGraph.wf_l hℳ K.less K.less_spec m)).trans ?_
    refine (PowerlessBMSQuotientSubsetImage.membership_formula_l (output_m φ) ξ _ _).trans ?_
    exact exists_congr (fun y => and_congr
      (output_formula_l K φ η K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ _ y) Iff.rfl)
  refine ⟨F, fun n => ?_⟩
  obtain ⟨y, hy, hUnique⟩ := SecondOrderCanonicalClassMinimum.exists_unique_l K hCoding hGuard
    φ (η.pushFree (numberCode_l K n).val) (hSome _ (numberCode_l K n).property)
  refine ⟨y, ⟨hy, hReal (numberCode_l K n).val y (numberCode_l K n).property hy.2.1,
    fun m => (hRead n m).trans ?_⟩, fun z hz => hUnique z hz.1⟩
  constructor
  · rintro ⟨z, hz, hzm⟩
    exact (hUnique z hz) ▸ hzm
  · intro hm
    exact ⟨y, hy, hm⟩

#print axioms range_l
#print axioms real_family_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalRealWitness
