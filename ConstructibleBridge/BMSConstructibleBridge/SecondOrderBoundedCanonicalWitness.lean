import BMSConstructibleBridge.SecondOrderCanonicalWitnessSyntax
import BMSConstructibleBridge.SecondOrderFunctionProperties

/-! # 已有共同层界中的唯一规范见证图

先证明全类最小见证仍在任何已有见证所在层，再用原二阶理解收集
两集合之间的实际可定义图。没有收集无界输出，也没有 Type 层选择。
更换可用层界不改变函数图；共同界存在性仍是独立前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderBoundedCanonicalWitness

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderCanonicalClassMinimum (minimum_l)
open SecondOrderCanonicalLevelSyntax (level_l)
open SecondOrderCanonicalLevelDerives (guard_l)

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
/-- 最小见证不越过任意已有见证的实际层界。 -/
theorem bounded_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {a X P x y : type_l hℳ}
    (hP : level_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ a X P)
    (hSome : ∃ z, mem_l hℳ z X ∧ φ.satisfies ((η.pushFree x).pushFree z))
    (hy : minimum_l φ (η.pushFree x) K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ y) :
    mem_l hℳ y X := by
  obtain ⟨z, hz, hφz⟩ := hSome
  have hzClass : PowerlessRelativeClassCorrespondence.member_l hℳ B z :=
    ⟨a, X, SecondOrderCanonicalLevel.hierarchy_l hP, hz⟩
  have hBase b hb c hc := hGuard.2.1 b c hb hc
  rcases SecondOrderCanonicalClassOrder.compare_l K hCoding
    hGuard.1 hBase hGuard.2.2.1 hGuard.2.2.2 hy.1 hzClass with hyz | hEq | hzy
  · exact SecondOrderCanonicalClassOrder.initial_l K hCoding hP hz hyz
  · exact hEq.symm ▸ hz
  · exact False.elim (hy.2.2 z hφz hzy)

include hCoding hGuard in
theorem unique_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {x y z : type_l hℳ}
    (hy : minimum_l φ (η.pushFree x) K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ y)
    (hz : minimum_l φ (η.pushFree x) K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ z) : y = z := by
  have hBase b hb c hc := hGuard.2.1 b c hb hc
  rcases SecondOrderCanonicalClassOrder.compare_l K hCoding
    hGuard.1 hBase hGuard.2.2.1 hGuard.2.2.2 hy.1 hz.1 with hyz | hEq | hzy
  · exact False.elim (hz.2.2 y hy.2.1 hyz)
  · exact hEq
  · exact False.elim (hy.2.2 z hz.2.1 hzy)

def selection_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ A X F : type_l hℳ) : Prop :=
  map_l (ℳ := 𝒱) F A X ∧ ∀ x y, value_l (ℳ := 𝒱) F x y ↔ mem_l hℳ x A ∧
    minimum_l φ (η.pushFree x) ω e t₁ t₂ t₃ Pair Valid B P₀ y

include hCoding hGuard in
/-- 所有实际请求已有同一层内见证时，产生唯一的内部函数对象。 -/
theorem exists_unique_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {a X P A : type_l hℳ}
    (hP : level_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ a X P)
    (hRequests : ∀ x, mem_l hℳ x A →
      ∃ y, mem_l hℳ y X ∧ φ.satisfies ((η.pushFree x).pushFree y)) :
    ∃! F, selection_l φ η K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ A X F := by
  obtain ⟨F, hF⟩ := SecondOrderDefinableRelationImage.exists_l hℳ
    (SecondOrderCanonicalWitnessSyntax.relation_m φ)
    (SecondOrderCanonicalWitnessSyntax.support_env_l η K.omega (zero_l K)
      t₁ t₂ t₃ Pair Valid B P₀) A X
  have hRead x y := SecondOrderCanonicalWitnessSyntax.relation_formula_l K φ η
    K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ x y
  have hValue x y : value_l (ℳ := 𝒱) F x y ↔ mem_l hℳ x A ∧
      minimum_l φ (η.pushFree x) K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ y := by
    constructor
    · rintro ⟨p, hp, hPair⟩
      obtain ⟨x', y', hx', _, hφ, hPair'⟩ := (hF p).mp hp
      obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hPair hPair').mp rfl
      exact ⟨hx', (hRead x y).mp hφ⟩
    · rintro ⟨hx, hy⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
      exact ⟨p, (hF p).mpr ⟨x, y, hx, bounded_l K hCoding hGuard φ η hP (hRequests x hx) hy,
        (hRead x y).mpr hy, hp⟩, hp⟩
  have hMap : map_l (ℳ := 𝒱) F A X := by
    refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨x, y, hx, hy, _, hPair⟩ := (hF p).mp hp
      exact ⟨x, y, hx, hy, hPair⟩
    · intro x hx
      obtain ⟨y₀, hy₀, hφ₀⟩ := hRequests x hx
      obtain ⟨y, hy, _⟩ := SecondOrderCanonicalClassMinimum.exists_unique_l K hCoding hGuard φ
        (η.pushFree x) ⟨y₀, ⟨a, X, SecondOrderCanonicalLevel.hierarchy_l hP, hy₀⟩, hφ₀⟩
      refine ⟨y, ⟨bounded_l K hCoding hGuard φ η hP (hRequests x hx) hy,
        (hValue x y).mpr ⟨hx, hy⟩⟩, ?_⟩
      intro z hz
      exact unique_l K hCoding hGuard φ η ((hValue x z).mp hz.2).2 hy
  refine ⟨F, ⟨hMap, hValue⟩, ?_⟩
  intro G hG
  apply SecondOrderQuotient.ext_l hℳ G F
  intro p
  constructor
  · intro hp
    obtain ⟨x, y, _, _, hPair⟩ := hG.1.1 p hp
    have hxy : value_l (ℳ := 𝒱) F x y := (hValue x y).mpr ((hG.2 x y).mp ⟨p, hp, hPair⟩)
    obtain ⟨q, hq, hPair'⟩ := hxy
    exact (SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair) ▸ hq
  · intro hp
    obtain ⟨x, y, _, _, hPair⟩ := hMap.1 p hp
    have hxy : value_l (ℳ := 𝒱) G x y := (hG.2 x y).mpr ((hValue x y).mp ⟨p, hp, hPair⟩)
    obtain ⟨q, hq, hPair'⟩ := hxy
    exact (SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair) ▸ hq

/-- 两个可用层界只改变陪域规格，不改变同一请求的完整图。 -/
theorem bound_independent_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {ω e t₁ t₂ t₃ Pair Valid B P₀ A X Y F G : type_l hℳ}
    (hF : selection_l φ η ω e t₁ t₂ t₃ Pair Valid B P₀ A X F)
    (hG : selection_l φ η ω e t₁ t₂ t₃ Pair Valid B P₀ A Y G) : F = G := by
  apply SecondOrderQuotient.ext_l hℳ F G
  intro p
  constructor
  · intro hp
    obtain ⟨x, y, _, _, hPair⟩ := hF.1.1 p hp
    obtain ⟨q, hq, hPair'⟩ := (hG.2 x y).mpr ((hF.2 x y).mp ⟨p, hp, hPair⟩)
    exact (SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair) ▸ hq
  · intro hp
    obtain ⟨x, y, _, _, hPair⟩ := hG.1.1 p hp
    obtain ⟨q, hq, hPair'⟩ := (hF.2 x y).mpr ((hG.2 x y).mp ⟨p, hp, hPair⟩)
    exact (SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair) ▸ hq

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderBoundedCanonicalWitness
