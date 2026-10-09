import BMSConstructibleBridge.PowerlessCanonicalCodedSkolemSyntax
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalEdgeReading
import BMSConstructibleBridge.PowerlessRelativeClassFormulaInstances
import BMSConstructibleBridge.SecondOrderCanonicalClassSkolem

/-! # 原类相对请求的规范最小见证同值读数

纯隶属 ℒ、原 Z₂。明确构造原请求的 Class 实例，输出槽显式带 Class
守卫。原全局比较与覆盖比较的认同保留请求、参数和缺省 B 分支；
全部候选在原公式所规定的域中，不能把缺省值冒充存在见证。
本模块是原算子衔接的中间读数，未宣称任意原 raw 公式均绝对。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalSkolemReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassFormulaInstances (instance_m instance_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev free₂_m {Δ : SortContext ℒ} (B : Term ℒ [] Δ .set) :=
  Term.weakenFree (σ := ℒ) SetTheory.SetSort.set
    (Term.weakenFree (σ := ℒ) SetTheory.SetSort.set B)

/-- 原输出／输入槽序不变；Class 参数 B 从原参数项读取。 -/
def request_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: .set :: Δ) :=
  .conj (PowerlessRelativeHierarchySyntax.class_m (free₂_m B) (.fvar .here))
    (instance_m φ (free₂_m B) (fun v => .fvar v))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem request_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (b : Term ℒ [] Δ .set) (η : Env 𝒩₀ [] Δ)
    (hb : (b.eval η).val = B) (x y : M) :
    (request_m φ b).satisfies
      (((PowerlessRelativeClassRelativization.env_l η).pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y) := by
  let ξ : Env 𝒩₀ [] (.set :: .set :: Δ) := (η.pushFree x).pushFree y
  let ζ : Env 𝒱 [] (.set :: .set :: Δ) :=
    ((PowerlessRelativeClassRelativization.env_l η).pushFree x.val).pushFree y.val
  have hB : (free₂_m b).eval ζ = B := by
    have hRead := PowerlessRelativeClassRelativization.term_l η b
    simp only [Term.eval_weakenFree] at hRead
    simpa only [free₂_m, ζ, Term.eval_weakenFree] using hRead.trans hb
  have hν : ∀ v : Variable (.set :: .set :: Δ) .set,
      (show Term ℒ [] (.set :: .set :: Δ) .set from .fvar v).eval ζ = (ξ.freeVal v).val := by
    intro v
    cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v => rfl
  have hInstance := instance_l K φ ζ (free₂_m b) (fun v => .fvar v) ξ hB hν
  have hClass : (PowerlessRelativeHierarchySyntax.class_m (free₂_m b)
      (show Term ℒ [] (.set :: .set :: Δ) .set from .fvar .here)).satisfies ζ := by
    apply (PowerlessRelativeHierarchySemantics.class_formula_l K ζ _ _).mpr
    rw [hB]
    exact y.property
  change (_ ∧ _) ↔ _
  exact ⟨fun h => hInstance.mp h.2, fun h => ⟨hClass, hInstance.mpr h⟩⟩

theorem output_class_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (b : Term ℒ [] Δ .set) (η : Env 𝒱 [] Δ)
    (hb : b.eval η = B) (x y : SecondOrderQuotient.type_l hℳ)
    (h : (request_m φ b).satisfies ((η.pushFree x).pushFree y)) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  have hClass := (PowerlessRelativeHierarchySemantics.class_formula_l K
    ((η.pushFree x).pushFree y) (free₂_m b) (.fvar .here)).mp h.1
  simpa only [PowerlessRelativeClassCorrespondence.member_l,
    free₂_m, Term.eval_weakenFree, Term.eval, Env.pushFree_here, hb] using hClass

/-- 不同 AST 的实际请求读数足够；原 raw 元数据不必属于 Class。 -/
theorem transfer_l (K : source_coding_l hℳ) {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ) (ω P₀ x y : M) (hω : ω.val = K.omega)
    {t₁ t₂ t₃ Pair Valid : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hB : ∃ z, mem_l hℳ z B) (hSeed : wellOrder_l (ℳ := 𝒱) B P₀.val)
    (hBound : ∀ p, mem_l hℳ p P₀.val → ∃ z t,
      mem_l hℳ z B ∧ mem_l hℳ t B ∧ SecondOrderPairObjects.ordered_l hℳ z t p)
    (hRequest : ∀ z : M, ψ.satisfies ((ξ.pushFree x.val).pushFree z.val) ↔
      φ.satisfies ((η.pushFree x).pushFree z))
    (hOutput : ∀ z, ψ.satisfies ((ξ.pushFree x.val).pushFree z) →
      PowerlessRelativeClassCorrespondence.member_l hℳ B z) :
    PowerlessCanonicalCodedSkolemSyntax.relation_l (𝒩 := 𝒩₀) φ η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ ω P₀ x y ↔
    SecondOrderCanonicalClassSkolem.relation_l ψ ξ K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val t₁ t₂ t₃ Pair Valid B P₀.val x.val y.val := by
  let B₀ : M := ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  have hSome : (∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z ∧
      ψ.satisfies ((ξ.pushFree x.val).pushFree z)) ↔
      ∃ z : M, φ.satisfies ((η.pushFree x).pushFree z) := by
    constructor
    · rintro ⟨z, hz, hψ⟩
      let z₀ : M := ⟨z, hz⟩
      exact ⟨z₀, (hRequest z₀).mp hψ⟩
    · rintro ⟨z, hφ⟩
      exact ⟨z.val, z.property, (hRequest z).mpr hφ⟩
  have hMinimum :
      (φ.satisfies ((η.pushFree x).pushFree y) ∧ ∀ z : M,
        φ.satisfies ((η.pushFree x).pushFree z) →
          ¬PowerlessCanonicalCodedEdgeSyntax.edge_l (𝒩 := 𝒩₀) B₀ ω P₀ z y) ↔
      SecondOrderCanonicalClassMinimum.minimum_l ψ (ξ.pushFree x.val)
        K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
        t₁ t₂ t₃ Pair Valid B P₀.val y.val := by
    constructor
    · rintro ⟨hφ, hMin⟩
      refine ⟨y.property, (hRequest y).mpr hφ, ?_⟩
      intro z hz hzy
      let z₀ : M := ⟨z, hOutput z hz⟩
      exact hMin z₀ ((hRequest z₀).mp hz)
        ((PowerlessRelativeClassCanonicalEdgeReading.edge_l (hBase := hBase)
          K ω P₀ z₀ y hω hCoding hB hSeed hBound).mpr hzy)
    · intro h
      refine ⟨(hRequest y).mp h.2.1, ?_⟩
      intro z hz hzy
      exact h.2.2 z.val ((hRequest z).mpr hz)
        ((PowerlessRelativeClassCanonicalEdgeReading.edge_l (hBase := hBase)
          K ω P₀ z y hω hCoding hB hSeed hBound).mp hzy)
  change (_ ∨ _) ↔ (_ ∨ _)
  exact or_congr hMinimum (and_congr (not_congr hSome.symm)
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩)

theorem relation_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (b : Term ℒ [] Δ .set) (η : Env 𝒩₀ [] Δ)
    (hb : (b.eval η).val = B) (ω P₀ x y : M) (hω : ω.val = K.omega)
    {t₁ t₂ t₃ Pair Valid : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hB : ∃ z, mem_l hℳ z B) (hSeed : wellOrder_l (ℳ := 𝒱) B P₀.val)
    (hBound : ∀ p, mem_l hℳ p P₀.val → ∃ z t,
      mem_l hℳ z B ∧ mem_l hℳ t B ∧ SecondOrderPairObjects.ordered_l hℳ z t p) :
    PowerlessCanonicalCodedSkolemSyntax.relation_l (𝒩 := 𝒩₀) φ η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ ω P₀ x y ↔
    SecondOrderCanonicalClassSkolem.relation_l (request_m φ b)
      (PowerlessRelativeClassRelativization.env_l η) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val t₁ t₂ t₃ Pair Valid B P₀.val x.val y.val := by

  have hRead := PowerlessRelativeClassRelativization.term_l η b
  simp only [Term.eval_weakenFree] at hRead
  exact transfer_l K φ (request_m φ b) η (PowerlessRelativeClassRelativization.env_l η)
    ω P₀ x y hω hCoding hB hSeed hBound
    (fun z => request_formula_l K φ b η hb x z)
    (fun z hz => output_class_l K φ b _ (hRead.trans hb) x.val z hz)

#print axioms request_formula_l
#print axioms output_class_l
#print axioms transfer_l
#print axioms relation_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalSkolemReading
