import BMSConstructibleBridge.PowerlessRelativizationDelta
import BMSConstructibleBridge.PowerlessRelativeClassLeastRelation
import BMSConstructibleBridge.SecondOrderCutoffDefinableSurjectionDerives
import BMSConstructibleBridge.PowerlessRelativeCutoffClassWellOrder

/-! # 固定源域中任意原公式的实际 Class Skolem 图

对象语言为纯隶属 ℒ，背景为原 Z₂。相对化原矩阵的全部量词后使用 Δ₀
关系图和指定环境良序取得最小见证；源矩阵无需自身是 Δ₀。源域及排序图
都是实际 Class 集合，所选函数也真正属于 Class，没有 Type 见证选择。

这是后续闭包、凝聚的语义辅助接口，不是源域的 Collection。尤其输出图
不保证属于该源域；枚举见证属于 cutoff 的证明仍须独立完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceLeastWitness

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderCutoffDefinableSurjectionDerives (relation_m relation_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  structure_l PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ClassModel" => structure_l hℳ B hBase

include hBase in
/-- 同一原源矩阵的全域最小见证图，保留源域中全部内部对象的精确规格。 -/
theorem exists_l (A Y R : type_l hℳ B) (hY : ∃ y, mem_l hℳ y Y.val)
    (hR : wellOrder_l (ℳ := 𝒱) Y.val R.val)
    (hAY : ∀ x, mem_l hℳ x A.val → mem_l hℳ x Y.val)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) Y.val hY) [] Δ)
    (hSome : ∀ x : PowerlessMemberStructure.type_l (ℳ := 𝒱) Y.val,
      mem_l hℳ x.val A.val → ∃ y, φ.satisfies ((η.pushFree y).pushFree x)) :
    ∃ J : type_l hℳ B, map_l (ℳ := 𝒱) J.val A.val Y.val ∧
      ∀ x y : PowerlessMemberStructure.type_l (ℳ := 𝒱) Y.val,
        value_l (ℳ := 𝒱) J.val x.val y.val ↔ mem_l hℳ x.val A.val ∧
          φ.satisfies ((η.pushFree y).pushFree x) ∧
          ∀ z : PowerlessMemberStructure.type_l (ℳ := 𝒱) Y.val,
            φ.satisfies ((η.pushFree z).pushFree x) → ¬value_l (ℳ := 𝒱) R.val z.val y.val := by
  let ρ : Env ClassModel [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with
        | .set => ⟨(η.freeVal v).val,
          PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property (η.freeVal v).property⟩ }
  let ξ : Env ClassModel [] (.set :: Δ) := ρ.pushFree Y
  let ψ : Formula ℒ [] (.set :: .set :: .set :: Δ) := relation_m φ
    (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
    (fun v => .fvar (.there (.there (.there v))))
  have hψ : Formula.IsDelta0 membershipLevyBound ψ :=
    PowerlessRelativizationDelta.instance_l φ _ _
  have hBody (x y : PowerlessMemberStructure.type_l (ℳ := 𝒱) Y.val) :
      ψ.satisfies (((PowerlessRelativeClassRelativization.env_l ξ).pushFree y.val).pushFree x.val) ↔
        φ.satisfies ((η.pushFree y).pushFree x) :=
    relation_formula_l φ
      (((PowerlessRelativeClassRelativization.env_l ξ).pushFree y.val).pushFree x.val)
      (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
      (fun v => .fvar (.there (.there (.there v)))) η x y rfl rfl rfl (fun _ => rfl)
  obtain ⟨J, hJ, hRead⟩ := PowerlessRelativeClassLeastRelation.of_formula_l hψ ξ A Y R hR (by
    intro x hx
    let x' : PowerlessMemberStructure.type_l (ℳ := 𝒱) Y.val := ⟨x, hAY x hx⟩
    obtain ⟨y, hxy⟩ := hSome x' hx
    exact ⟨y.val, y.property, (hBody x' y).mpr hxy⟩)
  refine ⟨J, hJ, fun x y => (hRead x.val y.val).trans ?_⟩
  constructor
  · rintro ⟨hx, _hy, hxy, hMin⟩
    exact ⟨hx, (hBody x y).mp hxy,
      fun z hxz => hMin z.val z.property ((hBody x z).mpr hxz)⟩
  · rintro ⟨hx, hxy, hMin⟩
    exact ⟨hx, y.property, (hBody x y).mpr hxy,
      fun z hz hxz => hMin ⟨z, hz⟩ ((hBody x ⟨z, hz⟩).mp hxz)⟩

/-- cutoff 的排序图在证明内构造；最小见证函数仅承诺实际 Class 身份。 -/
theorem cutoff_l (K : source_coding_l hℳ) {ω Ω W A : SecondOrderQuotient.type_l hℳ}
    (P₀ : type_l hℳ B) (hSeed : SecondOrderCanonicalLevelDerives.guard_l B P₀.val)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W) (hAW : mem_l hℳ A W)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) W ⟨A, hAW⟩) [] Δ)
    (hSome : ∀ x : PowerlessMemberStructure.type_l (ℳ := 𝒱) W,
      mem_l hℳ x.val A → ∃ y, φ.satisfies ((η.pushFree y).pushFree x)) :
    ∃ R J : type_l hℳ B, wellOrder_l (ℳ := 𝒱) W R.val ∧ map_l (ℳ := 𝒱) J.val A W ∧
      ∀ x y : PowerlessMemberStructure.type_l (ℳ := 𝒱) W,
        value_l (ℳ := 𝒱) J.val x.val y.val ↔ mem_l hℳ x.val A ∧
          φ.satisfies ((η.pushFree y).pushFree x) ∧
          ∀ z : PowerlessMemberStructure.type_l (ℳ := 𝒱) W,
            φ.satisfies ((η.pushFree z).pushFree x) → ¬value_l (ℳ := 𝒱) R.val z.val y.val := by
  have hBase' x hx y hy := hSeed.2.1 x y hx hy
  have hClass := PowerlessRelativeLevelClosure.class_l hℳ hBase' hW
  let W' : type_l hℳ B := ⟨W, hClass⟩
  let A' : type_l hℳ B :=
    ⟨A, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase' hClass hAW⟩
  obtain ⟨R, hR⟩ := PowerlessRelativeCutoffClassWellOrder.exists_l K P₀ hSeed hω hΩ hW
  obtain ⟨J, hJ, hRead⟩ := exists_l (hBase := hBase') A' W' R ⟨A, hAW⟩ hR
    (fun x hx => PowerlessRelativeLevelClosure.transitive_l hℳ hBase' hW A hAW x hx) φ η hSome
  exact ⟨R, J, hR, hJ, hRead⟩

#print axioms exists_l
#print axioms cutoff_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceLeastWitness
