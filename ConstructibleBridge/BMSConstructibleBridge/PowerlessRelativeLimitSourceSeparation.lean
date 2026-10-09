import BMSConstructibleBridge.PowerlessRelativeLimitSourceBasics
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparation
import BMSConstructibleBridge.PowerlessSourceAmbient
import BMSConstructibleBridge.PowerlessWeakSeparationSyntax

/-! # 实际极限层子模型的原 Δ₀ Separation

环境层中的精确切片，经传递成员域的有界绝对性取得子模型中原
Separation AST 的全部参数实例。闭模式使用原分离句，不以另造
样本或外部成员规格替代。这里仍只有 Δ₀ 分离，不是完整源理论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSourceSeparation

open Logic FirstOrder PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β C ω : SecondOrderQuotient.type_l hℳ}
  (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
  (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
  (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C) (hωC : mem_l hℳ ω C)

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "LevelModel" => PowerlessMemberStructure.structure_l (ℳ := 𝒱) C (Exists.intro ω hωC)
local notation "CType" => PowerlessMemberStructure.type_l (ℳ := 𝒱) C

include hBase hLimit hC in
theorem exists_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env LevelModel [] Δ) (A : CType) :
    ∃ Y : CType, ∀ x : CType, mem_l hℳ x.val Y.val ↔
      mem_l hℳ x.val A.val ∧ φ.satisfies (η.pushFree x) := by
  let ξ := PowerlessSourceAmbient.env_l η
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  have hCT : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) C := fun x y hx hy => hTrans x hx y hy
  obtain ⟨Y, hY, hRead⟩ := PowerlessRelativeLimitDeltaSeparation.exists_l
    hBase hLimit hC hφ ξ A.property (fun s v => by cases s; exact (η.freeVal v).property)
  refine ⟨⟨Y, hY⟩, fun x => (hRead x.val).trans (and_congr Iff.rfl ?_)⟩
  have hAbsolute := PowerlessSourceAmbient.formula_l hCT hφ (η.pushFree x)
  have hEnv : PowerlessSourceAmbient.env_l (η.pushFree (sort := SetTheory.SetSort.set) x) =
      ξ.pushFree (sort := SetTheory.SetSort.set) x.val := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v
      cases s
      cases v <;> rfl
  rw [hEnv] at hAbsolute
  exact hAbsolute.symm

include hBase hLimit hC in
theorem models_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) : (SecondOrderSeparationAxiom.sentence_m φ).TrueIn LevelModel := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  apply (PowerlessWeakSeparationSyntax.schema_formula_l φ η).mpr
  exact exists_l hBase hLimit hC hωC hφ η

theorem derives_m {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (PowerlessRelativeLimitSourceBasics.guarded_m (SecondOrderSeparationAxiom.sentence_m φ))) :=
  PowerlessRelativeLimitSourceBasics.derives_m _
    (fun _ _ _ _ _ _ hBase hC hLimit _ hωC => models_l hBase hLimit hC hωC hφ)

#print axioms exists_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSourceSeparation
