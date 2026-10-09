import BMSConstructibleBridge.PowerlessHereditarySubset
import BMSConstructibleBridge.PowerlessHereditaryBounded
import BMSConstructibleBridge.PowerlessRelativeClassDeltaSeparation

/-! # 遗传子模型中的实际 Δ₀ 分离模式

在相对类中取得精确切片，再由遗传子集封闭把见证放回遗传类。
两侧有界真值经原商核验一致；每个外部有限参数实例回传原 Z₂ 推导。
这里没有证明无界分离，更没有加入 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryDeltaSeparation

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessHereditaryStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

def env_l {Γ Δ : SortContext ℒ} (η : Env (structure_l hℳ B hBase) Γ Δ) :
    Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) Γ Δ where
  boundVal {s} v := match s with
    | .set => ⟨(η.boundVal v).val, PowerlessHereditaryClass.contained_l hℳ hBase (η.boundVal v).property⟩
  freeVal {s} v := match s with
    | .set => ⟨(η.freeVal v).val, PowerlessHereditaryClass.contained_l hℳ hBase (η.freeVal v).property⟩

theorem exists_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env (structure_l hℳ B hBase) [] Δ)
    (X : type_l hℳ B) : ∃ Y : type_l hℳ B, ∀ x : type_l hℳ B,
      mem_l hℳ x.val Y.val ↔ mem_l hℳ x.val X.val ∧ φ.satisfies (η.pushFree x) := by
  let X' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨X.val, PowerlessHereditaryClass.contained_l hℳ hBase X.property⟩
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassDeltaSeparation.exists_l hφ (env_l η) X'
  have hSubset : ∀ x, mem_l hℳ x Y.val → mem_l hℳ x X.val := by
    intro x hx
    let x' : PowerlessRelativeClassStructure.type_l hℳ B :=
      ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hx⟩
    exact ((hY x').mp hx).1
  have hHH := PowerlessHereditarySubset.member_l hℳ hBase X.property Y.property hSubset
  refine ⟨⟨Y.val, hHH⟩, fun x => ?_⟩
  let x' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨x.val, PowerlessHereditaryClass.contained_l hℳ hBase x.property⟩
  have hEnv : PowerlessRelativeClassRelativization.env_l ((env_l η).pushFree (sort := SetTheory.SetSort.set) x') =
      PowerlessHereditaryRelativization.env_l (η.pushFree (sort := SetTheory.SetSort.set) x) := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v
      cases s
      cases v <;> rfl
  have hClass := PowerlessRelativeClassBounded.formula_l hφ
    ((env_l η).pushFree (sort := SetTheory.SetSort.set) x')
  rw [hEnv] at hClass
  exact (hY x').trans (and_congr Iff.rfl
    (hClass.trans (PowerlessHereditaryBounded.formula_l hφ (η.pushFree x)).symm))

theorem models_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    (SecondOrderSeparationAxiom.sentence_m φ).TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  apply (PowerlessWeakSeparationSyntax.schema_formula_l φ η).mpr
  exact exists_l hφ η

theorem derives_m {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessHereditaryRelativization.guarded_m (SecondOrderSeparationAxiom.sentence_m φ))) :=
  PowerlessHereditaryRelativization.derives_m _ (fun _ _ _ _ => models_l hφ)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryDeltaSeparation
