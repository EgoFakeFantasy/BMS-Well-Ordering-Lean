import BMSConstructibleBridge.PowerlessHereditaryFullSeparation
import BMSConstructibleBridge.PowerlessHereditaryBasicAxioms
import BMSConstructibleBridge.PowerlessHereditaryPairing
import BMSConstructibleBridge.SecondOrderWeakSetTheory

/-! # 实际遗传子模型的弱集合论解释

纯隶属 ℒ，原 Z₂ 背景，原 Derives 推导核。实际传递、非空、遗传基底
的子模型满足完整分离及既有七项基础公理；任意该弱理论闭句推导
回传为原 Z₂ 中的守卫相对化推导。不加入 Collection、选择或首 Ω。
这里没有把弱理论解释冒充最终固定高度 BMS 良序证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryWeakTheory

open Logic FirstOrder
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessHereditaryStructure.structure_l

universe u

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hB : PowerlessHereditaryClass.member_l hℳ B B) (hNonempty : ∃ d, mem_l hℳ d B) :
    Theory.Models (PowerlessHereditaryStructure.structure_l hℳ B hBase)
      SecondOrderWeakSetTheory.theory_m := by
  intro φ h
  cases h with
  | extensionality => exact PowerlessHereditaryStructure.extensionality_l hℳ B hBase
  | empty => exact PowerlessHereditaryBasicAxioms.empty_l hℳ B hBase
  | pairing => exact PowerlessHereditaryPairing.models_l hℳ B hBase
  | union => exact PowerlessHereditaryBasicAxioms.union_l hℳ B hBase
  | infinity => exact PowerlessHereditaryStructure.infinity_l hℳ B hBase
  | foundation => exact PowerlessHereditaryStructure.foundation_l hℳ B hBase
  | transitive => exact PowerlessHereditaryStructure.transitive_superset_l hℳ B hBase
  | separation φ =>
      exact PowerlessHereditaryFullSeparation.source_models_l hℳ B hBase hB hNonempty φ

def sentence_m (φ : Sentence ℒ) : Sentence ℒ :=
  Metatheory.Formula.forall_close <|
    .imp (PowerlessHereditaryFullSeparation.base_m (.fvar .here))
      (PowerlessHereditaryRelativization.formula_m φ)

theorem sentence_models_l
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {φ : Sentence ℒ}
    (h : Derives SecondOrderWeakSetTheory.theory_m [] φ) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hGuard
  obtain ⟨hBase, hB, hNonempty⟩ :=
    (PowerlessHereditaryFullSeparation.base_formula_l K η (.fvar .here)).mp hGuard
  have hEnv : η = (Env.empty (M := SecondOrderQuotient.structure_l hℳ)).pushFree
      (sort := SetTheory.SetSort.set) (η.freeVal .here) := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; cases v with
      | here => rfl
      | there v => nomatch v
  rw [hEnv]
  apply (PowerlessHereditaryRelativization.sentence_l (hBase := hBase) K φ).mpr
  exact h.sound (models_l hℳ (η.freeVal .here) hBase hB hNonempty) Env.empty
    (by intro ψ hψ; cases hψ)

/-- 经已核验的同一语言、同一 universe 模型解释回传原对象推导。 -/
theorem interpretation_m {φ : Sentence ℒ} (h : Derives SecondOrderWeakSetTheory.theory_m [] φ) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => sentence_models_l hℳ h)

#print axioms models_l
#print axioms sentence_models_l
#print axioms interpretation_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryWeakTheory
