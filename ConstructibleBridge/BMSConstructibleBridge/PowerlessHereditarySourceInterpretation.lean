import BMSConstructibleBridge.PowerlessHereditarySourceCore
import BMSConstructibleBridge.PowerlessBMSObjectProof

/-! # 原无幂集源推导的遗传域回传

背景原 Z₂、对象语言 ℒ 和原 Derives 核。任意原 PowerlessTheory 闭句
推导解释为实际遗传域上的守卫相对化推导；同一外部 H 的原 BMS 源
句子可直接回传。守卫还未消去，源算术与原候选实数还需对应，故不
把这里的 bms_derives_m 冒充 SecondOrderConcreteFormula.closed_m H。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditarySourceInterpretation

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessHereditaryStructure.structure_l

universe u

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {φ : Sentence ℒ}
    (hφ : Derives PowerlessTheory.theory_m [] φ) :
    (PowerlessHereditaryWeakTheory.sentence_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
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
  exact hφ.sound (PowerlessHereditarySourceCore.models_l (hBase := hBase) K hB hNonempty)
    Env.empty (by intro ψ hψ; cases hψ)

theorem derives_m {φ : Sentence ℒ} (hφ : Derives PowerlessTheory.theory_m [] φ) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (PowerlessHereditaryWeakTheory.sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ hφ)

theorem bms_derives_m (H : Nat) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m
        (PowerlessHereditaryWeakTheory.sentence_m (PowerlessBMSObjectProof.sentence_m H))) :=
  derives_m (PowerlessBMSObjectProof.derives_m H)

#print axioms models_l
#print axioms derives_m
#print axioms bms_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditarySourceInterpretation
