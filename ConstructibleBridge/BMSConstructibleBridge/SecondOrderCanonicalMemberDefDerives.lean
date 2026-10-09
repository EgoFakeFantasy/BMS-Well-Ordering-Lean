import BMSConstructibleBridge.SecondOrderCanonicalMemberDefFormulaSemantics
import BMSConstructibleBridge.SecondOrderCompleteness

/-! # 唯一原图 Def 操作在原 Z₂ 中的正式推导

对象语言为原数／实数双排序签名，背景为原 SecondOrderArithmetic.theory_m，
结论量化任意输入实数及根数。没有可数选择、标准性或输入良基前提。
本句证明递归可用的全域原图操作，不宣称相对构造层或 BMS 最终句成立。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalMemberDefDerives

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderCanonicalMemberDefFormula
open SecondOrderCanonicalMemberDefFormulaSemantics (formula_l)

set_option autoImplicit false

universe u

def sentence_m : Sentence signature_m :=
  .forallE .set <| .forallE .num <| .existsE .set <| .conj
    (formula_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)) <|
    .forallE .set <| .imp
      (formula_m (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar .here))
      (.equal (.bvar .here) (.bvar (.there .here)))

private theorem closure_pure_m (φ : Formula signature_m [.set, .num, .set] [])
    (ψ : Formula signature_m [.set, .set, .num, .set] [])
    (hφ : language_m φ = true) (hψ : language_m ψ = true) :
    language_m (.forallE .set <| .forallE .num <| .existsE .set <| .conj φ <|
      .forallE .set <| .imp ψ (.equal (.bvar .here) (.bvar (.there .here)))) = true := by
  change (language_m _ && (language_m _ && true)) = true
  rw [hφ, hψ]
  rfl

theorem pure_sentence_m : language_m sentence_m = true :=
  closure_pure_m _ _
    (pure_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here) rfl rfl rfl)
    (pure_m (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
      (.bvar .here) rfl rfl rfl)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) : sentence_m.TrueIn ℳ := by
  intro A r
  obtain ⟨W, hW, hUnique⟩ := SecondOrderCanonicalMemberDefGraph.canonical_exists_l hℳ A r
  refine ⟨W, ?_, ?_⟩
  · exact (formula_l hℳ _ _ _ _).mpr hW
  · intro Z hZ
    exact hUnique Z ((formula_l hℳ _ _ _ _).mp hZ)

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  exact models_l hℳ

#print axioms pure_sentence_m
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalMemberDefDerives
