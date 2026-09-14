import BMSConstructibleBridge.SecondOrderCompleteness
import BMSConstructibleBridge.SecondOrderInterpretation

/-!
# 已完成解释的实际对象推导

先在任意二阶算术模型中核验同一内部图商，再由固定签名强完备性回传。
这里得到真正的对象 `Derives`，而不只是标准模型真值；目前仅覆盖明确列出的
外延、空集及反配对存在，不包含全部 TMC 公理或 BM4 固定高度证明生成器。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAxioms

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic GraphTranslation

set_option autoImplicit false

/-- 原纯集合论签名中的完整外延公理。 -/
def extensionality_m : Sentence ℒ :=
  .forallE .set (.forallE .set (.imp
    (.forallE .set (.iff
      (.rel .membership (.cons (.bvar .here) (.cons (.bvar (.there (.there .here))) .nil)))
      (.rel .membership (.cons (.bvar .here) (.cons (.bvar (.there .here)) .nil)))))
    (.equal (.bvar (.there .here)) (.bvar .here))))

def empty_m : Sentence ℒ :=
  .existsE .set (.forallE .set
    (.neg (.rel .membership (.cons (.bvar .here) (.cons (.bvar (.there .here)) .nil)))))

/-- 固定图翻译的全模型正确性回传；调用者仍须逐一验证所需源公理。 -/
theorem interpretation_m (φ : Sentence ℒ)
    (h : ∀ (ℳ : FirstOrder.Structure.{0, 0, 0, 0} signature_m)
      (hℳ : Theory.Models ℳ theory_m), φ.TrueIn (SecondOrderQuotient.structure_l hℳ)) :
    Derives theory_m [] (form_m φ) := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  refine (SecondOrderInterpretation.form_l hℳ φ (fun v => nomatch v) (fun v => nomatch v)).mpr ?_
  have h₁ : SecondOrderInterpretation.source_l hℳ
      (Γ := []) (Δ := []) (fun v => nomatch v) (fun v => nomatch v) = Env.empty := by
    apply Env.ext <;> intro s v <;> nomatch v
  rw [h₁]
  exact h ℳ hℳ

theorem extensionality_derives_m : Derives theory_m [] (form_m extensionality_m) := by
  apply interpretation_m
  intro ℳ hℳ
  change ∀ a b : SecondOrderQuotient.type_l hℳ,
    (∀ c, SecondOrderQuotient.mem_l hℳ c a ↔ SecondOrderQuotient.mem_l hℳ c b) → a = b
  exact SecondOrderQuotient.ext_l hℳ

theorem empty_derives_m : Derives theory_m [] (form_m empty_m) := by
  apply interpretation_m
  intro ℳ hℳ
  exact SecondOrderQuotient.empty_l hℳ

/-- 任意数有配对坐标的实际纯算术闭句。 -/
def unpair_m : Sentence signature_m :=
  .forallE .num <| .existsE .num <| .existsE .num <|
    PrimitiveFormulas.pair_m (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here)))

theorem unpair_derives_m : Derives theory_m [] unpair_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  simp only [unpair_m, Formula.TrueIn, Formula.satisfies, SecondOrderPairing.formula_l]
  exact SecondOrderUnpairing.surjective_l hℳ

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAxioms
