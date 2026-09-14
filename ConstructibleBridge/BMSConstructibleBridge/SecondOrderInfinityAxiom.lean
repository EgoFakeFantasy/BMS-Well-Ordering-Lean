import BMSConstructibleBridge.SecondOrderInfinity
import BMSConstructibleBridge.SecondOrderAxioms

/-!
# 无穷公理的二阶对象推导

源句子直接要求一个含空对象且对成员定义的后继封闭的集合。没有自然数或
后继函数的集合论扩展符号。完整原翻译的对象证明来自任意模型内部归纳集。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInfinityAxiom

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic GraphTranslation

set_option autoImplicit false

universe u

private def member {Γ Δ : SortContext ℒ} (s t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .rel .membership (.cons s (.cons t .nil))

/-- 纯隶属语言中的实际无穷公理：存在含空集且对 x ∪ {x} 封闭的集合。 -/
def formula_m : Sentence ℒ :=
  .existsE .set <| .conj
    (.existsE .set (.conj
      (.forallE .set (.neg (member (.bvar .here) (.bvar (.there .here)))))
      (member (.bvar .here) (.bvar (.there .here)))))
    (.forallE .set (.imp (member (.bvar .here) (.bvar (.there .here)))
      (.existsE .set (.conj (member (.bvar .here) (.bvar (.there (.there .here))))
        (.forallE .set (.iff (member (.bvar .here) (.bvar (.there .here)))
          (.disj (member (.bvar .here) (.bvar (.there (.there .here))))
            (.equal (.bvar .here) (.bvar (.there (.there .here)))))))))))

theorem formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) :
    formula_m.TrueIn (SecondOrderQuotient.structure_l hℳ) ↔
      ∃ W : SecondOrderQuotient.type_l hℳ,
        (∃ E, (∀ B, ¬SecondOrderQuotient.mem_l hℳ B E) ∧ SecondOrderQuotient.mem_l hℳ E W) ∧
        ∀ A, SecondOrderQuotient.mem_l hℳ A W →
          ∃ B, SecondOrderQuotient.mem_l hℳ B W ∧ ∀ C,
            SecondOrderQuotient.mem_l hℳ C B ↔ SecondOrderQuotient.mem_l hℳ C A ∨ C = A := by
  simp only [formula_m, member, Formula.TrueIn, Formula.satisfies]
  rfl

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) : formula_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (formula_l hℳ).mpr
  obtain ⟨W, ⟨E, hE, hEW⟩, hW⟩ := SecondOrderInfinity.exists_l hℳ
  refine ⟨SecondOrderQuotient.mk_l hℳ W, ⟨SecondOrderQuotient.mk_l hℳ E, ?_, hEW⟩, ?_⟩
  · intro b
    obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ b
    exact hE B
  · intro a h
    obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
    obtain ⟨B, hB, h₁⟩ := hW A h
    refine ⟨SecondOrderQuotient.mk_l hℳ B, hB, fun c => ?_⟩
    obtain ⟨C, rfl⟩ := SecondOrderQuotient.surj_l hℳ c
    exact (h₁ C).trans (or_congr Iff.rfl (SecondOrderQuotient.eq_iff_l hℳ C A).symm)

theorem derives_m : Derives theory_m [] (form_m formula_m) :=
  SecondOrderAxioms.interpretation_m formula_m (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInfinityAxiom
