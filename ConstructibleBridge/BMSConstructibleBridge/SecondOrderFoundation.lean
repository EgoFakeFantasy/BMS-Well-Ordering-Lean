import BMSConstructibleBridge.SecondOrderGraphMinimum
import BMSConstructibleBridge.SecondOrderAxioms
import BMSConstructibleBridge.SecondOrderPairSet

/-!
# 任意模型图商的正则公理

用实际成员翻译选点，再由内部关系极小元取得与母对象不交的成员。跨关系实数
的对象通过内部双模拟比较；最后回传整个公理的对象推导，不声称商外部良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFoundation

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing GraphTranslation

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (hA : ∃ B, SecondOrderGraph.mem_l B A) :
    ∃ B, SecondOrderGraph.mem_l B A ∧
      ∀ C, SecondOrderGraph.mem_l C B → ¬SecondOrderGraph.mem_l C A := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    atom_m GraphSyntax.mem_m (.fvar (.there (.there .here))) (.fvar (.there (.there .here)))
      (.fvar .here) (.fvar (.there .here))
  have hφ : language_m φ = true :=
    atom_pure_m _ _ _ _ _
      (pure_language_m GraphSyntax.mem_matrix_m GraphSyntax.mem_matrix_pure_m) rfl rfl rfl rfl
  obtain ⟨P, hP⟩ := comprehension_l hℳ φ hφ
    (((Env.empty (M := ℳ)).pushFree A.real).pushFree A.root)
  have h₀ : ∀ b, mem_l b P ↔ ∃ c, relation_l A.real c A.root ∧
      SecondOrderBisimulation.eq_l A.real A.real b c :=
    fun b => (hP b).trans (SecondOrderInterpretation.mem_l _ _ _ _ _)
  obtain ⟨_, a, ha, _⟩ := hA
  obtain ⟨b, hb, h₁, h₂⟩ := SecondOrderGraphMinimum.exists_l hℳ A.real P a
    (SecondOrderDomain.child_l hℳ A.real A.root a A.wf ha)
    ((h₀ a).mpr ⟨a, ha, SecondOrderBisimulation.refl_l hℳ A.real a⟩)
  let B : SecondOrderGraph.code_l ℳ := ⟨A.real, b, h₁⟩
  refine ⟨B, (h₀ b).mp hb, ?_⟩
  rintro C ⟨c, hc, h₃⟩ ⟨d, hd, h₄⟩
  exact h₂ c hc ((h₀ c).mpr ⟨d, hd,
    SecondOrderBisimulation.trans_l hℳ A.real C.real A.real c C.root d
      (SecondOrderBisimulation.symm_l hℳ C.real A.real C.root c h₃) h₄⟩)

private def member {Γ Δ : SortContext ℒ} (s t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .rel .membership (.cons s (.cons t .nil))

/-- 每个非空对象包含一个与其不交的成员，全式仅使用原隶属语言。 -/
def formula_m : Sentence ℒ :=
  .forallE .set <| .imp
    (.existsE .set (member (.bvar .here) (.bvar (.there .here))))
    (.existsE .set (.conj (member (.bvar .here) (.bvar (.there .here)))
      (.forallE .set (.imp (member (.bvar .here) (.bvar (.there .here)))
        (.neg (member (.bvar .here) (.bvar (.there (.there .here)))))))))

theorem models_l (hℳ : Theory.Models ℳ theory_m) :
    formula_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  change ∀ a : SecondOrderQuotient.type_l hℳ, (∃ b, SecondOrderQuotient.mem_l hℳ b a) →
    ∃ b, SecondOrderQuotient.mem_l hℳ b a ∧
      ∀ c, SecondOrderQuotient.mem_l hℳ c b → ¬SecondOrderQuotient.mem_l hℳ c a
  intro a ha
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  have hA : ∃ B, SecondOrderGraph.mem_l B A := by
    obtain ⟨b, hb⟩ := ha
    obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ b
    exact ⟨B, hb⟩
  obtain ⟨B, hB, h⟩ := exists_l hℳ A hA
  refine ⟨SecondOrderQuotient.mk_l hℳ B, hB, fun c hc hd => ?_⟩
  obtain ⟨C, rfl⟩ := SecondOrderQuotient.surj_l hℳ c
  exact h C hc hd

theorem derives_m : Derives theory_m [] (form_m formula_m) :=
  SecondOrderAxioms.interpretation_m formula_m (fun _ hℳ => models_l hℳ)

/-- 正则公理作用于单元素对象，排除自身为自身成员。 -/
theorem irrefl_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ) :
    ¬SecondOrderGraph.mem_l A A := by
  intro h
  obtain ⟨S, hS⟩ := SecondOrderPairSet.exists_l hℳ A A
  have hA : SecondOrderGraph.mem_l A S :=
    (hS A).mpr (Or.inl (SecondOrderGraph.refl_l hℳ A))
  obtain ⟨B, hB, h₁⟩ := exists_l hℳ S ⟨A, hA⟩
  have h₂ : SecondOrderGraph.eq_l B A := ((hS B).mp hB).elim id id
  exact h₁ A ((SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ A)
    (SecondOrderGraph.symm_l hℳ h₂)).mp h) hA

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFoundation
