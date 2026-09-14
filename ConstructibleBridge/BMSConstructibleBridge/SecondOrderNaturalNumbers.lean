import BMSConstructibleBridge.SecondOrderFoundation
import BMSConstructibleBridge.SecondOrderInfinity

/-!
# 模型数与解释内部自然数的精确对应

同一模型小于关系的数根没有额外双模拟相等，成员关系恰好是模型小于。
其内部像在每个归纳对象中，覆盖所有模型数而非只覆盖标准自然数像。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNaturalNumbers

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderNaturalGraph

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem eq_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b) (m n : num_l ℳ) :
    SecondOrderGraph.eq_l (code_l hℳ R hR m) (code_l hℳ R hR n) ↔ m = n := by
  constructor
  · intro h
    rcases SecondOrderOrder.trichotomy_l hℳ m n with h₁ | h₁ | h₁
    · have h₂ : SecondOrderGraph.mem_l (code_l hℳ R hR m) (code_l hℳ R hR n) :=
        ⟨m, (hR m n).mpr h₁, SecondOrderBisimulation.refl_l hℳ R m⟩
      exact False.elim (SecondOrderFoundation.irrefl_l hℳ (code_l hℳ R hR m)
        ((SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ _)
          (SecondOrderGraph.symm_l hℳ h)).mp h₂))
    · exact h₁
    · have h₂ : SecondOrderGraph.mem_l (code_l hℳ R hR n) (code_l hℳ R hR m) :=
        ⟨n, (hR n m).mpr h₁, SecondOrderBisimulation.refl_l hℳ R n⟩
      exact False.elim (SecondOrderFoundation.irrefl_l hℳ (code_l hℳ R hR n)
        ((SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ _) h).mp h₂))
  · rintro rfl
    exact SecondOrderGraph.refl_l hℳ _

theorem mem_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b) (m n : num_l ℳ) :
    SecondOrderGraph.mem_l (code_l hℳ R hR m) (code_l hℳ R hR n) ↔
      SecondOrderOrder.lt_l m n := by
  constructor
  · rintro ⟨k, hk, h⟩
    have h₁ := (eq_l hℳ R hR m k).mp h
    exact h₁ ▸ (hR k n).mp hk
  · intro h
    exact ⟨m, (hR m n).mpr h, SecondOrderBisimulation.refl_l hℳ R m⟩

theorem range_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b) :
    ∃ Ω : SecondOrderGraph.code_l ℳ, ∀ A, SecondOrderGraph.mem_l A Ω ↔
      ∃ n, SecondOrderGraph.eq_l A (code_l hℳ R hR n) := by
  obtain ⟨P, hP⟩ := comprehension_l hℳ .truth rfl (Env.empty (M := ℳ))
  obtain ⟨Ω, hΩ⟩ := SecondOrderGraftSemantics.exists_l hℳ R P (fun n _ => wf_l hℳ R hR n)
  refine ⟨Ω, fun A => (hΩ A).trans ?_⟩
  exact ⟨fun ⟨n, _, h⟩ => ⟨n, h⟩, fun ⟨n, h⟩ => ⟨n, (hP n).mpr True.intro, h⟩⟩

/-- 归纳对象的精确成员规格，不使用额外的集合论函数符号。 -/
def inductive_l (I : SecondOrderGraph.code_l ℳ) : Prop :=
  (∃ E, (∀ A, ¬SecondOrderGraph.mem_l A E) ∧ SecondOrderGraph.mem_l E I) ∧
    ∀ A, SecondOrderGraph.mem_l A I → ∃ B, SecondOrderGraph.mem_l B I ∧
      ∀ C, SecondOrderGraph.mem_l C B ↔ SecondOrderGraph.mem_l C A ∨ SecondOrderGraph.eq_l C A

/-- 模型归纳使每个模型数的集合表示都属于每个归纳对象。 -/
theorem inductive_mem_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b)
    (I : SecondOrderGraph.code_l ℳ) (hI : inductive_l I) (n : num_l ℳ) :
    SecondOrderGraph.mem_l (code_l hℳ R hR n) I := by
  let φ : Formula signature_m [] [.num, .set, .set, .num] :=
    GraphTranslation.atom_m GraphSyntax.mem_m (.fvar (.there .here))
      (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there (.there (.there .here))))
  have hφ : language_m φ = true := GraphTranslation.atom_pure_m _ _ _ _ _
    (pure_language_m GraphSyntax.mem_matrix_m GraphSyntax.mem_matrix_pure_m) rfl rfl rfl rfl
  apply induct_l hℳ φ hφ
    ((((Env.empty (M := ℳ)).pushFree I.root).pushFree I.real).pushFree R)
    (fun n => SecondOrderGraph.mem_l (code_l hℳ R hR n) I)
    (fun _ => SecondOrderInterpretation.mem_l _ _ _ _ _) ?_ ?_ n
  · obtain ⟨E, hE, h₀⟩ := hI.1
    have h : SecondOrderGraph.eq_l E (code_l hℳ R hR (zero_l ℳ)) := by
      apply (SecondOrderGraph.ext_l hℳ _ _).mpr
      intro A
      exact iff_of_false (hE A) (SecondOrderInfinity.zero_l hℳ R hR A)
    exact (SecondOrderGraph.mem_congr_l hℳ h (SecondOrderGraph.refl_l hℳ I)).mp h₀
  · intro i hi
    obtain ⟨B, hB, h⟩ := hI.2 (code_l hℳ R hR i) hi
    have h₁ : SecondOrderGraph.eq_l B (code_l hℳ R hR (succ_l i)) := by
      apply (SecondOrderGraph.ext_l hℳ _ _).mpr
      intro C
      exact (h C).trans (SecondOrderInfinity.succ_l hℳ R hR i C).symm
    exact (SecondOrderGraph.mem_congr_l hℳ h₁ (SecondOrderGraph.refl_l hℳ I)).mp hB

theorem range_inductive_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b)
    (Ω : SecondOrderGraph.code_l ℳ)
    (hΩ : ∀ A, SecondOrderGraph.mem_l A Ω ↔ ∃ n, SecondOrderGraph.eq_l A (code_l hℳ R hR n)) :
    inductive_l Ω := by
  refine ⟨⟨code_l hℳ R hR (zero_l ℳ), SecondOrderInfinity.zero_l hℳ R hR, ?_⟩, ?_⟩
  · exact (hΩ _).mpr ⟨zero_l ℳ, SecondOrderGraph.refl_l hℳ _⟩
  · intro A hA
    obtain ⟨n, h⟩ := (hΩ A).mp hA
    refine ⟨code_l hℳ R hR (succ_l n),
      (hΩ _).mpr ⟨succ_l n, SecondOrderGraph.refl_l hℳ _⟩, fun C => ?_⟩
    refine (SecondOrderInfinity.succ_l hℳ R hR n C).trans (or_congr
      (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ C) h).symm ?_)
    exact ⟨fun h₁ => SecondOrderGraph.trans_l hℳ h₁ (SecondOrderGraph.symm_l hℳ h),
      fun h₁ => SecondOrderGraph.trans_l hℳ h₁ h⟩

theorem least_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b)
    (Ω : SecondOrderGraph.code_l ℳ)
    (hΩ : ∀ A, SecondOrderGraph.mem_l A Ω ↔ ∃ n, SecondOrderGraph.eq_l A (code_l hℳ R hR n))
    (I : SecondOrderGraph.code_l ℳ) (hI : inductive_l I) :
    ∀ A, SecondOrderGraph.mem_l A Ω → SecondOrderGraph.mem_l A I := by
  intro A hA
  obtain ⟨n, h⟩ := (hΩ A).mp hA
  exact (SecondOrderGraph.mem_congr_l hℳ h (SecondOrderGraph.refl_l hℳ I)).mpr
    (inductive_mem_l hℳ R hR I hI n)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNaturalNumbers
