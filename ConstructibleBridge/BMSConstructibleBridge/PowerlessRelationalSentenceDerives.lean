import BMSConstructibleBridge.PowerlessRelationalSentenceSyntax
import BMSConstructibleBridge.PowerlessRelationalSourceCompilation

/-! # 跨域闭句编译模式的原 Z₂ 推导

同一编码系统、数码和长度先于全部非空域选定；各域的集合求值图实际存在。
由已验证的类相对化与原图翻译回到原 Derives 核，不把语义辅助定理冒充终局。
外部索引是每个固定源闭句，不是模型内部的统一真值断言。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalSentenceDerives

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelationalSentenceSyntax

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    (φ : Sentence ℒ) {ω : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) :
    ∃ e t₁ t₂ t₃ T c : type_l hℳ B, mem_l hℳ c.val ω.val ∧ ∃ N : type_l hℳ B,
      mem_l hℳ N.val ω.val ∧ ∀ A : type_l hℳ B, ∀ hA : ∃ a, member_l (structure_l hℳ B hBase) a A,
        ∃ S G, PowerlessRelativeClassEvaluationSystem.spec_l (𝒩 := structure_l hℳ B hBase) ω A e t₁ t₂ t₃ T S G ∧
          ∀ m, member_l (structure_l hℳ B hBase) m ω → subset_l (ℳ := structure_l hℳ B hBase) N m →
            ∀ f, map_l (ℳ := structure_l hℳ B hBase) f m A →
              (value_l (ℳ := structure_l hℳ B hBase) G c f ↔
                φ.TrueIn (PowerlessMemberStructure.structure_l (ℳ := structure_l hℳ B hBase) A hA)) := by
  obtain ⟨e, t₁, t₂, t₃, T, hSystem⟩ := PowerlessRelativeClassEvaluationSystem.uniform_exists_l hω
  obtain ⟨_, _, hStatic⟩ := hSystem ω
  have he := (PowerlessRelativeClassNaturalProperties.tags_natural_l hω hStatic.1).1
  have hEmpty : PowerlessSourceEnvironment.bounded_l (Env.empty : Env (structure_l hℳ B hBase) [] []) e := by
    intro t
    match t with
    | .bvar v => nomatch v
    | .fvar v => nomatch v
    | .app q _ => nomatch q
  obtain ⟨c, N, hc, hN, _, hCompile⟩ := PowerlessRelationalSourceCompilation.formula_l
    hω hStatic.1 hStatic.2.2.1 φ Env.empty he hEmpty
  refine ⟨e, t₁, t₂, t₃, T, c, hc, N, hN, ?_⟩
  intro A hA
  obtain ⟨S, G, hSG⟩ := hSystem A
  refine ⟨S, G, hSG, ?_⟩
  intro m hm hM f hf
  exact hCompile hSG hA m hm hM f hf Env.empty (PowerlessSourceEnvironment.empty_l f)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {Δ : SortContext ℒ} (φ : Sentence ℒ) (ω : Term ℒ [] Δ .set) :
    (sentence_m φ ω).TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l, existence_formula_l]
  exact fun hω => exists_l φ hω

theorem derives_m {Δ : SortContext ℒ} (φ : Sentence ℒ) (ω : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m (sentence_m φ ω))) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ hℳ B hBase => models_l hℳ B hBase φ ω)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalSentenceDerives
