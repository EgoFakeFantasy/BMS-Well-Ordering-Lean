import BMSConstructibleBridge.PowerlessRelativeFiniteProgramAlphabet
import BMSConstructibleBridge.PowerlessRelativeLimitFiniteMaps

/-! # 共同极限层中的实际指令与内部有限词

常量母集只需包含于 W，标签属于 W，ω 属于 W。实际三类字母表
的每个指令因此属于 W，而字母表自身不要求属于 W。对任意内部
有限长度，原有限图定理回收同一程序词的 W 成员性。
这些界供后续同母界求值矩阵使用，不预设完整收集或求值像。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramLimitWord

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessRelativeFiniteProgramAlphabet (alphabet_m alphabet_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem instruction_l {B β W C ω t₀ t₁ t₂ q : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hC : ∀ x, mem_l hℳ x C → mem_l hℳ x W) (hω : mem_l hℳ ω W)
    (h₀ : mem_l hℳ t₀ W) (h₁ : mem_l hℳ t₁ W) (h₂ : mem_l hℳ t₂ W)
    (hq : PowerlessRelativeFiniteProgramAlphabet.instruction_l C ω t₀ t₁ t₂ q) :
    mem_l hℳ q W := by
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hB hW
  rcases hq with ⟨a, ha, hq⟩ | ⟨k, hk, hq⟩ | ⟨k, l, p, hk, hl, hp, hq⟩
  · exact PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW h₀ (hC a ha) hq
  · exact PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW h₁ (hTrans ω hω k hk) hq
  · exact PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW h₂
      (PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW
        (hTrans ω hω k hk) (hTrans ω hω l hl) hp) hq

theorem word_l (K : source_coding_l hℳ) {B β W C ω t₀ t₁ t₂ Q n w : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hC : ∀ x, mem_l hℳ x C → mem_l hℳ x W)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hωW : mem_l hℳ ω W)
    (h₀ : mem_l hℳ t₀ W) (h₁ : mem_l hℳ t₁ W) (h₂ : mem_l hℳ t₂ W)
    (hQ : ∀ q, mem_l hℳ q Q ↔ PowerlessRelativeFiniteProgramAlphabet.instruction_l C ω t₀ t₁ t₂ q)
    (hn : mem_l hℳ n ω) (hw : map_l (ℳ := 𝒱) w n Q) :
    (∀ q, mem_l hℳ q Q → mem_l hℳ q W) ∧ mem_l hℳ w W := by
  have hQW : ∀ q, mem_l hℳ q Q → mem_l hℳ q W :=
    fun q hq => instruction_l hB hβ hW hC hωW h₀ h₁ h₂ ((hQ q).mp hq)
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  exact ⟨hQW, PowerlessRelativeLimitFiniteMaps.subset_member_l hℳ hB hβ hW K
    (hωEq ▸ hωW) hQW (hωEq ▸ hn) hw⟩

def schema_m {Δ : SortContext ℒ} (B β W C ω t₀ t₁ t₂ Q n w : Term ℒ [] Δ .set) :
    Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .imp (ThirdOrderTheory.subset_m C W) <|
          .imp (SecondOrderOmegaSyntax.omega_m ω) <|
            .imp (SecondOrderObjectSyntax.member_m ω W) <|
              .imp (SecondOrderObjectSyntax.member_m t₀ W) <|
                .imp (SecondOrderObjectSyntax.member_m t₁ W) <|
                  .imp (SecondOrderObjectSyntax.member_m t₂ W) <|
                    .imp (alphabet_m C ω t₀ t₁ t₂ Q) <|
                      .imp (SecondOrderObjectSyntax.member_m n ω) <|
                        .imp (SecondOrderObjectSyntax.map_m w n Q) <|
                          .conj (ThirdOrderTheory.subset_m Q W) (SecondOrderObjectSyntax.member_m w W)

def sentence_m {Δ : SortContext ℒ} (B β W C ω t₀ t₁ t₂ Q n w : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β W C ω t₀ t₁ t₂ Q n w)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β W C ω t₀ t₁ t₂ Q n w : Term ℒ [] Δ .set) :
    (sentence_m B β W C ω t₀ t₁ t₂ Q n w).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K, subset_formula_l,
    SecondOrderOmegaSyntax.omega_l, alphabet_formula_l, map_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro η hB hβ hW hC hω hωW h₀ h₁ h₂ hQ hn hw
  exact word_l K hB hβ hW hC hω hωW h₀ h₁ h₂ hQ hn hw

theorem derives_m {Δ : SortContext ℒ} (B β W C ω t₀ t₁ t₂ Q n w : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B β W C ω t₀ t₁ t₂ Q n w)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 B β W C ω t₀ t₁ t₂ Q n w)

#print axioms instruction_l
#print axioms word_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramLimitWord
