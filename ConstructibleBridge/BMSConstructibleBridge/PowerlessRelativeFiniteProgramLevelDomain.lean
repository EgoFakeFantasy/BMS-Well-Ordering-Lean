import BMSConstructibleBridge.PowerlessRelativeFiniteProgramDomain
import BMSConstructibleBridge.PowerlessRelativeLimitClosure

/-! # 从实际原种子构造同一层内字母表与全程序域

种子 C 及其枚举不改变。由实际极限层的 Kuratowski 配对闭包，
回收三类指令的全部成员均在 W；随后真正构造 Q、Seq(Q) 和
原 Seq(Q)×ω。Q⊆W 不作为额外公理，也不升级为 Q∈W。
对象出口保留实际 Class Q、原字母表和全域规格，供闭包像构造消费。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramLevelDomain

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem alphabet_bound_l {B β W C ω t₀ t₁ t₂ Q : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hCW : ∀ x, mem_l hℳ x C → mem_l hℳ x W)
    (hωW : ∀ x, mem_l hℳ x ω → mem_l hℳ x W)
    (h₀ : mem_l hℳ t₀ W) (h₁ : mem_l hℳ t₁ W) (h₂ : mem_l hℳ t₂ W)
    (hQ : ∀ q, mem_l hℳ q Q ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l C ω t₀ t₁ t₂ q) :
    ∀ q, mem_l hℳ q Q → mem_l hℳ q W := by
  intro q hq
  rcases (hQ q).mp hq with ⟨a, ha, hCode⟩ | ⟨k, hk, hCode⟩ |
    ⟨k, l, p, hk, hl, hPair, hCode⟩
  · exact PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW h₀ (hCW a ha) hCode
  · exact PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW h₁ (hωW k hk) hCode
  · have hp := PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW
      (hωW k hk) (hωW l hl) hPair
    exact PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW h₂ hp hCode

theorem exists_l {B β W C ω t₀ t₁ t₂ : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ B C)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ B ω)
    (hCW : ∀ x, mem_l hℳ x C → mem_l hℳ x W)
    (hωW : ∀ x, mem_l hℳ x ω → mem_l hℳ x W)
    (h₀ : mem_l hℳ t₀ W) (h₁ : mem_l hℳ t₁ W) (h₂ : mem_l hℳ t₂ W) :
    ∃ Q S P, PowerlessRelativeClassCorrespondence.member_l hℳ B Q ∧
      (∀ q, mem_l hℳ q Q ↔ PowerlessRelativeFiniteProgramAlphabet.instruction_l C ω t₀ t₁ t₂ q) ∧
      (∀ q, mem_l hℳ q Q → mem_l hℳ q W) ∧
      PowerlessRelativeFiniteProgramDomain.domain_l B ω Q S P := by
  have hWC := PowerlessRelativeLevelClosure.class_l hℳ hB hW
  have ht₀ := PowerlessRelativeClassCorrespondence.transitive_l hℳ hB hWC h₀
  have ht₁ := PowerlessRelativeClassCorrespondence.transitive_l hℳ hB hWC h₁
  have ht₂ := PowerlessRelativeClassCorrespondence.transitive_l hℳ hB hWC h₂
  obtain ⟨Q, hQ, hAlphabet⟩ := PowerlessRelativeFiniteProgramAlphabet.exists_l hB hC hωC ht₀ ht₁ ht₂
  obtain ⟨S, P, hDomain⟩ := PowerlessRelativeFiniteProgramDomain.exists_l hB hω hωC hQ
  exact ⟨Q, S, P, hQ, hAlphabet,
    alphabet_bound_l hB hβ hW hCW hωW h₀ h₁ h₂ hAlphabet, hDomain⟩

def conclusion_m {Δ : SortContext ℒ} (B C W ω t₀ t₁ t₂ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    let Q : Term ℒ [.set, .set, .set] Δ .set := .bvar (.there (.there .here))
    let S := .bvar (.there .here)
    let P := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.class_m (up₃ B) Q) <|
      .conj (PowerlessRelativeFiniteProgramAlphabet.alphabet_m
        (up₃ C) (up₃ ω) (up₃ t₀) (up₃ t₁) (up₃ t₂) Q) <|
        .conj (ThirdOrderTheory.subset_m Q (up₃ W))
          (PowerlessRelativeFiniteProgramDomain.domain_m (up₃ B) (up₃ ω) Q S P)

def schema_m {Δ : SortContext ℒ} (B β C W ω t₀ t₁ t₂ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
          .imp (SecondOrderOmegaSyntax.omega_m ω) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
              .imp (ThirdOrderTheory.subset_m C W) <|
                .imp (ThirdOrderTheory.subset_m ω W) <|
                  .imp (SecondOrderObjectSyntax.member_m t₀ W) <|
                    .imp (SecondOrderObjectSyntax.member_m t₁ W) <|
                      .imp (SecondOrderObjectSyntax.member_m t₂ W)
                        (conclusion_m B C W ω t₀ t₁ t₂)

def sentence_m {Δ : SortContext ℒ} (B β C W ω t₀ t₁ t₂ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β C W ω t₀ t₁ t₂)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β C W ω t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    (sentence_m B β C W ω t₀ t₁ t₂).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    subset_formula_l, PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₃, up₂, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hB hβ hW hC hω hωC hCW hωW h₀ h₁ h₂
  exact exists_l hB hβ hW hC hω hωC hCW hωW h₀ h₁ h₂

theorem derives_m {Δ : SortContext ℒ} (B β C W ω t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B β C W ω t₀ t₁ t₂)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B β C W ω t₀ t₁ t₂)

#print axioms alphabet_bound_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramLevelDomain
