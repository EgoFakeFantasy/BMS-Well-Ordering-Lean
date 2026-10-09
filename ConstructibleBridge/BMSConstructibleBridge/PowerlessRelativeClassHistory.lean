import BMSConstructibleBridge.PowerlessRelativeClassCofinalParameterBounds
import BMSConstructibleBridge.PowerlessRelativeCutoffClassHistory
import BMSConstructibleBridge.PowerlessRelativeCofinalDefGraph
import BMSConstructibleBridge.SecondOrderOmegaOrdinal

/-! # 任意内部序数上的实际 Class 原历史

背景为原 Z₂，语言为纯隶属 ℒ。对任意实际序数 α，先构造严格更高的
共尾极限母层，再构造其完整原 Def 图。原预算归纳给同一历史图的 Class
身份，保留原 Def 后继及精确极限方程，不需要首不可数 Ω 或类内枚举。

这里只闭合长历史的实际存在；不是完整 Class Collection 或 BMS 终局。
所有见证留在 Prop，末尾原图翻译接口给出正式 Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassHistory

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up (up t)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

theorem exists_l (K : source_coding_l hℳ) {B ω α : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hα : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) α) :
    ∃ β U, mem_l hℳ α β ∧ PowerlessRelativeHierarchySemantics.limit_l hℳ β ∧
      PowerlessRelativeCofinalLimitBounds.cofinal_l β ∧
      PowerlessRelativeHierarchySemantics.level_l hℳ B β U ∧ mem_l hℳ B U ∧ mem_l hℳ ω U ∧
      ∃ D f : type_l hℳ B, PowerlessRelativeCofinalDefGraph.graph_l U D.val ∧
        PowerlessRelativeHierarchySemantics.history_l hℳ B α f.val U ∧
        PowerlessHierarchyLightHistory.history_l hℳ B D.val α U f.val := by
  have hωEq : ω = K.omega := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  let B₀ : type_l hℳ B := ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  let ω₀ : type_l hℳ B := ⟨ω, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (hωEq.symm ▸ SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  let η : Env (structure_l hℳ B hBase) [] [.set] := Env.empty |>.pushFree ω₀
  obtain ⟨β, U, hαβ, hLimit, hCofinal, hU, hBU, hParams⟩ :=
    PowerlessRelativeClassCofinalParameterBounds.exists_l η B₀ α hα
  have hωU : mem_l hℳ ω U := hParams .set .here
  have hKωU : mem_l hℳ K.omega U := hωEq ▸ hωU
  obtain ⟨D, hD, hRead⟩ := PowerlessRelativeCofinalDefFunction.exists_l
    hBase K hLimit hU hCofinal hKωU
  have hβ := PowerlessRelativeLevelClosure.ordinal_l hℳ hU
  obtain ⟨f, hf⟩ := PowerlessRelativeCutoffClassHistory.class_exists_l hℳ K hBase D hRead hα hU
    (fun a ha => hβ.transitive α hαβ a ha)
  exact ⟨β, U, hαβ, hLimit, hCofinal, hU, hBU, hωU, D, f, ⟨hD, hRead⟩, hf,
    PowerlessHierarchyLightHistoryUnique.from_original_l hℳ hRead (fun _ hx => hx) hf⟩

def result_m {Γ Δ : SortContext ℒ} (B ω α : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    let β : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set :=
      .bvar (.there (.there (.there .here)))
    let U := .bvar (.there (.there .here))
    let D := .bvar (.there .here)
    let f := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.class_m (up₄ B) D) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (up₄ B) f) <|
        .conj (SecondOrderObjectSyntax.member_m (up₄ α) β) <|
          .conj (PowerlessRelativeHierarchySyntax.limit_m β) <|
            .conj (PowerlessRelativeCofinalLimitBounds.cofinal_m β) <|
              .conj (PowerlessRelativeHierarchySyntax.level_m (up₄ B) β U) <|
                .conj (SecondOrderObjectSyntax.member_m (up₄ B) U) <|
                  .conj (SecondOrderObjectSyntax.member_m (up₄ ω) U) <|
                    .conj (PowerlessRelativeCofinalDefGraph.graph_m U D) <|
                      .conj (PowerlessRelativeHierarchySyntax.history_m (up₄ B) (up₄ α) f U)
                        (PowerlessHierarchyLightHistory.formula_m (up₄ B) D (up₄ α) U f)

theorem result_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B ω α : Term ℒ Γ Δ .set) :
    (result_m B ω α).satisfies η ↔ ∃ β U D f : Raw,
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) D ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) f ∧
      mem_l hℳ (α.eval η) β ∧ PowerlessRelativeHierarchySemantics.limit_l hℳ β ∧
      PowerlessRelativeCofinalLimitBounds.cofinal_l β ∧
      PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) β U ∧
      mem_l hℳ (B.eval η) U ∧ mem_l hℳ (ω.eval η) U ∧
      PowerlessRelativeCofinalDefGraph.graph_l U D ∧
      PowerlessRelativeHierarchySemantics.history_l hℳ (B.eval η) (α.eval η) f U ∧
      PowerlessHierarchyLightHistory.history_l hℳ (B.eval η) D (α.eval η) U f := by
  simp only [result_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeCofinalLimitBounds.cofinal_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeCofinalDefGraph.graph_formula_l K,
    PowerlessRelativeHierarchySemantics.history_formula_l K,
    PowerlessHierarchyLightHistory.reading_formula_l hℳ, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up₄, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let α : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  let B := .fvar (.there (.there .here))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.ordinal_m α) (result_m B ω α)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    result_formula_l K, Term.eval]
  intro hBase hω hα
  obtain ⟨β, U, hαβ, hLimit, hCofinal, hU, hBU, hωU, D, f, hD, hf, hLight⟩ :=
    exists_l K hBase hω hα
  exact ⟨β, U, D.val, f.val, D.property, f.property, hαβ, hLimit, hCofinal,
    hU, hBU, hωU, hD, hf, hLight⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms exists_l
#print axioms result_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassHistory
