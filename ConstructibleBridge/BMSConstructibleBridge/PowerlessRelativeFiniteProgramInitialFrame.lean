import BMSConstructibleBridge.PowerlessRelativeClassBasicClosure
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramStep
import BMSConstructibleBridge.PowerlessRelativeLimitClosure
import BMSConstructibleBridge.PowerlessDefinableFiniteTraceDerives

/-! # 实际有限程序的空集初始帧

对象语言为纯隶属语言，背景为原 Z₂，正式出口为原核的图翻译推导。
从实际内部 ω 的归纳性取得原空集 e，再用实际 Class 的空集和
Kuratowski 配对闭包构造 a = (e, (e, e))。同一个 e、a 还留在给定
极限层 W 中；不预供初值，不假定内部 ω 外部标准，不抽取 Type 选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramInitialFrame

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 原空集及原记录关系的共同见证；Class 闭包不作为额外前提。 -/
theorem exists_l {B β W ω : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hωW : mem_l hℳ ω W) :
    ∃ e a, (∀ x, ¬mem_l hℳ x e) ∧
      PowerlessRelativeFiniteProgramStep.record_l e e e a ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B e ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B a ∧
      mem_l hℳ e W ∧ mem_l hℳ a W := by
  obtain ⟨e, he, heω⟩ := hω.1.1
  have heC := PowerlessRelativeClassBasicClosure.empty_l hℳ hB he
  have heW := PowerlessRelativeLevelClosure.transitive_l hℳ hB hW ω hωW e heω
  obtain ⟨a, ha⟩ := PowerlessRelativeFiniteProgramStep.record_exists_l e e e
  have haC := PowerlessRelativeFiniteProgramStep.record_class_l hB heC heC heC ha
  have haW : mem_l hℳ a W := by
    obtain ⟨p, hp, hpa⟩ := ha
    have hpW := PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW heW heW hp
    exact PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW heW hpW hpa
  exact ⟨e, a, he, ha, heC, haC, heW, haW⟩

def initial_m {Γ Δ : SortContext ℒ} (B W e a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
    .conj (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m B e) <|
        .conj (PowerlessRelativeHierarchySyntax.class_m B a) <|
          .conj (SecondOrderObjectSyntax.member_m e W) (SecondOrderObjectSyntax.member_m a W)

theorem initial_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B W e a : Term ℒ Γ Δ .set) :
    (initial_m B W e a).satisfies η ↔
      (∀ x, ¬mem_l hℳ x (e.eval η)) ∧
        PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η) ∧
        PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (e.eval η) ∧
        PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (a.eval η) ∧
        mem_l hℳ (e.eval η) (W.eval η) ∧ mem_l hℳ (a.eval η) (W.eval η) := by
  simp only [initial_m, Formula.satisfies, PowerlessDefinableFiniteTraceDerives.zero_formula_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

def conclusion_m {Δ : SortContext ℒ} (B W : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set <| .existsE .set <|
    initial_m (up₂ B) (up₂ W) (.bvar (.there .here)) (.bvar .here)

/-- 保留主路线原层和内部 ω 守卫，结论真正绑定两个初值。 -/
def schema_m {Δ : SortContext ℒ} (B β W ω : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .imp (SecondOrderOmegaSyntax.omega_m ω) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
            .imp (SecondOrderObjectSyntax.member_m ω W) (conclusion_m B W)

def sentence_m {Δ : SortContext ℒ} (B β W ω : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β W ω)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β W ω : Term ℒ [] Δ .set) :
    (sentence_m B β W ω).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    initial_formula_l K, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hB hβ hW hω _ hωW
  exact exists_l hB hβ hW hω hωW

theorem derives_m {Δ : SortContext ℒ} (B β W ω : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B β W ω)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B β W ω)

#print axioms exists_l
#print axioms initial_formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramInitialFrame
