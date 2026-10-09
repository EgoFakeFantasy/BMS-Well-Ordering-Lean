import BMSConstructibleBridge.PowerlessRelativeCodedHistoryCollapseReading
import BMSConstructibleBridge.PowerlessRelativeSourceFamilyCodedCapture

/-! # 实际首 Ω 坍缩目标的原类与 Def 闭包对象推导

对象语言为纯隶属 ℒ，正式出口为原 num/set Z₂ 中 GraphTranslation 的
普通 Derives。原有限族 Φ 可继续扩展；两个完整覆盖模板的包含性只是
外部 AST 条件。原首 Ω 层、实际元素性与同一坍缩是闭句中的明确守卫。

源与目标成员域的非空性在证明内由基对象和同一 H 得到。源覆盖、目标
传递性、操作闭包、基集／ω 固定性及原历史均从真实守卫推出；未添加
目标已是 Class／层／完整源模型的前提。这是完整弱凝聚的输入原则，
不是已消去 hSources 的最终固定高度良序闭句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCodedHistoryCollapseDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 覆盖阶段和实际层对象同时属于 T，不只保留抽象 Class 成员性。 -/
def stage_m {Γ Δ : SortContext ℒ} (B T x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <|
    .conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up (up T))) <|
      .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up T))) <|
        .conj (PowerlessRelativeHierarchySyntax.level_m (up (up B))
          (.bvar (.there .here)) (.bvar .here))
          (SecondOrderObjectSyntax.member_m (up (up x)) (.bvar .here))

/-- 原商中的所有 T 成员均有原阶段覆盖，原 Def 的任意输出仍属于 T。 -/
def result_m {Γ Δ : SortContext ℒ} (B T : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up T)) <|
    .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
      .conj (stage_m (up B) (up T) (.bvar .here)) <|
      .forallE .set <| .imp
        (PowerlessMemberDefSyntax.global_m (.bvar (.there .here)) (.bvar .here))
        (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up T)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

def result_l (B T : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∀ x, mem_l hℳ x T → PowerlessRelativeClassCorrespondence.member_l hℳ B x ∧
    (∃ a y, mem_l hℳ a T ∧ mem_l hℳ y T ∧
      PowerlessRelativeHierarchySemantics.level_l hℳ B a y ∧ mem_l hℳ x y) ∧
    ∀ r, SecondOrderMemberDef.spec_l hℳ x r → mem_l hℳ r T

theorem stage_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (B T x : Term ℒ Γ Δ .set) :
    (stage_m B T x).satisfies ζ ↔ ∃ a y, mem_l hℳ a (T.eval ζ) ∧
      mem_l hℳ y (T.eval ζ) ∧
      PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval ζ) a y ∧ mem_l hℳ (x.eval ζ) y := by
  simp only [stage_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.level_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

theorem result_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (B T : Term ℒ Γ Δ .set) :
    (result_m B T).satisfies ζ ↔ result_l (B.eval ζ) (T.eval ζ) := by
  simp only [result_m, result_l, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    stage_formula_l K,
    PowerlessMemberDefDerives.formula_l K, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- B∈I 与 B⊆I、ω∈I 与 ω⊆I 分别保留，不能互相替代。 -/
def schema_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (I W T H B ω : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  .imp (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W) <|
    .imp (ThirdOrderTheory.subset_m I W) <|
      .imp (parameters_m Δ I τ) <|
        .imp (SecondOrderObjectSyntax.member_m B I) <|
          .imp (SecondOrderObjectSyntax.member_m ω I) <|
            .imp (ThirdOrderTheory.subset_m B I) <|
              .imp (ThirdOrderTheory.subset_m ω I) <|
                .imp (PowerlessRelativeFiniteHullAssignments.closed_m I) <|
                  .imp (PowerlessRelativeMembershipCollapse.spec_m I T H) <|
                    .imp (PowerlessRelativeFiniteElementarity.form_m Φ I W τ) (result_m B T)

def sentence_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (I W T H B ω : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ I W T H B ω τ)

/-- 原资格的实际消费接口，T/H 可由调用端在 Prop 中取得。 -/
theorem target_l (K : source_coding_l hℳ)
    {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (T H : SecondOrderQuotient.type_l hℳ)
    (hSource : (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W).satisfies ζ)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) (I.eval ζ) (W.eval ζ))
    (hParams : (parameters_m Δ I τ).satisfies ζ)
    (hB : mem_l hℳ (B.eval ζ) (I.eval ζ)) (hωI : mem_l hℳ (ω.eval ζ) (I.eval ζ))
    (hBI : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) (B.eval ζ) (I.eval ζ))
    (hωSub : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) (ω.eval ζ) (I.eval ζ))
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) (I.eval ζ))
    (hH : PowerlessRelativeMembershipCollapse.spec_l (I.eval ζ) T H)
    (hElem : (PowerlessRelativeFiniteElementarity.form_m Φ I W τ).satisfies ζ) :
    result_l (B.eval ζ) T := by
  obtain ⟨hBase, hω, Ω, hΩ, hLevel⟩ :=
    (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K ζ B ω W).mp hSource
  have hParameters := (parameters_formula_l Δ ζ I τ).mp hParams
  have hI : ∃ x, mem_l hℳ x (I.eval ζ) := ⟨B.eval ζ, hB⟩
  have hW : ∃ x, mem_l hℳ x (W.eval ζ) := ⟨B.eval ζ, hIW (B.eval ζ) hB⟩
  obtain ⟨b, hb, _⟩ := hH.2.1.2 (B.eval ζ) hB
  have hT : ∃ x, mem_l hℳ x T := ⟨b, hb.1⟩
  let ν : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) (I.eval ζ) hI) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => ⟨(τ v).eval ζ, hParameters .set v⟩ }
  let B₀ : PowerlessMemberStructure.type_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) (I.eval ζ) := ⟨B.eval ζ, hB⟩
  let ω₀ : PowerlessMemberStructure.type_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) (I.eval ζ) := ⟨ω.eval ζ, hωI⟩
  have hCover := PowerlessRelativeCodedHistoryCollapseReading.coverage_l
    (hI := hI) (hW := hW) (hT := hT) K Φ hΦ ζ I W τ ν (fun _ => rfl)
    hIW rfl rfl B₀ ω₀ hBase hω hΩ hLevel hBI hωSub hClosed hH hElem
  intro x hx
  have hPacket := hCover ⟨x, hx⟩
  exact ⟨PowerlessRelativeCodedHistoryCollapseReading.class_l K hPacket,
    PowerlessRelativeCodedHistoryCollapseReading.stage_l K hPacket,
    fun r hDef => PowerlessRelativeCodedHistoryCollapseReading.def_l K
      (fun x y hx hy => hH.1 x hx y hy) hPacket hDef⟩

/-- 任意原 Z₂ 模型的真实资格实例，不把成员结构的完整理论作为假设。 -/
theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (I W T H B ω : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    (sentence_m Φ I W T H B ω τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ζ hSource hIW hParams hB hωI hBI hωSub hClosed hH hElem
  apply (result_formula_l K ζ B T).mpr
  exact target_l K Φ hΦ ζ I W B ω τ (T.eval ζ) (H.eval ζ) hSource
    ((ThirdOrderSemantics.subset_formula_l ζ I W).mp hIW) hParams hB hωI
    ((ThirdOrderSemantics.subset_formula_l ζ B I).mp hBI)
    ((ThirdOrderSemantics.subset_formula_l ζ ω I).mp hωSub)
    ((PowerlessRelativeFiniteHullAssignments.closed_formula_l ζ I).mp hClosed)
    ((PowerlessRelativeMembershipCollapse.spec_formula_l ζ I T H).mp hH) hElem

theorem derives_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (I W T H B ω : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ I W T H B ω τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ Φ hΦ I W T H B ω τ)

#print axioms result_formula_l
#print axioms stage_formula_l
#print axioms target_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCodedHistoryCollapseDerives
