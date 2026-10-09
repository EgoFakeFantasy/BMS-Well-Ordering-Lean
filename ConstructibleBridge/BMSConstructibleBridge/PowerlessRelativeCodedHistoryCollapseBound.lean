import BMSConstructibleBridge.PowerlessRelativeCodedHistoryCollapseDerives
import BMSConstructibleBridge.PowerlessRelativeCollapseStageIndex
import BMSConstructibleBridge.PowerlessRelativeLevelMemberIndexBound
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseOrdinalBound

/-! # 同一实际坍缩的有界原阶段覆盖

保留原共同族中捕获的完整赋值在 MemberI/MemberW 的真值，再沿原 H
运输整份赋值。源层对象属于 W 给出源阶段严格低于 Ω；序数像不增大
给出目标阶段严格低于同一个 Ω。由原层单调性得 T⊆W，并从精确阶段集
规格得 J⊆Ω。原 Z₂ Derives 保留原来源守卫，不预供这些界或 ClassH。
J⊆Ω 不是 J∈Ω；严格高度、完整 Collection 和最终 BMS 推导仍待证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCodedHistoryCollapseBound

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteHullCodedCoverage (context_m variable_m)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 原阶段界和原层资格共用同一组 H 像见证，未替换给定 T/H。 -/
theorem stage_l (K : source_coding_l hℳ)
    {I₀ W₀ T H Ω : type_l hℳ} {hI : ∃ x, mem_l hℳ x I₀}
    {hW : ∃ x, mem_l hℳ x W₀} {hT : ∃ x, mem_l hℳ x T}
    {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (ζ : Env 𝒱 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI) [] Δ)
    (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hIW : subset_l (ℳ := 𝒱) I₀ W₀) (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (B ω : PowerlessMemberStructure.type_l (ℳ := 𝒱) I₀)
    (hB : ∀ x, mem_l hℳ x B.val → ∀ y, mem_l hℳ y x → mem_l hℳ y B.val)
    (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B.val ω.val Ω)
    (hLevel : PowerlessRelativeHierarchySemantics.level_l hℳ B.val Ω W₀)
    (hBI : ∀ x, mem_l hℳ x B.val → mem_l hℳ x I₀)
    (hωI : ∀ x, mem_l hℳ x ω.val → mem_l hℳ x I₀)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I₀)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I₀ T H)
    (hElem : (PowerlessRelativeFiniteElementarity.form_m Φ I W τ).satisfies ζ) :
    ∀ x : PowerlessMemberStructure.type_l (ℳ := 𝒱) T,
      ∃ α C, mem_l hℳ α T ∧ mem_l hℳ α Ω ∧ mem_l hℳ C T ∧
        PowerlessRelativeHierarchySemantics.level_l hℳ B.val α C ∧ mem_l hℳ x.val C := by
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hTransW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W₀ :=
    fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hB hLevel x hx y hy
  have hTransT : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) T :=
    fun x y hx hy => hH.1 x hx y hy
  have hClosedW := PowerlessRelativeLimitOperationClosure.closed_l hℳ hB
    (PowerlessRelativeCutoffLimit.limit_l K hB hω hΩ) hLevel
  have hClosedT := PowerlessRelativeMembershipCollapseClosure.closed_l hH hClosed
  have hFixedB := PowerlessRelativeMembershipCollapseBase.base_l hℳ
    B.val I₀ T H hB hBI hH.2.1 hH.2.2.2.1 B.property
  have hFixedω := PowerlessRelativeMembershipCollapseBase.base_l hℳ
    ω.val I₀ T H (fun x hx y hy => SecondOrderOmegaTransitive.member_l hℳ hω hx hy)
    hωI hH.2.1 hH.2.2.2.1 ω.property
  have hR := PowerlessMemberCollapseTransport.graph_l (hI := hI) (hT := hT)
    H hH.2.1 hH.2.2.1 hH.2.2.2.2.1 hH.2.2.2.2.2
  have hCoverElem := PowerlessRelativeFiniteElementarity.subfamily_formula_l
    (PowerlessRelativeFiniteHullCodedCoverage.family_m Δ) Φ hΦ ζ I W τ hElem
  intro x
  obtain ⟨z, hz, hzx⟩ := hH.2.2.1 x.val x.property
  let z₀ : PowerlessMemberStructure.type_l (ℳ := 𝒱) I₀ := ⟨z, hz⟩
  have hCover := PowerlessRelativeMemberCodedCoverage.exists_l (hW₀ := hW) K
    (PowerlessSourceInclusion.inclusion_l hIW B)
    (PowerlessSourceInclusion.inclusion_l hIW ω)
    (PowerlessSourceInclusion.inclusion_l hIW z₀) hB hω hΩ hLevel
  obtain ⟨η, hηB, hηω, hηx, hPI, hPW⟩ := PowerlessRelativeFiniteHullCodedCoverage.capture_env_l
    (hI := hI) (hW := hW) ζ I W τ ν hτ hIW hI₀ hW₀
    (PowerlessRelativeCodedHistoryCollapseReading.ext_l hW hTransW) B ω z₀ hCoverElem hCover
  let θ := PowerlessSourceInclusion.env_l (hU := hW) hIW η
  let v := fun i : Fin 20 => θ.boundVal (variable_m i)
  have hBV : (v 19).val = B.val := congrArg Subtype.val hηB
  have hωV : (v 18).val = ω.val := congrArg Subtype.val hηω
  have hPointW := (PowerlessRelativeFiniteHullCodedCoverage.matrix_formula_l
    (PowerlessRelativeCodedHistoryCollapseReading.ext_l hW hTransW) θ).mp hPW
  have hRawW := PowerlessMemberCodedHistoryReading.point_l (hW₀ := hW) K hTransW hClosedW
    (v 19) (v 18) (v 17) (v 16) (v 15) (v 14) (v 13) (v 12) (v 11) (v 10)
    (v 9) (v 8) (v 7) (v 6) (v 5) (v 4) (v 3) (v 2) (v 1) (v 0)
    (hωV.symm ▸ hω) hPointW
  have hSourceLevel : PowerlessRelativeHierarchySemantics.level_l hℳ B.val (v 16).val (v 15).val :=
    hBV ▸ (PowerlessRawCodedHistoryReading.level_l K (hωV.trans hωEq) hRawW).1
  have hαΩ := PowerlessRelativeLevelMemberIndexBound.below_l hB hSourceLevel hLevel (v 15).property
  obtain ⟨ξ, hξ⟩ := PowerlessMemberCollapseTransport.env_exists_l hR.left_total_l η
  let w := fun i : Fin 20 => ξ.boundVal (variable_m i)
  have hPointT := (PowerlessRelativeFiniteHullCodedCoverage.matrix_formula_l
    (PowerlessRelativeCodedHistoryCollapseReading.ext_l hT hTransT) ξ).mp
      ((PowerlessMemberCollapseTransport.formula_l hR
        (PowerlessRelativeFiniteHullCodedCoverage.matrix_m Δ) η ξ hξ).mp hPI)
  have hBImage := hξ.1 (variable_m 19)
  change SecondOrderFunctionObjects.value_l hℳ H (η.boundVal (variable_m 19)).val (w 19).val at hBImage
  rw [hηB] at hBImage
  have hBTarget := SecondOrderFunctionProperties.value_unique_l hℳ hH.2.1 hBImage hFixedB
  have hωImage := hξ.1 (variable_m 18)
  change SecondOrderFunctionObjects.value_l hℳ H (η.boundVal (variable_m 18)).val (w 18).val at hωImage
  rw [hηω] at hωImage
  have hωTarget := SecondOrderFunctionProperties.value_unique_l hℳ hH.2.1 hωImage hFixedω
  have hxImage := hξ.1 (variable_m 17)
  change SecondOrderFunctionObjects.value_l hℳ H (η.boundVal (variable_m 17)).val (w 17).val at hxImage
  rw [hηx] at hxImage
  have hxTarget := SecondOrderFunctionProperties.value_unique_l hℳ hH.2.1 hxImage hzx
  have hαβ : SecondOrderFunctionObjects.value_l hℳ H (v 16).val (w 16).val :=
    hξ.1 (variable_m 16)
  have hβΩ : mem_l hℳ (w 16).val Ω := by
    rcases PowerlessRelativeMembershipCollapseOrdinalBound.le_l hH
        (η.boundVal (variable_m 16)).property hαβ
        (PowerlessRelativeLevelClosure.ordinal_l hℳ hSourceLevel) with h | h
    · exact h.symm ▸ hαΩ
    · exact (PowerlessRelativeLevelClosure.ordinal_l hℳ hLevel).transitive (v 16).val hαΩ (w 16).val h
  have hRawT := PowerlessMemberCodedHistoryReading.point_l (hW₀ := hT) K hTransT hClosedT
    (w 19) (w 18) (w 17) (w 16) (w 15) (w 14) (w 13) (w 12) (w 11) (w 10)
    (w 9) (w 8) (w 7) (w 6) (w 5) (w 4) (w 3) (w 2) (w 1) (w 0)
    (hωTarget.symm ▸ hω) hPointT
  rw [hBTarget, hωTarget, hxTarget] at hRawT
  exact ⟨(w 16).val, (w 15).val, (w 16).property, hβΩ, (w 15).property,
    (PowerlessRawCodedHistoryReading.level_l K hωEq hRawT).1, hRawT.2.2.1⟩

/-- 精确阶段集的界是包含于 Ω，而不是严格小于 Ω。 -/
def result_m {Γ Δ : SortContext ℒ} (B T W ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (ThirdOrderTheory.subset_m T W) <| .existsE .set <|
    .conj (PowerlessRelativeOrdinalCutoff.first_m (up B) (up ω) (.bvar .here)) <|
      .conj (PowerlessRelativeHierarchySyntax.level_m (up B) (.bvar .here) (up W)) <|
        .forallE .set <| .imp
          (PowerlessRelativeCollapseStageIndex.spec_m (up (up B)) (up (up T)) (.bvar .here))
          (ThirdOrderTheory.subset_m (.bvar .here) (.bvar (.there .here)))

def result_l (B T W ω : type_l hℳ) : Prop :=
  (∀ x, mem_l hℳ x T → mem_l hℳ x W) ∧ ∃ Ω,
    PowerlessRelativeOrdinalCutoff.first_l B ω Ω ∧
    PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W ∧
    ∀ J, PowerlessRelativeCollapseStageIndex.spec_l B T J → ∀ a, mem_l hℳ a J → mem_l hℳ a Ω

theorem result_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (ζ : Env 𝒱 Γ Δ) (B T W ω : Term ℒ Γ Δ .set) :
    (result_m B T W ω).satisfies ζ ↔ result_l (B.eval ζ) (T.eval ζ) (W.eval ζ) (ω.eval ζ) := by
  simp only [result_m, result_l, Formula.satisfies, ThirdOrderSemantics.subset_formula_l,
    ThirdOrderSemantics.subset_l, ThirdOrderSemantics.member_l,
    PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeCollapseStageIndex.spec_formula_l K,
    up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

theorem target_l (K : source_coding_l hℳ)
    {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (ζ : Env 𝒱 [] Ε) (I W B ω : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) (T H : type_l hℳ)
    (hSource : (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W).satisfies ζ)
    (hIW : subset_l (ℳ := 𝒱) (I.eval ζ) (W.eval ζ))
    (hParams : (parameters_m Δ I τ).satisfies ζ)
    (hB : mem_l hℳ (B.eval ζ) (I.eval ζ)) (hωI : mem_l hℳ (ω.eval ζ) (I.eval ζ))
    (hBI : subset_l (ℳ := 𝒱) (B.eval ζ) (I.eval ζ))
    (hωSub : subset_l (ℳ := 𝒱) (ω.eval ζ) (I.eval ζ))
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) (I.eval ζ))
    (hH : PowerlessRelativeMembershipCollapse.spec_l (I.eval ζ) T H)
    (hElem : (PowerlessRelativeFiniteElementarity.form_m Φ I W τ).satisfies ζ) :
    result_l (B.eval ζ) T (W.eval ζ) (ω.eval ζ) := by
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
  let B₀ : PowerlessMemberStructure.type_l (ℳ := 𝒱) (I.eval ζ) := ⟨B.eval ζ, hB⟩
  let ω₀ : PowerlessMemberStructure.type_l (ℳ := 𝒱) (I.eval ζ) := ⟨ω.eval ζ, hωI⟩
  have hStage := stage_l (hI := hI) (hW := hW) (hT := hT) K Φ hΦ ζ I W τ ν (fun _ => rfl)
    hIW rfl rfl B₀ ω₀ hBase hω hΩ hLevel hBI hωSub hClosed hH hElem
  have hTW (x : type_l hℳ) (hx : mem_l hℳ x T) : mem_l hℳ x (W.eval ζ) := by
    obtain ⟨α, C, _, hα, _, hC, hxC⟩ := hStage ⟨x, hx⟩
    exact PowerlessRelativeLevelClosure.subset_l hℳ hBase hα hC hLevel x hxC
  refine ⟨hTW, Ω, hΩ, hLevel, ?_⟩
  intro J hJ a ha
  obtain ⟨_, C, hCT, hC⟩ := (hJ a).mp ha
  exact PowerlessRelativeLevelMemberIndexBound.below_l hBase hC hLevel (hTW C hCT)

def schema_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (I W T H B ω : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  .imp (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W) <|
    .imp (ThirdOrderTheory.subset_m I W) <| .imp (parameters_m Δ I τ) <|
      .imp (SecondOrderObjectSyntax.member_m B I) <| .imp (SecondOrderObjectSyntax.member_m ω I) <|
        .imp (ThirdOrderTheory.subset_m B I) <| .imp (ThirdOrderTheory.subset_m ω I) <|
          .imp (PowerlessRelativeFiniteHullAssignments.closed_m I) <|
            .imp (PowerlessRelativeMembershipCollapse.spec_m I T H) <|
              .imp (PowerlessRelativeFiniteElementarity.form_m Φ I W τ) (result_m B T W ω)

def sentence_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (I W T H B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ I W T H B ω τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (I W T H B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    (sentence_m Φ I W T H B ω τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ζ hSource hIW hParams hB hωI hBI hωSub hClosed hH hElem
  apply (result_formula_l K ζ B T W ω).mpr
  exact target_l K Φ hΦ ζ I W B ω τ (T.eval ζ) (H.eval ζ) hSource
    ((ThirdOrderSemantics.subset_formula_l ζ I W).mp hIW) hParams hB hωI
    ((ThirdOrderSemantics.subset_formula_l ζ B I).mp hBI)
    ((ThirdOrderSemantics.subset_formula_l ζ ω I).mp hωSub)
    ((PowerlessRelativeFiniteHullAssignments.closed_formula_l ζ I).mp hClosed)
    ((PowerlessRelativeMembershipCollapse.spec_formula_l ζ I T H).mp hH) hElem

theorem derives_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (I W T H B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m Φ I W T H B ω τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ Φ hΦ I W T H B ω τ)

#print axioms stage_l
#print axioms result_formula_l
#print axioms target_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCodedHistoryCollapseBound
