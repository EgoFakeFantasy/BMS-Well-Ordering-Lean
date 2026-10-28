import BMSConstructibleBridge.SecondOrderRelativeHierarchyMonotonicity

/-! # 每个相对阶段保持指定基集

以实际子集公式作内部良基归纳。极限阶段的前驱由非最小性取得，所有行仍
来自同一实数历史；不使用宿主序数归纳或可数选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyBase

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderGraphSubsetFormula (subset_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def rows_m : Formula signature_m [] [.num, .set, .set] :=
  .forallE .set <| .imp
    (SecondOrderSections.formula_m (.fvar (.there .here)) (.bvar .here) (.fvar .here)) <|
    .imp (GraphTranslation.domain_m (.bvar .here) (Term.app (σ := signature_m) .zero .nil))
      (SecondOrderGraphSubsetFormula.formula_m (.fvar (.there (.there .here))) (.bvar .here)
        (Term.app (σ := signature_m) .zero .nil) (Term.app (σ := signature_m) .zero .nil))

theorem pure_m : language_m rows_m = true := by
  have hRow := SecondOrderSections.pure_m (Γ := [.set]) (Δ := [.num, .set, .set])
    (.fvar (.there .here)) (.bvar .here) (.fvar .here) rfl rfl rfl
  have hW := GraphTranslation.domain_pure_m (Γ := [.set]) (Δ := [.num, .set, .set])
    (.bvar .here) (Term.app (σ := signature_m) .zero .nil) rfl rfl
  have hSub := SecondOrderGraphSubsetFormula.pure_m (Γ := [.set]) (Δ := [.num, .set, .set])
    (.fvar (.there (.there .here))) (.bvar .here) (Term.app (σ := signature_m) .zero .nil)
    (Term.app (σ := signature_m) .zero .nil) rfl rfl rfl rfl
  exact SecondOrderFormulaArguments.forall_pure_m .set _
    (SecondOrderFormulaArguments.imp_pure_m _ _ hRow
      (SecondOrderFormulaArguments.imp_pure_m _ _ hW hSub))

theorem formula_l (hℳ : Theory.Models ℳ theory_m) (B S : set_l ℳ) (n : num_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ)) :
    rows_m.satisfies ((((Env.empty (M := ℳ)).pushFree B).pushFree S).pushFree n) ↔
      ∀ W, SecondOrderSections.spec_l S n W → ∀ hW : SecondOrderDomain.wf_l W (zero_l ℳ),
        subset_l ⟨B, zero_l ℳ, hB⟩ ⟨W, zero_l ℳ, hW⟩ := by
  constructor
  · intro h W hRow hW
    let η := ((((Env.empty (M := ℳ)).pushFree B).pushFree S).pushFree n).pushBound W
    have hRow' := (SecondOrderSections.formula_l η (.fvar (.there .here)) (.bvar .here) (.fvar .here)).mpr hRow
    have hW' := (SecondOrderInterpretation.domain_l η (.bvar .here) (Term.app (σ := signature_m) .zero .nil)).mpr hW
    exact (SecondOrderGraphSubsetFormula.formula_l hℳ η (.fvar (.there (.there .here))) (.bvar .here)
      (Term.app (σ := signature_m) .zero .nil) (Term.app (σ := signature_m) .zero .nil) hB hW).mp (h W hRow' hW')
  · intro h W hRow hW
    let η := ((((Env.empty (M := ℳ)).pushFree B).pushFree S).pushFree n).pushBound W
    have hRow' := (SecondOrderSections.formula_l η (.fvar (.there .here)) (.bvar .here) (.fvar .here)).mp hRow
    have hW' := (SecondOrderInterpretation.domain_l η (.bvar .here) (Term.app (σ := signature_m) .zero .nil)).mp hW
    exact (SecondOrderGraphSubsetFormula.formula_l hℳ η (.fvar (.there (.there .here))) (.bvar .here)
      (Term.app (σ := signature_m) .zero .nil) (Term.app (σ := signature_m) .zero .nil) hB hW').mpr (h W hRow' hW')

theorem contains_l (hℳ : Theory.Models ℳ theory_m) {B R S : set_l ℳ}
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ))
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩)
    (hWf : ∀ n, SecondOrderDomain.wf_l R n) (hS : SecondOrderRelativeHierarchy.spec_l B R S) :
    ∀ n W, SecondOrderSections.spec_l S n W → ∀ hW : SecondOrderDomain.wf_l W (zero_l ℳ),
      subset_l ⟨B, zero_l ℳ, hB⟩ ⟨W, zero_l ℳ, hW⟩ := by
  intro n
  apply (formula_l hℳ B S n hB).mp
  apply SecondOrderWellFoundedInduction.induction_l hℳ rows_m pure_m
    (((Env.empty (M := ℳ)).pushFree B).pushFree S) R ?_ n (hWf n)
  intro k _ hPast
  apply (formula_l hℳ B S k hB).mpr
  intro W hRow hW
  rcases hS k W hRow with ⟨_, rfl⟩ | ⟨i, Y, hi, hY, hDef⟩ | ⟨hLimit, G, P, hUnion⟩
  · exact fun _ hx => hx
  · have hYw := SecondOrderRelativeHierarchy.rows_wf_l hℳ hB hWf hS i Y hY
    have hContains := SecondOrderRelativeHierarchyMonotonicityStep.successor_contains_l hℳ
      ⟨Y, zero_l ℳ, hYw⟩
      (SecondOrderRelativeHierarchyTransitivity.transitive_l hℳ hB hBase hWf hS i Y hY hYw) hW hDef
    intro X hx
    exact hContains X ((formula_l hℳ B S i hB).mp (hPast i hi.1) Y hY hYw X hx)
  · classical
    have hPred : ∃ i, relation_l R i k := by
      by_contra hNone
      exact hLimit.1 (fun i hi => hNone ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hPred
    obtain ⟨Y, hY⟩ := SecondOrderSections.exists_l hℳ S i
    have hYw := SecondOrderRelativeHierarchy.rows_wf_l hℳ hB hWf hS i Y hY
    have hRows : SecondOrderPredecessorUnionSemantics.rows_wf_l R S k :=
      fun j _ Z hZ => SecondOrderRelativeHierarchy.rows_wf_l hℳ hB hWf hS j Z hZ
    intro X hx
    exact (SecondOrderPredecessorUnionSemantics.mem_l hℳ hUnion hRows X).mpr
      ⟨i, ⟨Y, zero_l ℳ, hYw⟩, hi, hY, rfl,
        (formula_l hℳ B S i hB).mp (hPast i hi) Y hY hYw X hx⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyBase
