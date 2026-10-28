import BMSConstructibleBridge.SecondOrderRelativeHierarchyFormula
import BMSConstructibleBridge.SecondOrderWellFoundedRecursion

/-! # 原 Z₂ 中的相对层次历史

按模型内关系递归，得到一个实际实数编码的所有阶段。内部良基归纳应用于
实际“每一行的零根无内部下降链”公式，包含非标准阶段数，不使用宿主 Acc。
基图、关系良基、传递及非自返条件仍需调用者在应用时证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchy

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def spec_l (B R S : set_l ℳ) : Prop :=
  ∀ n W, SecondOrderSections.spec_l S n W → SecondOrderRelativeHierarchyStep.spec_l B R S n W

private theorem stage_formula_l (hℳ : Theory.Models ℳ theory_m) (B R H W : set_l ℳ) (n : num_l ℳ) :
    SecondOrderPointwiseOperator.stage_l SecondOrderRelativeHierarchyFormula.formula_m
      (((Env.empty (M := ℳ)).pushFree B).pushFree R) H n W ↔
      SecondOrderRelativeHierarchyStep.spec_l B R H n W :=
  SecondOrderRelativeHierarchyFormula.formula_l hℳ _

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (B R : set_l ℳ)
    (hWf : ∀ n, SecondOrderDomain.wf_l R n)
    (hTrans : ∀ a b c, relation_l R a b → relation_l R b c → relation_l R a c)
    (hIrrefl : ∀ n, ¬relation_l R n n) : ∃ S, spec_l B R S := by
  let φ := SecondOrderRelativeHierarchyFormula.formula_m
  let η := ((Env.empty (M := ℳ)).pushFree B).pushFree R
  have hAsymm : ∀ a b, relation_l R a b → ¬relation_l R b a :=
    fun a b hab hba => hIrrefl a (hTrans a b a hab hba)
  have hLocal : SecondOrderWellFoundedAgreement.local_l
      (SecondOrderSetOperator.relation_l (SecondOrderPointwiseOperator.formula_m φ) η) R := by
    apply SecondOrderPointwiseOperator.local_l
    intro H K n h W
    rw [stage_formula_l hℳ, stage_formula_l hℳ]
    exact ⟨SecondOrderRelativeHierarchyStep.transfer_l hℳ h,
      SecondOrderRelativeHierarchyStep.transfer_l hℳ (fun i hi t => (h i hi t).symm)⟩
  obtain ⟨S, hS, _⟩ := SecondOrderWellFoundedRecursion.exists_l hℳ
    (SecondOrderPointwiseOperator.formula_m φ)
    (SecondOrderPointwiseOperator.pure_m φ SecondOrderRelativeHierarchyFormula.pure_m) η R
    hWf hTrans hIrrefl hLocal (SecondOrderPointwiseOperator.total_l hℳ φ
      SecondOrderRelativeHierarchyFormula.pure_m η)
  have hTotal : ∀ n, ∃! W, SecondOrderPointwiseOperator.stage_l φ η S n W := by
    intro n
    obtain ⟨W, hW, hUnique⟩ := SecondOrderRelativeHierarchyStep.exists_l hℳ B R S n hAsymm
    exact ⟨W, (stage_formula_l hℳ B R S W n).mpr hW,
      fun Y hY => hUnique Y ((stage_formula_l hℳ B R S Y n).mp hY)⟩
  have hRows := SecondOrderPointwiseOperator.rows_l φ η hS hTotal
  refine ⟨S, fun n W hW => ?_⟩
  obtain ⟨Y, hY, hRow⟩ := hRows n
  have hEq := SecondOrderSections.unique_l hℳ hW hRow
  subst W
  exact (stage_formula_l hℳ B R S Y n).mp hY

def rows_m : Formula signature_m [] [.num, .set] :=
  .forallE .set <| .imp
    (SecondOrderSections.formula_m (.fvar (.there .here)) (.bvar .here) (.fvar .here))
    (GraphTranslation.domain_m (.bvar .here) (Term.app (σ := signature_m) .zero .nil))

theorem rows_pure_m : language_m rows_m = true := by
  have hSections := SecondOrderSections.pure_m (Γ := [.set]) (Δ := [.num, .set])
    (.fvar (.there .here)) (.bvar .here) (.fvar .here) rfl rfl rfl
  have hDomain := GraphTranslation.domain_pure_m (Γ := [.set]) (Δ := [.num, .set])
    (.bvar .here) (Term.app (σ := signature_m) .zero .nil) rfl rfl
  exact SecondOrderFormulaArguments.forall_pure_m .set _
    (SecondOrderFormulaArguments.imp_pure_m _ _ hSections hDomain)

theorem rows_formula_l (S : set_l ℳ) (n : num_l ℳ) :
    rows_m.satisfies (((Env.empty (M := ℳ)).pushFree S).pushFree n) ↔
      ∀ W, SecondOrderSections.spec_l S n W → SecondOrderDomain.wf_l W (zero_l ℳ) := by
  simp only [rows_m, Formula.satisfies, SecondOrderSections.formula_l,
    SecondOrderInterpretation.domain_l, Term.eval]
  rfl

theorem rows_wf_l (hℳ : Theory.Models ℳ theory_m) {B R S : set_l ℳ}
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ)) (hWf : ∀ n, SecondOrderDomain.wf_l R n)
    (hS : spec_l B R S) : ∀ n W, SecondOrderSections.spec_l S n W →
      SecondOrderDomain.wf_l W (zero_l ℳ) := by
  intro n
  apply (rows_formula_l S n).mp
  apply SecondOrderWellFoundedInduction.induction_l hℳ rows_m rows_pure_m
    ((Env.empty (M := ℳ)).pushFree S) R ?_ n (hWf n)
  intro k _ hPast
  apply (rows_formula_l S k).mpr
  intro W hW
  apply SecondOrderRelativeHierarchyStep.root_l hℳ hB _ (hS k W hW)
  intro i hi Y hY
  exact (rows_formula_l S i).mp (hPast i hi) Y hY

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchy
