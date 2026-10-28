import BMSConstructibleBridge.PowerlessRelativeClassCountableDoubleTail
import BMSConstructibleBridge.SecondOrderOrdinalLimitDerives

/-! # 首不可数截断以下的真实共尾极限

对象语言是纯隶属 ℒ，背景是原 Z₂。对任意 α∈Ω，先正规化实际
良基图，再构造原内部二维尾包络 γ。类内可数性严格推出 γ∈Ω，
原双尾成员规格给 α∈γ、非零极限和极限阶段共尾。全部图和范围
前提在本模块内构造，不留作调用端守卫；普通 Derives 覆盖任意模型。
此结论消去‘早共尾极限存在’缺口，不等于完整 cutoff Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffCofinalLimits

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

theorem exists_l (K : source_coding_l hℳ) {B ω Ω a : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω) (haΩ : mem_l hℳ a Ω) :
    ∃ γ : type_l hℳ, Ordinal γ ∧ mem_l hℳ γ Ω ∧ mem_l hℳ a γ ∧
      PowerlessRelativeHierarchySemantics.limit_l hℳ γ ∧
        PowerlessRelativeCofinalLimitBounds.cofinal_l γ := by
  have ha : Ordinal a := by
    apply SetTheory.Structure.IsOrdinal.mem hΩ.1
    exact haΩ
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hΩ' : PowerlessRelativeOrdinalCutoff.first_l B K.omega Ω := hωEq ▸ hΩ
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨S, hS⟩ := SecondOrderValidRootGraph.exists_l hℳ A.real
  have hW := SecondOrderValidRootGraph.wf_l hS
  have hEq : mk_l hℳ A = SecondOrderOrdinalDoubleTailOrder.base_l hℳ hW A.root :=
    (SecondOrderQuotient.eq_iff_l hℳ _ _).mpr
      (SecondOrderValidRootGraph.agrees_l hℳ hS A.root A.wf)
  obtain ⟨G, hG⟩ := SecondOrderOrdinalDoubleTailGraph.exists_l hℳ S A.root
  obtain ⟨C, hC⟩ := SecondOrderOrdinalDoubleTailRange.exists_l hℳ hG hW
  have hBound := PowerlessRelativeClassCountableDoubleTail.below_l (hBase := hBase) K hG hW
    (hEq ▸ ha) hΩ' (hEq ▸ haΩ) C hC
  have hOrd := (SecondOrderOrdinalDoubleTailCofinal.properties_l hℳ hG hW (hEq ▸ ha) C hC).1
  exact ⟨mk_l hℳ C, hOrd, hBound.1, hEq.symm ▸ hBound.2.1, hBound.2.2⟩

theorem cofinal_l (K : source_coding_l hℳ) {B ω Ω : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω) :
    PowerlessRelativeCofinalLimitBounds.cofinal_l Ω := by
  intro a haΩ
  obtain ⟨γ, _, hγΩ, haγ, hLimit, _⟩ := exists_l K hBase hω hΩ haΩ
  exact ⟨γ, hγΩ, haγ, hLimit⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def result_m {Γ Δ : SortContext ℒ} (Ω a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.ordinal_m (.bvar .here)) <|
    .conj (member_m (.bvar .here) (up Ω)) <| .conj (member_m (up a) (.bvar .here)) <|
      .conj (PowerlessRelativeHierarchySyntax.limit_m (.bvar .here))
        (PowerlessRelativeCofinalLimitBounds.cofinal_m (.bvar .here))

theorem result_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (Ω a : Term ℒ Γ Δ .set) :
    (result_m Ω a).satisfies η ↔ ∃ γ : type_l hℳ, Ordinal γ ∧ mem_l hℳ γ (Ω.eval η) ∧
      mem_l hℳ (a.eval η) γ ∧ PowerlessRelativeHierarchySemantics.limit_l hℳ γ ∧
        PowerlessRelativeCofinalLimitBounds.cofinal_l γ := by
  simp only [result_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l, PowerlessRelativeCofinalLimitBounds.cofinal_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval, SecondOrderQuotient.structure_l]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  let Ω := .fvar (.there (.there .here))
  let a := .fvar (.there (.there (.there .here)))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
        .imp (member_m a Ω) (result_m Ω a)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

def cofinal_schema_m : Formula ℒ [] [.set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  let Ω := .fvar (.there (.there .here))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω)
        (PowerlessRelativeCofinalLimitBounds.cofinal_m Ω)

def cofinal_sentence_m : Sentence ℒ := Metatheory.Formula.forall_close cofinal_schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    result_formula_l,
    member_m, Arguments.eval, Term.eval, SecondOrderQuotient.structure_l]
  exact fun hBase hω hΩ haΩ => exists_l K hBase hω hΩ haΩ

theorem cofinal_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    cofinal_sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [cofinal_schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeCofinalLimitBounds.cofinal_formula_l, Term.eval]
  exact fun hBase hω hΩ => cofinal_l K hBase hω hΩ

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

theorem cofinal_derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m cofinal_sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => cofinal_models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffCofinalLimits
