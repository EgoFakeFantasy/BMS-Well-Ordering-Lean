import BMSConstructibleBridge.PowerlessRelativeClassCanonicalEdgeReading
import BMSConstructibleBridge.PowerlessRelativeClassFormulaInstances
import BMSConstructibleBridge.SecondOrderComparisonCoding
import BMSConstructibleBridge.SecondOrderCanonicalLevelDerives

/-! # 同一全局规范序的 Class 定义：原 Z₂ 对象推导

原 Z₂ 中先固定一个实际编码包，再量化所有 Class 左右端，证明
完整覆盖定义与原 raw 全局比较逐点相同。不存在逐输入重新选码的
Type 函数，也不预供比较历史或覆盖包；正式出口是原推导核 Derives。
这是同一数码程序读数的前置结果，不是 BMS 良序终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalEdgeDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassFormulaInstances (instance_m instance_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₃ (up₃ t)

private abbrev context_m : SortContext ℒ := [.set, .set, .set, .set, .set]

private def parameters_m {Γ Δ : SortContext ℒ} (B ω P₀ x y : Term ℒ Γ Δ .set) :
    Variable context_m .set → Term ℒ Γ Δ .set
  | .here => B
  | .there .here => ω
  | .there (.there .here) => P₀
  | .there (.there (.there .here)) => x
  | .there (.there (.there (.there .here))) => y

private def formula_m : Formula ℒ [] context_m :=
  PowerlessCanonicalCodedEdgeSyntax.edge_m (.fvar .here) (.fvar (.there .here))
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))

/-- 统一代码先固定，然后比较所有实际 Class 对象。 -/
def reading_m {Γ Δ : SortContext ℒ}
    (B ω P₀ e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let x : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let y := .bvar .here
    .imp (PowerlessRelativeHierarchySyntax.class_m (up₂ B) x) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m (up₂ B) y) <|
        .iff (instance_m formula_m (up₂ B) (parameters_m (up₂ B) (up₂ ω) (up₂ P₀) x y))
          (SecondOrderCanonicalClassOrder.edge_m (up₂ ω) (up₂ e) (up₂ t₁) (up₂ t₂) (up₂ t₃)
            (up₂ Pair) (up₂ Valid) (up₂ B) (up₂ P₀) x y)

private theorem reading_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} (K : source_coding_l hℳ)
    {Γ Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (B ω P₀ e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set)
    (hGuard : SecondOrderCanonicalLevelDerives.guard_l (B.eval η) (P₀.eval η))
    (hω : ω.eval η = K.omega) (he : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K
      (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η) (Valid.eval η))
    (hP₀ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (P₀.eval η)) :
    (reading_m B ω P₀ e t₁ t₂ t₃ Pair Valid).satisfies η := by
  simp only [reading_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    SecondOrderCanonicalClassOrder.edge_formula_l K, up₂, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro x y hx hy
  have hBase : ∀ z, mem_l hℳ z (B.eval η) → ∀ t,
      mem_l hℳ t z → mem_l hℳ t (B.eval η) :=
    fun z hz t ht => hGuard.2.1 z t hz ht
  let B₀ : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) :=
    ⟨B.eval η, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  let ω₀ : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) :=
    ⟨ω.eval η, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
      (hω.symm ▸ SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  let P₀₀ : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨P₀.eval η, hP₀⟩
  let x₀ : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨x, hx⟩
  let y₀ : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨y, hy⟩
  let ξ : Env (PowerlessRelativeClassStructure.structure_l hℳ (B.eval η) hBase) [] context_m :=
    Env.empty |>.pushFree y₀ |>.pushFree x₀ |>.pushFree P₀₀ |>.pushFree ω₀ |>.pushFree B₀
  let ζ := η.pushBound x |>.pushBound y
  let ν := parameters_m (up₂ B) (up₂ ω) (up₂ P₀) (.bvar (.there .here)) (.bvar .here)
  have hB : (up₂ B).eval ζ = B.eval η := by
    simp only [ζ, up₂, up, Term.eval_weakenBound]
  have hν : ∀ v, (ν v).eval ζ = (ξ.freeVal v).val := by
    intro v
    cases v with
    | here => simp only [ν, parameters_m, ζ, up₂, up, Term.eval_weakenBound]; rfl
    | there v => cases v with
      | here => simp only [ν, parameters_m, ζ, up₂, up, Term.eval_weakenBound]; rfl
      | there v => cases v with
        | here => simp only [ν, parameters_m, ζ, up₂, up, Term.eval_weakenBound]; rfl
        | there v => cases v with
          | here => rfl
          | there v => cases v with
            | here => rfl
            | there v => nomatch v
  rw [(instance_l K formula_m ζ (up₂ B) ν ξ hB hν), formula_m,
    PowerlessCanonicalCodedEdgeSyntax.edge_formula_l
      (PowerlessRelativeClassStructure.ext_l hℳ (B.eval η) hBase) ξ
      (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))]
  change PowerlessCanonicalCodedEdgeSyntax.edge_l
    (𝒩 := PowerlessRelativeClassStructure.structure_l hℳ (B.eval η) hBase) B₀ ω₀ P₀₀ x₀ y₀ ↔
    SecondOrderCanonicalClassOrder.edge_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η)
      (t₃.eval η) (Pair.eval η) (Valid.eval η) (B.eval η) (P₀.eval η) x y
  rw [hω, he]
  exact PowerlessRelativeClassCanonicalEdgeReading.edge_l (hBase := hBase)
    K ω₀ P₀₀ x₀ y₀ hω hCoding hGuard.1 hGuard.2.2.1 hGuard.2.2.2

private abbrev input_m : SortContext ℒ := [.set, .set, .set]
private abbrev B_m : Term ℒ [] input_m .set := .fvar .here
private abbrev ω_m : Term ℒ [] input_m .set := .fvar (.there .here)
private abbrev P₀_m : Term ℒ [] input_m .set := .fvar (.there (.there .here))

def schema_m : Formula ℒ [] input_m :=
  .imp (guard_m B_m P₀_m) <| .imp (SecondOrderOmegaSyntax.omega_m ω_m) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B_m P₀_m) <|
      .existsE .set <| .existsE .set <| .existsE .set <|
      .existsE .set <| .existsE .set <| .existsE .set <|
        reading_m (up₆ B_m) (up₆ ω_m) (up₆ P₀_m)
          (.bvar (.there (.there (.there (.there (.there .here))))))
          (.bvar (.there (.there (.there (.there .here)))))
          (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
          (.bvar (.there .here)) (.bvar .here)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, guard_formula_l, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K₀]
  intro hGuard hω hP₀
  have hΩ : omega_l (ℳ := SecondOrderQuotient.structure_l hℳ) (ω_m.eval η) :=
    (omega_formula_l η ω_m).mp ((SecondOrderOmegaSyntax.omega_l hℳ η ω_m).mpr hω)
  obtain ⟨K, e, t₁, t₂, t₃, Pair, Valid, hωEq, he, hCoding⟩ :=
    SecondOrderComparisonCoding.exists_l (hℳ := hℳ) hΩ
  refine ⟨e, t₁, t₂, t₃, Pair, Valid, ?_⟩
  apply reading_l K
  · simpa only [up₆, up₃, up₂, up, Term.eval_weakenBound] using hGuard
  · simpa only [up₆, up₃, up₂, up, Term.eval_weakenBound] using hωEq
  · exact he
  · exact hCoding
  · change PowerlessRelativeClassCorrespondence.member_l hℳ (B_m.eval η) (P₀_m.eval η)
    exact hP₀

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalEdgeDerives
