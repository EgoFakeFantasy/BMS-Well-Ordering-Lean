import BMSConstructibleBridge.PowerlessRelativeSourceFamilyCodedCapture
import BMSConstructibleBridge.PowerlessRelativeFiniteHullClosure
import BMSConstructibleBridge.PowerlessRelativeCodedHistoryCollapseReading

/-! # 同一实际有限族的操作闭包与内部 ω 覆盖

从原完整包在 MemberW 中的空集资格及 W 的传递性认同真实零码，
该见证仍属于同一个 I。四个实际操作公式给出 I 的闭包，再对纯成员
公式调用原 Z₂ 内部归纳，覆盖全部内部数字而非仅宿主标准数。
对象出口保留原来源和元素性守卫，但不预供 I 的闭包或 ω⊆I；
未断言严格凝聚高度、完整 Collection 或最终 BMS 良序闭句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullOmegaCoverage

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

/-- 第一自由槽为内部数，第二槽为同一个实际源域。 -/
def template_m : Formula ℒ [] [.set, .set] :=
  SecondOrderObjectSyntax.member_m (.fvar .here) (.fvar (.there .here))

theorem template_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (I n : carrier_l 𝒩) :
    template_m.satisfies ((Env.empty (M := 𝒩)).pushFree I |>.pushFree n) ↔ member_l 𝒩 n I := by
  simp only [template_m, SecondOrderObjectSyntax.member_m, Formula.satisfies,
    Arguments.eval, Term.eval]
  rfl

theorem induction_derives_m : Derives SecondOrderArithmetic.theory_m []
    (SecondOrderArithmetic.induction_m (GraphTranslation.form_m template_m)) :=
  GraphTranslation.induction_m template_m

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 零码与真实单点添加闭包足以覆盖模型的全部内部自然数。 -/
theorem omega_l (K : source_coding_l hℳ) {I : type_l hℳ}
    (h₀ : mem_l hℳ (numberCode_l K (SecondOrderModel.zero_l ℳ)).val I)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I) :
    ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I := by
  let η : Env 𝒱 [] [.set] := Env.empty.pushFree I
  have h := PowerlessBMSQuotientInduction.induction_l K template_m η
    ((template_formula_l (𝒩 := 𝒱) I _).mpr h₀) (by
      intro n hn
      have hnI : mem_l hℳ (numberCode_l K n).val I :=
        (template_formula_l (𝒩 := 𝒱) I _).mp hn
      exact (template_formula_l (𝒩 := 𝒱) I _).mpr
        (PowerlessRelativeFiniteHullAssignments.adjoin_l (hℳ := hℳ) hClosed hnI hnI
          (PowerlessBMSQuotientSuccessor.successor_l K n)))
  intro x hx
  obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x, hx⟩
  have hxEq : (numberCode_l K n).val = x := congrArg Subtype.val hn
  exact hxEq ▸ (template_formula_l (𝒩 := 𝒱) I _).mp (h n)

/-- 捕获空对象的真实成员证书，不要求源域传递或已经覆盖 ω。 -/
theorem zero_l (K : source_coding_l hℳ)
    {I₀ W₀ Ω : type_l hℳ} {hI : ∃ x, mem_l hℳ x I₀} {hW : ∃ x, mem_l hℳ x W₀}
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
    (hElem : (PowerlessRelativeFiniteElementarity.form_m Φ I W τ).satisfies ζ) :
    mem_l hℳ (numberCode_l K (SecondOrderModel.zero_l ℳ)).val I₀ := by
  have hTransW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W₀ :=
    fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hB hLevel x hx y hy
  have hCover := PowerlessRelativeMemberCodedCoverage.exists_l (hW₀ := hW) K
    (PowerlessSourceInclusion.inclusion_l hIW B)
    (PowerlessSourceInclusion.inclusion_l hIW ω)
    (PowerlessSourceInclusion.inclusion_l hIW B) hB hω hΩ hLevel
  have hCoverElem := PowerlessRelativeFiniteElementarity.subfamily_formula_l
    (PowerlessRelativeFiniteHullCodedCoverage.family_m Δ) Φ hΦ ζ I W τ hElem
  obtain ⟨a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G, hPoint⟩ :=
    PowerlessRelativeFiniteHullCodedCoverage.capture_l (hI := hI) (hW := hW)
      ζ I W τ ν hτ hIW hI₀ hW₀
      (PowerlessRelativeCodedHistoryCollapseReading.ext_l hW hTransW) B ω B hCoverElem hCover
  have he : PowerlessNatural.zero_l (ℳ := 𝒱) e.val := by
    intro x hx
    exact hPoint.2.2.2.2.2.1.1.1
      ⟨x, hTransW e.val x (hIW e.val e.property) hx⟩ hx
  have hEq : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x => iff_of_false (he x)
      (PowerlessBMSQuotientSuccessor.zero_l K x))
  exact hEq ▸ e.property

/-- 来源守卫与实际共同族给出两项基础资格，未预供这两个结论。 -/
theorem target_l (K : source_coding_l hℳ)
    {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (ζ : Env 𝒱 [] Ε) (I W B ω : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (hSource : (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W).satisfies ζ)
    (hIW : subset_l (ℳ := 𝒱) (I.eval ζ) (W.eval ζ))
    (hParams : (parameters_m Δ I τ).satisfies ζ)
    (hB : mem_l hℳ (B.eval ζ) (I.eval ζ)) (hωI : mem_l hℳ (ω.eval ζ) (I.eval ζ))
    (hElem : (PowerlessRelativeFiniteElementarity.form_m Φ I W τ).satisfies ζ) :
    PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) (I.eval ζ) ∧
      subset_l (ℳ := 𝒱) (ω.eval ζ) (I.eval ζ) := by
  obtain ⟨hBase, hω, Ω, hΩ, hLevel⟩ :=
    (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K ζ B ω W).mp hSource
  have hParameters := (parameters_formula_l Δ ζ I τ).mp hParams
  have hI : ∃ x, mem_l hℳ x (I.eval ζ) := ⟨B.eval ζ, hB⟩
  have hW : ∃ x, mem_l hℳ x (W.eval ζ) := ⟨B.eval ζ, hIW (B.eval ζ) hB⟩
  let ν : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) (I.eval ζ) hI) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => ⟨(τ v).eval ζ, hParameters .set v⟩ }
  let B₀ : PowerlessMemberStructure.type_l (ℳ := 𝒱) (I.eval ζ) := ⟨B.eval ζ, hB⟩
  let ω₀ : PowerlessMemberStructure.type_l (ℳ := 𝒱) (I.eval ζ) := ⟨ω.eval ζ, hωI⟩
  have h₀ := zero_l (hI := hI) (hW := hW) K Φ hΦ ζ I W τ ν (fun _ => rfl)
    hIW rfl rfl B₀ ω₀ hBase hω hΩ hLevel hElem
  have hTransW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) (W.eval ζ) :=
    fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hLevel x hx y hy
  have hClosed := PowerlessRelativeFiniteHullClosure.closure_l ζ I W τ
    (fun a b => SecondOrderPairObjects.pair_exists_l hℳ a b)
    (PowerlessRelativeFiniteHullClosure.binary_exists_l hℳ)
    (fun a b hz => SecondOrderQuotient.ext_l hℳ a b hz) hTransW
    (PowerlessRelativeFiniteHullClosure.limit_closed_l hℳ hBase
      (PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ) hLevel) hIW rfl rfl
    (PowerlessRelativeFiniteElementarity.subfamily_formula_l
      (PowerlessRelativeFiniteHullClosure.family_m Δ) Φ hΦ₀ ζ I W τ hElem)
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  exact ⟨hClosed, fun x hx => omega_l K h₀ hClosed x (hωEq ▸ hx)⟩

def schema_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (I W B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  .imp (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W) <|
    .imp (ThirdOrderTheory.subset_m I W) <| .imp (parameters_m Δ I τ) <|
      .imp (SecondOrderObjectSyntax.member_m B I) <| .imp (SecondOrderObjectSyntax.member_m ω I) <|
        .imp (PowerlessRelativeFiniteElementarity.form_m Φ I W τ) <|
          .conj (PowerlessRelativeFiniteHullAssignments.closed_m I) (ThirdOrderTheory.subset_m ω I)

def sentence_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (I W B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ I W B ω τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (I W B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    (sentence_m Φ I W B ω τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ζ hSource hIW hParams hB hωI hElem
  obtain ⟨hClosed, hωSub⟩ := target_l K Φ hΦ hΦ₀ ζ I W B ω τ hSource
    ((ThirdOrderSemantics.subset_formula_l ζ I W).mp hIW) hParams hB hωI hElem
  exact ⟨(PowerlessRelativeFiniteHullAssignments.closed_formula_l ζ I).mpr hClosed,
    (ThirdOrderSemantics.subset_formula_l ζ ω I).mpr hωSub⟩

theorem derives_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (I W B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m Φ I W B ω τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ Φ hΦ hΦ₀ I W B ω τ)

#print axioms template_formula_l
#print axioms induction_derives_m
#print axioms omega_l
#print axioms zero_l
#print axioms target_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullOmegaCoverage
