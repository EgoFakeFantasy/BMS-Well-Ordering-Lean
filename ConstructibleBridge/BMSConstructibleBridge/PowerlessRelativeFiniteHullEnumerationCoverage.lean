import BMSConstructibleBridge.PowerlessRelativeFiniteHullOmegaCoverage
import BMSConstructibleBridge.PowerlessRelativeFiniteHullMemberValues
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationSectionDerives

/-! # 实际枚举将完整值域回收到同一有限壳

对象语言为纯隶属 ℒ，背景及正式出口为原 Z₂。对原共同有限族增加
一个三绑定槽的函数值存在式。内部 ω 覆盖与原图的值唯一性保证：
若实际 ω 枚举图和目标集合均已在 I，则目标的全部成员也在 I。
I 不假定传递；局部函数值必须经完整配对矩阵及真实配对闭包读回。
这里没有预供 A⊆I，也不声称任意层内集合已经有层内枚举。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullEnumerationCoverage

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

/-- 原绑定槽依次为数、枚举图、目标集合，输出是新增存在槽。 -/
def witness_m (Δ : SortContext ℒ) : Formula ℒ [.set, .set, .set] Δ :=
  .existsE .set <| .conj
    (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there (.there (.there .here)))))
    (SecondOrderObjectSyntax.value_m (.bvar (.there (.there .here)))
      (.bvar (.there .here)) (.bvar .here))

def family_m (Δ : SortContext ℒ) : PowerlessRelativeFiniteElementarity.family_m Δ :=
  [Sigma.mk ([.set, .set, .set] : SortContext ℒ) (witness_m Δ)]

theorem witness_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (η : Env 𝒩 [.set, .set, .set] Δ) :
    (witness_m Δ).satisfies η ↔ ∃ y,
      member_l 𝒩 y (η.boundVal (.there (.there .here))) ∧
        value_l (ℳ := 𝒩) (η.boundVal (.there .here)) (η.boundVal .here) y := by
  simp only [witness_m, Formula.satisfies, ThirdOrderSemantics.value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem target_l (K : source_coding_l hℳ) {Δ Ε : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ family_m Δ, p ∈ Φ)
    (ζ : Env 𝒱 [] Ε) (I W B ω F A : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (hSource : (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W).satisfies ζ)
    (hIW : subset_l (ℳ := 𝒱) (I.eval ζ) (W.eval ζ))
    (hParams : (parameters_m Δ I τ).satisfies ζ)
    (hB : mem_l hℳ (B.eval ζ) (I.eval ζ)) (hωI : mem_l hℳ (ω.eval ζ) (I.eval ζ))
    (hElem : (PowerlessRelativeFiniteElementarity.form_m Φ I W τ).satisfies ζ)
    (hF : mem_l hℳ (F.eval ζ) (I.eval ζ)) (hA : mem_l hℳ (A.eval ζ) (I.eval ζ))
    (hMap : map_l (ℳ := 𝒱) (F.eval ζ) (ω.eval ζ) (A.eval ζ))
    (hOnto : ∀ x, mem_l hℳ x (A.eval ζ) → ∃ n, mem_l hℳ n (ω.eval ζ) ∧
      value_l (ℳ := 𝒱) (F.eval ζ) n x) :
    subset_l (ℳ := 𝒱) (A.eval ζ) (I.eval ζ) := by
  obtain ⟨hClosedI, hωSub⟩ := PowerlessRelativeFiniteHullOmegaCoverage.target_l
    K Φ hΦ hΦ₀ ζ I W B ω τ hSource hIW hParams hB hωI hElem
  obtain ⟨hBase, hω, Ω, hΩ, hLevel⟩ :=
    (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K ζ B ω W).mp hSource
  have hTransW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) (W.eval ζ) :=
    fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hLevel x hx y hy
  have hClosedW := PowerlessRelativeFiniteHullClosure.limit_closed_l hℳ hBase
    (PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ) hLevel
  have hPair := (PowerlessRelativeFiniteHullClosure.family_formula_l ζ I W τ).mp
    (PowerlessRelativeFiniteElementarity.subfamily_formula_l
      (PowerlessRelativeFiniteHullClosure.family_m Δ) Φ hΦ₀ ζ I W τ hElem)
  have hOne := PowerlessRelativeFiniteElementarity.subfamily_formula_l
    (family_m Δ) Φ hΦ₁ ζ I W τ hElem
  have hEntry : (PowerlessRelativeFiniteElementarity.entry_m (witness_m Δ) I W τ).satisfies ζ :=
    hOne.1
  have hParameters := (parameters_formula_l Δ ζ I τ).mp hParams
  have hI : ∃ x, mem_l hℳ x (I.eval ζ) := ⟨B.eval ζ, hB⟩
  have hW : ∃ x, mem_l hℳ x (W.eval ζ) := ⟨B.eval ζ, hIW (B.eval ζ) hB⟩
  let ν : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) (I.eval ζ) hI) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => ⟨(τ v).eval ζ, hParameters .set v⟩ }
  have hRead := (PowerlessRelativeFiniteElementarity.entry_formula_l (witness_m Δ) ζ I W τ
    (PowerlessRelativization.env_l ν) (fun _ => rfl)).mp hEntry
  let f : PowerlessMemberStructure.type_l (ℳ := 𝒱) (I.eval ζ) := ⟨F.eval ζ, hF⟩
  let a : PowerlessMemberStructure.type_l (ℳ := 𝒱) (I.eval ζ) := ⟨A.eval ζ, hA⟩
  have hMapRaw : SecondOrderFunctionObjects.map_l hℳ (F.eval ζ) (ω.eval ζ) (A.eval ζ) := hMap
  intro x hx
  obtain ⟨n, hn, hnx⟩ := hOnto x hx
  let n₀ : PowerlessMemberStructure.type_l (ℳ := 𝒱) (I.eval ζ) := ⟨n, hωSub n hn⟩
  let ξ : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) (I.eval ζ) hI)
      [.set, .set, .set] Δ :=
    ((ν.pushBound (sort := SetTheory.SetSort.set) a).pushBound
      (sort := SetTheory.SetSort.set) f).pushBound (sort := SetTheory.SetSort.set) n₀
  let ξW := PowerlessSourceInclusion.env_l (hU := hW) hIW ξ
  have hReflect := hRead (PowerlessRelativization.env_l ξ) (fun _ _ => rfl) (fun v => by
    cases v with
    | here => exact n₀.property
    | there v => cases v with
      | here => exact f.property
      | there v => cases v with
        | here => exact a.property
        | there v => nomatch v)
  let x₀ : PowerlessMemberStructure.type_l (ℳ := 𝒱) (W.eval ζ) :=
    ⟨x, hTransW (A.eval ζ) x (hIW (A.eval ζ) hA) hx⟩
  have hValueW : value_l (ℳ := PowerlessMemberStructure.structure_l (ℳ := 𝒱) (W.eval ζ) hW)
      (PowerlessSourceInclusion.inclusion_l hIW f)
      (PowerlessSourceInclusion.inclusion_l hIW n₀) x₀ :=
    (PowerlessRelativeFiniteHullMemberValues.value_l hTransW (fun _ h => h)
      (fun _ _ _ _ _ _ => Iff.rfl) hClosedW.1 _ _ _).mp hnx
  have hLeft : (witness_m Δ).satisfies ξW :=
    (witness_formula_l ξW).mpr ⟨x₀, hx, hValueW⟩
  have hRight := (PowerlessRelativization.formula_l (witness_m Δ) ξ).mp
    (hReflect.mp ((PowerlessRelativization.formula_l (witness_m Δ) ξW).mpr hLeft))
  obtain ⟨y, _hyA, hny⟩ := (witness_formula_l ξ).mp hRight
  have hnyRaw := (PowerlessRelativeFiniteHullMemberValues.value_l hTransW hIW
    hPair.2.1 hClosedI.1 f n₀ y).mpr hny
  have hEq : x = y.val := SecondOrderFunctionProperties.value_unique_l hℳ hMapRaw hnx hnyRaw
  exact hEq.symm ▸ y.property

def schema_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (I W B ω F A : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  .imp (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W) <|
    .imp (ThirdOrderTheory.subset_m I W) <| .imp (parameters_m Δ I τ) <|
      .imp (SecondOrderObjectSyntax.member_m B I) <| .imp (SecondOrderObjectSyntax.member_m ω I) <|
        .imp (PowerlessRelativeFiniteElementarity.form_m Φ I W τ) <|
          .imp (SecondOrderObjectSyntax.member_m F I) <| .imp (SecondOrderObjectSyntax.member_m A I) <|
            .imp (SecondOrderObjectSyntax.map_m F ω A) <|
              .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m F ω A)
                (ThirdOrderTheory.subset_m A I)

def sentence_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (I W B ω F A : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ I W B ω F A τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ family_m Δ, p ∈ Φ)
    (I W B ω F A : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    (sentence_m Φ I W B ω F A τ).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ζ hSource hIW hParams hB hωI hElem hF hA hMap hOnto
  apply (ThirdOrderSemantics.subset_formula_l ζ A I).mpr
  exact target_l K Φ hΦ hΦ₀ hΦ₁ ζ I W B ω F A τ hSource
    ((ThirdOrderSemantics.subset_formula_l ζ I W).mp hIW) hParams hB hωI hElem hF hA
    ((ThirdOrderSemantics.map_formula_l ζ F ω A).mp hMap)
    ((PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l ζ F ω A).mp hOnto)

theorem derives_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ family_m Δ, p ∈ Φ)
    (I W B ω F A : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ I W B ω F A τ)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ hℳ => models_l hℳ Φ hΦ hΦ₀ hΦ₁ I W B ω F A τ)

#print axioms witness_formula_l
#print axioms target_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullEnumerationCoverage
