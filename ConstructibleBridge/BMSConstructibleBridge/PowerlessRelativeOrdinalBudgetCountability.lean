import BMSConstructibleBridge.PowerlessRelativeOrdinalBudgetTailFunction
import BMSConstructibleBridge.PowerlessRelativeClassCountableDoubleTail
import BMSConstructibleBridge.PowerlessRelativeClassBinaryUnion

/-! # 实际规范预算尾严格低于首 Class 不可数序数

原 Z₂ 背景下，指标域和基础序数都低于 Ω 时，实际 Class 二维图的精确像
有单一内部枚举。将它与基础序数的枚举交错，再限制同一单射到每个尾值，
取得真实 Class 可数性及严格界。无需逐块选择枚举，也不要求构图母界可数。
输入仍是原数码图的语义规格；最终固定高度对象推导与 hSources 消去另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeOrdinalBudgetCountability

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (mem_l mk_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderModel (num_l set_l)
open SecondOrderOrdinalBudgetOrder (tail_l base_l)
open SecondOrderOrdinalBudgetFunction (index_l index_covers_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₁" => structure_l hℳ B hBase
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

private theorem enumeration_l (X O d : type_l hℳ B) (hd : mem_l hℳ d.val X.val)
    (hCount : PowerlessRelativeOrdinalCutoff.countable_l B O.val X.val) :
    ∃ E : type_l hℳ B, map_l (ℳ := 𝒩₁) E O X ∧ ∀ x : type_l hℳ B,
      mem_l hℳ x.val X.val → ∃ i : type_l hℳ B,
        mem_l hℳ i.val O.val ∧ value_l (ℳ := 𝒩₁) E i x := by
  obtain ⟨r, hr, hR, hInj⟩ := hCount
  let R : type_l hℳ B := ⟨r, hr⟩
  have hRClass := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) R X O).mpr hR
  have hInjClass (x z i : type_l hℳ B) (hxi : value_l (ℳ := 𝒩₁) R x i)
      (hzi : value_l (ℳ := 𝒩₁) R z i) : x = z := Subtype.ext (hInj x.val z.val i.val
    ((PowerlessRelativeClassFunctionAbsolute.value_l R x i).mp hxi)
    ((PowerlessRelativeClassFunctionAbsolute.value_l R z i).mp hzi))
  obtain ⟨E, hE, hOnto, _⟩ := PowerlessRelativeClassInjectionEnumeration.exists_l hRClass hInjClass hd
  exact ⟨E, hE, hOnto⟩

include hBase in
theorem below_l (K : source_coding_l hℳ) (A : SecondOrderGraph.code_l ℳ)
    {Q N R S G : set_l ℳ} {r : num_l ℳ}
    (hQ : ∀ i j, SecondOrderPairing.relation_l Q i j ↔ SecondOrderBisimulation.eq_l A.real A.real i j)
    (hN : SecondOrderRootRepresentatives.spec_l A.real Q N A.root)
    (hRel : SecondOrderRootOrdinalRelation.spec_l A.real Q N R)
    (hG : SecondOrderOrdinalBudgetGraph.spec_l S r R G) (hS : ∀ n, SecondOrderDomain.wf_l S n)
    (hA : Ordinal (mk_l hℳ A)) (hξ : Ordinal (base_l hℳ hS r))
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ (base_l hℳ hS r))
    {Ω : SecondOrderQuotient.type_l hℳ}
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B K.omega Ω)
    (hAΩ : mem_l hℳ (mk_l hℳ A) Ω) (hξΩ : mem_l hℳ (base_l hℳ hS r) Ω)
    (n m : num_l ℳ) (hn : SecondOrderModel.mem_l n N) :
    mem_l hℳ (tail_l hℳ hG hS (SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hN hRel) n m) Ω := by
  let hR := SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hN hRel
  let T (i j : num_l ℳ) := tail_l hℳ hG hS hR i j
  obtain ⟨C, P, Z, _, hPRead, hZ, hZRead⟩ :=
    PowerlessRelativeOrdinalBudgetTailFunction.exists_l hℳ A hQ hN hRel hG hS K hBase hA hξ hLimit
  let A' : type_l hℳ B := ⟨mk_l hℳ A, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hA⟩
  let X : type_l hℳ B := ⟨base_l hℳ hS r, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hξ⟩
  let O : type_l hℳ B := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  have hω := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr K.omega_spec
  have haA : mem_l hℳ (index_l hℳ A hN n hn) A'.val :=
    (index_covers_l hℳ A hQ hN _).mpr ⟨n, hn, rfl⟩
  let a : type_l hℳ B := ⟨index_l hℳ A hN n hn,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A'.property haA⟩
  obtain ⟨E, hE, hEOnto⟩ := enumeration_l A' O a haA (hΩ.2.2 _ hAΩ)
  have hP (p : type_l hℳ B) : mem_l hℳ p.val P.val ↔ ∃ a k : type_l hℳ B,
      mem_l hℳ a.val A'.val ∧ mem_l hℳ k.val O.val ∧ ordered_l (ℳ := 𝒩₁) a k p := by
    constructor
    · intro hp
      obtain ⟨a, k, ha, hk, hak⟩ := (hPRead p.val).mp hp
      let a' : type_l hℳ B := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A'.property ha⟩
      let k' : type_l hℳ B := ⟨k, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property hk⟩
      exact ⟨a', k', ha, hk, (PowerlessRelativeClassFunctionAbsolute.ordered_l a' k' p).mpr hak⟩
    · rintro ⟨a, k, ha, hk, hak⟩
      exact (hPRead p.val).mpr ⟨a.val, k.val, ha, hk,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l a k p).mp hak⟩
  let φ : Formula ℒ [] [.set, .set] := .equal (.fvar .here) (.fvar (.there .here))
  obtain ⟨J, hJ, hJRead⟩ := PowerlessRelativeClassFunctionRelation.exists_l
    (φ := φ) (show Formula.IsDelta0 membershipLevyBound φ from .equal _ _) (Env.empty (M := 𝒩₁)) O O (by
      intro x hx
      exact ⟨x, ⟨hx, rfl⟩, fun _ hz => hz.2.symm⟩)
  have hJOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val O.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val O.val ∧ value_l (ℳ := 𝒩₁) J i y :=
    fun y hy => ⟨y, hy, (hJRead y y).mpr ⟨hy, hy, rfl⟩⟩
  obtain ⟨D, hD, hDOnto⟩ := PowerlessRelativeClassProductEnumeration.exists_l hω hE hJ hEOnto hJOnto hP
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassFunctionRange.exists_l hBase P Z hZ
  have hZClass : map_l (ℳ := 𝒩₁) Z P C :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) Z P C).mpr hZ
  have hYRead (y : type_l hℳ B) : mem_l hℳ y.val Y.val ↔
      ∃ p : type_l hℳ B, mem_l hℳ p.val P.val ∧ value_l (ℳ := 𝒩₁) Z p y := by
    constructor
    · intro hy
      obtain ⟨p, hpy⟩ := (hY y.val).mp hy
      have hp := (SecondOrderFunctionProperties.value_mem_l hℳ hZ hpy).1
      let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase P.property hp⟩
      exact ⟨p', hp, (PowerlessRelativeClassFunctionAbsolute.value_l Z p' y).mpr hpy⟩
    · rintro ⟨p, _, hpy⟩
      exact (hY y.val).mpr ⟨p.val, (PowerlessRelativeClassFunctionAbsolute.value_l Z p y).mp hpy⟩
  have hZY : map_l (ℳ := 𝒩₁) Z P Y := by
    constructor
    · intro p hp
      obtain ⟨x, y, hx, _, hxy⟩ := hZClass.1 p hp
      exact ⟨x, y, hx, (hYRead y).mpr ⟨x, hx, p, hp, hxy⟩, hxy⟩
    · intro p hp
      obtain ⟨y, hy, hUnique⟩ := hZClass.2 p hp
      exact ⟨y, ⟨(hYRead y).mpr ⟨p, hp, hy.2⟩, hy.2⟩, fun z hz =>
        hUnique z ⟨(PowerlessRelativeClassFunctionProperties.value_mem_l hZClass hz.2).2, hz.2⟩⟩
  obtain ⟨F, hF, hFRead⟩ := PowerlessRelativeClassFunctionComposition.exists_l hD hZY
  have hFOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val Y.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val O.val ∧ value_l (ℳ := 𝒩₁) F i y := by
    intro y hy
    obtain ⟨p, hp, hpy⟩ := (hYRead y).mp hy
    obtain ⟨i, hi, hip⟩ := hDOnto p hp
    exact ⟨i, hi, (hFRead i y).mpr ⟨hi, hy, p, hp, hip, hpy⟩⟩
  have hYTail i j (hi : SecondOrderModel.mem_l i N) : mem_l hℳ (T i j) Y.val := by
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ
      (index_l hℳ A hN i hi) (numberCode_l K j).val
    exact (hY (T i j)).mpr ⟨p, (hZRead i j hi p (T i j) hp).mpr rfl⟩
  obtain ⟨d, hd⟩ := hLimit.1
  let d' : type_l hℳ B := ⟨d, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hd⟩
  obtain ⟨E₀, hE₀, hE₀Onto⟩ := enumeration_l X O d' hd (hΩ.2.2 _ hξΩ)
  obtain ⟨W, hW, V, hV, hVOnto⟩ := PowerlessRelativeClassBinaryUnion.enumeration_l
    hω hE₀ hF hE₀Onto hFOnto
  have hWCount := PowerlessRelativeClassOntoCountability.countable_l (hBase := hBase) K K.omega_spec
    W.property V.property ((PowerlessRelativeClassFunctionAbsolute.map_l V O W).mp hV)
    ((PowerlessRelativeClassFunctionAbsolute.onto_l V O W).mp hVOnto)
  have hTOrd : Ordinal (T n m) :=
    PowerlessRelativeOrdinalBudgetReading.ordinal_l hℳ A hQ hN hRel hG hS hA hξ n m hn
  let U : type_l hℳ B := ⟨T n m, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hTOrd⟩
  have hUW : subset_l (ℳ := 𝒩₁) U W := by
    intro x hx
    rcases (SecondOrderOrdinalBudgetOrder.reading_l hℳ hG hS hR n m x.val).mp hx with
      hx | ⟨i, j, hij, he⟩
    · exact (hW x).mpr (Or.inl hx)
    · have hi : SecondOrderModel.mem_l i N := by
        rcases hij with hij | ⟨rfl, _⟩
        · exact ((hRel i n).mp hij).1
        · exact hn
      exact (hW x).mpr (Or.inr (he.symm ▸ hYTail i j hi))
  obtain ⟨f, hfClass, hfMap, hfInj⟩ := hWCount
  let F₀ : type_l hℳ B := ⟨f, hfClass⟩
  have hF₀ := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) F₀ W O).mpr hfMap
  obtain ⟨I, hI, hIRead⟩ := PowerlessRelativeClassFunctionRestriction.exists_l hF₀ hUW
  have hIInj : injective_l (ℳ := 𝒱) I.val := by
    intro x z i hxi hzi
    obtain ⟨hx, hi⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase I hxi
    obtain ⟨hz, _⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase I hzi
    let x' : type_l hℳ B := ⟨x, hx⟩
    let z' : type_l hℳ B := ⟨z, hz⟩
    let i' : type_l hℳ B := ⟨i, hi⟩
    have hFx := ((hIRead x' i').mp ((PowerlessRelativeClassFunctionAbsolute.value_l I x' i').mpr hxi)).2
    have hFz := ((hIRead z' i').mp ((PowerlessRelativeClassFunctionAbsolute.value_l I z' i').mpr hzi)).2
    exact hfInj x z i ((PowerlessRelativeClassFunctionAbsolute.value_l F₀ x' i').mp hFx)
      ((PowerlessRelativeClassFunctionAbsolute.value_l F₀ z' i').mp hFz)
  exact PowerlessRelativeCountableOrdinalBound.below_l (hBase := hBase) K K.omega_spec hTOrd
    ⟨I.val, I.property, (PowerlessRelativeClassFunctionAbsolute.map_l I U O).mp hI, hIInj⟩ hΩ

#print axioms below_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeOrdinalBudgetCountability
