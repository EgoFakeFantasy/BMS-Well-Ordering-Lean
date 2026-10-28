import BMSConstructibleBridge.PowerlessRelativeClassDoubleTailFunction
import BMSConstructibleBridge.PowerlessRelativeClassProductEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRange
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationUnion
import BMSConstructibleBridge.PowerlessRelativeClassOntoCountability
import BMSConstructibleBridge.PowerlessRelativeCountableOrdinalBound
import BMSConstructibleBridge.PowerlessHereditarySuccessor

/-! # 原内部二维尾极限的实际类内可数性

背景为原 Z₂。二维图先独立构造为 Class 对象，再枚举其定义域 ω×ω、
取精确像、与基础序数后继的枚举交错，最后得到类内单射。这里并未
对每个块选择一个枚举，也没有使用 Class Collection。严格截断界
只在实际可数性完成后推出，构图时的共同母层不要求低于截断。

本文件消去实际双尾的 Class 图／可数性前提，但输入 hG 和 hC 仍为
原二阶图的语义规格。对象双尾闭句的语法装配和最终 hSources 消去
是后续义务；不能把此语义定理冒充最终固定高度的 Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCountableDoubleTail

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (mem_l mk_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderModel (num_l zero_l)
open SecondOrderOrdinalDoubleTailOrder (base_l tail_l reading_l)

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

include hBase in
theorem countable_l (K : source_coding_l hℳ) {S G : SecondOrderModel.set_l ℳ}
    {r : num_l ℳ} (hG : SecondOrderOrdinalDoubleTailGraph.spec_l S r G)
    (hS : ∀ a, SecondOrderDomain.wf_l S a) (hα : Ordinal (base_l hℳ hS r))
    (hCount : PowerlessRelativeOrdinalCutoff.countable_l B K.omega (base_l hℳ hS r))
    (C : SecondOrderGraph.code_l ℳ)
    (hC : ∀ X : SecondOrderGraph.code_l ℳ, SecondOrderGraph.mem_l X C ↔
      SecondOrderGraph.mem_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
        SecondOrderGraph.eq_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
          ∃ n m, SecondOrderGraph.eq_l X (SecondOrderOrdinalDoubleTailGraph.code_l hℳ hG hS n m)) :
    PowerlessRelativeOrdinalCutoff.countable_l B K.omega (mk_l hℳ C) := by
  let α := base_l hℳ hS r
  let T (n m : num_l ℳ) := tail_l hℳ hG hS n m
  let a := T (zero_l ℳ) (zero_l ℳ)
  obtain ⟨hOrd, hαC, hLimit, hCofinal⟩ :=
    SecondOrderOrdinalDoubleTailCofinal.properties_l hℳ hG hS hα C hC
  have hRead (x : SecondOrderQuotient.type_l hℳ) : mem_l hℳ x (mk_l hℳ C) ↔
      mem_l hℳ x α ∨ x = α ∨ ∃ n m, x = T n m := by
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact (hC X).trans (or_congr Iff.rfl (or_congr (SecondOrderQuotient.eq_iff_l hℳ _ _).symm
      (exists_congr fun _ => exists_congr fun _ => (SecondOrderQuotient.eq_iff_l hℳ _ _).symm)))
  have haSucc : PowerlessRelativeHierarchySemantics.successor_l hℳ α a := by
    intro x
    rw [reading_l hℳ hG hS (zero_l ℳ) (zero_l ℳ) x]
    constructor
    · rintro (hx | hx | ⟨i, j, hij, _⟩)
      · exact Or.inl hx
      · exact Or.inr hx
      · rcases hij with hi | ⟨_, hj⟩
        · exact (SecondOrderTriangularMonotone.zero_bound_l hℳ i hi).elim
        · exact (SecondOrderTriangularMonotone.zero_bound_l hℳ j hj).elim
    · exact fun hx => hx.elim Or.inl (Or.inr ∘ Or.inl)
  have hTC (n m : num_l ℳ) : mem_l hℳ (T n m) (mk_l hℳ C) :=
    (hRead _).mpr (Or.inr (Or.inr ⟨n, m, rfl⟩))
  let D : type_l hℳ B := ⟨mk_l hℳ C, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hOrd⟩
  let O : type_l hℳ B := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  let A : type_l hℳ B := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
    D.property (hTC _ _)⟩
  have hω := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr K.omega_spec
  obtain ⟨P, R, hPRead, hR, hRRead⟩ := PowerlessRelativeClassDoubleTailFunction.exists_l
    (hBase := hBase) K hG hS hα D hOrd hLimit hCofinal hTC
  have hP (p : type_l hℳ B) : mem_l hℳ p.val P.val ↔ ∃ n m : type_l hℳ B,
      mem_l hℳ n.val O.val ∧ mem_l hℳ m.val O.val ∧ ordered_l (ℳ := 𝒩₁) n m p := by
    constructor
    · intro hp
      obtain ⟨n, m, hn, hm, hnm⟩ := (hPRead p.val).mp hp
      let n' : type_l hℳ B := ⟨n, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property hn⟩
      let m' : type_l hℳ B := ⟨m, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property hm⟩
      exact ⟨n', m', hn, hm, (PowerlessRelativeClassFunctionAbsolute.ordered_l n' m' p).mpr hnm⟩
    · rintro ⟨n, m, hn, hm, hnm⟩
      exact (hPRead p.val).mpr ⟨n.val, m.val, hn, hm,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l n m p).mp hnm⟩
  let φ : Formula ℒ [] [.set, .set] := .equal (.fvar .here) (.fvar (.there .here))
  let η := Env.empty (M := 𝒩₁)
  obtain ⟨J, hJ, hJRead⟩ := PowerlessRelativeClassFunctionRelation.exists_l
    (φ := φ) (show Formula.IsDelta0 membershipLevyBound φ from .equal _ _) η O O (by
      intro x hx
      exact ⟨x, ⟨hx, rfl⟩, fun _ hz => hz.2.symm⟩)
  have hJOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val O.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val O.val ∧ value_l (ℳ := 𝒩₁) J i y :=
    fun y hy => ⟨y, hy, (hJRead y y).mpr ⟨hy, hy, rfl⟩⟩
  obtain ⟨E, hE, hEOnto⟩ := PowerlessRelativeClassProductEnumeration.exists_l hω hJ hJ hJOnto hJOnto hP
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassFunctionRange.exists_l hBase P R hR
  have hRClass : map_l (ℳ := 𝒩₁) R P D :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) R P D).mpr hR
  have hYRead (y : type_l hℳ B) : mem_l hℳ y.val Y.val ↔
      ∃ p : type_l hℳ B, mem_l hℳ p.val P.val ∧ value_l (ℳ := 𝒩₁) R p y := by
    constructor
    · intro hy
      obtain ⟨p, hpy⟩ := (hY y.val).mp hy
      have hpP := (SecondOrderFunctionProperties.value_mem_l hℳ hR hpy).1
      let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase P.property hpP⟩
      exact ⟨p', hpP, (PowerlessRelativeClassFunctionAbsolute.value_l R p' y).mpr hpy⟩
    · rintro ⟨p, _, hpy⟩
      exact (hY y.val).mpr ⟨p.val, (PowerlessRelativeClassFunctionAbsolute.value_l R p y).mp hpy⟩
  have hRY : map_l (ℳ := 𝒩₁) R P Y := by
    constructor
    · intro p hp
      obtain ⟨x, y, hx, _, hxy⟩ := hRClass.1 p hp
      exact ⟨x, y, hx, (hYRead y).mpr ⟨x, hx, p, hp, hxy⟩, hxy⟩
    · intro p hp
      obtain ⟨y, hy, hUnique⟩ := hRClass.2 p hp
      exact ⟨y, ⟨(hYRead y).mpr ⟨p, hp, hy.2⟩, hy.2⟩, fun z hz =>
        hUnique z ⟨(PowerlessRelativeClassFunctionProperties.value_mem_l hRClass hz.2).2, hz.2⟩⟩
  obtain ⟨F, hF, hFRead⟩ := PowerlessRelativeClassFunctionComposition.exists_l hE hRY
  have hFOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val Y.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val O.val ∧ value_l (ℳ := 𝒩₁) F i y := by
    intro y hy
    obtain ⟨p, hp, hpy⟩ := (hYRead y).mp hy
    obtain ⟨i, hi, hip⟩ := hEOnto p hp
    exact ⟨i, hi, (hFRead i y).mpr ⟨hi, hy, p, hp, hip, hpy⟩⟩
  have hYTail (y : type_l hℳ B) : mem_l hℳ y.val Y.val ↔ ∃ n m, y.val = T n m := by
    constructor
    · intro hy
      obtain ⟨p, hp, hpy⟩ := (hYRead y).mp hy
      obtain ⟨i, j, hi, hj, hpPair⟩ := (hPRead p.val).mp hp
      obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨i, hi⟩
      obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨j, hj⟩
      have hn' : (numberCode_l K n).val = i := congrArg Subtype.val hn
      have hm' : (numberCode_l K m).val = j := congrArg Subtype.val hm
      exact ⟨n, m, (hRRead n m p.val y.val (hn'.symm ▸ hm'.symm ▸ hpPair)).mp
        ((PowerlessRelativeClassFunctionAbsolute.value_l R p y).mp hpy)⟩
    · rintro ⟨n, m, hy⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (numberCode_l K n).val (numberCode_l K m).val
      exact (hY y.val).mpr ⟨p, (hRRead n m p y.val hp).mpr hy⟩
  have hαHC := (PowerlessHereditaryOrdinalCountability.ordinal_iff_l (hBase := hBase) K K.omega_spec hα).mp hCount
  obtain ⟨b, hbHC, hbSucc⟩ := PowerlessHereditarySuccessor.exists_l hBase hαHC
  have hba : b = a := SecondOrderQuotient.ext_l hℳ b a (fun x => (hbSucc x).trans (haSucc x).symm)
  have haCount := PowerlessHereditaryOrdinalCountability.countable_of_hereditary_l
    (hBase := hBase) K K.omega_spec (hba ▸ hbHC)
  obtain ⟨q, hqClass, hqMap, hqInj⟩ := haCount
  let Q : type_l hℳ B := ⟨q, hqClass⟩
  let d : type_l hℳ B := ⟨α, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase D.property hαC⟩
  have hdA : mem_l hℳ d.val A.val := (haSucc α).mpr (Or.inr rfl)
  have hQ : map_l (ℳ := 𝒩₁) Q A O :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) Q A O).mpr hqMap
  have hQInj (x z i : type_l hℳ B) (hx : value_l (ℳ := 𝒩₁) Q x i)
      (hz : value_l (ℳ := 𝒩₁) Q z i) : x = z := Subtype.ext (hqInj x.val z.val i.val
    ((PowerlessRelativeClassFunctionAbsolute.value_l Q x i).mp hx)
    ((PowerlessRelativeClassFunctionAbsolute.value_l Q z i).mp hz))
  obtain ⟨J', hJ', hJ'Onto, _⟩ := PowerlessRelativeClassInjectionEnumeration.exists_l hQ hQInj hdA
  have hUnion (y : type_l hℳ B) : mem_l hℳ y.val D.val ↔
      mem_l hℳ y.val A.val ∨ mem_l hℳ y.val Y.val :=
    (hRead y.val).trans (or_assoc.symm.trans (or_congr (haSucc y.val).symm (hYTail y).symm))
  obtain ⟨F', hF', hOnto⟩ := PowerlessRelativeClassEnumerationUnion.exists_l hω hJ' hF hJ'Onto hFOnto hUnion
  exact PowerlessRelativeClassOntoCountability.countable_l (hBase := hBase) K K.omega_spec D.property F'.property
    ((PowerlessRelativeClassFunctionAbsolute.map_l F' O D).mp hF')
    ((PowerlessRelativeClassFunctionAbsolute.onto_l F' O D).mp hOnto)

include hBase in
theorem below_l (K : source_coding_l hℳ) {S G : SecondOrderModel.set_l ℳ}
    {r : num_l ℳ} (hG : SecondOrderOrdinalDoubleTailGraph.spec_l S r G)
    (hS : ∀ a, SecondOrderDomain.wf_l S a) (hα : Ordinal (base_l hℳ hS r))
    {Ω : SecondOrderQuotient.type_l hℳ} (hΩ : PowerlessRelativeOrdinalCutoff.first_l B K.omega Ω)
    (hαΩ : mem_l hℳ (base_l hℳ hS r) Ω) (C : SecondOrderGraph.code_l ℳ)
    (hC : ∀ X : SecondOrderGraph.code_l ℳ, SecondOrderGraph.mem_l X C ↔
      SecondOrderGraph.mem_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
        SecondOrderGraph.eq_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
          ∃ n m, SecondOrderGraph.eq_l X (SecondOrderOrdinalDoubleTailGraph.code_l hℳ hG hS n m)) :
    mem_l hℳ (mk_l hℳ C) Ω ∧ mem_l hℳ (base_l hℳ hS r) (mk_l hℳ C) ∧
      PowerlessRelativeHierarchySemantics.limit_l hℳ (mk_l hℳ C) ∧
        PowerlessRelativeCofinalLimitBounds.cofinal_l (mk_l hℳ C) := by
  obtain ⟨hOrd, hαC, hLimit, hCofinal⟩ :=
    SecondOrderOrdinalDoubleTailCofinal.properties_l hℳ hG hS hα C hC
  have hCount := countable_l (hBase := hBase) K hG hS hα (hΩ.2.2 _ hαΩ) C hC
  exact ⟨PowerlessRelativeCountableOrdinalBound.below_l (hBase := hBase) K K.omega_spec hOrd hCount hΩ,
    hαC, hLimit, hCofinal⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCountableDoubleTail
