import BMSConstructibleBridge.SecondOrderOrdinalTailFunction
import BMSConstructibleBridge.SecondOrderOrdinalTailLimit
import BMSConstructibleBridge.PowerlessRelativeClassLimitSuccessorGraph
import BMSConstructibleBridge.PowerlessRelativeClassFunctionIteration
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationUnion
import BMSConstructibleBridge.PowerlessRelativeClassOntoCountability
import BMSConstructibleBridge.PowerlessHereditarySuccessor

/-! # 类内可数序数的内部 ω 尾极限仍类内可数

尾函数先在原商中实际构造，再用已有有限轨迹界证明其图属于类。
其精确像由 Δ₀ 分离取得，与基础序数后继的类内枚举交错，产生真正的
类内满射。全过程不假定任何截断层已经满足完整 Separation／Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCountableTailLimit

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (mem_l mk_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩" => structure_l hℳ B hBase
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

include hℳ in
private theorem not_lt_zero_l (m : SecondOrderModel.num_l ℳ) :
    ¬SecondOrderOrder.lt_l m (SecondOrderModel.zero_l ℳ) := by
  rintro ⟨k, hk⟩
  exact SecondOrderModel.nonzero_l hℳ _
    ((SecondOrderModel.add_succ_l hℳ m k).symm.trans hk)

include hBase in
theorem countable_l (K : source_coding_l hℳ) {S G : SecondOrderModel.set_l ℳ}
    {r : SecondOrderModel.num_l ℳ} (hG : SecondOrderOrdinalTailGraph.spec_l S r G)
    (hS : ∀ a, SecondOrderDomain.wf_l S a)
    (hα : Ordinal (mk_l hℳ ⟨S, r, hS r⟩))
    (hCount : PowerlessRelativeOrdinalCutoff.countable_l B K.omega (mk_l hℳ ⟨S, r, hS r⟩))
    (C : SecondOrderGraph.code_l ℳ)
    (hC : ∀ X : SecondOrderGraph.code_l ℳ, SecondOrderGraph.mem_l X C ↔
      SecondOrderGraph.mem_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
        SecondOrderGraph.eq_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
          ∃ n, SecondOrderGraph.eq_l X (SecondOrderOrdinalTailGraph.code_l hℳ hG hS n)) :
    PowerlessRelativeOrdinalCutoff.countable_l B K.omega (mk_l hℳ C) := by
  let α := mk_l hℳ (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ)
  let T (n : SecondOrderModel.num_l ℳ) := mk_l hℳ (SecondOrderOrdinalTailGraph.code_l hℳ hG hS n)
  let a := T (SecondOrderModel.zero_l ℳ)
  obtain ⟨hOrd, hαC, hNoMax⟩ := SecondOrderOrdinalTailLimit.properties_l hℳ hG hS hα C hC
  have hRead (x : SecondOrderQuotient.type_l hℳ) : mem_l hℳ x (mk_l hℳ C) ↔
      mem_l hℳ x α ∨ x = α ∨ ∃ n, x = T n := by
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact (hC X).trans (or_congr Iff.rfl (or_congr
      (SecondOrderQuotient.eq_iff_l hℳ _ _).symm
      (exists_congr fun _ => (SecondOrderQuotient.eq_iff_l hℳ _ _).symm)))
  have haSucc : PowerlessRelativeHierarchySemantics.successor_l hℳ α a := by
    intro x
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    have h := SecondOrderOrdinalTailMembers.members_l hℳ hG hS (SecondOrderModel.zero_l ℳ) X
    have h' := h.trans (or_congr Iff.rfl (or_congr
      (SecondOrderQuotient.eq_iff_l hℳ _ _).symm
      (exists_congr fun _ => and_congr Iff.rfl (SecondOrderQuotient.eq_iff_l hℳ _ _).symm)))
    exact h'.trans ⟨fun h => h.elim Or.inl (fun h => h.elim Or.inr
      (fun ⟨n, hn, _⟩ => (not_lt_zero_l (hℳ := hℳ) n hn).elim)), fun h => h.elim Or.inl (Or.inr ∘ Or.inl)⟩
  have hTC (n : SecondOrderModel.num_l ℳ) : mem_l hℳ (T n) (mk_l hℳ C) :=
    (hRead _).mpr (Or.inr (Or.inr ⟨n, rfl⟩))
  let D : type_l hℳ B := ⟨mk_l hℳ C, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hOrd⟩
  let O : type_l hℳ B := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  have hω := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr K.omega_spec
  let A : type_l hℳ B := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase D.property (hTC _)⟩
  obtain ⟨H, hH, hHRead⟩ := PowerlessRelativeClassLimitSuccessorGraph.exists_l D hOrd hNoMax
  obtain ⟨F, hF, hFRead⟩ := SecondOrderOrdinalTailFunction.exists_l K hG hS D.val hTC
  have hIter := SecondOrderOrdinalTailFunction.iteration_l (H := H.val) K hG hS hF hFRead (fun x y hx hy hxy => by
    let x' : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase D.property hx⟩
    let y' : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase D.property hy⟩
    exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) H x' y').mp
      ((hHRead x' y').mpr ⟨hx, hy, hxy⟩))
  have hFClass := PowerlessRelativeClassFunctionIteration.member_l (hBase := hBase) K D H
    (hTC (SecondOrderModel.zero_l ℳ)) hH hIter
  let F' : type_l hℳ B := ⟨F, hFClass⟩
  have hF' : map_l (ℳ := 𝒩) F' O D := (PowerlessRelativeClassFunctionAbsolute.map_l F' O D).mpr hF
  let φ : Formula ℒ [] [.set, .set, .set] := membershipLevyBound.boundedExists
    (.fvar (.there .here)) (PowerlessValueBounded.formula_m
      (.fvar (.there (.there .here))) (.bvar .here) (.fvar .here))
  let η : Env 𝒩 [] [.set, .set] := (Env.empty.pushFree F').pushFree O
  have hφ (y : type_l hℳ B) : φ.satisfies (η.pushFree y) ↔
      ∃ i : type_l hℳ B, mem_l hℳ i.val O.val ∧ value_l (ℳ := 𝒩) F' i y := by
    simp only [φ, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
      membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l, Arguments.eval, Term.eval]
    rfl
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassDeltaSeparation.exists_l
    (show Formula.IsDelta0 membershipLevyBound φ from .bounded_exists _ (PowerlessValueBounded.delta_l _ _ _)) η D
  have hYRead (y : type_l hℳ B) : mem_l hℳ y.val Y.val ↔
      mem_l hℳ y.val D.val ∧ ∃ i : type_l hℳ B, mem_l hℳ i.val O.val ∧ value_l (ℳ := 𝒩) F' i y :=
    (hY y).trans (and_congr Iff.rfl (hφ y))
  have hFY : map_l (ℳ := 𝒩) F' O Y := by
    constructor
    · intro p hp
      obtain ⟨i, y, hi, hy, hPair⟩ := hF'.1 p hp
      exact ⟨i, y, hi, (hYRead y).mpr ⟨hy, i, hi, p, hp, hPair⟩, hPair⟩
    · intro i hi
      obtain ⟨y, hy, hUnique⟩ := hF'.2 i hi
      exact ⟨y, ⟨(hYRead y).mpr ⟨hy.1, i, hi, hy.2⟩, hy.2⟩,
        fun z hz => hUnique z ⟨((hYRead z).mp hz.1).1, hz.2⟩⟩
  have hYTail (y : type_l hℳ B) : mem_l hℳ y.val Y.val ↔ ∃ n, y.val = T n := by
    constructor
    · intro hy
      obtain ⟨_, i, hi, hiy⟩ := (hYRead y).mp hy
      obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨i.val, hi⟩
      have hn' : (numberCode_l K n).val = i.val := congrArg Subtype.val hn
      exact ⟨n, (hFRead n y.val).mp (hn'.symm ▸
        (PowerlessRelativeClassFunctionAbsolute.value_l F' i y).mp hiy)⟩
    · rintro ⟨n, hn⟩
      let i : type_l hℳ B := ⟨(numberCode_l K n).val,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property (numberCode_l K n).property⟩
      exact (hYRead y).mpr ⟨hn.symm ▸ hTC n, i, (numberCode_l K n).property,
        (PowerlessRelativeClassFunctionAbsolute.value_l F' i y).mpr ((hFRead n y.val).mpr hn)⟩
  have hαHC := (PowerlessHereditaryOrdinalCountability.ordinal_iff_l (hBase := hBase) K K.omega_spec hα).mp hCount
  obtain ⟨b, hbHC, hbSucc⟩ := PowerlessHereditarySuccessor.exists_l hBase hαHC
  have hba : b = a := SecondOrderQuotient.ext_l hℳ b a
    (fun x => (hbSucc x).trans (haSucc x).symm)
  have haCount := PowerlessHereditaryOrdinalCountability.countable_of_hereditary_l
    (hBase := hBase) K K.omega_spec (hba ▸ hbHC)
  obtain ⟨q, hqClass, hqMap, hqInj⟩ := haCount
  let Q : type_l hℳ B := ⟨q, hqClass⟩
  let d : type_l hℳ B := ⟨α, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase D.property hαC⟩
  have hdA : mem_l hℳ d.val A.val := (haSucc α).mpr (Or.inr rfl)
  have hQ : map_l (ℳ := 𝒩) Q A O :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) Q A O).mpr hqMap
  have hQInj (x y i : type_l hℳ B) (hx : value_l (ℳ := 𝒩) Q x i)
      (hy : value_l (ℳ := 𝒩) Q y i) : x = y := Subtype.ext (hqInj x.val y.val i.val
    ((PowerlessRelativeClassFunctionAbsolute.value_l Q x i).mp hx)
    ((PowerlessRelativeClassFunctionAbsolute.value_l Q y i).mp hy))
  obtain ⟨J, hJ, hJOnto, _⟩ := PowerlessRelativeClassInjectionEnumeration.exists_l hQ hQInj (d := d) hdA
  have hUnion (y : type_l hℳ B) : mem_l hℳ y.val D.val ↔
      mem_l hℳ y.val A.val ∨ mem_l hℳ y.val Y.val := by
    exact (hRead y.val).trans (or_assoc.symm.trans
      (or_congr (haSucc y.val).symm (hYTail y).symm))
  obtain ⟨J', hJ', hOnto⟩ := PowerlessRelativeClassEnumerationUnion.exists_l hω hJ hFY hJOnto
    (fun y hy => ((hYRead y).mp hy).2) hUnion
  exact PowerlessRelativeClassOntoCountability.countable_l (hBase := hBase) K K.omega_spec D.property J'.property
    ((PowerlessRelativeClassFunctionAbsolute.map_l J' O D).mp hJ')
    ((PowerlessRelativeClassFunctionAbsolute.onto_l J' O D).mp hOnto)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCountableTailLimit
