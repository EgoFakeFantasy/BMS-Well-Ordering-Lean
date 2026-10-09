import BMSConstructibleBridge.SecondOrderFiniteAssignmentLift
import BMSConstructibleBridge.PowerlessAssignmentUpdate
import BMSConstructibleBridge.PowerlessRelativeClassFunctionProperties

/-! # 原前插赋值与实际类内槽更新的连接

先对全部内部数槽核验更新读数，再由 ω 的内部数码覆盖和映射域守卫
推广到全部类坐标。最终构造同时给出两张实际有限赋值图及完整更新式，
母集枚举仍只要求属于原商。此处尚不证明 Sat 求值保持或原 Def 良序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyAssignmentUpdate

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderFiniteAssignmentLift (number_l)
open SecondOrderSequenceSyntax (read_l)
open SecondOrderAssignmentSyntax (valid_l extension_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

theorem of_numbers_l (K : source_coding_l hℳ) {ω A F G x : type_l hℳ B}
    (hωEq : ω.val = K.omega) (L e : SecondOrderModel.num_l ℳ)
    (hF : map_l (ℳ := ClassModel) F (number_l hBase K ω hωEq L) A)
    (hG : map_l (ℳ := ClassModel) G (number_l hBase K ω hωEq L) A)
    (hPoint : ∀ i : SecondOrderModel.num_l ℳ, ∀ y : type_l hℳ B,
      value_l (ℳ := ClassModel) G (number_l hBase K ω hωEq i) y ↔
        (i = e ∧ y = x) ∨ i ≠ e ∧ value_l (ℳ := ClassModel) F (number_l hBase K ω hωEq i) y) :
    PowerlessAssignmentUpdate.update_l (ℳ := ClassModel) F (number_l hBase K ω hωEq e) x G := by
  have hBounds {H : type_l hℳ B}
      (hH : map_l (ℳ := ClassModel) H (number_l hBase K ω hωEq L) A)
      {i y : type_l hℳ B} (hiy : value_l (ℳ := ClassModel) H i y) : mem_l hℳ i.val ω.val := by
    have hiL := (PowerlessRelativeClassFunctionProperties.value_mem_l hH hiy).1
    have hiω := SecondOrderOmegaTransitive.member_l hℳ (k := (numberCode_l K L).val)
      (x := i.val) K.omega_spec (numberCode_l K L).property hiL
    exact hωEq.symm ▸ hiω
  intro i y
  classical
  by_cases hi : mem_l hℳ i.val ω.val
  · obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨i.val, hωEq ▸ hi⟩
    have hiRaw := congrArg (fun q => q.val) hn
    have hiEq : number_l hBase K ω hωEq n = i := Subtype.ext hiRaw
    have hNumEq : number_l hBase K ω hωEq n = number_l hBase K ω hωEq e ↔ n = e := by
      constructor
      · intro h
        have hRaw := congrArg (fun q : type_l hℳ B => q.val) h
        exact numberCode_injective_l K (Subtype.ext hRaw)
      · exact fun h => h ▸ rfl
    rw [← hiEq]
    exact (hPoint n y).trans (or_congr (and_congr hNumEq.symm Iff.rfl)
      (and_congr (not_congr hNumEq.symm) Iff.rfl))
  · have hGFalse : ¬value_l (ℳ := ClassModel) G i y := fun h => hi (hBounds hG h)
    have hFFalse : ¬value_l (ℳ := ClassModel) F i y := fun h => hi (hBounds hF h)
    have hiNe : i ≠ number_l hBase K ω hωEq e := by
      rintro rfl
      exact hi (hωEq.symm ▸ (numberCode_l K e).property)
    refine iff_of_false hGFalse ?_
    rintro (⟨hEq, _⟩ | ⟨_, h⟩)
    · exact hiNe hEq
    · exact hFFalse h

theorem exists_l (K : source_coding_l hℳ) {ω A x : type_l hℳ B}
    (hω : omega_l (ℳ := ClassModel) ω) (hωEq : ω.val = K.omega)
    {E : SecondOrderModel.set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    {c l d v : SecondOrderModel.num_l ℳ} (hc : valid_l E c l) (hd : extension_l E c l d v)
    (L z : SecondOrderModel.num_l ℳ) (hLength : SecondOrderOrder.lt_l l L)
    {U : SecondOrderQuotient.type_l hℳ}
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A.val)
    (hx : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K v).val x.val) :
    ∃ F G : type_l hℳ B,
      map_l (ℳ := ClassModel) F (number_l hBase K ω hωEq L) A ∧
      map_l (ℳ := ClassModel) G (number_l hBase K ω hωEq L) A ∧
      PowerlessAssignmentUpdate.update_l (ℳ := ClassModel) F (number_l hBase K ω hωEq l) x G ∧
      (∀ i : SecondOrderModel.num_l ℳ, ∀ y : type_l hℳ B,
        value_l (ℳ := ClassModel) F (number_l hBase K ω hωEq i) y ↔ ∃ j,
          SecondOrderLegacyAssignmentPadding.padded_l E c l L z i j ∧
            value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K j).val y.val) ∧
      (∀ i : SecondOrderModel.num_l ℳ, ∀ y : type_l hℳ B,
        value_l (ℳ := ClassModel) G (number_l hBase K ω hωEq i) y ↔ ∃ j,
          SecondOrderLegacyAssignmentPadding.padded_l E d (SecondOrderModel.succ_l l) L z i j ∧
            value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K j).val y.val) := by
  obtain ⟨p, hp, hPRead⟩ := SecondOrderLegacyAssignmentPadding.exists_l hℳ hE hc L z
  obtain ⟨q, hq, hQRead⟩ := SecondOrderLegacyAssignmentPadding.exists_l hℳ hE hd.1 L z
  obtain ⟨F, hF, hFRead⟩ := SecondOrderFiniteAssignmentLift.exists_l K hω hωEq hp hU
  obtain ⟨G, hG, hGRead⟩ := SecondOrderFiniteAssignmentLift.exists_l K hω hωEq hq hU
  have hCode (i j : SecondOrderModel.num_l ℳ) : read_l E q i j ↔
      (i = l ∧ j = v) ∨ i ≠ l ∧ read_l E p i j :=
    (hQRead i j).trans ((SecondOrderLegacyAssignmentPadding.prepend_l hℳ hd hLength).trans
      (or_congr Iff.rfl (and_congr Iff.rfl (hPRead i j).symm)))
  have hPoint (i : SecondOrderModel.num_l ℳ) (y : type_l hℳ B) :
      value_l (ℳ := ClassModel) G (number_l hBase K ω hωEq i) y ↔
        (i = l ∧ y = x) ∨ i ≠ l ∧ value_l (ℳ := ClassModel) F (number_l hBase K ω hωEq i) y := by
    constructor
    · intro h
      obtain ⟨j, hij, hjy⟩ := (hGRead i y).mp h
      rcases (hCode i j).mp hij with ⟨hI, hJ⟩ | ⟨hi, hij⟩
      · subst i
        subst j
        exact Or.inl ⟨rfl, Subtype.ext (SecondOrderFunctionLaws.value_unique_l hℳ hU hjy hx)⟩
      · exact Or.inr ⟨hi, (hFRead i y).mpr ⟨j, hij, hjy⟩⟩
    · rintro (⟨hi, hy⟩ | ⟨hi, h⟩)
      · subst i
        subst y
        exact (hGRead l x).mpr ⟨v, (hCode l v).mpr (Or.inl ⟨rfl, rfl⟩), hx⟩
      · obtain ⟨j, hij, hjy⟩ := (hFRead i y).mp h
        exact (hGRead i y).mpr ⟨j, (hCode i j).mpr (Or.inr ⟨hi, hij⟩), hjy⟩
  refine ⟨F, G, hF, hG, of_numbers_l K hωEq L l hF hG hPoint, ?_, ?_⟩
  · intro i y
    exact (hFRead i y).trans (exists_congr (fun j => and_congr (hPRead i j) Iff.rfl))
  · intro i y
    exact (hGRead i y).trans (exists_congr (fun j => and_congr (hQRead i j) Iff.rfl))

#print axioms of_numbers_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyAssignmentUpdate
