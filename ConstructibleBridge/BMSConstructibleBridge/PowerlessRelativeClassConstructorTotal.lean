import BMSConstructibleBridge.PowerlessRelativeClassConstructorBounds
import BMSConstructibleBridge.PowerlessBMSQuotientConstructorTotal

/-! # 实际原构造子的类内全域唯一性

加法见证用已证类内实际加法图重建，配数的中间自然数由同一 ω 收回类内。
因此原商合法构造子可反向搬入类，不假定完整源模型或 Type 层选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassConstructorTotal

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem code_from_ambient_l (K : source_coding_l hℳ) {ω e T a b c : type_l hℳ B}
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
    (ha : mem_l hℳ a.val K.omega) (hb : mem_l hℳ b.val K.omega)
    (hCode : PowerlessPairingCode.code_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val T.val a.val b.val c.val) :
    PowerlessPairingCode.code_l (ℳ := structure_l hℳ B hBase) ω e T a b c := by
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨a.val, ha⟩
  obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨b.val, hb⟩
  have haEq : a.val = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
  have hbEq : b.val = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
  rw [haEq, hbEq] at hCode
  obtain ⟨v, hv, hc⟩ := (PowerlessBMSQuotientPairingBounds.instance_l K hT hSpec i j c.val).mp hCode
  let code (k : SecondOrderModel.num_l ℳ) : type_l hℳ B :=
    ⟨(numberCode_l K k).val, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property
      (hω.symm ▸ (numberCode_l K k).property)⟩
  refine ⟨code (SecondOrderModel.add_l i j), code v, ?_, ?_, ?_⟩
  · exact (PowerlessRelativeClassAdditionAbsolute.instance_l K hω he haEq hbEq).mpr rfl
  · apply (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) T _ _).mpr
    exact (hSpec _ _).mpr hv
  · exact (PowerlessRelativeClassAdditionAbsolute.instance_l K hω he (a := code v) rfl haEq).mpr hc

theorem constructor_from_ambient_l (K : source_coding_l hℳ) {ω e T t a b n : type_l hℳ B}
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
    (hConstructor : PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val T.val t.val a.val b.val n.val) :
    PowerlessFormulaConstructor.constructor_l (ℳ := structure_l hℳ B hBase) ω e T t a b n := by
  obtain ⟨ha, hb, p, hp, ht, hpω, c, hc, hn⟩ := hConstructor
  have hcω := PowerlessFormulaConstructorBounded.code_natural_l K hT ht hc
  let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property (hω.symm ▸ hpω)⟩
  let c' : type_l hℳ B := ⟨c, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property (hω.symm ▸ hcω)⟩
  have hMember {x : SecondOrderQuotient.type_l hℳ} (hx : mem_l hℳ x K.omega) : mem_l hℳ x ω.val := hω.symm ▸ hx
  exact ⟨hMember ha, hMember hb, p', code_from_ambient_l K hω he hT hSpec ha hb hp,
    hMember ht, hMember hpω, c', code_from_ambient_l K hω he hT hSpec ht hpω hc,
    (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) c' n).mpr hn⟩

def functional_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e T : carrier_l 𝒩) : Prop :=
  ∀ t, member_l 𝒩 t ω → ∀ a, member_l 𝒩 a ω → ∀ b, member_l 𝒩 b ω →
    ∃ n, member_l 𝒩 n ω ∧ PowerlessFormulaConstructor.constructor_l ω e T t a b n ∧
      ∀ m, PowerlessFormulaConstructor.constructor_l ω e T t a b m → m = n

theorem functional_of_spec_l (K : source_coding_l hℳ) {ω e T : type_l hℳ B}
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val) :
    functional_l (𝒩 := structure_l hℳ B hBase) ω e T := by
  intro t ht a ha b hb
  have ht' : mem_l hℳ t.val K.omega := hω ▸ ht
  have ha' : mem_l hℳ a.val K.omega := hω ▸ ha
  have hb' : mem_l hℳ b.val K.omega := hω ▸ hb
  obtain ⟨n, hnω, hn⟩ := PowerlessBMSQuotientConstructorTotal.exists_l K hT hSpec ht' ha' hb'
  let n' : type_l hℳ B := ⟨n, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property (hω.symm ▸ hnω)⟩
  refine ⟨n', (show mem_l hℳ n ω.val from hω.symm ▸ hnω),
    constructor_from_ambient_l K hω he hT hSpec hn, ?_⟩
  intro m hm
  have hm' := PowerlessRelativeClassConstructorBounds.constructor_to_ambient_l (hω.symm ▸ K.omega_spec) hm
  rw [hω, he] at hm'
  exact Subtype.ext (PowerlessBMSQuotientConstructorTotal.unique_l K hT hSpec hm' hn)

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def functional_m {Γ Δ : SortContext ℒ} (ω e T : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up ω)) <|
    .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up ω))) <|
      .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up (up ω)))) <|
        .existsE .set <|
          let t : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
          let a : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
          let b : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
          let n : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
          .conj (SecondOrderObjectSyntax.member_m n (w ω)) <|
            .conj (PowerlessFormulaConstructor.constructor_m (w ω) (w e) (w T) t a b n) <|
              .forallE .set <| .imp
                (PowerlessFormulaConstructor.constructor_m (up (w ω)) (up (w e)) (up (w T)) (up t) (up a) (up b) (.bvar .here))
                (.equal (.bvar .here) (up n))

theorem functional_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e T : Term ℒ Γ Δ .set) :
    (functional_m ω e T).satisfies η ↔ functional_l (ω.eval η) (e.eval η) (T.eval η) := by
  simp only [functional_m, functional_l, Formula.satisfies, PowerlessFormulaConstructor.constructor_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms constructor_from_ambient_l
#print axioms functional_of_spec_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassConstructorTotal
