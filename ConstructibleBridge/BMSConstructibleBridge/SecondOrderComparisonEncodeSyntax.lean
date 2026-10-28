import BMSConstructibleBridge.SecondOrderComparisonReal
import BMSConstructibleBridge.PowerlessMemberDefArithmeticSemantics

/-! # 唯一比较实数的纯隶属编码公式

输出是实际 ω 子集。每一对内部自然数上的比较位使用原配数的纯公式，
并与完整模型中的实际枚举查询对应；不替换为另一种配数算法。
全部数量词由 ω 守卫，不假设模型外部标准性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonEncodeSyntax

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderObjectSyntax

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

def template_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let ω : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .fvar .here
  let e : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let W : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let f : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let P : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  .conj (ThirdOrderTheory.subset_m (.fvar (.there (.there .here))) (.fvar .here)) <|
    .forallE .set <| .forallE .set <|
      .imp (member_m (.bvar (.there .here)) ω) <| .imp (member_m (.bvar .here) ω) <|
        .iff (PowerlessMemberDefSyntax.edge_m ω e W (.bvar (.there .here)) (.bvar .here))
          (SecondOrderComparisonReal.query_m f P (.bvar (.there .here)) (.bvar .here))

private def bind_m {Γ Δ : SortContext ℒ} (ω e W f P : Term ℒ Γ Δ .set) :
    Substitution ℒ [] [.set, .set, .set, .set, .set] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => ω
    | .there .here => e
    | .there (.there .here) => W
    | .there (.there (.there .here)) => f
    | .there (.there (.there (.there .here))) => P)

def formula_m {Γ Δ : SortContext ℒ} (ω e W f P : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  template_m.substitute (bind_m ω e W f P)

def encoded_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e W f P : carrier_l 𝒩) : Prop :=
  template_m.satisfies (((((Env.empty.pushFree P).pushFree f).pushFree W).pushFree e).pushFree ω)

theorem guard_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {ω e W f P : carrier_l 𝒩}
    (h : encoded_l (𝒩 := 𝒩) ω e W f P) : ThirdOrderSemantics.subset_l (ℳ := 𝒩) W ω := by
  exact h.1

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e W f P : Term ℒ Γ Δ .set) :
    (formula_m ω e W f P).satisfies η ↔
      encoded_l (ω.eval η) (e.eval η) (W.eval η) (f.eval η) (P.eval η) := by
  refine (Formula.satisfies_substitute η _ template_m).trans ?_
  apply Iff.of_eq
  apply congrArg (fun ξ => template_m.satisfies ξ)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    rcases v with _ | _ | _ | _ | _ | v
    all_goals first | rfl | nomatch v

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem reading_l (K : source_coding_l hℳ)
    (A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (W : SecondOrderModel.set_l ℳ)
    (hA : setRel_l K A W) (f P : SecondOrderQuotient.type_l hℳ) :
    encoded_l (𝒩 := 𝒱) K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val A.val f P ↔
      SecondOrderComparisonReal.spec_l K f P W := by
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set] :=
    (((((Env.empty.pushFree P).pushFree f).pushFree A.val).pushFree
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val).pushFree K.omega)
  let w : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .fvar .here
  let z : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let S : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let i : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .bvar (.there .here)
  let j : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .bvar .here
  have hEdge a b : (PowerlessMemberDefSyntax.edge_m w z S i j).satisfies
      ((η.pushBound (numberCode_l K a).val).pushBound (numberCode_l K b).val) ↔
      SecondOrderPairing.relation_l W a b :=
    PowerlessMemberDefArithmeticSemantics.edge_formula_l K _ w z S i j A W a b
      rfl rfl rfl rfl rfl hA
  have hBody : encoded_l (𝒩 := 𝒱) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val A.val f P ↔
      subset_l (ℳ := 𝒱) A.val K.omega ∧
        ∀ a b, SecondOrderQuotient.mem_l hℳ a K.omega → SecondOrderQuotient.mem_l hℳ b K.omega →
          ((PowerlessMemberDefSyntax.edge_m w z S i j).satisfies ((η.pushBound a).pushBound b) ↔
            ∃ x y, value_l (ℳ := 𝒱) f a x ∧ value_l (ℳ := 𝒱) f b y ∧ value_l (ℳ := 𝒱) P x y) := by
    simp only [encoded_l, template_m, Formula.satisfies, subset_formula_l,
      SecondOrderComparisonReal.query_formula_l, member_m, Arguments.eval, Term.eval]
    rfl
  rw [hBody]
  constructor
  · intro h a b
    exact (hEdge a b).symm.trans
      (h.2 _ _ (numberCode_l K a).property (numberCode_l K b).property)
  · intro h
    refine ⟨A.property, ?_⟩
    intro a b ha hb
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨a, ha⟩
    obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨b, hb⟩
    have hn' : (numberCode_l K n).val = a := congrArg Subtype.val hn
    have hm' : (numberCode_l K m).val = b := congrArg Subtype.val hm
    simpa only [hn', hm'] using (hEdge n m).trans (h n m)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonEncodeSyntax
