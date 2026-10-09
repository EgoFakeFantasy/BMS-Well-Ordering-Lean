import BMSConstructibleBridge.SecondOrderLegacyAssignmentPadding
import BMSConstructibleBridge.PowerlessMemberDefArithmeticSemantics
import BMSConstructibleBridge.PowerlessRelativeClassFiniteMapLift

/-! # 原赋值填充在环境商中的实际纯公式

原 E 只要求是环境 ω 子集，不要求属于相对类。数量词沿实际数码满射
读取全部内部数；连接公式精确刻画填充后沿环境枚举 U 的赋值图。
本文件只验证 AST 的读数，不声称原求值与类内 Sat 已经等价。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyAssignmentSyntax

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax
open PowerlessBMSQuotientCoding PowerlessArithmeticTerms
open PowerlessBMSQuotientArithmetic PowerlessBMSQuotientTranslation

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessArithmetic.structure_l PowerlessBMSQuotientPureTransfer.arithmeticStructure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 守卫数量词的读数；此引理不是对任意宿主谓词的归纳原则。 -/
theorem forall_numbers_l (K : source_coding_l hℳ)
    (P : SecondOrderQuotient.type_l hℳ → Prop) :
    (∀ x, (SecondOrderQuotient.structure_l hℳ).relInterp .membership
      (.cons x (.cons K.omega .nil)) → P x) ↔
      ∀ n : SecondOrderModel.num_l ℳ, P (numberCode_l K n).val := by
  constructor
  · exact fun h n => h _ (numberCode_l K n).property
  · intro h x hx
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x, hx⟩
    have hxEq : (numberCode_l K n).val = x := congrArg Subtype.val hn
    rw [← hxEq]
    exact h n

theorem exists_numbers_l (K : source_coding_l hℳ)
    (P : SecondOrderQuotient.type_l hℳ → Prop) :
    (∃ x, (SecondOrderQuotient.structure_l hℳ).relInterp .membership
      (.cons x (.cons K.omega .nil)) ∧ P x) ↔
      ∃ n : SecondOrderModel.num_l ℳ, P (numberCode_l K n).val := by
  constructor
  · rintro ⟨x, hx, hP⟩
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x, hx⟩
    have hxEq : (numberCode_l K n).val = x := congrArg Subtype.val hn
    exact ⟨n, hxEq.symm ▸ hP⟩
  · exact fun ⟨n, hn⟩ => ⟨_, (numberCode_l K n).property, hn⟩

def parameters_m {Γ Δ : SortContext ℒ} (E c l L z i j : Term ℒ Γ Δ .set) :
    assignment_m [.set, .num, .num, .num, .num, .num, .num] Γ Δ
  | _, .here => E
  | _, .there .here => c
  | _, .there (.there .here) => l
  | _, .there (.there (.there .here)) => L
  | _, .there (.there (.there (.there .here))) => z
  | _, .there (.there (.there (.there (.there .here)))) => i
  | _, .there (.there (.there (.there (.there (.there .here))))) => j

def arithmetic_m : Formula SecondOrderSyntax.signature_m []
    [.set, .num, .num, .num, .num, .num, .num] :=
  SecondOrderLegacyAssignmentPadding.padded_m (.fvar .here) (.fvar (.there .here))
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))

def padded_m {Γ Δ : SortContext ℒ} (ω e E c l L z i j : Term ℒ Γ Δ .set) :
    Formula ℒ Γ Δ :=
  PowerlessArithmeticTranslation.formula_m (Γ := []) ω e (fun v => nomatch v)
    (parameters_m E c l L z i j) arithmetic_m

theorem padded_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (ω e E c l L z i j : Term ℒ Γ Δ .set)
    (aE : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega)
    (vE : SecondOrderModel.set_l ℳ) (vc vl vL vz vi vj : SecondOrderModel.num_l ℳ)
    (hω : ω.eval η = K.omega) (he : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hE : E.eval η = aE.val) (hRep : setRel_l K aE vE)
    (hc : c.eval η = (numberCode_l K vc).val) (hl : l.eval η = (numberCode_l K vl).val)
    (hL : L.eval η = (numberCode_l K vL).val) (hz : z.eval η = (numberCode_l K vz).val)
    (hi : i.eval η = (numberCode_l K vi).val) (hj : j.eval η = (numberCode_l K vj).val) :
    (padded_m ω e E c l L z i j).satisfies η ↔
      SecondOrderLegacyAssignmentPadding.padded_l vE vc vl vL vz vi vj := by
  let ξ : Env (arithmetic_l K) [] [.set, .num, .num, .num, .num, .num, .num] := {
    boundVal := fun v => nomatch v
    freeVal := fun v => match v with
      | .here => aE
      | .there .here => numberCode_l K vc
      | .there (.there .here) => numberCode_l K vl
      | .there (.there (.there .here)) => numberCode_l K vL
      | .there (.there (.there (.there .here))) => numberCode_l K vz
      | .there (.there (.there (.there (.there .here)))) => numberCode_l K vi
      | .there (.there (.there (.there (.there (.there .here))))) => numberCode_l K vj }
  let ξ' : Env ℳ [] [.set, .num, .num, .num, .num, .num, .num] := {
    boundVal := fun v => nomatch v
    freeVal := fun v => match v with
      | .here => vE
      | .there .here => vc
      | .there (.there .here) => vl
      | .there (.there (.there .here)) => vL
      | .there (.there (.there (.there .here))) => vz
      | .there (.there (.there (.there (.there .here)))) => vi
      | .there (.there (.there (.there (.there (.there .here))))) => vj }
  have hτ : agrees_l η (parameters_m E c l L z i j) ξ.freeVal := by
    intro s v
    exact match v with
      | .here => hE
      | .there .here => hc
      | .there (.there .here) => hl
      | .there (.there (.there .here)) => hL
      | .there (.there (.there (.there .here))) => hz
      | .there (.there (.there (.there (.there .here)))) => hi
      | .there (.there (.there (.there (.there (.there .here))))) => hj
  have hRelated : SecondOrderPureTransfer.environments_related_l
      (PowerlessBMSQuotientMultiplication.correspondence_l K) ξ ξ' := by
    constructor
    · intro s v
      nomatch v
    · intro s v
      exact match v with
        | .here => hRep
        | .there .here => numberEquiv_numberCode_l K vc
        | .there (.there .here) => numberEquiv_numberCode_l K vl
        | .there (.there (.there .here)) => numberEquiv_numberCode_l K vL
        | .there (.there (.there (.there .here))) => numberEquiv_numberCode_l K vz
        | .there (.there (.there (.there (.there .here)))) => numberEquiv_numberCode_l K vi
        | .there (.there (.there (.there (.there (.there .here))))) => numberEquiv_numberCode_l K vj
  exact (PowerlessBMSQuotientParameterTransfer.formula_l K arithmetic_m
    (SecondOrderArithmetic.pure_language_m _ rfl) ξ ξ' η ω e (fun v => nomatch v)
    (parameters_m E c l L z i j) hω he (fun v => nomatch v) hτ hRelated).trans
    (SecondOrderLegacyAssignmentPadding.padded_formula_l ξ' _ _ _ _ _ _ _)

def link_l (K : source_coding_l hℳ) (E : SecondOrderModel.set_l ℳ)
    (c l L z : SecondOrderModel.num_l ℳ) (U f : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∀ i y, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f (numberCode_l K i).val y ↔
    ∃ j, SecondOrderLegacyAssignmentPadding.padded_l E c l L z i j ∧
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K j).val y

def link_m {Γ Δ : SortContext ℒ} (ω e E c l L z U f : Term ℒ Γ Δ .set) :
    Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up ω)) <| .forallE .set <|
    .iff (value_m (up (up f)) (.bvar (.there .here)) (.bvar .here)) <|
      .existsE .set <| .conj (member_m (.bvar .here) (up (up (up ω)))) <|
        .conj (padded_m (up (up (up ω))) (up (up (up e))) (up (up (up E)))
          (up (up (up c))) (up (up (up l))) (up (up (up L))) (up (up (up z)))
          (.bvar (.there (.there .here))) (.bvar .here))
          (value_m (up (up (up U))) (.bvar .here) (.bvar (.there .here)))

theorem link_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (ω e E c l L z U f : Term ℒ Γ Δ .set)
    (aE : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega)
    (vE : SecondOrderModel.set_l ℳ) (vc vl vL vz : SecondOrderModel.num_l ℳ)
    (hω : ω.eval η = K.omega) (he : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hE : E.eval η = aE.val) (hRep : setRel_l K aE vE)
    (hc : c.eval η = (numberCode_l K vc).val) (hl : l.eval η = (numberCode_l K vl).val)
    (hL : L.eval η = (numberCode_l K vL).val) (hz : z.eval η = (numberCode_l K vz).val) :
    (link_m ω e E c l L z U f).satisfies η ↔
      link_l K vE vc vl vL vz (U.eval η) (f.eval η) := by
  simp only [link_m, Formula.satisfies, member_m, value_formula_l, up,
    Term.eval_weakenBound, Term.eval, Arguments.eval, Env.pushBound_bound_here,
    Env.pushBound_bound_there]
  rw [hω, forall_numbers_l K]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro y
  apply iff_congr Iff.rfl
  rw [exists_numbers_l K]
  apply exists_congr
  intro j
  apply and_congr _ Iff.rfl
  exact padded_formula_l K _ _ _ _ _ _ _ _ _ _ aE vE vc vl vL vz i j
    (by simpa only [Term.eval_weakenBound] using hω)
    (by simpa only [Term.eval_weakenBound] using he)
    (by simpa only [Term.eval_weakenBound] using hE) hRep
    (by simpa only [Term.eval_weakenBound] using hc)
    (by simpa only [Term.eval_weakenBound] using hl)
    (by simpa only [Term.eval_weakenBound] using hL)
    (by simpa only [Term.eval_weakenBound] using hz) rfl rfl

#print axioms padded_formula_l
#print axioms link_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyAssignmentSyntax
