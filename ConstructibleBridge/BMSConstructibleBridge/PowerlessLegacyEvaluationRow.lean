import BMSConstructibleBridge.PowerlessLegacyAssignmentSyntax
import BMSConstructibleBridge.SecondOrderLegacyFormulaTranslationLength
import BMSConstructibleBridge.PowerlessBMSQuotientStrongInduction

/-! # 原公式求值保持性的环境商归纳行

所有数码与原实数参数均在环境商中解释；只有实际赋值 f 有显式类成员
守卫。行量词覆盖内部合法码、非标准赋值长度和任意默认数值。本文件
验证归纳所用的实际纯公式，不把该公式的存在当成求值保持性证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationRow

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax
open PowerlessBMSQuotientCoding PowerlessArithmeticTerms PowerlessBMSQuotientArithmetic
open PowerlessBMSQuotientTranslation
open PowerlessLegacyAssignmentSyntax (link_m link_l forall_numbers_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessArithmetic.structure_l PowerlessBMSQuotientPureTransfer.arithmeticStructure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev raw_up {Γ Δ : SortContext SecondOrderSyntax.signature_m}
    {s : SecondOrderSyntax.sort_m} (t : Term SecondOrderSyntax.signature_m Γ Δ s) :=
  t.weakenBound SecondOrderSyntax.sort_m.num

def guard_parameters_m {Γ Δ : SortContext ℒ} (E C n l c q L : Term ℒ Γ Δ .set) :
    assignment_m [.set, .set, .num, .num, .num, .num, .num] Γ Δ
  | _, .here => E
  | _, .there .here => C
  | _, .there (.there .here) => n
  | _, .there (.there (.there .here)) => l
  | _, .there (.there (.there (.there .here))) => c
  | _, .there (.there (.there (.there (.there .here)))) => q
  | _, .there (.there (.there (.there (.there (.there .here))))) => L

def guard_arithmetic_m : Formula SecondOrderSyntax.signature_m []
    [.set, .set, .num, .num, .num, .num, .num] :=
  .conj (SecondOrderAssignmentSyntax.formula_m (.fvar .here) (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there (.there .here))))) <|
    .conj (SecondOrderLegacyFormulaTranslation.query_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there (.there .here)))))))
      (SecondOrderLegacyFormulaTranslationLength.bound_m (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there (.there (.there (.there .here))))))))

def guard_m {Γ Δ : SortContext ℒ} (ω e E C n l c q L : Term ℒ Γ Δ .set) :
    Formula ℒ Γ Δ :=
  PowerlessArithmeticTranslation.formula_m (Γ := []) ω e (fun v => nomatch v)
    (guard_parameters_m E C n l c q L) guard_arithmetic_m

def guard_l (E C : SecondOrderModel.set_l ℳ) (n l c q L : SecondOrderModel.num_l ℳ) : Prop :=
  SecondOrderAssignmentSyntax.valid_l E c l ∧
    SecondOrderLegacyFormulaTranslation.query_l C n l q ∧
      SecondOrderLegacyFormulaTranslationLength.bound_l l n L

theorem guard_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (ω e E C n l c q L : Term ℒ Γ Δ .set)
    (aE aC : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega)
    (vE vC : SecondOrderModel.set_l ℳ) (vn vl vc vq vL : SecondOrderModel.num_l ℳ)
    (hω : ω.eval η = K.omega) (he : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hE : E.eval η = aE.val) (hC : C.eval η = aC.val)
    (hRepE : setRel_l K aE vE) (hRepC : setRel_l K aC vC)
    (hn : n.eval η = (numberCode_l K vn).val)
    (hl : l.eval η = (numberCode_l K vl).val)
    (hc : c.eval η = (numberCode_l K vc).val)
    (hq : q.eval η = (numberCode_l K vq).val)
    (hL : L.eval η = (numberCode_l K vL).val) :
    (guard_m ω e E C n l c q L).satisfies η ↔ guard_l vE vC vn vl vc vq vL := by
  let ξ : Env (arithmetic_l K) [] [.set, .set, .num, .num, .num, .num, .num] := {
    boundVal := fun v => nomatch v
    freeVal := fun v => match v with
      | .here => aE
      | .there .here => aC
      | .there (.there .here) => numberCode_l K vn
      | .there (.there (.there .here)) => numberCode_l K vl
      | .there (.there (.there (.there .here))) => numberCode_l K vc
      | .there (.there (.there (.there (.there .here)))) => numberCode_l K vq
      | .there (.there (.there (.there (.there (.there .here))))) => numberCode_l K vL }
  let ξ' : Env ℳ [] [.set, .set, .num, .num, .num, .num, .num] := {
    boundVal := fun v => nomatch v
    freeVal := fun v => match v with
      | .here => vE
      | .there .here => vC
      | .there (.there .here) => vn
      | .there (.there (.there .here)) => vl
      | .there (.there (.there (.there .here))) => vc
      | .there (.there (.there (.there (.there .here)))) => vq
      | .there (.there (.there (.there (.there (.there .here))))) => vL }
  have hτ : agrees_l η (guard_parameters_m E C n l c q L) ξ.freeVal := by
    intro s v
    exact match v with
      | .here => hE
      | .there .here => hC
      | .there (.there .here) => hn
      | .there (.there (.there .here)) => hl
      | .there (.there (.there (.there .here))) => hc
      | .there (.there (.there (.there (.there .here)))) => hq
      | .there (.there (.there (.there (.there (.there .here))))) => hL
  have hRelated : SecondOrderPureTransfer.environments_related_l
      (PowerlessBMSQuotientMultiplication.correspondence_l K) ξ ξ' := by
    constructor
    · intro s v
      nomatch v
    · intro s v
      exact match v with
        | .here => hRepE
        | .there .here => hRepC
        | .there (.there .here) => numberEquiv_numberCode_l K vn
        | .there (.there (.there .here)) => numberEquiv_numberCode_l K vl
        | .there (.there (.there (.there .here))) => numberEquiv_numberCode_l K vc
        | .there (.there (.there (.there (.there .here)))) => numberEquiv_numberCode_l K vq
        | .there (.there (.there (.there (.there (.there .here))))) => numberEquiv_numberCode_l K vL
  refine (PowerlessBMSQuotientParameterTransfer.formula_l K guard_arithmetic_m
    (SecondOrderArithmetic.pure_language_m _ rfl) ξ ξ' η ω e (fun v => nomatch v)
    (guard_parameters_m E C n l c q L) hω he (fun v => nomatch v) hτ hRelated).trans ?_
  simp only [guard_arithmetic_m, guard_l, Formula.satisfies, SecondOrderAssignmentSyntax.raw_l,
    SecondOrderLegacyFormulaTranslation.query_formula_l,
    SecondOrderLegacyFormulaTranslationLength.bound_formula_l, Term.eval]
  rfl

def source_parameters_m {Γ Δ : SortContext ℒ} (T n l c : Term ℒ Γ Δ .set) :
    assignment_m [.set, .num, .num, .num] Γ Δ
  | _, .here => T
  | _, .there .here => n
  | _, .there (.there .here) => l
  | _, .there (.there (.there .here)) => c

def source_arithmetic_m : Formula SecondOrderSyntax.signature_m [] [.set, .num, .num, .num] :=
  .existsE .num <| .conj
    (PrimitiveFormulas.pair_m (raw_up (.fvar (.there (.there .here))))
      (raw_up (.fvar (.there (.there (.there .here))))) (.bvar .here))
    (GraphSyntax.edge_m (raw_up (.fvar .here))
      (raw_up (.fvar (.there .here))) (.bvar .here))

def source_m {Γ Δ : SortContext ℒ} (ω e T n l c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessArithmeticTranslation.formula_m (Γ := []) ω e (fun v => nomatch v)
    (source_parameters_m T n l c) source_arithmetic_m

theorem source_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (ω e T n l c : Term ℒ Γ Δ .set)
    (aT : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega)
    (vT : SecondOrderModel.set_l ℳ) (vn vl vc : SecondOrderModel.num_l ℳ)
    (hω : ω.eval η = K.omega) (he : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hT : T.eval η = aT.val) (hRepT : setRel_l K aT vT)
    (hn : n.eval η = (numberCode_l K vn).val) (hl : l.eval η = (numberCode_l K vl).val)
    (hc : c.eval η = (numberCode_l K vc).val) :
    (source_m ω e T n l c).satisfies η ↔
      SecondOrderPairing.relation_l vT vn (SecondOrderPairing.value_l vl vc) := by
  let ξ : Env (arithmetic_l K) [] [.set, .num, .num, .num] := {
    boundVal := fun v => nomatch v
    freeVal := fun v => match v with
      | .here => aT
      | .there .here => numberCode_l K vn
      | .there (.there .here) => numberCode_l K vl
      | .there (.there (.there .here)) => numberCode_l K vc }
  let ξ' : Env ℳ [] [.set, .num, .num, .num] := {
    boundVal := fun v => nomatch v
    freeVal := fun v => match v with
      | .here => vT
      | .there .here => vn
      | .there (.there .here) => vl
      | .there (.there (.there .here)) => vc }
  have hτ : agrees_l η (source_parameters_m T n l c) ξ.freeVal := by
    intro s v
    exact match v with
      | .here => hT
      | .there .here => hn
      | .there (.there .here) => hl
      | .there (.there (.there .here)) => hc
  have hRelated : SecondOrderPureTransfer.environments_related_l
      (PowerlessBMSQuotientMultiplication.correspondence_l K) ξ ξ' := by
    constructor
    · intro s v
      nomatch v
    · intro s v
      exact match v with
        | .here => hRepT
        | .there .here => numberEquiv_numberCode_l K vn
        | .there (.there .here) => numberEquiv_numberCode_l K vl
        | .there (.there (.there .here)) => numberEquiv_numberCode_l K vc
  refine (PowerlessBMSQuotientParameterTransfer.formula_l K source_arithmetic_m
    (SecondOrderArithmetic.pure_language_m _ rfl) ξ ξ' η ω e (fun v => nomatch v)
    (source_parameters_m T n l c) hω he (fun v => nomatch v) hτ hRelated).trans ?_
  simp only [source_arithmetic_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l, raw_up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩

#print axioms guard_formula_l
#print axioms source_formula_l

def body_m {Γ Δ : SortContext ℒ}
    (ω e B A E C T U R n l c q L z f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (guard_m ω e E C n l c q L) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B f) <| .imp (map_m f L A) <|
      .imp (link_m ω e E c l L z U f) <|
        .iff (source_m ω e T n l c) (value_m R q f)

def body_l (K : source_coding_l hℳ) (B A U R : SecondOrderQuotient.type_l hℳ)
    (E C T : SecondOrderModel.set_l ℳ) (n l c q L z : SecondOrderModel.num_l ℳ)
    (f : SecondOrderQuotient.type_l hℳ) : Prop :=
  guard_l E C n l c q L → PowerlessRelativeClassCorrespondence.member_l hℳ B f →
    map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f (numberCode_l K L).val A →
      link_l K E c l L z U f →
        (SecondOrderPairing.relation_l T n (SecondOrderPairing.value_l l c) ↔
          value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R (numberCode_l K q).val f)

theorem body_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (ω e B A E C T U R n l c q L z f : Term ℒ Γ Δ .set)
    (aE aC aT : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega)
    (vE vC vT : SecondOrderModel.set_l ℳ) (vn vl vc vq vL vz : SecondOrderModel.num_l ℳ)
    (hω : ω.eval η = K.omega) (he : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hE : E.eval η = aE.val) (hC : C.eval η = aC.val) (hT : T.eval η = aT.val)
    (hRepE : setRel_l K aE vE) (hRepC : setRel_l K aC vC) (hRepT : setRel_l K aT vT)
    (hn : n.eval η = (numberCode_l K vn).val) (hl : l.eval η = (numberCode_l K vl).val)
    (hc : c.eval η = (numberCode_l K vc).val) (hq : q.eval η = (numberCode_l K vq).val)
    (hL : L.eval η = (numberCode_l K vL).val) (hz : z.eval η = (numberCode_l K vz).val) :
    (body_m ω e B A E C T U R n l c q L z f).satisfies η ↔
      body_l K (B.eval η) (A.eval η) (U.eval η) (R.eval η) vE vC vT vn vl vc vq vL vz (f.eval η) := by
  have hGuard := guard_formula_l K η ω e E C n l c q L aE aC vE vC vn vl vc vq vL
    hω he hE hC hRepE hRepC hn hl hc hq hL
  have hLink := PowerlessLegacyAssignmentSyntax.link_formula_l K η ω e E c l L z U f aE vE vc vl vL vz
    hω he hE hRepE hc hl hL hz
  have hSource := source_formula_l K η ω e T n l c aT vT vn vl vc hω he hT hRepT hn hl hc
  simp only [body_m, body_l, Formula.satisfies, hGuard, hLink, hSource,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l, value_formula_l, hL, hq]
  rfl

def row_l (K : source_coding_l hℳ) (B A U R : SecondOrderQuotient.type_l hℳ)
    (E C T : SecondOrderModel.set_l ℳ) (n : SecondOrderModel.num_l ℳ) : Prop :=
  ∀ l c q L z f, body_l K B A U R E C T n l c q L z f

def row_m {Γ Δ : SortContext ℒ} (ω e B A E C T U R n : Term ℒ Γ Δ .set) :
    Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up ω)) <|
    .forallE .set <| .imp (member_m (.bvar .here) (up (up ω))) <|
      .forallE .set <| .imp (member_m (.bvar .here) (up (up (up ω)))) <|
        .forallE .set <| .imp (member_m (.bvar .here) (up (up (up (up ω))))) <|
          .forallE .set <| .imp (member_m (.bvar .here) (up (up (up (up (up ω)))))) <|
            .forallE .set <|
              let w (t : Term ℒ Γ Δ .set) := up (up (up (up (up (up t)))))
              body_m (w ω) (w e) (w B) (w A) (w E) (w C) (w T) (w U) (w R) (w n)
                (.bvar (.there (.there (.there (.there (.there .here))))))
                (.bvar (.there (.there (.there (.there .here)))))
                (.bvar (.there (.there (.there .here))))
                (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem row_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (ω e B A E C T U R n : Term ℒ Γ Δ .set)
    (aE aC aT : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega)
    (vE vC vT : SecondOrderModel.set_l ℳ) (vn : SecondOrderModel.num_l ℳ)
    (hω : ω.eval η = K.omega) (he : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hE : E.eval η = aE.val) (hC : C.eval η = aC.val) (hT : T.eval η = aT.val)
    (hRepE : setRel_l K aE vE) (hRepC : setRel_l K aC vC) (hRepT : setRel_l K aT vT)
    (hn : n.eval η = (numberCode_l K vn).val) :
    (row_m ω e B A E C T U R n).satisfies η ↔
      row_l K (B.eval η) (A.eval η) (U.eval η) (R.eval η) vE vC vT vn := by
  simp only [row_m, Formula.satisfies, member_m, Arguments.eval, up,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]
  rw [hω, forall_numbers_l K]
  unfold row_l
  apply forall_congr'
  intro l
  rw [forall_numbers_l K]
  apply forall_congr'
  intro c
  rw [forall_numbers_l K]
  apply forall_congr'
  intro q
  rw [forall_numbers_l K]
  apply forall_congr'
  intro L
  rw [forall_numbers_l K]
  apply forall_congr'
  intro z
  apply forall_congr'
  intro f
  let ξ : Env (SecondOrderQuotient.structure_l hℳ)
      (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ :=
    ((((((η.pushBound (numberCode_l K l).val).pushBound (numberCode_l K c).val).pushBound
      (numberCode_l K q).val).pushBound (numberCode_l K L).val).pushBound (numberCode_l K z).val).pushBound f)
  let w (t : Term ℒ Γ Δ .set) := up (up (up (up (up (up t)))))
  have h := body_formula_l K ξ (w ω) (w e) (w B) (w A) (w E) (w C) (w T) (w U) (w R) (w n)
    (.bvar (.there (.there (.there (.there (.there .here))))))
    (.bvar (.there (.there (.there (.there .here)))))
    (.bvar (.there (.there (.there .here))))
    (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)
    aE aC aT vE vC vT vn l c q L z
    (by simpa only [w, up, ξ, Term.eval_weakenBound] using hω)
    (by simpa only [w, up, ξ, Term.eval_weakenBound] using he)
    (by simpa only [w, up, ξ, Term.eval_weakenBound] using hE)
    (by simpa only [w, up, ξ, Term.eval_weakenBound] using hC)
    (by simpa only [w, up, ξ, Term.eval_weakenBound] using hT) hRepE hRepC hRepT
    (by simpa only [w, up, ξ, Term.eval_weakenBound] using hn) rfl rfl rfl rfl rfl
  simpa only [w, up, ξ, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here,
    Env.pushBound_bound_there] using h

#print axioms body_formula_l
#print axioms row_formula_l


end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationRow
