import BMSConstructibleBridge.PowerlessLegacyEvaluationRow

/-! # 全部原商赋值上的求值保持归纳行

复用原码守卫、原求值和填充连接的实际纯公式。正文不含赋值的
Class 成员守卫，行量词覆盖全部内部长度、默认值和原商赋值。
本模块只核对实际归纳正文，不把正文的存在当成求值保持证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationRawRow

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax
open PowerlessBMSQuotientCoding
open PowerlessLegacyEvaluationRow (guard_m guard_l guard_formula_l source_m source_formula_l)
open PowerlessLegacyAssignmentSyntax (link_m link_l forall_numbers_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def body_m {Γ Δ : SortContext ℒ}
    (ω e A E C T U R n l c q L z f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (guard_m ω e E C n l c q L) <| .imp (map_m f L A) <|
    .imp (link_m ω e E c l L z U f) <|
      .iff (source_m ω e T n l c) (value_m R q f)

def body_l (K : source_coding_l hℳ) (A U R : SecondOrderQuotient.type_l hℳ)
    (E C T : SecondOrderModel.set_l ℳ) (n l c q L z : SecondOrderModel.num_l ℳ)
    (f : SecondOrderQuotient.type_l hℳ) : Prop :=
  guard_l E C n l c q L →
    map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f (numberCode_l K L).val A →
      link_l K E c l L z U f →
        (SecondOrderPairing.relation_l T n (SecondOrderPairing.value_l l c) ↔
          value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R (numberCode_l K q).val f)

theorem body_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (ω e A E C T U R n l c q L z f : Term ℒ Γ Δ .set)
    (aE aC aT : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega)
    (vE vC vT : SecondOrderModel.set_l ℳ) (vn vl vc vq vL vz : SecondOrderModel.num_l ℳ)
    (hω : ω.eval η = K.omega) (he : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hE : E.eval η = aE.val) (hC : C.eval η = aC.val) (hT : T.eval η = aT.val)
    (hRepE : setRel_l K aE vE) (hRepC : setRel_l K aC vC) (hRepT : setRel_l K aT vT)
    (hn : n.eval η = (numberCode_l K vn).val) (hl : l.eval η = (numberCode_l K vl).val)
    (hc : c.eval η = (numberCode_l K vc).val) (hq : q.eval η = (numberCode_l K vq).val)
    (hL : L.eval η = (numberCode_l K vL).val) (hz : z.eval η = (numberCode_l K vz).val) :
    (body_m ω e A E C T U R n l c q L z f).satisfies η ↔
      body_l K (A.eval η) (U.eval η) (R.eval η) vE vC vT vn vl vc vq vL vz (f.eval η) := by
  have hGuard := guard_formula_l K η ω e E C n l c q L aE aC vE vC vn vl vc vq vL
    hω he hE hC hRepE hRepC hn hl hc hq hL
  have hLink := PowerlessLegacyAssignmentSyntax.link_formula_l K η ω e E c l L z U f aE vE vc vl vL vz
    hω he hE hRepE hc hl hL hz
  have hSource := source_formula_l K η ω e T n l c aT vT vn vl vc hω he hT hRepT hn hl hc
  simp only [body_m, body_l, Formula.satisfies, hGuard, hLink, hSource,
    map_formula_l, value_formula_l, hL, hq]

def row_l (K : source_coding_l hℳ) (A U R : SecondOrderQuotient.type_l hℳ)
    (E C T : SecondOrderModel.set_l ℳ) (n : SecondOrderModel.num_l ℳ) : Prop :=
  ∀ l c q L z f, body_l K A U R E C T n l c q L z f

def row_m {Γ Δ : SortContext ℒ} (ω e A E C T U R n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up ω)) <|
    .forallE .set <| .imp (member_m (.bvar .here) (up (up ω))) <|
      .forallE .set <| .imp (member_m (.bvar .here) (up (up (up ω)))) <|
        .forallE .set <| .imp (member_m (.bvar .here) (up (up (up (up ω))))) <|
          .forallE .set <| .imp (member_m (.bvar .here) (up (up (up (up (up ω)))))) <|
            .forallE .set <|
              let w (t : Term ℒ Γ Δ .set) := up (up (up (up (up (up t)))))
              body_m (w ω) (w e) (w A) (w E) (w C) (w T) (w U) (w R) (w n)
                (.bvar (.there (.there (.there (.there (.there .here))))))
                (.bvar (.there (.there (.there (.there .here)))))
                (.bvar (.there (.there (.there .here))))
                (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem row_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (ω e A E C T U R n : Term ℒ Γ Δ .set)
    (aE aC aT : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega)
    (vE vC vT : SecondOrderModel.set_l ℳ) (vn : SecondOrderModel.num_l ℳ)
    (hω : ω.eval η = K.omega) (he : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hE : E.eval η = aE.val) (hC : C.eval η = aC.val) (hT : T.eval η = aT.val)
    (hRepE : setRel_l K aE vE) (hRepC : setRel_l K aC vC) (hRepT : setRel_l K aT vT)
    (hn : n.eval η = (numberCode_l K vn).val) :
    (row_m ω e A E C T U R n).satisfies η ↔
      row_l K (A.eval η) (U.eval η) (R.eval η) vE vC vT vn := by
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
  have h := body_formula_l K ξ (w ω) (w e) (w A) (w E) (w C) (w T) (w U) (w R) (w n)
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

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationRawRow
