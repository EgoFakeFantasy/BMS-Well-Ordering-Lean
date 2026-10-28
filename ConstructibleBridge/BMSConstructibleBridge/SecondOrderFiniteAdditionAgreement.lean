import BMSConstructibleBridge.PowerlessRelativeLimitFiniteAdditionDerives

/-! # 内部有限轨迹与实际 ω 迭代图逐点一致

归纳性质同时量化任意较长的有限轨迹，避免对模型内部长度作宿主归纳，
也避免先假定类内已有无限迭代图。此处的无限图仅作为原商中的比较对象。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteAdditionAgreement

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding SecondOrderObjectSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

def formula_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let n : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .fvar .here
  let ω : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let e : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let a : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let F : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let t : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .bvar (.there .here)
  let g : Term ℒ [.set, .set] [.set, .set, .set, .set, .set] .set := .bvar .here
  .forallE .set <| .forallE .set <| .imp (member_m t ω) <|
    .imp (PowerlessAdditionFiniteSyntax.trace_m ω e a t g) <|
      .imp (.disj (member_m n t) (.equal n t)) <| .forallE .set <|
        .imp (value_m (g.weakenBound SetTheory.SetSort.set) (n.weakenBound SetTheory.SetSort.set) (.bvar .here))
          (value_m (F.weakenBound SetTheory.SetSort.set) (n.weakenBound SetTheory.SetSort.set) (.bvar .here))

theorem formula_l (ω e a F n : SecondOrderQuotient.type_l hℳ) : formula_m.satisfies
    (((((Env.empty (M := SecondOrderQuotient.structure_l hℳ)).pushFree F).pushFree a).pushFree e).pushFree ω |>.pushFree n) ↔
      ∀ t g, SecondOrderQuotient.mem_l hℳ t ω →
        PowerlessAdditionFinite.trace_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω e a t g →
          SecondOrderQuotient.mem_l hℳ n t ∨ n = t → ∀ c,
            value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g n c →
              value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F n c := by
  simp only [formula_m, Formula.satisfies, PowerlessAdditionFiniteSyntax.trace_formula_l,
    ThirdOrderSemantics.value_formula_l, member_m, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

theorem agreement_l (K : source_coding_l hℳ) {a F : SecondOrderQuotient.type_l hℳ}
    (hF : PowerlessAddition.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val a F) (n : SecondOrderModel.num_l ℳ) :
    ∀ t g, SecondOrderQuotient.mem_l hℳ t K.omega →
      PowerlessAdditionFinite.trace_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega
        (numberCode_l K (SecondOrderModel.zero_l ℳ)).val a t g →
          SecondOrderQuotient.mem_l hℳ (numberCode_l K n).val t ∨ (numberCode_l K n).val = t → ∀ c,
            value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g (numberCode_l K n).val c →
              value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F (numberCode_l K n).val c := by
  obtain ⟨R, hMap, h₀, hStep⟩ := hF
  let e := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set, .set] :=
    (((Env.empty (M := SecondOrderQuotient.structure_l hℳ)).pushFree F).pushFree a).pushFree e |>.pushFree K.omega
  have h := PowerlessBMSQuotientInduction.induction_l K formula_m η ?_ ?_ n
  · exact (formula_l K.omega e a F _).mp h
  · apply (formula_l K.omega e a F _).mpr
    intro t g _ hg _ c hc
    obtain ⟨T, _, hG, hZero, _⟩ := hg
    have hca := PowerlessBMSQuotientRecursion.value_unique_l (hM := hℳ) hG hc hZero
    exact hca.symm ▸ h₀
  · intro i hi
    apply (formula_l K.omega e a F _).mpr
    intro t g ht hg hBound c hc
    let k := (numberCode_l K i).val
    let m := (numberCode_l K (SecondOrderModel.succ_l i)).val
    have hSucc := PowerlessBMSQuotientSuccessor.successor_l K i
    have hωOrd : SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) K.omega :=
      SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec
    have htOrd : SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) t := by
      apply SetTheory.Structure.IsOrdinal.mem hωOrd
      exact ht
    have hkt : SecondOrderQuotient.mem_l hℳ k t := by
      rcases hBound with hm | hm
      · exact htOrd.transitive m hm k ((hSucc k).mpr (Or.inr rfl))
      · exact hm ▸ (hSucc k).mpr (Or.inr rfl)
    have hTrace := hg
    obtain ⟨T, hT, hG, _, hGStep⟩ := hg
    obtain ⟨x, hx, _⟩ := hG.2 k ((hT k).mpr (Or.inl hkt))
    have hFx := (formula_l K.omega e a F k).mp hi t g ht hTrace (Or.inl hkt) x hx.2
    obtain ⟨y, hy, _⟩ := hMap.2 m (numberCode_l K (SecondOrderModel.succ_l i)).property
    have hxy := (PowerlessAddition.step_formula_l K.omega x y).mp
      (hStep k m x y (numberCode_l K i).property hSucc hFx hy.2)
    have hxc := hGStep k m x c hkt hSucc hx.2 hc
    have hcy := PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) (a := x) (b := c) (c := y) hxc hxy
    exact hcy.symm ▸ hy.2

theorem value_l (K : source_coding_l hℳ) {a F n g c : SecondOrderQuotient.type_l hℳ}
    (hF : PowerlessAddition.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val a F)
    (hn : SecondOrderQuotient.mem_l hℳ n K.omega)
    (hg : PowerlessAdditionFinite.trace_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val a n g)
    (hc : ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g n c) :
    ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F n c := by
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have hEq : (numberCode_l K i).val = n := congrArg Subtype.val hi
  have h := agreement_l K hF i n g hn hg (Or.inr hEq) c
  rw [hEq] at h
  exact h hc

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteAdditionAgreement
