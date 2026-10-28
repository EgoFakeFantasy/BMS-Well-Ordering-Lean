import BMSConstructibleBridge.PowerlessFunctionTraceBounded
import BMSConstructibleBridge.SecondOrderFiniteAdditionAgreement
import BMSConstructibleBridge.PowerlessFunctionIteration

/-! # 任意集合自映射的有限轨迹与实际无限迭代逐点一致

归纳公式同时比较任意更长的内部有限轨迹；无限图只作为原商中的比较对象。
有限图的类成员界与无限图的类成员界是后续独立义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteFunctionAgreement

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding SecondOrderObjectSyntax
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev w {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def condition_m {Γ Δ : SortContext ℒ} (ω e A H a F n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .imp (member_m (.bvar (.there .here)) (w ω)) <|
    .imp (PowerlessFunctionTraceBounded.formula_m (w ω) (w e) (w A) (w H) (w a)
      (.bvar (.there .here)) (.bvar .here)) <|
      .imp (.disj (member_m (w n) (.bvar (.there .here))) (.equal (w n) (.bvar (.there .here)))) <|
        .forallE .set <| .imp (value_m (.bvar (.there .here)) (up (w n)) (.bvar .here))
          (value_m (up (w F)) (up (w n)) (.bvar .here))

def condition_l (ω e A H a F n : type_l hℳ) : Prop :=
  ∀ t g, mem_l hℳ t ω → PowerlessFunctionTraceBounded.trace_l
    (𝒩 := SecondOrderQuotient.structure_l hℳ) ω e A H a t g →
      mem_l hℳ n t ∨ n = t → ∀ c,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g n c →
          value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F n c

theorem condition_formula_l {Γ Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (ω e A H a F n : Term ℒ Γ Δ .set) : (condition_m ω e A H a F n).satisfies η ↔
      condition_l (ω.eval η) (e.eval η) (A.eval η) (H.eval η) (a.eval η) (F.eval η) (n.eval η) := by
  simp only [condition_m, condition_l, Formula.satisfies, PowerlessFunctionTraceBounded.formula_l,
    value_formula_l, member_m, Arguments.eval, up, w, Term.eval_weakenBound, Term.eval]
  rfl

def template_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] := condition_m
  (.fvar (.there .here)) (.fvar (.there (.there .here)))
  (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
  (.fvar (.there (.there (.there (.there (.there .here))))))
  (.fvar (.there (.there (.there (.there (.there (.there .here))))))) (.fvar .here)

theorem template_formula_l (ω e A H a F n : type_l hℳ) : template_m.satisfies
    ((((((((Env.empty (M := SecondOrderQuotient.structure_l hℳ)).pushFree F).pushFree a).pushFree H).pushFree A).pushFree e).pushFree ω).pushFree n) ↔
      condition_l ω e A H a F n := condition_formula_l _ _ _ _ _ _ _ _

theorem agreement_l (K : source_coding_l hℳ) {A H a F : type_l hℳ}
    (hH : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) H A A)
    (hF : PowerlessFunctionIteration.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val A H a F)
    (n : SecondOrderModel.num_l ℳ) : condition_l K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val A H a F (numberCode_l K n).val := by
  obtain ⟨hMap, h₀, hStep⟩ := hF
  let e := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set, .set, .set, .set] :=
    ((((((Env.empty).pushFree F).pushFree a).pushFree H).pushFree A).pushFree e).pushFree K.omega
  have h := PowerlessBMSQuotientInduction.induction_l K template_m η ?_ ?_ n
  · exact (template_formula_l K.omega e A H a F _).mp h
  · apply (template_formula_l K.omega e A H a F _).mpr
    intro t g _ hg _ c hc
    obtain ⟨_, _, _, hG, hZero, _⟩ := hg
    have hca := PowerlessBMSQuotientRecursion.value_unique_l (hM := hℳ) hG hc hZero
    exact hca.symm ▸ h₀
  · intro i hi
    apply (template_formula_l K.omega e A H a F _).mpr
    intro t g ht hg hBound c hc
    let k := (numberCode_l K i).val
    let m := (numberCode_l K (SecondOrderModel.succ_l i)).val
    have hSucc := PowerlessBMSQuotientSuccessor.successor_l K i
    have htOrd : SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) t := by
      apply SetTheory.Structure.IsOrdinal.mem (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)
      exact ht
    have hkt : mem_l hℳ k t := by
      rcases hBound with hm | hm
      · exact htOrd.transitive m hm k ((hSucc k).mpr (Or.inr rfl))
      · exact hm ▸ (hSucc k).mpr (Or.inr rfl)
    have hTrace := hg
    obtain ⟨T, _, hT, hG, _, hGStep⟩ := hg
    obtain ⟨x, hx, _⟩ := hG.2 k ((hT k).mpr (Or.inl hkt))
    have hFx := (template_formula_l K.omega e A H a F k).mp hi t g ht hTrace (Or.inl hkt) x hx.2
    obtain ⟨y, hy, _⟩ := hMap.2 m (numberCode_l K (SecondOrderModel.succ_l i)).property
    have hHxy := hStep k m x y (numberCode_l K i).property hSucc hFx hy.2
    have hHxc := hGStep k hkt m ((hT m).mpr hBound) x hx.1 c
      (PowerlessBMSQuotientRecursion.value_mem_l (hM := hℳ) hG hc).2 hSucc hx.2 hc
    have hcy := PowerlessBMSQuotientRecursion.value_unique_l (hM := hℳ) hH hHxc hHxy
    exact hcy.symm ▸ hy.2

theorem value_l (K : source_coding_l hℳ) {A H a F n g c : type_l hℳ}
    (hH : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) H A A)
    (hF : PowerlessFunctionIteration.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val A H a F)
    (hn : mem_l hℳ n K.omega)
    (hg : PowerlessFunctionTraceBounded.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val A H a n g)
    (hc : ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g n c) :
    ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F n c := by
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have hEq : (numberCode_l K i).val = n := congrArg Subtype.val hi
  have h := agreement_l K hH hF i n g hn hg (Or.inr hEq) c
  rw [hEq] at h
  exact h hc

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteFunctionAgreement
