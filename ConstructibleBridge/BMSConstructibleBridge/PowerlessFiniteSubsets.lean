import BMSConstructibleBridge.PowerlessFiniteClosureMinimum

/-!
# 有限子集集合的精确纯语言规格

在任何有限子集闭合超集内按分离筛选有限子集。其规格双向覆盖模型内全部
有限子集，不是外部有限对象枚举；一般幂集的存在不在结论中。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteSubsets

open Logic FirstOrder ThirdOrderSemantics PowerlessFiniteClosureSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def spec_l (ω x p : carrier_l ℳ) : Prop :=
  ∀ a, member_l ℳ a p ↔ finite_l ω a ∧ subset_l a x

def spec_m {Γ Δ : SortContext ℒ} (ω x p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.iff
    (SecondOrderObjectSyntax.member_m (.bvar .here) (p.weakenBound SetTheory.SetSort.set))
    (.conj (finite_m (ω.weakenBound SetTheory.SetSort.set) (.bvar .here))
      (subset_m (.bvar .here) (x.weakenBound SetTheory.SetSort.set))))

theorem spec_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω x p : Term ℒ Γ Δ .set) : (spec_m ω x p).satisfies η ↔
      spec_l (ω.eval η) (x.eval η) (p.eval η) := by
  simp only [spec_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    finite_formula_l, PowerlessFiniteClosureSyntax.subset_formula_l,
    Arguments.eval, Term.eval, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderWeakSetTheory.theory_m)
    (ω x b : carrier_l ℳ) (hxb : subset_l x b) (hb : closed_l ω b) :
    ∃ p, spec_l ω x p := by
  let φ : Formula ℒ [] [.set, .set, .set] :=
    .conj (finite_m (.fvar (.there (.there .here))) (.fvar .here))
      (subset_m (.fvar .here) (.fvar (.there .here)))
  let η : Env ℳ [] [.set, .set] := ((Env.empty (M := ℳ)).pushFree ω).pushFree x
  have hφ a : φ.satisfies (η.pushFree a) ↔ finite_l ω a ∧ subset_l a x := by
    simp only [φ, Formula.satisfies, finite_formula_l,
      PowerlessFiniteClosureSyntax.subset_formula_l, Term.eval]
    rfl
  have hSep := hℳ _ (SecondOrderWeakSetTheory.axiom_m.separation φ)
  have hSep' := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp hSep η
  obtain ⟨p, hp⟩ := (PowerlessWeakSeparationSyntax.schema_formula_l φ η).mp hSep' b
  refine ⟨p, fun a => ?_⟩
  refine (hp a).trans ((and_congr Iff.rfl (hφ a)).trans ?_)
  exact ⟨fun h => h.2, fun h => ⟨hb a h.1 (fun z hz => hxb z (h.2 z hz)), h⟩⟩

def sentence_m : Sentence ℒ :=
  .forallE .set (.imp (SecondOrderOmegaSyntax.omega_m (.bvar .here))
    (.forallE .set (.existsE .set (spec_m (.bvar (.there (.there .here)))
      (.bvar (.there .here)) (.bvar .here)))))

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteSubsets
