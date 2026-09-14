import BMSConstructibleBridge.PowerlessEvaluationPresentation

/-!
# 有限参数末尾追加后的求值子集

参数赋值 f 的实际定义域为 m，待定义元素 x 追加到槽 m。
按求值图 F 的数码 c 分离 A 的子集，不预设完整幂集或源编译正确性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationSlice

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def point_l (ω A F c f x : carrier_l ℳ) : Prop :=
  ∃ m, member_l ℳ m ω ∧ map_l f m A ∧ ∃ g,
    PowerlessAppendGraph.append_l f m x g ∧ PowerlessEvaluationClause.query_l F c g

def point_m {Γ Δ : SortContext ℒ} (ω A F c f x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
  let v (t : Term ℒ Γ Δ .set) := (w t).weakenBound SetTheory.SetSort.set
  .existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (w ω))
    (.conj (SecondOrderObjectSyntax.map_m (w f) (.bvar .here) (w A))
      (.existsE .set (.conj (PowerlessAppendGraph.append_m (v f) (.bvar (.there .here)) (v x) (.bvar .here))
        (PowerlessEvaluationClause.query_m (v F) (v c) (.bvar .here))))))

theorem point_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω A F c f x : Term ℒ Γ Δ .set) :
    (point_m ω A F c f x).satisfies η ↔ point_l (ω.eval η) (A.eval η) (F.eval η) (c.eval η) (f.eval η) (x.eval η) := by
  simp only [point_m, point_l, Formula.satisfies, map_formula_l, PowerlessAppendGraph.append_formula_l,
    PowerlessEvaluationClause.query_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def slice_l (ω A F c f B : carrier_l ℳ) : Prop :=
  ∀ x, member_l ℳ x B ↔ member_l ℳ x A ∧ point_l ω A F c f x

def slice_m {Γ Δ : SortContext ℒ} (ω A F c f B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
  .forallE .set (.iff (SecondOrderObjectSyntax.member_m (.bvar .here) (w B))
    (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (w A))
      (point_m (w ω) (w A) (w F) (w c) (w f) (.bvar .here))))

theorem slice_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω A F c f B : Term ℒ Γ Δ .set) :
    (slice_m ω A F c f B).satisfies η ↔ slice_l (ω.eval η) (A.eval η) (F.eval η) (c.eval η) (f.eval η) (B.eval η) := by
  simp only [slice_m, slice_l, Formula.satisfies, point_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (ω A F c f : carrier_l ℳ) :
    ∃ B, slice_l ω A F c f B := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 5 :=
    { bound := Fin.cases ω (Fin.cases A (Fin.cases F (Fin.cases c (fun _ => f)))), free := fun _ => A }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
    point_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar .here)
  have h : ∀ x, φ.satisfies ((PowerlessComprehension.env_l η).pushFree x) ↔ point_l ω A F c f x := by
    intro x
    simp only [φ, point_formula_l]
    rfl
  obtain ⟨B, hB⟩ := PowerlessComprehension.separation_l hℳ φ η A
  exact ⟨B, fun x => (hB x).trans (and_congr Iff.rfl (h x))⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A F c f B C : carrier_l ℳ} (hB : slice_l ω A F c f B) (hC : slice_l ω A F c f C) : B = C :=
  (PowerlessTheory.ext_l hℳ).eq_of_same_members B C (fun x => (hB x).trans (hC x).symm)

theorem subset_l {ω A F c f B : carrier_l ℳ} (hB : slice_l ω A F c f B) : ThirdOrderSemantics.subset_l B A :=
  fun x hx => ((hB x).mp hx).1

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationSlice
