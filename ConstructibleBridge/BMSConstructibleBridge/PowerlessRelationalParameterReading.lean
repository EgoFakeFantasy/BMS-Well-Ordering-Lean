import BMSConstructibleBridge.PowerlessRelationalParameterSyntax

/-! # 带参数求值读数的对象公式与精确语义

每个足够长的内部赋值域都实际存在表示函数，且所有表示函数均满足原
公式读值等价。参数留在成员域，槽与编码留在外层；两者不能混同。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalParameterReading

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderObjectSyntax (member_m map_m value_m)
open PowerlessRelationalParameterSyntax (represents_m assignment_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) := t.weakenBound SetTheory.SetSort.set

def correctness_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    (slots params : Variable Δ .set → Term ℒ Γ Θ .set) (m A G c : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  .forallE .set <| .imp (map_m (.bvar .here) (up m) (up A)) <|
    .imp (represents_m (fun v => up (slots v)) (fun v => up (params v)) (.bvar .here)) <|
      .iff (value_m (up G) (up c) (.bvar .here))
        (PowerlessRelativeParameters.instance_m φ (up A) (fun v => up (params v)))

theorem correctness_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ρ : Env 𝒩 Γ Θ)
    (slots params : Variable Δ .set → Term ℒ Γ Θ .set) (m A G c : Term ℒ Γ Θ .set)
    {D : carrier_l 𝒩} {hD : ∃ a, member_l 𝒩 a D}
    (η : Env (PowerlessMemberStructure.structure_l D hD) [] Δ)
    (hA : A.eval ρ = D) (hParams : ∀ v, (params v).eval ρ = (η.freeVal v).val) :
    (correctness_m φ slots params m A G c).satisfies ρ ↔
      ∀ f, map_l f (m.eval ρ) (A.eval ρ) →
        (∀ v, value_l f ((slots v).eval ρ) ((params v).eval ρ)) →
          (value_l (G.eval ρ) (c.eval ρ) f ↔ φ.satisfies η) := by
  simp only [correctness_m, Formula.satisfies, map_formula_l, value_formula_l,
    PowerlessRelationalParameterSyntax.represents_values_l, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here]
  apply forall_congr'
  intro f
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  refine iff_congr Iff.rfl (PowerlessRelativeParameters.instance_l φ (ρ.pushBound f)
    (up A) (fun v => up (params v)) η ?_ ?_)
  · simpa only [up, Term.eval_weakenBound] using hA
  · intro v
    simpa only [up, Term.eval_weakenBound] using hParams v

def reading_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    (slots params : Variable Δ .set → Term ℒ Γ Θ .set) (ω A G c N : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up ω)) <|
    .imp (ThirdOrderTheory.subset_m (up N) (.bvar .here)) <|
      .conj (assignment_m (fun v => up (slots v)) (fun v => up (params v)) (.bvar .here) (up A))
        (correctness_m φ (fun v => up (slots v)) (fun v => up (params v))
          (.bvar .here) (up A) (up G) (up c))

theorem reading_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ρ : Env 𝒩 Γ Θ)
    (slots params : Variable Δ .set → Term ℒ Γ Θ .set) (ω A G c N : Term ℒ Γ Θ .set)
    {D : carrier_l 𝒩} {hD : ∃ a, member_l 𝒩 a D}
    (η : Env (PowerlessMemberStructure.structure_l D hD) [] Δ)
    (hA : A.eval ρ = D) (hParams : ∀ v, (params v).eval ρ = (η.freeVal v).val) :
    (reading_m φ slots params ω A G c N).satisfies ρ ↔
      ∀ m, member_l 𝒩 m (ω.eval ρ) → subset_l (N.eval ρ) m →
        (∃ f, map_l f m (A.eval ρ) ∧ ∀ v, value_l f ((slots v).eval ρ) ((params v).eval ρ)) ∧
        (∀ f, map_l f m (A.eval ρ) → (∀ v, value_l f ((slots v).eval ρ) ((params v).eval ρ)) →
          (value_l (G.eval ρ) (c.eval ρ) f ↔ φ.satisfies η)) := by
  simp only [reading_m, Formula.satisfies, subset_formula_l, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]
  apply forall_congr'
  intro m
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  have hA' : (up A).eval (ρ.pushBound m) = D := by simpa only [up, Term.eval_weakenBound] using hA
  have hParams' (v : Variable Δ .set) : (up (params v)).eval (ρ.pushBound m) = (η.freeVal v).val := by
    simpa only [up, Term.eval_weakenBound] using hParams v
  have hAssign := PowerlessRelationalParameterSyntax.assignment_formula_l (ρ.pushBound m)
    (fun v => up (slots v)) (fun v => up (params v)) (.bvar .here) (up A)
  have hCorrect := correctness_formula_l φ (ρ.pushBound m)
    (fun v => up (slots v)) (fun v => up (params v)) (.bvar .here) (up A) (up G) (up c) η hA' hParams'
  simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using and_congr hAssign hCorrect

/-- 参数环境上的读值规格同时包含真实表示赋值的存在性。 -/
def spec_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ξ : Env 𝒩 [] Δ) (ω A G c N : carrier_l 𝒩)
    {hA : ∃ a, member_l 𝒩 a A} (η : Env (PowerlessMemberStructure.structure_l A hA) [] Δ) : Prop :=
  ∀ m, member_l 𝒩 m ω → subset_l N m →
    (∃ f, map_l f m A ∧ PowerlessSourceEnvironment.represents_l ξ η f) ∧
    (∀ f, map_l f m A → PowerlessSourceEnvironment.represents_l ξ η f →
      (value_l G c f ↔ φ.satisfies η))

theorem environment_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ρ : Env 𝒩 Γ Θ)
    (slots params : Variable Δ .set → Term ℒ Γ Θ .set) (ω A G c N : Term ℒ Γ Θ .set)
    {D : carrier_l 𝒩} {hD : ∃ a, member_l 𝒩 a D}
    (η : Env (PowerlessMemberStructure.structure_l D hD) [] Δ) (hA : A.eval ρ = D)
    (hParams : ∀ v, (params v).eval ρ = (η.freeVal v).val) :
    (reading_m φ slots params ω A G c N).satisfies ρ ↔
      spec_l φ (PowerlessRelationalParameterSyntax.env_l ρ slots)
        (ω.eval ρ) D (G.eval ρ) (c.eval ρ) (N.eval ρ) η := by
  rw [reading_formula_l φ ρ slots params ω A G c N η hA hParams]
  simp only [hA]
  unfold spec_l
  apply forall_congr'
  intro m
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  have hRep (f : carrier_l 𝒩) :
      (∀ v, value_l f ((slots v).eval ρ) ((params v).eval ρ)) ↔
        PowerlessSourceEnvironment.represents_l (PowerlessRelationalParameterSyntax.env_l ρ slots) η f := by
    constructor
    · intro h t
      match t with
      | .bvar v => nomatch v
      | .app q _ => nomatch q
      | .fvar v =>
        change value_l f ((slots v).eval ρ) (η.freeVal v).val
        rw [← hParams v]
        exact h v
    · intro h v
      rw [hParams v]
      exact h (.fvar v)
  exact and_congr (exists_congr (fun f => and_congr Iff.rfl (hRep f)))
    (forall_congr' (fun f => imp_congr Iff.rfl (imp_congr (hRep f) Iff.rfl)))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalParameterReading
