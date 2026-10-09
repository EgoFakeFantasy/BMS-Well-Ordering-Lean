import BMSConstructibleBridge.PowerlessRelationalParameterContext

/-! # 参数编译模式的跨域部分

同一个域只存在量化一次求值图，随后覆盖域内全部参数环境；槽环境在域
量词外固定。对象句同时保留槽界和每个足够长赋值域上的真实表示函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalParameterDomain

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelationalParameterSyntax (env_l bounded_m env_weakenBound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) := t.weakenBound SetTheory.SetSort.set

def domain_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ξ : Env 𝒩 [] Δ) (ω e T t₁ t₂ t₃ c N A : carrier_l 𝒩) : Prop :=
  ∀ hA : ∃ a, member_l 𝒩 a A, ∃ S G,
    PowerlessRelativeClassEvaluationSystem.spec_l ω A e t₁ t₂ t₃ T S G ∧
    ∀ η : Env (PowerlessMemberStructure.structure_l A hA) [] Δ,
      PowerlessRelationalParameterReading.spec_l φ ξ ω A G c N η

def domain_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    (slots : Variable Δ .set → Term ℒ Γ Θ .set)
    (ω e T t₁ t₂ t₃ c N A : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  let w (t : Term ℒ Γ Θ .set) := up (up t)
  .imp (PowerlessRelationalSentenceSyntax.nonempty_m A) <| .existsE .set <| .existsE .set <|
    .conj (PowerlessRelativeClassEvaluationSystem.spec_m (w ω) (w A) (w e) (w t₁) (w t₂) (w t₃)
      (w T) (.bvar (.there .here)) (.bvar .here))
      (PowerlessRelationalParameterContext.parameters_m φ (fun v => w (slots v))
        (w ω) (w A) (.bvar .here) (w c) (w N))

theorem domain_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ρ : Env 𝒩 Γ Θ) (slots : Variable Δ .set → Term ℒ Γ Θ .set)
    (ω e T t₁ t₂ t₃ c N A : Term ℒ Γ Θ .set) :
    (domain_m φ slots ω e T t₁ t₂ t₃ c N A).satisfies ρ ↔
      domain_l φ (env_l ρ slots) (ω.eval ρ) (e.eval ρ) (T.eval ρ)
        (t₁.eval ρ) (t₂.eval ρ) (t₃.eval ρ) (c.eval ρ) (N.eval ρ) (A.eval ρ) := by
  simp only [domain_m, domain_l, Formula.satisfies, PowerlessRelationalSentenceSyntax.nonempty_formula_l,
    PowerlessRelativeClassEvaluationSystem.spec_formula_l, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  apply forall_congr'
  intro hA
  apply exists_congr
  intro S
  apply exists_congr
  intro G
  have h := PowerlessRelationalParameterContext.parameters_formula_l φ ((ρ.pushBound S).pushBound G)
    (fun v => up (up (slots v))) (up (up ω)) (up (up A)) (.bvar .here) (up (up c)) (up (up N))
    hA (by simp only [up, Term.eval_weakenBound])
  simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, env_weakenBound_l]
    using and_congr Iff.rfl h

def slots_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    (slots : Variable Δ .set → Term ℒ Γ Θ .set)
    (ω e T t₁ t₂ t₃ c N : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  .conj (bounded_m slots N) <| .forallE .set <|
    domain_m φ (fun v => up (slots v)) (up ω) (up e) (up T) (up t₁) (up t₂) (up t₃) (up c) (up N) (.bvar .here)

theorem slots_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ρ : Env 𝒩 Γ Θ) (slots : Variable Δ .set → Term ℒ Γ Θ .set)
    (ω e T t₁ t₂ t₃ c N : Term ℒ Γ Θ .set) :
    (slots_m φ slots ω e T t₁ t₂ t₃ c N).satisfies ρ ↔
      PowerlessSourceEnvironment.bounded_l (env_l ρ slots) (N.eval ρ) ∧
      ∀ A, domain_l φ (env_l ρ slots) (ω.eval ρ) (e.eval ρ) (T.eval ρ)
        (t₁.eval ρ) (t₂.eval ρ) (t₃.eval ρ) (c.eval ρ) (N.eval ρ) A := by
  simp only [slots_m, Formula.satisfies, PowerlessRelationalParameterSyntax.bounded_formula_l,
    domain_formula_l, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, env_weakenBound_l]

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalParameterDomain
