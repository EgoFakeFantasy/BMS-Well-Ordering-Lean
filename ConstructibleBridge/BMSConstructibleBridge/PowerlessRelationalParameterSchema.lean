import BMSConstructibleBridge.PowerlessRelationalParameterDomain

/-! # 带参数跨域编译的原对象模式

数码、最小赋值长度和全部变量槽均先存在量化，随后才量化求值域与域内
参数。外部公式是模式索引，不是一个内部统一真值谓词的参数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalParameterSchema

open Logic FirstOrder ThirdOrderSemantics
open _root_.YesMetaZFC.Automation
open PrefixQuantification (entry_m weaken_m)
open PowerlessRelationalParameterDomain (domain_l slots_m slots_formula_l)
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) := t.weakenBound SetTheory.SetSort.set

def slots_exists_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    (ω e T t₁ t₂ t₃ c N : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  PrefixQuantification.exists_m Δ <| slots_m φ (fun v => entry_m v)
    (weaken_m Δ ω) (weaken_m Δ e) (weaken_m Δ T) (weaken_m Δ t₁) (weaken_m Δ t₂) (weaken_m Δ t₃)
    (weaken_m Δ c) (weaken_m Δ N)

theorem slots_exists_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ρ : Env 𝒩 Γ Θ) (ω e T t₁ t₂ t₃ c N : Term ℒ Γ Θ .set) :
    (slots_exists_m φ ω e T t₁ t₂ t₃ c N).satisfies ρ ↔
      ∃ ξ : Env 𝒩 [] Δ, PowerlessSourceEnvironment.bounded_l ξ (N.eval ρ) ∧
        ∀ A, domain_l φ ξ (ω.eval ρ) (e.eval ρ) (T.eval ρ)
          (t₁.eval ρ) (t₂.eval ρ) (t₃.eval ρ) (c.eval ρ) (N.eval ρ) A := by
  rw [slots_exists_m, PrefixQuantification.exists_formula_l]
  simp only [slots_formula_l, PowerlessRelationalParameterSyntax.env_entry_l, PrefixQuantification.weaken_l]
  constructor
  · rintro ⟨xs, h⟩
    exact ⟨RelationalTranslation.templateEnv xs, h⟩
  · rintro ⟨ξ, h⟩
    refine ⟨ModelClosure.valuesOfAssignment ξ.freeVal, ?_⟩
    simpa only [ModelClosure.template_of_env] using h

def codes_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    (ω e T t₁ t₂ t₃ : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  let w (t : Term ℒ Γ Θ .set) := up (up t)
  .existsE .set <| .conj (member_m (.bvar .here) (up ω)) <|
    .existsE .set <| .conj (member_m (.bvar .here) (w ω)) <|
      slots_exists_m φ (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (.bvar (.there .here)) (.bvar .here)

theorem codes_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ρ : Env 𝒩 Γ Θ) (ω e T t₁ t₂ t₃ : Term ℒ Γ Θ .set) :
    (codes_m φ ω e T t₁ t₂ t₃).satisfies ρ ↔
      ∃ c, member_l 𝒩 c (ω.eval ρ) ∧ ∃ N, member_l 𝒩 N (ω.eval ρ) ∧
        ∃ ξ : Env 𝒩 [] Δ, PowerlessSourceEnvironment.bounded_l ξ N ∧
          ∀ A, domain_l φ ξ (ω.eval ρ) (e.eval ρ) (T.eval ρ)
            (t₁.eval ρ) (t₂.eval ρ) (t₃.eval ρ) c N A := by
  simp only [codes_m, Formula.satisfies, slots_exists_formula_l, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

def existence_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ) (ω : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    codes_m φ (up (up (up (up (up ω))))) (.bvar (.there (.there (.there (.there .here)))))
      (.bvar .here) (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar (.there .here))

theorem existence_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ρ : Env 𝒩 Γ Θ) (ω : Term ℒ Γ Θ .set) :
    (existence_m φ ω).satisfies ρ ↔
      ∃ e t₁ t₂ t₃ T c, member_l 𝒩 c (ω.eval ρ) ∧ ∃ N, member_l 𝒩 N (ω.eval ρ) ∧
        ∃ ξ : Env 𝒩 [] Δ, PowerlessSourceEnvironment.bounded_l ξ N ∧
          ∀ A, domain_l φ ξ (ω.eval ρ) e T t₁ t₂ t₃ c N A := by
  simp only [existence_m, Formula.satisfies, codes_formula_l, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]

def schema_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ) (ω : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) (existence_m φ ω)

def sentence_m {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    (ω : Term ℒ [] Θ .set) : Sentence ℒ := Metatheory.Formula.forall_close (schema_m φ ω)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalParameterSchema
