import BMSConstructibleBridge.PowerlessSatisfactionExistenceSyntax
import BMSConstructibleBridge.PowerlessRelationalParameterContext

/-! # 同一公共 Sat 图上的带参数对象模式

共同静态规格先于公式数码、最小长度和全部参数槽；求值域非空时存在一张
R，同时满足 Sat 规格及全部参数环境上的真实赋值与公式读数。外部公式仅
是模式索引；这里不重新选择编码，也不把 R 换回中间求值图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionParameterSchema

open Logic FirstOrder ThirdOrderSemantics
open _root_.YesMetaZFC.Automation
open PrefixQuantification (entry_m weaken_m)
open PowerlessRelationalParameterSyntax (env_l bounded_m env_weakenBound_l)
open SecondOrderObjectSyntax (member_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) := t.weakenBound SetTheory.SetSort.set

def domain_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ξ : Env 𝒩 [] Δ) (ω e t₁ t₂ t₃ T F c L A : carrier_l 𝒩) : Prop :=
  ∀ hA : ∃ a, member_l 𝒩 a A, ∃ R,
    PowerlessSatisfactionSpecification.spec_l ω A e t₁ t₂ t₃ T F R ∧
    ∀ η : Env (PowerlessMemberStructure.structure_l A hA) [] Δ,
      PowerlessRelationalParameterReading.spec_l φ ξ ω A R c L η

def domain_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    (slots : Variable Δ .set → Term ℒ Γ Θ .set)
    (ω e t₁ t₂ t₃ T F c L A : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  .imp (PowerlessRelationalSentenceSyntax.nonempty_m A) <| .existsE .set <|
    .conj (PowerlessSatisfactionSpecification.spec_m (up ω) (up A) (up e)
      (up t₁) (up t₂) (up t₃) (up T) (up F) (.bvar .here))
      (PowerlessRelationalParameterContext.parameters_m φ (fun v => up (slots v))
        (up ω) (up A) (.bvar .here) (up c) (up L))

theorem domain_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ρ : Env 𝒩 Γ Θ) (slots : Variable Δ .set → Term ℒ Γ Θ .set)
    (ω e t₁ t₂ t₃ T F c L A : Term ℒ Γ Θ .set) :
    (domain_m φ slots ω e t₁ t₂ t₃ T F c L A).satisfies ρ ↔
      domain_l φ (env_l ρ slots) (ω.eval ρ) (e.eval ρ) (t₁.eval ρ) (t₂.eval ρ)
        (t₃.eval ρ) (T.eval ρ) (F.eval ρ) (c.eval ρ) (L.eval ρ) (A.eval ρ) := by
  simp only [domain_m, domain_l, Formula.satisfies, PowerlessRelationalSentenceSyntax.nonempty_formula_l,
    PowerlessSatisfactionSpecification.spec_formula_l, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here]
  apply forall_congr'
  intro hA
  apply exists_congr
  intro R
  have h := PowerlessRelationalParameterContext.parameters_formula_l φ (ρ.pushBound R)
    (fun v => up (slots v)) (up ω) (up A) (.bvar .here) (up c) (up L)
    hA (by simp only [up, Term.eval_weakenBound])
  simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, env_weakenBound_l]
    using and_congr Iff.rfl h

def slots_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    (slots : Variable Δ .set → Term ℒ Γ Θ .set)
    (ω e t₁ t₂ t₃ T F c L : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  .conj (bounded_m slots L) <| .forallE .set <|
    domain_m φ (fun v => up (slots v)) (up ω) (up e) (up t₁) (up t₂) (up t₃)
      (up T) (up F) (up c) (up L) (.bvar .here)

theorem slots_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ρ : Env 𝒩 Γ Θ) (slots : Variable Δ .set → Term ℒ Γ Θ .set)
    (ω e t₁ t₂ t₃ T F c L : Term ℒ Γ Θ .set) :
    (slots_m φ slots ω e t₁ t₂ t₃ T F c L).satisfies ρ ↔
      PowerlessSourceEnvironment.bounded_l (env_l ρ slots) (L.eval ρ) ∧
      ∀ A, domain_l φ (env_l ρ slots) (ω.eval ρ) (e.eval ρ) (t₁.eval ρ) (t₂.eval ρ)
        (t₃.eval ρ) (T.eval ρ) (F.eval ρ) (c.eval ρ) (L.eval ρ) A := by
  simp only [slots_m, Formula.satisfies, PowerlessRelationalParameterSyntax.bounded_formula_l,
    domain_formula_l, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, env_weakenBound_l]

def slots_exists_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    (ω e t₁ t₂ t₃ T F c L : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  PrefixQuantification.exists_m Δ <| slots_m φ (fun v => entry_m v)
    (weaken_m Δ ω) (weaken_m Δ e) (weaken_m Δ t₁) (weaken_m Δ t₂) (weaken_m Δ t₃)
    (weaken_m Δ T) (weaken_m Δ F) (weaken_m Δ c) (weaken_m Δ L)

theorem slots_exists_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ρ : Env 𝒩 Γ Θ) (ω e t₁ t₂ t₃ T F c L : Term ℒ Γ Θ .set) :
    (slots_exists_m φ ω e t₁ t₂ t₃ T F c L).satisfies ρ ↔
      ∃ ξ : Env 𝒩 [] Δ, PowerlessSourceEnvironment.bounded_l ξ (L.eval ρ) ∧
        ∀ A, domain_l φ ξ (ω.eval ρ) (e.eval ρ) (t₁.eval ρ) (t₂.eval ρ)
          (t₃.eval ρ) (T.eval ρ) (F.eval ρ) (c.eval ρ) (L.eval ρ) A := by
  rw [slots_exists_m, PrefixQuantification.exists_formula_l]
  simp only [slots_formula_l, PowerlessRelationalParameterSyntax.env_entry_l, PrefixQuantification.weaken_l]
  constructor
  · rintro ⟨xs, h⟩
    exact ⟨RelationalTranslation.templateEnv xs, h⟩
  · rintro ⟨ξ, h⟩
    refine ⟨ModelClosure.valuesOfAssignment ξ.freeVal, ?_⟩
    simpa only [ModelClosure.template_of_env] using h

/-- 共同静态规格与编译输出的合法性保持在槽量词之外。 -/
def codes_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    (ω e t₁ t₂ t₃ T N F : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  let w (t : Term ℒ Γ Θ .set) := up (up t)
  .conj (PowerlessSatisfactionExistenceSyntax.static_m ω e t₁ t₂ t₃ T N F) <|
    .existsE .set <| .existsE .set <|
      .conj (member_m (.bvar (.there .here)) (w ω)) <| .conj (member_m (.bvar .here) (w ω)) <|
        .conj (value_m (w F) (.bvar (.there .here)) (.bvar .here))
          (slots_exists_m φ (w ω) (w e) (w t₁) (w t₂) (w t₃) (w T) (w F)
            (.bvar (.there .here)) (.bvar .here))

theorem codes_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ρ : Env 𝒩 Γ Θ) (ω e t₁ t₂ t₃ T N F : Term ℒ Γ Θ .set) :
    (codes_m φ ω e t₁ t₂ t₃ T N F).satisfies ρ ↔
      PowerlessSatisfactionExistenceSyntax.static_l (ω.eval ρ) (e.eval ρ) (t₁.eval ρ) (t₂.eval ρ)
        (t₃.eval ρ) (T.eval ρ) (N.eval ρ) (F.eval ρ) ∧
      ∃ c L, member_l 𝒩 c (ω.eval ρ) ∧ member_l 𝒩 L (ω.eval ρ) ∧ value_l (F.eval ρ) c L ∧
        ∃ ξ : Env 𝒩 [] Δ, PowerlessSourceEnvironment.bounded_l ξ L ∧
          ∀ A, domain_l φ ξ (ω.eval ρ) (e.eval ρ) (t₁.eval ρ) (t₂.eval ρ)
            (t₃.eval ρ) (T.eval ρ) (F.eval ρ) c L A := by
  simp only [codes_m, Formula.satisfies, PowerlessSatisfactionExistenceSyntax.static_formula_l,
    slots_exists_formula_l, value_formula_l, member_m, member_l, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]

def statement_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ω : carrier_l 𝒩) : Prop :=
  ∃ e t₁ t₂ t₃ T N F, PowerlessSatisfactionExistenceSyntax.static_l ω e t₁ t₂ t₃ T N F ∧
    ∃ c L, member_l 𝒩 c ω ∧ member_l 𝒩 L ω ∧ value_l F c L ∧
      ∃ ξ : Env 𝒩 [] Δ, PowerlessSourceEnvironment.bounded_l ξ L ∧
        ∀ A, domain_l φ ξ ω e t₁ t₂ t₃ T F c L A

def existence_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ) (ω : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    .existsE .set <| .existsE .set <|
      codes_m φ (up (up (up (up (up (up (up ω)))))))
        (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
        (.bvar (.there (.there (.there (.there (.there .here))))))
        (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here))))
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem existence_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (ρ : Env 𝒩 Γ Θ) (ω : Term ℒ Γ Θ .set) :
    (existence_m φ ω).satisfies ρ ↔ statement_l φ (ω.eval ρ) := by
  simp only [existence_m, statement_l, Formula.satisfies, codes_formula_l, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]

def schema_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ) (ω : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) (existence_m φ ω)

def sentence_m {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ) (ω : Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ ω)

#print axioms domain_formula_l
#print axioms slots_exists_formula_l
#print axioms existence_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionParameterSchema
