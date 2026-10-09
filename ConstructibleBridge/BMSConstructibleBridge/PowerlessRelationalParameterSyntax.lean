import YesMetaZFC.Automation.PrefixQuantification
import BMSConstructibleBridge.PowerlessRelationalSentenceSyntax
import BMSConstructibleBridge.PowerlessSourceEnvironment

/-! # 有限参数槽及表示赋值的原公式

槽项与参数项分开，有限合取覆盖每个原自由变量。公开逐项语义和原
represents 对应，供后续先存在槽、再量化实际参数的对象模式组装。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalParameterSyntax

open Logic FirstOrder ThirdOrderSemantics
open _root_.YesMetaZFC.Automation
open SecondOrderObjectSyntax (member_m map_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

def env_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (ρ : Env 𝒩 Γ Θ) (slots : Variable Δ .set → Term ℒ Γ Θ .set) : Env 𝒩 [] Δ where
  boundVal v := nomatch v
  freeVal {s} v := match s with | .set => (slots v).eval ρ

theorem env_weakenBound_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (ρ : Env 𝒩 Γ Θ) (slots : Variable Δ .set → Term ℒ Γ Θ .set) (x : carrier_l 𝒩) :
    env_l (ρ.pushBound x) (fun v => (slots v).weakenBound SetTheory.SetSort.set) = env_l ρ slots := by
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    cases s
    exact Term.eval_weakenBound ρ x (slots v)

theorem env_entry_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (ρ : Env 𝒩 Γ Θ) (xs : Values 𝒩.Carrier Δ) :
    env_l (PrefixQuantification.env_l ρ xs) (fun v => PrefixQuantification.entry_m v) =
      RelationalTranslation.templateEnv xs := by
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    cases s
    exact PrefixQuantification.entry_l ρ xs v

def bounded_m {Γ Δ Θ : SortContext ℒ} (slots : Variable Δ .set → Term ℒ Γ Θ .set)
    (N : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  PrefixQuantification.conjunction_m Δ (fun {s} v => match s with | .set => member_m (slots v) N)

theorem bounded_values_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (ρ : Env 𝒩 Γ Θ) (slots : Variable Δ .set → Term ℒ Γ Θ .set) (N : Term ℒ Γ Θ .set) :
    (bounded_m slots N).satisfies ρ ↔ ∀ v, member_l 𝒩 ((slots v).eval ρ) (N.eval ρ) := by
  rw [bounded_m, PrefixQuantification.conjunction_formula_l]
  exact ⟨fun h v => h v, fun h s v => by cases s; exact h v⟩

theorem bounded_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (ρ : Env 𝒩 Γ Θ) (slots : Variable Δ .set → Term ℒ Γ Θ .set) (N : Term ℒ Γ Θ .set) :
    (bounded_m slots N).satisfies ρ ↔ PowerlessSourceEnvironment.bounded_l (env_l ρ slots) (N.eval ρ) := by
  rw [bounded_m, PrefixQuantification.conjunction_formula_l]
  constructor
  · intro h t
    match t with
    | .bvar v => nomatch v
    | .app q _ => nomatch q
    | .fvar v => exact h v
  · intro h s v
    cases s
    exact h (.fvar v)

def represents_m {Γ Δ Θ : SortContext ℒ}
    (slots params : Variable Δ .set → Term ℒ Γ Θ .set) (f : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  PrefixQuantification.conjunction_m Δ (fun {s} v => match s with | .set => value_m f (slots v) (params v))

theorem represents_values_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (ρ : Env 𝒩 Γ Θ) (slots params : Variable Δ .set → Term ℒ Γ Θ .set) (f : Term ℒ Γ Θ .set) :
    (represents_m slots params f).satisfies ρ ↔
      ∀ v, value_l (f.eval ρ) ((slots v).eval ρ) ((params v).eval ρ) := by
  rw [represents_m, PrefixQuantification.conjunction_formula_l]
  exact ⟨fun h v => (value_formula_l ρ _ _ _).mp (h v),
    fun h s v => by cases s; exact (value_formula_l ρ _ _ _).mpr (h v)⟩

theorem represents_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    {A : carrier_l 𝒩} {hA : ∃ a, member_l 𝒩 a A} (ρ : Env 𝒩 Γ Θ)
    (slots params : Variable Δ .set → Term ℒ Γ Θ .set) (f : Term ℒ Γ Θ .set)
    (η : Env (PowerlessMemberStructure.structure_l A hA) [] Δ)
    (hParams : ∀ v, (params v).eval ρ = (η.freeVal v).val) :
    (represents_m slots params f).satisfies ρ ↔
      PowerlessSourceEnvironment.represents_l (env_l ρ slots) η (f.eval ρ) := by
  rw [represents_values_l]
  constructor
  · intro h t
    match t with
    | .bvar v => nomatch v
    | .app q _ => nomatch q
    | .fvar v =>
      change value_l (f.eval ρ) ((slots v).eval ρ) (η.freeVal v).val
      rw [← hParams v]
      exact h v
  · intro h v
    rw [hParams v]
    exact h (.fvar v)

private abbrev up {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) := t.weakenBound SetTheory.SetSort.set

def assignment_m {Γ Δ Θ : SortContext ℒ}
    (slots params : Variable Δ .set → Term ℒ Γ Θ .set) (m A : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  .existsE .set <| .conj (map_m (.bvar .here) (up m) (up A))
    (represents_m (fun v => up (slots v)) (fun v => up (params v)) (.bvar .here))

theorem assignment_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ Θ : SortContext ℒ}
    (ρ : Env 𝒩 Γ Θ) (slots params : Variable Δ .set → Term ℒ Γ Θ .set) (m A : Term ℒ Γ Θ .set) :
    (assignment_m slots params m A).satisfies ρ ↔
      ∃ f, map_l f (m.eval ρ) (A.eval ρ) ∧
        ∀ v, value_l f ((slots v).eval ρ) ((params v).eval ρ) := by
  simp only [assignment_m, Formula.satisfies, map_formula_l, represents_values_l, up, Term.eval_weakenBound, Term.eval]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalParameterSyntax
