import BMSConstructibleBridge.PowerlessRelativeCutoffLeastWitnessStage
import BMSConstructibleBridge.PowerlessValueBounded

/-! # 实际前史中的有界最小见证阶段

对象语言为纯隶属 ℒ，背景为原 Z₂。真实前史 F:Ω→W 把无界的层定义
换成有界图求值；固定矩阵若为 Δ₀，整个最小阶段正文仍为 Δ₀。原任意
公式对 W 相对化后可使用这个接口。这里先核验 AST 与实际最小阶段的
逐参数对应；Class 阶段图、共同上界及 Collection 不是本模块的结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeHistoryWitnessStage

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set

private def binding_m {Γ Ε Δ : SortContext ℒ}
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    Substitution ℒ [] (.set :: Δ) (.set :: .set :: Γ) Ε :=
  .map (fun v => nomatch v) (fun {s} v => match s with
    | .set => match v with
      | .here => .bvar .here
      | .there v => up (up (τ v)))

def env_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Ε Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Ε) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Env 𝒩 [] Δ where
  boundVal v := nomatch v
  freeVal {s} v := match s with | .set => (τ v).eval η

private theorem env_pushBound_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Ε Δ : SortContext ℒ} (η : Env 𝒩 Γ Ε)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) (x : 𝒩.Carrier .set) :
    env_l (η.pushBound x) (fun v => up (τ v)) = env_l η τ := by
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s; exact Term.eval_weakenBound _ _ _

def occurs_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (F W a : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up W)) <|
    .conj (PowerlessValueBounded.formula_m (up F) (up a) (.bvar .here)) <|
      .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
        (φ.substitute (binding_m τ))

theorem occurs_delta_l {Γ Ε Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (F W a : Term ℒ Γ Ε .set)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    Formula.IsDelta0 membershipLevyBound (occurs_m φ F W a τ) := by
  refine .bounded_exists W <| .conj (PowerlessValueBounded.delta_l _ _ _) <|
    .bounded_exists (.bvar .here) ?_
  unfold binding_m
  exact Formula.IsDelta0.substituteMapped
    (boundSubstitution := fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
    (freeSubstitution := fun {s} (v : Variable (SetTheory.SetSort.set :: Δ) s) => match s with
      | .set => (show Term ℒ (.set :: .set :: Γ) Ε .set from
        match v with | .here => .bvar .here | .there v => up (up (τ v)))) hφ

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def occurs_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env 𝒱 [] Δ) (F W a : type_l hℳ) : Prop :=
  ∃ C, mem_l hℳ C W ∧ value_l (ℳ := 𝒱) F a C ∧
    ∃ y, mem_l hℳ y C ∧ φ.satisfies (η.pushFree y)

theorem occurs_formula_l {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env 𝒱 Γ Ε) (F W a : Term ℒ Γ Ε .set)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    (occurs_m φ F W a τ).satisfies η ↔
      occurs_l φ (env_l η τ) (F.eval η) (W.eval η) (a.eval η) := by
  have hBody (C y : type_l hℳ) :
      (φ.substitute (binding_m τ)).satisfies ((η.pushBound C).pushBound y) ↔
        φ.satisfies ((env_l η τ).pushFree y) := by
    rw [Formula.satisfies_substitute]
    apply Iff.of_eq
    apply congrArg (fun ρ => φ.satisfies ρ)
    apply Env.ext
    · intro s v; nomatch v
    · intro s v
      cases s
      cases v with
      | here => rfl
      | there v =>
        change (up (up (τ v))).eval ((η.pushBound C).pushBound y) = (τ v).eval η
        simp only [up, Term.eval_weakenBound]
  simp only [occurs_m, occurs_l, Formula.satisfies, PowerlessValueBounded.formula_l,
    hBody, SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def rank_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (F W a : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .conj (occurs_m φ F W a τ) <| .forallE .set <|
    .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up a))
      (.neg (occurs_m φ (up F) (up W) (.bvar .here) (fun v => up (τ v))))

theorem rank_delta_l {Γ Ε Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (F W a : Term ℒ Γ Ε .set)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    Formula.IsDelta0 membershipLevyBound (rank_m φ F W a τ) :=
  .conj (occurs_delta_l hφ F W a τ) <|
    .bounded_forall a (.neg (occurs_delta_l hφ (up F) (up W) (.bvar .here) (fun v => up (τ v))))

def rank_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env 𝒱 [] Δ) (F W a : type_l hℳ) : Prop :=
  occurs_l φ η F W a ∧ ∀ b, mem_l hℳ b a → ¬occurs_l φ η F W b

theorem rank_formula_l {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env 𝒱 Γ Ε) (F W a : Term ℒ Γ Ε .set)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    (rank_m φ F W a τ).satisfies η ↔
      rank_l φ (env_l η τ) (F.eval η) (W.eval η) (a.eval η) := by
  simp only [rank_m, rank_l, Formula.satisfies, occurs_formula_l, env_pushBound_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem occurs_iff_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒱 [] Δ)
    {B Ω F W a : type_l hℳ}
    (hΩ : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) Ω)
    (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B Ω F W) (ha : mem_l hℳ a Ω) :
    occurs_l φ η F W a ↔ PowerlessRelativeWitnessLeastStage.occurs_l φ η B a := by
  constructor
  · rintro ⟨C, _, hFC, y, hy, hφ⟩
    exact ⟨C, ⟨Ω, F, W, hΩ, ha, hF, hFC⟩, y, hy, hφ⟩
  · rintro ⟨C, hC, y, hy, hφ⟩
    obtain ⟨D, ⟨hDW, hFD⟩, _⟩ := hF.1.2 a ha
    have hCD := PowerlessRelativeHierarchyAgreement.level_unique_l hℳ hC
      ⟨Ω, F, W, hΩ, ha, hF, hFD⟩
    exact ⟨D, hDW, hFD, y, hCD ▸ hy, hφ⟩

theorem rank_iff_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒱 [] Δ)
    {B Ω F W a : type_l hℳ}
    (hΩ : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) Ω)
    (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B Ω F W) (ha : mem_l hℳ a Ω) :
    rank_l φ η F W a ↔ PowerlessRelativeWitnessLeastStage.rank_l φ η B a := by
  have hRead := occurs_iff_l φ η hΩ hF ha
  constructor
  · rintro ⟨h, hMin⟩
    exact ⟨hRead.mp h, fun b hb hOcc =>
      hMin b hb ((occurs_iff_l φ η hΩ hF (hΩ.transitive a ha b hb)).mpr hOcc)⟩
  · rintro ⟨h, hMin⟩
    exact ⟨hRead.mpr h, fun b hb hOcc =>
      hMin b hb ((occurs_iff_l φ η hΩ hF (hΩ.transitive a ha b hb)).mp hOcc)⟩

#print axioms occurs_delta_l
#print axioms rank_formula_l
#print axioms rank_iff_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeHistoryWitnessStage
