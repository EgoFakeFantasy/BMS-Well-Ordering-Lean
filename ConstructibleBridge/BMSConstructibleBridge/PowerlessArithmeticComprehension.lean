import BMSConstructibleBridge.PowerlessArithmeticTranslation

/-!
# 实际内部算术结构的完整理解方案

先把任意带参数的双排序正文翻译成同一纯集合模型中的公式，再在实际 ω 上分离。
所得集合确为该模型的对象；不把宿主谓词直接当作实数，也不使用幂集存在性。
本方向从完整 Powerless 模型取得算术模型，不反向解释 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessArithmeticComprehension

open Logic FirstOrder ThirdOrderSemantics PowerlessArithmeticTerms

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessArithmetic.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private def variable_m {Γ : SortContext SecondOrderSyntax.signature_m} {s : SecondOrderSyntax.sort_m} :
    Variable Γ s → Variable (context_m Γ) .set
  | .here => .here
  | .there v => .there (variable_m v)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

private def assignment_l {ω : carrier_l ℳ} : {Γ : SortContext SecondOrderSyntax.signature_m} →
    ({s : SecondOrderSyntax.sort_m} → Variable Γ s → sort_l ω s) → Assignment ℳ (context_m Γ)
  | .nil, _ => Assignment.empty
  | _ :: _, ρ => Assignment.push (M := ℳ) (sort := SetTheory.SetSort.set) (val_l (ρ .here))
      (assignment_l (fun v => ρ (.there v)))

private theorem variable_l {ω : carrier_l ℳ} : {Γ : SortContext SecondOrderSyntax.signature_m} →
    (ρ : {s : SecondOrderSyntax.sort_m} → Variable Γ s → sort_l ω s) →
    {s : SecondOrderSyntax.sort_m} → (v : Variable Γ s) → assignment_l ρ (variable_m v) = val_l (ρ v)
  | _, _, _, .here => rfl
  | _, ρ, _, .there v => variable_l (fun v => ρ (.there v)) v

private def coordinates_l : {Γ : SortContext ℒ} → Assignment ℳ Γ → Fin Γ.length → carrier_l ℳ
  | .nil, _ => Fin.elim0
  | .set :: _, ρ => Fin.cases (ρ .here) (coordinates_l (fun v => ρ (.there v)))

private theorem coordinates_variable_l : {Γ : SortContext ℒ} → (ρ : Assignment ℳ Γ) →
    (v : Variable Γ .set) → coordinates_l ρ v.position = ρ v
  | .set :: _, _, .here => rfl
  | .set :: _, ρ, .there v => coordinates_variable_l (fun v => ρ (.there v)) v

private def project_l {Γ : SortContext ℒ} (ω : carrier_l ℳ) (η : Env ℳ [] Γ) :
    SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length :=
  { bound := coordinates_l η.freeVal, free := fun _ => ω }

private theorem project_env_l {Γ : SortContext ℒ} (ω : carrier_l ℳ) (η : Env ℳ [] Γ) :
    PowerlessComprehension.env_l (project_l ω η) = η := by
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    cases s
    exact coordinates_variable_l η.freeVal v

variable {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

/-- 任意原参数和二阶量词的正文，都由同一模型中的实际 ω 子集实现。 -/
theorem extension_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {Δ : SortContext SecondOrderSyntax.signature_m} (ξ : Env 𝒩 [] Δ)
    (φ : Formula SecondOrderSyntax.signature_m [] (.num :: Δ)) :
    ∃ X : PowerlessArithmetic.set_l ω, ∀ n : PowerlessArithmetic.num_l ω,
      member_l ℳ n.val X.val ↔ φ.satisfies
        (ξ.pushFree (σ := SecondOrderSyntax.signature_m) (sort := .num) n) := by
  let η : Env ℳ [] (.set :: .set :: context_m Δ) :=
    ⟨Assignment.empty, Assignment.push ω (Assignment.push e (assignment_l ξ.freeVal))⟩
  let τ : assignment_m (.num :: Δ) [] (.set :: .set :: .set :: context_m Δ) :=
    fun v => match v with
      | .here => .fvar .here
      | .there v => .fvar (.there (.there (.there (variable_m v))))
  let ψ : Formula ℒ [] (.set :: .set :: .set :: context_m Δ) :=
    PowerlessArithmeticTranslation.formula_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (fun {s} (v : Variable ([] : SortContext SecondOrderSyntax.signature_m) s) => nomatch v) τ φ
  have h : ∀ n : PowerlessArithmetic.num_l ω,
      ψ.satisfies (η.pushFree n.val) ↔ φ.satisfies
        (ξ.pushFree (σ := SecondOrderSyntax.signature_m) (sort := .num) n) := by
    intro n
    apply PowerlessArithmeticTranslation.formula_l hℳ hω
      (ξ.pushFree (σ := SecondOrderSyntax.signature_m) (sort := .num) n) (η.pushFree n.val)
      _ _ _ _ rfl rfl
    · intro s v
      nomatch v
    · intro s v
      cases v with
      | here => rfl
      | there v => exact variable_l ξ.freeVal v
  obtain ⟨X, hX⟩ := PowerlessComprehension.separation_l hℳ ψ (project_l ω η) ω
  have hX₀ : ∀ x, member_l ℳ x X ↔ member_l ℳ x ω ∧ ψ.satisfies (η.pushFree x) := by
    intro x
    have hx := hX x
    change member_l ℳ x X ↔ member_l ℳ x ω ∧
      ψ.satisfies ((PowerlessComprehension.env_l (project_l ω η)).pushFree x) at hx
    simpa only [project_env_l] using hx
  refine ⟨⟨X, fun x hx => ((hX₀ x).mp hx).1⟩, ?_⟩
  intro n
  exact ⟨fun hx => (h n).mp ((hX₀ n.val).mp hx).2,
    fun hx => (hX₀ n.val).mpr ⟨n.property, (h n).mpr hx⟩⟩

/-- 同一个实际集合满足原理解公式，绑定代入没有引入额外集合参数。 -/
theorem comprehension_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {Δ : SortContext SecondOrderSyntax.signature_m} (ξ : Env 𝒩 [] Δ)
    (φ : Formula SecondOrderSyntax.signature_m [] (.num :: Δ)) :
    (SecondOrderArithmetic.comprehension_m φ).satisfies ξ := by
  obtain ⟨X, hX⟩ := extension_l hℳ hω ξ φ
  change ∃ X : PowerlessArithmetic.set_l ω, ∀ n : PowerlessArithmetic.num_l ω,
    member_l ℳ n.val X.val ↔ _
  refine ⟨X, fun n => (hX n).trans ?_⟩
  symm
  rw [Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    cases v <;> rfl

private theorem close_l {Δ : SortContext SecondOrderSyntax.signature_m}
    (φ : Formula SecondOrderSyntax.signature_m [] Δ) (h : ∀ ξ : Env 𝒩 [] Δ, φ.satisfies ξ) :
    (Metatheory.Formula.forall_close φ).TrueIn 𝒩 := by
  induction Δ with
  | nil => exact h Env.empty
  | cons s Δ hᵢ =>
    apply hᵢ
    intro ξ
    rw [Formula.satisfies_forallFreeTop]
    exact fun x => h (ξ.pushFree x)

/-- 基础公理与全部理解实例在同一内部算术结构中成立。 -/
theorem models_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω) :
    Theory.Models 𝒩 SecondOrderArithmetic.theory_m := by
  intro φ h
  cases h with
  | base k => exact PowerlessArithmetic.base_l hℳ hω he F k
  | comprehension φ _ => exact close_l _ (fun ξ => comprehension_l hℳ hω ξ φ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessArithmeticComprehension
