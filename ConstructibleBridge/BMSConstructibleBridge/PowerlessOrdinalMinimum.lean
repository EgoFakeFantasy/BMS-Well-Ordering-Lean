import BMSConstructibleBridge.PowerlessOrdinalCollection

/-!
# 原公式定义的最小序数

在一个已有序数见证的后继中分离，再用内部正则性取全局最小见证。
选择结果由序数比较保证唯一；不加入对象选择，也不用外部良基性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalMinimum

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def binding_m {Γ : SortContext ℒ} :
    Substitution ℒ [] (.set :: Γ) [.set] (.set :: Γ) :=
  .map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
    (fun {s} (v : Variable (.set :: Γ) s) => match v with
    | .here => .bvar .here
    | .there v => .fvar (.there v))

theorem binding_formula_l {Γ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Γ)) (η : Env ℳ [] Γ) (α β : carrier_l ℳ) :
    (φ.substitute binding_m).satisfies ((η.pushFree α).pushBound β) ↔
      φ.satisfies (η.pushFree β) := by
  rw [Formula.satisfies_substitute]
  apply Iff.of_eq
  congr 1
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    cases v <;> rfl

def minimum_m {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Γ)) :
    Formula ℒ [] (.set :: Γ) :=
  .conj (PowerlessOrdinal.ordinal_m (.fvar .here)) (.conj φ
    (.forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar .here))
      (.neg (φ.substitute binding_m)))))

def minimum_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Γ))
    (η : Env ℳ [] Γ) (α : carrier_l ℳ) : Prop :=
  PowerlessOrdinal.ordinal_l α ∧ φ.satisfies (η.pushFree α) ∧
    ∀ β, member_l ℳ β α → ¬φ.satisfies (η.pushFree β)

theorem minimum_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Γ)) (η : Env ℳ [] Γ) (α : carrier_l ℳ) :
    (minimum_m φ).satisfies (η.pushFree α) ↔ minimum_l φ η α := by
  simp only [minimum_m, minimum_l, Formula.satisfies, PowerlessOrdinal.ordinal_formula_l hℳ,
    binding_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∃ α, PowerlessOrdinal.ordinal_l α ∧ φ.satisfies ((PowerlessComprehension.env_l η).pushFree α)) :
    ∃ α, minimum_l φ (PowerlessComprehension.env_l η) α := by
  obtain ⟨α, hα, hφ⟩ := h
  obtain ⟨β, hβ⟩ := PowerlessNatural.successor_exists_l hℳ α
  have hβ₀ := PowerlessOrdinalOrder.successor_l hℳ hα hβ
  obtain ⟨C, hC⟩ := PowerlessComprehension.separation_l hℳ φ η β
  obtain ⟨γ, hγ, h₀⟩ := PowerlessBasic.foundation_l hℳ
    ⟨α, (hC α).mpr ⟨(hβ α).mpr (Or.inr rfl), hφ⟩⟩
  obtain ⟨hγβ, hγφ⟩ := (hC γ).mp hγ
  refine ⟨γ, PowerlessOrdinal.mem_l hβ₀ hγβ, hγφ, ?_⟩
  intro δ hδ hδφ
  exact h₀ δ hδ ((hC δ).mpr ⟨PowerlessOrdinal.transitive_l hβ₀ γ δ hγβ hδ, hδφ⟩)

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Γ)} {η : Env ℳ [] Γ} {α β : carrier_l ℳ}
    (hα : minimum_l φ η α) (hβ : minimum_l φ η β) : α = β := by
  rcases PowerlessOrdinalOrder.trichotomy_l hℳ hα.1 hβ.1 with h | h | h
  · exact (hβ.2.2 α h hα.2.1).elim
  · exact h
  · exact (hα.2.2 β h hβ.2.1).elim

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalMinimum

