import BMSConstructibleBridge.PowerlessSourceAmbient
import BMSConstructibleBridge.PowerlessNaturalStep

/-!
# 传递成员域中的基本自然数关系绝对性

直接核验原语义的空集、子集、后继与归纳集合，不要求子结构满足
核心公理。量词见证由其属于参数集合及域传递性取回，保留实际元素。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceNaturalAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {A : carrier_l ℳ}
  {hA : ∃ a, member_l ℳ a A} (hAT : PowerlessNaturalOrder.transitive_l A)

include hAT

theorem zero_l {a : type_l A} :
    PowerlessNatural.zero_l (ℳ := structure_l A hA) a ↔ PowerlessNatural.zero_l a.val := by
  constructor
  · intro h x hx
    exact h ⟨x, hAT a.val x a.property hx⟩ hx
  · intro h x hx
    exact h x.val hx

theorem subset_l {a b : type_l A} :
    ThirdOrderSemantics.subset_l (ℳ := structure_l A hA) a b ↔ ThirdOrderSemantics.subset_l a.val b.val := by
  constructor
  · intro h x hx
    exact h ⟨x, hAT a.val x a.property hx⟩ hx
  · intro h x hx
    exact h x.val hx

theorem successor_l {a b : type_l A} :
    PowerlessNatural.successor_l (ℳ := structure_l A hA) a b ↔ PowerlessNatural.successor_l a.val b.val := by
  constructor
  · intro h x
    constructor
    · intro hx
      rcases (h ⟨x, hAT b.val x b.property hx⟩).mp hx with h₀ | h₀
      · exact Or.inl h₀
      · exact Or.inr (congrArg Subtype.val h₀)
    · rintro (hx | hx)
      · exact (h ⟨x, hAT a.val x a.property hx⟩).mpr (Or.inl hx)
      · subst x
        exact (h a).mpr (Or.inr rfl)
  · intro h x
    constructor
    · intro hx
      rcases (h x.val).mp hx with h₀ | h₀
      · exact Or.inl h₀
      · exact Or.inr (Subtype.ext h₀)
    · rintro (hx | hx)
      · exact (h x.val).mpr (Or.inl hx)
      · exact (h x.val).mpr (Or.inr (congrArg Subtype.val hx))

theorem inductive_l {a : type_l A} :
    ThirdOrderSemantics.inductive_l (ℳ := structure_l A hA) a ↔ ThirdOrderSemantics.inductive_l a.val := by
  rw [PowerlessNatural.inductive_iff_l (ℳ := structure_l A hA) a,
    PowerlessNatural.inductive_iff_l a.val]
  constructor
  · rintro ⟨⟨z, hz, hza⟩, h⟩
    refine ⟨⟨z.val, (zero_l hAT).mp hz, hza⟩, ?_⟩
    intro x hx
    obtain ⟨y, hy, h₀⟩ := h ⟨x, hAT a.val x a.property hx⟩ hx
    exact ⟨y.val, hy, (successor_l hAT).mp h₀⟩
  · rintro ⟨⟨z, hz, hza⟩, h⟩
    refine ⟨⟨⟨z, hAT a.val z a.property hza⟩, (zero_l hAT).mpr hz, hza⟩, ?_⟩
    intro x hx
    obtain ⟨y, hy, h₀⟩ := h x.val hx
    exact ⟨⟨y, hAT a.val y a.property hy⟩, hy, (successor_l hAT).mpr h₀⟩

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l A hA) Γ Δ) (a : Term ℒ Γ Δ .set) :
    Formula.satisfies η (SecondOrderOmegaSyntax.inductive_m a) ↔ ThirdOrderSemantics.inductive_l (a.eval η).val :=
  (ThirdOrderSemantics.inductive_formula_l η a).trans (inductive_l hAT)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceNaturalAbsolute
