import BMSConstructibleBridge.PowerlessSourceNaturalAbsolute

/-!
# 原配对与函数图公式的传递子域绝对性

有序对的两个中间集合属于该对，图值的有序对见证属于该图；
因此域传递性足以取回全部见证，无须假定子域有配对公理或收集公理。
函数图的总性与唯一性也保留原定义域和值域，不更换公开公式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceGraphAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {A : carrier_l ℳ}
  {hA : ∃ a, member_l ℳ a A} (hAT : PowerlessNaturalOrder.transitive_l A)

include hAT

theorem pair_l {a b p : type_l A} :
    ThirdOrderSemantics.pair_l (ℳ := structure_l A hA) a b p ↔ ThirdOrderSemantics.pair_l a.val b.val p.val := by
  constructor
  · intro h x
    constructor
    · intro hx
      rcases (h ⟨x, hAT p.val x p.property hx⟩).mp hx with hx | hx
      · exact Or.inl (congrArg Subtype.val hx)
      · exact Or.inr (congrArg Subtype.val hx)
    · rintro (hx | hx)
      · subst x
        exact (h a).mpr (Or.inl rfl)
      · subst x
        exact (h b).mpr (Or.inr rfl)
  · intro h x
    constructor
    · intro hx
      exact ((h x.val).mp hx).imp Subtype.ext Subtype.ext
    · intro hx
      exact (h x.val).mpr (hx.imp (congrArg Subtype.val) (congrArg Subtype.val))

theorem ordered_l {a b p : type_l A} :
    ThirdOrderSemantics.ordered_l (ℳ := structure_l A hA) a b p ↔
      ThirdOrderSemantics.ordered_l a.val b.val p.val := by
  constructor
  · rintro ⟨x, y, hx, hy, hp⟩
    exact ⟨x.val, y.val, (pair_l hAT).mp hx, (pair_l hAT).mp hy, (pair_l hAT).mp hp⟩
  · rintro ⟨x, y, hx, hy, hp⟩
    have hxA := hAT p.val x p.property ((hp x).mpr (Or.inl rfl))
    have hyA := hAT p.val y p.property ((hp y).mpr (Or.inr rfl))
    exact ⟨⟨x, hxA⟩, ⟨y, hyA⟩, (pair_l hAT).mpr hx, (pair_l hAT).mpr hy, (pair_l hAT).mpr hp⟩

theorem value_l {f a b : type_l A} :
    ThirdOrderSemantics.value_l (ℳ := structure_l A hA) f a b ↔ ThirdOrderSemantics.value_l f.val a.val b.val := by
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨p.val, hp, (ordered_l hAT).mp h⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨⟨p, hAT f.val p f.property hp⟩, hp, (ordered_l hAT).mpr h⟩

theorem map_l {f B C : type_l A} :
    ThirdOrderSemantics.map_l (ℳ := structure_l A hA) f B C ↔ ThirdOrderSemantics.map_l f.val B.val C.val := by
  constructor
  · rintro ⟨h₀, h₁⟩
    constructor
    · intro p hp
      obtain ⟨x, y, hx, hy, h⟩ := h₀ ⟨p, hAT f.val p f.property hp⟩ hp
      exact ⟨x.val, y.val, hx, hy, (ordered_l hAT).mp h⟩
    · intro x hx
      let x₀ : type_l A := ⟨x, hAT B.val x B.property hx⟩
      obtain ⟨y, hy, h⟩ := h₁ x₀ hx
      refine ⟨y.val, ⟨hy.1, (value_l hAT).mp hy.2⟩, ?_⟩
      intro z hz
      exact congrArg Subtype.val (h ⟨z, hAT C.val z C.property hz.1⟩ ⟨hz.1, (value_l hAT).mpr hz.2⟩)
  · rintro ⟨h₀, h₁⟩
    constructor
    · intro p hp
      obtain ⟨x, y, hx, hy, h⟩ := h₀ p.val hp
      exact ⟨⟨x, hAT B.val x B.property hx⟩, ⟨y, hAT C.val y C.property hy⟩, hx, hy, (ordered_l hAT).mpr h⟩
    · intro x hx
      obtain ⟨y, hy, h⟩ := h₁ x.val hx
      refine ⟨⟨y, hAT C.val y C.property hy.1⟩, ⟨hy.1, (value_l hAT).mpr hy.2⟩, ?_⟩
      intro z hz
      exact Subtype.ext (h z.val ⟨hz.1, (value_l hAT).mp hz.2⟩)

theorem ordered_source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l A hA) Γ Δ)
    (a b p : Term ℒ Γ Δ .set) :
    Formula.satisfies η (SecondOrderObjectSyntax.ordered_m a b p) ↔
      ThirdOrderSemantics.ordered_l (a.eval η).val (b.eval η).val (p.eval η).val :=
  (ThirdOrderSemantics.ordered_formula_l η a b p).trans (ordered_l hAT)

theorem value_source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l A hA) Γ Δ)
    (f a b : Term ℒ Γ Δ .set) :
    Formula.satisfies η (SecondOrderObjectSyntax.value_m f a b) ↔
      ThirdOrderSemantics.value_l (f.eval η).val (a.eval η).val (b.eval η).val :=
  (ThirdOrderSemantics.value_formula_l η f a b).trans (value_l hAT)

theorem map_source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l A hA) Γ Δ)
    (f B C : Term ℒ Γ Δ .set) :
    Formula.satisfies η (SecondOrderObjectSyntax.map_m f B C) ↔
      ThirdOrderSemantics.map_l (f.eval η).val (B.eval η).val (C.eval η).val :=
  (ThirdOrderSemantics.map_formula_l η f B C).trans (map_l hAT)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceGraphAbsolute
