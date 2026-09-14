import BMSConstructibleBridge.PowerlessTriangularFiniteSyntax
import BMSConstructibleBridge.PowerlessAdditionFiniteAbsolute

/-!
# 有限三角数公式的层内正确解释

实际 T 只在外部作为比较对象，不要求 T 属于成员域。有限图闭包
同时给三角数轨迹和每一步加法见证，保留原内部自然数范围。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTriangularFiniteAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {A : carrier_l ℳ} {hA : ∃ a, member_l ℳ a A} (hAT : PowerlessNaturalOrder.transitive_l A)

include hℳ hAT

theorem trace_l {ω e n g : type_l A} (hω : omega_l ω.val) (hn : member_l ℳ n.val ω.val)
    (hF : ∀ m, member_l ℳ m ω.val → ∀ f, map_l f m ω.val → member_l ℳ f A) :
    PowerlessTriangularFinite.trace_l (ℳ := structure_l A hA) ω e n g ↔
      PowerlessTriangularFinite.trace_l ω.val e.val n.val g.val := by
  constructor
  · rintro ⟨m, hm, hg, h₀, h₁⟩
    have hG := (PowerlessSourceGraphAbsolute.map_l hAT).mp hg
    refine ⟨m.val, (PowerlessSourceNaturalAbsolute.successor_l hAT).mp hm,
      hG, (PowerlessSourceGraphAbsolute.value_l hAT).mp h₀, ?_⟩
    intro k l x y hk hl hx hy
    have hkA := hAT n.val k n.property hk
    have hlA := hAT m.val l m.property (PowerlessFunction.value_mem_l hℳ hG hy).1
    have hxA := hAT ω.val x ω.property (PowerlessFunction.value_mem_l hℳ hG hx).2
    have hyA := hAT ω.val y ω.property (PowerlessFunction.value_mem_l hℳ hG hy).2
    have hkω := PowerlessNaturalOrder.subset_l hℳ hω n.val hn k hk
    have hlω := PowerlessNatural.successor_mem_l hℳ hω hkω hl
    exact (PowerlessAdditionFiniteAbsolute.finite_l hℳ hAT hω hlω hF).mp
      (h₁ ⟨k, hkA⟩ ⟨l, hlA⟩ ⟨x, hxA⟩ ⟨y, hyA⟩ hk
        ((PowerlessSourceNaturalAbsolute.successor_l hAT).mpr hl)
        ((PowerlessSourceGraphAbsolute.value_l hAT).mpr hx) ((PowerlessSourceGraphAbsolute.value_l hAT).mpr hy))
  · rintro ⟨m, hm, hg, h₀, h₁⟩
    have hmA := hAT ω.val m ω.property (PowerlessNatural.successor_mem_l hℳ hω hn hm)
    refine ⟨⟨m, hmA⟩, (PowerlessSourceNaturalAbsolute.successor_l hAT).mpr hm,
      (PowerlessSourceGraphAbsolute.map_l hAT).mpr hg, (PowerlessSourceGraphAbsolute.value_l hAT).mpr h₀, ?_⟩
    intro k l x y hk hl hx hy
    have hl₀ := (PowerlessSourceNaturalAbsolute.successor_l hAT).mp hl
    have hkω := PowerlessNaturalOrder.subset_l hℳ hω n.val hn k.val hk
    exact (PowerlessAdditionFiniteAbsolute.finite_l hℳ hAT hω
      (PowerlessNatural.successor_mem_l hℳ hω hkω hl₀) hF).mpr
      (h₁ k.val l.val x.val y.val hk hl₀ ((PowerlessSourceGraphAbsolute.value_l hAT).mp hx)
        ((PowerlessSourceGraphAbsolute.value_l hAT).mp hy))

theorem finite_l {ω e n t : type_l A} (hω : omega_l ω.val) (hn : member_l ℳ n.val ω.val)
    (hF : ∀ m, member_l ℳ m ω.val → ∀ f, map_l f m ω.val → member_l ℳ f A) :
    PowerlessTriangularFinite.value_l (ℳ := structure_l A hA) ω e n t ↔
      PowerlessTriangularFinite.value_l ω.val e.val n.val t.val := by
  constructor
  · rintro ⟨g, hg, ht⟩
    exact ⟨g.val, (trace_l hℳ hAT hω hn hF).mp hg, (PowerlessSourceGraphAbsolute.value_l hAT).mp ht⟩
  · rintro ⟨g, hg, ht⟩
    have hg₀ := hg
    obtain ⟨m, hm, hG, _⟩ := hg₀
    have hgA := hF m (PowerlessNatural.successor_mem_l hℳ hω hn hm) g hG
    exact ⟨⟨g, hgA⟩, (trace_l hℳ hAT hω hn hF).mpr hg, (PowerlessSourceGraphAbsolute.value_l hAT).mpr ht⟩

theorem value_l {ω e n t : type_l A} {T : carrier_l ℳ} (hω : omega_l ω.val)
    (he : PowerlessNatural.zero_l e.val) (hT : PowerlessTriangular.triangular_l ω.val e.val T)
    (hn : member_l ℳ n.val ω.val)
    (hF : ∀ m, member_l ℳ m ω.val → ∀ f, map_l f m ω.val → member_l ℳ f A) :
    PowerlessTriangularFinite.value_l (ℳ := structure_l A hA) ω e n t ↔ ThirdOrderSemantics.value_l T n.val t.val :=
  (finite_l hℳ hAT hω hn hF).trans (PowerlessTriangularFinite.equiv_l hℳ hω he hT hn)

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l A hA) Γ Δ)
    (ω e n t : Term ℒ Γ Δ .set) {T : carrier_l ℳ} (hω : omega_l (ω.eval η).val)
    (he : PowerlessNatural.zero_l (e.eval η).val) (hT : PowerlessTriangular.triangular_l (ω.eval η).val (e.eval η).val T)
    (hn : member_l ℳ (n.eval η).val (ω.eval η).val)
    (hF : ∀ m, member_l ℳ m (ω.eval η).val → ∀ f, map_l f m (ω.eval η).val → member_l ℳ f A) :
    Formula.satisfies η (PowerlessTriangularFiniteSyntax.value_m ω e n t) ↔
      ThirdOrderSemantics.value_l T (n.eval η).val (t.eval η).val :=
  (PowerlessTriangularFiniteSyntax.value_formula_l η ω e n t).trans (value_l hℳ hAT hω he hT hn hF)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTriangularFiniteAbsolute
