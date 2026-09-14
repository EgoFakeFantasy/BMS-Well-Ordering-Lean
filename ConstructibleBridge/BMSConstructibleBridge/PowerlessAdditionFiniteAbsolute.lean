import BMSConstructibleBridge.PowerlessAdditionFiniteSyntax
import BMSConstructibleBridge.PowerlessSourceGraphAbsolute

/-!
# 有限加法见证在传递成员域中的正确解释

有限轨迹正文只需传递性和实际 ω。存在轨迹的反向传输另行消费
明确的有限自然数图闭包；不把内部加法的无限迭代图放入假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionFiniteAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {A : carrier_l ℳ} {hA : ∃ a, member_l ℳ a A} (hAT : PowerlessNaturalOrder.transitive_l A)

include hℳ hAT

theorem trace_l {ω e a n g : type_l A} (hω : omega_l ω.val) (hn : member_l ℳ n.val ω.val) :
    PowerlessAdditionFinite.trace_l (ℳ := structure_l A hA) ω e a n g ↔
      PowerlessAdditionFinite.trace_l ω.val e.val a.val n.val g.val := by
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
    exact (PowerlessSourceNaturalAbsolute.successor_l hAT).mp
      (h₁ ⟨k, hkA⟩ ⟨l, hlA⟩ ⟨x, hxA⟩ ⟨y, hyA⟩ hk
        ((PowerlessSourceNaturalAbsolute.successor_l hAT).mpr hl)
        ((PowerlessSourceGraphAbsolute.value_l hAT).mpr hx) ((PowerlessSourceGraphAbsolute.value_l hAT).mpr hy))
  · rintro ⟨m, hm, hg, h₀, h₁⟩
    have hmA := hAT ω.val m ω.property (PowerlessNatural.successor_mem_l hℳ hω hn hm)
    refine ⟨⟨m, hmA⟩, (PowerlessSourceNaturalAbsolute.successor_l hAT).mpr hm,
      (PowerlessSourceGraphAbsolute.map_l hAT).mpr hg, (PowerlessSourceGraphAbsolute.value_l hAT).mpr h₀, ?_⟩
    intro k l x y hk hl hx hy
    exact (PowerlessSourceNaturalAbsolute.successor_l hAT).mpr
      (h₁ k.val l.val x.val y.val hk ((PowerlessSourceNaturalAbsolute.successor_l hAT).mp hl)
        ((PowerlessSourceGraphAbsolute.value_l hAT).mp hx) ((PowerlessSourceGraphAbsolute.value_l hAT).mp hy))

theorem finite_l {ω e a b c : type_l A} (hω : omega_l ω.val) (hb : member_l ℳ b.val ω.val)
    (hF : ∀ n, member_l ℳ n ω.val → ∀ g, map_l g n ω.val → member_l ℳ g A) :
    PowerlessAdditionFinite.addition_l (ℳ := structure_l A hA) ω e a b c ↔
      PowerlessAdditionFinite.addition_l ω.val e.val a.val b.val c.val := by
  constructor
  · rintro ⟨g, hg, hc⟩
    exact ⟨g.val, (trace_l hℳ hAT hω hb).mp hg, (PowerlessSourceGraphAbsolute.value_l hAT).mp hc⟩
  · rintro ⟨g, hg, hc⟩
    have hg₀ := hg
    obtain ⟨m, hm, hG, _⟩ := hg₀
    have hgA := hF m (PowerlessNatural.successor_mem_l hℳ hω hb hm) g hG
    exact ⟨⟨g, hgA⟩, (trace_l hℳ hAT hω hb).mpr hg, (PowerlessSourceGraphAbsolute.value_l hAT).mpr hc⟩

theorem addition_l {ω e a b c : type_l A} (hω : omega_l ω.val) (he : PowerlessNatural.zero_l e.val)
    (ha : member_l ℳ a.val ω.val) (hb : member_l ℳ b.val ω.val)
    (hF : ∀ n, member_l ℳ n ω.val → ∀ g, map_l g n ω.val → member_l ℳ g A) :
    PowerlessAdditionFinite.addition_l (ℳ := structure_l A hA) ω e a b c ↔
      PowerlessAddition.addition_l ω.val e.val a.val b.val c.val :=
  (finite_l hℳ hAT hω hb hF).trans (PowerlessAdditionFinite.equiv_l hℳ hω he ha hb)

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l A hA) Γ Δ)
    (ω e a b c : Term ℒ Γ Δ .set) (hω : omega_l (ω.eval η).val) (he : PowerlessNatural.zero_l (e.eval η).val)
    (ha : member_l ℳ (a.eval η).val (ω.eval η).val) (hb : member_l ℳ (b.eval η).val (ω.eval η).val)
    (hF : ∀ n, member_l ℳ n (ω.eval η).val → ∀ g, map_l g n (ω.eval η).val → member_l ℳ g A) :
    Formula.satisfies η (PowerlessAdditionFiniteSyntax.addition_m ω e a b c) ↔
      PowerlessAddition.addition_l (ω.eval η).val (e.eval η).val (a.eval η).val (b.eval η).val (c.eval η).val :=
  (PowerlessAdditionFiniteSyntax.addition_formula_l η ω e a b c).trans (addition_l hℳ hAT hω he ha hb hF)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionFiniteAbsolute
