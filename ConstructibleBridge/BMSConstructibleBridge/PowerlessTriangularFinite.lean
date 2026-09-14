import BMSConstructibleBridge.PowerlessTriangular
import BMSConstructibleBridge.PowerlessAdditionFinite

/-!
# 三角数的内部有限计算见证

用长度 n+1 的自然数图及有限加法描述三角数递推。限制实际 T 给出
见证，原纯公式的内部 ω 归纳核验每个见证的值，而非只核验标准长度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTriangularFinite

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def trace_l (ω e n g : carrier_l ℳ) : Prop :=
  ∃ m, PowerlessNatural.successor_l n m ∧ map_l g m ω ∧ value_l g e e ∧
    ∀ k l x y, member_l ℳ k n → PowerlessNatural.successor_l k l → value_l g k x → value_l g l y →
      PowerlessAdditionFinite.addition_l ω e x l y

def value_l (ω e n t : carrier_l ℳ) : Prop := ∃ g, trace_l ω e n g ∧ ThirdOrderSemantics.value_l g n t

theorem restriction_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T n : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hT : PowerlessTriangular.triangular_l ω e T) (hn : member_l ℳ n ω) :
    ∃ g, trace_l ω e n g ∧ ∀ t, ThirdOrderSemantics.value_l g n t ↔ ThirdOrderSemantics.value_l T n t := by
  obtain ⟨m, hm⟩ := PowerlessNatural.successor_exists_l hℳ n
  have hM := PowerlessNaturalOrder.subset_l hℳ hω m (PowerlessNatural.successor_mem_l hℳ hω hn hm)
  obtain ⟨g, hg, hV⟩ := PowerlessRestriction.exists_l hℳ hT.1 hM
  refine ⟨g, ⟨m, hm, hg, (hV e e).mpr ⟨?_, hT.2.1⟩, ?_⟩, ?_⟩
  · exact (hm e).mpr (PowerlessNaturalCompare.zero_le_l hℳ hω he n hn)
  · intro k l x y hk hl hx hy
    have hkω := PowerlessNaturalOrder.subset_l hℳ hω n hn k hk
    have hlω := PowerlessNatural.successor_mem_l hℳ hω hkω hl
    exact (PowerlessAdditionFinite.equiv_l hℳ hω he (PowerlessFunction.value_mem_l hℳ hg hx).2 hlω).mpr
      (hT.2.2 k l x y hkω hl ((hV k x).mp hx).2 ((hV l y).mp hy).2)
  · intro t
    exact (hV n t).trans ⟨And.right, fun h => ⟨(hm n).mpr (Or.inr rfl), h⟩⟩

theorem agree_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T n g : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hT : PowerlessTriangular.triangular_l ω e T) (hn : member_l ℳ n ω) (hg : trace_l ω e n g) :
    ∀ k x y, ThirdOrderSemantics.value_l g k x → ThirdOrderSemantics.value_l T k y → x = y := by
  obtain ⟨m, hm, hg, h₀, h₁⟩ := hg
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases g (fun _ => T), free := fun _ => ω }
  have h : ∀ k, PowerlessTraceUnique.agree_m.satisfies ((PowerlessComprehension.env_l η).pushFree k) ↔
      ∀ x y, ThirdOrderSemantics.value_l g k x → ThirdOrderSemantics.value_l T k y → x = y :=
    fun k => PowerlessTraceUnique.agree_formula_l _
  have h₂ := PowerlessNatural.induction_l hℳ PowerlessTraceUnique.agree_m η hω
    (fun z hz => (h z).mpr (by
      have h₃ := PowerlessNatural.zero_unique_l hℳ hz he
      subst z
      intro x y hx hy
      exact (PowerlessFunction.value_unique_l hℳ hg hx h₀).trans
        (PowerlessFunction.value_unique_l hℳ hT.1 hy hT.2.1).symm))
    (fun k l hk hl h₃ => (h l).mpr (by
      intro x y hx hy
      have hkn := PowerlessTraceUnique.below_l hℳ hω hn hm hl (PowerlessFunction.value_mem_l hℳ hg hx).1
      obtain ⟨a, ha, _⟩ := hg.2 k ((hm k).mpr (Or.inl hkn))
      obtain ⟨b, hb, _⟩ := hT.1.2 k hk
      have h₄ := (h k).mp h₃ a b ha.2 hb.2
      subst b
      have h₅ := (PowerlessAdditionFinite.equiv_l hℳ hω he ha.1
        (PowerlessNatural.successor_mem_l hℳ hω hk hl)).mp (h₁ k l a x hkn hl ha.2 hx)
      exact PowerlessAddition.unique_l hℳ hω he h₅ (hT.2.2 k l a y hk hl hb.2 hy)))
  intro k x y hx hy
  have hk := PowerlessNaturalOrder.subset_l hℳ hω m (PowerlessNatural.successor_mem_l hℳ hω hn hm)
    k (PowerlessFunction.value_mem_l hℳ hg hx).1
  exact (h k).mp (h₂ k hk) x y hx hy

theorem equiv_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T n t : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hT : PowerlessTriangular.triangular_l ω e T) (hn : member_l ℳ n ω) :
    value_l ω e n t ↔ ThirdOrderSemantics.value_l T n t := by
  constructor
  · rintro ⟨g, hg, ht⟩
    obtain ⟨v, hv, _⟩ := hT.1.2 n hn
    have h := agree_l hℳ hω he hT hn hg n t v ht hv.2
    exact h.symm ▸ hv.2
  · intro ht
    obtain ⟨g, hg, hV⟩ := restriction_l hℳ hω he hT hn
    exact ⟨g, hg, (hV t).mpr ht⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTriangularFinite
