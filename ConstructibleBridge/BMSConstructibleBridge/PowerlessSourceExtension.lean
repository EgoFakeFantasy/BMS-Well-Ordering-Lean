import BMSConstructibleBridge.PowerlessSourceEnvironment

/-! # 源环境压入变量与实际图追加的对应 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceExtension

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessSourceEnvironment

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}

theorem bound_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A f g k : carrier_l ℳ} {hA : ∃ a, ThirdOrderSemantics.member_l ℳ a A}
    {ξ : Env ℳ Γ Δ} {η : Env (structure_l A hA) Γ Δ}
    (hη : represents_l ξ η f) (a : type_l A) (hg : PowerlessAppendGraph.append_l f k a.val g) :
    represents_l (ξ.pushBound k) (η.pushBound a) g := by
  intro t
  match t with
  | .bvar .here => exact (PowerlessAppendGraph.value_l hℳ hg).mpr (Or.inr ⟨rfl, rfl⟩)
  | .bvar (.there v) => exact (PowerlessAppendGraph.value_l hℳ hg).mpr (Or.inl (hη (.bvar v)))
  | .fvar v => exact (PowerlessAppendGraph.value_l hℳ hg).mpr (Or.inl (hη (.fvar v)))
  | .app q _ => nomatch q

theorem free_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A f g k : carrier_l ℳ} {hA : ∃ a, ThirdOrderSemantics.member_l ℳ a A}
    {ξ : Env ℳ Γ Δ} {η : Env (structure_l A hA) Γ Δ}
    (hη : represents_l ξ η f) (a : type_l A) (hg : PowerlessAppendGraph.append_l f k a.val g) :
    represents_l (ξ.pushFree k) (η.pushFree a) g := by
  intro t
  match t with
  | .bvar v => exact (PowerlessAppendGraph.value_l hℳ hg).mpr (Or.inl (hη (.bvar v)))
  | .fvar .here => exact (PowerlessAppendGraph.value_l hℳ hg).mpr (Or.inr ⟨rfl, rfl⟩)
  | .fvar (.there v) => exact (PowerlessAppendGraph.value_l hℳ hg).mpr (Or.inl (hη (.fvar v)))
  | .app q _ => nomatch q

theorem bounded_free_l {k l : carrier_l ℳ} {ξ : Env ℳ Γ Δ}
    (hξ : bounded_l ξ k) (hl : PowerlessNatural.successor_l k l) : bounded_l (ξ.pushFree k) l := by
  intro t
  match t with
  | .bvar v => exact (hl _).mpr (Or.inl (hξ (.bvar v)))
  | .fvar .here => exact (hl k).mpr (Or.inr rfl)
  | .fvar (.there v) => exact (hl _).mpr (Or.inl (hξ (.fvar v)))
  | .app q _ => nomatch q

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceExtension
