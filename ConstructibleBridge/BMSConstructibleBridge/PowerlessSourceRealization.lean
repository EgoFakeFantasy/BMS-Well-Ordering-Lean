import BMSConstructibleBridge.PowerlessSourceExtension

/-!
# 任意源环境的实际有限图表示

按上游自由、绑定上下文逐变量追加真实 Kuratowski 图，从空图开始。
结果同时给出内部自然数长度、图的映射性质、有界槽及全部项值的表示。
这里只实现给定的外部源环境，不把内部有限赋值空间换成外部列表。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceRealization

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessSourceEnvironment

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem free_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A : carrier_l ℳ} (hω : omega_l ω) {hA : ∃ a, ThirdOrderSemantics.member_l ℳ a A}
    {Δ : SortContext ℒ} (η : Env (structure_l A hA) [] Δ) :
    ∃ k f, ∃ ξ : Env ℳ [] Δ, ThirdOrderSemantics.member_l ℳ k ω ∧ map_l f k A ∧
      bounded_l ξ k ∧ represents_l ξ η f := by
  induction Δ with
  | nil =>
      obtain ⟨e, he⟩ := PowerlessBasic.empty_l hℳ
      refine ⟨e, e, Env.empty, PowerlessNatural.zero_mem_l hℳ hω he,
        PowerlessFiniteAssignments.empty_l he A, ?_, ?_⟩
      · intro t
        match t with
        | .bvar v => nomatch v
        | .fvar v => nomatch v
        | .app q _ => nomatch q
      · intro t
        match t with
        | .bvar v => nomatch v
        | .fvar v => nomatch v
        | .app q _ => nomatch q
  | cons s Δ h =>
      cases s
      let η₀ : Env (structure_l A hA) [] Δ :=
        ⟨η.boundVal, fun v => η.freeVal (.there v)⟩
      obtain ⟨k, f, ξ, hk, hf, hξ, hη⟩ := h η₀
      let a : type_l A := η.freeVal .here
      obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
      obtain ⟨g, hg⟩ := PowerlessAppendGraph.exists_l hℳ f k a.val
      have h₀ : η₀.pushFree a = η := by
        apply Env.ext
        · intro _ v
          nomatch v
        · intro s v
          cases v <;> rfl
      refine ⟨l, g, ξ.pushFree k, PowerlessNatural.successor_mem_l hℳ hω hk hl,
        PowerlessAppendGraph.map_l hℳ hf a.property hl hg,
        PowerlessSourceExtension.bounded_free_l hξ hl, ?_⟩
      exact h₀ ▸ PowerlessSourceExtension.free_l hℳ hη a hg

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A : carrier_l ℳ} (hω : omega_l ω) {hA : ∃ a, ThirdOrderSemantics.member_l ℳ a A}
    {Γ Δ : SortContext ℒ} (η : Env (structure_l A hA) Γ Δ) :
    ∃ k f, ∃ ξ : Env ℳ Γ Δ, ThirdOrderSemantics.member_l ℳ k ω ∧ map_l f k A ∧
      bounded_l ξ k ∧ represents_l ξ η f := by
  induction Γ with
  | nil => exact free_l hℳ hω η
  | cons s Γ h =>
      cases s
      let η₀ : Env (structure_l A hA) Γ Δ :=
        ⟨(fun v => η.boundVal (.there v)), η.freeVal⟩
      obtain ⟨k, f, ξ, hk, hf, hξ, hη⟩ := h η₀
      let a : type_l A := η.boundVal .here
      obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
      obtain ⟨g, hg⟩ := PowerlessAppendGraph.exists_l hℳ f k a.val
      have h₀ : η₀.pushBound a = η := by
        apply Env.ext
        · intro s v
          cases v <;> rfl
        · intro _ _
          rfl
      refine ⟨l, g, ξ.pushBound k, PowerlessNatural.successor_mem_l hℳ hω hk hl,
        PowerlessAppendGraph.map_l hℳ hf a.property hl hg, push_l hξ hl, ?_⟩
      exact h₀ ▸ PowerlessSourceExtension.bound_l hℳ hη a hg

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceRealization
