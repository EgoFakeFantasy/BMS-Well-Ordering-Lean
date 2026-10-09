import BMSConstructibleBridge.PowerlessRelationalSourceCompilation
import BMSConstructibleBridge.PowerlessRelativeClassFunctionExtension

/-! # 任意有限参数环境的实际赋值

先选择互异的有界自然数槽，再对任意非空域中的参数环境构造表示它的集合
函数。初始常值图与逐槽更新均在类内；不将可能没有见证的 represents 当作
交付前提。归纳仅针对外部有限上下文，不要求内部 ω 标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalParameterAssignment

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def distinct_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ} (ξ : Env 𝒩 [] Δ) : Prop :=
  ∀ v w : Variable Δ .set, ξ.freeVal v = ξ.freeVal w → v = w

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem slots_l {ω e : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (he : PowerlessNatural.zero_l (ℳ := structure_l hℳ B hBase) e) (Δ : SortContext ℒ) :
    ∃ k : type_l hℳ B, ∃ ξ : Env (structure_l hℳ B hBase) [] Δ,
      mem_l hℳ k.val ω.val ∧ PowerlessSourceEnvironment.bounded_l ξ k ∧ distinct_l ξ := by
  induction Δ with
  | nil =>
    refine ⟨e, Env.empty, PowerlessRelativeClassNaturalProperties.zero_mem_l hω he, ?_, ?_⟩
    · intro t
      match t with
      | .bvar v => nomatch v
      | .fvar v => nomatch v
      | .app q _ => nomatch q
    · intro v
      nomatch v
  | cons s Δ ih =>
    cases s
    obtain ⟨k, ξ, hk, hξ, hDistinct⟩ := ih
    obtain ⟨l, hlω, hl⟩ := PowerlessRelativeClassNaturalProperties.successor_exists_l hω hk
    refine ⟨l, ξ.pushFree k, hlω, ?_, ?_⟩
    · intro t
      match t with
      | .bvar v => nomatch v
      | .fvar .here => exact (hl k).mpr (Or.inr rfl)
      | .fvar (.there v) => exact (hl _).mpr (Or.inl (hξ (.fvar v)))
      | .app q _ => nomatch q
    · intro v w h
      cases v with
      | here =>
        cases w with
        | here => rfl
        | there w => exact ((PowerlessRelativeClassSourceEnvironment.fresh_l hξ (.fvar w)) h.symm).elim
      | there v =>
        cases w with
        | here => exact ((PowerlessRelativeClassSourceEnvironment.fresh_l hξ (.fvar v)) h).elim
        | there w => exact congrArg Variable.there (hDistinct v w h)

theorem exists_l {Δ : SortContext ℒ} {m A : type_l hℳ B}
    (hA : ∃ a, member_l (structure_l hℳ B hBase) a A)
    (ξ : Env (structure_l hℳ B hBase) [] Δ)
    (η : Env (PowerlessMemberStructure.structure_l (ℳ := structure_l hℳ B hBase) A hA) [] Δ)
    (hξ : PowerlessSourceEnvironment.bounded_l ξ m) (hDistinct : distinct_l ξ) :
    ∃ f : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) f m A ∧
      PowerlessSourceEnvironment.represents_l ξ η f := by
  induction Δ with
  | nil =>
    obtain ⟨a, ha⟩ := hA
    obtain ⟨f, hf, _⟩ := PowerlessRelativeClassFunctionExtension.constant_l m A a ha
    refine ⟨f, hf, ?_⟩
    intro t
    match t with
    | .bvar v => nomatch v
    | .fvar v => nomatch v
    | .app q _ => nomatch q
  | cons s Δ ih =>
    cases s
    let ξ' : Env (structure_l hℳ B hBase) [] Δ := ⟨ξ.boundVal, fun v => ξ.freeVal (.there v)⟩
    let η' : Env (PowerlessMemberStructure.structure_l (ℳ := structure_l hℳ B hBase) A hA) [] Δ :=
      ⟨η.boundVal, fun v => η.freeVal (.there v)⟩
    have hTail : PowerlessSourceEnvironment.bounded_l ξ' m := by
      intro t
      match t with
      | .bvar v => nomatch v
      | .fvar v => exact hξ (.fvar (.there v))
      | .app q _ => nomatch q
    have hTailDistinct : distinct_l ξ' := by
      intro v w h
      have hEq := hDistinct (.there v) (.there w) h
      cases hEq
      rfl
    obtain ⟨f, hf, hRep⟩ := ih ξ' η' hTail hTailDistinct
    obtain ⟨g, hg, hUpdate⟩ := PowerlessRelativeClassAssignmentUpdate.exists_l hf
      (hξ (.fvar .here)) (η.freeVal .here).property
    refine ⟨g, hg, ?_⟩
    intro t
    match t with
    | .bvar v => nomatch v
    | .app q _ => nomatch q
    | .fvar .here => exact PowerlessAssignmentUpdate.at_l hUpdate
    | .fvar (.there v) =>
      have hNe : ξ.freeVal (.there v) ≠ ξ.freeVal .here := by
        intro h
        have hEq := hDistinct (.there v) .here h
        cases hEq
      exact (PowerlessAssignmentUpdate.away_l hUpdate hNe).mpr (hRep (.fvar v))

#print axioms slots_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalParameterAssignment
