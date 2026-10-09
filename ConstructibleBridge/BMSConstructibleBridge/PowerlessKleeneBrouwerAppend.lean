import BMSConstructibleBridge.PowerlessKleeneBrouwerMinimumStep
import BMSConstructibleBridge.SecondOrderFunctionAppendDerives

/-! # 固定前缀的实际内部追加

纯隶属 ℒ，原 Z₂。原 ω 的后继闭包给出同一内部新长度；
显式添加 Kuratowski 有序对取得真实新图，陪域保持原 I。
后继、图、全 raw 坐标读数和旧前缀扩展均由对象推导产生。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerAppend

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassSequenceSplit (prefix_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem not_self_l (x : Raw) : ¬mem_l hℳ x x := by
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  exact SecondOrderFoundation.irrefl_l hℳ X

theorem exists_l {ω I p n b : Raw} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hn : mem_l hℳ n ω) (hp : map_l (ℳ := 𝒱) p n I) (hb : mem_l hℳ b I) :
    ∃ s q, mem_l hℳ s ω ∧ PowerlessNatural.successor_l (ℳ := 𝒱) n s ∧
      map_l (ℳ := 𝒱) q s I ∧
      (∀ i a, value_l (ℳ := 𝒱) q i a ↔ value_l (ℳ := 𝒱) p i a ∨ i = n ∧ a = b) ∧
      PowerlessKleeneBrouwerPrefix.extension_l (𝒩 := 𝒱) ω I p n q := by
  obtain ⟨s, hs, hSucc⟩ := hω.1.2 n hn
  obtain ⟨t, ht⟩ := SecondOrderPairObjects.ordered_exists_l hℳ n b
  obtain ⟨q, hq⟩ := SecondOrderFunctionAppendDerives.adjoin_l hℳ p t
  have hMap : map_l (ℳ := 𝒱) q s I :=
    SecondOrderFunctionAppend.map_l hℳ hp (not_self_l n) hb hSucc ht hq
  have hRead (i a : Raw) : value_l (ℳ := 𝒱) q i a ↔
      value_l (ℳ := 𝒱) p i a ∨ i = n ∧ a = b :=
    SecondOrderFunctionAppend.value_l hℳ ht hq i a
  have hPrefix : prefix_l (ℳ₀ := 𝒱) n I q p := by
    intro i hi a _ha
    constructor
    · intro hpa
      exact (hRead i a).mpr (Or.inl hpa)
    · intro hqa
      rcases (hRead i a).mp hqa with hpa | ⟨hEq, _⟩
      · exact hpa
      · exact (not_self_l n (hEq ▸ hi)).elim
  exact ⟨s, q, hs, hSucc, hMap, hRead,
    s, hs, hMap, fun i hi => (hSucc i).mpr (Or.inl hi), hPrefix⟩

def result_m {Γ Δ : SortContext ℒ} (ω I p n b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <|
    let w (t : Term ℒ Γ Δ .set) := up (up t)
    let s : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let q : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar .here
    .conj (SecondOrderObjectSyntax.member_m s (w ω)) <|
      .conj (PowerlessSuccessorBounded.formula_m (w n) s) <|
        .conj (PowerlessMapBounded.formula_m q s (w I)) <|
          .conj (SecondOrderFunctionAppendDerives.reading_m (w p) (w n) (w b) q)
            (PowerlessKleeneBrouwerPrefix.extension_m (w ω) (w I) (w p) (w n) q)

def schema_m {Δ : SortContext ℒ} (ω I p n b : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (SecondOrderObjectSyntax.member_m n ω) <|
    .imp (PowerlessMapBounded.formula_m p n I) <| .imp (SecondOrderObjectSyntax.member_m b I)
      (result_m ω I p n b)

def sentence_m {Δ : SortContext ℒ} (ω I p n b : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω I p n b)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I p n b : Term ℒ [] Δ .set) : (sentence_m ω I p n b).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, result_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    SecondOrderObjectSyntax.member_m, PowerlessSuccessorBounded.formula_l,
    PowerlessMapBounded.formula_l, SecondOrderFunctionAppendDerives.reading_m,
    ThirdOrderSemantics.value_formula_l, PowerlessKleeneBrouwerPrefix.extension_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  exact fun hω hn hp hb => exists_l (hℳ := hℳ) hω hn hp hb

theorem derives_m {Δ : SortContext ℒ} (ω I p n b : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω I p n b)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω I p n b)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerAppend
