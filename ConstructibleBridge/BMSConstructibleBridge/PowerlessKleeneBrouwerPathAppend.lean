import BMSConstructibleBridge.PowerlessKleeneBrouwerPath
import BMSConstructibleBridge.SecondOrderNaturalCases

/-! # 真正下降路径的实际追加

纯隶属 ℒ，原 Z₂。给定旧末节点 a 与其实际 A 前驱 b，
同一追加图继续满足每对内部相邻坐标上的下降条件。
相邻新坐标的前驱由原后继单射识别，不用外部有限性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPathAppend

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessKleeneBrouwerPath (path_l path_m path_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

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

theorem preserves_l {ω I A z r p n k a b s q : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω) (hn : mem_l hℳ n ω)
    (hPath : path_l (𝒩 := 𝒱) ω I A z r p) (hp : map_l (ℳ := 𝒱) p n I)
    (hk : mem_l hℳ k n) (hLast : PowerlessNatural.successor_l (ℳ := 𝒱) k n)
    (hpa : value_l (ℳ := 𝒱) p k a) (hEdge : value_l (ℳ := 𝒱) A b a)
    (hs : mem_l hℳ s ω) (hSucc : PowerlessNatural.successor_l (ℳ := 𝒱) n s)
    (hq : map_l (ℳ := 𝒱) q s I)
    (hRead : ∀ i c, value_l (ℳ := 𝒱) q i c ↔ value_l (ℳ := 𝒱) p i c ∨ i = n ∧ c = b) :
    path_l (𝒩 := 𝒱) ω I A z r q := by
  obtain ⟨m, _hm, hP, hRoot, hEdges⟩ := hPath
  have hSame : m = n := PowerlessKleeneBrouwerDecisive.domain_unique_l hP hp
  subst m
  have hN : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) n :=
    SetTheory.Structure.IsOrdinal.mem (SecondOrderOmegaOrdinal.ordinal_l hℳ hω) hn
  have hOld i (hi : mem_l hℳ i n) c :
      value_l (ℳ := 𝒱) q i c ↔ value_l (ℳ := 𝒱) p i c :=
    (hRead i c).trans ⟨fun h => h.elim id
      (fun h => (not_self_l n (h.1 ▸ hi)).elim), Or.inl⟩
  refine ⟨s, hs, hq, (hRead z r).mpr (Or.inl hRoot), ?_⟩
  intro i _hi j hj hIJ x hx y hy hqx hqy
  rcases (hSucc j).mp hj with hjn | hEq
  · have hin := hN.transitive j hjn i ((hIJ i).mpr (Or.inr rfl))
    exact hEdges i hin j hjn hIJ x hx y hy ((hOld i hin x).mp hqx) ((hOld j hjn y).mp hqy)
  · subst j
    have hIK : i = k := SecondOrderNaturalCases.successor_injective_l hℳ hIJ hLast
    subst i
    have hXa : x = a :=
      SecondOrderFunctionProperties.value_unique_l hℳ hp ((hOld k hk x).mp hqx) hpa
    have hYb : y = b := by
      rcases (hRead n y).mp hqy with hpy | ⟨_, hYb⟩
      · exact (not_self_l n (SecondOrderFunctionProperties.value_mem_l hℳ hp hpy).1).elim
      · exact hYb
    subst x
    subst y
    exact hEdge

theorem exists_l {ω I A z r p n k a b : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hPath : path_l (𝒩 := 𝒱) ω I A z r p) (hn : mem_l hℳ n ω)
    (hp : map_l (ℳ := 𝒱) p n I) (hk : mem_l hℳ k n)
    (hLast : PowerlessNatural.successor_l (ℳ := 𝒱) k n)
    (hpa : value_l (ℳ := 𝒱) p k a) (hb : mem_l hℳ b I)
    (hEdge : value_l (ℳ := 𝒱) A b a) :
    ∃ s q, mem_l hℳ s ω ∧ PowerlessNatural.successor_l (ℳ := 𝒱) n s ∧
      map_l (ℳ := 𝒱) q s I ∧ path_l (𝒩 := 𝒱) ω I A z r q ∧
      ∀ i c, value_l (ℳ := 𝒱) q i c ↔ value_l (ℳ := 𝒱) p i c ∨ i = n ∧ c = b := by
  obtain ⟨s, q, hs, hSucc, hq, hRead, _hExt⟩ := PowerlessKleeneBrouwerAppend.exists_l hω hn hp hb
  exact ⟨s, q, hs, hSucc, hq, preserves_l hω hn hPath hp hk hLast hpa hEdge hs hSucc hq hRead, hRead⟩

def result_m {Γ Δ : SortContext ℒ} (ω I A z r p n b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <|
    let w (t : Term ℒ Γ Δ .set) := up (up t)
    let s : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let q : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar .here
    .conj (SecondOrderObjectSyntax.member_m s (w ω)) <|
      .conj (PowerlessSuccessorBounded.formula_m (w n) s) <|
        .conj (PowerlessMapBounded.formula_m q s (w I)) <|
          .conj (path_m (w ω) (w I) (w A) (w z) (w r) q)
            (SecondOrderFunctionAppendDerives.reading_m (w p) (w n) (w b) q)

def schema_m {Δ : SortContext ℒ} (ω I A z r p n k a b : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (path_m ω I A z r p) <|
    .imp (SecondOrderObjectSyntax.member_m n ω) <| .imp (PowerlessMapBounded.formula_m p n I) <|
      .imp (SecondOrderObjectSyntax.member_m k n) <| .imp (PowerlessSuccessorBounded.formula_m k n) <|
        .imp (PowerlessValueBounded.formula_m p k a) <| .imp (SecondOrderObjectSyntax.member_m b I) <|
          .imp (PowerlessValueBounded.formula_m A b a) (result_m ω I A z r p n b)

def sentence_m {Δ : SortContext ℒ} (ω I A z r p n k a b : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω I A z r p n k a b)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I A z r p n k a b : Term ℒ [] Δ .set) : (sentence_m ω I A z r p n k a b).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, result_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l, path_formula_l,
    SecondOrderObjectSyntax.member_m, PowerlessSuccessorBounded.formula_l,
    PowerlessMapBounded.formula_l, PowerlessValueBounded.formula_l,
    SecondOrderFunctionAppendDerives.reading_m, ThirdOrderSemantics.value_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  exact fun hω hPath hn hp hk hLast hpa hb hEdge =>
    exists_l (hℳ := hℳ) hω hPath hn hp hk hLast hpa hb hEdge

theorem derives_m {Δ : SortContext ℒ} (ω I A z r p n k a b : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m ω I A z r p n k a b)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω I A z r p n k a b)

#print axioms preserves_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPathAppend
