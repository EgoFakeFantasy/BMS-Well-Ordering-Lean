import BMSConstructibleBridge.PowerlessKleeneBrouwerPathInduction
import BMSConstructibleBridge.PowerlessFiniteAssignments

/-! # 根单点路径与整棵路径树的内部最小元

纯隶属 ℒ，原 Z₂。根坐标 z 是原空对象，实际追加产生单点根路径。
每条同根路径均延伸它；原 H 输出集合归纳给出任意非空 raw 子集最小元。
尚未把该最小元条款装配为真实 Class 关系的完整环境良序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPathMinimum

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessKleeneBrouwerPath (path_l path_m path_formula_l)
open PowerlessKleeneBrouwerPrefix (extension_l)
open PowerlessKleeneBrouwerSyntax (compare_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem root_l {ω I A z r : Raw} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hZero : PowerlessNatural.zero_l (ℳ := 𝒱) z) (hz : mem_l hℳ z ω) (hr : mem_l hℳ r I) :
    ∃ n p, mem_l hℳ n ω ∧ mem_l hℳ z n ∧
      PowerlessKleeneBrouwerPathInduction.node_l ω I A z r p n z r ∧
        ∀ f, path_l (𝒩 := 𝒱) ω I A z r f → extension_l (𝒩 := 𝒱) ω I p n f := by
  have hEmpty := PowerlessFiniteAssignments.empty_l hZero I
  obtain ⟨n, p, hn, hSucc, hp, hRead, _⟩ := PowerlessKleeneBrouwerAppend.exists_l hω hz hEmpty hr
  have hzn := (hSucc z).mpr (Or.inr rfl)
  have hpr := (hRead z r).mpr (Or.inr ⟨rfl, rfl⟩)
  have hSingle (i : Raw) (hi : mem_l hℳ i n) : i = z := by
    rcases (hSucc i).mp hi with hiz | heq
    · exact (hZero i hiz).elim
    · exact heq
  have hEdges : PowerlessKleeneBrouwerPath.edges_l (𝒩 := 𝒱) n I A p := by
    intro i hi j hj hNext
    have hiEq := hSingle i hi
    have hjEq := hSingle j hj
    subst i
    subst j
    exact (hZero z ((hNext z).mpr (Or.inr rfl))).elim
  refine ⟨n, p, hn, hzn, ⟨⟨n, hn, hp, hpr, hEdges⟩, hp, hSucc, hpr⟩, ?_⟩
  intro f hPath
  obtain ⟨m, hm, hf, hfr, _⟩ := hPath
  have hzm := (SecondOrderFunctionProperties.value_mem_l hℳ hf hfr).1
  refine ⟨m, hm, hf, fun i hi => (hSingle i hi).symm ▸ hzm, ?_⟩
  intro i hi a _ha
  have hiEq := hSingle i hi
  subst i
  constructor
  · intro hpa
    exact SecondOrderFunctionProperties.value_unique_l hℳ hp hpr hpa ▸ hfr
  · intro hfa
    exact SecondOrderFunctionProperties.value_unique_l hℳ hf hfr hfa ▸ hpr

theorem minimum_l {ω I A z r T H U : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ b, mem_l hℳ b I → mem_l hℳ b ω)
    (hZero : PowerlessNatural.zero_l (ℳ := 𝒱) z) (hz : mem_l hℳ z ω) (hr : mem_l hℳ r I)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hU : ∀ f, mem_l hℳ f U → path_l (𝒩 := 𝒱) ω I A z r f)
    (hNonempty : ∃ f, mem_l hℳ f U) :
    ∃ f, mem_l hℳ f U ∧ ∀ g, mem_l hℳ g U → ¬compare_l (𝒩 := 𝒱) ω I g f := by
  obtain ⟨n, p, hn, hzn, hNode, hExtensions⟩ := root_l hω hZero hz hr
  obtain ⟨X, hX, _⟩ := hH.2.1.2 r hr
  exact PowerlessKleeneBrouwerPathInduction.all_l hω hSub hH X r hr hX.2 p n hn z hzn hNode U
    (fun f hf => ⟨hU f hf, hExtensions f (hU f hf)⟩) hNonempty

def minimum_m {Γ Δ : SortContext ℒ} (ω I A z r : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <|
    .imp (membershipLevyBound.boundedForall (.bvar .here)
      (path_m (up (up ω)) (up (up I)) (up (up A)) (up (up z)) (up (up r)) (.bvar .here))) <|
      .imp (.existsE .set (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here))))
        (PowerlessKleeneBrouwerMinimumStep.minimum_m (up ω) (up I) (.bvar .here))

theorem minimum_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω I A z r : Term ℒ Γ Δ .set) :
    (minimum_m ω I A z r).satisfies η ↔
      ∀ U, (∀ f, mem_l hℳ f U →
        path_l (𝒩 := 𝒱) (ω.eval η) (I.eval η) (A.eval η) (z.eval η) (r.eval η) f) →
        (∃ f, mem_l hℳ f U) → ∃ f, mem_l hℳ f U ∧
          ∀ g, mem_l hℳ g U → ¬compare_l (𝒩 := 𝒱) (ω.eval η) (I.eval η) g f := by
  simp only [minimum_m, Formula.satisfies, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, path_formula_l,
    SecondOrderObjectSyntax.member_m, PowerlessKleeneBrouwerMinimumStep.minimum_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (ω I A z r T H : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (ThirdOrderTheory.subset_m I ω) <|
    .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (up z)))) <|
      .imp (SecondOrderObjectSyntax.member_m z ω) <| .imp (SecondOrderObjectSyntax.member_m r I) <|
        .imp (SecondOrderCollapseSyntax.formula_m A I T H) (minimum_m ω I A z r)

def sentence_m {Δ : SortContext ℒ} (ω I A z r T H : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω I A z r T H)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I A z r T H : Term ℒ [] Δ .set) : (sentence_m ω I A z r T H).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    ThirdOrderSemantics.subset_formula_l, subset_l, SecondOrderObjectSyntax.member_m,
    SecondOrderCollapseSyntax.formula_l, minimum_formula_l, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  intro hω hSub hZero hz hr hH U hU hNonempty
  exact minimum_l (hℳ := hℳ) hω hSub hZero hz hr hH hU hNonempty

theorem derives_m {Δ : SortContext ℒ} (ω I A z r T H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω I A z r T H)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω I A z r T H)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPathMinimum
