import BMSConstructibleBridge.PowerlessKleeneBrouwerBranchMinimum

/-! # 从分支纤维最小元到整个前缀子集最小元

纯隶属 ℒ，原 Z₂。实际选择最小出现分支，再使用该纤维的最小元；
只有前缀本身时用非自返性。输入的纤维最小元义务将在原集合归纳
中由子节点假设承担，此处不把这些条件误报为路径树已良序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerMinimumStep

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessKleeneBrouwerSyntax (compare_l compare_m compare_formula_l)
open PowerlessKleeneBrouwerPrefix (extension_l)

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

theorem point_cases_l {ω I p n f : Raw} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hn : mem_l hℳ n ω) (hp : map_l (ℳ := 𝒱) p n I)
    (hExt : extension_l (𝒩 := 𝒱) ω I p n f) :
    f = p ∨ ∃ b, mem_l hℳ b I ∧ value_l (ℳ := 𝒱) f n b := by
  obtain ⟨m, hm, hf, hInclude, hPrefix⟩ := hExt
  have hOrd := SecondOrderOmegaOrdinal.ordinal_l hℳ hω
  rcases hOrd.wellOrder.linear.compare n hn m hm with hEq | hnm | hmn
  · have hSame : n = m := SecondOrderQuotient.ext_l hℳ n m hEq
    subst m
    exact Or.inl (PowerlessKleeneBrouwerComparison.prefix_ext_l hf hp hPrefix)
  · obtain ⟨b, hb, _⟩ := hf.2 n hnm
    exact Or.inr ⟨b, hb.1, hb.2⟩
  · exact (not_self_l m (hInclude m hmn)).elim

theorem step_l {ω I p n U : Raw} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ b, mem_l hℳ b I → mem_l hℳ b ω)
    (hn : mem_l hℳ n ω) (hp : map_l (ℳ := 𝒱) p n I)
    (hU : ∀ f, mem_l hℳ f U → extension_l (𝒩 := 𝒱) ω I p n f)
    (hNonempty : ∃ f, mem_l hℳ f U)
    (hFibers : ∀ b, mem_l hℳ b I → (∃ f, mem_l hℳ f U ∧ value_l (ℳ := 𝒱) f n b) →
      ∃ f, mem_l hℳ f U ∧ value_l (ℳ := 𝒱) f n b ∧
        ∀ g, mem_l hℳ g U → value_l (ℳ := 𝒱) g n b → ¬compare_l (𝒩 := 𝒱) ω I g f) :
    ∃ f, mem_l hℳ f U ∧ ∀ g, mem_l hℳ g U → ¬compare_l (𝒩 := 𝒱) ω I g f := by
  classical
  have hSequences f (hf : mem_l hℳ f U) : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω I f := by
    obtain ⟨m, hm, hMap, _⟩ := hU f hf
    exact ⟨m, hm, hMap⟩
  have hP : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω I p := ⟨n, hn, hp⟩
  by_cases hBranches : ∃ f, mem_l hℳ f U ∧ ∃ b, mem_l hℳ b I ∧ value_l (ℳ := 𝒱) f n b
  · obtain ⟨b, hb, hBranch, hLeast⟩ := PowerlessKleeneBrouwerBranchMinimum.least_l hω hSub hSequences hBranches
    obtain ⟨f, hf, hfb, hMin⟩ := hFibers b hb hBranch
    have hNe : f ≠ p := by
      intro hEq
      exact not_self_l n (SecondOrderFunctionProperties.value_mem_l hℳ hp (hEq ▸ hfb)).1
    refine ⟨f, hf, ?_⟩
    intro g hg
    rcases point_cases_l hω hn hp (hU g hg) with hEq | ⟨a, ha, hga⟩
    · subst g
      have hFP : compare_l (𝒩 := 𝒱) ω I f p :=
        (PowerlessKleeneBrouwerPrefix.length_cases_l hω hn hp (hU f hf)).resolve_left hNe
      exact PowerlessKleeneBrouwerComparison.asymmetric_l hω hSub (hSequences f hf) hP hFP
    · rcases hLeast g hg a ha hga with hEq | hba
      · subst a
        exact hMin g hg hga
      · have hFG := PowerlessKleeneBrouwerPrefix.branch_compare_l (hU f hf) (hU g hg) hfb hga hba
        exact PowerlessKleeneBrouwerComparison.asymmetric_l hω hSub
          (hSequences f hf) (hSequences g hg) hFG
  · have hOnly g (hg : mem_l hℳ g U) : g = p := by
      rcases point_cases_l hω hn hp (hU g hg) with hEq | hBranch
      · exact hEq
      · exact (hBranches ⟨g, hg, hBranch⟩).elim
    obtain ⟨f, hf⟩ := hNonempty
    refine ⟨f, hf, ?_⟩
    intro g hg hGF
    have hSelf : compare_l (𝒩 := 𝒱) ω I p p := by
      simpa only [hOnly g hg, hOnly f hf] using hGF
    exact PowerlessKleeneBrouwerSyntax.irreflexive_l hSelf

def fiber_m {Γ Δ : SortContext ℒ} (ω I U n b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists U <|
    .conj (PowerlessValueBounded.formula_m (.bvar .here) (up n) (up b)) <|
      membershipLevyBound.boundedForall (up U) <|
        .imp (PowerlessValueBounded.formula_m (.bvar .here) (up (up n)) (up (up b)))
          (.neg (compare_m (up (up ω)) (up (up I)) (.bvar .here) (.bvar (.there .here))))

theorem fiber_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω I U n b : Term ℒ Γ Δ .set) :
    (fiber_m ω I U n b).satisfies η ↔
      ∃ f, member_l 𝒩 f (U.eval η) ∧ value_l f (n.eval η) (b.eval η) ∧
        ∀ g, member_l 𝒩 g (U.eval η) → value_l g (n.eval η) (b.eval η) →
          ¬compare_l (𝒩 := 𝒩) (ω.eval η) (I.eval η) g f := by
  simp only [fiber_m, Formula.LevyBound.boundedExists, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, compare_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def minimum_m {Γ Δ : SortContext ℒ} (ω I U : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists U <| membershipLevyBound.boundedForall (up U) <|
    .neg (compare_m (up (up ω)) (up (up I)) (.bvar .here) (.bvar (.there .here)))

theorem minimum_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω I U : Term ℒ Γ Δ .set) :
    (minimum_m ω I U).satisfies η ↔ ∃ f, member_l 𝒩 f (U.eval η) ∧
      ∀ g, member_l 𝒩 g (U.eval η) → ¬compare_l (𝒩 := 𝒩) (ω.eval η) (I.eval η) g f := by
  simp only [minimum_m, Formula.LevyBound.boundedExists, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    compare_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (ω I p n U : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (ThirdOrderTheory.subset_m I ω) <|
    .imp (SecondOrderObjectSyntax.member_m n ω) <| .imp (PowerlessMapBounded.formula_m p n I) <|
      .imp (membershipLevyBound.boundedForall U
        (PowerlessKleeneBrouwerPrefix.extension_m (up ω) (up I) (up p) (up n) (.bvar .here))) <|
        .imp (.existsE .set (SecondOrderObjectSyntax.member_m (.bvar .here) (up U))) <|
          .imp (membershipLevyBound.boundedForall I <|
            .imp (PowerlessKleeneBrouwerBranchMinimum.branch_m (up n) (up U) (.bvar .here))
              (fiber_m (up ω) (up I) (up U) (up n) (.bvar .here)))
            (minimum_m ω I U)

def sentence_m {Δ : SortContext ℒ} (ω I p n U : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω I p n U)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I p n U : Term ℒ [] Δ .set) : (sentence_m ω I p n U).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    ThirdOrderSemantics.subset_formula_l, subset_l, SecondOrderObjectSyntax.member_m,
    PowerlessMapBounded.formula_l, PowerlessKleeneBrouwerPrefix.extension_formula_l,
    Formula.LevyBound.boundedForall, Formula.LevyBound.membership, membershipLevyBound,
    PowerlessKleeneBrouwerBranchMinimum.branch_formula_l, fiber_formula_l, minimum_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact fun hω hSub hn hp hU hNonempty hFibers =>
    step_l (hℳ := hℳ) hω hSub hn hp hU hNonempty hFibers

theorem derives_m {Δ : SortContext ℒ} (ω I p n U : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω I p n U)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω I p n U)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerMinimumStep
