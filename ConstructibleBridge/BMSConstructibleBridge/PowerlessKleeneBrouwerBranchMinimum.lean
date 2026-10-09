import BMSConstructibleBridge.PowerlessKleeneBrouwerPrefix

/-! # 非空下一分支的实际最小值

纯隶属 ℒ，原 Z₂。U 可是任意 raw 序列子集；原分离从实际 ω 中
收集下一坐标的分支值，原正则性取最小值。没有把 U 假定为 Class，
也没有从逐元素存在抽取 Type 层函数。原对象出口保留同一 U 和坐标。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerBranchMinimum

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def branch_m {Γ Δ : SortContext ℒ} (n U b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists U
    (PowerlessValueBounded.formula_m (.bvar .here) (up n) (up b))

theorem branch_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (n U b : Term ℒ Γ Δ .set) :
    (branch_m n U b).satisfies η ↔
      ∃ f, member_l 𝒩 f (U.eval η) ∧ value_l f (n.eval η) (b.eval η) := by
  simp only [branch_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def result_m {Γ Δ : SortContext ℒ} (n I U : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists I <|
    .conj (branch_m (up n) (up U) (.bvar .here)) <|
      membershipLevyBound.boundedForall (up U) <|
        membershipLevyBound.boundedForall (up (up I)) <|
          let b : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
          let g : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
          let a : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
          .imp (PowerlessValueBounded.formula_m g (up (up (up n))) a)
            (.disj (.equal b a) (SecondOrderObjectSyntax.member_m b a))

theorem result_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (n I U : Term ℒ Γ Δ .set) :
    (result_m n I U).satisfies η ↔
      ∃ b, member_l 𝒩 b (I.eval η) ∧ (∃ f, member_l 𝒩 f (U.eval η) ∧ value_l f (n.eval η) b) ∧
        ∀ g, member_l 𝒩 g (U.eval η) → ∀ a, member_l 𝒩 a (I.eval η) →
          value_l g (n.eval η) a → b = a ∨ member_l 𝒩 b a := by
  simp only [result_m, Formula.LevyBound.boundedExists, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies, branch_formula_l,
    PowerlessValueBounded.formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem least_l {ω I U n : Raw} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ a, mem_l hℳ a I → mem_l hℳ a ω)
    (hU : ∀ f, mem_l hℳ f U → PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω I f)
    (hNonempty : ∃ f, mem_l hℳ f U ∧ ∃ b, mem_l hℳ b I ∧ value_l (ℳ := 𝒱) f n b) :
    ∃ b, mem_l hℳ b I ∧ (∃ f, mem_l hℳ f U ∧ value_l (ℳ := 𝒱) f n b) ∧
      ∀ g, mem_l hℳ g U → ∀ a, mem_l hℳ a I →
        value_l (ℳ := 𝒱) g n a → b = a ∨ mem_l hℳ b a := by
  let φ : Formula ℒ [] [.set, .set, .set] :=
    branch_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  let η : Env 𝒱 [] [.set, .set] := ((Env.empty).pushFree U).pushFree n
  have hφRead b : φ.satisfies (η.pushFree b) ↔
      ∃ f, mem_l hℳ f U ∧ value_l (ℳ := 𝒱) f n b := by
    simp only [φ, η, branch_formula_l, Term.eval]
    rfl
  obtain ⟨D, hD⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
    (SecondOrderSeparationAxiom.models_l hℳ φ η) ω
  have hDRead b : mem_l hℳ b D ↔ mem_l hℳ b ω ∧
      ∃ f, mem_l hℳ f U ∧ value_l (ℳ := 𝒱) f n b :=
    (hD b).trans (and_congr Iff.rfl (hφRead b))
  obtain ⟨f₀, hf₀, b₀, hb₀, hfb₀⟩ := hNonempty
  have hFoundation := SecondOrderFoundation.models_l hℳ
  change ∀ D : Raw, (∃ b, mem_l hℳ b D) →
    ∃ b, mem_l hℳ b D ∧ ∀ a, mem_l hℳ a b → ¬mem_l hℳ a D at hFoundation
  obtain ⟨b, hbD, hMin⟩ := hFoundation D
    ⟨b₀, (hDRead b₀).mpr ⟨hSub b₀ hb₀, f₀, hf₀, hfb₀⟩⟩
  obtain ⟨hbω, f, hfU, hfb⟩ := (hDRead b).mp hbD
  obtain ⟨_m, _hm, hf⟩ := hU f hfU
  refine ⟨b, (SecondOrderFunctionProperties.value_mem_l hℳ hf hfb).2, ⟨f, hfU, hfb⟩, ?_⟩
  intro g hgU a ha hga
  have hOrd := SecondOrderOmegaOrdinal.ordinal_l hℳ hω
  rcases hOrd.wellOrder.linear.compare b hbω a (hSub a ha) with hEq | hba | hab
  · exact Or.inl (SecondOrderQuotient.ext_l hℳ b a hEq)
  · exact Or.inr hba
  · exact (hMin a hab ((hDRead a).mpr ⟨hSub a ha, g, hgU, hga⟩)).elim

def schema_m {Δ : SortContext ℒ} (ω I U n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (ThirdOrderTheory.subset_m I ω) <|
    .imp (membershipLevyBound.boundedForall U
      (PowerlessRelativeClassFiniteSequences.sequence_m (up ω) (up I) (.bvar .here))) <|
      .imp (membershipLevyBound.boundedExists U <|
        membershipLevyBound.boundedExists (up I) <|
          PowerlessValueBounded.formula_m (.bvar (.there .here)) (up (up n)) (.bvar .here))
        (result_m n I U)

def sentence_m {Δ : SortContext ℒ} (ω I U n : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω I U n)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I U n : Term ℒ [] Δ .set) : (sentence_m ω I U n).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    ThirdOrderSemantics.subset_formula_l, subset_l,
    Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound,
    PowerlessRelativeClassFiniteSequences.sequence_formula_l,
    PowerlessValueBounded.formula_l, result_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact fun hω hSub hU hNonempty => least_l (hℳ := hℳ) hω hSub hU hNonempty

theorem derives_m {Δ : SortContext ℒ} (ω I U n : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω I U n)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω I U n)

#print axioms least_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerBranchMinimum
