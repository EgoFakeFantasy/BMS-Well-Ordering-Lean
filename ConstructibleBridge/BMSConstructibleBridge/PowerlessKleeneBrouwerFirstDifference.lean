import BMSConstructibleBridge.PowerlessKleeneBrouwerDecisive
import BMSConstructibleBridge.SecondOrderSeparationAxiom

/-! # 内部有限序列的最小差异位置

纯隶属 ℒ，原 Z₂。实际分离共同定义域中的差异点，再用原正则性
取得最小点；若差异集为空，整个共同前缀相同。所有图均可为 raw
参数，不要求预先取得其 Class 资格，也不假定内部长度外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerFirstDifference

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassSequenceSplit (prefix_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def mismatch_m {Γ Δ : SortContext ℒ} (I f g i : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists I <| membershipLevyBound.boundedExists (up I) <|
    .conj (PowerlessValueBounded.formula_m (up (up f)) (up (up i)) (.bvar (.there .here))) <|
      .conj (PowerlessValueBounded.formula_m (up (up g)) (up (up i)) (.bvar .here))
        (.neg (.equal (.bvar (.there .here)) (.bvar .here)))

def mismatch_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (I f g i : carrier_l 𝒩) : Prop :=
  ∃ a, member_l 𝒩 a I ∧ ∃ b, member_l 𝒩 b I ∧ value_l f i a ∧ value_l g i b ∧ a ≠ b

theorem mismatch_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (I f g i : Term ℒ Γ Δ .set) :
    (mismatch_m I f g i).satisfies η ↔
      mismatch_l (I.eval η) (f.eval η) (g.eval η) (i.eval η) := by
  simp only [mismatch_m, mismatch_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem equal_value_l {I f g n m j : Raw}
    (hf : map_l (ℳ := 𝒱) f n I) (hg : map_l (ℳ := 𝒱) g m I)
    (hjn : mem_l hℳ j n) (hjm : mem_l hℳ j m)
    (hNo : ¬mismatch_l (𝒩 := 𝒱) I f g j) :
    ∀ a, mem_l hℳ a I → (value_l (ℳ := 𝒱) g j a ↔ value_l (ℳ := 𝒱) f j a) := by
  classical
  obtain ⟨a, ha, _⟩ := hf.2 j hjn
  obtain ⟨b, hb, _⟩ := hg.2 j hjm
  have hEq : a = b := by
    by_contra hNe
    exact hNo ⟨a, ha.1, b, hb.1, ha.2, hb.2, hNe⟩
  subst b
  intro c _hc
  constructor
  · intro hgc
    have hEq := SecondOrderFunctionProperties.value_unique_l hℳ hg hgc hb.2
    subst c
    exact ha.2
  · intro hfc
    have hEq := SecondOrderFunctionProperties.value_unique_l hℳ hf hfc ha.2
    subst c
    exact hb.2

theorem least_l {ω k I f g n m : Raw} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hk : mem_l hℳ k ω) (hKn : ∀ j, mem_l hℳ j k → mem_l hℳ j n)
    (hKm : ∀ j, mem_l hℳ j k → mem_l hℳ j m)
    (hf : map_l (ℳ := 𝒱) f n I) (hg : map_l (ℳ := 𝒱) g m I) :
    prefix_l (ℳ₀ := 𝒱) k I f g ∨
      ∃ i, mem_l hℳ i k ∧ prefix_l (ℳ₀ := 𝒱) i I f g ∧ mismatch_l (𝒩 := 𝒱) I f g i := by
  classical
  let φ : Formula ℒ [] [.set, .set, .set, .set] :=
    mismatch_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar .here)
  let η : Env 𝒱 [] [.set, .set, .set] :=
    (((Env.empty).pushFree g).pushFree f).pushFree I
  have hφRead i : φ.satisfies (η.pushFree i) ↔ mismatch_l (𝒩 := 𝒱) I f g i := by
    simp only [φ, η, mismatch_formula_l, Term.eval]
    rfl
  obtain ⟨D, hD⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
    (SecondOrderSeparationAxiom.models_l hℳ φ η) k
  have hDRead i : mem_l hℳ i D ↔ mem_l hℳ i k ∧ mismatch_l (𝒩 := 𝒱) I f g i :=
    (hD i).trans (and_congr Iff.rfl (hφRead i))
  by_cases hNonempty : ∃ i, mem_l hℳ i D
  · have hFoundation := SecondOrderFoundation.models_l hℳ
    change ∀ D : Raw, (∃ i, mem_l hℳ i D) →
      ∃ i, mem_l hℳ i D ∧ ∀ j, mem_l hℳ j i → ¬mem_l hℳ j D at hFoundation
    obtain ⟨i, hiD, hMin⟩ := hFoundation D hNonempty
    obtain ⟨hik, hMismatch⟩ := (hDRead i).mp hiD
    have hkOrd : SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) k :=
      SetTheory.Structure.IsOrdinal.mem (SecondOrderOmegaOrdinal.ordinal_l hℳ hω) hk
    refine Or.inr ⟨i, hik, ?_, hMismatch⟩
    intro j hji
    have hjk := hkOrd.transitive i hik j hji
    exact equal_value_l hf hg (hKn j hjk) (hKm j hjk)
      (fun hDiff => hMin j hji ((hDRead j).mpr ⟨hjk, hDiff⟩))
  · refine Or.inl ?_
    intro j hjk
    exact equal_value_l hf hg (hKn j hjk) (hKm j hjk)
      (fun hDiff => hNonempty ⟨j, (hDRead j).mpr ⟨hjk, hDiff⟩⟩)

def result_m {Γ Δ : SortContext ℒ} (k I f g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (PowerlessRelativeClassSequenceSplitDerives.prefix_m k I f g) <|
    membershipLevyBound.boundedExists k <|
      .conj (PowerlessRelativeClassSequenceSplitDerives.prefix_m (.bvar .here) (up I) (up f) (up g))
        (mismatch_m (up I) (up f) (up g) (.bvar .here))

def schema_m {Δ : SortContext ℒ} (ω k I f g n m : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (SecondOrderObjectSyntax.member_m k ω) <|
    .imp (ThirdOrderTheory.subset_m k n) <| .imp (ThirdOrderTheory.subset_m k m) <|
      .imp (PowerlessMapBounded.formula_m f n I) <| .imp (PowerlessMapBounded.formula_m g m I)
        (result_m k I f g)

def sentence_m {Δ : SortContext ℒ} (ω k I f g n m : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω k I f g n m)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω k I f g n m : Term ℒ [] Δ .set) : (sentence_m ω k I f g n m).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, result_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    SecondOrderObjectSyntax.member_m, ThirdOrderSemantics.subset_formula_l, subset_l,
    PowerlessMapBounded.formula_l, PowerlessRelativeClassSequenceSplitDerives.prefix_formula_l,
    Formula.LevyBound.boundedExists, Formula.LevyBound.membership, membershipLevyBound,
    mismatch_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact fun hω hk hKn hKm hf hg => least_l (hℳ := hℳ) hω hk hKn hKm hf hg

theorem derives_m {Δ : SortContext ℒ} (ω k I f g n m : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω k I f g n m)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω k I f g n m)

#print axioms least_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerFirstDifference
