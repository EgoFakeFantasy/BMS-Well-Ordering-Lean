import BMSConstructibleBridge.SecondOrderRowOrderCanonical
import BMSConstructibleBridge.SecondOrderSeparationAxiom

/-! # 精确全部行族的纯 Δ₀ 检查

分别检查 Y 的每个成员确为一行，以及 I 的每个指标都在 Y 中有一行。
原 Z₂ 商中的实际分离提供行存在，外延性把任意环境候选行识别为 Y
中同一指标的已给行。因此等价覆盖全部环境集合，而非只覆盖相对 Class。
这里只消去行族规格的无界候选量词，不构造统一层次历史或其共同层界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRowFamilyBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open PowerlessRelativeClassRowFamily (row_l row_m row_delta_l row_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (I A Q Y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (membershipLevyBound.boundedForall Y <|
    membershipLevyBound.boundedExists (up I) <|
      row_m (up (up A)) (up (up Q)) (.bvar .here) (.bvar (.there .here))) <|
    membershipLevyBound.boundedForall I <|
      membershipLevyBound.boundedExists (up Y) <|
        row_m (up (up A)) (up (up Q)) (.bvar (.there .here)) (.bvar .here)

theorem delta_l {Γ Δ : SortContext ℒ} (I A Q Y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m I A Q Y) :=
  .conj (.bounded_forall Y (.bounded_exists (up I) (row_delta_l _ _ _ _)))
    (.bounded_forall I (.bounded_exists (up Y) (row_delta_l _ _ _ _)))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (I A Q Y : carrier_l 𝒩) : Prop :=
  (∀ Z, member_l 𝒩 Z Y → ∃ i, member_l 𝒩 i I ∧ row_l A Q i Z) ∧
    ∀ i, member_l 𝒩 i I → ∃ Z, member_l 𝒩 Z Y ∧ row_l A Q i Z

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (I A Q Y : Term ℒ Γ Δ .set) :
    (formula_m I A Q Y).satisfies η ↔ holds_l (I.eval η) (A.eval η) (Q.eval η) (Y.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.boundedExists, Formula.LevyBound.membership, membershipLevyBound,
    Formula.satisfies, row_formula_l, Arguments.eval, up, Term.eval_weakenBound]
  simp only [Term.eval, Env.pushBound, Assignment.push]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

private theorem row_exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (A Q i : SecondOrderQuotient.type_l hℳ) :
    ∃ Z, row_l (ℳ₀ := SecondOrderQuotient.structure_l hℳ) A Q i Z := by
  let φ : Formula ℒ [] [.set, .set, .set] := PowerlessValueBounded.formula_m
    (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set] :=
    ((Env.empty).pushFree Q).pushFree i
  obtain ⟨Z, hZ⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
    (SecondOrderSeparationAxiom.models_l hℳ φ η) A
  refine ⟨Z, fun x => ?_⟩
  have hValue : φ.satisfies (η.pushFree x) ↔
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) Q i x := by
    simpa only [φ, η, Term.eval, Env.pushFree, Assignment.push] using
      (PowerlessValueBounded.formula_l (η.pushFree x)
        (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here))
  exact (hZ x).trans (and_congr Iff.rfl hValue)

/-- 精确规格量化任意原商候选行；不把外部候选限制在 Class 或某个母层。 -/
theorem family_iff_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {I A Q Y : SecondOrderQuotient.type_l hℳ} :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) I A Q Y ↔
      PowerlessRelativeClassRowOrderCanonical.family_l
        (ℳ₀ := SecondOrderQuotient.structure_l hℳ) I A Q Y := by
  constructor
  · rintro ⟨hRows, hCover⟩ Z
    constructor
    · exact hRows Z
    · rintro ⟨i, hi, hRow⟩
      obtain ⟨W, hW, hRowW⟩ := hCover i hi
      have hEq : Z = W := SecondOrderQuotient.ext_l hℳ Z W
        (fun x => (hRow x).trans (hRowW x).symm)
      exact hEq.symm ▸ hW
  · intro hFamily
    refine ⟨fun Z hZ => (hFamily Z).mp hZ, ?_⟩
    intro i hi
    obtain ⟨Z, hRow⟩ := row_exists_l hℳ A Q i
    exact ⟨Z, (hFamily Z).mpr ⟨i, hi, hRow⟩, hRow⟩

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let I : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let A : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let Q : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let Y : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  .iff (formula_m I A Q Y) (SecondOrderRowOrderCanonical.family_m I A Q Y)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

/-- 无条件原 Z₂ 推出全部四参数实例的有界检查器与原精确行族规格等价。 -/
theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact (formula_l η _ _ _ _).trans
    ((family_iff_l hℳ).trans (SecondOrderRowOrderCanonical.family_formula_l η _ _ _ _).symm)

#print axioms delta_l
#print axioms formula_l
#print axioms family_iff_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRowFamilyBounded
