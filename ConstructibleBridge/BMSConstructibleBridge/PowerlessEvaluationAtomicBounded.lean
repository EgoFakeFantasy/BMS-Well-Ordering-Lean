import BMSConstructibleBridge.PowerlessEvaluationClause
import BMSConstructibleBridge.PowerlessValueBounded
import BMSConstructibleBridge.SecondOrderFunctionProperties
import BMSConstructibleBridge.SecondOrderAxioms

/-! # 赋值图上原子求值的纯 Δ₀ 检查

值见证只在给定陪域 A 中寻找。原商映射的坐标界给出与原无界关系的
双向等价，不要求变量预先属于定义域；非法变量两边同为假。
条件式闭句回传原 Z₂ 推导核，未假设整个相对类满足源集合论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationAtomicBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def equal_m {Γ Δ : SortContext ℒ} (A f i j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists A <| .conj
    (PowerlessValueBounded.formula_m (up f) (up i) (.bvar .here))
    (PowerlessValueBounded.formula_m (up f) (up j) (.bvar .here))

theorem equal_delta_l {Γ Δ : SortContext ℒ} (A f i j : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (equal_m A f i j) :=
  .bounded_exists A (.conj (PowerlessValueBounded.delta_l _ _ _) (PowerlessValueBounded.delta_l _ _ _))

def equal_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (A f i j : carrier_l 𝒩) : Prop :=
  ∃ a, member_l 𝒩 a A ∧ value_l (ℳ := 𝒩) f i a ∧ value_l (ℳ := 𝒩) f j a

theorem equal_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (A f i j : Term ℒ Γ Δ .set) :
    (equal_m A f i j).satisfies η ↔ equal_l (A.eval η) (f.eval η) (i.eval η) (j.eval η) := by
  simp only [equal_m, equal_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def member_m {Γ Δ : SortContext ℒ} (A f i j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  membershipLevyBound.boundedExists A <| membershipLevyBound.boundedExists (up A) <|
    .conj (PowerlessValueBounded.formula_m (w f) (w i) (.bvar (.there .here))) <| .conj
      (PowerlessValueBounded.formula_m (w f) (w j) (.bvar .here))
      (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here))

theorem member_delta_l {Γ Δ : SortContext ℒ} (A f i j : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (member_m A f i j) :=
  .bounded_exists A (.bounded_exists (up A) (.conj (PowerlessValueBounded.delta_l _ _ _)
    (.conj (PowerlessValueBounded.delta_l _ _ _) (.rel _ _))))

def member_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (A f i j : carrier_l 𝒩) : Prop :=
  ∃ a, ThirdOrderSemantics.member_l 𝒩 a A ∧ ∃ b, ThirdOrderSemantics.member_l 𝒩 b A ∧
    value_l (ℳ := 𝒩) f i a ∧ value_l (ℳ := 𝒩) f j b ∧ ThirdOrderSemantics.member_l 𝒩 a b

theorem member_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (A f i j : Term ℒ Γ Δ .set) :
    (member_m A f i j).satisfies η ↔ member_l (A.eval η) (f.eval η) (i.eval η) (j.eval η) := by
  simp only [member_m, member_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem equal_iff_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {n A f i j : type_l hℳ}
    (hf : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f n A) :
    equal_l (𝒩 := SecondOrderQuotient.structure_l hℳ) A f i j ↔
      PowerlessEvaluationClause.equal_l (ℳ := SecondOrderQuotient.structure_l hℳ) f i j := by
  constructor
  · rintro ⟨a, _, hi, hj⟩
    exact ⟨a, hi, hj⟩
  · rintro ⟨a, hi, hj⟩
    exact ⟨a, (SecondOrderFunctionProperties.value_mem_l hℳ hf hi).2, hi, hj⟩

theorem member_iff_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {n A f i j : type_l hℳ}
    (hf : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f n A) :
    member_l (𝒩 := SecondOrderQuotient.structure_l hℳ) A f i j ↔
      PowerlessEvaluationClause.member_l (ℳ := SecondOrderQuotient.structure_l hℳ) f i j := by
  constructor
  · rintro ⟨a, _, b, _, hi, hj, hab⟩
    exact ⟨a, b, hi, hj, hab⟩
  · rintro ⟨a, b, hi, hj, hab⟩
    exact ⟨a, (SecondOrderFunctionProperties.value_mem_l hℳ hf hi).2,
      b, (SecondOrderFunctionProperties.value_mem_l hℳ hf hj).2, hi, hj, hab⟩

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let n : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let A : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let f : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let i : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let j : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  .imp (SecondOrderObjectSyntax.map_m f n A) <| .conj
    (.iff (equal_m A f i j) (PowerlessEvaluationClause.equal_m f i j))
    (.iff (member_m A f i j) (PowerlessEvaluationClause.member_m f i j))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hf
  have hf' := (map_formula_l η _ _ _).mp hf
  exact ⟨(equal_formula_l η _ _ _ _).trans
    ((equal_iff_l hℳ hf').trans (PowerlessEvaluationClause.equal_formula_l η _ _ _).symm),
    (member_formula_l η _ _ _ _).trans
      ((member_iff_l hℳ hf').trans (PowerlessEvaluationClause.member_formula_l η _ _ _).symm)⟩

#print axioms equal_delta_l
#print axioms member_delta_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationAtomicBounded
