import BMSConstructibleBridge.PowerlessHereditaryParameterSeparation
import BMSConstructibleBridge.PowerlessHereditaryIntrinsicRelativization
import BMSConstructibleBridge.PowerlessHereditaryRelativization
import BMSConstructibleBridge.PowerlessWeakSeparationSyntax

/-! # 实际遗传子模型的完整分离模式及原 Z₂ 推导

纯隶属 ℒ，背景原 Z₂。每个外部原公式实例仍使用
SecondOrderSeparationAxiom.sentence_m；按遗传域真值分离，
不是按 Class 真值冒充。分离程序及所有实际枚举在证明内构造。

基底传递、非空且自身遗传是明确守卫，实际实数基底已证明满足。
没有 all_countable、首 Ω、Collection 或完整源理论前提。
这闭合完整分离这一项，不代表完整源模型或最终固定高度良序完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFullSeparation

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l
  PowerlessHereditaryStructure.structure_l PowerlessHereditaryStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₁" => PowerlessHereditaryStructure.structure_l hℳ B hBase

theorem exists_l (hB : PowerlessHereditaryClass.member_l hℳ B B)
    (hNonempty : ∃ d, mem_l hℳ d B) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒩₁ [] Δ)
    (X : PowerlessHereditaryStructure.type_l hℳ B) :
    ∃ Y : PowerlessHereditaryStructure.type_l hℳ B,
      ∀ x : PowerlessHereditaryStructure.type_l hℳ B,
        mem_l hℳ x.val Y.val ↔ mem_l hℳ x.val X.val ∧ φ.satisfies (η.pushFree x) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  let χ := PowerlessHereditaryIntrinsicRelativization.env_l η
  let X₀ := PowerlessHereditaryIntrinsicRelativization.lift_l (hBase := hBase) X
  obtain ⟨Y, hY, hRead⟩ := PowerlessHereditaryParameterSeparation.exists_l hBase K.omega_spec hB
    hNonempty (PowerlessHereditaryIntrinsicRelativization.formula_m φ) χ X₀ X.property
    (fun v => (η.freeVal v).property)
  refine ⟨⟨Y.val, hY⟩, fun x => ?_⟩
  let x₀ := PowerlessHereditaryIntrinsicRelativization.lift_l (hBase := hBase) x
  have hEnv : χ.pushFree (sort := SetTheory.SetSort.set) x₀ =
      PowerlessHereditaryIntrinsicRelativization.env_l (η.pushFree (sort := SetTheory.SetSort.set) x) := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; cases v <;> rfl
  have h := hRead x₀
  rw [hEnv] at h
  exact h.trans (and_congr Iff.rfl (PowerlessHereditaryIntrinsicRelativization.formula_l φ
    (η.pushFree x)))

theorem source_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hB : PowerlessHereditaryClass.member_l hℳ B B) (hNonempty : ∃ d, mem_l hℳ d B)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    (SecondOrderSeparationAxiom.sentence_m φ).TrueIn
      (PowerlessHereditaryStructure.structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  apply (PowerlessWeakSeparationSyntax.schema_formula_l φ η).mpr
  exact fun X => exists_l hB hNonempty φ η X

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def base_m {Γ Δ : SortContext ℒ} (B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .conj (PowerlessHereditaryClass.formula_m B B)
      (.existsE .set (SecondOrderObjectSyntax.member_m (.bvar .here) (up B)))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close <|
    .imp (base_m (.fvar .here))
      (PowerlessHereditaryRelativization.formula_m (SecondOrderSeparationAxiom.sentence_m φ))

theorem base_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B : Term ℒ Γ Δ .set) : (base_m B).satisfies η ↔
      (∀ x, mem_l hℳ x (B.eval η) → ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval η)) ∧
        PowerlessHereditaryClass.member_l hℳ (B.eval η) (B.eval η) ∧
          ∃ d, mem_l hℳ d (B.eval η) := by
  simp only [base_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessHereditaryClass.formula_l K, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hGuard
  obtain ⟨hBase, hB, hNonempty⟩ := (base_formula_l K η (.fvar .here)).mp hGuard
  have hEnv : η = (Env.empty (M := SecondOrderQuotient.structure_l h𝒩)).pushFree
      (sort := SetTheory.SetSort.set) (η.freeVal .here) := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; cases v with
      | here => rfl
      | there v => nomatch v
  rw [hEnv]
  exact (PowerlessHereditaryRelativization.sentence_l (hBase := hBase) K
    (SecondOrderSeparationAxiom.sentence_m φ)).mpr
    (source_models_l h𝒩 (η.freeVal .here) hBase hB hNonempty φ)

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ)

#print axioms exists_l
#print axioms source_models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFullSeparation
