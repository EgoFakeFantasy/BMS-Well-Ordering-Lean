import BMSConstructibleBridge.PowerlessRelativeMemberSatisfactionReading
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseClosure
import BMSConstructibleBridge.PowerlessMemberCollapseTransport
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparationDerives

/-! # 实际坍缩后的完整静态与 Sat 包及原对象读取句

同一个十参数原公式先从实际 MemberI 沿原 H 运输到 MemberT，再由
实际目标传递性和已证真实闭包读回原商。源包仍须由原共同族给出；
不预供目标完整源理论、可构造层资格或图值选择函数。

纯 ℒ 的读取守卫句另外经原图翻译取得普通 Derives Z₂ 出口。全部参数
在同一域中的资格显式保留；域对象自身不要求属于域。这里尚未识别
原 Def 截迹，也未消去最终候选源存在性前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseEvaluation

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

/-- 自由槽从最深至首槽为 ω、A、e、t₁、t₂、t₃、P、N、F、R。 -/
abbrev context_m : SortContext ℒ :=
  [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set]

private abbrev ω_m : Term ℒ [] context_m .set :=
  .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))

def data_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A e t₁ t₂ t₃ P N F R : carrier_l 𝒩) : Prop :=
  PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒩) ω e t₁ t₂ t₃ P N F ∧
    PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒩) ω A e t₁ t₂ t₃ P F R

def data_m : Formula ℒ [] context_m :=
  let A : Term ℒ [] context_m .set :=
    .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let e : Term ℒ [] context_m .set :=
    .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let t₁ : Term ℒ [] context_m .set :=
    .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let t₂ : Term ℒ [] context_m .set :=
    .fvar (.there (.there (.there (.there (.there .here)))))
  let t₃ : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there .here))))
  let P : Term ℒ [] context_m .set := .fvar (.there (.there (.there .here)))
  let N : Term ℒ [] context_m .set := .fvar (.there (.there .here))
  let F : Term ℒ [] context_m .set := .fvar (.there .here)
  let R : Term ℒ [] context_m .set := .fvar .here
  .conj (PowerlessSatisfactionExistenceSyntax.static_m ω_m e t₁ t₂ t₃ P N F)
    (PowerlessSatisfactionSpecification.spec_m ω_m A e t₁ t₂ t₃ P F R)

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (η : Env 𝒩 [] context_m) :
    data_m.satisfies η ↔ data_l (𝒩 := 𝒩)
      (η.freeVal (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
      (η.freeVal (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
      (η.freeVal (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (η.freeVal (.there (.there (.there (.there (.there (.there .here)))))))
      (η.freeVal (.there (.there (.there (.there (.there .here))))))
      (η.freeVal (.there (.there (.there (.there .here)))))
      (η.freeVal (.there (.there (.there .here))))
      (η.freeVal (.there (.there .here))) (η.freeVal (.there .here)) (η.freeVal .here) := by
  simp only [data_m, data_l, ω_m, Formula.satisfies,
    PowerlessSatisfactionExistenceSyntax.static_formula_l,
    PowerlessSatisfactionSpecification.spec_formula_l, Term.eval]

/-- 全部参数在域中的资格不包含域本身；结论仍是完整原公式。 -/
def schema_m : Formula ℒ [] (.set :: context_m) :=
  let W : Term ℒ [] (.set :: context_m) .set := .fvar .here
  .imp (PowerlessRelativeHierarchyDerives.transitive_m W) <|
    .imp (PowerlessRelativeFiniteHullAssignments.closed_m W) <|
      .imp (SecondOrderOmegaSyntax.omega_m (ω_m.weakenFree SetTheory.SetSort.set)) <|
        .imp (parameters_m context_m W (fun v => .fvar (.there v))) <|
          .imp (PowerlessRelativization.formula_m data_m)
            (data_m.weakenFree SetTheory.SetSort.set)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ζ
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeFiniteHullAssignments.closed_formula_l,
    SecondOrderOmegaSyntax.omega_l]
  intro hTrans hClosed hω hParams hData
  have hParams' := (parameters_formula_l context_m ζ (.fvar .here)
    (fun v => .fvar (.there v))).mp hParams
  let W := ζ.freeVal .here
  have hW : PowerlessNaturalOrder.transitive_l (ℳ := SecondOrderQuotient.structure_l hℳ) W :=
    fun x y hx hy => hTrans x hx y hy
  have h₀ : ∃ x, mem_l hℳ x W :=
    ⟨ζ.freeVal (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))),
      hParams' _ (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))⟩
  let η : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) W h₀) [] context_m :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with
        | .set => ⟨ζ.freeVal (.there v), hParams' _ v⟩ }
  have hEnv : (PowerlessRelativization.env_l η).pushFree W = ζ := by
    apply Env.ext
    · intro _ v
      nomatch v
    · intro s v
      cases s
      cases v <;> rfl
  have hNative := (formula_l η).mp
    ((PowerlessRelativization.formula_l data_m η).mp (hEnv.symm ▸ hData))
  have hRaw := PowerlessRelativeMemberSatisfactionReading.guarded_l hW hClosed hω
    hNative.1 hNative.2
  have hRead := (formula_l (PowerlessRelativization.env_l η)).mpr hRaw
  rw [← hEnv]
  exact (Formula.satisfies_weakenFree (PowerlessRelativization.env_l η) W data_m).mpr hRead

/-- 原语言、原 Type 0 模型解释与原推导核；没有替换背景理论。 -/
theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m sentence_m (fun _ hℳ => models_l hℳ)

section Collapse

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {I T H : SecondOrderQuotient.type_l hℳ}
  {hI : ∃ x, mem_l hℳ x I} {hT : ∃ x, mem_l hℳ x T}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ℳ₁" => PowerlessMemberStructure.structure_l (ℳ := 𝒱) I hI
local notation "𝒩₁" => PowerlessMemberStructure.structure_l (ℳ := 𝒱) T hT

/-- 实际 H 运输同一个完整原包，不另选一个相似的 Sat 或编码图。 -/
theorem model_l (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (η : Env ℳ₁ [] context_m) (ξ : Env 𝒩₁ [] context_m)
    (h : PowerlessMemberCollapseTransport.environments_related_l
      (PowerlessMemberCollapseTransport.relation_l H) η ξ) :
    data_m.satisfies η ↔ data_m.satisfies ξ :=
  PowerlessMemberCollapseTransport.member_l H hH.2.1 hH.2.2.1
    hH.2.2.2.2.1 hH.2.2.2.2.2 data_m η ξ h

/-- 同一 H、原源包和真实基础闭包给出完整目标原商规格。 -/
theorem raw_l (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I)
    (η : Env ℳ₁ [] context_m) (ξ : Env 𝒩₁ [] context_m)
    (h : PowerlessMemberCollapseTransport.environments_related_l
      (PowerlessMemberCollapseTransport.relation_l H) η ξ)
    (hω : SecondOrderOmega.omega_l hℳ (ω_m.eval η).val)
    (hωI : ∀ x, mem_l hℳ x (ω_m.eval η).val → mem_l hℳ x I)
    (hData : data_m.satisfies η) :
    data_m.satisfies (PowerlessRelativization.env_l ξ) := by
  have hFixed := PowerlessRelativeMembershipCollapseBase.base_l hℳ
    (ω_m.eval η).val I T H
    (fun x hx y hy => SecondOrderOmegaTransitive.member_l hℳ hω hx hy)
    hωI hH.2.1 hH.2.2.2.1 (ω_m.eval η).property
  have hRelated := PowerlessMemberCollapseTransport.term_l h ω_m
  have hωEq : (ω_m.eval ξ).val = (ω_m.eval η).val :=
    SecondOrderFunctionProperties.value_unique_l hℳ hH.2.1 hRelated hFixed
  have hωTarget : SecondOrderOmega.omega_l hℳ (ω_m.eval ξ).val := hωEq.symm ▸ hω
  have hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) T :=
    fun x y hx hy => hH.1 x hx y hy
  have hNative := (formula_l ξ).mp ((model_l hH η ξ h).mp hData)
  have hRaw := PowerlessRelativeMemberSatisfactionReading.guarded_l
    hTrans (PowerlessRelativeMembershipCollapseClosure.closed_l hH hClosed)
    hωTarget hNative.1 hNative.2
  exact (formula_l (PowerlessRelativization.env_l ξ)).mpr hRaw

end Collapse

#print axioms formula_l
#print axioms models_l
#print axioms derives_m
#print axioms model_l
#print axioms raw_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseEvaluation
