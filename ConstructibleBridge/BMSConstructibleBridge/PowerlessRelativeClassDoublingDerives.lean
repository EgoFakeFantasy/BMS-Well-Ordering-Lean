import BMSConstructibleBridge.PowerlessRelativeClassDoubling
import BMSConstructibleBridge.PowerlessRelativeClassAdditionAbsolute
import BMSConstructibleBridge.PowerlessAdditionSyntax

/-! # 内部倍数图的原 Z₂ 对象出口

图的规格使用原无限迭代加法定义，不用有限轨迹检查式替换加法语义。
覆盖每个内部自然数及任意候选输出，保留非标准模型范围。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassDoublingDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def body_m {Γ Δ : SortContext ℒ} (ω e F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up ω)) <|
    .forallE .set <| .iff
      (SecondOrderObjectSyntax.value_m (up (up F)) (.bvar (.there .here)) (.bvar .here))
      (PowerlessAdditionSyntax.addition_m (up (up ω)) (up (up e)) (.bvar (.there .here))
        (.bvar (.there .here)) (.bvar .here))

theorem body_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e F : Term ℒ Γ Δ .set) : (body_m ω e F).satisfies η ↔
      ∀ n, member_l 𝒩 n (ω.eval η) → ∀ y, value_l (ℳ := 𝒩) (F.eval η) n y ↔
        PowerlessAddition.addition_l (ℳ := 𝒩) (ω.eval η) (e.eval η) n n y := by
  simp only [body_m, Formula.satisfies, value_formula_l, PowerlessAdditionSyntax.addition_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def sentence_m : Sentence ℒ := .forallE .set <| .forallE .set <|
  .imp (SecondOrderOmegaSyntax.omega_m (.bvar (.there .here))) <|
    .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here))))) <|
      .existsE .set <| .conj
        (SecondOrderObjectSyntax.map_m (.bvar .here) (.bvar (.there (.there .here))) (.bvar (.there (.there .here))))
        (body_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))

theorem sentence_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} : sentence_m.TrueIn 𝒩 ↔
    ∀ ω e : carrier_l 𝒩, omega_l (ℳ := 𝒩) ω → (∀ x, ¬member_l 𝒩 x e) →
      ∃ F, map_l (ℳ := 𝒩) F ω ω ∧ ∀ n, member_l 𝒩 n ω → ∀ y,
        value_l (ℳ := 𝒩) F n y ↔ PowerlessAddition.addition_l (ℳ := 𝒩) ω e n n y := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, omega_formula_l, map_formula_l,
    body_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
  rfl

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply sentence_l.mpr
  intro ω e hω he
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) K.omega_spec
  have heEq : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := SecondOrderQuotient.ext_l hℳ _ _
    (fun x => iff_of_false ((PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp he x)
      (PowerlessBMSQuotientSuccessor.zero_l K x))
  obtain ⟨α, C₀, hC₀, hωC₀⟩ := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)
  obtain ⟨β, hβ, hαβ, hNoMax⟩ := SecondOrderOrdinalLimitDerives.exists_l hℳ α
    (PowerlessRelativeLevelClosure.ordinal_l hℳ hC₀)
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hβ
  have hωC := PowerlessRelativeLevelClosure.subset_l hℳ hBase hαβ hC₀ hC K.omega hωC₀
  obtain ⟨F, ω', hω', hMap, hPoint⟩ := PowerlessRelativeClassDoubling.exists_l K hBase hC
    ⟨⟨α, hαβ⟩, hNoMax⟩ hωC
  have hEq : ω' = ω := Subtype.ext (hω'.trans hωEq.symm)
  subst ω'
  have hMap' := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) F ω ω).mp hMap
  refine ⟨F, hMap, fun n hn y => ?_⟩
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n.val, hωEq ▸ hn⟩
  have hi' : n.val = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
  have hAdd := PowerlessRelativeClassAdditionAbsolute.instance_l (hBase := hBase) K
    (ω := ω) (e := e) (a := n) (b := n) (c := y) hωEq heEq hi' hi'
  constructor
  · intro hValue
    apply hAdd.mpr
    have hValue' := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F n y).mp hValue
    rw [hi'] at hValue'
    exact SecondOrderFunctionProperties.value_unique_l hℳ hMap' hValue' (hPoint i)
  · intro hAdd'
    apply (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F n y).mpr
    change value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val n.val y.val
    rw [hi', hAdd.mp hAdd']
    exact hPoint i

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassDoublingDerives
