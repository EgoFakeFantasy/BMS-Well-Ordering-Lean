import BMSConstructibleBridge.PowerlessDefinableMembershipDiagram
import BMSConstructibleBridge.SecondOrderCollapseSyntax

/-! # 可定义虚拟隶属图的实际集合坍缩

纯隶属 ℒ、原 Z₂。单值部分求值的全输出像不要求是集合；直接构造
代码隶属图、其真实域域及传递坍缩值域、满射集合函数和递归方程。
对象模式只要求原公式在 ω 上单值，没有 Collection、选择或外部良基。
仅坍缩真实域域：无邻接边的孤立代码不在函数域中。所得 T/H 是 raw
对象，不预称 Class；虚拟壳的元素性、凝聚和类内重新枚举仍须另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableMembershipCollapse

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessDefinableMembershipDiagram (spec_l spec_m value_iff_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def domain_m {Γ Δ : SortContext ℒ} (A D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up D)) <|
    .existsE .set <| .disj
      (SecondOrderObjectSyntax.value_m (up (up A)) (.bvar (.there .here)) (.bvar .here))
      (SecondOrderObjectSyntax.value_m (up (up A)) (.bvar .here) (.bvar (.there .here)))

def domain_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (A D : 𝒩.Carrier .set) : Prop :=
  ∀ x, member_l 𝒩 x D ↔ ∃ y, value_l A x y ∨ value_l A y x

theorem domain_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (A D : Term ℒ Γ Δ .set) :
    (domain_m A D).satisfies η ↔ domain_l (A.eval η) (D.eval η) := by
  simp only [domain_m, domain_l, Formula.satisfies, ThirdOrderSemantics.value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 正则数图的真实域域由原理解取得，不收集原求值输出。 -/
theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (hUnique : ∀ n a b, SecondOrderQuotient.mem_l hℳ n K.omega →
      φ.satisfies ((η.pushFree n).pushFree a) → φ.satisfies ((η.pushFree n).pushFree b) → a = b) :
    ∃ A D T H : Raw, spec_l φ η K.omega A ∧ domain_l (𝒩 := 𝒱) A D ∧
      SecondOrderCollapseFunction.spec_l hℳ A D T H := by
  obtain ⟨A, R, hSpec, _, hR, hWF⟩ :=
    PowerlessDefinableMembershipDiagram.coded_exists_l K φ η hUnique
  have hRead n m : SecondOrderPairing.relation_l R n m ↔
      SecondOrderFunctionObjects.value_l hℳ A (numberCode_l K n).val (numberCode_l K m).val := by
    refine (hR n m).trans ⟨?_, ?_⟩
    · intro h
      exact (value_iff_l φ η hSpec _ _).mpr
        ⟨(numberCode_l K n).property, (numberCode_l K m).property, h⟩
    · intro h
      exact ((value_iff_l φ η hSpec _ _).mp h).2.2
  obtain ⟨P, hP⟩ := SecondOrderCollapseGraph.field_exists_l hℳ R
  obtain ⟨D, hD⟩ := SecondOrderNaturalSubsets.exists_l hℳ K.less K.less_spec P
  have hCode : ∀ x, SecondOrderQuotient.mem_l hℳ x D ↔
      ∃ n, SecondOrderCollapseGraph.field_l R n ∧ x = (numberCode_l K n).val := by
    intro x
    exact (hD x).trans (exists_congr (fun n => and_congr (hP n) Iff.rfl))
  have hDomain : domain_l (𝒩 := 𝒱) A D := by
    intro x
    change SecondOrderQuotient.mem_l hℳ x D ↔ ∃ y,
      SecondOrderFunctionObjects.value_l hℳ A x y ∨ SecondOrderFunctionObjects.value_l hℳ A y x
    rw [hCode]
    constructor
    · rintro ⟨n, ⟨m, h | h⟩, rfl⟩
      · exact ⟨(numberCode_l K m).val, Or.inl ((hRead n m).mp h)⟩
      · exact ⟨(numberCode_l K m).val, Or.inr ((hRead m n).mp h)⟩
    · rintro ⟨y, h | h⟩
      · have hBounds := (value_iff_l φ η hSpec x y).mp h
        obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x, hBounds.1⟩
        obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨y, hBounds.2.1⟩
        have hn' : (numberCode_l K n).val = x := congrArg Subtype.val hn
        have hm' : (numberCode_l K m).val = y := congrArg Subtype.val hm
        rw [← hn', ← hm'] at h
        exact ⟨n, ⟨m, Or.inl ((hRead n m).mpr h)⟩, hn'.symm⟩
      · have hBounds := (value_iff_l φ η hSpec y x).mp h
        obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x, hBounds.2.1⟩
        obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨y, hBounds.1⟩
        have hn' : (numberCode_l K n).val = x := congrArg Subtype.val hn
        have hm' : (numberCode_l K m).val = y := congrArg Subtype.val hm
        rw [← hn', ← hm'] at h
        exact ⟨n, ⟨m, Or.inr ((hRead m n).mpr h)⟩, hn'.symm⟩
  obtain ⟨T, H, hCollapse⟩ := SecondOrderCollapseFunction.exists_l hℳ K.less R
    K.less_spec hWF A D hRead hCode
  exact ⟨A, D, T, H, hSpec, hDomain, hCollapse⟩

def conclusion_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    let A : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set :=
      .bvar (.there (.there (.there .here)))
    let D := .bvar (.there (.there .here))
    let T := .bvar (.there .here)
    let H := .bvar .here
    .conj (spec_m φ (up (up (up (up ω)))) A) <|
      .conj (domain_m A D) (SecondOrderCollapseSyntax.formula_m A D T H)

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ [] Δ :=
  .forallE .set <| .imp (SecondOrderOmegaSyntax.omega_m (.bvar .here)) <|
    .imp (PowerlessBMSQuotientSubsetImageDerives.unique_m φ (.bvar .here))
      (conclusion_m φ (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    PowerlessBMSQuotientSubsetImageDerives.unique_m,
    PowerlessBMSQuotientSubsetImageDerives.at_formula_l,
    PowerlessBMSQuotientSubsetImageDerives.parameters_pushBound_l,
    PowerlessBMSQuotientSubsetImageDerives.parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval, and_imp]
  intro ω hω hUnique
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  obtain rfl := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  obtain ⟨A, D, T, H, hSpec, hDomain, hCollapse⟩ := exists_l K φ η hUnique
  simp only [conclusion_m, Formula.satisfies, PowerlessDefinableMembershipDiagram.spec_formula_l,
    domain_formula_l, SecondOrderCollapseSyntax.formula_l,
    PowerlessBMSQuotientSubsetImageDerives.parameters_pushBound_l,
    PowerlessBMSQuotientSubsetImageDerives.parameters_empty_l, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  exact ⟨A, D, T, H, hSpec, hDomain, hCollapse⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableMembershipCollapse
