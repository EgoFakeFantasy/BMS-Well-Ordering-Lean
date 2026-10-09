import BMSConstructibleBridge.SecondOrderWeakSetTheory
import BMSConstructibleBridge.PowerlessWeakSeparationSyntax
import BMSConstructibleBridge.PowerlessBMSQuotientSubsetImageDerives
import BMSConstructibleBridge.PowerlessFiniteSupport

/-!
# 无收集背景中的纯公式集合归纳

在任意弱集合论模型中，以传递超集局部化反例，再对分离出的反例集合应用
正则公理。所得是每个实际公式实例的归纳，并非商模型在外部良基。
最终给出弱集合论原推导及其原 Z₂ 图翻译推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessWeakSetInduction

open Logic FirstOrder PowerlessBMSQuotientSubsetImageDerives

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

private def insert_m {Γ Δ : SortContext ℒ} (x : Term ℒ Γ Δ .set) :
    VariableSubstitution ℒ (.set :: Δ) Γ Δ
  | _, .here => x
  | _, .there v => .fvar v

def at_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  φ.substitute (show Substitution ℒ [] (.set :: Δ) Γ Δ from
    .map (fun v => nomatch v) (insert_m x))

theorem at_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒩 Γ Δ) (x : Term ℒ Γ Δ .set) :
    (at_m φ x).satisfies η ↔ φ.satisfies ((parameters_l η).pushFree (x.eval η)) := by
  refine (Formula.satisfies_substitute η _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    cases v <;> rfl

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Formula ℒ [] Δ :=
  .imp (.forallE .set (.imp
    (.forallE .set (.imp
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
      (at_m φ (.bvar .here)))) (at_m φ (.bvar .here))))
    (.forallE .set (at_m φ (.bvar .here)))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

private def member_l (a b : 𝒩.Carrier .set) : Prop :=
  𝒩.relInterp .membership (.cons a (.cons b .nil))

theorem schema_formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env 𝒩 [] Δ) : (schema_m φ).satisfies η ↔
      ((∀ x, (∀ y, member_l y x → φ.satisfies (η.pushFree y)) →
        φ.satisfies (η.pushFree x)) → ∀ x, φ.satisfies (η.pushFree x)) := by
  simp only [schema_m, Formula.satisfies, at_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval, parameters_pushBound_l, parameters_empty_l]
  rfl

/-- 所有参数及对象均来自同一任意模型；仅实例公式可定义性用于分离。 -/
theorem induction_l (h𝒩 : Theory.Models 𝒩 SecondOrderWeakSetTheory.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒩 [] Δ)
    (hStep : ∀ x, (∀ y, member_l y x → φ.satisfies (η.pushFree y)) →
      φ.satisfies (η.pushFree x)) : ∀ x, φ.satisfies (η.pushFree x) := by
  classical
  have hPair := h𝒩 _ SecondOrderWeakSetTheory.axiom_m.pairing
  change ∀ a b : 𝒩.Carrier .set, ∃ c, ∀ d, member_l d c ↔ d = a ∨ d = b at hPair
  have hTrans := h𝒩 _ SecondOrderWeakSetTheory.axiom_m.transitive
  change ∀ a : 𝒩.Carrier .set, ∃ t, (∀ b, member_l b a → member_l b t) ∧
    ∀ b c, member_l b t → member_l c b → member_l c t at hTrans
  have hFoundation := h𝒩 _ SecondOrderWeakSetTheory.axiom_m.foundation
  change ∀ a : 𝒩.Carrier .set, (∃ b, member_l b a) → ∃ b, member_l b a ∧
    ∀ c, member_l c b → ¬member_l c a at hFoundation
  have hSep := h𝒩 _ (SecondOrderWeakSetTheory.axiom_m.separation (.neg φ))
  have hSep' := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp hSep η
  have hSep'' := (PowerlessWeakSeparationSyntax.schema_formula_l (.neg φ) η).mp hSep'
  intro x
  by_contra hx
  obtain ⟨s, hs⟩ := hPair x x
  obtain ⟨t, hst, ht⟩ := hTrans s
  obtain ⟨b, hb⟩ := hSep'' t
  have hxb : member_l x b := (hb x).mpr ⟨hst x ((hs x).mpr (Or.inl rfl)), hx⟩
  obtain ⟨y, hyb, hy⟩ := hFoundation b ⟨x, hxb⟩
  obtain ⟨hyt, hny⟩ := (hb y).mp hyb
  apply hny
  apply hStep y
  intro z hzy
  by_contra hnz
  exact hy z hzy ((hb z).mpr ⟨ht y z hyt hzy, hnz⟩)

/-- 非空可定义类有隶属极小元；不要求整个类已经是集合。 -/
theorem minimum_l (h𝒩 : Theory.Models 𝒩 SecondOrderWeakSetTheory.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒩 [] Δ)
    (h : ∃ x, φ.satisfies (η.pushFree x)) :
    ∃ x, φ.satisfies (η.pushFree x) ∧
      ∀ y, member_l y x → ¬φ.satisfies (η.pushFree y) := by
  classical
  by_contra hn
  have hAll := induction_l h𝒩 (.neg φ) η (fun x ih hx =>
    hn ⟨x, hx, fun y hy => ih y hy⟩)
  obtain ⟨x, hx⟩ := h
  exact hAll x hx

theorem models_l (h𝒩 : Theory.Models 𝒩 SecondOrderWeakSetTheory.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : (sentence_m φ).TrueIn 𝒩 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact (schema_formula_l φ η).mpr (induction_l h𝒩 φ η)

/-- 弱集合论的实际对象归纳模式，不借助 Collection。 -/
theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Derives SecondOrderWeakSetTheory.theory_m [] (sentence_m φ) :=
  PowerlessFiniteSupport.derives_m (fun _ h𝒩 => models_l h𝒩 φ)

theorem second_order_derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderWeakSetTheory.derives_m (derives_m φ)

#print axioms derives_m
#print axioms second_order_derives_m
#print axioms minimum_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessWeakSetInduction
