import BMSConstructibleBridge.PowerlessDefinableFiniteTrace
import BMSConstructibleBridge.PowerlessWeakSetInduction
import BMSConstructibleBridge.SecondOrderDefinableRelationImage
import BMSConstructibleBridge.SecondOrderRegularRelation

/-! # 可定义求值的隶属拉回是实际良基关系

原 Z₂ 中，集合定义域上的总单值原矩阵可拉回隶属为实际关系集合。
其每个非空内部子集有极小元，即便整个求值像尚未是集合。使用已有
传递超集、原分离及可定义类极小元，而非 Collection、无限选择或
模型外部良基性。这是项闭包坍缩的辅助原对象模式，不是凝聚定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableMembershipPullback

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives (at_m at_formula_l unique_m
  parameters_l parameters_pushBound_l parameters_empty_l)
open PowerlessDefinableFiniteTrace (lift_m lift_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

def edge_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ) (a b : carrier_l 𝒱) : Prop :=
  ∃ x y, φ.satisfies ((η.pushFree a).pushFree x) ∧
    φ.satisfies ((η.pushFree b).pushFree y) ∧ member_l 𝒱 x y

def edge_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <|
    .conj (at_m φ (up₂ a) (.bvar (.there .here))) <|
      .conj (at_m φ (up₂ b) (.bvar .here))
        (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here))

theorem edge_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ) (a b : Term ℒ Γ Δ .set) :
    (edge_m φ a b).satisfies η ↔ edge_l φ (parameters_l η) (a.eval η) (b.eval η) := by
  simp only [edge_m, edge_l, Formula.satisfies, at_formula_l, parameters_pushBound_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def matrix_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  edge_m (lift_m (lift_m φ)) (.fvar .here) (.fvar (.there .here))

theorem matrix_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ) (a b : carrier_l 𝒱) :
    (matrix_m φ).satisfies ((η.pushFree b).pushFree a) ↔ edge_l φ η a b := by
  simp only [matrix_m, edge_formula_l, edge_l, parameters_empty_l,
    Term.eval, Env.pushFree_here, Env.pushFree_there, lift_formula_l]

private def image_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (U y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up U))
    (at_m φ (.bvar .here) (up y))

private theorem image_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 Γ Δ) (U y : Term ℒ Γ Δ .set) :
    (image_m φ U y).satisfies η ↔ ∃ a, member_l 𝒱 a (U.eval η) ∧
      φ.satisfies (((parameters_l η).pushFree a).pushFree (y.eval η)) := by
  simp only [image_m, Formula.satisfies, at_formula_l, parameters_pushBound_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

private def image_template_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  image_m (lift_m (lift_m φ)) (.fvar (.there .here)) (.fvar .here)

private theorem image_template_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (U y : carrier_l 𝒱) :
    (image_template_m φ).satisfies ((η.pushFree U).pushFree y) ↔
      ∃ a, member_l 𝒱 a U ∧ φ.satisfies ((η.pushFree a).pushFree y) := by
  simp only [image_template_m, image_formula_l, parameters_empty_l,
    Term.eval, Env.pushFree_here, Env.pushFree_there, lift_formula_l]

def clean_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (R D : carrier_l 𝒱) : Prop :=
  ∀ p, member_l 𝒱 p R → ∃ a b, member_l 𝒱 a D ∧ member_l 𝒱 b D ∧ ordered_l a b p

def wf_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (D R : carrier_l 𝒱) : Prop :=
  ∀ U, (∃ a, member_l 𝒱 a U) → (∀ a, member_l 𝒱 a U → member_l 𝒱 a D) →
    ∃ a, member_l 𝒱 a U ∧ ∀ b, member_l 𝒱 b U → ¬value_l R b a

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem minimum_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (D : type_l hℳ)
    (hTotal : ∀ a, mem_l hℳ a D → ∃ x, φ.satisfies ((η.pushFree a).pushFree x))
    (hUnique : ∀ a x y, mem_l hℳ a D → φ.satisfies ((η.pushFree a).pushFree x) →
      φ.satisfies ((η.pushFree a).pushFree y) → x = y)
    (U : type_l hℳ) (hNonempty : ∃ a, mem_l hℳ a U)
    (hSubset : ∀ a, mem_l hℳ a U → mem_l hℳ a D) :
    ∃ a, mem_l hℳ a U ∧ ∀ b, mem_l hℳ b U → ¬edge_l φ η b a := by
  obtain ⟨a, ha⟩ := hNonempty
  obtain ⟨x, hx⟩ := hTotal a (hSubset a ha)
  have hSome : ∃ y, (image_template_m φ).satisfies ((η.pushFree U).pushFree y) :=
    ⟨x, (image_template_formula_l φ η U x).mpr ⟨a, ha, hx⟩⟩
  obtain ⟨y, hy, hMin⟩ := PowerlessWeakSetInduction.minimum_l
    (SecondOrderWeakSetTheory.models_l hℳ) (image_template_m φ) (η.pushFree U) hSome
  obtain ⟨c, hc, hcy⟩ := (image_template_formula_l φ η U y).mp hy
  refine ⟨c, hc, fun b hb hEdge => ?_⟩
  obtain ⟨z, w, hbz, hcw, hzw⟩ := hEdge
  have hwy := hUnique c w y (hSubset c hc) hcw hcy
  subst w
  exact hMin z hzw ((image_template_formula_l φ η U z).mpr ⟨b, hb, hbz⟩)

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (D : type_l hℳ)
    (hTotal : ∀ a, mem_l hℳ a D → ∃ x, φ.satisfies ((η.pushFree a).pushFree x))
    (hUnique : ∀ a x y, mem_l hℳ a D → φ.satisfies ((η.pushFree a).pushFree x) →
      φ.satisfies ((η.pushFree a).pushFree y) → x = y) :
    ∃ R, clean_l (𝒱 := SecondOrderQuotient.structure_l hℳ) R D ∧
      (∀ a b, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R a b ↔
        mem_l hℳ a D ∧ mem_l hℳ b D ∧ edge_l φ η a b) ∧
      wf_l (𝒱 := SecondOrderQuotient.structure_l hℳ) D R := by
  obtain ⟨R, hR⟩ := SecondOrderDefinableRelationImage.exists_l hℳ (matrix_m φ) η D D
  have hClean : clean_l (𝒱 := SecondOrderQuotient.structure_l hℳ) R D := by
    intro p hp
    obtain ⟨a, b, ha, hb, _, hPair⟩ := (hR p).mp hp
    exact ⟨a, b, ha, hb, hPair⟩
  have hRead (a b : type_l hℳ) : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R a b ↔
      mem_l hℳ a D ∧ mem_l hℳ b D ∧ edge_l φ η a b := by
    constructor
    · rintro ⟨p, hp, hPair⟩
      obtain ⟨c, d, hc, hd, hcd, hPair'⟩ := (hR p).mp hp
      obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hPair hPair').mp rfl
      exact ⟨hc, hd, (matrix_formula_l φ η _ _).mp hcd⟩
    · rintro ⟨ha, hb, hab⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ a b
      exact ⟨p, (hR p).mpr ⟨a, b, ha, hb, (matrix_formula_l φ η a b).mpr hab, hp⟩, hp⟩
  refine ⟨R, hClean, hRead, fun U hU hUD => ?_⟩
  obtain ⟨a, ha, hMin⟩ := minimum_l hℳ φ η D hTotal hUnique U hU hUD
  exact ⟨a, ha, fun b hb hba => hMin b hb ((hRead b a).mp hba).2.2⟩

theorem regular_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {D R : type_l hℳ}
    (hWF : wf_l (𝒱 := SecondOrderQuotient.structure_l hℳ) D R) :
    SecondOrderRegularRelation.regular_l hℳ R D :=
  fun U hU hField => hWF U hU (fun a ha => (hField a ha).1)

def clean_m {Γ Δ : SortContext ℒ} (R D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up R)) <|
    .existsE .set <| .existsE .set <| .conj
      (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up₃ D)) <| .conj
        (SecondOrderObjectSyntax.member_m (.bvar .here) (up₃ D))
        (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here)
          (.bvar (.there (.there .here))))

def reading_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (D R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let a : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let b := .bvar .here
    .iff (SecondOrderObjectSyntax.value_m (up₂ R) a b) <| .conj
      (SecondOrderObjectSyntax.member_m a (up₂ D)) <| .conj
        (SecondOrderObjectSyntax.member_m b (up₂ D)) (edge_m φ a b)

def wf_m {Γ Δ : SortContext ℒ} (D R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <|
    let U : Term ℒ (.set :: Γ) Δ .set := .bvar .here
    .imp (.existsE .set (SecondOrderObjectSyntax.member_m (.bvar .here) (up U))) <|
      .imp (.forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up U))
        (SecondOrderObjectSyntax.member_m (.bvar .here) (up₂ D)))) <|
        .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up U)) <|
          .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up₂ U)) <|
            .neg (SecondOrderObjectSyntax.value_m (up₃ R) (.bvar .here) (.bvar (.there .here)))

theorem clean_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (R D : Term ℒ Γ Δ .set) :
    (clean_m R D).satisfies η ↔ clean_l (R.eval η) (D.eval η) := by
  simp only [clean_m, clean_l, Formula.satisfies, ordered_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem wf_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (D R : Term ℒ Γ Δ .set) :
    (wf_m D R).satisfies η ↔ wf_l (D.eval η) (R.eval η) := by
  simp only [wf_m, wf_l, Formula.satisfies, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem reading_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ) (D R : Term ℒ Γ Δ .set) :
    (reading_m φ D R).satisfies η ↔ ∀ a b, value_l (R.eval η) a b ↔
      member_l 𝒱 a (D.eval η) ∧ member_l 𝒱 b (D.eval η) ∧ edge_l φ (parameters_l η) a b := by
  simp only [reading_m, Formula.satisfies, value_formula_l, edge_formula_l, parameters_pushBound_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def total_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up D)) <|
    .existsE .set <| at_m φ (.bvar (.there .here)) (.bvar .here)

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (D : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (total_m φ D) <| .imp (unique_m φ D) <| .existsE .set <|
    .conj (clean_m (.bvar .here) (up D)) <|
      .conj (reading_m φ (up D) (.bvar .here)) (wf_m (up D) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (D : Term ℒ [] Δ .set) : Sentence ℒ := Metatheory.Formula.forall_close (schema_m φ D)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (D : Term ℒ [] Δ .set) :
    (sentence_m φ D).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, total_m, unique_m, Formula.satisfies, at_formula_l,
    clean_formula_l, wf_formula_l, reading_formula_l, parameters_pushBound_l, parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there, and_imp]
  intro η hTotal hUnique
  exact exists_l hℳ φ η (D.eval η) hTotal hUnique

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (D : Term ℒ [] Δ .set) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ D)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ D)

#print axioms minimum_l
#print axioms exists_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableMembershipPullback
