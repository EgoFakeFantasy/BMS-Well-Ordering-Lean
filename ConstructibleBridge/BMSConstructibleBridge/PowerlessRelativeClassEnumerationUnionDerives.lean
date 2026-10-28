import BMSConstructibleBridge.PowerlessRelativeClassEnumerationUnion

/-! # 两个类内可数集合之并可数：原 Z₂ 推导

对象句显式量化实际集合满射。所有存在量词都在类内；集合并、映射及满射
规格保留原纯隶属语言，不借用 Type 层的可数性声明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEnumerationUnionDerives

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def union_m {Γ Δ : SortContext ℒ} (U V W : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up W))
    (.disj (SecondOrderObjectSyntax.member_m (.bvar .here) (up U))
      (SecondOrderObjectSyntax.member_m (.bvar .here) (up V)))

theorem union_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (U V W : Term ℒ Γ Δ .set) : (union_m U V W).satisfies η ↔
      ∀ y, member_l 𝒩 y (W.eval η) ↔ member_l 𝒩 y (U.eval η) ∨ member_l 𝒩 y (V.eval η) := by
  simp only [union_m, Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem onto_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω U G : Term ℒ Γ Δ .set) : (PowerlessMemberDefSyntax.onto_m ω U G).satisfies η ↔
      ∀ y, member_l 𝒩 y (U.eval η) → ∃ i, member_l 𝒩 i (ω.eval η) ∧ value_l (ℳ := 𝒩) (G.eval η) i y := by
  simp only [PowerlessMemberDefSyntax.onto_m, Formula.satisfies, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

def conclusion_m {Γ Δ : SortContext ℒ} (ω W : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (SecondOrderObjectSyntax.map_m (.bvar .here) (up ω) (up W))
    (PowerlessMemberDefSyntax.onto_m (up ω) (up W) (.bvar .here))

theorem conclusion_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω W : Term ℒ Γ Δ .set) : (conclusion_m ω W).satisfies η ↔
      ∃ F, map_l (ℳ := 𝒩) F (ω.eval η) (W.eval η) ∧ ∀ y, member_l 𝒩 y (W.eval η) →
        ∃ i, member_l 𝒩 i (ω.eval η) ∧ value_l (ℳ := 𝒩) F i y := by
  simp only [conclusion_m, Formula.satisfies, map_formula_l, onto_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar .here
  let G : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let H : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let U : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let V : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let W : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (SecondOrderObjectSyntax.map_m G ω U) <|
    .imp (SecondOrderObjectSyntax.map_m H ω V) <| .imp (PowerlessMemberDefSyntax.onto_m ω U G) <|
      .imp (PowerlessMemberDefSyntax.onto_m ω V H) <| .imp (union_m U V W) (conclusion_m ω W)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y, SecondOrderQuotient.mem_l hℳ y x →
      SecondOrderQuotient.mem_l hℳ y B) :
    sentence_m.TrueIn (PowerlessRelativeClassStructure.structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l, map_formula_l, onto_l, union_l, conclusion_l]
  intro hω hG hH hGOnto hHOnto hW
  exact PowerlessRelativeClassEnumerationUnion.exists_l hω hG hH hGOnto hHOnto hW

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEnumerationUnionDerives
