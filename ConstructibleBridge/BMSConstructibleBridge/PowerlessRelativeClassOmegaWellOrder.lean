import BMSConstructibleBridge.PowerlessRelativeClassWellOrderPullback

/-! # 内部 ω 隶属序的实际良序图

比较关系是内部自然数的实际隶属序，而非任意选择的枚举序。
内部子集的最小元由类内正则性取得；所有内部自然数均在量化范围内。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassOmegaWellOrder

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassEnumerationWellOrder (wellOrder_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

theorem exists_l {ω : type_l hℳ B} (hω : omega_l (ℳ := ClassModel) ω) :
    ∃ R : type_l hℳ B, wellOrder_l (ℳ := ClassModel) ω R ∧ ∀ x y : type_l hℳ B,
      value_l (ℳ := ClassModel) R x y ↔ mem_l hℳ x.val ω.val ∧
        mem_l hℳ y.val ω.val ∧ mem_l hℳ x.val y.val := by
  let φ : Formula ℒ [] [.set, .set] := member_m (.fvar .here) (.fvar (.there .here))
  obtain ⟨R, hRead⟩ := PowerlessRelativeClassRelationalGraph.exists_l
    (φ := φ) (.rel _ _) (Env.empty (M := ClassModel)) ω ω
  have hGraph (x y : type_l hℳ B) : value_l (ℳ := ClassModel) R x y ↔
      mem_l hℳ x.val ω.val ∧ mem_l hℳ y.val ω.val ∧ mem_l hℳ x.val y.val := hRead x y
  have hOrd := SecondOrderOmegaOrdinal.ordinal_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω)
  refine ⟨R, ⟨?_, ?_, ?_, ?_⟩, hGraph⟩
  · intro x hx hxx
    exact hOrd.wellOrder.linear.irrefl x.val hx ((hGraph x x).mp hxx).2.2
  · intro x y z hxyz hxy hyz
    exact (hGraph x z).mpr ⟨hxyz.1, hxyz.2.2,
      hOrd.wellOrder.linear.trans x.val hxyz.1 y.val hxyz.2.1 z.val hxyz.2.2
        ((hGraph x y).mp hxy).2.2 ((hGraph y z).mp hyz).2.2⟩
  · intro x y hxy
    rcases hOrd.wellOrder.linear.compare x.val hxy.1 y.val hxy.2 with hEq | hlt | hgt
    · exact Or.inr (Or.inl (Subtype.ext (SecondOrderQuotient.ext_l hℳ x.val y.val hEq)))
    · exact Or.inl ((hGraph x y).mpr ⟨hxy.1, hxy.2, hlt⟩)
    · exact Or.inr (Or.inr ((hGraph y x).mpr ⟨hxy.2, hxy.1, hgt⟩))
  · intro U hU
    have hFoundation := PowerlessRelativeClassStructure.foundation_l hℳ B hBase
    change ∀ U : type_l hℳ B, (∃ x : type_l hℳ B, mem_l hℳ x.val U.val) →
      ∃ x : type_l hℳ B, mem_l hℳ x.val U.val ∧ ∀ y : type_l hℳ B,
        mem_l hℳ y.val x.val → ¬mem_l hℳ y.val U.val at hFoundation
    obtain ⟨x, hx, hMin⟩ := hFoundation U hU.2
    exact ⟨x, hx, fun y hy hlt => hMin y ((hGraph y x).mp hlt).2.2 hy⟩

def specification_m {Γ Δ : SortContext ℒ} (ω R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (wellOrder_m ω R) <| .forallE .set <| .forallE .set <|
    .iff (value_m (up (up R)) (.bvar (.there .here)) (.bvar .here)) <|
      .conj (member_m (.bvar (.there .here)) (up (up ω))) <|
        .conj (member_m (.bvar .here) (up (up ω)))
          (member_m (.bvar (.there .here)) (.bvar .here))

theorem specification_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω R : Term ℒ Γ Δ .set) :
    (specification_m ω R).satisfies η ↔ wellOrder_l (ω.eval η) (R.eval η) ∧ ∀ x y,
      value_l (R.eval η) x y ↔ member_l ℳ₀ x (ω.eval η) ∧
        member_l ℳ₀ y (ω.eval η) ∧ member_l ℳ₀ x y := by
  simp only [specification_m, Formula.satisfies,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, value_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set] :=
  .imp (SecondOrderOmegaSyntax.omega_m (.fvar .here)) <|
    .existsE .set (specification_m (.fvar .here) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l, specification_formula_l, Term.eval]
  exact fun hω => exists_l (hBase := hBase) hω

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassOmegaWellOrder
