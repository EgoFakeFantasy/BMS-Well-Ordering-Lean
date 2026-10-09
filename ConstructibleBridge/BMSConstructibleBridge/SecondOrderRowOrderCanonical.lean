import BMSConstructibleBridge.PowerlessRelativeClassRowOrderCanonical
import BMSConstructibleBridge.SecondOrderMemberDefWellOrder

/-! # 规范行像集良序的原 Z₂ 对象推导

四个原商参数先置于实际共同传递基点。类内设施只构造图，最终载体规格、
完整比较图和良序量词均不受类守卫。任意环境候选行先与类内实际分离行
外延识别，故不会漏掉类外量词。此工具不是最终固定行 BMS 良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRowOrderCanonical

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m ordered_m)
open PowerlessRelativeClassRowFamily (row_l row_m row_delta_l row_formula_l)
open PowerlessRelativeClassRowOrderCanonical (family_l graph_l comparison_m comparison_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def family_m {Γ Δ : SortContext ℒ} (I A Q Y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up Y)) <|
    membershipLevyBound.boundedExists (up I) <|
      row_m (up (up A)) (up (up Q)) (.bvar .here) (.bvar (.there .here))

theorem family_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (I A Q Y : Term ℒ Γ Δ .set) :
    (family_m I A Q Y).satisfies η ↔ family_l (I.eval η) (A.eval η) (Q.eval η) (Y.eval η) := by
  simp only [family_m, family_l, Formula.satisfies, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, row_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def graph_m {Γ Δ : SortContext ℒ} (I U A Q Y L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up t))
  .forallE .set <| .iff (member_m (.bvar .here) (up L)) <|
    .existsE .set <| .existsE .set <|
      .conj (member_m (.bvar (.there .here)) (w Y)) <|
        .conj (member_m (.bvar .here) (w Y)) <|
          .conj (ordered_m (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here))))
            (comparison_m (w I) (w U) (w A) (w Q) (.bvar (.there .here)) (.bvar .here))

theorem graph_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (I U A Q Y L : Term ℒ Γ Δ .set) :
    (graph_m I U A Q Y L).satisfies η ↔
      graph_l (I.eval η) (U.eval η) (A.eval η) (Q.eval η) (Y.eval η) (L.eval η) := by
  simp only [graph_m, graph_l, Formula.satisfies, ordered_formula_l, comparison_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem row_absolute_l {B : type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    (A Q i y : PowerlessRelativeClassStructure.type_l hℳ B) :
    row_l (ℳ₀ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) A Q i y ↔
      row_l (ℳ₀ := 𝒱) A.val Q.val i.val y.val := by
  let η : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) [] [.set, .set, .set, .set] :=
    (((Env.empty.pushFree y).pushFree i).pushFree Q).pushFree A
  let a : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let q : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let k : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let z : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  exact (row_formula_l η a q k z).symm.trans
    ((PowerlessRelativeClassBounded.formula_l (row_delta_l a q k z) η).trans
      (row_formula_l (PowerlessRelativeClassRelativization.env_l η) a q k z))

theorem family_ambient_l {B : type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    {I A Q Y : PowerlessRelativeClassStructure.type_l hℳ B}
    (hY : family_l (ℳ₀ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) I A Q Y) :
    family_l (ℳ₀ := 𝒱) I.val A.val Q.val Y.val := by
  intro y
  constructor
  · intro hy
    let y' : PowerlessRelativeClassStructure.type_l hℳ B :=
      ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩
    obtain ⟨i, hi, hRow⟩ := (hY y').mp hy
    exact ⟨i.val, hi, (row_absolute_l (hBase := hBase) A Q i y').mp hRow⟩
  · rintro ⟨i, hi, hRow⟩
    let i' : PowerlessRelativeClassStructure.type_l hℳ B :=
      ⟨i, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase I.property hi⟩
    obtain ⟨z, hZ, _⟩ := PowerlessRelativeClassRowFamily.row_exists_l (hBase := hBase) A Q i'
    have hZRaw := (row_absolute_l (hBase := hBase) A Q i' z).mp hZ
    have hEq : y = z.val := SecondOrderQuotient.ext_l hℳ y z.val
      (fun x => (hRow x).trans (hZRaw x).symm)
    exact hEq.symm ▸ (hY z).mpr ⟨i', hi, hZ⟩

theorem exists_l {I U A Q : type_l hℳ} (hU : wellOrder_l (ℳ := 𝒱) I U) :
    ∃ Y L : type_l hℳ, family_l (ℳ₀ := 𝒱) I A Q Y ∧
      graph_l (ℳ₀ := 𝒱) I U A Q Y L ∧ wellOrder_l (ℳ := 𝒱) Y L := by
  obtain ⟨C₁, hC₁⟩ := SecondOrderPairObjects.pair_exists_l hℳ I U
  obtain ⟨C₂, hC₂⟩ := SecondOrderPairObjects.pair_exists_l hℳ A Q
  obtain ⟨C, hC⟩ := SecondOrderPairObjects.pair_exists_l hℳ C₁ C₂
  have hSup := SecondOrderTransitiveSuperset.models_l hℳ
  change ∀ C : type_l hℳ, ∃ B, (∀ x, mem_l hℳ x C → mem_l hℳ x B) ∧
    ∀ x y, mem_l hℳ x B → mem_l hℳ y x → mem_l hℳ y B at hSup
  obtain ⟨B, hCB, hTrans⟩ := hSup C
  have hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B :=
    fun x hx y hy => hTrans x y hx hy
  have hC₁B := hCB C₁ ((hC C₁).mpr (Or.inl rfl))
  have hC₂B := hCB C₂ ((hC C₂).mpr (Or.inr rfl))
  let I' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨I, PowerlessRelativeClassCorrespondence.base_l hℳ hBase
      (hTrans C₁ I hC₁B ((hC₁ I).mpr (Or.inl rfl)))⟩
  let U' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨U, PowerlessRelativeClassCorrespondence.base_l hℳ hBase
      (hTrans C₁ U hC₁B ((hC₁ U).mpr (Or.inr rfl)))⟩
  let A' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨A, PowerlessRelativeClassCorrespondence.base_l hℳ hBase
      (hTrans C₂ A hC₂B ((hC₂ A).mpr (Or.inl rfl)))⟩
  let Q' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨Q, PowerlessRelativeClassCorrespondence.base_l hℳ hBase
      (hTrans C₂ Q hC₂B ((hC₂ Q).mpr (Or.inr rfl)))⟩
  obtain ⟨Y, L, hFamily, hGraph, hOrder⟩ :=
    PowerlessRelativeClassRowOrderCanonical.exists_l (hBase := hBase) I' A' Q' U' hU
  exact ⟨Y.val, L.val, family_ambient_l hFamily, hGraph, hOrder⟩

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let I : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let U : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let A : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let Q : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let w (t : Term ℒ [] [.set, .set, .set, .set] .set) := up (up t)
  .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m I U) <|
    .existsE .set <| .existsE .set <|
      .conj (family_m (w I) (w A) (w Q) (.bvar (.there .here))) <|
        .conj (graph_m (w I) (w U) (w A) (w Q) (.bvar (.there .here)) (.bvar .here))
          (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (.bvar (.there .here)) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, family_formula_l, graph_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, up, Term.eval_weakenBound, Term.eval]
  exact fun hU => exists_l (hℳ := hℳ) hU

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

def specification_m {Γ Δ : SortContext ℒ} (I U A Q Y L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (family_m I A Q Y) <| .conj (graph_m I U A Q Y L)
    (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m Y L)

theorem specification_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (I U A Q Y L : Term ℒ Γ Δ .set) :
    (specification_m I U A Q Y L).satisfies η ↔ family_l (I.eval η) (A.eval η) (Q.eval η) (Y.eval η) ∧
      graph_l (I.eval η) (U.eval η) (A.eval η) (Q.eval η) (Y.eval η) (L.eval η) ∧
        wellOrder_l (Y.eval η) (L.eval η) := by
  simp only [specification_m, Formula.satisfies, family_formula_l, graph_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l]

def unique_schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let I : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let U : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let A : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let Q : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let w (t : Term ℒ [] [.set, .set, .set, .set] .set) := up (up t)
  .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m I U) <|
    .existsE .set <| .existsE .set <|
      .conj (specification_m (w I) (w U) (w A) (w Q) (.bvar (.there .here)) (.bvar .here)) <|
        .forallE .set <| .forallE .set <|
          .imp (specification_m (up (up (w I))) (up (up (w U))) (up (up (w A))) (up (up (w Q)))
            (.bvar (.there .here)) (.bvar .here)) <|
            .conj (.equal (.bvar (.there .here)) (.bvar (.there (.there (.there .here)))))
              (.equal (.bvar .here) (.bvar (.there (.there .here))))

def unique_sentence_m : Sentence ℒ := Metatheory.Formula.forall_close unique_schema_m

theorem unique_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : unique_sentence_m.TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [unique_schema_m, Formula.satisfies, specification_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, up, Term.eval_weakenBound, Term.eval]
  intro hU
  obtain ⟨Y, L, hFamily, hGraph, hOrder⟩ := exists_l (hℳ := hℳ) hU
  refine ⟨Y, L, ⟨hFamily, hGraph, hOrder⟩, ?_⟩
  rintro Z T ⟨hZ, hT, _⟩
  have hEq : Z = Y := SecondOrderQuotient.ext_l hℳ Z Y (fun x => (hZ x).trans (hFamily x).symm)
  subst Z
  exact ⟨rfl, PowerlessRelativeClassRowOrderCanonical.graph_unique_l hT hGraph⟩

theorem unique_derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m unique_sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => unique_models_l hℳ)

#print axioms family_ambient_l
#print axioms exists_l
#print axioms derives_m
#print axioms unique_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRowOrderCanonical
