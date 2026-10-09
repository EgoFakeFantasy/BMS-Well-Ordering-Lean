import BMSConstructibleBridge.PowerlessRelativeClassWellOrderSection
import BMSConstructibleBridge.SecondOrderMemberDefBoundedSlice

/-! # 实际关系的全部行子集及统一表示图

给定内部指标集 I、母集 A 和实际关系 Q，每行由 Δ₀ 分离取得。
把 I、A、Q 放入同一传递层 C 后，全部行同时属于 Def(C)，故统一
行图及其精确值域能在类内构造。该共同界由固定层的定义子集证明给出，
没有使用一般 Collection；指标可以是全部内部公式码与参数序列。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRowFamily

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassEnumerationWellOrder (wellOrder_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def row_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (A Q i Z : carrier_l ℳ₀) : Prop :=
  ∀ x, member_l ℳ₀ x Z ↔ member_l ℳ₀ x A ∧ value_l Q i x

def row_m {Γ Δ : SortContext ℒ} (A Q i Z : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (membershipLevyBound.boundedForall Z <|
    .conj (member_m (.bvar .here) (up A))
      (PowerlessValueBounded.formula_m (up Q) (up i) (.bvar .here))) <|
    membershipLevyBound.boundedForall A <|
      .imp (PowerlessValueBounded.formula_m (up Q) (up i) (.bvar .here))
        (member_m (.bvar .here) (up Z))

theorem row_delta_l {Γ Δ : SortContext ℒ} (A Q i Z : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (row_m A Q i Z) :=
  .conj (.bounded_forall _ (.conj (.rel _ _) (PowerlessValueBounded.delta_l _ _ _)))
    (.bounded_forall _ (.imp (PowerlessValueBounded.delta_l _ _ _) (.rel _ _)))

theorem row_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (A Q i Z : Term ℒ Γ Δ .set) :
    (row_m A Q i Z).satisfies η ↔ row_l (A.eval η) (Q.eval η) (i.eval η) (Z.eval η) := by
  simp only [row_m, row_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  constructor
  · rintro ⟨hSubset, hCover⟩ x
    exact ⟨hSubset x, fun hx => hCover x hx.1 hx.2⟩
  · intro hRead
    exact ⟨fun x hx => (hRead x).mp hx, fun x hx hValue => (hRead x).mpr ⟨hx, hValue⟩⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase

theorem row_exists_l (A Q i : type_l hℳ B) :
    ∃! Z : type_l hℳ B, row_l (ℳ₀ := 𝒩) A Q i Z := by
  let φ : Formula ℒ [] [.set, .set, .set] := PowerlessValueBounded.formula_m
    (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  let η : Env 𝒩 [] [.set, .set] := ((Env.empty).pushFree Q).pushFree i
  obtain ⟨Z, hZ⟩ := PowerlessRelativeClassDeltaSeparation.exists_l
    (φ := φ) (PowerlessValueBounded.delta_l _ _ _) η A
  have hRead : row_l (ℳ₀ := 𝒩) A Q i Z := fun x =>
    (hZ x).trans (and_congr Iff.rfl (PowerlessValueBounded.formula_l (η.pushFree x) _ _ _))
  refine ⟨Z, hRead, ?_⟩
  intro W hW
  apply (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
  intro x
  exact (hW x).trans (hRead x).symm

/-- 全部行共用一个后继层界，不收集各行的独立层见证。 -/
theorem row_bound_l {C D : SecondOrderQuotient.type_l hℳ} {A Q i Z : type_l hℳ B}
    (hDef : SecondOrderMemberDef.spec_l hℳ C D)
    (hTrans : ∀ x, mem_l hℳ x C → ∀ y, mem_l hℳ y x → mem_l hℳ y C)
    (hAC : mem_l hℳ A.val C) (hQC : mem_l hℳ Q.val C) (hiC : mem_l hℳ i.val C)
    (hRow : row_l (ℳ₀ := 𝒩) A Q i Z) : mem_l hℳ Z.val D := by
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set] :=
    (((Env.empty).pushFree Q.val).pushFree i.val).pushFree A.val
  let φ : Formula ℒ [] [.set, .set, .set, .set] :=
    .conj (member_m (.fvar .here) (.fvar (.there .here)))
      (PowerlessValueBounded.formula_m (.fvar (.there (.there (.there .here))))
        (.fvar (.there (.there .here))) (.fvar .here))
  have hφ : Formula.IsDelta0 membershipLevyBound φ :=
    .conj (.rel _ _) (PowerlessValueBounded.delta_l _ _ _)
  have hParams : ∀ s (v : Variable [SetTheory.SetSort.set, .set, .set] s),
      mem_l hℳ (η.freeVal v) C := by
    intro s v
    cases v with
    | here => exact hAC
    | there v => cases v with
      | here => exact hiC
      | there v => cases v with
        | here => exact hQC
        | there v => nomatch v
  have hRaw (x : SecondOrderQuotient.type_l hℳ) : mem_l hℳ x Z.val ↔
      mem_l hℳ x A.val ∧ value_l (ℳ := SecondOrderQuotient.structure_l hℳ) Q.val i.val x := by
    constructor
    · intro hx
      let x' : type_l hℳ B := ⟨x,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Z.property hx⟩
      have h := (hRow x').mp hx
      exact ⟨h.1, (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Q i x').mp h.2⟩
    · rintro ⟨hx, hValue⟩
      let x' : type_l hℳ B := ⟨x,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hx⟩
      exact (hRow x').mpr ⟨hx,
        (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Q i x').mpr hValue⟩
  have hφRead (x : SecondOrderQuotient.type_l hℳ) : φ.satisfies (η.pushFree x) ↔
      mem_l hℳ x A.val ∧ value_l (ℳ := SecondOrderQuotient.structure_l hℳ) Q.val i.val x := by
    simp only [φ, η, Formula.satisfies, member_m, PowerlessValueBounded.formula_l,
      Arguments.eval, Term.eval]
    rfl
  apply SecondOrderMemberDefBoundedSlice.member_l hℳ hDef hTrans hφ η hParams
  intro x
  exact (hRaw x).trans ⟨fun hx => ⟨hTrans A.val hAC x hx.1, (hφRead x).mpr hx⟩,
    fun hx => (hφRead x).mp hx.2⟩

theorem exists_l (I A Q : type_l hℳ B) :
    ∃ Y F : type_l hℳ B, map_l (ℳ := 𝒩) F I Y ∧
      (∀ y : type_l hℳ B, mem_l hℳ y.val Y.val → ∃ i : type_l hℳ B,
        mem_l hℳ i.val I.val ∧ value_l (ℳ := 𝒩) F i y) ∧
      (∀ i y : type_l hℳ B, value_l (ℳ := 𝒩) F i y ↔
        mem_l hℳ i.val I.val ∧ row_l (ℳ₀ := 𝒩) A Q i y) ∧
      (∀ y : type_l hℳ B, mem_l hℳ y.val Y.val ↔
        ∃ i : type_l hℳ B, mem_l hℳ i.val I.val ∧ row_l (ℳ₀ := 𝒩) A Q i y) := by
  let η : Env 𝒩 [] [.set, .set] := ((Env.empty).pushFree Q).pushFree A
  obtain ⟨a, C, hC, hIC, hParams⟩ := PowerlessRelativeClassParameterBounds.exists_l η I
  have hAC : mem_l hℳ A.val C := hParams _ .here
  have hQC : mem_l hℳ Q.val C := hParams _ (.there .here)
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  obtain ⟨b, D, _, hD, hDef⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hC
  let D' : type_l hℳ B := ⟨D, PowerlessRelativeLevelClosure.class_l hℳ hBase hD⟩
  let φ : Formula ℒ [] [.set, .set, .set, .set] := row_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar .here) (.fvar (.there .here))
  have hφ (i y : type_l hℳ B) : φ.satisfies ((η.pushFree y).pushFree i) ↔
      row_l (ℳ₀ := 𝒩) A Q i y := row_formula_l _ _ _ _ _
  obtain ⟨F, hF, hFValue⟩ := PowerlessRelativeClassFunctionRelation.exists_l
    (φ := φ) (row_delta_l _ _ _ _) η I D' (by
      intro i hi
      obtain ⟨Z, hZ, hUnique⟩ := row_exists_l (hBase := hBase) A Q i
      have hZD := row_bound_l hDef hTrans hAC hQC (hTrans I.val hIC i.val hi) hZ
      exact ⟨Z, ⟨hZD, (hφ i Z).mpr hZ⟩,
        fun W hW => hUnique W ((hφ i W).mp hW.2)⟩)
  have hFRead (i y : type_l hℳ B) : value_l (ℳ := 𝒩) F i y ↔
      mem_l hℳ i.val I.val ∧ mem_l hℳ y.val D ∧ row_l (ℳ₀ := 𝒩) A Q i y :=
    (hFValue i y).trans (and_congr Iff.rfl (and_congr Iff.rfl (hφ i y)))
  let ψ : Formula ℒ [] [.set, .set, .set] :=
    membershipLevyBound.boundedExists (.fvar (.there .here))
      (PowerlessValueBounded.formula_m (.fvar (.there (.there .here))) (.bvar .here) (.fvar .here))
  let ξ : Env 𝒩 [] [.set, .set] := ((Env.empty).pushFree F).pushFree I
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassDeltaSeparation.exists_l
    (φ := ψ) (.bounded_exists _ (PowerlessValueBounded.delta_l _ _ _)) ξ D'
  have hYRead (y : type_l hℳ B) : mem_l hℳ y.val Y.val ↔ mem_l hℳ y.val D ∧
      ∃ i : type_l hℳ B, mem_l hℳ i.val I.val ∧ value_l (ℳ := 𝒩) F i y := by
    refine (hY y).trans (and_congr Iff.rfl ?_)
    simp only [ψ, ξ, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
      membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l, Arguments.eval, Term.eval]
    rfl
  have hRead (i y : type_l hℳ B) : value_l (ℳ := 𝒩) F i y ↔
      mem_l hℳ i.val I.val ∧ row_l (ℳ₀ := 𝒩) A Q i y := by
    constructor
    · intro hValue
      have h := (hFRead i y).mp hValue
      exact ⟨h.1, h.2.2⟩
    · rintro ⟨hi, hRow⟩
      exact (hFRead i y).mpr ⟨hi,
        row_bound_l hDef hTrans hAC hQC (hTrans I.val hIC i.val hi) hRow, hRow⟩
  have hMap : map_l (ℳ := 𝒩) F I Y := by
    refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨i, y, hi, hy, hPair⟩ := hF.1 p hp
      exact ⟨i, y, hi, (hYRead y).mpr ⟨hy, i, hi, p, hp, hPair⟩, hPair⟩
    · intro i hi
      obtain ⟨y, ⟨hy, hValue⟩, hUnique⟩ := hF.2 i hi
      exact ⟨y, ⟨(hYRead y).mpr ⟨hy, i, hi, hValue⟩, hValue⟩,
        fun z hz => hUnique z ⟨((hYRead z).mp hz.1).1, hz.2⟩⟩
  refine ⟨Y, F, hMap, fun y hy => ((hYRead y).mp hy).2, hRead, ?_⟩
  intro y
  constructor
  · intro hy
    obtain ⟨i, hi, hValue⟩ := ((hYRead y).mp hy).2
    exact ⟨i, hi, ((hRead i y).mp hValue).2⟩
  · rintro ⟨i, hi, hRow⟩
    exact (hYRead y).mpr ⟨row_bound_l hDef hTrans hAC hQC (hTrans I.val hIC i.val hi) hRow,
      i, hi, (hRead i y).mpr ⟨hi, hRow⟩⟩

def specification_m {Γ Δ : SortContext ℒ} (I A Q Y F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (map_m F I Y) <|
    .conj (PowerlessRelativeClassEnumerationSectionDerives.onto_m F I Y) <|
      .conj (.forallE .set <| .forallE .set <|
        .iff (value_m (up (up F)) (.bvar (.there .here)) (.bvar .here))
          (.conj (member_m (.bvar (.there .here)) (up (up I)))
            (row_m (up (up A)) (up (up Q)) (.bvar (.there .here)) (.bvar .here)))) <|
        .forallE .set <| .iff (member_m (.bvar .here) (up Y)) <|
          .existsE .set <| .conj (member_m (.bvar .here) (up (up I)))
            (row_m (up (up A)) (up (up Q)) (.bvar .here) (.bvar (.there .here)))

theorem specification_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (I A Q Y F : Term ℒ Γ Δ .set) :
    (specification_m I A Q Y F).satisfies η ↔
      map_l (F.eval η) (I.eval η) (Y.eval η) ∧
        (∀ y, member_l ℳ₀ y (Y.eval η) → ∃ i,
          member_l ℳ₀ i (I.eval η) ∧ value_l (F.eval η) i y) ∧
        (∀ i y, value_l (F.eval η) i y ↔ member_l ℳ₀ i (I.eval η) ∧
          row_l (A.eval η) (Q.eval η) i y) ∧
        (∀ y, member_l ℳ₀ y (Y.eval η) ↔ ∃ i, member_l ℳ₀ i (I.eval η) ∧
          row_l (A.eval η) (Q.eval η) i y) := by
  simp only [specification_m, Formula.satisfies, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l, value_formula_l,
    row_formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let I : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let A : Term ℒ [] [.set, .set, .set] .set := .fvar (.there .here)
  let Q : Term ℒ [] [.set, .set, .set] .set := .fvar (.there (.there .here))
  .existsE .set <| .existsE .set <|
    specification_m (up (up I)) (up (up A)) (up (up Q)) (.bvar (.there .here)) (.bvar .here)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, specification_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  exact exists_l (hBase := hBase) _ _ _

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms row_bound_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRowFamily
