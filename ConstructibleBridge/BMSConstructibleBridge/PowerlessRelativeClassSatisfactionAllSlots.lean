import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionFamilyWellOrder

/-! # 全部内部自由槽位的 Sat 子集族良序

先取 I = ω × Seq(A)，再取 ω × I 作为统一表示空间。所有槽、公式码和
赋值共用同一行族界，不收集逐槽构造的子集族，也不选择任意表示。
这里 R 仍是给定关系；完整 Sat 与原五标签 Def 的连接分别另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlots

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassEnumerationWellOrder (wellOrder_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up (up t)))

def query_m {Γ Δ : SortContext ℒ} (ω A S I R t x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up I) <|
    .conj (PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here) (up (up t)))
      (PowerlessRelativeClassSatisfactionRows.query_m (up (up ω)) (up (up A)) (up (up S))
        (.bvar (.there .here)) (up (up R)) (.bvar .here) (up (up x)))

theorem query_delta_l {Γ Δ : SortContext ℒ} (ω A S I R t x : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (query_m ω A S I R t x) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
    (PowerlessRelativeClassSatisfactionRows.query_delta_l _ _ _ _ _ _ _)))

def query_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω A S I R t x : carrier_l ℳ₀) : Prop :=
  ∃ e p, member_l ℳ₀ e ω ∧ member_l ℳ₀ p I ∧ ordered_l e p t ∧
    PowerlessRelativeClassSatisfactionRows.query_l ω A S e R p x

theorem query_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω A S I R t x : Term ℒ Γ Δ .set) :
    (query_m ω A S I R t x).satisfies η ↔
      query_l (ω.eval η) (A.eval η) (S.eval η) (I.eval η) (R.eval η) (t.eval η) (x.eval η) := by
  simp only [query_m, query_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessPairBounded.ordered_formula_l, PowerlessRelativeClassSatisfactionRows.query_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨e, he, p, hp, h⟩ => ⟨e, p, he, hp, h⟩,
    fun ⟨e, p, he, hp, h⟩ => ⟨e, he, p, hp, h⟩⟩

def family_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω A S I R Y : carrier_l ℳ₀) : Prop :=
  ∀ Z, member_l ℳ₀ Z Y ↔ ∃ e p, member_l ℳ₀ e ω ∧ member_l ℳ₀ p I ∧
    PowerlessRelativeClassSatisfactionFamilyWellOrder.slice_l ω A S e R p Z

def family_m {Γ Δ : SortContext ℒ} (ω A S I R Y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up Y)) <|
    membershipLevyBound.boundedExists (up ω) <|
      membershipLevyBound.boundedExists (up (up I)) <|
        PowerlessRelativeClassSatisfactionFamilyWellOrder.slice_m
          (up (up (up ω))) (up (up (up A))) (up (up (up S)))
          (.bvar (.there .here)) (up (up (up R))) (.bvar .here) (.bvar (.there (.there .here)))

theorem family_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω A S I R Y : Term ℒ Γ Δ .set) :
    (family_m ω A S I R Y).satisfies η ↔
      family_l (ω.eval η) (A.eval η) (S.eval η) (I.eval η) (R.eval η) (Y.eval η) := by
  simp only [family_m, family_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessRelativeClassSatisfactionFamilyWellOrder.slice_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  apply forall_congr'
  intro Z
  apply iff_congr Iff.rfl
  exact ⟨fun ⟨e, he, p, hp, h⟩ => ⟨e, p, he, hp, h⟩,
    fun ⟨e, p, he, hp, h⟩ => ⟨e, he, p, hp, h⟩⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

private theorem coordinates_l {e p e' p' t : type_l hℳ B}
    (ht : ordered_l (ℳ := ClassModel) e p t) (ht' : ordered_l (ℳ := ClassModel) e' p' t) :
    e' = e ∧ p' = p := by
  have h := (SecondOrderPairObjects.ordered_eq_l hℳ
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l e' p' t).mp ht')
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l e p t).mp ht)).mp rfl
  exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩

theorem read_l {ω A S I R t e p x : type_l hℳ B}
    (he : mem_l hℳ e.val ω.val) (hp : mem_l hℳ p.val I.val)
    (ht : ordered_l (ℳ := ClassModel) e p t) :
    query_l (ℳ₀ := ClassModel) ω A S I R t x ↔
      PowerlessRelativeClassSatisfactionRows.query_l (ℳ₀ := ClassModel) ω A S e R p x := by
  constructor
  · rintro ⟨e', p', _, _, ht', hQuery⟩
    obtain ⟨hE, hP⟩ := coordinates_l ht ht'
    subst e'
    subst p'
    exact hQuery
  · exact fun h => ⟨e, p, he, hp, ht, h⟩

theorem exists_l {ω A P : type_l hℳ B}
    (hω : omega_l (ℳ := ClassModel) ω) (hP : wellOrder_l (ℳ := ClassModel) A P)
    (R : type_l hℳ B) :
    ∃ S I Y L : type_l hℳ B, PowerlessFiniteSequencesSyntax.spec_l (ℳ := ClassModel) ω A S ∧
      (∀ p, mem_l hℳ p.val I.val ↔ ∃ c f : type_l hℳ B,
        mem_l hℳ c.val ω.val ∧ mem_l hℳ f.val S.val ∧ ordered_l (ℳ := ClassModel) c f p) ∧
      family_l (ℳ₀ := ClassModel) ω A S I R Y ∧ wellOrder_l (ℳ := ClassModel) Y L := by
  obtain ⟨S, T, hS, hT, _⟩ := PowerlessRelativeClassSequenceWellOrder.exists_l hω hP
  obtain ⟨N, hN, _⟩ := PowerlessRelativeClassOmegaWellOrder.exists_l hω
  obtain ⟨I, K, hI, hK, _⟩ := PowerlessRelativeClassLexicographicWellOrder.exists_l hN hT
  obtain ⟨J, U, hJ, hU, _⟩ := PowerlessRelativeClassLexicographicWellOrder.exists_l hN hK
  let η : Env ClassModel [] [.set, .set, .set, .set, .set] :=
    (((((Env.empty).pushFree R).pushFree I).pushFree S).pushFree A).pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] := query_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar .here) (.fvar (.there .here))
  obtain ⟨Q, hQ⟩ := PowerlessRelativeClassRelationalGraph.exists_l
    (φ := φ) (query_delta_l _ _ _ _ _ _ _) η J A
  have hRead (t x : type_l hℳ B) : value_l (ℳ := ClassModel) Q t x ↔
      mem_l hℳ t.val J.val ∧ mem_l hℳ x.val A.val ∧ query_l (ℳ₀ := ClassModel) ω A S I R t x :=
    (hQ t x).trans (and_congr Iff.rfl (and_congr Iff.rfl (query_formula_l _ _ _ _ _ _ _ _)))
  obtain ⟨Y, F, hF, hOnto, _, hRange⟩ := PowerlessRelativeClassRowFamily.exists_l (hBase := hBase) J A Q
  obtain ⟨G, hG, hInject, _⟩ := PowerlessRelativeClassWellOrderSection.exists_l hF hU hOnto
  obtain ⟨L, hL, _⟩ := PowerlessRelativeClassWellOrderPullback.exists_l hG hInject hU
  have hSlice {t e p : type_l hℳ B} (he : mem_l hℳ e.val ω.val) (hp : mem_l hℳ p.val I.val)
      (ht : ordered_l (ℳ := ClassModel) e p t) (Z : type_l hℳ B) :
      PowerlessRelativeClassRowFamily.row_l (ℳ₀ := ClassModel) A Q t Z ↔
        PowerlessRelativeClassSatisfactionFamilyWellOrder.slice_l (ℳ₀ := ClassModel) ω A S e R p Z := by
    have htJ := (hJ t).mpr ⟨e, p, he, hp, ht⟩
    have hPoint (x : type_l hℳ B) :
        (mem_l hℳ x.val A.val ∧ value_l (ℳ := ClassModel) Q t x) ↔
          (mem_l hℳ x.val A.val ∧ PowerlessRelativeClassSatisfactionRows.query_l
            (ℳ₀ := ClassModel) ω A S e R p x) := by
      apply and_congr_right
      intro hx
      exact (hRead t x).trans ⟨fun h => (read_l he hp ht).mp h.2.2,
        fun h => ⟨htJ, hx, (read_l he hp ht).mpr h⟩⟩
    constructor
    · intro h x
      exact (h x).trans (hPoint x)
    · intro h x
      exact (h x).trans (hPoint x).symm
  refine ⟨S, I, Y, L, hS, hI, ?_, hL⟩
  intro Z
  constructor
  · intro hZ
    obtain ⟨t, ht, hRow⟩ := (hRange Z).mp hZ
    obtain ⟨e, p, he, hp, hPair⟩ := (hJ t).mp ht
    exact ⟨e, p, he, hp, (hSlice he hp hPair Z).mp hRow⟩
  · rintro ⟨e, p, he, hp, hSliceZ⟩
    obtain ⟨t, ht⟩ := SecondOrderPairObjects.ordered_exists_l hℳ e.val p.val
    let t' : type_l hℳ B := ⟨t, PowerlessRelativeClassPair.ordered_l hℳ hBase e.property p.property ht⟩
    have ht' := (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) e p t').mpr ht
    exact (hRange Z).mpr ⟨t', (hJ t').mpr ⟨e, p, he, hp, ht'⟩,
      (hSlice he hp ht' Z).mpr hSliceZ⟩

def specification_m {Γ Δ : SortContext ℒ} (ω A R S I Y L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessFiniteSequencesSyntax.spec_m ω A S) <|
    .conj (.forallE .set <| .iff (member_m (.bvar .here) (up I))
      (PowerlessRelativeClassProduct.body_m (up ω) (up S) (.bvar .here))) <|
      .conj (family_m ω A S I R Y) (wellOrder_m Y L)

theorem specification_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω A R S I Y L : Term ℒ Γ Δ .set) :
    (specification_m ω A R S I Y L).satisfies η ↔
      PowerlessFiniteSequencesSyntax.spec_l (ω.eval η) (A.eval η) (S.eval η) ∧
        (∀ p, member_l ℳ₀ p (I.eval η) ↔ ∃ c f, member_l ℳ₀ c (ω.eval η) ∧
          member_l ℳ₀ f (S.eval η) ∧ ordered_l (ℳ := ℳ₀) c f p) ∧
        family_l (ω.eval η) (A.eval η) (S.eval η) (I.eval η) (R.eval η) (Y.eval η) ∧
          wellOrder_l (Y.eval η) (L.eval η) := by
  simp only [specification_m, Formula.satisfies, PowerlessFiniteSequencesSyntax.spec_formula_l,
    PowerlessRelativeClassProduct.body_formula_l, family_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let A : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let P : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let R : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (wellOrder_m A P) <|
    .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
      specification_m (up₄ ω) (up₄ A) (up₄ R) (.bvar (.there (.there (.there .here))))
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    specification_formula_l, up₄, up, Term.eval_weakenBound, Term.eval]
  exact fun hω hP => exists_l (hBase := hBase) hω hP _

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlots
