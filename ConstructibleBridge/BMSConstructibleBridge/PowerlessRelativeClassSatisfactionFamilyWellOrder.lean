import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionRows
import BMSConstructibleBridge.PowerlessRelativeClassOmegaWellOrder
import BMSConstructibleBridge.PowerlessRelativeClassSequenceWellOrder
import BMSConstructibleBridge.PowerlessRelativeClassLexicographicWellOrder

/-! # 全部内部码与参数表示的 Sat 子集族良序

内部码按 ω 的隶属序比较，参数按全有限序列的长度优先序比较。
其积良序给每个相同子集唯一最小表示，再由实际逆图拉回良序。
正式出口在原 Z₂，并保留子集族的全部内部码规格。R 是给定关系；
接到完整 Sat 及原 Def 的等价需要单独证明，不能从图存在推断该等价。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionFamilyWellOrder

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassEnumerationWellOrder (wellOrder_m)
open PowerlessRelativeClassSatisfactionRows (query_m query_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up (up t)))

def slice_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω A S e R p Z : carrier_l ℳ₀) : Prop :=
  ∀ x, member_l ℳ₀ x Z ↔ member_l ℳ₀ x A ∧ query_l ω A S e R p x

def slice_m {Γ Δ : SortContext ℒ} (ω A S e R p Z : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (membershipLevyBound.boundedForall Z <|
    .conj (member_m (.bvar .here) (up A))
      (query_m (up ω) (up A) (up S) (up e) (up R) (up p) (.bvar .here))) <|
    membershipLevyBound.boundedForall A <|
      .imp (query_m (up ω) (up A) (up S) (up e) (up R) (up p) (.bvar .here))
        (member_m (.bvar .here) (up Z))

theorem slice_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω A S e R p Z : Term ℒ Γ Δ .set) :
    (slice_m ω A S e R p Z).satisfies η ↔
      slice_l (ω.eval η) (A.eval η) (S.eval η) (e.eval η) (R.eval η) (p.eval η) (Z.eval η) := by
  simp only [slice_m, slice_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessRelativeClassSatisfactionRows.query_formula_l, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  constructor
  · rintro ⟨hSubset, hCover⟩ x
    exact ⟨hSubset x, fun hx => hCover x hx.1 hx.2⟩
  · intro hRead
    exact ⟨fun x hx => (hRead x).mp hx, fun x hx hQuery => (hRead x).mpr ⟨hx, hQuery⟩⟩

def family_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω A S e R Y : carrier_l ℳ₀) : Prop :=
  ∀ Z, member_l ℳ₀ Z Y ↔ ∃ c f p, member_l ℳ₀ c ω ∧ member_l ℳ₀ f S ∧
    ordered_l c f p ∧ slice_l ω A S e R p Z

def family_m {Γ Δ : SortContext ℒ} (ω A S e R Y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up Y)) <|
    membershipLevyBound.boundedExists (up ω) <|
      membershipLevyBound.boundedExists (up (up S)) <| .existsE .set <|
        .conj (ordered_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
          (slice_m (up₄ ω) (up₄ A) (up₄ S) (up₄ e) (up₄ R) (.bvar .here)
            (.bvar (.there (.there (.there .here)))))

theorem family_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω A S e R Y : Term ℒ Γ Δ .set) :
    (family_m ω A S e R Y).satisfies η ↔
      family_l (ω.eval η) (A.eval η) (S.eval η) (e.eval η) (R.eval η) (Y.eval η) := by
  simp only [family_m, family_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    ordered_formula_l, slice_formula_l, member_m, Arguments.eval,
    up₄, up, Term.eval_weakenBound, Term.eval]
  apply forall_congr'
  intro Z
  apply iff_congr Iff.rfl
  exact ⟨fun ⟨c, hc, f, hf, p, h⟩ => ⟨c, f, p, hc, hf, h⟩,
    fun ⟨c, f, p, hc, hf, h⟩ => ⟨c, hc, f, hf, p, h⟩⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

theorem exists_l {ω A P : type_l hℳ B}
    (hω : omega_l (ℳ := ClassModel) ω) (hP : wellOrder_l (ℳ := ClassModel) A P)
    (e R : type_l hℳ B) :
    ∃ S Y L : type_l hℳ B, PowerlessFiniteSequencesSyntax.spec_l (ℳ := ClassModel) ω A S ∧
      family_l (ℳ₀ := ClassModel) ω A S e R Y ∧ wellOrder_l (ℳ := ClassModel) Y L := by
  obtain ⟨S, T, hS, hT, _⟩ := PowerlessRelativeClassSequenceWellOrder.exists_l hω hP
  obtain ⟨N, hN, _⟩ := PowerlessRelativeClassOmegaWellOrder.exists_l hω
  obtain ⟨I, K, hI, hK, _⟩ := PowerlessRelativeClassLexicographicWellOrder.exists_l hN hT
  obtain ⟨Q, hQ⟩ := PowerlessRelativeClassSatisfactionRows.exists_l (hBase := hBase) ω A S e R I
  obtain ⟨Y, F, hF, hOnto, _, hRange⟩ := PowerlessRelativeClassRowFamily.exists_l (hBase := hBase) I A Q
  obtain ⟨J, hJ, hInject, _⟩ := PowerlessRelativeClassWellOrderSection.exists_l hF hK hOnto
  obtain ⟨L, hL, _⟩ := PowerlessRelativeClassWellOrderPullback.exists_l hJ hInject hK
  have hSlice (p Z : type_l hℳ B) (hp : mem_l hℳ p.val I.val) :
      PowerlessRelativeClassRowFamily.row_l (ℳ₀ := ClassModel) A Q p Z ↔
        slice_l (ℳ₀ := ClassModel) ω A S e R p Z := by
    have hPoint (x : type_l hℳ B) :
        (mem_l hℳ x.val A.val ∧ value_l (ℳ := ClassModel) Q p x) ↔
          (mem_l hℳ x.val A.val ∧ query_l (ℳ₀ := ClassModel) ω A S e R p x) := by
      apply and_congr_right
      intro hx
      exact (hQ p x).trans ⟨fun h => h.2.2, fun h => ⟨hp, hx, h⟩⟩
    constructor
    · intro h x
      exact (h x).trans (hPoint x)
    · intro h x
      exact (h x).trans (hPoint x).symm
  refine ⟨S, Y, L, hS, ?_, hL⟩
  intro Z
  constructor
  · intro hZ
    obtain ⟨p, hp, hRow⟩ := (hRange Z).mp hZ
    obtain ⟨c, f, hc, hf, hPair⟩ := (hI p).mp hp
    exact ⟨c, f, p, hc, hf, hPair, (hSlice p Z hp).mp hRow⟩
  · rintro ⟨c, f, p, hc, hf, hPair, hSliceZ⟩
    have hp := (hI p).mpr ⟨c, f, hc, hf, hPair⟩
    exact (hRange Z).mpr ⟨p, hp, (hSlice p Z hp).mpr hSliceZ⟩

def specification_m {Γ Δ : SortContext ℒ}
    (ω A e R S Y L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessFiniteSequencesSyntax.spec_m ω A S) <|
    .conj (family_m ω A S e R Y) (wellOrder_m Y L)

theorem specification_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω A e R S Y L : Term ℒ Γ Δ .set) :
    (specification_m ω A e R S Y L).satisfies η ↔
      PowerlessFiniteSequencesSyntax.spec_l (ω.eval η) (A.eval η) (S.eval η) ∧
        family_l (ω.eval η) (A.eval η) (S.eval η) (e.eval η) (R.eval η) (Y.eval η) ∧
          wellOrder_l (Y.eval η) (L.eval η) := by
  simp only [specification_m, Formula.satisfies, PowerlessFiniteSequencesSyntax.spec_formula_l,
    family_formula_l, PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l]

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let A : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let P : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let e : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let R : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (wellOrder_m A P) <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      specification_m (up₃ ω) (up₃ A) (up₃ e) (up₃ R)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    specification_formula_l, up₃, up, Term.eval_weakenBound, Term.eval]
  exact fun hω hP => exists_l (hBase := hBase) hω hP _ _

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionFamilyWellOrder
