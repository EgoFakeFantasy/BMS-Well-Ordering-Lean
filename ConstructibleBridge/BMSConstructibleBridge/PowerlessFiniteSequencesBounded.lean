import BMSConstructibleBridge.PowerlessFiniteSequencesSyntax
import BMSConstructibleBridge.PowerlessMapBounded
import BMSConstructibleBridge.SecondOrderAxioms
import Mathlib.Data.Set.Insert

/-! # 母序列集内的有限序列规格的纯 Δ₀ 检查

给定实际完整母集 M = Seq(ω, X) 及 A ⊆ X，用 S 和 M 上的双覆盖检查
表达 S = Seq(ω, A)。长度见证限制到模型内部 ω，不要求外部标准有限。
映射陪域扩大只用同一 Kuratowski 代码的坐标唯一性；其正向证明无需
外延公理，因而规格等价对任意纯结构成立。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteSequencesBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private theorem pair_coordinates_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {a b c d p q : carrier_l 𝒩}
    (hp : pair_l (ℳ := 𝒩) a b p) (hq : pair_l (ℳ := 𝒩) c d q) (h : p = q) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  apply Set.pair_eq_pair_iff.mp
  ext x
  change (x = a ∨ x = b) ↔ (x = c ∨ x = d)
  exact (hp x).symm.trans (h ▸ hq x)

private theorem ordered_coordinates_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {a b c d p : carrier_l 𝒩}
    (hp : ordered_l (ℳ := 𝒩) a b p) (hq : ordered_l (ℳ := 𝒩) c d p) :
    a = c ∧ b = d := by
  obtain ⟨s, t, hs, ht, hp⟩ := hp
  obtain ⟨v, w, hv, hw, hq⟩ := hq
  rcases pair_coordinates_l hp hq rfl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have h₃ : a = c := (pair_coordinates_l hs hv h₁).elim And.left And.left
    have h₄ := pair_coordinates_l ht hw h₂
    refine ⟨h₃, h₄.elim And.right ?_⟩
    exact fun h₅ => h₅.2.trans (h₃.symm.trans h₅.1)
  · have h₃ : a = c ∧ a = d := by
      rcases pair_coordinates_l hs hw h₁ with h | h
      · exact h
      · exact h.symm
    have h₄ : b = c := (pair_coordinates_l ht hv h₂).elim And.right And.right
    exact ⟨h₃.1, h₄.trans (h₃.1.symm.trans h₃.2)⟩

/-- 图中所有值已经落在原陪域，扩大陪域不会引入新的图值。 -/
theorem map_subset_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {f n A X : carrier_l 𝒩} (hA : subset_l (ℳ := 𝒩) A X)
    (hf : map_l (ℳ := 𝒩) f n A) : map_l (ℳ := 𝒩) f n X := by
  constructor
  · intro p hp
    obtain ⟨x, y, hx, hy, hxy⟩ := hf.1 p hp
    exact ⟨x, y, hx, hA y hy, hxy⟩
  · intro x hx
    obtain ⟨y, hy, hUnique⟩ := hf.2 x hx
    refine ⟨y, ⟨hA y hy.1, hy.2⟩, ?_⟩
    rintro z ⟨_, p, hp, hxz⟩
    obtain ⟨x', z', _, hz', hx'z'⟩ := hf.1 p hp
    have hz : z = z' := (ordered_coordinates_l hxz hx'z').2
    exact hUnique z ⟨hz.symm ▸ hz', ⟨p, hp, hxz⟩⟩

def sequence_m {Γ Δ : SortContext ℒ} (ω A f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <|
    PowerlessMapBounded.formula_m (up f) (.bvar .here) (up A)

theorem sequence_delta_l {Γ Δ : SortContext ℒ} (ω A f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (sequence_m ω A f) :=
  .bounded_exists ω (PowerlessMapBounded.delta_l _ _ _)

theorem sequence_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (ω A f : Term ℒ Γ Δ .set) :
    (sequence_m ω A f).satisfies η ↔
      PowerlessFiniteSequencesSyntax.sequence_l
        (ℳ := 𝒩) (ω.eval η) (A.eval η) (f.eval η) := by
  simp only [sequence_m, PowerlessFiniteSequencesSyntax.sequence_l,
    Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessMapBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def formula_m {Γ Δ : SortContext ℒ} (ω A M S : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj
    (membershipLevyBound.boundedForall S <|
      .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up M))
        (sequence_m (up ω) (up A) (.bvar .here)))
    (membershipLevyBound.boundedForall M <|
      .imp (sequence_m (up ω) (up A) (.bvar .here))
        (SecondOrderObjectSyntax.member_m (.bvar .here) (up S)))

theorem delta_l {Γ Δ : SortContext ℒ} (ω A M S : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω A M S) :=
  .conj (.bounded_forall S (.conj (.rel _ _) (sequence_delta_l _ _ _)))
    (.bounded_forall M (.imp (sequence_delta_l _ _ _) (.rel _ _)))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A M S : carrier_l 𝒩) : Prop :=
  (∀ f, member_l 𝒩 f S → member_l 𝒩 f M ∧
    PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒩) ω A f) ∧
  (∀ f, member_l 𝒩 f M →
    PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒩) ω A f → member_l 𝒩 f S)

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A M S : Term ℒ Γ Δ .set) :
    (formula_m ω A M S).satisfies η ↔
      holds_l (ω.eval η) (A.eval η) (M.eval η) (S.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    sequence_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 母界只须覆盖全部实际有限赋值，不必自身是完整母序列集。 -/
theorem spec_iff_of_coverage_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {ω A M S : carrier_l 𝒩}
    (hCoverage : ∀ f, PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒩) ω A f →
      member_l 𝒩 f M) :
    holds_l (𝒩 := 𝒩) ω A M S ↔
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω A S := by
  constructor
  · rintro ⟨hForward, hReverse⟩ f
    exact ⟨fun hf => (hForward f hf).2,
      fun hf => hReverse f (hCoverage f hf) hf⟩
  · intro hS
    exact ⟨fun f hf => ⟨hCoverage f ((hS f).mp hf), (hS f).mp hf⟩,
      fun f _ hf => (hS f).mpr hf⟩

theorem spec_iff_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {ω A X M S : carrier_l 𝒩}
    (hM : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω X M)
    (hA : subset_l (ℳ := 𝒩) A X) :
    holds_l (𝒩 := 𝒩) ω A M S ↔
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω A S := by
  have hMother (f : carrier_l 𝒩)
      (hf : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒩) ω A f) :
      member_l 𝒩 f M := by
    obtain ⟨n, hn, hMap⟩ := hf
    exact (hM f).mpr ⟨n, hn, map_subset_l hA hMap⟩
  exact spec_iff_of_coverage_l hMother

def schema_m {Δ : SortContext ℒ} (ω A X M S : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessFiniteSequencesSyntax.spec_m ω X M) <|
    .imp (ThirdOrderTheory.subset_m A X) <|
      .iff (formula_m ω A M S) (PowerlessFiniteSequencesSyntax.spec_m ω A S)

def sentence_m {Δ : SortContext ℒ} (ω A X M S : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω A X M S)

theorem models_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (ω A X M S : Term ℒ [] Δ .set) : (sentence_m ω A X M S).TrueIn 𝒩 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessFiniteSequencesSyntax.spec_formula_l,
    subset_formula_l, formula_l]
  exact fun hM hA => spec_iff_l hM hA

theorem derives_m {Δ : SortContext ℒ} (ω A X M S : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m ω A X M S)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ _ => models_l ω A X M S)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteSequencesBounded
