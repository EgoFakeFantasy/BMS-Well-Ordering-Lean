import BMSConstructibleBridge.PowerlessRelationBounded
import BMSConstructibleBridge.PowerlessFiniteSequencesBounded
import BMSConstructibleBridge.PowerlessMemberDefImageBounded
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionIndexCanonical

/-! # 规范满足指标包的纯 Δ₀ 检查

对象语言为纯隶属 ℒ。C 只为全部实际有限序列提供覆盖界；其余见证在
调用端另行有界。序列集及两次积均作双向检查，N、T、K、U 同时具有
干净成员和指定域上的全部坐标读数。正文不含良序或 Class 量词。

任意纯结构先读成有界规格；在原 Z₂ 商及真实序列覆盖界下，恢复全部
raw 坐标上的四张关系读数。独立 raw 规格明确排除辅助图的垃圾成员，
所以只单向恢复旧规范指标包：旧包仅要求辅助 N、T、K 的逐值读数，
并不能反向推出这三张图的干净成员。本文件不构造 Class 良序历史、
枚举族或共同层界，原对象推导由后续历史调用端装配。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalIndexBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderObjectSyntax (member_m)
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def omega_m {Γ Δ : SortContext ℒ} (ω N : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelationBounded.clean_m N ω ω) <|
    membershipLevyBound.boundedForall ω <|
      membershipLevyBound.boundedForall (up ω) <|
        .iff (PowerlessValueBounded.formula_m (up₂ N) (.bvar (.there .here)) (.bvar .here))
          (member_m (.bvar (.there .here)) (.bvar .here))

theorem omega_delta_l {Γ Δ : SortContext ℒ} (ω N : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (omega_m ω N) :=
  .conj (PowerlessRelationBounded.clean_delta_l _ _ _)
    (.bounded_forall _ (.bounded_forall _ (.iff (PowerlessValueBounded.delta_l _ _ _) (.rel _ _))))

def omega_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω N : carrier_l 𝒩) : Prop :=
  PowerlessRelationBounded.clean_l (𝒩 := 𝒩) N ω ω ∧
    ∀ x, member_l 𝒩 x ω → ∀ y, member_l 𝒩 y ω →
      (value_l (ℳ := 𝒩) N x y ↔ member_l 𝒩 x y)

theorem omega_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω N : Term ℒ Γ Δ .set) :
    (omega_m ω N).satisfies η ↔ omega_holds_l (ω.eval η) (N.eval η) := by
  simp only [omega_m, omega_holds_l, Formula.satisfies,
    PowerlessRelationBounded.clean_formula_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, PowerlessValueBounded.formula_l,
    member_m, Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def shortlex_m {Γ Δ : SortContext ℒ} (ω A P S T : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelationBounded.clean_m T S S) <|
    membershipLevyBound.boundedForall S <|
      membershipLevyBound.boundedForall (up S) <|
        .iff (PowerlessValueBounded.formula_m (up₂ T) (.bvar (.there .here)) (.bvar .here))
          (PowerlessRelativeClassSequenceOrderGraph.shortlex_m
            (up₂ ω) (up₂ A) (up₂ P) (.bvar (.there .here)) (.bvar .here))

theorem shortlex_delta_l {Γ Δ : SortContext ℒ} (ω A P S T : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (shortlex_m ω A P S T) :=
  .conj (PowerlessRelationBounded.clean_delta_l _ _ _)
    (.bounded_forall _ (.bounded_forall _ (.iff (PowerlessValueBounded.delta_l _ _ _)
      (PowerlessRelativeClassSequenceOrderGraph.shortlex_delta_l _ _ _ _ _))))

def shortlex_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A P S T : carrier_l 𝒩) : Prop :=
  PowerlessRelationBounded.clean_l (𝒩 := 𝒩) T S S ∧
    ∀ f, member_l 𝒩 f S → ∀ g, member_l 𝒩 g S →
      (value_l (ℳ := 𝒩) T f g ↔
        PowerlessRelativeClassSequenceOrderGraph.shortlex_l (ℳ₀ := 𝒩) ω A P f g)

theorem shortlex_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A P S T : Term ℒ Γ Δ .set) :
    (shortlex_m ω A P S T).satisfies η ↔
      shortlex_holds_l (ω.eval η) (A.eval η) (P.eval η) (S.eval η) (T.eval η) := by
  simp only [shortlex_m, shortlex_holds_l, Formula.satisfies,
    PowerlessRelationBounded.clean_formula_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, PowerlessValueBounded.formula_l,
    PowerlessRelativeClassSequenceOrderGraph.shortlex_formula_l,
    Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- D 是实际积载体；两个关系参数 R、Q 不作良序假设。 -/
def lex_m {Γ Δ : SortContext ℒ} (X Y R Q D L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelationBounded.clean_m L D D) <|
    membershipLevyBound.boundedForall D <|
      membershipLevyBound.boundedForall (up D) <|
        .iff (PowerlessValueBounded.formula_m (up₂ L) (.bvar (.there .here)) (.bvar .here))
          (PowerlessRelativeClassLexicographicWellOrder.lex_m
            (up₂ X) (up₂ Y) (up₂ R) (up₂ Q) (.bvar (.there .here)) (.bvar .here))

theorem lex_delta_l {Γ Δ : SortContext ℒ} (X Y R Q D L : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (lex_m X Y R Q D L) :=
  .conj (PowerlessRelationBounded.clean_delta_l _ _ _)
    (.bounded_forall _ (.bounded_forall _ (.iff (PowerlessValueBounded.delta_l _ _ _)
      (PowerlessRelativeClassLexicographicWellOrder.lex_delta_l _ _ _ _ _ _))))

def lex_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (X Y R Q D L : carrier_l 𝒩) : Prop :=
  PowerlessRelationBounded.clean_l (𝒩 := 𝒩) L D D ∧
    ∀ p, member_l 𝒩 p D → ∀ q, member_l 𝒩 q D →
      (value_l (ℳ := 𝒩) L p q ↔
        PowerlessRelativeClassLexicographicWellOrder.lex_l (ℳ₀ := 𝒩) X Y R Q p q)

theorem lex_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (X Y R Q D L : Term ℒ Γ Δ .set) :
    (lex_m X Y R Q D L).satisfies η ↔ lex_holds_l
      (X.eval η) (Y.eval η) (R.eval η) (Q.eval η) (D.eval η) (L.eval η) := by
  simp only [lex_m, lex_holds_l, Formula.satisfies,
    PowerlessRelationBounded.clean_formula_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, PowerlessValueBounded.formula_l,
    PowerlessRelativeClassLexicographicWellOrder.lex_formula_l,
    Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def formula_m {Γ Δ : SortContext ℒ}
    (C ω A P S I J N T K U : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessFiniteSequencesBounded.formula_m ω A C S) <|
    .conj (PowerlessMemberDefImageBounded.product_m ω S I) <|
      .conj (PowerlessMemberDefImageBounded.product_m ω I J) <|
        .conj (omega_m ω N) <| .conj (shortlex_m ω A P S T) <|
          .conj (lex_m ω S N T I K) (lex_m ω I N K J U)

theorem delta_l {Γ Δ : SortContext ℒ} (C ω A P S I J N T K U : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m C ω A P S I J N T K U) :=
  .conj (PowerlessFiniteSequencesBounded.delta_l _ _ _ _)
    (.conj (PowerlessMemberDefImageBounded.product_delta_l _ _ _)
      (.conj (PowerlessMemberDefImageBounded.product_delta_l _ _ _)
        (.conj (omega_delta_l _ _) (.conj (shortlex_delta_l _ _ _ _ _)
          (.conj (lex_delta_l _ _ _ _ _ _) (lex_delta_l _ _ _ _ _ _))))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (C ω A P S I J N T K U : carrier_l 𝒩) : Prop :=
  PowerlessFiniteSequencesBounded.holds_l (𝒩 := 𝒩) ω A C S ∧
    PowerlessMemberDefImageBounded.product_holds_l (𝒩 := 𝒩) ω S I ∧
      PowerlessMemberDefImageBounded.product_holds_l (𝒩 := 𝒩) ω I J ∧
        omega_holds_l (𝒩 := 𝒩) ω N ∧ shortlex_holds_l (𝒩 := 𝒩) ω A P S T ∧
          lex_holds_l (𝒩 := 𝒩) ω S N T I K ∧ lex_holds_l (𝒩 := 𝒩) ω I N K J U

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (C ω A P S I J N T K U : Term ℒ Γ Δ .set) :
    (formula_m C ω A P S I J N T K U).satisfies η ↔ holds_l
      (C.eval η) (ω.eval η) (A.eval η) (P.eval η) (S.eval η) (I.eval η) (J.eval η)
      (N.eval η) (T.eval η) (K.eval η) (U.eval η) := by
  simp only [formula_m, holds_l, Formula.satisfies, PowerlessFiniteSequencesBounded.formula_l,
    PowerlessMemberDefImageBounded.product_formula_l, omega_formula_l, shortlex_formula_l, lex_formula_l]

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

/-- 四张辅助关系都有干净成员，且读数量化全部原 raw 坐标。 -/
structure rawspec_l (ω A P S I J N T K U : Raw) : Prop where
  sequence : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) ω A S
  indexProduct : PowerlessRelativeClassSatisfactionIndexCanonical.product_l (ℳ₀ := 𝒱) ω S I
  slotProduct : PowerlessRelativeClassSatisfactionIndexCanonical.product_l (ℳ₀ := 𝒱) ω I J
  numberClean : PowerlessRelationBounded.clean_l (𝒩 := 𝒱) N ω ω
  shortlexClean : PowerlessRelationBounded.clean_l (𝒩 := 𝒱) T S S
  firstLexClean : PowerlessRelationBounded.clean_l (𝒩 := 𝒱) K I I
  finalLexClean : PowerlessRelationBounded.clean_l (𝒩 := 𝒱) U J J
  numberRead : ∀ x y, value_l (ℳ := 𝒱) N x y ↔
    mem_l hℳ x ω ∧ mem_l hℳ y ω ∧ mem_l hℳ x y
  shortlexRead : ∀ f g, value_l (ℳ := 𝒱) T f g ↔
    PowerlessRelativeClassSequenceOrderGraph.shortlex_l (ℳ₀ := 𝒱) ω A P f g
  firstLexRead : ∀ p q, value_l (ℳ := 𝒱) K p q ↔
    PowerlessRelativeClassLexicographicWellOrder.lex_l (ℳ₀ := 𝒱) ω S N T p q
  finalLexRead : ∀ p q, value_l (ℳ := 𝒱) U p q ↔
    PowerlessRelativeClassLexicographicWellOrder.lex_l (ℳ₀ := 𝒱) ω I N K p q

private theorem product_iff_l (X Y D : Raw) :
    PowerlessMemberDefImageBounded.product_holds_l (𝒩 := 𝒱) X Y D ↔
      PowerlessRelativeClassSatisfactionIndexCanonical.product_l (ℳ₀ := 𝒱) X Y D := by
  constructor
  · rintro ⟨hClean, hCover⟩ p
    constructor
    · intro hp
      obtain ⟨x, hx, y, hy, hxy⟩ := hClean p hp
      exact ⟨x, y, hx, hy, hxy⟩
    · rintro ⟨x, y, hx, hy, hxy⟩
      obtain ⟨q, hq, hxq⟩ := hCover x hx y hy
      exact (SecondOrderPairObjects.ordered_unique_l hℳ hxq hxy) ▸ hq
  · intro hProduct
    constructor
    · intro p hp
      obtain ⟨x, y, hx, hy, hxy⟩ := (hProduct p).mp hp
      exact ⟨x, hx, y, hy, hxy⟩
    · intro x hx y hy
      obtain ⟨p, hxy⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
      exact ⟨p, (hProduct p).mpr ⟨x, y, hx, hy, hxy⟩, hxy⟩

private theorem clean_value_coordinates_l {R X Y x y : Raw}
    (hClean : PowerlessRelationBounded.clean_l (𝒩 := 𝒱) R X Y)
    (hValue : value_l (ℳ := 𝒱) R x y) : mem_l hℳ x X ∧ mem_l hℳ y Y := by
  obtain ⟨p, hp, hxy⟩ := hValue
  obtain ⟨a, b, ha, hb, hab⟩ := hClean p hp
  obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxy hab).mp rfl
  exact ⟨ha, hb⟩

private theorem full_read_l {R X Y : Raw} {ψ : Raw → Raw → Prop}
    (hClean : PowerlessRelationBounded.clean_l (𝒩 := 𝒱) R X Y)
    (hRead : ∀ x, mem_l hℳ x X → ∀ y, mem_l hℳ y Y →
      (value_l (ℳ := 𝒱) R x y ↔ ψ x y))
    (hSupport : ∀ x y, ψ x y → mem_l hℳ x X ∧ mem_l hℳ y Y) :
    ∀ x y, value_l (ℳ := 𝒱) R x y ↔ ψ x y := by
  intro x y
  constructor
  · intro hxy
    have hBounds := clean_value_coordinates_l hClean hxy
    exact (hRead x hBounds.1 y hBounds.2).mp hxy
  · intro hxy
    have hBounds := hSupport x y hxy
    exact (hRead x hBounds.1 y hBounds.2).mpr hxy

/-- 真实序列覆盖界恢复精确独立规格，不要求 C 是完整序列集或属于 Class。 -/
theorem reading_l {C ω A P S I J N T K U : Raw}
    (hCoverage : ∀ f, PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω A f → mem_l hℳ f C) :
    holds_l (𝒩 := 𝒱) C ω A P S I J N T K U ↔ rawspec_l ω A P S I J N T K U := by
  constructor
  · rintro ⟨hS₀, hI₀, hJ₀, hN, hT, hK, hU⟩
    have hS := (PowerlessFiniteSequencesBounded.spec_iff_of_coverage_l hCoverage).mp hS₀
    have hI := (product_iff_l ω S I).mp hI₀
    have hJ := (product_iff_l ω I J).mp hJ₀
    refine ⟨hS, hI, hJ, hN.1, hT.1, hK.1, hU.1, ?_, ?_, ?_, ?_⟩
    · apply full_read_l hN.1
      · intro x hx y hy
        exact (hN.2 x hx y hy).trans
          ⟨fun hxy => ⟨hx, hy, hxy⟩, fun hxy => hxy.2.2⟩
      · exact fun _ _ hxy => ⟨hxy.1, hxy.2.1⟩
    · apply full_read_l hT.1 hT.2
      rintro f g ⟨n, m, hn, hm, hf, hg, _⟩
      exact ⟨(hS f).mpr ⟨n, hn, hf⟩, (hS g).mpr ⟨m, hm, hg⟩⟩
    · apply full_read_l hK.1 hK.2
      rintro p q ⟨x, y, a, b, hx, hy, ha, hb, hp, hq, _⟩
      exact ⟨(hI p).mpr ⟨x, y, hx, hy, hp⟩, (hI q).mpr ⟨a, b, ha, hb, hq⟩⟩
    · apply full_read_l hU.1 hU.2
      rintro p q ⟨x, y, a, b, hx, hy, ha, hb, hp, hq, _⟩
      exact ⟨(hJ p).mpr ⟨x, y, hx, hy, hp⟩, (hJ q).mpr ⟨a, b, ha, hb, hq⟩⟩
  · intro h
    refine ⟨(PowerlessFiniteSequencesBounded.spec_iff_of_coverage_l hCoverage).mpr h.sequence,
      (product_iff_l ω S I).mpr h.indexProduct, (product_iff_l ω I J).mpr h.slotProduct,
      ⟨h.numberClean, ?_⟩, ⟨h.shortlexClean, ?_⟩,
      ⟨h.firstLexClean, ?_⟩, ⟨h.finalLexClean, ?_⟩⟩
    · intro x hx y hy
      exact (h.numberRead x y).trans ⟨fun hxy => hxy.2.2, fun hxy => ⟨hx, hy, hxy⟩⟩
    · exact fun f _ g _ => h.shortlexRead f g
    · exact fun p _ q _ => h.firstLexRead p q
    · exact fun p _ q _ => h.finalLexRead p q

/-- 取同一 N、T、K 的实际见证，恢复旧包而不增加良序或 Class 假设。 -/
theorem canonical_spec_l {C ω A P S I J N T K U : Raw}
    (hCoverage : ∀ f, PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω A f → mem_l hℳ f C)
    (h : holds_l (𝒩 := 𝒱) C ω A P S I J N T K U) :
    PowerlessRelativeClassSatisfactionIndexCanonical.spec_l (ℳ₀ := 𝒱) ω A P S I J U := by
  have hRaw := (reading_l hCoverage).mp h
  refine ⟨hRaw.sequence, hRaw.indexProduct, hRaw.slotProduct, ?_,
    N, T, K, hRaw.numberRead, hRaw.shortlexRead, hRaw.firstLexRead, hRaw.finalLexRead⟩
  intro p hp
  obtain ⟨x, y, _, _, hxy⟩ := hRaw.finalLexClean p hp
  exact ⟨x, y, hxy⟩

theorem formula_reading_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (C ω A P S I J N T K U : Term ℒ Γ Δ .set)
    (hCoverage : ∀ f, PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) (ω.eval η) (A.eval η) f →
      mem_l hℳ f (C.eval η)) :
    (formula_m C ω A P S I J N T K U).satisfies η ↔ rawspec_l
      (ω.eval η) (A.eval η) (P.eval η) (S.eval η) (I.eval η) (J.eval η)
      (N.eval η) (T.eval η) (K.eval η) (U.eval η) :=
  (formula_l η C ω A P S I J N T K U).trans (reading_l hCoverage)

#print axioms delta_l
#print axioms formula_l
#print axioms reading_l
#print axioms canonical_spec_l
#print axioms formula_reading_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalIndexBounded
