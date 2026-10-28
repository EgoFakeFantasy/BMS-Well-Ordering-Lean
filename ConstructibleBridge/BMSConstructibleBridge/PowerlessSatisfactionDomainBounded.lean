import BMSConstructibleBridge.PowerlessSatisfactionSpecification
import BMSConstructibleBridge.PowerlessMapBounded
import BMSConstructibleBridge.PowerlessPairBounded
import BMSConstructibleBridge.PowerlessFiniteSequencesSyntax
import BMSConstructibleBridge.SecondOrderAxioms

/-! # Sat 定义域的无额外前提 Δ₀ 检查

合法有序对的两个坐标均在其自身两层成员中。遍历 R 的这些坐标，
只对合法对触发定义域要求，与原 value 规格在任意纯结构中等价。
没有要求 R 是映射或积子集，也没有禁止原规格允许的垃圾成员。
定义域闭句的图翻译回到原 Z₂ Derives；零码检查缩到完整赋值集时
仍显式消费已经证明的定义域和完整 Seq 规格。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionDomainBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₅ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up (up (up t))))

def domain_m {Γ Δ : SortContext ℒ} (ω A F R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall R <|
    membershipLevyBound.boundedForall (.bvar .here) <|
      membershipLevyBound.boundedForall (.bvar .here) <|
        membershipLevyBound.boundedForall (.bvar (.there (.there .here))) <|
          membershipLevyBound.boundedForall (.bvar .here) <|
            let c : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
              .bvar (.there (.there .here))
            let f := .bvar .here
            let p := .bvar (.there (.there (.there (.there .here))))
            .imp (PowerlessPairBounded.ordered_m c f p) <|
              .conj (member_m c (up₅ ω)) <|
                membershipLevyBound.boundedExists (up₅ ω) <| .conj
                  (PowerlessValueBounded.formula_m (up (up₅ F)) (up c) (.bvar .here))
                  (PowerlessMapBounded.formula_m (up f) (.bvar .here) (up (up₅ A)))

theorem domain_delta_l {Γ Δ : SortContext ℒ} (ω A F R : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (domain_m ω A F R) :=
  .bounded_forall R <| .bounded_forall (.bvar .here) <| .bounded_forall (.bvar .here) <|
    .bounded_forall (.bvar (.there (.there .here))) <| .bounded_forall (.bvar .here) <|
      .imp (PowerlessPairBounded.ordered_delta_l _ _ _) <| .conj (.rel _ _) <|
        .bounded_exists (up₅ ω) <| .conj (PowerlessValueBounded.delta_l _ _ _)
          (PowerlessMapBounded.delta_l _ _ _)

def domain_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω A F R : carrier_l 𝒩) : Prop :=
  ∀ p, member_l 𝒩 p R → ∀ s, member_l 𝒩 s p → ∀ c, member_l 𝒩 c s →
    ∀ t, member_l 𝒩 t p → ∀ f, member_l 𝒩 f t → ordered_l (ℳ := 𝒩) c f p →
      member_l 𝒩 c ω ∧ ∃ L, member_l 𝒩 L ω ∧ value_l (ℳ := 𝒩) F c L ∧ map_l (ℳ := 𝒩) f L A

theorem domain_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A F R : Term ℒ Γ Δ .set) :
    (domain_m ω A F R).satisfies η ↔ domain_l (ω.eval η) (A.eval η) (F.eval η) (R.eval η) := by
  simp only [domain_m, domain_l, Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessPairBounded.ordered_formula_l, PowerlessValueBounded.formula_l,
    PowerlessMapBounded.formula_l, member_m, Arguments.eval, up₅, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 两层坐标界来自每个 value 的实际对见证，不来自额外的图规范前提。 -/
theorem domain_iff_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {ω A F R : carrier_l 𝒩} :
    domain_l ω A F R ↔ PowerlessSatisfactionSpecification.domain_l ω A F R := by
  constructor
  · intro h c f hValue
    obtain ⟨p, hp, s, t, hs, ht, hPair⟩ := hValue
    exact h p hp s ((hPair s).mpr (Or.inl rfl)) c ((hs c).mpr (Or.inl rfl))
      t ((hPair t).mpr (Or.inr rfl)) f ((ht f).mpr (Or.inr rfl)) ⟨s, t, hs, ht, hPair⟩
  · intro h p hp s _ c _ t _ f _ hPair
    exact h c f ⟨p, hp, hPair⟩

def zero_m {Γ Δ : SortContext ℒ} (S e R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall S <| .neg
    (PowerlessValueBounded.formula_m (up R) (up e) (.bvar .here))

theorem zero_delta_l {Γ Δ : SortContext ℒ} (S e R : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (zero_m S e R) :=
  .bounded_forall S (.neg (PowerlessValueBounded.delta_l _ _ _))

def zero_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (S e R : carrier_l 𝒩) : Prop :=
  ∀ f, member_l 𝒩 f S → ¬value_l (ℳ := 𝒩) R e f

theorem zero_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (S e R : Term ℒ Γ Δ .set) :
    (zero_m S e R).satisfies η ↔ zero_l (S.eval η) (e.eval η) (R.eval η) := by
  simp only [zero_m, zero_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem zero_iff_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {ω A F S e R : carrier_l 𝒩}
    (hDomain : PowerlessSatisfactionSpecification.domain_l ω A F R)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω A S) :
    zero_l S e R ↔ PowerlessSatisfactionSpecification.zero_l e R := by
  constructor
  · intro h f hValue
    obtain ⟨_, L, hL, _, hMap⟩ := hDomain e f hValue
    exact h f ((hS f).mpr ⟨L, hL, hMap⟩) hValue
  · intro h f _
    exact h f

def schema_m {Δ : SortContext ℒ} (ω A F R : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .iff (domain_m ω A F R) (PowerlessSatisfactionSpecification.domain_m ω A F R)

def sentence_m {Δ : SortContext ℒ} (ω A F R : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω A F R)

theorem derives_m {Δ : SortContext ℒ} (ω A F R : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω A F R)) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact (domain_formula_l η ω A F R).trans
    (domain_iff_l.trans (PowerlessSatisfactionSpecification.domain_formula_l η ω A F R).symm)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionDomainBounded
