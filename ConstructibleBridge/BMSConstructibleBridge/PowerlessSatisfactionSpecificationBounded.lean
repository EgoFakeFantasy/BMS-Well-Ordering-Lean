import BMSConstructibleBridge.PowerlessSatisfactionDomainBounded
import BMSConstructibleBridge.PowerlessSatisfactionExistentialBounded
import BMSConstructibleBridge.PowerlessFormulaConstructorBounded
import BMSConstructibleBridge.PowerlessEvaluationAtomicBounded

/-! # 原完整 Sat 规格的纯 Δ₀ 检查器

定义域从图自身取得坐标界；零码检查在完整赋值集内；四个原方程
保留相同合法长度以及每个子码的有效性守卫。数值序列集 N 和母集
赋值集 S 分开，存在分支直接读取 R。双向等价不要求 R 无垃圾，
不假定完整源理论，也不把条件式检查器当作 Sat 的存在或层界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionSpecificationBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderObjectSyntax (member_m)
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₅ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up (up (up t))))

def clauses_m {Γ Δ : SortContext ℒ}
    (ω A e N T S t₁ t₂ t₃ F R c L f a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let query (x : Term ℒ Γ Δ .set) := PowerlessValueBounded.formula_m R x f
  let valid (x : Term ℒ Γ Δ .set) := PowerlessValueBounded.formula_m F x L
  let branch (t : Term ℒ Γ Δ .set) (p q φ : Formula ℒ Γ Δ) :=
    .imp (PowerlessFormulaConstructorBounded.formula_m ω e N T t a b c) <|
      .imp p <| .imp q <| .iff (query c) φ
  .conj (branch e (member_m a L) (member_m b L) (PowerlessEvaluationAtomicBounded.member_m A f a b)) <|
    .conj (branch t₁ (member_m a L) (member_m b L) (PowerlessEvaluationAtomicBounded.equal_m A f a b)) <|
      .conj (branch t₂ (valid a) (valid b) (.neg (.conj (query a) (query b))))
        (branch t₃ (member_m a L) (valid b) (PowerlessSatisfactionExistentialBounded.formula_m ω A S R f a b))

private theorem branch_delta_l {Γ Δ : SortContext ℒ}
    (ω e N T t a b c R f : Term ℒ Γ Δ .set) {p q φ : Formula ℒ Γ Δ}
    (hp : Formula.IsDelta0 membershipLevyBound p) (hq : Formula.IsDelta0 membershipLevyBound q)
    (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    Formula.IsDelta0 membershipLevyBound (.imp
      (PowerlessFormulaConstructorBounded.formula_m ω e N T t a b c)
      (.imp p (.imp q (.iff (PowerlessValueBounded.formula_m R c f) φ)))) :=
  .imp (PowerlessFormulaConstructorBounded.delta_l _ _ _ _ _ _ _ _) <|
    .imp hp <| .imp hq <| .iff (PowerlessValueBounded.delta_l _ _ _) hφ

theorem clauses_delta_l {Γ Δ : SortContext ℒ}
    (ω A e N T S t₁ t₂ t₃ F R c L f a b : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (clauses_m ω A e N T S t₁ t₂ t₃ F R c L f a b) :=
  .conj (branch_delta_l _ _ _ _ _ _ _ _ _ _ (.rel _ _) (.rel _ _)
    (PowerlessEvaluationAtomicBounded.member_delta_l _ _ _ _)) <|
    .conj (branch_delta_l _ _ _ _ _ _ _ _ _ _ (.rel _ _) (.rel _ _)
      (PowerlessEvaluationAtomicBounded.equal_delta_l _ _ _ _)) <|
      .conj (branch_delta_l _ _ _ _ _ _ _ _ _ _ (PowerlessValueBounded.delta_l _ _ _)
        (PowerlessValueBounded.delta_l _ _ _) (.neg (.conj
          (PowerlessValueBounded.delta_l _ _ _) (PowerlessValueBounded.delta_l _ _ _))))
        (branch_delta_l _ _ _ _ _ _ _ _ _ _ (.rel _ _) (PowerlessValueBounded.delta_l _ _ _)
          (PowerlessSatisfactionExistentialBounded.delta_l _ _ _ _ _ _ _))

def clauses_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A e N T S t₁ t₂ t₃ F R c L f a b : carrier_l 𝒩) : Prop :=
  (PowerlessFormulaConstructorBounded.holds_l ω e N T e a b c → member_l 𝒩 a L → member_l 𝒩 b L →
    (value_l R c f ↔ PowerlessEvaluationAtomicBounded.member_l A f a b)) ∧
  (PowerlessFormulaConstructorBounded.holds_l ω e N T t₁ a b c → member_l 𝒩 a L → member_l 𝒩 b L →
    (value_l R c f ↔ PowerlessEvaluationAtomicBounded.equal_l A f a b)) ∧
  (PowerlessFormulaConstructorBounded.holds_l ω e N T t₂ a b c → value_l F a L → value_l F b L →
    (value_l R c f ↔ ¬(value_l R a f ∧ value_l R b f))) ∧
  (PowerlessFormulaConstructorBounded.holds_l ω e N T t₃ a b c → member_l 𝒩 a L → value_l F b L →
    (value_l R c f ↔ PowerlessSatisfactionExistentialBounded.holds_l ω A S R f a b))

theorem clauses_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A e N T S t₁ t₂ t₃ F R c L f a b : Term ℒ Γ Δ .set) :
    (clauses_m ω A e N T S t₁ t₂ t₃ F R c L f a b).satisfies η ↔
      clauses_l (ω.eval η) (A.eval η) (e.eval η) (N.eval η) (T.eval η) (S.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (F.eval η) (R.eval η)
        (c.eval η) (L.eval η) (f.eval η) (a.eval η) (b.eval η) := by
  simp only [clauses_m, clauses_l, Formula.satisfies, PowerlessFormulaConstructorBounded.formula_l,
    PowerlessValueBounded.formula_l, PowerlessEvaluationAtomicBounded.member_formula_l,
    PowerlessEvaluationAtomicBounded.equal_formula_l, PowerlessSatisfactionExistentialBounded.formula_l,
    member_m, member_l, Arguments.eval]

def equations_m {Γ Δ : SortContext ℒ}
    (ω A e N T S t₁ t₂ t₃ F R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall ω <|
    membershipLevyBound.boundedForall (up ω) <|
      membershipLevyBound.boundedForall (up (up S)) <|
        membershipLevyBound.boundedForall (up (up (up ω))) <|
          membershipLevyBound.boundedForall (up (up (up (up ω)))) <|
            let c : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
              .bvar (.there (.there (.there (.there .here))))
            let L := .bvar (.there (.there (.there .here)))
            let f := .bvar (.there (.there .here))
            let a := .bvar (.there .here)
            let b := .bvar .here
            .imp (PowerlessMapBounded.formula_m f L (up₅ A)) <|
              clauses_m (up₅ ω) (up₅ A) (up₅ e) (up₅ N) (up₅ T) (up₅ S)
                (up₅ t₁) (up₅ t₂) (up₅ t₃) (up₅ F) (up₅ R) c L f a b

theorem equations_delta_l {Γ Δ : SortContext ℒ}
    (ω A e N T S t₁ t₂ t₃ F R : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (equations_m ω A e N T S t₁ t₂ t₃ F R) :=
  .bounded_forall ω <| .bounded_forall (up ω) <| .bounded_forall (up (up S)) <|
    .bounded_forall (up (up (up ω))) <| .bounded_forall (up (up (up (up ω)))) <|
      .imp (PowerlessMapBounded.delta_l _ _ _) (clauses_delta_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

def equations_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A e N T S t₁ t₂ t₃ F R : carrier_l 𝒩) : Prop :=
  ∀ c, member_l 𝒩 c ω → ∀ L, member_l 𝒩 L ω → ∀ f, member_l 𝒩 f S →
    ∀ a, member_l 𝒩 a ω → ∀ b, member_l 𝒩 b ω → map_l f L A →
      clauses_l ω A e N T S t₁ t₂ t₃ F R c L f a b

theorem equations_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A e N T S t₁ t₂ t₃ F R : Term ℒ Γ Δ .set) :
    (equations_m ω A e N T S t₁ t₂ t₃ F R).satisfies η ↔
      equations_l (ω.eval η) (A.eval η) (e.eval η) (N.eval η) (T.eval η) (S.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (F.eval η) (R.eval η) := by
  simp only [equations_m, equations_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessMapBounded.formula_l, clauses_formula_l,
    Arguments.eval, up₅, up, Term.eval_weakenBound, Term.eval]
  rfl

def spec_m {Γ Δ : SortContext ℒ} (ω A e N T S t₁ t₂ t₃ F R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessSatisfactionDomainBounded.domain_m ω A F R) <|
    .conj (PowerlessSatisfactionDomainBounded.zero_m S e R) (equations_m ω A e N T S t₁ t₂ t₃ F R)

theorem delta_l {Γ Δ : SortContext ℒ} (ω A e N T S t₁ t₂ t₃ F R : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (spec_m ω A e N T S t₁ t₂ t₃ F R) :=
  .conj (PowerlessSatisfactionDomainBounded.domain_delta_l _ _ _ _) <|
    .conj (PowerlessSatisfactionDomainBounded.zero_delta_l _ _ _) (equations_delta_l _ _ _ _ _ _ _ _ _ _ _)

def spec_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω A e N T S t₁ t₂ t₃ F R : carrier_l 𝒩) : Prop :=
  PowerlessSatisfactionDomainBounded.domain_l ω A F R ∧
    PowerlessSatisfactionDomainBounded.zero_l S e R ∧ equations_l ω A e N T S t₁ t₂ t₃ F R

theorem spec_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A e N T S t₁ t₂ t₃ F R : Term ℒ Γ Δ .set) :
    (spec_m ω A e N T S t₁ t₂ t₃ F R).satisfies η ↔
      spec_l (ω.eval η) (A.eval η) (e.eval η) (N.eval η) (T.eval η) (S.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (F.eval η) (R.eval η) := by
  simp only [spec_m, spec_l, Formula.satisfies, PowerlessSatisfactionDomainBounded.domain_formula_l,
    PowerlessSatisfactionDomainBounded.zero_formula_l, equations_formula_l]

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

private theorem clauses_iff_l (K : source_coding_l hℳ) {A N T S t₁ t₂ t₃ F R c L f a b : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N)
    (hT : map_l (ℳ := 𝒱) T K.omega K.omega)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega A S) (hMap : map_l (ℳ := 𝒱) f L A) :
    clauses_l (𝒩 := 𝒱) K.omega A (zero_l K) N T S t₁ t₂ t₃ F R c L f a b ↔
      ((PowerlessFormulaConstructor.constructor_l (ℳ := 𝒱) K.omega (zero_l K) T (zero_l K) a b c →
        mem_l hℳ a L → mem_l hℳ b L →
          (value_l (ℳ := 𝒱) R c f ↔ PowerlessEvaluationClause.member_l (ℳ := 𝒱) f a b)) ∧
      (PowerlessFormulaConstructor.constructor_l (ℳ := 𝒱) K.omega (zero_l K) T t₁ a b c →
        mem_l hℳ a L → mem_l hℳ b L →
          (value_l (ℳ := 𝒱) R c f ↔ PowerlessEvaluationClause.equal_l (ℳ := 𝒱) f a b)) ∧
      (PowerlessFormulaConstructor.constructor_l (ℳ := 𝒱) K.omega (zero_l K) T t₂ a b c →
        value_l (ℳ := 𝒱) F a L → value_l (ℳ := 𝒱) F b L →
          (value_l (ℳ := 𝒱) R c f ↔ ¬(value_l (ℳ := 𝒱) R a f ∧ value_l (ℳ := 𝒱) R b f))) ∧
      (PowerlessFormulaConstructor.constructor_l (ℳ := 𝒱) K.omega (zero_l K) T t₃ a b c →
        mem_l hℳ a L → value_l (ℳ := 𝒱) F b L →
          (value_l (ℳ := 𝒱) R c f ↔
            PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := 𝒱) K.omega A R f a b))) := by
  unfold clauses_l
  rw [PowerlessFormulaConstructorBounded.constructor_iff_l K hN hT,
    PowerlessFormulaConstructorBounded.constructor_iff_l K hN hT,
    PowerlessFormulaConstructorBounded.constructor_iff_l K hN hT,
    PowerlessFormulaConstructorBounded.constructor_iff_l K hN hT,
    PowerlessEvaluationAtomicBounded.member_iff_l hℳ hMap,
    PowerlessEvaluationAtomicBounded.equal_iff_l hℳ hMap,
    PowerlessSatisfactionExistentialBounded.exists_iff_l hℳ hS]
  rfl

theorem equations_iff_l (K : source_coding_l hℳ) {A N T S t₁ t₂ t₃ F R : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N)
    (hT : map_l (ℳ := 𝒱) T K.omega K.omega)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega A S) :
    equations_l (𝒩 := 𝒱) K.omega A (zero_l K) N T S t₁ t₂ t₃ F R ↔
      PowerlessSatisfactionSpecification.equations_l (𝒩 := 𝒱) K.omega A (zero_l K) t₁ t₂ t₃ T F R := by
  constructor
  · intro h c L f hc hL hMap a b
    have hfS := (hS f).mpr ⟨L, hL, hMap⟩
    have hClauses (hCtor : PowerlessFormulaConstructor.constructor_l (ℳ := 𝒱)
        K.omega (zero_l K) T (zero_l K) a b c) :=
      (clauses_iff_l K hN hT hS hMap).mp (h c hc L hL f hfS a hCtor.1 b hCtor.2.1 hMap)
    refine ⟨fun hCtor => (hClauses hCtor).1 hCtor, ?_, ?_, ?_⟩
    · intro hCtor
      exact ((clauses_iff_l K hN hT hS hMap).mp
        (h c hc L hL f hfS a hCtor.1 b hCtor.2.1 hMap)).2.1 hCtor
    · intro hCtor
      exact ((clauses_iff_l K hN hT hS hMap).mp
        (h c hc L hL f hfS a hCtor.1 b hCtor.2.1 hMap)).2.2.1 hCtor
    · intro hCtor
      exact ((clauses_iff_l K hN hT hS hMap).mp
        (h c hc L hL f hfS a hCtor.1 b hCtor.2.1 hMap)).2.2.2 hCtor
  · intro h c hc L hL f _ a _ b _ hMap
    exact (clauses_iff_l K hN hT hS hMap).mpr (h c L f hc hL hMap a b)

theorem spec_iff_l (K : source_coding_l hℳ) {A N T S t₁ t₂ t₃ F R : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N)
    (hT : map_l (ℳ := 𝒱) T K.omega K.omega)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega A S) :
    spec_l (𝒩 := 𝒱) K.omega A (zero_l K) N T S t₁ t₂ t₃ F R ↔
      PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒱) K.omega A (zero_l K) t₁ t₂ t₃ T F R := by
  constructor
  · rintro ⟨hDomain, hZero, hEquations⟩
    have hDomain' := PowerlessSatisfactionDomainBounded.domain_iff_l.mp hDomain
    exact ⟨hDomain', (PowerlessSatisfactionDomainBounded.zero_iff_l hDomain' hS).mp hZero,
      (equations_iff_l K hN hT hS).mp hEquations⟩
  · rintro ⟨hDomain, hZero, hEquations⟩
    exact ⟨PowerlessSatisfactionDomainBounded.domain_iff_l.mpr hDomain,
      (PowerlessSatisfactionDomainBounded.zero_iff_l hDomain hS).mpr hZero,
      (equations_iff_l K hN hT hS).mpr hEquations⟩

theorem guarded_iff_l {ω A e N T S t₁ t₂ t₃ F R : type_l hℳ}
    (hω : omega_l (ℳ := 𝒱) ω) (he : ∀ x, ¬mem_l hℳ x e)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) ω ω N)
    (hT : map_l (ℳ := 𝒱) T ω ω)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) ω A S) :
    spec_l (𝒩 := 𝒱) ω A e N T S t₁ t₂ t₃ F R ↔
      PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒱) ω A e t₁ t₂ t₃ T F R := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have heEq : e = zero_l K := SecondOrderQuotient.ext_l hℳ _ _
    (fun x => iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  rw [hωEq] at hN hT hS ⊢
  rw [heEq]
  exact spec_iff_l K hN hT hS

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionSpecificationBounded
