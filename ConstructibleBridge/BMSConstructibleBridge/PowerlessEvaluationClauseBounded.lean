import BMSConstructibleBridge.PowerlessFormulaConstructorBounded
import BMSConstructibleBridge.PowerlessEvaluationAtomicBounded
import BMSConstructibleBridge.PowerlessEvaluationExistentialBounded

/-! # 原局部求值算子的纯 Δ₀ 矩阵

保持原三角配数及隶属、等号、与非、存在四分支。字段限制在 ω，原子值
限制在 A，更新图限制在全有限赋值集 S；数值加法用独立的全有限数值集 N。
原关系等价只使用原 Z₂ 图商及显式规格，不调用完整源理论模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationClauseBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def branch_m {Γ Δ : SortContext ℒ} (ω e N T t n : Term ℒ Γ Δ .set)
    (φ : Formula ℒ (.set :: .set :: Γ) Δ) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := up (up s)
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <| .conj
    (PowerlessFormulaConstructorBounded.formula_m (w ω) (w e) (w N) (w T) (w t)
      (.bvar (.there .here)) (.bvar .here) (w n)) φ

theorem branch_delta_l {Γ Δ : SortContext ℒ} (ω e N T t n : Term ℒ Γ Δ .set)
    {φ : Formula ℒ (.set :: .set :: Γ) Δ} (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    Formula.IsDelta0 membershipLevyBound (branch_m ω e N T t n φ) :=
  .bounded_exists ω (.bounded_exists (up ω)
    (.conj (PowerlessFormulaConstructorBounded.delta_l _ _ _ _ _ _ _ _) hφ))

def formula_m {Γ Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ H n f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := up (up s)
  .disj (branch_m ω e N T e n
    (PowerlessEvaluationAtomicBounded.member_m (w A) (w f) (.bvar (.there .here)) (.bvar .here))) <|
    .disj (branch_m ω e N T t₁ n
      (PowerlessEvaluationAtomicBounded.equal_m (w A) (w f) (.bvar (.there .here)) (.bvar .here))) <|
      .disj (branch_m ω e N T t₂ n <| .neg <| .conj
        (PowerlessEvaluationQueryBounded.formula_m (w H) (.bvar (.there .here)) (w f))
        (PowerlessEvaluationQueryBounded.formula_m (w H) (.bvar .here) (w f)))
        (branch_m ω e N T t₃ n <| PowerlessEvaluationExistentialBounded.formula_m
          (w ω) (w A) (w S) (w H) (w f) (.bvar (.there .here)) (.bvar .here))

theorem delta_l {Γ Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ H n f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e N T A S t₁ t₂ t₃ H n f) :=
  .disj (branch_delta_l _ _ _ _ _ _ (PowerlessEvaluationAtomicBounded.member_delta_l _ _ _ _))
    (.disj (branch_delta_l _ _ _ _ _ _ (PowerlessEvaluationAtomicBounded.equal_delta_l _ _ _ _))
      (.disj (branch_delta_l _ _ _ _ _ _ (.neg (.conj
        (PowerlessEvaluationQueryBounded.delta_l _ _ _) (PowerlessEvaluationQueryBounded.delta_l _ _ _))))
        (branch_delta_l _ _ _ _ _ _ (PowerlessEvaluationExistentialBounded.delta_l _ _ _ _ _ _ _))))

def branch_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e N T t n : carrier_l 𝒩)
    (P : carrier_l 𝒩 → carrier_l 𝒩 → Prop) : Prop :=
  ∃ a, member_l 𝒩 a ω ∧ ∃ b, member_l 𝒩 b ω ∧
    PowerlessFormulaConstructorBounded.holds_l (𝒩 := 𝒩) ω e N T t a b n ∧ P a b

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e N T A S t₁ t₂ t₃ H n f : carrier_l 𝒩) : Prop :=
  branch_l ω e N T e n (PowerlessEvaluationAtomicBounded.member_l A f) ∨
    branch_l ω e N T t₁ n (PowerlessEvaluationAtomicBounded.equal_l A f) ∨
      branch_l ω e N T t₂ n (fun a b =>
        ¬ (PowerlessEvaluationClause.query_l H a f ∧ PowerlessEvaluationClause.query_l H b f)) ∨
        branch_l ω e N T t₃ n (PowerlessEvaluationExistentialBounded.holds_l ω A S H f)

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N T A S t₁ t₂ t₃ H n f : Term ℒ Γ Δ .set) :
    (formula_m ω e N T A S t₁ t₂ t₃ H n f).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (A.eval η) (S.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (H.eval η) (n.eval η) (f.eval η) := by
  simp only [formula_m, branch_m, holds_l, branch_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessFormulaConstructorBounded.formula_l, PowerlessEvaluationAtomicBounded.member_formula_l,
    PowerlessEvaluationAtomicBounded.equal_formula_l, PowerlessEvaluationQueryBounded.formula_l,
    PowerlessEvaluationExistentialBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem branch_iff_l (K : source_coding_l hℳ) {N T t n : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega)
    {P Q : type_l hℳ → type_l hℳ → Prop} (h : ∀ a b, P a b ↔ Q a b) :
    branch_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val N T t n P ↔
      ∃ a b, PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
        K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val T t a b n ∧ Q a b := by
  constructor
  · rintro ⟨a, _, b, _, hc, hP⟩
    exact ⟨a, b, (PowerlessFormulaConstructorBounded.constructor_iff_l K hN hT).mp hc, (h a b).mp hP⟩
  · rintro ⟨a, b, hc, hQ⟩
    exact ⟨a, hc.1, b, hc.2.1,
      (PowerlessFormulaConstructorBounded.constructor_iff_l K hN hT).mpr hc, (h a b).mpr hQ⟩

theorem clause_iff_l (K : source_coding_l hℳ) {N T A S t₁ t₂ t₃ H n f : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega A S)
    (hf : mem_l hℳ f S) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val N T A S t₁ t₂ t₃ H n f ↔
      PowerlessEvaluationClause.clause_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega
        (numberCode_l K (SecondOrderModel.zero_l ℳ)).val T A t₁ t₂ t₃ H n f := by
  obtain ⟨_, _, hMap⟩ := (hS f).mp hf
  unfold holds_l PowerlessEvaluationClause.clause_l
  exact or_congr (branch_iff_l K hN hT (fun _ _ => PowerlessEvaluationAtomicBounded.member_iff_l hℳ hMap))
    (or_congr (branch_iff_l K hN hT (fun _ _ => PowerlessEvaluationAtomicBounded.equal_iff_l hℳ hMap))
      (or_congr (branch_iff_l K hN hT (fun _ _ => Iff.rfl))
        (branch_iff_l K hN hT (fun _ _ => PowerlessEvaluationExistentialBounded.exists_iff_l hℳ hS))))

theorem guarded_iff_l {ω e N T A S t₁ t₂ t₃ H n f : type_l hℳ}
    (hω : omega_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω)
    (he : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) e)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω ω N)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T ω ω)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω A S)
    (hf : mem_l hℳ f S) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) ω e N T A S t₁ t₂ t₃ H n f ↔
      PowerlessEvaluationClause.clause_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω e T A t₁ t₂ t₃ H n f := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have heEq := SecondOrderQuotient.ext_l hℳ _ _ (fun x =>
    iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  rw [hωEq] at hN hT hS ⊢
  rw [heEq]
  exact clause_iff_l K hN hT hS hf

private abbrev context_m : SortContext ℒ :=
  [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set]

/-- 对所有实际赋值的原局部规则等价，不声称统一真值图已经存在。 -/
def schema_m : Formula ℒ [] context_m :=
  let ω : Term ℒ [] context_m .set := .fvar .here
  let e : Term ℒ [] context_m .set := .fvar (.there .here)
  let N : Term ℒ [] context_m .set := .fvar (.there (.there .here))
  let T : Term ℒ [] context_m .set := .fvar (.there (.there (.there .here)))
  let A : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there .here))))
  let S : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let t₁ : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let t₂ : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let t₃ : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let H : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
  let n : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
  let f : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (up e)))) <|
      .imp (PowerlessFiniteSequencesSyntax.spec_m ω ω N) <|
        .imp (SecondOrderObjectSyntax.map_m T ω ω) <|
          .imp (PowerlessFiniteSequencesSyntax.spec_m ω A S) <|
            .imp (SecondOrderObjectSyntax.member_m f S) <|
              .iff (formula_m ω e N T A S t₁ t₂ t₃ H n f)
                (PowerlessEvaluationClause.clause_m ω e T A t₁ t₂ t₃ H n f)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hω he hN hT hS hf
  have hω' := (omega_formula_l η _).mp hω
  have he' : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) (η.2 (.there .here)) := he
  have hN' := (PowerlessFiniteSequencesSyntax.spec_formula_l η _ _ _).mp hN
  have hT' := (map_formula_l η _ _ _).mp hT
  have hS' := (PowerlessFiniteSequencesSyntax.spec_formula_l η _ _ _).mp hS
  refine (formula_l η _ _ _ _ _ _ _ _ _ _ _ _).trans
    (Iff.trans ?_ (PowerlessEvaluationClause.clause_formula_l η _ _ _ _ _ _ _ _ _ _).symm)
  exact guarded_iff_l hω' he' hN' hT' hS' hf

#print axioms delta_l
#print axioms clause_iff_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationClauseBounded
