import BMSConstructibleBridge.PowerlessFiniteEvaluationRelation
import BMSConstructibleBridge.PowerlessFiniteEvaluationEquations

/-! # 集合求值关系的实际逻辑方程

由全部原商输入上的图规格把稳定查询换成集合关系取值。NAND 的两个
子码由构造子正文保证属于 ω；量词更新由全有限赋值集保证新赋值在图域。
保留这两项界限，不能只用类内坐标上的条件对应替换所有递归调用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationRelationEquations

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open PowerlessFormulaConstructor (constructor_l constructor_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

def exists_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω A G f i b : carrier_l 𝒩) : Prop :=
  ∃ m, member_l 𝒩 m ω ∧ map_l f m A ∧ member_l 𝒩 i m ∧
    ∃ a, member_l 𝒩 a A ∧ ∃ g, map_l g m A ∧ PowerlessAssignmentUpdate.update_l f i a g ∧ value_l G b g

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def exists_m {Γ Δ : SortContext ℒ} (ω A G f i b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up t))
  .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up ω)) <|
    .conj (SecondOrderObjectSyntax.map_m (up f) (.bvar .here) (up A)) <|
      .conj (SecondOrderObjectSyntax.member_m (up i) (.bvar .here)) <|
        .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up A))) <|
          .existsE .set <| .conj (SecondOrderObjectSyntax.map_m (.bvar .here) (.bvar (.there (.there .here))) (w A)) <|
            .conj (PowerlessAssignmentUpdate.update_m (w f) (w i) (.bvar (.there .here)) (.bvar .here))
              (SecondOrderObjectSyntax.value_m (w G) (w b) (.bvar .here))

theorem exists_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A G f i b : Term ℒ Γ Δ .set) :
    (exists_m ω A G f i b).satisfies η ↔ exists_l (ω.eval η) (A.eval η) (G.eval η) (f.eval η) (i.eval η) (b.eval η) := by
  simp only [exists_m, exists_l, Formula.satisfies, map_formula_l, value_formula_l,
    PowerlessAssignmentUpdate.update_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {C ω e N T A S t₁ t₂ t₃ Q G n f : carrier_l 𝒩}

theorem read_l (hG : PowerlessFiniteEvaluationRelation.spec_l C ω e N T A S t₁ t₂ t₃ Q G)
    (hn : member_l 𝒩 n ω) (hf : member_l 𝒩 f S) :
    value_l G n f ↔ PowerlessFiniteEvaluationQuery.holds_l C ω e N T A S t₁ t₂ t₃ Q n f := by
  simpa only [hn, hf, true_and] using hG n f

theorem equation_l (hG : PowerlessFiniteEvaluationRelation.spec_l C ω e N T A S t₁ t₂ t₃ Q G)
    (hn : member_l 𝒩 n ω) {P : Prop}
    (h : PowerlessFiniteEvaluationQuery.holds_l C ω e N T A S t₁ t₂ t₃ Q n f ↔ member_l 𝒩 f S ∧ P) :
    value_l G n f ↔ member_l 𝒩 f S ∧ P :=
  ⟨fun hValue => h.mp ((hG n f).mp hValue).2.2,
    fun hValue => (hG n f).mpr ⟨hn, hValue.1, h.mpr hValue⟩⟩

theorem exists_congr_l (hG : PowerlessFiniteEvaluationRelation.spec_l C ω e N T A S t₁ t₂ t₃ Q G)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω A S) {i b : carrier_l 𝒩} (hb : member_l 𝒩 b ω) :
    PowerlessFiniteEvaluationClause.exists_l C ω e N T A S t₁ t₂ t₃ Q f i b ↔ exists_l ω A G f i b := by
  constructor
  · rintro ⟨m, hm, hf, hi, a, ha, g, hg, hUpdate, hQuery⟩
    exact ⟨m, hm, hf, hi, a, ha, g, hg, hUpdate,
      (read_l hG hb ((hS g).mpr ⟨m, hm, hg⟩)).mpr hQuery⟩
  · rintro ⟨m, hm, hf, hi, a, ha, g, hg, hUpdate, hValue⟩
    exact ⟨m, hm, hf, hi, a, ha, g, hg, hUpdate,
      (read_l hG hb ((hS g).mpr ⟨m, hm, hg⟩)).mp hValue⟩

def equations_l (ω e T A S t₁ t₂ t₃ G : carrier_l 𝒩) : Prop :=
  ∀ n, member_l 𝒩 n ω → ∀ f a b,
    (constructor_l ω e T e a b n → (value_l G n f ↔ member_l 𝒩 f S ∧ PowerlessEvaluationClause.member_l f a b)) ∧
    (constructor_l ω e T t₁ a b n → (value_l G n f ↔ member_l 𝒩 f S ∧ PowerlessEvaluationClause.equal_l f a b)) ∧
    (constructor_l ω e T t₂ a b n → (value_l G n f ↔ member_l 𝒩 f S ∧ ¬(value_l G a f ∧ value_l G b f))) ∧
    (constructor_l ω e T t₃ a b n → (value_l G n f ↔ member_l 𝒩 f S ∧ exists_l ω A G f a b))

theorem equations_of_query_l (hG : PowerlessFiniteEvaluationRelation.spec_l C ω e N T A S t₁ t₂ t₃ Q G)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω A S)
    (hQ : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω C Q)
    (hEquation : PowerlessFiniteEvaluationEquations.equations_l C ω e N T A S t₁ t₂ t₃) :
    equations_l ω e T A S t₁ t₂ t₃ G := by
  intro n hn f a b
  have hFour := hEquation Q hQ n hn f a b
  refine ⟨fun h => equation_l hG hn (hFour.1 h), fun h => equation_l hG hn (hFour.2.1 h), ?_, ?_⟩
  · intro h
    refine (equation_l hG hn (hFour.2.2.1 h)).trans (and_congr_right fun hf => ?_)
    exact not_congr (and_congr (read_l hG h.1 hf).symm (read_l hG h.2.1 hf).symm)
  · intro h
    exact (equation_l hG hn (hFour.2.2.2 h)).trans
      (and_congr Iff.rfl (exists_congr_l hG hS h.2.1))

def equations_m {Γ Δ : SortContext ℒ} (ω e T A S t₁ t₂ t₃ G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
  membershipLevyBound.boundedForall ω <| .forallE .set <| .forallE .set <| .forallE .set <|
    let n : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
    let f : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let a : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let b : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
    let query (k : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set) := SecondOrderObjectSyntax.value_m (w G) k f
    let branch (t : Term ℒ Γ Δ .set) (φ : Formula ℒ (.set :: .set :: .set :: .set :: Γ) Δ) :=
      .imp (constructor_m (w ω) (w e) (w T) (w t) a b n)
        (.iff (query n) (.conj (SecondOrderObjectSyntax.member_m f (w S)) φ))
    .conj (branch e (PowerlessEvaluationClause.member_m f a b)) <|
      .conj (branch t₁ (PowerlessEvaluationClause.equal_m f a b)) <|
        .conj (branch t₂ (.neg (.conj (query a) (query b)))) (branch t₃ (exists_m (w ω) (w A) (w G) f a b))

theorem equations_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ)
    (ω e T A S t₁ t₂ t₃ G : Term ℒ Γ Δ .set) :
    (equations_m ω e T A S t₁ t₂ t₃ G).satisfies η ↔ equations_l (ω.eval η) (e.eval η) (T.eval η)
      (A.eval η) (S.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (G.eval η) := by
  simp only [equations_m, equations_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessFormulaConstructor.constructor_formula_l, value_formula_l,
    PowerlessEvaluationClause.member_formula_l, PowerlessEvaluationClause.equal_formula_l, exists_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q G : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessFiniteEvaluationRelation.spec_m C ω e N T A S t₁ t₂ t₃ Q G) <|
    .imp (PowerlessFiniteSequencesSyntax.spec_m ω A S) <|
      .imp (PowerlessFiniteSequencesSyntax.spec_m ω C Q) <|
        .imp (PowerlessFiniteEvaluationEquations.equations_m C ω e N T A S t₁ t₂ t₃)
          (equations_m ω e T A S t₁ t₂ t₃ G)

def sentence_m {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q G : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m C ω e N T A S t₁ t₂ t₃ Q G)

theorem models_l {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q G : Term ℒ [] Δ .set) :
    (sentence_m C ω e N T A S t₁ t₂ t₃ Q G).TrueIn 𝒩 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessFiniteEvaluationRelation.spec_formula_l,
    PowerlessFiniteSequencesSyntax.spec_formula_l, PowerlessFiniteEvaluationEquations.equations_formula_l,
    equations_formula_l]
  exact fun hG hS hQ hEquation => equations_of_query_l hG hS hQ hEquation

theorem derives_m {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q G : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m C ω e N T A S t₁ t₂ t₃ Q G)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ _ => models_l C ω e N T A S t₁ t₂ t₃ Q G)

#print axioms equations_of_query_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationRelationEquations
