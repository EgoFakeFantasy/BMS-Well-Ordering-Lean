import BMSConstructibleBridge.PowerlessFiniteEvaluationRelationEquations
import BMSConstructibleBridge.PowerlessFiniteEvaluationZero

/-! # 合法性守卫求值关系的纯对象规格

规格记录实际图的定义域、零码恒假及同一内部赋值长度上的四个条件分支。
所有守卫均写入纯 ℒ 公式，逐环境读数不假定模型满足任何理论。这里只给
规格的语法与语义对应；图存在、规格成立及最终 BMS 目标须另行证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionSpecification

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderObjectSyntax (member_m value_m map_m)
open PowerlessFormulaConstructor (constructor_l constructor_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def domain_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω A F R : carrier_l 𝒩) : Prop :=
  ∀ c f, value_l R c f → member_l 𝒩 c ω ∧
    ∃ L, member_l 𝒩 L ω ∧ value_l F c L ∧ map_l f L A

def domain_m {Γ Δ : SortContext ℒ} (ω A F R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  .forallE .set <| .forallE .set <|
    .imp (value_m (w R) (.bvar (.there .here)) (.bvar .here)) <|
      .conj (member_m (.bvar (.there .here)) (w ω)) <|
        .existsE .set <| .conj (member_m (.bvar .here) (up (w ω))) <|
          .conj (value_m (up (w F)) (.bvar (.there (.there .here))) (.bvar .here))
            (map_m (.bvar (.there .here)) (.bvar .here) (up (w A)))

theorem domain_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A F R : Term ℒ Γ Δ .set) :
    (domain_m ω A F R).satisfies η ↔ domain_l (ω.eval η) (A.eval η) (F.eval η) (R.eval η) := by
  simp only [domain_m, domain_l, Formula.satisfies, value_formula_l, map_formula_l,
    member_m, member_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def zero_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (e R : carrier_l 𝒩) : Prop :=
  ∀ f, ¬value_l R e f

def zero_m {Γ Δ : SortContext ℒ} (e R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessFiniteEvaluationZero.formula_m e R

theorem zero_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (e R : Term ℒ Γ Δ .set) :
    (zero_m e R).satisfies η ↔ zero_l (e.eval η) (R.eval η) :=
  PowerlessFiniteEvaluationZero.formula_l η e R

def equations_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A e t₁ t₂ t₃ T F R : carrier_l 𝒩) : Prop :=
  ∀ c L f, member_l 𝒩 c ω → member_l 𝒩 L ω → map_l f L A → ∀ a b,
    (constructor_l ω e T e a b c → member_l 𝒩 a L → member_l 𝒩 b L →
      (value_l R c f ↔ PowerlessEvaluationClause.member_l f a b)) ∧
    (constructor_l ω e T t₁ a b c → member_l 𝒩 a L → member_l 𝒩 b L →
      (value_l R c f ↔ PowerlessEvaluationClause.equal_l f a b)) ∧
    (constructor_l ω e T t₂ a b c → value_l F a L → value_l F b L →
      (value_l R c f ↔ ¬(value_l R a f ∧ value_l R b f))) ∧
    (constructor_l ω e T t₃ a b c → member_l 𝒩 a L → value_l F b L →
      (value_l R c f ↔ PowerlessFiniteEvaluationRelationEquations.exists_l ω A R f a b))

def equations_m {Γ Δ : SortContext ℒ} (ω A e t₁ t₂ t₃ T F R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up t))
  .forallE .set <| .forallE .set <| .forallE .set <|
    let c : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let L : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let f : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
    .imp (member_m c (w ω)) <| .imp (member_m L (w ω)) <| .imp (map_m f L (w A)) <|
      .forallE .set <| .forallE .set <|
        let v (t : Term ℒ Γ Δ .set) := up (up (w t))
        let c' := up (up c)
        let L' := up (up L)
        let f' := up (up f)
        let a : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
        let b : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
        let query (k : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set) := value_m (v R) k f'
        let valid (k : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set) := value_m (v F) k L'
        let branch (t : Term ℒ Γ Δ .set)
            (p q φ : Formula ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ) :=
          .imp (constructor_m (v ω) (v e) (v T) (v t) a b c') <|
            .imp p <| .imp q <| .iff (query c') φ
        .conj (branch e (member_m a L') (member_m b L') (PowerlessEvaluationClause.member_m f' a b)) <|
          .conj (branch t₁ (member_m a L') (member_m b L') (PowerlessEvaluationClause.equal_m f' a b)) <|
            .conj (branch t₂ (valid a) (valid b) (.neg (.conj (query a) (query b))))
              (branch t₃ (member_m a L') (valid b)
                (PowerlessFiniteEvaluationRelationEquations.exists_m (v ω) (v A) (v R) f' a b))

theorem equations_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A e t₁ t₂ t₃ T F R : Term ℒ Γ Δ .set) :
    (equations_m ω A e t₁ t₂ t₃ T F R).satisfies η ↔
      equations_l (ω.eval η) (A.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (T.eval η) (F.eval η) (R.eval η) := by
  simp only [equations_m, equations_l, Formula.satisfies, PowerlessFormulaConstructor.constructor_formula_l,
    value_formula_l, map_formula_l, PowerlessEvaluationClause.member_formula_l,
    PowerlessEvaluationClause.equal_formula_l, PowerlessFiniteEvaluationRelationEquations.exists_formula_l,
    member_m, member_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def spec_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω A e t₁ t₂ t₃ T F R : carrier_l 𝒩) : Prop :=
  domain_l ω A F R ∧ zero_l e R ∧ equations_l ω A e t₁ t₂ t₃ T F R

def spec_m {Γ Δ : SortContext ℒ} (ω A e t₁ t₂ t₃ T F R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (domain_m ω A F R) <| .conj (zero_m e R) (equations_m ω A e t₁ t₂ t₃ T F R)

theorem spec_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A e t₁ t₂ t₃ T F R : Term ℒ Γ Δ .set) :
    (spec_m ω A e t₁ t₂ t₃ T F R).satisfies η ↔
      spec_l (ω.eval η) (A.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (T.eval η) (F.eval η) (R.eval η) := by
  simp only [spec_m, spec_l, Formula.satisfies, domain_formula_l, zero_formula_l, equations_formula_l]

#print axioms domain_formula_l
#print axioms zero_formula_l
#print axioms equations_formula_l
#print axioms spec_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionSpecification
