import BMSConstructibleBridge.PowerlessRelativeClassUniformEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationUnionDerives

/-! # 给定实际统一枚举族的合并：原 Z₂ 推导

对象语言为纯隶属 ℒ，背景为原 SecondOrderArithmetic.theory_m，正式出口
使用原 Derives。四个自由参数为 ω、R、J、X；J 已是实际类内映射，其
每个值 j 都是从同一 ω 到 X 的实际集合函数，且给定族覆盖 X。

结论仅存在合并满射 U，不断言逐点枚举见证能被收集为 J，也不把 J 的
存在加入结论。本对象模式不是首不可数 Ω 的正规性结论；后续应用仍须
独立提供统一枚举族和覆盖规格。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassUniformEnumerationDerives

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 只读取给定族的实际成员函数，不在模式中加入选择或收集。 -/
def each_m {Γ Δ : SortContext ℒ} (ω R J X : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall ω <|
    membershipLevyBound.boundedForall (up R) <|
      let i : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
      let j : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar .here
      let lift (t : Term ℒ Γ Δ .set) := up (up t)
      .imp (PowerlessValueBounded.formula_m (lift J) i j)
        (SecondOrderObjectSyntax.map_m j (lift ω) (lift X))

theorem each_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (ω R J X : Term ℒ Γ Δ .set) :
    (each_m ω R J X).satisfies η ↔
      ∀ i, member_l 𝒩 i (ω.eval η) → ∀ j, member_l 𝒩 j (R.eval η) →
        value_l (ℳ := 𝒩) (J.eval η) i j →
          map_l (ℳ := 𝒩) j (ω.eval η) (X.eval η) := by
  simp only [each_m, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    map_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 覆盖条件显式保留两个内部 ω 坐标和实际 R 成员。 -/
def cover_m {Γ Δ : SortContext ℒ} (ω R J X : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall X <|
    membershipLevyBound.boundedExists (up ω) <|
      membershipLevyBound.boundedExists (up (up R)) <|
        let x : Term ℒ (.set :: .set :: .set :: Γ) Δ .set :=
          .bvar (.there (.there .here))
        let i : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
        let j : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
        let lift (t : Term ℒ Γ Δ .set) := up (up (up t))
        .conj (PowerlessValueBounded.formula_m (lift J) i j) <|
          membershipLevyBound.boundedExists (lift ω) <|
            PowerlessValueBounded.formula_m (up j) (.bvar .here) (up x)

theorem cover_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (ω R J X : Term ℒ Γ Δ .set) :
    (cover_m ω R J X).satisfies η ↔
      ∀ x, member_l 𝒩 x (X.eval η) →
        ∃ i, member_l 𝒩 i (ω.eval η) ∧ ∃ j, member_l 𝒩 j (R.eval η) ∧
          value_l (ℳ := 𝒩) (J.eval η) i j ∧
            ∃ k, member_l 𝒩 k (ω.eval η) ∧ value_l (ℳ := 𝒩) j k x := by
  simp only [cover_m, Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def conclusion_m {Γ Δ : SortContext ℒ} (ω X : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (SecondOrderObjectSyntax.map_m (.bvar .here) (up ω) (up X))
    (PowerlessMemberDefSyntax.onto_m (up ω) (up X) (.bvar .here))

theorem conclusion_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (ω X : Term ℒ Γ Δ .set) :
    (conclusion_m ω X).satisfies η ↔
      ∃ U, map_l (ℳ := 𝒩) U (ω.eval η) (X.eval η) ∧
        ∀ x, member_l 𝒩 x (X.eval η) →
          ∃ n, member_l 𝒩 n (ω.eval η) ∧ value_l (ℳ := 𝒩) U n x := by
  simp only [conclusion_m, Formula.satisfies, map_formula_l,
    PowerlessRelativeClassEnumerationUnionDerives.onto_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let R : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let J : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let X : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (SecondOrderObjectSyntax.map_m J ω R) <|
      .imp (each_m ω R J X) <| .imp (cover_m ω R J X) (conclusion_m ω X)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y, SecondOrderQuotient.mem_l hℳ y x →
      SecondOrderQuotient.mem_l hℳ y B) :
    sentence_m.TrueIn (PowerlessRelativeClassStructure.structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l, map_formula_l,
    each_l, cover_l, conclusion_l]
  intro hω hJ hEach hCover
  exact PowerlessRelativeClassUniformEnumeration.exists_l hω hJ
    (fun i j hi hj hij => hEach i hi j hj hij) hCover

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m
    (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms each_l
#print axioms cover_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassUniformEnumerationDerives
