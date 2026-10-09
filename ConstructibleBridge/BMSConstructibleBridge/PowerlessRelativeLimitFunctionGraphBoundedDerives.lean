import BMSConstructibleBridge.PowerlessRelativeLimitFunctionGraphBounded
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparationDerives

/-! # 极限层函数图两次 Def 成员界的原 Z₂ 对象模式

固定一个外部 Δ₀ 矩阵，实际纯 ℒ 句显式保留传递基集、原商层值、非零极限、
原 Def(W,D)、原 Def(D,E)、全部 raw 图读数及函数规格。八个固定对象槽与
矩阵原参数分开；参数 guard 只要求原 Δ 参数属于 D，不预设待证图 G∈D。

全部读数均在原商结构中核验，原 Def 使用 global_m 的实际对应，不以类内
相对化替代。每个合规格矩阵实例经原图翻译取得原 Z₂ Derives；这是有条件
的两 Def 成员界模式，不是共同界构造、统一真值断言或 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFunctionGraphBoundedDerives

open Logic FirstOrder ThirdOrderSemantics StabilityFrame SecondOrderObjectSyntax
open PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeHierarchySyntax (up)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

/-- 固定槽依次为 B、γ、W、D、E、定义域、值域、G；尾部只保留原矩阵参数。 -/
abbrev context_m (Δ : SortContext ℒ) : SortContext ℒ :=
  .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: Δ

private def tail_m {Δ : SortContext ℒ} {s : SetTheory.SetSort}
    (v : Variable Δ s) : Variable (context_m Δ) s :=
  .there (.there (.there (.there (.there (.there (.there (.there v)))))))

private def parameters_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (ρ : Env 𝒩 [] (context_m Δ)) : Env 𝒩 [] Δ :=
  { boundVal := fun v => nomatch v
    freeVal := fun v => ρ.freeVal (tail_m v) }

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [.set, .set] (context_m Δ)
  | _, .here => .bvar (.there .here)
  | _, .there .here => .bvar .here
  | _, .there (.there v) => .fvar (tail_m v)

private def matrix_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [.set, .set] (context_m Δ) :=
  φ.substitute (.map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v) insert_m)

private theorem matrix_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ρ : Env 𝒩 [] (context_m Δ)) (x y : carrier_l 𝒩) :
    (matrix_m φ).satisfies ((ρ.pushBound x).pushBound y) ↔
      φ.satisfies (((parameters_l ρ).pushFree y).pushFree x) := by
  refine (Formula.satisfies_substitute _ _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro _ v; nomatch v
  · intro s v
    cases s
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

/-- 完整 raw Value 读数；两坐标量词不限制为类内对象。 -/
def read_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (context_m Δ) :=
  let G : Term ℒ [.set, .set] (context_m Δ) .set :=
    .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let Domain : Term ℒ [.set, .set] (context_m Δ) .set :=
    .fvar (.there (.there (.there (.there (.there .here)))))
  let Range : Term ℒ [.set, .set] (context_m Δ) .set :=
    .fvar (.there (.there (.there (.there (.there (.there .here))))))
  .forallE .set <| .forallE .set <| .iff
    (value_m G (.bvar (.there .here)) (.bvar .here)) <|
      .conj (member_m (.bvar (.there .here)) Domain)
        (.conj (member_m (.bvar .here) Range) (matrix_m φ))

theorem read_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ρ : Env 𝒩 [] (context_m Δ)) :
    (read_m φ).satisfies ρ ↔ ∀ x y,
      ThirdOrderSemantics.value_l (ℳ := 𝒩)
        (ρ.freeVal (.there (.there (.there (.there (.there (.there (.there .here)))))))) x y ↔
      member_l 𝒩 x (ρ.freeVal (.there (.there (.there (.there (.there .here)))))) ∧
        member_l 𝒩 y (ρ.freeVal (.there (.there (.there (.there (.there (.there .here))))))) ∧
          φ.satisfies (((parameters_l ρ).pushFree y).pushFree x) := by
  simp only [read_m, Formula.satisfies, ThirdOrderSemantics.value_formula_l, matrix_formula_l,
    member_m, ThirdOrderSemantics.member_l, Arguments.eval, Term.eval]; rfl

private def subset_m {Γ Δ : SortContext ℒ} (X W : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.imp (member_m (.bvar .here) (up X)) (member_m (.bvar .here) (up W)))

private theorem subset_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (X W : Term ℒ Γ Δ .set) :
    (subset_m X W).satisfies η ↔ ∀ x, member_l 𝒩 x (X.eval η) → member_l 𝒩 x (W.eval η) := by
  simp only [subset_m, Formula.satisfies, member_m, ThirdOrderSemantics.member_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]; rfl

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (context_m Δ) :=
  let B : Term ℒ [] (context_m Δ) .set := .fvar .here
  let γ : Term ℒ [] (context_m Δ) .set := .fvar (.there .here)
  let W : Term ℒ [] (context_m Δ) .set := .fvar (.there (.there .here))
  let D : Term ℒ [] (context_m Δ) .set := .fvar (.there (.there (.there .here)))
  let E : Term ℒ [] (context_m Δ) .set := .fvar (.there (.there (.there (.there .here))))
  let Domain : Term ℒ [] (context_m Δ) .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let Range : Term ℒ [] (context_m Δ) .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let G : Term ℒ [] (context_m Δ) .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B γ W) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m γ) <|
        .imp (PowerlessMemberDefSyntax.global_m W D) <|
          .imp (PowerlessMemberDefSyntax.global_m D E) <|
            .imp (parameters_m Δ D (fun v => .fvar (tail_m v))) <|
              .imp (member_m Domain D) <| .imp (member_m Range D) <|
                .imp (subset_m Domain W) <| .imp (subset_m Range W) <|
                  .imp (map_m G Domain Range) <| .imp (read_m φ) (member_m G E)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ρ hBase hW hLimit hWD hDE hParams hDomainD hRangeD hDomainW hRangeW hG hRead
  change mem_l hℳ
    (ρ.freeVal (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (ρ.freeVal (.there (.there (.there (.there .here)))))
  exact PowerlessRelativeLimitFunctionGraphBounded.member_l hℳ
    ((PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ ρ (.fvar .here)).mp hBase)
    ((PowerlessRelativeHierarchySemantics.level_formula_l K ρ (.fvar .here)
      (.fvar (.there .here)) (.fvar (.there (.there .here)))).mp hW)
    ((PowerlessRelativeHierarchySemantics.limit_formula_l (hℳ := hℳ)
      ρ (.fvar (.there .here))).mp hLimit)
    ((PowerlessMemberDefDerives.formula_l K ρ (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))).mp hWD)
    ((PowerlessMemberDefDerives.formula_l K ρ (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))).mp hDE)
    hφ (parameters_l ρ)
    ((parameters_formula_l Δ ρ (.fvar (.there (.there (.there .here))))
      (fun v => .fvar (tail_m v))).mp hParams)
    hDomainD hRangeD
    ((subset_formula_l ρ (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there .here)))).mp hDomainW)
    ((subset_formula_l ρ (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there .here)))).mp hRangeW)
    ((ThirdOrderSemantics.map_formula_l ρ
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))).mp hG)
    ((read_formula_l φ ρ).mp hRead)

/-- 每个固定纯 Δ₀ 矩阵实例均回到原 Z₂ Derives 核。 -/
theorem derives_m {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ hφ)

#print axioms read_formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFunctionGraphBoundedDerives
