import BMSConstructibleBridge.PowerlessRelativeLimitSatisfactionStatic
import BMSConstructibleBridge.PowerlessRelativeClassInstantiation
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparationDerives

/-! # 固定外层 Sat 存在模式的纯对象语法

五个环境槽依次为基集 B、内阶段 γ、内层 D、外阶段 β、外层 C。
层谓词、严格先前关系及成员守卫均在原商环境读取；只相对化实际 ω、
序列规格、静态编码正文和 Sat 正文。F 由外层全称量化，R 为同一外层
中的存在见证；不向对象句加入原算术编码或合法性实数参数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSatisfactionSyntax

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

abbrev context_m (Δ : SortContext ℒ) : SortContext ℒ :=
  .set :: .set :: .set :: .set :: .set :: Δ

abbrev base_m {Γ Δ : SortContext ℒ} : Term ℒ Γ (context_m Δ) .set := .fvar .here

abbrev innerStage_m {Γ Δ : SortContext ℒ} : Term ℒ Γ (context_m Δ) .set :=
  .fvar (.there .here)

abbrev inner_m {Γ Δ : SortContext ℒ} : Term ℒ Γ (context_m Δ) .set :=
  .fvar (.there (.there .here))

abbrev outerStage_m {Γ Δ : SortContext ℒ} : Term ℒ Γ (context_m Δ) .set :=
  .fvar (.there (.there (.there .here)))

abbrev outer_m {Γ Δ : SortContext ℒ} : Term ℒ Γ (context_m Δ) .set :=
  .fvar (.there (.there (.there (.there .here))))

/-- 跳过五个层级环境槽，保持原静态参数的顺序。 -/
def tail_m {Γ Δ : SortContext ℒ} : VariableSubstitution ℒ Δ Γ (context_m Δ)
  | _, v => .fvar (.there (.there (.there (.there (.there v)))))

/-- 一个源自由槽对应当前绑定的 F。 -/
def one_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: Δ) [.set] (context_m Δ)
  | _, .here => .bvar .here
  | _, .there v => tail_m v

/-- 源头两个自由槽依次为 R、F，与两层绑定量词一致。 -/
def two_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [.set, .set] (context_m Δ)
  | _, .here => .bvar .here
  | _, .there .here => .bvar (.there .here)
  | _, .there (.there v) => tail_m v

def sourceStatic_m {Δ : SortContext ℒ} (ω e N T t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: Δ) :=
  let w (t : Term ℒ [] Δ .set) := t.weakenFree SetTheory.SetSort.set
  PowerlessSatisfactionExistenceSyntax.static_m
    (w ω) (w e) (w t₁) (w t₂) (w t₃) (w T) (w N) (.fvar .here)

theorem sourceStatic_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (η : Env 𝒩 [] Δ)
    (ω e N T t₁ t₂ t₃ : Term ℒ [] Δ .set) (F : carrier_l 𝒩) :
    (sourceStatic_m ω e N T t₁ t₂ t₃).satisfies (η.pushFree F) ↔
      PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒩)
        (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (T.eval η) (N.eval η) F := by
  simp only [sourceStatic_m, PowerlessSatisfactionExistenceSyntax.static_formula_l,
    Term.eval_weakenFree, Term.eval, Env.pushFree_here]

def sourceSat_m {Δ : SortContext ℒ} (ω e T A t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  let w (t : Term ℒ [] Δ .set) := (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set
  PowerlessSatisfactionSpecification.spec_m
    (w ω) (w A) (w e) (w t₁) (w t₂) (w t₃) (w T) (.fvar (.there .here)) (.fvar .here)

theorem sourceSat_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (η : Env 𝒩 [] Δ)
    (ω e T A t₁ t₂ t₃ : Term ℒ [] Δ .set) (F R : carrier_l 𝒩) :
    (sourceSat_m ω e T A t₁ t₂ t₃).satisfies ((η.pushFree F).pushFree R) ↔
      PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒩)
        (ω.eval η) (A.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (T.eval η) F R := by
  simp only [sourceSat_m, PowerlessSatisfactionSpecification.spec_formula_l,
    Term.eval_weakenFree, Term.eval, Env.pushFree_here, Env.pushFree_there]

/-- 原商层守卫不相对化，类内正文通过指定基集分别实例化。 -/
def schema_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    Formula ℒ [] (context_m Δ) :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m base_m) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m base_m innerStage_m inner_m) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m innerStage_m) <|
        .imp (PowerlessRelativeHierarchySyntax.level_m base_m outerStage_m outer_m) <|
          .imp (PowerlessRelativeHierarchySyntax.limit_m outerStage_m) <|
            .imp (member_m innerStage_m outerStage_m) <|
              .imp (parameters_m Δ inner_m tail_m) <|
                .imp (PowerlessRelativeClassInstantiation.formula_m base_m
                  (SecondOrderOmegaSyntax.omega_m ω) tail_m) <|
                  .imp (PowerlessRelativeClassInstantiation.formula_m base_m
                    (PowerlessFiniteSequencesSyntax.spec_m ω A S) tail_m) <|
                    .forallE .set <| .imp (member_m (.bvar .here) outer_m) <|
                      .imp (PowerlessRelativeClassInstantiation.formula_m base_m
                        (sourceStatic_m ω e N T t₁ t₂ t₃) one_m) <|
                        .existsE .set <| .conj (member_m (.bvar .here) outer_m)
                          (PowerlessRelativeClassInstantiation.formula_m base_m
                            (sourceSat_m ω e T A t₁ t₂ t₃) two_m)

def sentence_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω e N T A S t₁ t₂ t₃)

#print axioms sourceStatic_formula_l
#print axioms sourceSat_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSatisfactionSyntax
