import BMSConstructibleBridge.SecondOrderCanonicalClassMinimum
import BMSConstructibleBridge.SecondOrderDefinableRelationImage
import YesMetaZFC.Automation.PrefixQuantification

/-! # 实际二元请求与规范最小见证的纯公式

请求公式的首自由槽为输出，次槽为输入。编码包和基底是显式有限参数；
图构造所用正文保留原请求的全部自由参数，不换成宿主谓词。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalWitnessSyntax

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderCanonicalClassMinimum (minimum_l)
open PowerlessBMSQuotientSubsetImageDerives
  (at_m at_formula_l parameters_l parameters_empty_l parameters_pushBound_l)
open YesMetaZFC.Automation.PrefixQuantification (env_l entry_m weaken_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def minimum_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.class_m B y) <| .conj (at_m φ x y) <|
    .forallE .set <| .imp (at_m φ (up x) (.bvar .here)) <|
      .neg (SecondOrderCanonicalClassOrder.edge_m (up ω) (up e) (up t₁) (up t₂) (up t₃)
        (up Pair) (up Valid) (up B) (up P₀) (.bvar .here) (up y))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem minimum_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ x y : Term ℒ Γ Δ .set) :
    (minimum_m φ ω e t₁ t₂ t₃ Pair Valid B P₀ x y).satisfies η ↔
      minimum_l φ ((parameters_l η).pushFree (x.eval η))
        (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η)
        (Valid.eval η) (B.eval η) (P₀.eval η) (y.eval η) := by
  simp only [minimum_m, minimum_l, Formula.satisfies, at_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    SecondOrderCanonicalClassOrder.edge_formula_l K, parameters_pushBound_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def request_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (A X : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up A)) <|
    .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up X)))
      (at_m φ (.bvar (.there .here)) (.bvar .here))

theorem request_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 Γ Δ) (A X : Term ℒ Γ Δ .set) :
    (request_m φ A X).satisfies η ↔ ∀ x, SecondOrderQuotient.mem_l hℳ x (A.eval η) →
      ∃ y, SecondOrderQuotient.mem_l hℳ y (X.eval η) ∧
        φ.satisfies (((parameters_l η).pushFree x).pushFree y) := by
  simp only [request_m, Formula.satisfies, at_formula_l, SecondOrderObjectSyntax.member_m,
    parameters_pushBound_l, up, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

abbrev support_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set, .set]

private def lift_m {Δ : SortContext ℒ} (Θ : SortContext ℒ)
    (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ [] (.set :: .set :: (Θ ++ Δ)) :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ) [] (.set :: .set :: (Θ ++ Δ)) from
    .map (fun v => nomatch v) (fun {_} v => match v with
      | .here => .fvar .here
      | .there .here => .fvar (.there .here)
      | .there (.there v) => weaken_m (SetTheory.SetSort.set :: SetTheory.SetSort.set :: Θ) (.fvar v)))

private theorem lift_formula_l {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (xs : Values (SecondOrderQuotient.structure_l hℳ).Carrier Θ)
    (x y : SecondOrderQuotient.type_l hℳ) :
    (lift_m Θ φ).satisfies (((env_l η xs).pushFree x).pushFree y) ↔
      φ.satisfies ((η.pushFree x).pushFree y) := by
  refine (Formula.satisfies_substitute _ _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    cases v with
    | here => rfl
    | there v =>
      cases v with
      | here => rfl
      | there v =>
        exact YesMetaZFC.Automation.PrefixQuantification.weaken_l η
          (.cons y (.cons x xs)) (.fvar v)

private def parameter_m {Δ : SortContext ℒ} (v : Variable support_m .set) :
    Term ℒ [] (.set :: .set :: (support_m ++ Δ)) .set :=
  ((entry_m (Δ := Δ) v).weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set

/-- 用于原二阶理解的实际二元关系；首槽输入，次槽输出。 -/
def relation_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: (support_m ++ Δ)) :=
  minimum_m (lift_m (.set :: .set :: support_m) φ)
    (parameter_m .here) (parameter_m (.there .here)) (parameter_m (.there (.there .here)))
    (parameter_m (.there (.there (.there .here)))) (parameter_m (.there (.there (.there (.there .here)))))
    (parameter_m (.there (.there (.there (.there (.there .here))))))
    (parameter_m (.there (.there (.there (.there (.there (.there .here)))))))
    (parameter_m (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (parameter_m (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar .here) (.fvar (.there .here))

def support_env_l {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ : SecondOrderQuotient.type_l hℳ) : Env 𝒱 [] (support_m ++ Δ) :=
  env_l η (.cons ω (.cons e (.cons t₁ (.cons t₂ (.cons t₃ (.cons Pair
    (.cons Valid (.cons B (.cons P₀ .nil)))))))))

theorem relation_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ x y : SecondOrderQuotient.type_l hℳ) :
    (relation_m φ).satisfies (((support_env_l η ω e t₁ t₂ t₃ Pair Valid B P₀).pushFree y).pushFree x) ↔
      minimum_l φ (η.pushFree x) ω e t₁ t₂ t₃ Pair Valid B P₀ y := by
  have hLift z := lift_formula_l (Θ := .set :: .set :: support_m) φ η
    (.cons x (.cons y (.cons ω (.cons e (.cons t₁ (.cons t₂ (.cons t₃ (.cons Pair
      (.cons Valid (.cons B (.cons P₀ .nil))))))))))) x z
  rw [relation_m, minimum_formula_l K]
  simp only [PowerlessBMSQuotientSubsetImageDerives.parameters_empty_l, parameter_m,
    Term.eval_weakenFree, support_env_l, entry_m, env_l, Term.eval]
  unfold minimum_l
  exact and_congr Iff.rfl (and_congr (hLift y) (forall_congr' (fun z =>
    imp_congr (hLift z) Iff.rfl)))

/-- 同一最小见证正文，输出槽先于输入槽，供既有子集值域接口使用。 -/
def output_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: (support_m ++ Δ)) :=
  (relation_m φ).swapFreeTop

theorem output_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ x y : SecondOrderQuotient.type_l hℳ) :
    (output_m φ).satisfies (((support_env_l η ω e t₁ t₂ t₃ Pair Valid B P₀).pushFree x).pushFree y) ↔
      minimum_l φ (η.pushFree x) ω e t₁ t₂ t₃ Pair Valid B P₀ y := by
  let ξ := support_env_l η ω e t₁ t₂ t₃ Pair Valid B P₀
  change ((relation_m φ).rename (Renaming.free VariableRenaming.swapTop)).satisfies
    ((ξ.pushFree x).pushFree y) ↔ _
  refine (Formula.satisfies_rename _ _ _).trans ?_
  have hEnv : ((ξ.pushFree (sort := SetTheory.SetSort.set) x).pushFree
      (sort := SetTheory.SetSort.set) y).pullbackRenaming
      (Renaming.free VariableRenaming.swapTop) =
      ((ξ.pushFree (sort := SetTheory.SetSort.set) y).pushFree (sort := SetTheory.SetSort.set) x) := by
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      cases v with
      | here => rfl
      | there v => cases v <;> rfl
  rw [hEnv]
  exact relation_formula_l K φ η ω e t₁ t₂ t₃ Pair Valid B P₀ x y

#print axioms relation_formula_l
#print axioms output_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalWitnessSyntax
