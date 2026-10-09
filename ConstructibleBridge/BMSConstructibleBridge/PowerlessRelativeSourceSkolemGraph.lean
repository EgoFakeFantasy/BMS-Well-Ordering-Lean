import BMSConstructibleBridge.PowerlessSourceWitnessTotalization
import BMSConstructibleBridge.PowerlessRelativeSourceLeastWitnessDerives
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramGraphOperator

/-! # 原有限源矩阵的总 Skolem 图与程序守卫

背景是原 Z₂，语言是纯隶属 ℒ。原矩阵无需 Δ₀，也无需逐输入有见证；
以源域内默认值总化后在实际良序中取最小输出。结论给实际 Class
函数 J:W→W、完整原商读数及其纯 Δ₀ 图查询算子的单值和保层性。
不要求 J∈W，不断言 W 已满足 Collection 或源模型全部公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceSkolemGraph

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (mem_l)
open SecondOrderObjectSyntax (member_m map_m)
open PowerlessRelativeSourceLeastWitnessDerives (least_m least_formula_l reading_m)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

include hBase in
theorem exists_l (W R : PowerlessRelativeClassStructure.type_l hℳ B)
    (hW : ∃ x, mem_l hℳ x W.val) (hR : wellOrder_l (ℳ := 𝒱) W.val R.val)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) W.val hW) [] Δ)
    (d : PowerlessMemberStructure.type_l (ℳ := 𝒱) W.val) :
    ∃ J : PowerlessRelativeClassStructure.type_l hℳ B,
      map_l (ℳ := 𝒱) J.val W.val W.val ∧
        ∀ x y : PowerlessMemberStructure.type_l (ℳ := 𝒱) W.val,
          value_l (ℳ := 𝒱) J.val x.val y.val ↔
            (PowerlessSourceWitnessTotalization.formula_m φ).satisfies
              (((η.pushFree d).pushFree y).pushFree x) ∧
            ∀ z : PowerlessMemberStructure.type_l (ℳ := 𝒱) W.val,
              (PowerlessSourceWitnessTotalization.formula_m φ).satisfies
                (((η.pushFree d).pushFree z).pushFree x) →
              ¬value_l (ℳ := 𝒱) R.val z.val y.val := by
  obtain ⟨J, hJ, hRead⟩ := PowerlessRelativeSourceLeastWitness.exists_l
    (hBase := hBase) W W R hW hR (fun _ h => h)
    (PowerlessSourceWitnessTotalization.formula_m φ) (η.pushFree d)
    (fun x _ => PowerlessSourceWitnessTotalization.total_l φ η d x)
  exact ⟨J, hJ, fun x y => ⟨fun h => ((hRead x y).mp h).2,
    fun h => (hRead x y).mpr ⟨x.property, h⟩⟩⟩

/-- 有原见证时，所选输出仍是原矩阵的最小见证。 -/
theorem witness_l {W : SecondOrderQuotient.type_l hℳ} {hW : ∃ x, mem_l hℳ x W}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) W hW) [] Δ)
    (d x y : PowerlessMemberStructure.type_l (ℳ := 𝒱) W) (R : SecondOrderQuotient.type_l hℳ)
    (h : (PowerlessSourceWitnessTotalization.formula_m φ).satisfies
        (((η.pushFree d).pushFree y).pushFree x) ∧
      ∀ z : PowerlessMemberStructure.type_l (ℳ := 𝒱) W,
        (PowerlessSourceWitnessTotalization.formula_m φ).satisfies
          (((η.pushFree d).pushFree z).pushFree x) → ¬value_l (ℳ := 𝒱) R z.val y.val)
    (hSome : ∃ z, φ.satisfies ((η.pushFree z).pushFree x)) :
    φ.satisfies ((η.pushFree y).pushFree x) ∧
      ∀ z : PowerlessMemberStructure.type_l (ℳ := 𝒱) W,
        φ.satisfies ((η.pushFree z).pushFree x) → ¬value_l (ℳ := 𝒱) R z.val y.val := by
  exact ⟨(PowerlessSourceWitnessTotalization.agrees_l φ η d x y hSome).mp h.1,
    fun z hz => h.2 z ((PowerlessSourceWitnessTotalization.formula_l φ η d x z).mpr (Or.inl hz))⟩

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set

private def lift_m {Γ Ε Δ : SortContext ℒ} (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    Variable Δ .set → Term ℒ (.set :: Γ) Ε .set := fun v => up (τ v)

private abbrev context_m (Δ : SortContext ℒ) := .set :: .set :: .set :: Δ

private def binding_m {Γ Ε Δ : SortContext ℒ} (B : Term ℒ Γ Ε .set)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    Variable (.set :: Δ) .set → Term ℒ Γ Ε .set
  | .here => B
  | .there v => τ v

def payload_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: context_m Δ) :=
  let J : Term ℒ [] (.set :: context_m Δ) .set := .fvar .here
  let W := .fvar (.there .here)
  let R := .fvar (.there (.there .here))
  let B := .fvar (.there (.there (.there .here)))
  let τ : Variable Δ .set → Term ℒ [] (.set :: context_m Δ) .set :=
    fun v => .fvar (.there (.there (.there (.there v))))
  let ψ := PowerlessSourceWitnessTotalization.formula_m φ
  let δ := PowerlessRelativeFiniteProgramGraphOperator.relation_m J
  .conj (PowerlessRelativeHierarchySyntax.class_m B J) <|
    .conj (map_m J W W) <|
      .conj (reading_m ψ W R W J (binding_m B τ)) <|
        .conj (PowerlessRelativeFiniteProgramInstruction.functional_m δ B)
          (PowerlessRelativeFiniteProgramLimitStep.closed_m δ B W)

private def graph_binding_m {Ε Δ : SortContext ℒ} (B W R J : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    Substitution ℒ [] (.set :: .set :: .set :: .set :: Δ) [] Ε :=
  .map (fun v => nomatch v) (fun {s} v => match s with
    | .set => match v with
      | .here => J
      | .there .here => W
      | .there (.there .here) => R
      | .there (.there (.there .here)) => B
      | .there (.there (.there (.there v))) => τ v)

/-- 原参数 Δ 不随已绑定的见证图增长；只提升其指定的项。 -/
def graph_m {Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B W R J : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  (payload_m φ).substitute (graph_binding_m B W R J τ)

theorem graph_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ζ : Env 𝒩 [] Ε) (B W R J : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) (η : Env 𝒩 [] Δ)
    (hτ : ∀ v, (τ v).eval ζ = η.freeVal v) :
    (graph_m φ B W R J τ).satisfies ζ ↔
      (payload_m φ).satisfies
        ((((η.pushFree (B.eval ζ)).pushFree (R.eval ζ)).pushFree (W.eval ζ)).pushFree (J.eval ζ)) := by
  rw [graph_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ξ => (payload_m φ).satisfies ξ)
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s
    cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => cases v with
          | here => rfl
          | there v => exact hτ v

/-- 任意装配上下文中的实际见证图仍属于原相对可构造类。 -/
theorem class_l (K : source_coding_l hℳ) {Ε Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ζ : Env 𝒱 [] Ε)
    (B W R J : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (h : (graph_m φ B W R J τ).satisfies ζ) :
    PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ζ) (J.eval ζ) := by
  let η : Env 𝒱 [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => (τ v).eval ζ }
  have hp := (graph_formula_l φ ζ B W R J τ η (fun _ => rfl)).mp h
  have hc := (PowerlessRelativeHierarchySemantics.class_formula_l K
    ((((η.pushFree (B.eval ζ)).pushFree (R.eval ζ)).pushFree (W.eval ζ)).pushFree (J.eval ζ))
    (.fvar (.there (.there (.there .here)))) (.fvar .here)).mp hp.1
  change ∃ a c, PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval ζ) a c ∧
    mem_l hℳ (J.eval ζ) c
  simpa only [Term.eval, Env.pushFree_here, Env.pushFree_there] using hc

def conclusion_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (context_m Δ) := (payload_m φ).existsFreeTop .set

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (context_m Δ) :=
  let W : Term ℒ [] (context_m Δ) .set := .fvar .here
  let R := .fvar (.there .here)
  let B := .fvar (.there (.there .here))
  let τ : Variable Δ .set → Term ℒ [] (context_m Δ) .set :=
    fun v => .fvar (.there (.there (.there v)))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B W) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B R) <|
        .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m W R) <|
          .imp (member_m B W) <| .imp (parameters_m Δ W τ) (conclusion_m φ)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    member_m, Arguments.eval, Term.eval]
  intro ζ hBase hW hR hOrder hBW hParams
  let W := ζ.freeVal (.here : Variable (context_m Δ) .set)
  let R := ζ.freeVal (.there (.here : Variable (.set :: .set :: Δ) .set))
  let B := ζ.freeVal (.there (.there (.here : Variable (.set :: Δ) .set)))
  have hNonempty : ∃ x, mem_l h𝒩 x W := ⟨B, hBW⟩
  have hParams' := (parameters_formula_l Δ ζ (.fvar .here)
    (fun v => .fvar (.there (.there (.there v))))).mp hParams
  let η : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l h𝒩) W hNonempty) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with
        | .set => ⟨ζ.freeVal (.there (.there (.there v))), hParams' _ v⟩ }
  let d : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l h𝒩) W := ⟨B, hBW⟩
  obtain ⟨J, hJ, hRead⟩ := exists_l (hBase := hBase)
    ⟨W, hW⟩ ⟨R, hR⟩ hNonempty hOrder φ η d
  rw [conclusion_m, Formula.satisfies_existsFreeTop]
  refine ⟨J.val, ?_⟩
  let ξ : Env (SecondOrderQuotient.structure_l h𝒩) [] (.set :: context_m Δ) :=
    ζ.pushFree J.val
  have hReading : (reading_m (PowerlessSourceWitnessTotalization.formula_m φ)
      (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there .here))
      (.fvar .here) (binding_m (.fvar (.there (.there (.there .here))))
        (fun v => .fvar (.there (.there (.there (.there v))))))).satisfies ξ := by
    simp only [reading_m, Formula.satisfies, PowerlessValueBounded.formula_l,
      member_m, Arguments.eval, Term.eval_weakenBound, Term.eval]
    intro x y
    have hLeast (a b : PowerlessMemberStructure.type_l
        (ℳ := SecondOrderQuotient.structure_l h𝒩) W) :=
      least_formula_l (PowerlessSourceWitnessTotalization.formula_m φ)
        (show Env (SecondOrderQuotient.structure_l h𝒩) [.set, .set] (.set :: context_m Δ) from
          (ξ.pushBound a.val).pushBound b.val)
        (.fvar (.there .here)) (.fvar (.there (.there .here)))
        (.bvar (.there .here)) (.bvar .here)
        (lift_m (lift_m (binding_m (.fvar (.there (.there (.there .here))))
          (fun v => .fvar (.there (.there (.there (.there v))))))))
        (η.pushFree d) a b rfl rfl rfl (by intro v; cases v <;> rfl)
    constructor
    · intro hxy
      obtain ⟨hx, hy⟩ := SecondOrderFunctionProperties.value_mem_l h𝒩 hJ hxy
      exact ⟨hx, hy, (hLeast ⟨x, hx⟩ ⟨y, hy⟩).mpr ((hRead ⟨x, hx⟩ ⟨y, hy⟩).mp hxy)⟩
    · rintro ⟨hx, hy, hxy⟩
      exact (hRead ⟨x, hx⟩ ⟨y, hy⟩).mpr ((hLeast ⟨x, hx⟩ ⟨y, hy⟩).mp hxy)
  simp only [payload_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeFiniteProgramInstruction.functional_formula_l K,
    PowerlessRelativeFiniteProgramLimitStep.closed_formula_l K,
    parameters_empty_l, Term.eval, Env.pushFree_here, Env.pushFree_there]
  exact ⟨J.property, hJ, hReading,
    PowerlessRelativeFiniteProgramGraphOperator.functional_l (.fvar .here) ξ hJ,
    PowerlessRelativeFiniteProgramGraphOperator.range_closed_l (.fvar .here) ξ hJ (fun _ h => h)⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ)

#print axioms exists_l
#print axioms witness_l
#print axioms graph_formula_l
#print axioms class_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceSkolemGraph
