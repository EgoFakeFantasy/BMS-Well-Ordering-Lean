import BMSConstructibleBridge.PowerlessRelativeSourceLeastWitness

/-! # 原源公式最小见证图模式的 Z₂ 对象推导

外部模式索引是任意有限原公式，不是假定原矩阵有界。原矩阵只在实际
集合域 C 内求值，排序图 R 的环境良序及全部源参数守卫明确留在句中。
结论是实际 Class 集合函数；不添加 C 内 Collection 或图属于 C 的断言。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceLeastWitnessDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (mem_l)
open SecondOrderObjectSyntax (member_m map_m)
open SecondOrderCutoffDefinableSurjectionDerives (relation_m relation_formula_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set

private def lift_m {Γ Ε Δ : SortContext ℒ} (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    Variable Δ .set → Term ℒ (.set :: Γ) Ε .set := fun v => up (τ v)

def least_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C R x y : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .conj (relation_m φ C x y τ) <|
    membershipLevyBound.boundedForall C <|
      .imp (relation_m φ (up C) (up x) (.bvar .here) (lift_m τ))
        (.neg (PowerlessValueBounded.formula_m (up R) (.bvar .here) (up y)))

theorem least_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {C : carrier_l 𝒱} {hC : ∃ c, member_l 𝒱 c C} {Γ Ε Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ζ : Env 𝒱 Γ Ε)
    (c r x y : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set)
    (η : Env (PowerlessMemberStructure.structure_l C hC) [] Δ)
    (a b : PowerlessMemberStructure.type_l C)
    (hc : c.eval ζ = C) (hx : x.eval ζ = a.val) (hy : y.eval ζ = b.val)
    (hτ : ∀ v, (τ v).eval ζ = (η.freeVal v).val) :
    (least_m φ c r x y τ).satisfies ζ ↔ φ.satisfies ((η.pushFree b).pushFree a) ∧
      ∀ z : PowerlessMemberStructure.type_l C,
        φ.satisfies ((η.pushFree z).pushFree a) → ¬value_l (ℳ := 𝒱) (r.eval ζ) z.val b.val := by
  simp only [least_m, Formula.satisfies, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Arguments.eval,
    PowerlessValueBounded.formula_l, up, Term.eval_weakenBound, Term.eval, hc, hy]
  rw [relation_formula_l φ ζ c x y τ η a b hc hx hy hτ]
  apply and_congr Iff.rfl
  have hRel (z : PowerlessMemberStructure.type_l C) := relation_formula_l φ (ζ.pushBound z.val)
    (up c) (up x) (.bvar .here) (lift_m τ) η a z
    (by simpa only [up, Term.eval_weakenBound] using hc)
    (by simpa only [up, Term.eval_weakenBound] using hx) rfl
    (fun v => by simpa only [lift_m, up, Term.eval_weakenBound] using hτ v)
  constructor
  · intro h z hz
    exact h z.val z.property ((hRel z).mpr hz)
  · intro h z hz hφ
    exact h ⟨z, hz⟩ ((hRel ⟨z, hz⟩).mp hφ)

def total_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C A : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  membershipLevyBound.boundedForall A <|
    membershipLevyBound.boundedExists (up C) <|
      relation_m φ (up (up C)) (.bvar (.there .here)) (.bvar .here) (lift_m (lift_m τ))

def reading_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C R A J : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .forallE .set <| .forallE .set <|
    let x := .bvar (.there .here)
    let y := .bvar .here
    .iff (PowerlessValueBounded.formula_m (up (up J)) x y) <|
      .conj (member_m x (up (up A))) <| .conj (member_m y (up (up C)))
        (least_m φ (up (up C)) (up (up R)) x y (lift_m (lift_m τ)))

private abbrev context_m (Δ : SortContext ℒ) := .set :: .set :: .set :: .set :: Δ

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ [] (context_m Δ) :=
  let C : Term ℒ [] (context_m Δ) .set := .fvar .here
  let R := .fvar (.there .here)
  let A := .fvar (.there (.there .here))
  let B := .fvar (.there (.there (.there .here)))
  let τ : Variable Δ .set → Term ℒ [] (context_m Δ) .set :=
    fun v => .fvar (.there (.there (.there (.there v))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B A) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B R) <|
          .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m C R) <|
            .imp (.existsE .set (member_m (.bvar .here) (up C))) <|
              .imp (.forallE .set (.imp (member_m (.bvar .here) (up A)) (member_m (.bvar .here) (up C)))) <|
                .imp (parameters_m Δ C τ) <| .imp (total_m φ C A τ) <|
                  .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
                    .conj (map_m (.bvar .here) (up A) (up C))
                      (reading_m φ (up C) (up R) (up A) (.bvar .here) (lift_m τ))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) : (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, map_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  intro ζ hBase hA hC hR hOrder hNonempty hAC hParams hTotal
  let C := ζ.freeVal (.here : Variable (context_m Δ) .set)
  let A := ζ.freeVal (.there (.there (.here : Variable (.set :: .set :: Δ) .set)))
  let B := ζ.freeVal (.there (.there (.there (.here : Variable (.set :: Δ) .set))))
  let R := ζ.freeVal (.there (.here : Variable (.set :: .set :: .set :: Δ) .set))
  have hParams' := (parameters_formula_l Δ ζ (.fvar .here)
    (fun v => .fvar (.there (.there (.there (.there v)))))).mp hParams
  let η : Env (PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ)
    C hNonempty) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with
        | .set => ⟨ζ.freeVal (.there (.there (.there (.there v)))), hParams' _ v⟩ }
  have hSome (x : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C)
      (hx : mem_l hℳ x.val A) : ∃ y, φ.satisfies ((η.pushFree y).pushFree x) := by
    simp only [total_m, Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
      Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies, Arguments.eval,
      up, Term.eval_weakenBound, Term.eval] at hTotal
    obtain ⟨y, hy, hxy⟩ := hTotal x.val hx
    exact ⟨⟨y, hy⟩, (relation_formula_l φ ((ζ.pushBound x.val).pushBound y)
      (.fvar .here) (.bvar (.there .here)) (.bvar .here)
      (fun v => .fvar (.there (.there (.there (.there v))))) η x ⟨y, hy⟩
      rfl rfl rfl (fun _ => rfl)).mp hxy⟩
  obtain ⟨J, hJ, hRead⟩ := PowerlessRelativeSourceLeastWitness.exists_l (hBase := hBase)
    ⟨A, hA⟩ ⟨C, hC⟩ ⟨R, hR⟩ hNonempty hOrder hAC φ η hSome
  refine ⟨J.val, J.property, hJ, ?_⟩
  simp only [reading_m, Formula.satisfies, PowerlessValueBounded.formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  intro x y
  have hLeast (a b : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C) :=
    least_formula_l φ
      (show Env (SecondOrderQuotient.structure_l hℳ) [.set, .set, .set] (context_m Δ) from
        ((ζ.pushBound J.val).pushBound a.val).pushBound b.val)
      (.fvar .here) (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here)
      (fun v => .fvar (.there (.there (.there (.there v))))) η a b
      rfl rfl rfl (fun _ => rfl)
  constructor
  · intro hxy
    obtain ⟨hx, hy⟩ := SecondOrderFunctionProperties.value_mem_l hℳ hJ hxy
    obtain ⟨_, hφ, hMin⟩ := (hRead ⟨x, hAC x hx⟩ ⟨y, hy⟩).mp hxy
    exact ⟨hx, hy, (hLeast ⟨x, hAC x hx⟩ ⟨y, hy⟩).mpr ⟨hφ, hMin⟩⟩
  · rintro ⟨hx, hy, hLeastXY⟩
    obtain ⟨hφ, hMin⟩ := (hLeast ⟨x, hAC x hx⟩ ⟨y, hy⟩).mp hLeastXY
    exact (hRead ⟨x, hAC x hx⟩ ⟨y, hy⟩).mpr ⟨hx, hφ, hMin⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceLeastWitnessDerives
