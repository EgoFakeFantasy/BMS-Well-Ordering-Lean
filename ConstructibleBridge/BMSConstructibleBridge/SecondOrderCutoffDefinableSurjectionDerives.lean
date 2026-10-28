import BMSConstructibleBridge.SecondOrderCutoffDefinableSurjection

/-! # 有限源矩阵的截断满射反证：原 Z₂ 对象模式

源公式逐量词相对化，背景、层值、实际 ω、全部参数守卫均在对象句内。
总性、单值性、值域界及满射性使用同一有限矩阵，不以宿主函数替代。
Ω 仅作外部域界，原矩阵参数仍须属于实际源域；不要求 Ω∈C。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCutoffDefinableSurjectionDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set

private def lift_m {Γ Ε Δ : SortContext ℒ} (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    Variable Δ .set → Term ℒ (.set :: Γ) Ε .set := fun v => up (τ v)

private def insert_m {Γ Ε Δ : SortContext ℒ} (x y : Term ℒ Γ Ε .set)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    Variable (.set :: .set :: Δ) .set → Term ℒ Γ Ε .set
  | .here => x
  | .there .here => y
  | .there (.there v) => τ v

def relation_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C x y : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  PowerlessRelativeParameters.instance_m φ C (insert_m x y τ)

theorem relation_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {C : carrier_l 𝒱} {hC : ∃ c, member_l 𝒱 c C} {Γ Ε Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ζ : Env 𝒱 Γ Ε)
    (c x y : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set)
    (η : Env (PowerlessMemberStructure.structure_l C hC) [] Δ)
    (a b : PowerlessMemberStructure.type_l (ℳ := 𝒱) C)
    (hc : c.eval ζ = C) (hx : x.eval ζ = a.val) (hy : y.eval ζ = b.val)
    (hτ : ∀ v, (τ v).eval ζ = (η.freeVal v).val) :
    (relation_m φ c x y τ).satisfies ζ ↔ φ.satisfies ((η.pushFree b).pushFree a) := by
  apply PowerlessRelativeParameters.instance_l φ ζ c (insert_m x y τ)
    ((η.pushFree b).pushFree a) hc
  intro v
  cases v with
  | here => exact hx
  | there v => cases v with
    | here => exact hy
    | there v => exact hτ v

def total_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C ω : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .forallE .set <| .imp (member_m (.bvar .here) (up ω)) <|
    .existsE .set <| .conj (member_m (.bvar .here) (up (up C)))
      (relation_m φ (up (up C)) (.bvar (.there .here)) (.bvar .here) (lift_m (lift_m τ)))

def unique_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C ω : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let x : Term ℒ (.set :: .set :: .set :: Γ) Ε .set := .bvar (.there (.there .here))
    let y := .bvar (.there .here)
    let z := .bvar .here
    let c := up (up (up C))
    let t := lift_m (lift_m (lift_m τ))
    .imp (member_m x (up (up (up ω)))) <| .imp (member_m y c) <|
      .imp (member_m z c) <| .imp (relation_m φ c x y t) <|
        .imp (relation_m φ c x z t) (.equal y z)

def range_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C ω Ω : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .forallE .set <| .forallE .set <|
    let x : Term ℒ (.set :: .set :: Γ) Ε .set := .bvar (.there .here)
    let y := .bvar .here
    .imp (member_m x (up (up ω))) <| .imp (member_m y (up (up C))) <|
      .imp (relation_m φ (up (up C)) x y (lift_m (lift_m τ))) (member_m y (up (up Ω)))

def onto_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C ω Ω : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .forallE .set <| .imp (member_m (.bvar .here) (up Ω)) <|
    .existsE .set <| .conj (member_m (.bvar .here) (up (up ω)))
      (relation_m φ (up (up C)) (.bvar .here) (.bvar (.there .here)) (lift_m (lift_m τ)))

def constraints_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C ω Ω : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .conj (total_m φ C ω τ) <| .conj (unique_m φ C ω τ) <|
    .conj (range_m φ C ω Ω τ) (onto_m φ C ω Ω τ)

/-- 逐量词守卫给出同一实际源环境的三个证书，涵盖全部内部坐标。 -/
theorem certificates_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {C ω Ω : carrier_l 𝒱} {hC : ∃ c, member_l 𝒱 c C} {Γ Ε Δ : SortContext ℒ}
    (hCT : PowerlessNaturalOrder.transitive_l C) (hωC : member_l 𝒱 ω C)
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ζ : Env 𝒱 Γ Ε)
    (c w o : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set)
    (η : Env (PowerlessMemberStructure.structure_l C hC) [] Δ)
    (hc : c.eval ζ = C) (hw : w.eval ζ = ω) (ho : o.eval ζ = Ω)
    (hτ : ∀ v, (τ v).eval ζ = (η.freeVal v).val)
    (h : (constraints_m φ c w o τ).satisfies ζ) :
    (∀ x : PowerlessMemberStructure.type_l C, member_l 𝒱 x.val ω →
      ∃! y, φ.satisfies ((η.pushFree y).pushFree x)) ∧
    (∀ x y : PowerlessMemberStructure.type_l C, member_l 𝒱 x.val ω →
      φ.satisfies ((η.pushFree y).pushFree x) → member_l 𝒱 y.val Ω) ∧
    (∀ y : PowerlessMemberStructure.type_l C, member_l 𝒱 y.val Ω →
      ∃ x, member_l 𝒱 x.val ω ∧ φ.satisfies ((η.pushFree y).pushFree x)) := by
  rcases h with ⟨hTotal, hUnique, hRange, hOnto⟩
  simp only [total_m, unique_m, range_m, onto_m, Formula.satisfies, member_m,
    Arguments.eval, Term.eval_weakenBound, Term.eval, hc, hw, ho] at hTotal hUnique hRange hOnto
  have hR₂ (a b : PowerlessMemberStructure.type_l C) := relation_formula_l φ
    ((ζ.pushBound a.val).pushBound b.val) (up (up c)) (.bvar (.there .here)) (.bvar .here)
    (lift_m (lift_m τ)) η a b (by simpa only [up, Term.eval_weakenBound] using hc) rfl rfl
    (fun v => by simpa only [lift_m, up, Term.eval_weakenBound] using hτ v)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨b, hbC, hb⟩ := hTotal x.val hx
    let y : PowerlessMemberStructure.type_l C := ⟨b, hbC⟩
    refine ⟨y, (hR₂ x y).mp hb, ?_⟩
    intro z hz
    apply Subtype.ext
    have hRxz := relation_formula_l φ (((ζ.pushBound x.val).pushBound z.val).pushBound y.val)
      (up (up (up c))) (.bvar (.there (.there .here))) (.bvar (.there .here))
      (lift_m (lift_m (lift_m τ))) η x z
      (by simpa only [up, Term.eval_weakenBound] using hc) rfl rfl
      (fun v => by simpa only [lift_m, up, Term.eval_weakenBound] using hτ v)
    have hRxy := relation_formula_l φ (((ζ.pushBound x.val).pushBound z.val).pushBound y.val)
      (up (up (up c))) (.bvar (.there (.there .here))) (.bvar .here)
      (lift_m (lift_m (lift_m τ))) η x y
      (by simpa only [up, Term.eval_weakenBound] using hc) rfl rfl
      (fun v => by simpa only [lift_m, up, Term.eval_weakenBound] using hτ v)
    exact hUnique x.val z.val y.val hx z.property y.property (hRxz.mpr hz)
      (hRxy.mpr ((hR₂ x y).mp hb))
  · intro x y hx hφ
    exact hRange x.val y.val hx y.property ((hR₂ x y).mpr hφ)
  · intro y hy
    obtain ⟨a, haω, ha⟩ := hOnto y.val hy
    let x : PowerlessMemberStructure.type_l C := ⟨a, hCT ω a hωC haω⟩
    refine ⟨x, haω, ?_⟩
    exact (relation_formula_l φ ((ζ.pushBound y.val).pushBound x.val) (up (up c))
      (.bvar .here) (.bvar (.there .here)) (lift_m (lift_m τ)) η x y
      (by simpa only [up, Term.eval_weakenBound] using hc) rfl rfl
      (fun v => by simpa only [lift_m, up, Term.eval_weakenBound] using hτ v)).mp ha

private abbrev context_m (Δ : SortContext ℒ) := .set :: .set :: .set :: .set :: Δ

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ [] (context_m Δ) :=
  let C : Term ℒ [] (context_m Δ) .set := .fvar .here
  let Ω := .fvar (.there .here)
  let ω := .fvar (.there (.there .here))
  let B := .fvar (.there (.there (.there .here)))
  let τ : Variable Δ .set → Term ℒ [] (context_m Δ) .set :=
    fun v => .fvar (.there (.there (.there (.there v))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
        .imp (PowerlessRelativeHierarchySyntax.level_m B Ω C) <| .imp (member_m ω C) <|
          .imp (PowerlessRelativeLimitDeltaSeparationDerives.parameters_m Δ C (fun v => τ v))
            (.neg (constraints_m φ C ω Ω τ))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) : (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hω hΩ hLevel hωC hParams h
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η
    (.fvar (.there (.there (.there .here))))).mp hBase
  have hω' := (SecondOrderOmegaSyntax.omega_l (hℳ := hℳ) η (.fvar (.there (.there .here)))).mp hω
  have hΩ' := (PowerlessRelativeOrdinalCutoff.first_formula_l K η
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here))) (.fvar (.there .here))).mp hΩ
  have hLevel' := (PowerlessRelativeHierarchySemantics.level_formula_l K η
    (.fvar (.there (.there (.there .here)))) (.fvar (.there .here)) (.fvar .here)).mp hLevel
  have hParams' := (PowerlessRelativeLimitDeltaSeparationDerives.parameters_formula_l Δ η (.fvar .here)
    (fun v => .fvar (.there (.there (.there (.there v)))))).mp hParams
  let ξ : Env (PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ)
    (η.freeVal .here) (Exists.intro (η.freeVal (.there (.there .here))) hωC)) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with
        | .set => ⟨η.freeVal (.there (.there (.there (.there v)))), hParams' _ v⟩ }
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase' hLevel'
  have hCT : PowerlessNaturalOrder.transitive_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (η.freeVal .here) := fun x y hx hy => hTrans x hx y hy
  obtain ⟨hTotal, hRange, hOnto⟩ := certificates_l hCT hωC φ η
    (.fvar .here) (.fvar (.there (.there .here))) (.fvar (.there .here))
    (fun v => .fvar (.there (.there (.there (.there v))))) ξ rfl rfl rfl (fun _ => rfl) h
  exact SecondOrderCutoffDefinableSurjection.impossible_l K hBase' hω' hΩ' hLevel' hωC φ ξ
    hTotal hRange hOnto

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCutoffDefinableSurjectionDerives
