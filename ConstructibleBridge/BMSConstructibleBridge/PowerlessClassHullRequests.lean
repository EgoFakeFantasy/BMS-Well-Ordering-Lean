import BMSConstructibleBridge.SecondOrderCanonicalClassSkolem
import BMSConstructibleBridge.PowerlessRelativeClassPair
import BMSConstructibleBridge.PowerlessSourceFamily

/-! # 有限壳的实际区分与单集请求

纯隶属语言、原 Z₂。给原有限请求族添加两个真实请求：在两个不同
Class 对象间取隶属区分见证，以及为 Class 对象构造真实单集上邻。
请求使用不同标签的嵌套有序对，不用无标签析取，也不调用要求完整
PowerlessTheory 的旧拆分定理。规范 Class Skolem 的实际输出保留这些
原请求的见证规格；其总存在性复用原 result_l，程序代表另由真实调用
闭包装配。这里尚不把虚拟外延性或全部代码的域域覆盖当作已证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassHullRequests

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) :=
  v.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up v)
private abbrev up₄ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up₂ (up₂ v)
private abbrev up₅ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up₄ v)

def difference_m {Γ Δ : SortContext ℒ} (x y z : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .neg (.iff (SecondOrderObjectSyntax.member_m z x) (SecondOrderObjectSyntax.member_m z y))

def separate_m {Δ : SortContext ℒ} : Formula ℒ [] (.set :: .set :: Δ) :=
  .existsE .set <| .existsE .set <|
    .conj (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here)
      (.fvar (.there .here)))
      (difference_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))

def upper_m {Δ : SortContext ℒ} : Formula ℒ [] (.set :: .set :: Δ) :=
  SecondOrderObjectSyntax.pair_m (.fvar (.there .here)) (.fvar (.there .here)) (.fvar .here)

def family_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (s t : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: .set :: Δ) :=
  PowerlessSourceFamily.family_m s t (separate_m :: upper_m :: Φ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

theorem difference_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (x y z : Term ℒ Γ Δ .set) :
    (difference_m x y z).satisfies η ↔ ¬(ε (z.eval η) (x.eval η) ↔ ε (z.eval η) (y.eval η)) := by
  rfl

theorem separate_formula_l {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ) (p z : Raw) :
    (separate_m (Δ := Δ)).satisfies ((η.pushFree p).pushFree z) ↔
      ∃ x y, ordered_l (ℳ := 𝒱) x y p ∧ ¬(ε z x ↔ ε z y) := by
  simp only [separate_m, Formula.satisfies, ordered_formula_l, difference_formula_l,
    Term.eval, Env.pushBound_bound_here,
    Env.pushBound_bound_there]
  rfl

theorem upper_formula_l {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ) (x z : Raw) :
    (upper_m (Δ := Δ)).satisfies ((η.pushFree x).pushFree z) ↔
      SecondOrderPairObjects.pair_l hℳ x x z := by
  simpa only [upper_m, Term.eval, Env.pushFree_here, Env.pushFree_there] using
    SecondOrderObjectSyntax.pair_l hℳ ((η.pushFree x).pushFree z)
      (.fvar (.there .here)) (.fvar (.there .here)) (.fvar .here)

/-- 只用原 Z₂ 的有序对单射性，避免要求完整源理论。 -/
theorem left_l {Δ : SortContext ℒ} (φ ψ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (s t : Term ℒ [] Δ .set) (hst : s.eval η ≠ t.eval η)
    {p x : Raw} (hp : ordered_l (ℳ := 𝒱) (s.eval η) x p) (y : Raw) :
    (PowerlessSourceFamily.sum_m φ ψ s t).satisfies ((η.pushFree p).pushFree y) ↔
      φ.satisfies ((η.pushFree x).pushFree y) := by
  rw [PowerlessSourceFamily.sum_formula_l]
  constructor
  · rintro ⟨z, ⟨hz, hφ⟩ | ⟨hz, _⟩⟩
    · have hzx := ((SecondOrderPairObjects.ordered_eq_l hℳ hz hp).mp rfl).2
      exact hzx ▸ hφ
    · exact (hst ((SecondOrderPairObjects.ordered_eq_l hℳ hp hz).mp rfl).1).elim
  · intro hφ
    exact ⟨x, Or.inl ⟨hp, hφ⟩⟩

theorem right_l {Δ : SortContext ℒ} (φ ψ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (s t : Term ℒ [] Δ .set) (hst : s.eval η ≠ t.eval η)
    {p x : Raw} (hp : ordered_l (ℳ := 𝒱) (t.eval η) x p) (y : Raw) :
    (PowerlessSourceFamily.sum_m φ ψ s t).satisfies ((η.pushFree p).pushFree y) ↔
      ψ.satisfies ((η.pushFree x).pushFree y) := by
  rw [PowerlessSourceFamily.sum_formula_l]
  constructor
  · rintro ⟨z, ⟨hz, _⟩ | ⟨hz, hψ⟩⟩
    · exact (hst ((SecondOrderPairObjects.ordered_eq_l hℳ hz hp).mp rfl).1).elim
    · have hzx := ((SecondOrderPairObjects.ordered_eq_l hℳ hz hp).mp rfl).2
      exact hzx ▸ hψ
  · intro hψ
    exact ⟨x, Or.inr ⟨hp, hψ⟩⟩

theorem separate_class_l {B x y : Raw}
    (hB : ∀ a, ε a B → ∀ b, ε b a → ε b B)
    (hx : PowerlessRelativeClassCorrespondence.member_l hℳ B x)
    (hy : PowerlessRelativeClassCorrespondence.member_l hℳ B y) (hxy : x ≠ y) :
    ∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z ∧ ¬(ε z x ↔ ε z y) := by
  classical
  have hSome : ∃ z, ¬(ε z x ↔ ε z y) := by
    by_contra h
    apply hxy
    apply SecondOrderQuotient.ext_l hℳ x y
    intro z
    by_contra hz
    exact h ⟨z, hz⟩
  obtain ⟨z, hz⟩ := hSome
  refine ⟨z, ?_, hz⟩
  by_cases hzx : ε z x
  · exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hB hx hzx
  · have hzy : ε z y := by
      by_contra hzy
      exact hz (iff_of_false hzx hzy)
    exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hB hy hzy

theorem upper_class_l {B x : Raw} (hB : ∀ a, ε a B → ∀ b, ε b a → ε b B)
    (hx : PowerlessRelativeClassCorrespondence.member_l hℳ B x) :
    ∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z ∧
      SecondOrderPairObjects.pair_l hℳ x x z := by
  obtain ⟨z, hz⟩ := SecondOrderPairObjects.pair_exists_l hℳ x x
  exact ⟨z, PowerlessRelativeClassPair.pair_l hℳ hB hx hx hz, hz⟩

theorem separate_l {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (η : Env 𝒱 [] Δ) (s t : Term ℒ [] Δ .set) (hst : s.eval η ≠ t.eval η)
    {ω e t₁ t₂ t₃ Pair Valid B P₀ x y p q z : Raw}
    (hB : ∀ a, ε a B → ∀ b, ε b a → ε b B)
    (hx : PowerlessRelativeClassCorrespondence.member_l hℳ B x)
    (hy : PowerlessRelativeClassCorrespondence.member_l hℳ B y) (hxy : x ≠ y)
    (hp : ordered_l (ℳ := 𝒱) x y p) (hq : ordered_l (ℳ := 𝒱) (s.eval η) p q)
    (hz : SecondOrderCanonicalClassSkolem.relation_l (family_m Φ s t) η
      ω e t₁ t₂ t₃ Pair Valid B P₀ q z) : ¬(ε z x ↔ ε z y) := by
  have hLeft (w : Raw) : (family_m Φ s t).satisfies ((η.pushFree q).pushFree w) ↔
      separate_m.satisfies ((η.pushFree p).pushFree w) :=
    left_l separate_m (PowerlessSourceFamily.family_m s t (upper_m :: Φ)) η s t hst hq w
  obtain ⟨w, hw, hDiff⟩ := separate_class_l hB hx hy hxy
  have hSome : ∃ w, PowerlessRelativeClassCorrespondence.member_l hℳ B w ∧
      (family_m Φ s t).satisfies ((η.pushFree q).pushFree w) :=
    ⟨w, hw, (hLeft w).mpr ((separate_formula_l η p w).mpr ⟨x, y, hp, hDiff⟩)⟩
  have h := (hLeft z).mp (SecondOrderCanonicalClassSkolem.witness_l (family_m Φ s t) η hz hSome)
  obtain ⟨a, b, hab, hz⟩ := (separate_formula_l η p z).mp h
  obtain ⟨ha, hb⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hab hp).mp rfl
  exact ha ▸ hb ▸ hz

theorem upper_l {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (η : Env 𝒱 [] Δ) (s t : Term ℒ [] Δ .set) (hst : s.eval η ≠ t.eval η)
    {ω e t₁ t₂ t₃ Pair Valid B P₀ x p q z : Raw}
    (hB : ∀ a, ε a B → ∀ b, ε b a → ε b B)
    (hx : PowerlessRelativeClassCorrespondence.member_l hℳ B x)
    (hp : ordered_l (ℳ := 𝒱) (s.eval η) x p) (hq : ordered_l (ℳ := 𝒱) (t.eval η) p q)
    (hz : SecondOrderCanonicalClassSkolem.relation_l (family_m Φ s t) η
      ω e t₁ t₂ t₃ Pair Valid B P₀ q z) : SecondOrderPairObjects.pair_l hℳ x x z := by
  have hRight (w : Raw) : (family_m Φ s t).satisfies ((η.pushFree q).pushFree w) ↔
      upper_m.satisfies ((η.pushFree x).pushFree w) :=
    (right_l separate_m (PowerlessSourceFamily.family_m s t (upper_m :: Φ)) η s t hst hq w).trans
      (left_l upper_m (PowerlessSourceFamily.family_m s t Φ) η s t hst hp w)
  obtain ⟨w, hw, hPair⟩ := upper_class_l hB hx
  have hSome : ∃ w, PowerlessRelativeClassCorrespondence.member_l hℳ B w ∧
      (family_m Φ s t).satisfies ((η.pushFree q).pushFree w) :=
    ⟨w, hw, (hRight w).mpr ((upper_formula_l η x w).mpr hPair)⟩
  exact (upper_formula_l η x z).mp ((hRight z).mp
    (SecondOrderCanonicalClassSkolem.witness_l (family_m Φ s t) η hz hSome))

def separate_effect_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let x : Term ℒ [.set, .set, .set, .set, .set] Δ .set := .bvar (.there (.there (.there (.there .here))))
    let y := .bvar (.there (.there (.there .here)))
    let p := .bvar (.there (.there .here))
    let q := .bvar (.there .here)
    let z := .bvar .here
    .imp (PowerlessRelativeHierarchySyntax.class_m (up₅ B) x) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m (up₅ B) y) <| .imp (.neg (.equal x y)) <|
        .imp (SecondOrderObjectSyntax.ordered_m x y p) <|
          .imp (SecondOrderObjectSyntax.ordered_m (up₅ s) p q) <|
            .imp (SecondOrderCanonicalClassSkolem.relation_m (family_m Φ s t)
              (up₅ ω) (up₅ e) (up₅ t₁) (up₅ t₂) (up₅ t₃) (up₅ Pair) (up₅ Valid)
              (up₅ B) (up₅ P₀) q z) (difference_m x y z)

def upper_effect_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let x : Term ℒ [.set, .set, .set, .set] Δ .set := .bvar (.there (.there (.there .here)))
    let p := .bvar (.there (.there .here))
    let q := .bvar (.there .here)
    let z := .bvar .here
    .imp (PowerlessRelativeHierarchySyntax.class_m (up₄ B) x) <|
      .imp (SecondOrderObjectSyntax.ordered_m (up₄ s) x p) <|
        .imp (SecondOrderObjectSyntax.ordered_m (up₄ t) p q) <|
          .imp (SecondOrderCanonicalClassSkolem.relation_m (family_m Φ s t)
            (up₄ ω) (up₄ e) (up₄ t₁) (up₄ t₂) (up₄ t₃) (up₄ Pair) (up₄ Valid)
            (up₄ B) (up₄ P₀) q z) (SecondOrderObjectSyntax.pair_m x x z)

def schema_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (.neg (.equal s t)) <|
      .conj (separate_effect_m Φ ω e t₁ t₂ t₃ Pair Valid B P₀ s t)
        (upper_effect_m Φ ω e t₁ t₂ t₃ Pair Valid B P₀ s t)

def sentence_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ s t : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ ω e t₁ t₂ t₃ Pair Valid B P₀ s t)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ s t : Term ℒ [] Δ .set) :
    (sentence_m Φ ω e t₁ t₂ t₃ Pair Valid B P₀ s t).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l]
  intro η hB hst
  constructor
  · simp only [separate_effect_m, Formula.satisfies,
      PowerlessRelativeHierarchySemantics.class_formula_l K,
      SecondOrderCanonicalClassSkolem.relation_formula_l K, ordered_formula_l, difference_formula_l,
      parameters_pushBound_l, parameters_empty_l, up₅, up₄, up₂, up, Term.eval_weakenBound,
      Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
    exact fun x y p q z hx hy hxy hp hq hz => separate_l Φ η s t hst hB hx hy hxy hp hq hz
  · simp only [upper_effect_m, Formula.satisfies,
      PowerlessRelativeHierarchySemantics.class_formula_l K,
      SecondOrderCanonicalClassSkolem.relation_formula_l K, ordered_formula_l,
      SecondOrderObjectSyntax.pair_l h𝒩, parameters_pushBound_l, parameters_empty_l,
      up₄, up₂, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, Env.pushBound_bound_there]
    exact fun x p q z hx hp hq hz => upper_l Φ η s t hst hB hx hp hq hz

theorem derives_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ s t : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ ω e t₁ t₂ t₃ Pair Valid B P₀ s t)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 Φ ω e t₁ t₂ t₃ Pair Valid B P₀ s t)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassHullRequests
