import BMSConstructibleBridge.PowerlessVirtualHullExtensionality

/-! # 虚拟壳对原有限请求的真实见证闭包

纯隶属语言、原 Z₂。逐一沿原有限请求族的实际标签路径构造查询；
同一虚拟域的配对与规范调用闭包捕获原请求的 Class 见证。原公式及
原自由参数不变，不用无标签析取，不要求虚拟域是集合，也不调用
需要完整 Collection 的旧 family_closed_l。
本出口是明确闭包守卫下的原 Derives 模式。它不把任意 raw 见证
假称 Class；向 W 的有限元素性过渡仍须证明原请求的候选域与 W 对应。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessVirtualHullRequests

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l at_m at_formula_l)
open PowerlessDefinableMembershipIsomorphism (image_l image_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) :=
  v.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up v)

private abbrev image_m {Γ Δ : SortContext ℒ} (θ : Formula ℒ [] (.set :: .set :: Δ))
    (C x : Term ℒ Γ Δ .set) :=
  PowerlessDefinableMembershipIsomorphism.image_m θ C x (fun v => .fvar v)

private theorem env_id_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) : PowerlessDefinableMembershipDiagram.env_l η (fun v => .fvar v) = parameters_l η := by
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s; rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

/-- 查询由真实有序对构成；原成员请求在该查询处逐输出精确对应。 -/
theorem query_l {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ) (s t : Term ℒ [] Δ .set)
    (I : Raw → Prop) (hst : s.eval η ≠ t.eval η) (hs : I (s.eval η)) (ht : I (t.eval η))
    (hPair : ∀ x y, I x → I y → ∃ p, I p ∧ ordered_l (ℳ := 𝒱) x y p)
    (hφ : φ ∈ Φ) (x : Raw) (hx : I x) :
    ∃ q, I q ∧ ∀ y, (PowerlessSourceFamily.family_m s t Φ).satisfies ((η.pushFree q).pushFree y) ↔
      φ.satisfies ((η.pushFree x).pushFree y) := by
  match Φ with
  | [] => exact (List.not_mem_nil hφ).elim
  | ψ :: Φ =>
    rcases List.mem_cons.mp hφ with rfl | hφ
    · obtain ⟨q, hq, hsx⟩ := hPair (s.eval η) x hs hx
      exact ⟨q, hq, fun y => PowerlessClassHullRequests.left_l φ
        (PowerlessSourceFamily.family_m s t Φ) η s t hst hsx y⟩
    · obtain ⟨p, hp, hRead⟩ := query_l Φ φ η s t I hst hs ht hPair hφ x hx
      obtain ⟨q, hq, htp⟩ := hPair (t.eval η) p ht hp
      exact ⟨q, hq, fun y => (PowerlessClassHullRequests.right_l ψ
        (PowerlessSourceFamily.family_m s t Φ) η s t hst htp y).trans (hRead y)⟩

theorem witness_l {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (η : Env 𝒱 [] Δ) (s t : Term ℒ [] Δ .set)
    {ω e t₁ t₂ t₃ Pair Valid B P₀ : Raw} (I : Raw → Prop)
    (hst : s.eval η ≠ t.eval η) (hs : I (s.eval η)) (ht : I (t.eval η))
    (hPair : ∀ x y, I x → I y → ∃ p, I p ∧ ordered_l (ℳ := 𝒱) x y p)
    (hCall : ∀ q z, I q → PowerlessRelativeClassCorrespondence.member_l hℳ B z →
      SecondOrderCanonicalClassSkolem.relation_l (PowerlessClassHullRequests.family_m Φ s t) η
        ω e t₁ t₂ t₃ Pair Valid B P₀ q z → I z)
    (hTotal : ∀ q, ∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z ∧
      SecondOrderCanonicalClassSkolem.relation_l (PowerlessClassHullRequests.family_m Φ s t) η
        ω e t₁ t₂ t₃ Pair Valid B P₀ q z)
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (hφ : φ ∈ Φ)
    (x : Raw) (hx : I x)
    (hSome : ∃ y, PowerlessRelativeClassCorrespondence.member_l hℳ B y ∧
      φ.satisfies ((η.pushFree x).pushFree y)) :
    ∃ y, I y ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  obtain ⟨q, hq, hRead⟩ := query_l
    (PowerlessClassHullRequests.separate_m :: PowerlessClassHullRequests.upper_m :: Φ)
    φ η s t I hst hs ht hPair (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hφ)) x hx
  obtain ⟨z, hz, hRel⟩ := hTotal q
  have hSome' : ∃ y, PowerlessRelativeClassCorrespondence.member_l hℳ B y ∧
      (PowerlessClassHullRequests.family_m Φ s t).satisfies ((η.pushFree q).pushFree y) := by
    obtain ⟨y, hy, hφy⟩ := hSome
    exact ⟨y, hy, (hRead y).mpr hφy⟩
  exact ⟨z, hCall q z hq hz hRel, (hRead z).mp
    (SecondOrderCanonicalClassSkolem.witness_l _ η hRel hSome')⟩

def closed_m {Γ Δ : SortContext ℒ} (θ φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (image_m θ (up C) (.bvar .here)) <|
    .imp (.existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) (.bvar .here))
      (at_m φ (.bvar (.there .here)) (.bvar .here))) <|
      .existsE .set <| .conj (image_m θ (up₂ C) (.bvar .here))
        (at_m φ (.bvar (.there .here)) (.bvar .here))

theorem closed_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (θ φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ) (B C : Term ℒ Γ Δ .set) :
    (closed_m θ φ B C).satisfies η ↔
      ∀ x, image_l θ (parameters_l η) (C.eval η) x →
        (∃ y, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y ∧
          φ.satisfies (((parameters_l η).pushFree x).pushFree y)) →
            ∃ y, image_l θ (parameters_l η) (C.eval η) y ∧
              φ.satisfies (((parameters_l η).pushFree x).pushFree y) := by
  simp only [closed_m, image_m, Formula.satisfies, image_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, at_formula_l, env_id_l,
    parameters_pushBound_l, up₂, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

def requests_m {Γ Δ : SortContext ℒ} (θ : Formula ℒ [] (.set :: .set :: Δ))
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ))) (B C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  match Φ with
  | [] => .truth
  | φ :: Φ => .conj (closed_m θ φ B C) (requests_m θ Φ B C)

theorem requests_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (θ : Formula ℒ [] (.set :: .set :: Δ)) (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (η : Env 𝒩 Γ Δ) (B C : Term ℒ Γ Δ .set) :
    (requests_m θ Φ B C).satisfies η ↔ ∀ φ ∈ Φ, (closed_m θ φ B C).satisfies η := by
  induction Φ with
  | nil => exact ⟨fun _ φ hφ => (List.not_mem_nil hφ).elim, fun _ => True.intro⟩
  | cons ψ Φ ih =>
    change ((closed_m θ ψ B C).satisfies η ∧ (requests_m θ Φ B C).satisfies η) ↔ _
    rw [ih]
    constructor
    · rintro ⟨hψ, hΦ⟩ φ hφ
      rcases List.mem_cons.mp hφ with rfl | hφ
      · exact hψ
      · exact hΦ φ hφ
    · intro h
      exact ⟨h ψ List.mem_cons_self, fun φ hφ => h φ (List.mem_cons_of_mem _ hφ)⟩

def schema_m {Δ : SortContext ℒ} (θ : Formula ℒ [] (.set :: .set :: Δ))
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ C s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (.neg (.equal s t)) <| .imp (image_m θ C s) <| .imp (image_m θ C t) <|
    .imp (PowerlessVirtualHullExtensionality.pair_m θ C) <|
      .imp (PowerlessVirtualHullExtensionality.call_m θ Φ ω e t₁ t₂ t₃ Pair Valid B P₀ C s t) <|
        .imp (PowerlessVirtualHullExtensionality.total_m Φ ω e t₁ t₂ t₃ Pair Valid B P₀ s t)
          (requests_m θ Φ B C)

def sentence_m {Δ : SortContext ℒ} (θ : Formula ℒ [] (.set :: .set :: Δ))
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ C s t : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m θ Φ ω e t₁ t₂ t₃ Pair Valid B P₀ C s t)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (θ : Formula ℒ [] (.set :: .set :: Δ)) (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ C s t : Term ℒ [] Δ .set) :
    (sentence_m θ Φ ω e t₁ t₂ t₃ Pair Valid B P₀ C s t).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessVirtualHullExtensionality.pair_m,
    PowerlessVirtualHullExtensionality.call_m, PowerlessVirtualHullExtensionality.total_m,
    image_m, image_formula_l, ordered_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    SecondOrderCanonicalClassSkolem.relation_formula_l K,
    env_id_l, parameters_pushBound_l, parameters_empty_l,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hst hs ht hPair hCall hTotal
  apply (requests_formula_l θ Φ η B C).mpr
  intro φ hφ
  apply (closed_formula_l K θ φ η B C).mpr
  simp only [parameters_empty_l]
  exact witness_l Φ η s t (image_l θ η (C.eval η)) hst hs ht hPair hCall hTotal φ hφ

theorem derives_m {Δ : SortContext ℒ} (θ : Formula ℒ [] (.set :: .set :: Δ))
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ C s t : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m θ Φ ω e t₁ t₂ t₃ Pair Valid B P₀ C s t)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 θ Φ ω e t₁ t₂ t₃ Pair Valid B P₀ C s t)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessVirtualHullRequests
