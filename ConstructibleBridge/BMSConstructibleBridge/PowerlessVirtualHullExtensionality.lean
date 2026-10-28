import BMSConstructibleBridge.PowerlessClassHullRequests
import BMSConstructibleBridge.PowerlessDefinableMembershipIsomorphism

/-! # 从真实有限请求闭包导出虚拟外延性与全码域覆盖

纯隶属语言、原 Z₂。虚拟域由代码母集上的原纯求值定义，不要求其为
实际集合。不同标签属于虚拟域，配对及规范算子调用在同一虚拟域闭合，
规范算子具有实际 Class 输出：这些建设性接口给区分见证及真实单集
上邻。前者消去同构定理的虚拟外延性守卫，后者让每个有输出的实际
代码成为隶属图的端点；代码求值总定义时，真实域域等于原代码母集。
公开出口是原对象推导模式。这些闭包／总化接口仍须由同一实际程序
装配，不把它们加成背景公理，也不宣称 T/H 属于 Class 或 Collection 完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessVirtualHullExtensionality

open Logic FirstOrder ThirdOrderSemantics
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l at_m at_formula_l)
open PowerlessDefinableMembershipIsomorphism (image_l image_formula_l ext_m ext_l ext_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) :=
  v.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up v)
private abbrev up₃ {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) := up (up₂ v)

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
local notation "ε" => SecondOrderQuotient.mem_l hℳ

theorem extensional_l {Δ : SortContext ℒ}
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ))) (η : Env 𝒱 [] Δ) (s t : Term ℒ [] Δ .set)
    {ω e t₁ t₂ t₃ Pair Valid B P₀ : Raw} (I : Raw → Prop)
    (hB : ∀ a, ε a B → ∀ b, ε b a → ε b B) (hst : s.eval η ≠ t.eval η)
    (hClass : ∀ x, I x → PowerlessRelativeClassCorrespondence.member_l hℳ B x)
    (hs : I (s.eval η))
    (hPair : ∀ x y, I x → I y → ∃ p, I p ∧ ordered_l (ℳ := 𝒱) x y p)
    (hCall : ∀ q z, I q → PowerlessRelativeClassCorrespondence.member_l hℳ B z →
      SecondOrderCanonicalClassSkolem.relation_l (PowerlessClassHullRequests.family_m Φ s t) η
        ω e t₁ t₂ t₃ Pair Valid B P₀ q z → I z)
    (hTotal : ∀ q, ∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z ∧
      SecondOrderCanonicalClassSkolem.relation_l (PowerlessClassHullRequests.family_m Φ s t) η
        ω e t₁ t₂ t₃ Pair Valid B P₀ q z) :
    ∀ x y, I x → I y → (∀ z, I z → (ε z x ↔ ε z y)) → x = y := by
  classical
  intro x y hx hy hExt
  by_contra hxy
  obtain ⟨p, hp, hxyP⟩ := hPair x y hx hy
  obtain ⟨q, hq, hspQ⟩ := hPair (s.eval η) p hs hp
  obtain ⟨z, hz, hRel⟩ := hTotal q
  have hzI := hCall q z hq hz hRel
  exact (PowerlessClassHullRequests.separate_l Φ η s t hst hB (hClass x hx) (hClass y hy)
    hxy hxyP hspQ hRel) (hExt z hzI)

theorem upper_l {Δ : SortContext ℒ}
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ))) (η : Env 𝒱 [] Δ) (s t : Term ℒ [] Δ .set)
    {ω e t₁ t₂ t₃ Pair Valid B P₀ : Raw} (I : Raw → Prop)
    (hB : ∀ a, ε a B → ∀ b, ε b a → ε b B) (hst : s.eval η ≠ t.eval η)
    (hClass : ∀ x, I x → PowerlessRelativeClassCorrespondence.member_l hℳ B x)
    (hs : I (s.eval η)) (ht : I (t.eval η))
    (hPair : ∀ x y, I x → I y → ∃ p, I p ∧ ordered_l (ℳ := 𝒱) x y p)
    (hCall : ∀ q z, I q → PowerlessRelativeClassCorrespondence.member_l hℳ B z →
      SecondOrderCanonicalClassSkolem.relation_l (PowerlessClassHullRequests.family_m Φ s t) η
        ω e t₁ t₂ t₃ Pair Valid B P₀ q z → I z)
    (hTotal : ∀ q, ∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z ∧
      SecondOrderCanonicalClassSkolem.relation_l (PowerlessClassHullRequests.family_m Φ s t) η
        ω e t₁ t₂ t₃ Pair Valid B P₀ q z) :
    ∀ x, I x → ∃ z, I z ∧ SecondOrderPairObjects.pair_l hℳ x x z := by
  intro x hx
  obtain ⟨p, hp, hsxP⟩ := hPair (s.eval η) x hs hx
  obtain ⟨q, hq, htpQ⟩ := hPair (t.eval η) p ht hp
  obtain ⟨z, hz, hRel⟩ := hTotal q
  exact ⟨z, hCall q z hq hz hRel,
    PowerlessClassHullRequests.upper_l Φ η s t hst hB (hClass x hx) hsxP htpQ hRel⟩

theorem domain_l {Δ : SortContext ℒ} (θ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    {C A D : Raw} (hA : PowerlessDefinableMembershipDiagram.spec_l θ η C A)
    (hD : PowerlessDefinableMembershipCollapse.domain_l (𝒩 := 𝒱) A D)
    (hCode : ∀ n, ε n C → ∃ x, θ.satisfies ((η.pushFree n).pushFree x))
    (hUpper : ∀ x, image_l θ η C x → ∃ z, image_l θ η C z ∧
      SecondOrderPairObjects.pair_l hℳ x x z) : D = C := by
  apply SecondOrderQuotient.ext_l hℳ D C
  intro n
  constructor
  · exact PowerlessDefinableMembershipIsomorphism.domain_subset_l θ η hA hD n
  · intro hn
    obtain ⟨x, hx⟩ := hCode n hn
    obtain ⟨z, ⟨m, hm, hmz⟩, hPair⟩ := hUpper x ⟨n, hn, hx⟩
    have hxz : ε x z := (hPair x).mpr (Or.inl rfl)
    have hEdge := (PowerlessDefinableMembershipDiagram.value_iff_l θ η hA n m).mpr
      ⟨hn, hm, x, z, hx, hmz, hxz⟩
    exact (hD n).mpr ⟨m, Or.inl hEdge⟩

def class_m {Γ Δ : SortContext ℒ} (θ : Formula ℒ [] (.set :: .set :: Δ))
    (B C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (image_m θ (up C) (.bvar .here))
    (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here))

def pair_m {Γ Δ : SortContext ℒ} (θ : Formula ℒ [] (.set :: .set :: Δ))
    (C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .imp (image_m θ (up₂ C) (.bvar (.there .here))) <|
    .imp (image_m θ (up₂ C) (.bvar .here)) <| .existsE .set <|
      .conj (image_m θ (up₃ C) (.bvar .here))
        (SecondOrderObjectSyntax.ordered_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))

def call_m {Δ : SortContext ℒ} (θ : Formula ℒ [] (.set :: .set :: Δ))
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ C s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .forallE .set <| .forallE .set <| .imp (image_m θ (up₂ C) (.bvar (.there .here))) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m (up₂ B) (.bvar .here)) <|
      .imp (SecondOrderCanonicalClassSkolem.relation_m (PowerlessClassHullRequests.family_m Φ s t)
        (up₂ ω) (up₂ e) (up₂ t₁) (up₂ t₂) (up₂ t₃) (up₂ Pair) (up₂ Valid)
        (up₂ B) (up₂ P₀) (.bvar (.there .here)) (.bvar .here))
        (image_m θ (up₂ C) (.bvar .here))

def total_m {Δ : SortContext ℒ} (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .forallE .set <| .existsE .set <|
    .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) (.bvar .here))
      (SecondOrderCanonicalClassSkolem.relation_m (PowerlessClassHullRequests.family_m Φ s t)
        (up₂ ω) (up₂ e) (up₂ t₁) (up₂ t₂) (up₂ t₃) (up₂ Pair) (up₂ Valid)
        (up₂ B) (up₂ P₀) (.bvar (.there .here)) (.bvar .here))

def code_total_m {Δ : SortContext ℒ} (θ : Formula ℒ [] (.set :: .set :: Δ))
    (C : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up C)) <|
    .existsE .set <| at_m θ (.bvar (.there .here)) (.bvar .here)

def upper_m {Γ Δ : SortContext ℒ} (θ : Formula ℒ [] (.set :: .set :: Δ))
    (C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (image_m θ (up C) (.bvar .here)) <| .existsE .set <|
    .conj (image_m θ (up₂ C) (.bvar .here))
      (SecondOrderObjectSyntax.pair_m (.bvar (.there .here)) (.bvar (.there .here)) (.bvar .here))

def schema_m {Δ : SortContext ℒ} (θ : Formula ℒ [] (.set :: .set :: Δ))
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ C A D s t : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <| .imp (.neg (.equal s t)) <|
    .imp (class_m θ B C) <| .imp (image_m θ C s) <| .imp (image_m θ C t) <|
      .imp (pair_m θ C) <| .imp (call_m θ Φ ω e t₁ t₂ t₃ Pair Valid B P₀ C s t) <|
        .imp (total_m Φ ω e t₁ t₂ t₃ Pair Valid B P₀ s t) <|
          .imp (PowerlessDefinableMembershipDiagram.spec_m θ C A) <|
            .imp (PowerlessDefinableMembershipCollapse.domain_m A D) <| .imp (code_total_m θ C) <|
              .conj (ext_m θ C (fun v => .fvar v))
                (.conj (upper_m θ C) (.equal D C))

def sentence_m {Δ : SortContext ℒ} (θ : Formula ℒ [] (.set :: .set :: Δ))
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ C A D s t : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m θ Φ ω e t₁ t₂ t₃ Pair Valid B P₀ C A D s t)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (θ : Formula ℒ [] (.set :: .set :: Δ)) (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ C A D s t : Term ℒ [] Δ .set) :
    (sentence_m θ Φ ω e t₁ t₂ t₃ Pair Valid B P₀ C A D s t).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, class_m, pair_m, call_m, total_m, code_total_m, image_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, image_formula_l,
    SecondOrderCanonicalClassSkolem.relation_formula_l K, ordered_formula_l, at_formula_l,
    PowerlessDefinableMembershipDiagram.spec_formula_l,
    PowerlessDefinableMembershipCollapse.domain_formula_l,
    env_id_l, parameters_pushBound_l, parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₃, up₂, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hB hst hClass hs ht hPair hCall hTotal hA hD hCode
  let I := image_l θ η (C.eval η)
  have hUpper := upper_l Φ η s t I hB hst hClass hs ht hPair hCall hTotal
  simp only [upper_m, image_m, Formula.satisfies, image_formula_l, ext_formula_l,
    SecondOrderObjectSyntax.pair_l h𝒩, env_id_l, parameters_pushBound_l, parameters_empty_l,
    up₂, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  exact ⟨extensional_l Φ η s t I hB hst hClass hs hPair hCall hTotal, hUpper,
    domain_l θ η hA hD hCode hUpper⟩

theorem derives_m {Δ : SortContext ℒ} (θ : Formula ℒ [] (.set :: .set :: Δ))
    (Φ : List (Formula ℒ [] (.set :: .set :: Δ)))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ C A D s t : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m θ Φ ω e t₁ t₂ t₃ Pair Valid B P₀ C A D s t)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 θ Φ ω e t₁ t₂ t₃ Pair Valid B P₀ C A D s t)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessVirtualHullExtensionality
