import BMSConstructibleBridge.PowerlessRelativeFiniteProgramStep
import BMSConstructibleBridge.PowerlessRelativeLimitFunctionAppend

/-! # 实际程序单步保持同一非零极限层

常量母集只需包含于层，算子只需将层内输入的 Class 输出留在该层。
从真实旧状态的 Kuratowski 坐标读出域、陪域和图，再用精确单点
存储规格证明新状态仍在同层。包括非法状态／指令的缺省分支；
不预设无限求值图、求值像集合或完整 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramLimitStep

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessRelativeLimitFunctionAppend (adjoin_l)
open PowerlessBMSQuotientSubsetImageDerives
  (at_m at_formula_l parameters_l parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def closed_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B W : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let x : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let y := .bvar .here
    .imp (SecondOrderObjectSyntax.member_m x (up₂ W)) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m (up₂ B) y) <|
        .imp (at_m φ x y) (SecondOrderObjectSyntax.member_m y (up₂ W))

def result_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω w e t₀ t₁ t₂ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let s : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let t := .bvar .here
    .imp (SecondOrderObjectSyntax.member_m s (up₂ W)) <|
      .imp (PowerlessRelativeFiniteProgramStep.step_m φ
        (up₂ B) (up₂ C) (up₂ ω) (up₂ w) (up₂ e) (up₂ t₀) (up₂ t₁) (up₂ t₂) s t)
        (SecondOrderObjectSyntax.member_m t (up₂ W))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def closed_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B W : type_l hℳ) : Prop :=
  ∀ x y, mem_l hℳ x W → PowerlessRelativeClassCorrespondence.member_l hℳ B y →
    φ.satisfies ((η.pushFree x).pushFree y) → mem_l hℳ y W

theorem closed_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ) (B W : Term ℒ Γ Δ .set) :
    (closed_m φ B W).satisfies η ↔ closed_l φ (parameters_l η) (B.eval η) (W.eval η) := by
  simp only [closed_m, closed_l, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, at_formula_l,
    parameters_pushBound_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up₂, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

-- 有界历史和实际末态共用同一 Kuratowski 坐标界，不另换编码约定。
theorem coordinates_l {W x y p : type_l hℳ}
    (hW : ∀ a, mem_l hℳ a W → ∀ b, mem_l hℳ b a → mem_l hℳ b W)
    (hpW : mem_l hℳ p W) (hp : ordered_l (ℳ := 𝒱) x y p) :
    mem_l hℳ x W ∧ mem_l hℳ y W := by
  obtain ⟨_, t, _, ht, hp⟩ := hp
  have htW := hW p hpW t ((hp t).mpr (Or.inr rfl))
  exact ⟨hW t htW x ((ht x).mpr (Or.inl rfl)), hW t htW y ((ht y).mpr (Or.inr rfl))⟩

theorem reading_l {W f k x : type_l hℳ}
    (hW : ∀ a, mem_l hℳ a W → ∀ b, mem_l hℳ b a → mem_l hℳ b W)
    (hfW : mem_l hℳ f W) (hx : value_l (ℳ := 𝒱) f k x) : mem_l hℳ x W := by
  obtain ⟨p, hp, hx⟩ := hx
  exact (coordinates_l hW (hW f hfW p hp) hx).2

theorem good_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B β W C f t₀ t₁ t₂ q y : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hCW : ∀ x, mem_l hℳ x C → mem_l hℳ x W) (hfW : mem_l hℳ f W)
    (hφ : closed_l φ η B W)
    (hy : PowerlessRelativeFiniteProgramInstruction.good_l φ η B C f t₀ t₁ t₂ q y) :
    mem_l hℳ y W := by
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hB hW
  rcases hy with ⟨x, _, hx, rfl⟩ | ⟨_, x, _, hx, hyC, hxy⟩ |
    ⟨_, _, _, x, z, _, _, hx, hz, hxy⟩
  · exact hCW _ hx
  · exact hφ x y (reading_l hTrans hfW hx) hyC hxy
  · exact PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW
      (reading_l hTrans hfW hx) (reading_l hTrans hfW hz) hxy

theorem computed_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B β W C f t₀ t₁ t₂ q y : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W) (hBW : mem_l hℳ B W)
    (hCW : ∀ x, mem_l hℳ x C → mem_l hℳ x W) (hfW : mem_l hℳ f W)
    (hφ : closed_l φ η B W)
    (hy : PowerlessRelativeFiniteProgramInstruction.computed_l φ η B C f t₀ t₁ t₂ q y) :
    mem_l hℳ y W := by
  rcases hy.2 with hy | ⟨_, rfl⟩
  · exact good_l φ η hB hβ hW hCW hfW hφ hy
  · exact hBW

theorem store_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B β W C A D f c t₀ t₁ t₂ q S E g : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W) (hBW : mem_l hℳ B W)
    (hCW : ∀ x, mem_l hℳ x C → mem_l hℳ x W)
    (hA : mem_l hℳ A W) (hD : mem_l hℳ D W) (hf : mem_l hℳ f W) (hc : mem_l hℳ c W)
    (hMap : map_l (ℳ := 𝒱) f A D) (hφ : closed_l φ η B W)
    (hg : PowerlessRelativeFiniteProgramStore.store_l φ η B C A D f c t₀ t₁ t₂ q S E g) :
    mem_l hℳ S W ∧ mem_l hℳ E W ∧ mem_l hℳ g W := by
  obtain ⟨y, hy, _, _, _, hS, hE, hg, hRead⟩ := hg
  have hyW := computed_l φ η hB hβ hW hBW hCW hf hφ hy
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ c y
  have hpW := PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW hc hyW hp
  refine ⟨adjoin_l hB hβ hW hA hc hS, adjoin_l hB hβ hW hD hyW hE, ?_⟩
  apply adjoin_l hB hβ hW hf hpW
  intro t
  constructor
  · intro ht
    obtain ⟨x, z, _, _, hxz⟩ := hg.1 t ht
    rcases (hRead x z).mp ⟨t, ht, hxz⟩ with h | ⟨rfl, rfl⟩
    · obtain ⟨u, hu, huxz⟩ := h
      exact Or.inl ((SecondOrderPairObjects.ordered_unique_l hℳ hxz huxz).symm ▸ hu)
    · exact Or.inr (SecondOrderPairObjects.ordered_unique_l hℳ hxz hp)
  · rintro (ht | rfl)
    · obtain ⟨x, z, _, _, hxz⟩ := hMap.1 t ht
      obtain ⟨u, hu, huxz⟩ := (hRead x z).mpr (Or.inl ⟨t, ht, hxz⟩)
      exact (SecondOrderPairObjects.ordered_unique_l hℳ hxz huxz).symm ▸ hu
    · obtain ⟨u, hu, hucy⟩ := (hRead c y).mpr (Or.inr ⟨rfl, rfl⟩)
      exact (SecondOrderPairObjects.ordered_unique_l hℳ hp hucy).symm ▸ hu

theorem step_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B β W C ω w e t₀ t₁ t₂ s t : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W) (hBW : mem_l hℳ B W)
    (hCW : ∀ x, mem_l hℳ x C → mem_l hℳ x W) (hφ : closed_l φ η B W)
    (hs : mem_l hℳ s W)
    (ht : PowerlessRelativeFiniteProgramStep.step_l φ η B C ω w e t₀ t₁ t₂ s t) :
    mem_l hℳ t W := by
  rcases ht.2 with ht | ⟨_, rfl⟩
  · obtain ⟨i, D, f, q, S, E, g, hValid, _, hStore, hRecord⟩ := ht
    obtain ⟨p, hDf, hip⟩ := hValid.1
    have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hB hW
    obtain ⟨hiW, hpW⟩ := coordinates_l hTrans hs hip
    obtain ⟨hDW, hfW⟩ := coordinates_l hTrans hpW hDf
    obtain ⟨hSW, hEW, hgW⟩ := store_l φ η hB hβ hW hBW hCW
      hiW hDW hfW hiW hValid.2.2.2.2.2 hφ hStore
    obtain ⟨p, hEg, hSp⟩ := hRecord
    exact PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW hSW
      (PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW hEW hgW hEg) hSp
  · exact hBW

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β W C ω w e t₀ t₁ t₂ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .imp (SecondOrderObjectSyntax.member_m B W) <|
          .imp (ThirdOrderTheory.subset_m C W) <| .imp (closed_m φ B W)
            (result_m φ B C W ω w e t₀ t₁ t₂)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β W C ω w e t₀ t₁ t₂ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B β W C ω w e t₀ t₁ t₂)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B β W C ω w e t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    (sentence_m φ B β W C ω w e t₀ t₁ t₂).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, result_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.limit_formula_l, PowerlessRelativeHierarchySemantics.level_formula_l K,
    closed_formula_l K, PowerlessRelativeFiniteProgramStep.step_formula_l K,
    subset_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    parameters_pushBound_l, parameters_empty_l, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hB hβ hW hBW hCW hφ s t hs ht
  exact step_l φ η hB hβ hW hBW hCW hφ hs ht

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β W C ω w e t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B β W C ω w e t₀ t₁ t₂)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B β W C ω w e t₀ t₁ t₂)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramLimitStep
