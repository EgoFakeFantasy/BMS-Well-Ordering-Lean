import BMSConstructibleBridge.PowerlessRelativeFiniteProgramInstruction

/-! # 指令执行的精确 Class 存储图延拓

指令求值和新存储图都是原对象；输入坐标必须尚未使用。
新图保留全部旧坐标，恰加入指令的唯一输出，扩大定义域与陪域。
域、陪域与图都属于 Class，其唯一性由精确成员及 raw Value 方程证明。
这是整段内部程序执行的一步，不是假定无限存储历史存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramStore

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m map_m)
open PowerlessRelativeFiniteProgramInstruction
  (computed_m computed_l computed_formula_l functional_m functional_l tags_m)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l)
open SecondOrderFunctionAppendDerives (adjoin_m reading_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₃ (up₃ t)

def store_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C A D f c t₀ t₁ t₂ q S E g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <|
    .conj (computed_m φ (up B) (up C) (up f) (up t₀) (up t₁) (up t₂) (up q) (.bvar .here)) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (up S)) <|
        .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (up E)) <|
          .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (up g)) <|
            .conj (adjoin_m (up A) (up c) (up S)) <|
              .conj (adjoin_m (up D) (.bvar .here) (up E)) <|
                .conj (map_m (up g) (up S) (up E))
                  (reading_m (up f) (up c) (.bvar .here) (up g))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def store_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B C A D f c t₀ t₁ t₂ q S E g : type_l hℳ) : Prop :=
  ∃ y, computed_l φ η B C f t₀ t₁ t₂ q y ∧
    PowerlessRelativeClassCorrespondence.member_l hℳ B S ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B E ∧
        PowerlessRelativeClassCorrespondence.member_l hℳ B g ∧
          (∀ x, mem_l hℳ x S ↔ mem_l hℳ x A ∨ x = c) ∧
            (∀ z, mem_l hℳ z E ↔ mem_l hℳ z D ∨ z = y) ∧
              map_l (ℳ := 𝒱) g S E ∧
                ∀ x z, value_l (ℳ := 𝒱) g x z ↔ value_l (ℳ := 𝒱) f x z ∨ x = c ∧ z = y

theorem store_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C A D f c t₀ t₁ t₂ q S E g : Term ℒ Γ Δ .set) :
    (store_m φ B C A D f c t₀ t₁ t₂ q S E g).satisfies η ↔
      store_l φ (parameters_l η) (B.eval η) (C.eval η) (A.eval η) (D.eval η)
        (f.eval η) (c.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η)
          (S.eval η) (E.eval η) (g.eval η) := by
  simp only [store_m, store_l, Formula.satisfies, computed_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, adjoin_m, reading_m,
    map_formula_l, value_formula_l, parameters_pushBound_l, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem exists_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C A D f c t₀ t₁ t₂ : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ B C)
    (hA : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hD : PowerlessRelativeClassCorrespondence.member_l hℳ B D)
    (hF : PowerlessRelativeClassCorrespondence.member_l hℳ B f)
    (hcC : PowerlessRelativeClassCorrespondence.member_l hℳ B c)
    (hf : map_l (ℳ := 𝒱) f A D) (hc : ¬mem_l hℳ c A)
    (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂) (hFunctional : functional_l φ η B)
    (q : type_l hℳ) : ∃ S E g, store_l φ η B C A D f c t₀ t₁ t₂ q S E g := by
  obtain ⟨y, hy, _⟩ := PowerlessRelativeFiniteProgramInstruction.exists_unique_l
    φ η hBase hC hD hf hTags hFunctional q
  obtain ⟨S, E, g, hS, hE, hG, hDomain, hRange, hg, hRead⟩ :=
    PowerlessRelativeClassFunctionAppend.exists_l hBase hF hA hD hcC hy.1 hf hc
  exact ⟨S, E, g, y, hy, hS, hE, hG, hDomain, hRange, hg, hRead⟩

private theorem graph_ext_l {g h S E T F : type_l hℳ}
    (hg : map_l (ℳ := 𝒱) g S E) (hh : map_l (ℳ := 𝒱) h T F)
    (hRead : ∀ x y, value_l (ℳ := 𝒱) g x y ↔ value_l (ℳ := 𝒱) h x y) : g = h := by
  apply SecondOrderQuotient.ext_l hℳ
  intro p
  constructor
  · intro hp
    obtain ⟨x, y, _, _, hxy⟩ := hg.1 p hp
    obtain ⟨q, hq, hxy'⟩ := (hRead x y).mp ⟨p, hp, hxy⟩
    exact (SecondOrderPairObjects.ordered_unique_l hℳ hxy hxy').symm ▸ hq
  · intro hp
    obtain ⟨x, y, _, _, hxy⟩ := hh.1 p hp
    obtain ⟨q, hq, hxy'⟩ := (hRead x y).mpr ⟨p, hp, hxy⟩
    exact (SecondOrderPairObjects.ordered_unique_l hℳ hxy hxy').symm ▸ hq

theorem unique_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C A D f c t₀ t₁ t₂ q S E g T F h : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ B C)
    (hD : PowerlessRelativeClassCorrespondence.member_l hℳ B D)
    (hf : map_l (ℳ := 𝒱) f A D) (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hFunctional : functional_l φ η B)
    (hG : store_l φ η B C A D f c t₀ t₁ t₂ q S E g)
    (hH : store_l φ η B C A D f c t₀ t₁ t₂ q T F h) : S = T ∧ E = F ∧ g = h := by
  obtain ⟨y, hy, _, _, _, hS, hE, hg, hReadG⟩ := hG
  obtain ⟨z, hz, _, _, _, hT, hF, hh, hReadH⟩ := hH
  obtain ⟨v, _, hv⟩ := PowerlessRelativeFiniteProgramInstruction.exists_unique_l
    φ η hBase hC hD hf hTags hFunctional q
  have hyz := (hv y hy).trans (hv z hz).symm
  subst z
  exact ⟨SecondOrderQuotient.ext_l hℳ S T (fun x => (hS x).trans (hT x).symm),
    SecondOrderQuotient.ext_l hℳ E F (fun x => (hE x).trans (hF x).symm),
    graph_ext_l hg hh (fun x y => (hReadG x y).trans (hReadH x y).symm)⟩

theorem old_values_l {A f c y g : type_l hℳ}
    (hc : ¬mem_l hℳ c A)
    (hRead : ∀ x z, value_l (ℳ := 𝒱) g x z ↔ value_l (ℳ := 𝒱) f x z ∨ x = c ∧ z = y)
    {x z : type_l hℳ} (hx : mem_l hℳ x A) :
    value_l (ℳ := 𝒱) g x z ↔ value_l (ℳ := 𝒱) f x z := by
  rw [hRead]
  constructor
  · rintro (h | ⟨hxc, _⟩)
    · exact h
    · exact (hc (hxc ▸ hx)).elim
  · exact Or.inl

theorem new_value_l {A D f c y g z : type_l hℳ}
    (hf : map_l (ℳ := 𝒱) f A D) (hc : ¬mem_l hℳ c A)
    (hRead : ∀ x w, value_l (ℳ := 𝒱) g x w ↔ value_l (ℳ := 𝒱) f x w ∨ x = c ∧ w = y) :
    value_l (ℳ := 𝒱) g c z ↔ z = y := by
  rw [hRead]
  constructor
  · rintro (hz | ⟨_, hz⟩)
    · exact (hc (SecondOrderFunctionProperties.value_mem_l hℳ hf hz).1).elim
    · exact hz
  · intro hz; exact Or.inr ⟨rfl, hz⟩

def result_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C A D f c t₀ t₁ t₂ q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (.existsE .set <| .existsE .set <| .existsE .set <|
      store_m φ (up₃ B) (up₃ C) (up₃ A) (up₃ D) (up₃ f) (up₃ c)
        (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ q)
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)) <|
    .forallE .set <| .forallE .set <| .forallE .set <|
      .forallE .set <| .forallE .set <| .forallE .set <|
        let S : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
          .bvar (.there (.there (.there (.there (.there .here)))))
        let E := .bvar (.there (.there (.there (.there .here))))
        let g := .bvar (.there (.there (.there .here)))
        let T := .bvar (.there (.there .here))
        let F := .bvar (.there .here)
        let h := .bvar .here
        let w (t : Term ℒ Γ Δ .set) := up₆ t
        .imp (store_m φ (w B) (w C) (w A) (w D) (w f) (w c)
          (w t₀) (w t₁) (w t₂) (w q) S E g) <|
          .imp (store_m φ (w B) (w C) (w A) (w D) (w f) (w c)
            (w t₀) (w t₁) (w t₂) (w q) T F h) <|
            .conj (.equal S T) (.conj (.equal E F) (.equal g h))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C A D f c t₀ t₁ t₂ q : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B A) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B D) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B f) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B c) <|
              .imp (map_m f A D) <| .imp (.neg (member_m c A)) <|
                .imp (tags_m t₀ t₁ t₂) <| .imp (functional_m φ B)
                  (result_m φ B C A D f c t₀ t₁ t₂ q)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C A D f c t₀ t₁ t₂ q : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C A D f c t₀ t₁ t₂ q)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B C A D f c t₀ t₁ t₂ q : Term ℒ [] Δ .set) :
    (sentence_m φ B C A D f c t₀ t₁ t₂ q).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, result_m, tags_m, functional_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    store_formula_l K, PowerlessBMSQuotientSubsetImageDerives.at_formula_l,
    parameters_pushBound_l, parameters_empty_l, member_m, Arguments.eval,
    up₆, up₃, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hA hD hF hcC hf hc hTags hFunctional
  exact ⟨exists_l φ η hBase hC hA hD hF hcC hf hc hTags hFunctional _,
    fun _ _ _ _ _ _ hG hH => unique_l φ η hBase hC hD hf hTags hFunctional hG hH⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C A D f c t₀ t₁ t₂ q : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C A D f c t₀ t₁ t₂ q)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B C A D f c t₀ t₁ t₂ q)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramStore
