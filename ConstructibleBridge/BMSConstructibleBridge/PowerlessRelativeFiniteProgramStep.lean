import BMSConstructibleBridge.PowerlessRelativeFiniteProgramStore
import BMSConstructibleBridge.SecondOrderNaturalCases

/-! # 实际有限程序的总单值状态转移

状态编码为 (内部计数, (精确陪域, 干净存储图))。
指令从原程序图读取；缺失坐标采用指定缺省指令。
有效状态执行一次精确延拓，无效状态返回基底 B。
只构造单步原关系，整段执行及内部计数不变式另行证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramStep

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (ordered_m member_m value_m map_m)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l)
open PowerlessRelativeFiniteProgramInstruction (functional_m functional_l tags_m)
open PowerlessRelativeFiniteProgramStore (store_m store_l store_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₇ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₃ (up₃ t))

def record_m {Γ Δ : SortContext ℒ} (i D f s : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (ordered_m (up D) (up f) (.bvar .here))
    (ordered_m (up i) (.bvar .here) (up s))

def current_m {Γ Δ : SortContext ℒ} (w e i q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (value_m w i q) <| .conj
    (.neg (.existsE .set (value_m (up w) (up i) (.bvar .here)))) (.equal q e)

def valid_m {Γ Δ : SortContext ℒ} (B ω i D f s : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (record_m i D f s) <| .conj (member_m i ω) <|
    .conj (PowerlessRelativeHierarchySyntax.class_m B i) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m B D) <|
        .conj (PowerlessRelativeHierarchySyntax.class_m B f) (map_m f i D)

def good_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ s t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      let i : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
        .bvar (.there (.there (.there (.there (.there (.there .here))))))
      let D := .bvar (.there (.there (.there (.there (.there .here)))))
      let f := .bvar (.there (.there (.there (.there .here))))
      let q := .bvar (.there (.there (.there .here)))
      let S := .bvar (.there (.there .here))
      let E := .bvar (.there .here)
      let g := .bvar .here
      .conj (valid_m (up₇ B) (up₇ ω) i D f (up₇ s)) <|
        .conj (current_m (up₇ w) (up₇ e) i q) <|
          .conj (store_m φ (up₇ B) (up₇ C) i D f i
            (up₇ t₀) (up₇ t₁) (up₇ t₂) q S E g) (record_m S E g (up₇ t))

def step_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ s t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.class_m B t) <| .disj
    (good_m φ B C ω w e t₀ t₁ t₂ s t) <| .conj
      (.neg (.existsE .set (good_m φ (up B) (up C) (up ω) (up w) (up e)
        (up t₀) (up t₁) (up t₂) (up s) (.bvar .here)))) (.equal t B)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def record_l (i D f s : type_l hℳ) : Prop :=
  ∃ p, ordered_l (ℳ := 𝒱) D f p ∧ ordered_l (ℳ := 𝒱) i p s

def current_l (w e i q : type_l hℳ) : Prop :=
  value_l (ℳ := 𝒱) w i q ∨ ((¬∃ z, value_l (ℳ := 𝒱) w i z) ∧ q = e)

def valid_l (B ω i D f s : type_l hℳ) : Prop :=
  record_l i D f s ∧ mem_l hℳ i ω ∧
    PowerlessRelativeClassCorrespondence.member_l hℳ B i ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B D ∧
        PowerlessRelativeClassCorrespondence.member_l hℳ B f ∧ map_l (ℳ := 𝒱) f i D

def good_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B C ω w e t₀ t₁ t₂ s t : type_l hℳ) : Prop :=
  ∃ i D f q S E g, valid_l B ω i D f s ∧ current_l w e i q ∧
    store_l φ η B C i D f i t₀ t₁ t₂ q S E g ∧ record_l S E g t

def step_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B C ω w e t₀ t₁ t₂ s t : type_l hℳ) : Prop :=
  PowerlessRelativeClassCorrespondence.member_l hℳ B t ∧
    (good_l φ η B C ω w e t₀ t₁ t₂ s t ∨
      ((¬∃ z, good_l φ η B C ω w e t₀ t₁ t₂ s z) ∧ t = B))

theorem record_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (i D f s : Term ℒ Γ Δ .set) :
    (record_m i D f s).satisfies η ↔ record_l (i.eval η) (D.eval η) (f.eval η) (s.eval η) := by
  simp only [record_m, record_l, Formula.satisfies, ordered_formula_l, up,
    Term.eval_weakenBound, Term.eval]
  rfl

theorem current_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (w e i q : Term ℒ Γ Δ .set) :
    (current_m w e i q).satisfies η ↔ current_l (w.eval η) (e.eval η) (i.eval η) (q.eval η) := by
  simp only [current_m, current_l, Formula.satisfies, value_formula_l, up,
    Term.eval_weakenBound, Term.eval]
  rfl

theorem valid_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B ω i D f s : Term ℒ Γ Δ .set) :
    (valid_m B ω i D f s).satisfies η ↔
      valid_l (B.eval η) (ω.eval η) (i.eval η) (D.eval η) (f.eval η) (s.eval η) := by
  simp only [valid_m, valid_l, Formula.satisfies, record_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l, member_m,
    Arguments.eval]
  rfl

theorem good_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω w e t₀ t₁ t₂ s t : Term ℒ Γ Δ .set) :
    (good_m φ B C ω w e t₀ t₁ t₂ s t).satisfies η ↔
      good_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
        (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (s.eval η) (t.eval η) := by
  simp only [good_m, good_l, Formula.satisfies, valid_formula_l K, current_formula_l,
    store_formula_l K, record_formula_l, parameters_pushBound_l,
    up₇, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem step_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω w e t₀ t₁ t₂ s t : Term ℒ Γ Δ .set) :
    (step_m φ B C ω w e t₀ t₁ t₂ s t).satisfies η ↔
      step_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
        (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (s.eval η) (t.eval η) := by
  simp only [step_m, step_l, Formula.satisfies, good_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, parameters_pushBound_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem record_exists_l (i D f : type_l hℳ) : ∃ s, record_l i D f s := by
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ D f
  obtain ⟨s, hs⟩ := SecondOrderPairObjects.ordered_exists_l hℳ i p
  exact ⟨s, p, hp, hs⟩

theorem record_unique_l {i D f s t : type_l hℳ}
    (hs : record_l i D f s) (ht : record_l i D f t) : s = t := by
  obtain ⟨p, hp, hs⟩ := hs
  obtain ⟨q, hq, ht⟩ := ht
  have hpq := SecondOrderPairObjects.ordered_unique_l hℳ hp hq
  subst q
  exact SecondOrderPairObjects.ordered_unique_l hℳ hs ht

theorem record_coordinates_l {i D f j E g s : type_l hℳ}
    (hs : record_l i D f s) (ht : record_l j E g s) : i = j ∧ D = E ∧ f = g := by
  obtain ⟨p, hp, hs⟩ := hs
  obtain ⟨q, hq, ht⟩ := ht
  obtain ⟨hij, hpq⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hs ht).mp rfl
  subst q
  exact ⟨hij, (SecondOrderPairObjects.ordered_eq_l hℳ hp hq).mp rfl⟩

theorem record_class_l {B i D f s : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hi : PowerlessRelativeClassCorrespondence.member_l hℳ B i)
    (hD : PowerlessRelativeClassCorrespondence.member_l hℳ B D)
    (hf : PowerlessRelativeClassCorrespondence.member_l hℳ B f)
    (hs : record_l i D f s) : PowerlessRelativeClassCorrespondence.member_l hℳ B s := by
  obtain ⟨p, hp, hs⟩ := hs
  exact PowerlessRelativeClassPair.ordered_l hℳ hBase hi
    (PowerlessRelativeClassPair.ordered_l hℳ hBase hD hf hp) hs

theorem current_exists_unique_l {w N Q : type_l hℳ}
    (hw : map_l (ℳ := 𝒱) w N Q) (e i : type_l hℳ) : ∃! q, current_l w e i q := by
  classical
  by_cases hSome : ∃ q, value_l (ℳ := 𝒱) w i q
  · obtain ⟨q, hq⟩ := hSome
    refine ⟨q, Or.inl hq, ?_⟩
    intro z hz
    rcases hz with hz | hz
    · exact SecondOrderFunctionProperties.value_unique_l hℳ hw hz hq
    · exact (hz.1 ⟨q, hq⟩).elim
  · refine ⟨e, Or.inr ⟨hSome, rfl⟩, ?_⟩
    intro z hz
    rcases hz with hz | hz
    · exact (hSome ⟨z, hz⟩).elim
    · exact hz.2

theorem good_exists_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C ω w N Q e t₀ t₁ t₂ i D f s : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ B C)
    (hw : map_l (ℳ := 𝒱) w N Q) (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hFunctional : functional_l φ η B) (hs : valid_l B ω i D f s) :
    ∃ t, good_l φ η B C ω w e t₀ t₁ t₂ s t := by
  obtain ⟨q, hq, _⟩ := current_exists_unique_l hw e i
  obtain ⟨S, E, g, hg⟩ := PowerlessRelativeFiniteProgramStore.exists_l φ η
    hBase hC hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.1 hs.2.2.2.2.2
    (fun hii => SecondOrderNaturalCases.asymmetry_l hℳ hii hii) hTags hFunctional q
  obtain ⟨t, ht⟩ := record_exists_l S E g
  exact ⟨t, i, D, f, q, S, E, g, hs, hq, hg, ht⟩

theorem good_class_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C ω w e t₀ t₁ t₂ s t : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (ht : good_l φ η B C ω w e t₀ t₁ t₂ s t) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B t := by
  obtain ⟨_, _, _, _, S, E, g, _, _, hg, ht⟩ := ht
  obtain ⟨_, _, hS, hE, hG, _⟩ := hg
  exact record_class_l hBase hS hE hG ht

theorem good_unique_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C ω w N Q e t₀ t₁ t₂ s t v : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ B C)
    (hw : map_l (ℳ := 𝒱) w N Q) (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hFunctional : functional_l φ η B)
    (ht : good_l φ η B C ω w e t₀ t₁ t₂ s t)
    (hv : good_l φ η B C ω w e t₀ t₁ t₂ s v) : t = v := by
  obtain ⟨i, D, f, q, S, E, g, hs, hq, hg, ht⟩ := ht
  obtain ⟨j, F, h, r, T, G, k, hs', hr, hk, hv⟩ := hv
  obtain ⟨hij, hDF, hfh⟩ := record_coordinates_l hs.1 hs'.1
  subst j; subst F; subst h
  obtain ⟨a, _, ha⟩ := current_exists_unique_l hw e i
  have hqr := (ha q hq).trans (ha r hr).symm
  subst r
  obtain ⟨hST, hEG, hgk⟩ := PowerlessRelativeFiniteProgramStore.unique_l φ η
    hBase hC hs.2.2.2.1 hs.2.2.2.2.2 hTags hFunctional hg hk
  subst T; subst G; subst k
  exact record_unique_l ht hv

theorem exists_unique_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C ω w N Q e t₀ t₁ t₂ : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ B C)
    (hw : map_l (ℳ := 𝒱) w N Q) (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hFunctional : functional_l φ η B) (s : type_l hℳ) :
    ∃! t, step_l φ η B C ω w e t₀ t₁ t₂ s t := by
  classical
  by_cases hSome : ∃ t, good_l φ η B C ω w e t₀ t₁ t₂ s t
  · obtain ⟨t, ht⟩ := hSome
    refine ⟨t, ⟨good_class_l φ η hBase ht, Or.inl ht⟩, ?_⟩
    intro v hv
    rcases hv.2 with hv | hv
    · exact good_unique_l φ η hBase hC hw hTags hFunctional hv ht
    · exact (hv.1 ⟨t, ht⟩).elim
  · refine ⟨B, ⟨PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase,
      Or.inr ⟨hSome, rfl⟩⟩, ?_⟩
    intro v hv
    rcases hv.2 with hv | hv
    · exact (hSome ⟨v, hv⟩).elim
    · exact hv.2

theorem initial_l (K : source_coding_l hℳ) {B e s : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (he : ∀ x, ¬mem_l hℳ x e) (hs : record_l e e e s) :
    valid_l B K.omega e e e s := by
  have heEq : e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := by
    apply SecondOrderQuotient.ext_l hℳ
    intro x
    exact iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x)
  have heω : mem_l hℳ e K.omega :=
    heEq.symm ▸ (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
  obtain ⟨α, Cω, hCω, hωCω⟩ := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)
  have heC := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
    (show PowerlessRelativeClassCorrespondence.member_l hℳ B K.omega from
      ⟨α, Cω, hCω, hωCω⟩) heω
  exact ⟨hs, heω, heC, heC, heC,
    ⟨fun x hx => (he x hx).elim, fun x hx => (he x hx).elim⟩⟩

theorem transition_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    {B C w N Q e t₀ t₁ t₂ i D f s t : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ B C)
    (hw : map_l (ℳ := 𝒱) w N Q) (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hFunctional : functional_l φ η B) (hs : valid_l B K.omega i D f s)
    (ht : step_l φ η B C K.omega w e t₀ t₁ t₂ s t) :
    ∃ q S E g, current_l w e i q ∧ store_l φ η B C i D f i t₀ t₁ t₂ q S E g ∧
      PowerlessNatural.successor_l (ℳ := 𝒱) i S ∧ valid_l B K.omega S E g t := by
  have hSome := good_exists_l φ η (e := e) hBase hC hw hTags hFunctional hs
  have hGood : good_l φ η B C K.omega w e t₀ t₁ t₂ s t := by
    rcases ht.2 with h | h
    · exact h
    · exact (h.1 hSome).elim
  obtain ⟨j, F, h, q, S, E, g, hs', hq, hg, hRecord⟩ := hGood
  obtain ⟨hij, hDF, hfh⟩ := record_coordinates_l hs.1 hs'.1
  subst j; subst F; subst h
  have hStore := hg
  obtain ⟨_, _, hS, hE, hG, hDomain, _, hMap, _⟩ := hg
  obtain ⟨k, hk⟩ := numberCode_surjective_l K ⟨i, hs.2.1⟩
  have hki : (numberCode_l K k).val = i := congrArg Subtype.val hk
  have hSEq : S = (numberCode_l K (SecondOrderModel.succ_l k)).val := by
    apply SecondOrderQuotient.ext_l hℳ
    intro x
    exact (hDomain x).trans (hki ▸ PowerlessBMSQuotientSuccessor.successor_l K k x).symm
  exact ⟨q, S, E, g, hq, hStore, hDomain, hRecord,
    hSEq.symm ▸ (numberCode_l K (SecondOrderModel.succ_l k)).property, hS, hE, hG, hMap⟩

def property_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .existsE .set <|
    let s : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let t := .bvar .here
    .conj (step_m φ (up₂ B) (up₂ C) (up₂ ω) (up₂ w) (up₂ e)
      (up₂ t₀) (up₂ t₁) (up₂ t₂) s t) <|
      .forallE .set <| .imp
        (step_m φ (up₃ B) (up₃ C) (up₃ ω) (up₃ w) (up₃ e)
          (up₃ t₀) (up₃ t₁) (up₃ t₂) (up s) (.bvar .here)) (.equal (.bvar .here) (up t))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (map_m w N Q) <| .imp (tags_m t₀ t₁ t₂) <|
        .imp (functional_m φ B) (property_m φ B C ω w e t₀ t₁ t₂)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω w N Q e t₀ t₁ t₂)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B C ω w N Q e t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω w N Q e t₀ t₁ t₂).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, property_m, tags_m, functional_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    step_formula_l K, PowerlessBMSQuotientSubsetImageDerives.at_formula_l,
    parameters_pushBound_l, parameters_empty_l, up₃, up₂, up,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hw hTags hFunctional s
  exact exists_unique_l φ η hBase hC hw hTags hFunctional s

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω w N Q e t₀ t₁ t₂)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B C ω w N Q e t₀ t₁ t₂)

#print axioms record_coordinates_l
#print axioms good_exists_l
#print axioms good_unique_l
#print axioms exists_unique_l
#print axioms initial_l
#print axioms transition_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramStep
