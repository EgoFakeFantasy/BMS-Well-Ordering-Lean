import BMSConstructibleBridge.PowerlessFiniteProgramStoreSyntax
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramStep

/-! # 同一原程序状态转移的类内纯矩阵

对象语言纯隶属 ℒ。复用原状态和当前指令编码；有效状态保持计数、
精确陪域、存储图，无效状态仍返回 B。仅省去由类内载体承担的
Class 资格原子，不更换程序或假定内部长度外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteProgramStepSyntax

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderObjectSyntax (member_m map_m)
open PowerlessRelativeFiniteProgramStep (record_m current_m)
open PowerlessFiniteProgramStoreSyntax (store_m store_l store_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))
private abbrev up₇ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₃ (up₃ t))

def valid_m {Γ Δ : SortContext ℒ} (ω i D f s : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (record_m i D f s) <| .conj (member_m i ω) (map_m f i D)

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
      .conj (valid_m (up₇ ω) i D f (up₇ s)) <|
        .conj (current_m (up₇ w) (up₇ e) i q) <|
          .conj (store_m φ (up₇ B) (up₇ C) i D f i
            (up₇ t₀) (up₇ t₁) (up₇ t₂) q S E g) (record_m S E g (up₇ t))

def step_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ s t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (good_m φ B C ω w e t₀ t₁ t₂ s t) <| .conj
    (.neg (.existsE .set (good_m φ (up B) (up C) (up ω) (up w) (up e)
      (up t₀) (up t₁) (up t₂) (up s) (.bvar .here)))) (.equal t B)

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def record_l (i D f s : carrier_l 𝒩) : Prop :=
  ∃ p, ordered_l D f p ∧ ordered_l i p s

def current_l (w e i q : carrier_l 𝒩) : Prop :=
  value_l w i q ∨ ((¬∃ z, value_l w i z) ∧ q = e)

def valid_l (ω i D f s : carrier_l 𝒩) : Prop :=
  record_l i D f s ∧ member_l 𝒩 i ω ∧ map_l f i D

def good_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (B C ω w e t₀ t₁ t₂ s t : carrier_l 𝒩) : Prop :=
  ∃ i D f q S E g, valid_l ω i D f s ∧ current_l w e i q ∧
    store_l φ η B C i D f i t₀ t₁ t₂ q S E g ∧ record_l S E g t

def step_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (B C ω w e t₀ t₁ t₂ s t : carrier_l 𝒩) : Prop :=
  good_l φ η B C ω w e t₀ t₁ t₂ s t ∨
    ((¬∃ z, good_l φ η B C ω w e t₀ t₁ t₂ s z) ∧ t = B)

theorem record_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ)
    (i D f s : Term ℒ Γ Δ .set) :
    (record_m i D f s).satisfies η ↔ record_l (i.eval η) (D.eval η) (f.eval η) (s.eval η) := by
  simp only [record_m, record_l, Formula.satisfies, ordered_formula_l,
    Term.eval_weakenBound, Term.eval]
  rfl

theorem current_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ)
    (w e i q : Term ℒ Γ Δ .set) :
    (current_m w e i q).satisfies η ↔ current_l (w.eval η) (e.eval η) (i.eval η) (q.eval η) := by
  simp only [current_m, current_l, Formula.satisfies, value_formula_l,
    Term.eval_weakenBound, Term.eval]
  rfl

theorem valid_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ)
    (ω i D f s : Term ℒ Γ Δ .set) :
    (valid_m ω i D f s).satisfies η ↔
      valid_l (ω.eval η) (i.eval η) (D.eval η) (f.eval η) (s.eval η) := by
  simp only [valid_m, valid_l, Formula.satisfies, record_formula_l, map_formula_l,
    member_m, Arguments.eval]
  rfl

theorem good_formula_l {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ)
    (B C ω w e t₀ t₁ t₂ s t : Term ℒ Γ Δ .set) :
    (good_m φ B C ω w e t₀ t₁ t₂ s t).satisfies η ↔
      good_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
        (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (s.eval η) (t.eval η) := by
  simp only [good_m, good_l, Formula.satisfies, valid_formula_l, current_formula_l,
    store_formula_l, record_formula_l, parameters_pushBound_l,
    up₇, up₃, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem step_formula_l {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ)
    (B C ω w e t₀ t₁ t₂ s t : Term ℒ Γ Δ .set) :
    (step_m φ B C ω w e t₀ t₁ t₂ s t).satisfies η ↔
      step_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
        (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (s.eval η) (t.eval η) := by
  simp only [step_m, step_l, Formula.satisfies, good_formula_l, parameters_pushBound_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms record_formula_l
#print axioms current_formula_l
#print axioms valid_formula_l
#print axioms good_formula_l
#print axioms step_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteProgramStepSyntax
