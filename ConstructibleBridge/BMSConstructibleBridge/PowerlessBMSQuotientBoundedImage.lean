import BMSConstructibleBridge.PowerlessBMSQuotientSubsetImageDerives

/-!
# 任意内部集合上的子集有界替换

先用两张给定图的根构造统一成员关系，再组装切片族。非定义域根所产生的
多余切片由完整分离移除。因此不需要把定义域选择性地枚举为外部自然数列。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientBoundedImage

open Logic FirstOrder PowerlessBMSQuotientSubsetImageDerives

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [.set] (.set :: .set :: Δ)
  | _, .here => .fvar .here
  | _, .there .here => .bvar .here
  | _, .there (.there v) => .fvar (.there (.there v))

/-- 自由槽依次为输出、定义域、原参数。 -/
def range_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  .existsE .set (.conj
    (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there .here)))
    (φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ) [.set]
      (.set :: .set :: Δ) from .map (fun v => nomatch v) insert_m)))

theorem range_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (D y : 𝒩.Carrier .set) :
    (range_m φ).satisfies ((η.pushFree D).pushFree y) ↔
      ∃ x, 𝒩.relInterp .membership (.cons x (.cons D .nil)) ∧
        φ.satisfies ((η.pushFree x).pushFree y) := by
  simp only [range_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval]
  apply exists_congr
  intro x
  apply and_congr Iff.rfl
  refine (Formula.satisfies_substitute _ _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

private abbrev quotient_l := SecondOrderQuotient.structure_l hℳ

/-- 值均为同一母集的子集时，可定义函数在任意内部集合上有精确值域。 -/
theorem exists_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) (d a : SecondOrderQuotient.type_l hℳ)
    (hUnique : ∀ x y z, SecondOrderQuotient.mem_l hℳ x d →
      φ.satisfies ((η.pushFree x).pushFree y) →
      φ.satisfies ((η.pushFree x).pushFree z) → y = z)
    (hBound : ∀ x y, SecondOrderQuotient.mem_l hℳ x d →
      φ.satisfies ((η.pushFree x).pushFree y) →
      ∀ t, SecondOrderQuotient.mem_l hℳ t y → SecondOrderQuotient.mem_l hℳ t a) :
    ∃ b, ∀ y, SecondOrderQuotient.mem_l hℳ y b ↔
      ∃ x, SecondOrderQuotient.mem_l hℳ x d ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  obtain ⟨D, rfl⟩ := SecondOrderQuotient.surj_l hℳ d
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨F, hF⟩ := SecondOrderGraphFormulaRelation.exists_l hℳ
    (PowerlessBMSQuotientSubsetImage.membership_m φ) η D.real A.real
  have hRelation n m (hn : SecondOrderDomain.wf_l D.real n)
      (hm : SecondOrderDomain.wf_l A.real m) :
      SecondOrderPairing.relation_l F n m ↔ ∃ y,
        φ.satisfies ((η.pushFree (SecondOrderQuotient.mk_l hℳ ⟨D.real, n, hn⟩)).pushFree y) ∧
        SecondOrderQuotient.mem_l hℳ (SecondOrderQuotient.mk_l hℳ ⟨A.real, m, hm⟩) y :=
    (hF n m hn hm).trans (PowerlessBMSQuotientSubsetImage.membership_formula_l φ η _ _)
  obtain ⟨G, hG, H, hH⟩ := SecondOrderSubsetCollection.exists_l hℳ A F
  have hCover y (hy : ∃ x, SecondOrderQuotient.mem_l hℳ x (SecondOrderQuotient.mk_l hℳ D) ∧
      φ.satisfies ((η.pushFree x).pushFree y)) :
      SecondOrderQuotient.mem_l hℳ y (SecondOrderQuotient.mk_l hℳ H) := by
    obtain ⟨x, hx, hy⟩ := hy
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    obtain ⟨n, hn, hXn⟩ := hx
    let N := SecondOrderGraph.child_l hℳ D n hn
    have hXN : SecondOrderQuotient.mk_l hℳ X = SecondOrderQuotient.mk_l hℳ N :=
      (SecondOrderQuotient.eq_iff_l hℳ X N).mpr hXn
    have hN : SecondOrderQuotient.mem_l hℳ (SecondOrderQuotient.mk_l hℳ N)
        (SecondOrderQuotient.mk_l hℳ D) := SecondOrderGraph.child_mem_l hℳ D n hn
    rw [hXN] at hy
    have hSlice : SecondOrderQuotient.mk_l hℳ
        (SecondOrderSubsetLayer.code_l hℳ A F G hG n) = y := by
      apply SecondOrderQuotient.ext_l hℳ
      intro t
      obtain ⟨T, rfl⟩ := SecondOrderQuotient.surj_l hℳ t
      change SecondOrderGraph.mem_l T (SecondOrderSubsetLayer.code_l hℳ A F G hG n) ↔ _
      rw [SecondOrderSubsetLayer.mem_l hℳ A F G hG n T]
      constructor
      · rintro ⟨m, hm, hFm, hTm⟩
        let B := SecondOrderGraph.child_l hℳ A m hm
        obtain ⟨z, hz, hBz⟩ := (hRelation n m N.wf B.wf).mp hFm
        have hzy := hUnique _ z y hN hz hy
        have hTB : SecondOrderQuotient.mk_l hℳ T = SecondOrderQuotient.mk_l hℳ B :=
          (SecondOrderQuotient.eq_iff_l hℳ T B).mpr hTm
        rw [hTB, ← hzy]
        exact hBz
      · intro hTy
        obtain ⟨m, hm, hTm⟩ := hBound _ y hN hy (SecondOrderQuotient.mk_l hℳ T) hTy
        let B := SecondOrderGraph.child_l hℳ A m hm
        have hTB : SecondOrderQuotient.mk_l hℳ T = SecondOrderQuotient.mk_l hℳ B :=
          (SecondOrderQuotient.eq_iff_l hℳ T B).mpr hTm
        refine ⟨m, hm, (hRelation n m N.wf B.wf).mpr ⟨y, hy, ?_⟩, hTm⟩
        change SecondOrderQuotient.mem_l hℳ (SecondOrderQuotient.mk_l hℳ B) y
        exact hTB ▸ hTy
    rw [← hSlice]
    exact (hH _).mpr ⟨n, SecondOrderGraph.refl_l hℳ _⟩
  obtain ⟨b, hb⟩ := (SecondOrderSeparationAxiom.schema_l hℳ (range_m φ)
    (η.pushFree (SecondOrderQuotient.mk_l hℳ D))).mp
      (SecondOrderSeparationAxiom.models_l hℳ _ _) (SecondOrderQuotient.mk_l hℳ H)
  refine ⟨b, fun y => ?_⟩
  rw [hb, range_formula_l]
  exact ⟨And.right, fun hy => ⟨hCover y hy, hy⟩⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientBoundedImage
