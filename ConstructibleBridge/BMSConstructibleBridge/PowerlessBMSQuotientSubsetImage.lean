import BMSConstructibleBridge.PowerlessBMSQuotientCoding
import BMSConstructibleBridge.SecondOrderGraphFormulaRelation
import BMSConstructibleBridge.SecondOrderSubsetCollection

/-!
# 无 Collection 的自然数索引、子集有界替换

每个内部数有唯一可定义输出，且输出都是同一个给定集合的子集时，值域是
原 Z₂ 图商中的集合。证明一次构造双索引成员关系，再收集其内部切片；不从
逐数存在的实数见证假定可数选择，也不要求给定集合的幂集存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientSubsetImage

open Logic FirstOrder PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [.set] (.set :: .set :: Δ)
  | _, .here => .bvar .here
  | _, .there .here => .fvar .here
  | _, .there (.there v) => .fvar (.there (.there v))

private def substitution_m {Δ : SortContext ℒ} :
    Substitution ℒ [] (.set :: .set :: Δ) [.set] (.set :: .set :: Δ) :=
  .map (fun v => nomatch v) insert_m

/-- 首自由槽为索引，次自由槽为待测元素；存在输出并读取其成员。 -/
def membership_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  .existsE .set (.conj (φ.substitute substitution_m)
    (.rel .membership (.cons (.fvar (.there .here)) (.cons (.bvar .here) .nil))))

theorem membership_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (n x : 𝒩.Carrier .set) :
    (membership_m φ).satisfies ((η.pushFree x).pushFree n) ↔
      ∃ y, φ.satisfies ((η.pushFree n).pushFree y) ∧
        𝒩.relInterp .membership (.cons x (.cons y .nil)) := by
  change (∃ y, (φ.substitute substitution_m).satisfies
    (((η.pushFree x).pushFree n).pushBound y) ∧
      𝒩.relInterp .membership (.cons x (.cons y .nil))) ↔ _
  apply exists_congr
  intro y
  apply and_congr _ Iff.rfl
  refine (Formula.satisfies_substitute _ _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev quotient_l := SecondOrderQuotient.structure_l hℳ

/-- 一张实际二元关系同时读取所有内部索引输出的成员。 -/
theorem relation_l (C : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env quotient_l [] Δ)
    (A : SecondOrderGraph.code_l ℳ) :
    ∃ F : SecondOrderModel.set_l ℳ, ∀ n m (hm : SecondOrderDomain.wf_l A.real m),
      SecondOrderPairing.relation_l F n m ↔
        ∃ y, φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) ∧
          SecondOrderQuotient.mem_l hℳ (SecondOrderQuotient.mk_l hℳ ⟨A.real, m, hm⟩) y := by
  obtain ⟨F, hF⟩ := SecondOrderGraphFormulaRelation.exists_l hℳ (membership_m φ) η C.less A.real
  refine ⟨F, fun n m hm => (hF n m
    (SecondOrderNaturalGraph.wf_l hℳ C.less C.less_spec n) hm).trans ?_⟩
  exact membership_formula_l φ η _ _

/-- 子集有界类函数的精确值域，不只是一个可能含额外元素的收集上界。 -/
theorem exists_l (C : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env quotient_l [] Δ)
    (a : SecondOrderQuotient.type_l hℳ)
    (hTotal : ∀ n, ∃ y, φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y))
    (hUnique : ∀ n y z,
      φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) →
      φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree z) → y = z)
    (hBound : ∀ n y, φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) →
      ∀ x, SecondOrderQuotient.mem_l hℳ x y → SecondOrderQuotient.mem_l hℳ x a) :
    ∃ b : SecondOrderQuotient.type_l hℳ, ∀ y, SecondOrderQuotient.mem_l hℳ y b ↔
      ∃ n, φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨F, hF⟩ := relation_l C φ η A
  obtain ⟨G, hG, H, hH⟩ := SecondOrderSubsetCollection.exists_l hℳ A F
  have hSlice (n : SecondOrderModel.num_l ℳ) (y : SecondOrderQuotient.type_l hℳ)
      (hy : φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y)) :
      SecondOrderQuotient.mk_l hℳ (SecondOrderSubsetLayer.code_l hℳ A F G hG n) = y := by
    apply SecondOrderQuotient.ext_l hℳ
    intro x
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    change SecondOrderGraph.mem_l X (SecondOrderSubsetLayer.code_l hℳ A F G hG n) ↔ _
    rw [SecondOrderSubsetLayer.mem_l hℳ A F G hG n X]
    constructor
    · rintro ⟨m, hm, hFm, hXm⟩
      let B := SecondOrderGraph.child_l hℳ A m hm
      obtain ⟨z, hz, hBz⟩ := (hF n m B.wf).mp hFm
      have hzy := hUnique n z y hz hy
      have hXB : SecondOrderQuotient.mk_l hℳ X = SecondOrderQuotient.mk_l hℳ B :=
        (SecondOrderQuotient.eq_iff_l hℳ X B).mpr hXm
      rw [hXB, ← hzy]
      exact hBz
    · intro hXy
      obtain ⟨m, hm, hXm⟩ := hBound n y hy (SecondOrderQuotient.mk_l hℳ X) hXy
      let B := SecondOrderGraph.child_l hℳ A m hm
      have hXB : SecondOrderQuotient.mk_l hℳ X = SecondOrderQuotient.mk_l hℳ B :=
        (SecondOrderQuotient.eq_iff_l hℳ X B).mpr hXm
      refine ⟨m, hm, (hF n m B.wf).mpr ⟨y, hy, ?_⟩, hXm⟩
      change SecondOrderQuotient.mem_l hℳ (SecondOrderQuotient.mk_l hℳ B) y
      rw [← hXB]
      exact hXy
  refine ⟨SecondOrderQuotient.mk_l hℳ H, fun y => ?_⟩
  obtain ⟨Y, rfl⟩ := SecondOrderQuotient.surj_l hℳ y
  change SecondOrderGraph.mem_l Y H ↔ _
  rw [hH]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨y, hy⟩ := hTotal n
    have hY := (SecondOrderQuotient.eq_iff_l hℳ Y _).mpr hn
    rw [hSlice n y hy] at hY
    exact ⟨n, hY.symm ▸ hy⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (SecondOrderQuotient.eq_iff_l hℳ Y _).mp (hSlice n _ hn).symm⟩

#print axioms relation_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientSubsetImage
