import BMSConstructibleBridge.SecondOrderEnumeratedMemberDef

/-!
# 相对 Def 的子集界

包括空分支在内，输出的每个成员都是母集的子集。由精确成员规格直接
证明，不诉诸外部全幂集或外部自然数的标准性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefProperties

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderQuotient

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem subset_l (hℳ : Theory.Models ℳ theory_m) {X Y B : type_l hℳ}
    (hDef : SecondOrderMemberDef.spec_l hℳ X Y) (hB : mem_l hℳ B Y) :
    ∀ z, mem_l hℳ z B → mem_l hℳ z X := by
  rcases hDef with ⟨hEmpty, hPair⟩ | hDef
  · have hBX : B = X := ((hPair B).mp hB).elim id id
    subst B
    exact fun z hz => False.elim (hEmpty z hz)
  · obtain ⟨A, a, ha, V, E, D, Q, R, T, F, H, hAX, P, hHY⟩ := hDef
    rw [← hHY] at hB
    obtain ⟨i, _, hSlice⟩ := (SecondOrderEnumeratedMemberDef.original_collection_l A a ha P B).mp hB
    intro z hz
    obtain ⟨n, _, hn⟩ := (hSlice z).mp hz
    rw [hn, ← hAX]
    exact (SecondOrderMemberStructure.value_l hℳ A a ha n).property

/-- 任意源公式及参数定义的子集属于实际 Def 输出。 -/
theorem coverage_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : SecondOrderPairing.relation_l A.real a A.root) {Y : type_l hℳ}
    (hDef : SecondOrderMemberDef.spec_l hℳ (mk_l hℳ A) Y)
    {Γ Δ : SortContext ℒ} (η : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) Γ Δ)
    (φ : Formula ℒ (.set :: Γ) Δ) :
    ∃ B, mem_l hℳ B Y ∧ ∀ n (hn : SecondOrderPairing.relation_l A.real n A.root),
      mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) B ↔
        φ.satisfies (η.pushBound (SecondOrderMemberStructure.value_l hℳ A a ha n)) := by
  obtain ⟨V, E, D, Q, R, T, F, H, P, hCoverage⟩ := SecondOrderLegalMemberCollection.exists_l hℳ A a ha
  have hH : SecondOrderMemberDef.spec_l hℳ (mk_l hℳ A) (mk_l hℳ H) :=
    Or.inr ⟨A, a, ha, V, E, D, Q, R, T, F, H, rfl, P, rfl⟩
  have hY := SecondOrderMemberDef.unique_l hℳ hH hDef
  obtain ⟨B, hBH, hRead⟩ := hCoverage Γ Δ η φ
  refine ⟨mk_l hℳ B, hY ▸ (mem_iff_l hℳ B H).mpr hBH, fun n hn => ?_⟩
  exact (mem_iff_l hℳ (SecondOrderGraph.child_l hℳ A n hn) B).trans (hRead n hn)

/-- 读取母集成员的某个根代表；没有抽取全局代表选择函数。 -/
theorem member_root_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {x : type_l hℳ} (hx : mem_l hℳ x (mk_l hℳ A)) :
    ∃ n, ∃ hn : SecondOrderPairing.relation_l A.real n A.root,
      x = mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn) := by
  obtain ⟨B, rfl⟩ := surj_l hℳ x
  obtain ⟨n, hn, hB⟩ := hx
  exact ⟨n, hn, (eq_iff_l hℳ _ _).mpr hB⟩

theorem mother_member_of_nonempty_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : SecondOrderPairing.relation_l A.real a A.root) {Y : type_l hℳ}
    (hDef : SecondOrderMemberDef.spec_l hℳ (mk_l hℳ A) Y) : mem_l hℳ (mk_l hℳ A) Y := by
  obtain ⟨B, hB, hRead⟩ := coverage_l hℳ A a ha hDef
    (Env.empty (M := SecondOrderMemberStructure.structure_l hℳ A a ha)) Formula.truth
  have hBX : B = mk_l hℳ A := by
    apply SecondOrderQuotient.ext_l hℳ
    intro z
    constructor
    · exact subset_l hℳ hDef hB z
    · intro hz
      obtain ⟨n, hn, rfl⟩ := member_root_l hℳ A hz
      exact (hRead n hn).mpr trivial
  exact hBX ▸ hB

theorem mother_member_l (hℳ : Theory.Models ℳ theory_m) {X Y : type_l hℳ}
    (hDef : SecondOrderMemberDef.spec_l hℳ X Y) : mem_l hℳ X Y := by
  rcases hDef with ⟨_, hPair⟩ | hDef
  · exact (hPair X).mpr (Or.inl rfl)
  · obtain ⟨A, a, ha, V, E, D, Q, R, T, F, H, hAX, P, hHY⟩ := hDef
    have h : SecondOrderMemberDef.spec_l hℳ (mk_l hℳ A) Y :=
      Or.inr ⟨A, a, ha, V, E, D, Q, R, T, F, H, rfl, P, hHY⟩
    exact hAX ▸ mother_member_of_nonempty_l hℳ A a ha h

theorem parameter_member_of_nonempty_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : SecondOrderPairing.relation_l A.real a A.root) {Y x : type_l hℳ}
    (hDef : SecondOrderMemberDef.spec_l hℳ (mk_l hℳ A) Y) (hx : mem_l hℳ x (mk_l hℳ A))
    (hTrans : ∀ y z, mem_l hℳ y (mk_l hℳ A) → mem_l hℳ z y → mem_l hℳ z (mk_l hℳ A)) :
    mem_l hℳ x Y := by
  let η := (Env.empty (M := SecondOrderMemberStructure.structure_l hℳ A a ha)).pushFree
    (sort := SetTheory.SetSort.set) ⟨x, hx⟩
  let φ : Formula ℒ [.set] [.set] :=
    .rel .membership (.cons (.bvar .here) (.cons (.fvar .here) .nil))
  obtain ⟨B, hB, hRead⟩ := coverage_l hℳ A a ha hDef η φ
  have hValue n (hn : SecondOrderPairing.relation_l A.real n A.root) :
      (SecondOrderMemberStructure.value_l hℳ A a ha n).val =
        mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn) := by
    change mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A a ha n) = _
    rw [SecondOrderMemberNormalizer.code_fixed_l hℳ A a ha n hn]
  have hRead' n (hn : SecondOrderPairing.relation_l A.real n A.root) :
      mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) B ↔
        mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) x := by
    have h := hRead n hn
    change mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) B ↔
      mem_l hℳ (SecondOrderMemberStructure.value_l hℳ A a ha n).val x at h
    rw [hValue n hn] at h
    exact h
  have hBx : B = x := by
    apply SecondOrderQuotient.ext_l hℳ
    intro z
    constructor
    · intro hz
      obtain ⟨n, hn, hzn⟩ := member_root_l hℳ A (subset_l hℳ hDef hB z hz)
      rw [hzn] at hz ⊢
      exact (hRead' n hn).mp hz
    · intro hz
      obtain ⟨n, hn, hzn⟩ := member_root_l hℳ A (hTrans x z hx hz)
      rw [hzn] at hz ⊢
      exact (hRead' n hn).mpr hz
  exact hBx ▸ hB

theorem contains_l (hℳ : Theory.Models ℳ theory_m) {X Y : type_l hℳ}
    (hDef : SecondOrderMemberDef.spec_l hℳ X Y)
    (hTrans : ∀ x z, mem_l hℳ x X → mem_l hℳ z x → mem_l hℳ z X) :
    ∀ x, mem_l hℳ x X → mem_l hℳ x Y := by
  intro x hx
  rcases hDef with ⟨hEmpty, _⟩ | hDef
  · exact False.elim (hEmpty x hx)
  · obtain ⟨A, a, ha, V, E, D, Q, R, T, F, H, hAX, P, hHY⟩ := hDef
    have h : SecondOrderMemberDef.spec_l hℳ (mk_l hℳ A) Y :=
      Or.inr ⟨A, a, ha, V, E, D, Q, R, T, F, H, rfl, P, hHY⟩
    rw [← hAX] at hx hTrans
    exact parameter_member_of_nonempty_l hℳ A a ha h hx hTrans

theorem transitive_l (hℳ : Theory.Models ℳ theory_m) {X Y : type_l hℳ}
    (hDef : SecondOrderMemberDef.spec_l hℳ X Y)
    (hTrans : ∀ x z, mem_l hℳ x X → mem_l hℳ z x → mem_l hℳ z X) :
    ∀ x z, mem_l hℳ x Y → mem_l hℳ z x → mem_l hℳ z Y := by
  intro x z hx hz
  exact contains_l hℳ hDef hTrans z (subset_l hℳ hDef hx z hz)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefProperties
