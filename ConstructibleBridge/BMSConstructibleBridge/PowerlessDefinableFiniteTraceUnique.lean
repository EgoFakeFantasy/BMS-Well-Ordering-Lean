import BMSConstructibleBridge.PowerlessDefinableFiniteTraceDerives

/-! # 单值可定义关系的有限轨迹唯一性

逐坐标唯一性使用原 Z₂ 的实际公式归纳，并覆盖非标准内部自然数。
不同轨迹可以有不同陪域；真正唯一的是干净函数图，而不是陪域。
不以无限递归或完整 Collection 为背景。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableFiniteTraceUnique

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessDefinableFiniteTrace (trace_l trace_m trace_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (at_m at_formula_l parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₃ (up₃ t)

private def point_m : Formula ℒ [] [.set, .set, .set] :=
  .forallE .set <| .forallE .set <|
    .imp (SecondOrderObjectSyntax.value_m (up₂ (.fvar (.there .here)))
      (up₂ (.fvar .here)) (.bvar (.there .here))) <|
      .imp (SecondOrderObjectSyntax.value_m (up₂ (.fvar (.there (.there .here))))
        (up₂ (.fvar .here)) (.bvar .here)) <|
        .equal (.bvar (.there .here)) (.bvar .here)

private theorem point_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (η : Env 𝒱 [] [.set, .set]) (k : carrier_l 𝒱) :
    point_m.satisfies (η.pushFree k) ↔ ∀ x y,
      value_l (η.freeVal .here) k x → value_l (η.freeVal (.there .here)) k y → x = y := by
  simp only [point_m, Formula.satisfies, value_formula_l, up₂, up,
    Term.eval_weakenBound, Term.eval, Env.pushFree_here, Env.pushFree_there]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private theorem successor_unique_l {i j k : type_l hℳ}
    (hj : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) i j)
    (hk : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) i k) : j = k :=
  SecondOrderQuotient.ext_l hℳ j k (fun x => (hj x).trans (hk x).symm)

private theorem predecessor_bound_l (K : source_coding_l hℳ) {n S : type_l hℳ}
    (hn : mem_l hℳ n K.omega)
    (hS : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) n S)
    (k : SecondOrderModel.num_l ℳ)
    (hk : mem_l hℳ (numberCode_l K (SecondOrderModel.succ_l k)).val S) :
    mem_l hℳ (numberCode_l K k).val n := by
  obtain ⟨l, hl⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have hl' : (numberCode_l K l).val = n := congrArg Subtype.val hl
  have hSEq := successor_unique_l hS (hl' ▸ PowerlessBMSQuotientSuccessor.successor_l K l)
  rw [hSEq] at hk
  have hlt := (SecondOrderOrder.succ_iff_l hℳ k l).mp
    ((numberCode_mem_iff_lt_l K _ _).mp hk)
  exact hl' ▸ (numberCode_mem_iff_lt_l K k l).mpr hlt

theorem overlap_values_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    {e a n m S D f T E g : type_l hℳ} (hn : mem_l hℳ n K.omega)
    (hm : mem_l hℳ m K.omega)
    (he : e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hF : trace_l φ η e a n S D f) (hG : trace_l φ η e a m T E g)
    (hUnique : ∀ x y z, φ.satisfies ((η.pushFree x).pushFree y) →
      φ.satisfies ((η.pushFree x).pushFree z) → y = z) :
    ∀ i x y, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f i x →
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g i y → x = y := by
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set] :=
    ((Env.empty).pushFree g).pushFree f
  have h := PowerlessBMSQuotientInduction.induction_l K point_m ξ ?_ ?_
  · intro i x y hx hy
    have hi := (SecondOrderFunctionProperties.value_mem_l hℳ hF.2.1 hx).1
    have hiω : mem_l hℳ i K.omega := by
      rcases (hF.1 i).mp hi with hi | hiEq
      · exact SecondOrderOmegaTransitive.member_l hℳ K.omega_spec hn hi
      · exact hiEq.symm ▸ hn
    obtain ⟨k, hk⟩ := numberCode_surjective_l K ⟨i, hiω⟩
    have hk' : (numberCode_l K k).val = i := congrArg Subtype.val hk
    have hValues := (point_formula_l ξ (numberCode_l K k).val).mp (h k)
    rw [hk'] at hValues
    exact hValues x y hx hy
  · apply (point_formula_l ξ _).mpr
    intro x y hx hy
    rw [← he] at hx hy
    exact (SecondOrderFunctionProperties.value_unique_l hℳ hF.2.1 hx hF.2.2.1).trans
      (SecondOrderFunctionProperties.value_unique_l hℳ hG.2.1 hy hG.2.2.1).symm
  · intro k hPrevious
    apply (point_formula_l ξ _).mpr
    intro x y hx hy
    have hjS := (SecondOrderFunctionProperties.value_mem_l hℳ hF.2.1 hx).1
    have hkN := predecessor_bound_l K hn hF.1 k hjS
    have hjT := (SecondOrderFunctionProperties.value_mem_l hℳ hG.2.1 hy).1
    have hkM := predecessor_bound_l K hm hG.1 k hjT
    have hkS := (hF.1 (numberCode_l K k).val).mpr (Or.inl hkN)
    have hkT := (hG.1 (numberCode_l K k).val).mpr (Or.inl hkM)
    obtain ⟨z, hz, _⟩ := hF.2.1.2 _ hkS
    obtain ⟨w, hw, _⟩ := hG.2.1.2 _ hkT
    have hzw := (point_formula_l ξ _).mp hPrevious z w hz.2 hw.2
    have hSucc := PowerlessBMSQuotientSuccessor.successor_l K k
    have hφF := hF.2.2.2 (numberCode_l K k).val
      (numberCode_l K (SecondOrderModel.succ_l k)).val z x hkN hSucc hz.2 hx
    have hφG := hG.2.2.2 (numberCode_l K k).val
      (numberCode_l K (SecondOrderModel.succ_l k)).val w y hkM hSucc hw.2 hy
    rw [← hzw] at hφG
    exact hUnique z x y hφF hφG

-- 保留同长度旧接口；不同长度的共同坐标规格由上面的实际公式归纳给出。
theorem values_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    {e a n S D f T E g : type_l hℳ} (hn : mem_l hℳ n K.omega)
    (he : e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hF : trace_l φ η e a n S D f) (hG : trace_l φ η e a n T E g)
    (hUnique : ∀ x y z, φ.satisfies ((η.pushFree x).pushFree y) →
      φ.satisfies ((η.pushFree x).pushFree z) → y = z) :
    ∀ i x y, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f i x →
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g i y → x = y :=
  overlap_values_l K φ η hn hn he hF hG hUnique

theorem unique_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    {e a n S D f T E g : type_l hℳ} (hn : mem_l hℳ n K.omega)
    (he : e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hF : trace_l φ η e a n S D f) (hG : trace_l φ η e a n T E g)
    (hUnique : ∀ x y z, φ.satisfies ((η.pushFree x).pushFree y) →
      φ.satisfies ((η.pushFree x).pushFree z) → y = z) : f = g := by
  have hValues := values_l K φ η hn he hF hG hUnique
  have hST := successor_unique_l hF.1 hG.1
  apply SecondOrderQuotient.ext_l hℳ
  intro p
  constructor
  · intro hp
    obtain ⟨i, x, hi, _, hPair⟩ := hF.2.1.1 p hp
    obtain ⟨y, hy, _⟩ := hG.2.1.2 i (hST ▸ hi)
    have hxy := hValues i x y ⟨p, hp, hPair⟩ hy.2
    obtain ⟨q, hq, hPair'⟩ := hy.2
    have hpq := SecondOrderPairObjects.ordered_unique_l hℳ hPair (hxy.symm ▸ hPair')
    exact hpq.symm ▸ hq
  · intro hp
    obtain ⟨i, y, hi, _, hPair⟩ := hG.2.1.1 p hp
    obtain ⟨x, hx, _⟩ := hF.2.1.2 i (hST.symm ▸ hi)
    have hxy := hValues i x y hx.2 ⟨p, hp, hPair⟩
    obtain ⟨q, hq, hPair'⟩ := hx.2
    have hpq := SecondOrderPairObjects.ordered_unique_l hℳ hPair (hxy ▸ hPair')
    exact hpq.symm ▸ hq

def functional_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    .imp (at_m φ (.bvar (.there (.there .here))) (.bvar (.there .here))) <|
      .imp (at_m φ (.bvar (.there (.there .here))) (.bvar .here))
        (.equal (.bvar (.there .here)) (.bvar .here))

def conclusion_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (e a n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    .forallE .set <| .forallE .set <| .forallE .set <|
      let S : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
        .bvar (.there (.there (.there (.there (.there .here)))))
      let D := .bvar (.there (.there (.there (.there .here))))
      let f := .bvar (.there (.there (.there .here)))
      let T := .bvar (.there (.there .here))
      let E := .bvar (.there .here)
      let g := .bvar .here
      .imp (trace_m φ (up₆ e) (up₆ a) (up₆ n) S D f) <|
        .imp (trace_m φ (up₆ e) (up₆ a) (up₆ n) T E g) (.equal f g)

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <| .imp (functional_m φ) <|
      .imp (SecondOrderObjectSyntax.member_m n ω) (conclusion_m φ e a n)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e a n : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ ω e a n)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ω e a n : Term ℒ [] Δ .set) :
    (sentence_m φ ω e a n).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, functional_m, conclusion_m,
    PowerlessDefinableFiniteTraceDerives.zero_m, Formula.satisfies,
    SecondOrderOmegaSyntax.omega_l, trace_formula_l, at_formula_l,
    parameters_pushBound_l, parameters_empty_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up₆, up₃, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hω he hUnique hn S D f T E g hF hG
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  rw [SecondOrderOmega.unique_l h𝒩 hω K.omega_spec] at hn
  have he' : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := by
    apply SecondOrderQuotient.ext_l h𝒩
    intro x
    exact iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x)
  exact unique_l K φ η hn he' hF hG hUnique

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e a n : Term ℒ [] Δ .set) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ ω e a n)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ ω e a n)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableFiniteTraceUnique
