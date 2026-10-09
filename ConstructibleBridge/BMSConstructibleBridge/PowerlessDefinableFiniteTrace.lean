import BMSConstructibleBridge.SecondOrderFunctionAppendDerives
import BMSConstructibleBridge.SecondOrderNaturalCases
import BMSConstructibleBridge.SecondOrderOmegaTransitive
import BMSConstructibleBridge.PowerlessBMSQuotientInduction
import BMSConstructibleBridge.PowerlessNaturalStep
import BMSConstructibleBridge.PowerlessBMSQuotientSubsetImageDerives

/-! # 无 Collection 的可定义关系内部有限轨迹

背景为原 Z₂，语言为纯隶属语言。任意总的原二元公式关系，在每个
内部自然数长度上都有实际有限函数图。陪域逐步扩大，不假定无限
轨迹集合或共同像界存在；归纳实例经原图翻译覆盖非标准内部长度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableFiniteTrace

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives (at_m at_formula_l parameters_l
  parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₃ t)

def trace_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (e a n S D f : carrier_l 𝒱) : Prop :=
  PowerlessNatural.successor_l n S ∧ map_l f S D ∧ value_l f e a ∧
    ∀ i j x y, member_l 𝒱 i n → PowerlessNatural.successor_l i j →
      value_l f i x → value_l f j y → φ.satisfies ((η.pushFree x).pushFree y)

def trace_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (e a n S D f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessNaturalStep.successor_m n S) <| .conj
    (SecondOrderObjectSyntax.map_m f S D) <| .conj
      (SecondOrderObjectSyntax.value_m f e a) <|
        .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
          let i : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set :=
            .bvar (.there (.there (.there .here)))
          let j := .bvar (.there (.there .here))
          let x := .bvar (.there .here)
          let y := .bvar .here
          .imp (SecondOrderObjectSyntax.member_m i (up₄ n)) <|
            .imp (PowerlessNaturalStep.successor_m i j) <|
              .imp (SecondOrderObjectSyntax.value_m (up₄ f) i x) <|
                .imp (SecondOrderObjectSyntax.value_m (up₄ f) j y) (at_m φ x y)

theorem trace_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (e a n S D f : Term ℒ Γ Δ .set) :
    (trace_m φ e a n S D f).satisfies η ↔
      trace_l φ (parameters_l η) (e.eval η) (a.eval η) (n.eval η)
        (S.eval η) (D.eval η) (f.eval η) := by
  simp only [trace_m, trace_l, Formula.satisfies, PowerlessNaturalStep.successor_formula_l,
    map_formula_l, value_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    at_formula_l, parameters_pushBound_l, up₄, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def finite_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (e a n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    trace_m φ (up₃ e) (up₃ a) (up₃ n) (.bvar (.there (.there .here)))
      (.bvar (.there .here)) (.bvar .here)

theorem finite_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (e a n : Term ℒ Γ Δ .set) :
    (finite_m φ e a n).satisfies η ↔ ∃ S D f,
      trace_l φ (parameters_l η) (e.eval η) (a.eval η) (n.eval η) S D f := by
  simp only [finite_m, Formula.satisfies, trace_formula_l, parameters_pushBound_l,
    up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

private def lift_variables_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [] (.set :: .set :: .set :: Δ)
  | _, .here => .fvar .here
  | _, .there .here => .fvar (.there .here)
  | _, .there (.there v) => .fvar (.there (.there (.there v)))

def lift_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: Δ) :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ) [] (.set :: .set :: .set :: Δ) from
    .map (fun v => nomatch v) lift_variables_m)

theorem lift_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (n x y : carrier_l 𝒱) :
    (lift_m φ).satisfies ((((η.pushFree n).pushFree x).pushFree y)) ↔
      φ.satisfies ((η.pushFree x).pushFree y) := by
  rw [lift_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro s v; nomatch v
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

def point_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (e a : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: Δ) :=
  finite_m (lift_m φ) (e.weakenFree SetTheory.SetSort.set)
    (a.weakenFree SetTheory.SetSort.set) (.fvar .here)

theorem point_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (e a : Term ℒ [] Δ .set) (n : carrier_l 𝒱) :
    (point_m φ e a).satisfies (η.pushFree n) ↔
      ∃ S D f, trace_l φ η (e.eval η) (a.eval η) n S D f := by
  simp only [point_m, finite_formula_l, parameters_empty_l,
    Term.eval_weakenFree, Term.eval, trace_l, lift_formula_l, Env.pushFree_here]

theorem induction_derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (e a : Term ℒ [] Δ .set) : Derives SecondOrderArithmetic.theory_m []
      (SecondOrderArithmetic.induction_m (GraphTranslation.form_m (point_m φ e a))) :=
  GraphTranslation.induction_m (point_m φ e a)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private theorem successor_unique_l {i j k : type_l hℳ}
    (hj : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) i j)
    (hk : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) i k) : j = k :=
  SecondOrderQuotient.ext_l hℳ j k (fun x => (hj x).trans (hk x).symm)

theorem step_bound_l (K : source_coding_l hℳ) {i j n S : type_l hℳ}
    (hn : mem_l hℳ n K.omega) (hi : mem_l hℳ i n)
    (hij : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) i j)
    (hS : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) n S) :
    mem_l hℳ j S := by
  obtain ⟨k, hk⟩ := numberCode_surjective_l K ⟨i,
    SecondOrderOmegaTransitive.member_l hℳ K.omega_spec hn hi⟩
  obtain ⟨l, hl⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have hk' := congrArg Subtype.val hk
  have hl' := congrArg Subtype.val hl
  have hj := successor_unique_l hij (hk' ▸ PowerlessBMSQuotientSuccessor.successor_l K k)
  have hS' := successor_unique_l hS (hl' ▸ PowerlessBMSQuotientSuccessor.successor_l K l)
  rw [hj, hS']
  apply (numberCode_mem_iff_lt_l K _ _).mpr
  apply (SecondOrderOrder.succ_iff_l hℳ k l).mpr
  exact (numberCode_mem_iff_lt_l K k l).mp (hk'.symm ▸ hl'.symm ▸ hi)

theorem extension_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    {e a n S D f T E g z d : type_l hℳ} (hn : mem_l hℳ n K.omega)
    (hF : trace_l φ η e a n S D f)
    (hG : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) g T E)
    (hT : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) S T)
    (hRead : ∀ x y, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g x y ↔
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f x y ∨ x = S ∧ y = d)
    (hz : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f n z)
    (hd : φ.satisfies ((η.pushFree z).pushFree d)) : trace_l φ η e a S T E g := by
  have hnS := (hF.1 n).mpr (Or.inr rfl)
  refine ⟨hT, hG, (hRead e a).mpr (Or.inl hF.2.2.1), ?_⟩
  intro i j x y hi hij hx hy
  rcases (hF.1 i).mp hi with hi | hiEq
  · have hjS := step_bound_l K hn hi hij hF.1
    have hxOld : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f i x := by
      rcases (hRead i x).mp hx with hxOld | ⟨hiS, _⟩
      · exact hxOld
      · have hSn : mem_l hℳ S n := hiS ▸ hi
        have hSS := (hF.1 S).mpr (Or.inl hSn)
        exact (SecondOrderNaturalCases.asymmetry_l hℳ hSS hSS).elim
    have hyOld : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f j y := by
      rcases (hRead j y).mp hy with hyOld | ⟨rfl, _⟩
      · exact hyOld
      · exact (SecondOrderNaturalCases.asymmetry_l hℳ hjS hjS).elim
    exact hF.2.2.2 i j x y hi hij hxOld hyOld
  · subst i
    have hxOld : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f n x := by
      rcases (hRead n x).mp hx with hxOld | ⟨hnEq, _⟩
      · exact hxOld
      · have hSS := hnEq ▸ hnS
        exact (SecondOrderNaturalCases.asymmetry_l hℳ hSS hSS).elim
    have hxz := SecondOrderFunctionProperties.value_unique_l hℳ hF.2.1 hxOld hz
    have hjEq := successor_unique_l hij hF.1
    subst j
    have hyd : y = d := by
      rcases (hRead S y).mp hy with hyOld | ⟨_, hyd⟩
      · have hSS := (SecondOrderFunctionProperties.value_mem_l hℳ hF.2.1 hyOld).1
        exact (SecondOrderNaturalCases.asymmetry_l hℳ hSS hSS).elim
      · exact hyd
    simpa only [hxz, hyd] using hd

theorem extend_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    {e a n S D f : type_l hℳ} (hn : mem_l hℳ n K.omega)
    (hF : trace_l φ η e a n S D f)
    (hTotal : ∀ x, ∃ y, φ.satisfies ((η.pushFree x).pushFree y)) :
    ∃ T E g, trace_l φ η e a S T E g := by
  obtain ⟨z, hz, _⟩ := hF.2.1.2 n ((hF.1 n).mpr (Or.inr rfl))
  obtain ⟨d, hd⟩ := hTotal z
  obtain ⟨T, E, g, hT, _, hG, hRead⟩ := SecondOrderFunctionAppendDerives.exists_l hℳ d hF.2.1
    (fun hSS => SecondOrderNaturalCases.asymmetry_l hℳ hSS hSS)
  exact ⟨T, E, g, extension_l K φ η hn hF hG hT hRead hz.2 hd⟩

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (e a : Term ℒ [] Δ .set)
    (he : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hTotal : ∀ x, ∃ y, φ.satisfies ((η.pushFree x).pushFree y))
    (n : SecondOrderModel.num_l ℳ) : ∃ S D f,
    trace_l φ η (e.eval η) (a.eval η) (numberCode_l K n).val S D f := by
  have h := PowerlessBMSQuotientInduction.induction_l K (point_m φ e a) η ?_ ?_
  · exact (point_formula_l φ η e a _).mp (h n)
  · apply (point_formula_l φ η e a _).mpr
    let z := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
    let S := (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val
    have hS := PowerlessBMSQuotientSuccessor.successor_l K (SecondOrderModel.zero_l ℳ)
    have hz := PowerlessBMSQuotientSuccessor.zero_l K
    obtain ⟨D, hD⟩ := SecondOrderPairObjects.pair_exists_l hℳ (a.eval η) (a.eval η)
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ z (a.eval η)
    obtain ⟨f, hf⟩ := SecondOrderPairObjects.pair_exists_l hℳ p p
    have hSingleton := SecondOrderFunctionAppend.singleton_l hℳ
      (fun x => (hS x).trans (or_iff_right (hz x)))
      ((hD (a.eval η)).mpr (Or.inl rfl)) hp
      (fun q => by simpa only [or_self] using hf q)
    exact ⟨S, D, f, hS, hSingleton.1,
      (hSingleton.2 _ _).mpr ⟨he, rfl⟩, fun i _ _ _ hi => (hz i hi).elim⟩
  · intro i hF
    obtain ⟨S, D, f, hF⟩ := (point_formula_l φ η e a _).mp hF
    have hSEq := successor_unique_l hF.1 (PowerlessBMSQuotientSuccessor.successor_l K i)
    apply (point_formula_l φ η e a _).mpr
    rw [← hSEq]
    exact extend_l K φ η (n := (numberCode_l K i).val) (numberCode_l K i).property hF hTotal

#print axioms trace_formula_l
#print axioms induction_derives_m
#print axioms step_bound_l
#print axioms extension_l
#print axioms extend_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableFiniteTrace
