import BMSConstructibleBridge.SecondOrderMinimum
import BMSConstructibleBridge.SecondOrderBisimulation

/-! # 母根各成员的最小数代表

内部双模拟相等图给定后，以模型内最小数规范化每个成员。不将商对象编码
成外部类型值，也不要求模型的自然数外部标准或良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRootRepresentatives

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def representative_l (A Q : set_l ℳ) (r n : num_l ℳ) : Prop :=
  relation_l A n r ∧ ∀ m, SecondOrderOrder.lt_l m n → relation_l A m r → ¬relation_l Q m n

def spec_l (A Q D : set_l ℳ) (r : num_l ℳ) : Prop :=
  ∀ n, mem_l n D ↔ representative_l A Q r n

def formula_m : Formula signature_m [] [.num, .set, .num, .set] :=
  .conj (GraphSyntax.edge_m (.fvar (.there .here)) (.fvar .here) (.fvar (.there (.there .here)))) <|
    .forallE .num <| .imp (PrimitiveFormulas.lt_m (.bvar .here) (.fvar .here)) <|
      .imp (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar .here) (.fvar (.there (.there .here))))
        (.neg (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.bvar .here) (.fvar .here)))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem formula_l (A Q : set_l ℳ) (r n : num_l ℳ) :
    formula_m.satisfies (((((Env.empty (M := ℳ)).pushFree Q).pushFree r).pushFree A).pushFree n) ↔
      representative_l A Q r n := by
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderOrder.formula_l]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A Q : set_l ℳ) (r : num_l ℳ) :
    ∃! D, spec_l A Q D r := by
  obtain ⟨D, hD⟩ := comprehension_l hℳ formula_m pure_m
    ((((Env.empty (M := ℳ)).pushFree Q).pushFree r).pushFree A)
  have hSpec : spec_l A Q D r := fun n => (hD n).trans (formula_l A Q r n)
  exact ⟨D, hSpec, fun E hE => ext_l hℳ E D (fun n => (hE n).trans (hSpec n).symm)⟩

theorem covers_l (hℳ : Theory.Models ℳ theory_m) {A Q D : set_l ℳ} {r b : num_l ℳ}
    (hQ : ∀ m n, relation_l Q m n ↔ SecondOrderBisimulation.eq_l A A m n)
    (hD : spec_l A Q D r) (hb : relation_l A b r) :
    ∃ n, mem_l n D ∧ SecondOrderBisimulation.eq_l A A n b := by
  let φ : Formula signature_m [] [.num, .set, .num, .set, .num] :=
    .conj (GraphSyntax.edge_m (.fvar (.there .here)) (.fvar .here) (.fvar (.there (.there .here))))
      (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.fvar .here)
        (.fvar (.there (.there (.there (.there .here))))))
  obtain ⟨P, hP⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    (((((Env.empty (M := ℳ)).pushFree b).pushFree Q).pushFree r).pushFree A)
  have hRead n : mem_l n P ↔ relation_l A n r ∧ relation_l Q n b := by
    refine (hP n).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l]
    rfl
  have hStart : mem_l b P := (hRead b).mpr ⟨hb, (hQ b b).mpr (SecondOrderBisimulation.refl_l hℳ A b)⟩
  obtain ⟨n, hn, hMin⟩ := SecondOrderMinimum.exists_l hℳ P ⟨b, hStart⟩
  obtain ⟨hnA, hnQ⟩ := (hRead n).mp hn
  have hEq := (hQ n b).mp hnQ
  refine ⟨n, (hD n).mpr ⟨hnA, ?_⟩, hEq⟩
  intro m hm hmA hmQ
  have hMB := SecondOrderBisimulation.trans_l hℳ A A A m n b ((hQ m n).mp hmQ) hEq
  exact hMin m hm ((hRead m).mpr ⟨hmA, (hQ m b).mpr hMB⟩)

theorem injective_l (hℳ : Theory.Models ℳ theory_m) {A Q D : set_l ℳ} {r m n : num_l ℳ}
    (hQ : ∀ i j, relation_l Q i j ↔ SecondOrderBisimulation.eq_l A A i j)
    (hD : spec_l A Q D r) (hm : mem_l m D) (hn : mem_l n D)
    (hEq : SecondOrderBisimulation.eq_l A A m n) : m = n := by
  have hm' := (hD m).mp hm
  have hn' := (hD n).mp hn
  rcases SecondOrderOrder.trichotomy_l hℳ m n with h | h | h
  · exact False.elim (hn'.2 m h hm'.1 ((hQ m n).mpr hEq))
  · exact h
  · exact False.elim (hm'.2 n h hn'.1 ((hQ n m).mpr (SecondOrderBisimulation.symm_l hℳ A A m n hEq)))

#print axioms covers_l
#print axioms injective_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRootRepresentatives
