import BMSConstructibleBridge.SecondOrderFormulaParameters
import BMSConstructibleBridge.SecondOrderMemberDefPacket
import BMSConstructibleBridge.SecondOrderInterpretation

/-! # 原图 Def 证书中的实际相等和隶属原子

正规化和双模拟均复用原 AST。这里的自由参数是原图、母根与默认成员编号，
量词仍遍历同一原模型的全部数和实数；不添加新的原子解释。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefAtoms

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) := t.weakenBound sort_m.num

def normal_m {Γ Δ : SortContext signature_m} (A : Term signature_m Γ Δ .set)
    (r a n b : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  SecondOrderRelationSpecification.body_m SecondOrderMemberNormalizer.formula_m n b
    (fun v => match v with | .here => A | .there .here => r | .there (.there .here) => a)

theorem normal_pure_m {Γ Δ : SortContext signature_m} (A : Term signature_m Γ Δ .set)
    (r a n b : Term signature_m Γ Δ .num) (hA : pure_term_m A = true)
    (hr : pure_term_m r = true) (ha : pure_term_m a = true)
    (hn : pure_term_m n = true) (hb : pure_term_m b = true) : language_m (normal_m A r a n b) = true := by
  apply SecondOrderRelationSpecification.body_pure_m _ _ _ _ (pure_language_m _ rfl) hn hb
  intro s v
  match v with
  | .here => exact hA
  | .there .here => exact hr
  | .there (.there .here) => exact ha

theorem normal_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (A : Term signature_m Γ Δ .set) (r a n b : Term signature_m Γ Δ .num) :
    (normal_m A r a n b).satisfies η ↔
      b.eval η = SecondOrderMemberNormalizer.value_l (A.eval η) (r.eval η) (a.eval η) (n.eval η) := by
  classical
  rw [normal_m, SecondOrderRelationSpecification.body_formula_l]
  simp only [SecondOrderMemberNormalizer.formula_m, Formula.satisfies, SecondOrderPairing.edge_l]
  change ((SecondOrderPairing.relation_l (A.eval η) (n.eval η) (r.eval η) ∧ b.eval η = n.eval η) ∨
    (¬SecondOrderPairing.relation_l (A.eval η) (n.eval η) (r.eval η) ∧ b.eval η = a.eval η)) ↔ _
  by_cases h : SecondOrderPairing.relation_l (A.eval η) (n.eval η) (r.eval η) <;>
    simp [SecondOrderMemberNormalizer.value_l, h]

def normalized_m {Γ Δ : SortContext signature_m}
    (φ : Formula signature_m [] [.set, .set, .num, .num])
    (A : Term signature_m Γ Δ .set) (r a n m : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num <| .existsE .num <|
    .conj (normal_m (up (up A)) (up (up r)) (up (up a)) (up (up n)) (.bvar (.there .here))) <|
      .conj (normal_m (up (up A)) (up (up r)) (up (up a)) (up (up m)) (.bvar .here))
        (GraphTranslation.atom_m φ (up (up A)) (up (up A)) (.bvar (.there .here)) (.bvar .here))

private theorem up_pure_m {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) (ht : pure_term_m t = true) : pure_term_m (up (up t)) = true :=
  (SecondOrderSubstitution.term_weaken_m (up t) sort_m.num).trans
    ((SecondOrderSubstitution.term_weaken_m t sort_m.num).trans ht)

theorem normalized_pure_m {Γ Δ : SortContext signature_m}
    (φ : Formula signature_m [] [.set, .set, .num, .num]) (hφ : language_m φ = true)
    (A : Term signature_m Γ Δ .set) (r a n m : Term signature_m Γ Δ .num)
    (hA : pure_term_m A = true) (hr : pure_term_m r = true) (ha : pure_term_m a = true)
    (hn : pure_term_m n = true) (hm : pure_term_m m = true) : language_m (normalized_m φ A r a n m) = true := by
  have hN := normal_pure_m (Γ := .num :: .num :: Γ) (up (up A)) (up (up r)) (up (up a)) (up (up n))
    (.bvar (.there .here)) (up_pure_m A hA) (up_pure_m r hr) (up_pure_m a ha) (up_pure_m n hn) rfl
  have hM := normal_pure_m (Γ := .num :: .num :: Γ) (up (up A)) (up (up r)) (up (up a)) (up (up m))
    (.bvar .here) (up_pure_m A hA) (up_pure_m r hr) (up_pure_m a ha) (up_pure_m m hm) rfl
  have hAtom := GraphTranslation.atom_pure_m φ (Γ := .num :: .num :: Γ)
    (up (up A)) (up (up A)) (.bvar (.there .here)) (.bvar .here) hφ
    (up_pure_m A hA) (up_pure_m A hA) rfl rfl
  change (language_m _ && (language_m _ && language_m _)) = true
  rw [hN, hM, hAtom]
  rfl

def equality_m : Formula signature_m [] [.num, .num, .set, .num, .num] :=
  normalized_m GraphSyntax.eq_m (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar .here) (.fvar (.there .here))

def membership_m : Formula signature_m [] [.num, .num, .set, .num, .num] :=
  normalized_m GraphSyntax.mem_m (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar .here) (.fvar (.there .here))

theorem equality_pure_m : language_m equality_m = true :=
  normalized_pure_m _ (pure_language_m GraphSyntax.matrix_m GraphSyntax.matrix_pure_m)
    _ _ _ _ _ rfl rfl rfl rfl rfl

theorem membership_pure_m : language_m membership_m = true :=
  normalized_pure_m _ (pure_language_m GraphSyntax.mem_matrix_m GraphSyntax.mem_matrix_pure_m)
    _ _ _ _ _ rfl rfl rfl rfl rfl

theorem equality_formula_l (A : set_l ℳ) (r a n m : num_l ℳ) : equality_m.satisfies
    ((((((Env.empty (M := ℳ)).pushFree a).pushFree r).pushFree A).pushFree m).pushFree n) ↔
      SecondOrderBisimulation.eq_l A A (SecondOrderMemberNormalizer.value_l A r a n)
        (SecondOrderMemberNormalizer.value_l A r a m) := by
  simp only [equality_m, normalized_m, Formula.satisfies, normal_formula_l,
    SecondOrderInterpretation.eq_l, up, Term.eval_weakenBound, Term.eval]
  change (∃ x y, x = SecondOrderMemberNormalizer.value_l A r a n ∧
    y = SecondOrderMemberNormalizer.value_l A r a m ∧ SecondOrderBisimulation.eq_l A A x y) ↔ _
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, _, rfl, rfl, h⟩

theorem membership_formula_l (A : set_l ℳ) (r a n m : num_l ℳ) : membership_m.satisfies
    ((((((Env.empty (M := ℳ)).pushFree a).pushFree r).pushFree A).pushFree m).pushFree n) ↔
      ∃ b, SecondOrderPairing.relation_l A b (SecondOrderMemberNormalizer.value_l A r a m) ∧
        SecondOrderBisimulation.eq_l A A (SecondOrderMemberNormalizer.value_l A r a n) b := by
  simp only [membership_m, normalized_m, Formula.satisfies, normal_formula_l,
    SecondOrderInterpretation.mem_l, up, Term.eval_weakenBound, Term.eval]
  change (∃ x y, x = SecondOrderMemberNormalizer.value_l A r a n ∧
    y = SecondOrderMemberNormalizer.value_l A r a m ∧ ∃ b, SecondOrderPairing.relation_l A b y ∧
      SecondOrderBisimulation.eq_l A A x b) ↔ _
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, _, rfl, rfl, h⟩

#print axioms equality_formula_l
#print axioms membership_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefAtoms
