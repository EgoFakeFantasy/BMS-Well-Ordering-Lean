import BMSConstructibleBridge.SecondOrderMemberDefAtoms

/-! # 完整原图 Def 证书的对象公式

原算术证书与相等／隶属原子以合取组合；后者不能用析取弱化。自由参数的
顺序固定为 V,E,D,Q,R,T,F,A,r,a，每个实数证书仍属于原模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefPacketFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def atom_parameters_m {Γ Δ : SortContext signature_m} (A : Term signature_m Γ Δ .set)
    (r a : Term signature_m Γ Δ .num) : VariableSubstitution signature_m [.set, .num, .num] Γ Δ
  | _, .here => A
  | _, .there .here => r
  | _, .there (.there .here) => a

def atoms_m {Γ Δ : SortContext signature_m} (A : Term signature_m Γ Δ .set)
    (r a : Term signature_m Γ Δ .num) (Q R : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .conj (SecondOrderRelationSpecification.formula_m SecondOrderMemberDefAtoms.equality_m Q
    (atom_parameters_m A r a))
    (SecondOrderRelationSpecification.formula_m SecondOrderMemberDefAtoms.membership_m R
      (atom_parameters_m A r a))

theorem atoms_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (A : Term signature_m Γ Δ .set) (r a : Term signature_m Γ Δ .num)
    (Q R : Term signature_m Γ Δ .set) : (atoms_m A r a Q R).satisfies η ↔
      (∀ n m, SecondOrderPairing.relation_l (Q.eval η) n m ↔ SecondOrderBisimulation.eq_l (A.eval η) (A.eval η)
        (SecondOrderMemberNormalizer.value_l (A.eval η) (r.eval η) (a.eval η) n)
        (SecondOrderMemberNormalizer.value_l (A.eval η) (r.eval η) (a.eval η) m)) ∧
      ∀ n m, SecondOrderPairing.relation_l (R.eval η) n m ↔ ∃ b,
        SecondOrderPairing.relation_l (A.eval η) b
          (SecondOrderMemberNormalizer.value_l (A.eval η) (r.eval η) (a.eval η) m) ∧
        SecondOrderBisimulation.eq_l (A.eval η) (A.eval η)
          (SecondOrderMemberNormalizer.value_l (A.eval η) (r.eval η) (a.eval η) n) b := by
  have hEnv : SecondOrderRelationSpecification.parameters_l η (atom_parameters_m A r a) =
      (((Env.empty (M := ℳ)).pushFree (a.eval η)).pushFree (r.eval η)).pushFree (A.eval η) := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => cases v with
          | here => rfl
          | there v => nomatch v
  simp only [atoms_m, Formula.satisfies, SecondOrderRelationSpecification.formula_l, hEnv,
    SecondOrderMemberDefAtoms.equality_formula_l, SecondOrderMemberDefAtoms.membership_formula_l]

def arithmetic_parameters_m {Γ Δ : SortContext signature_m}
    (V E D Q R T F : Term signature_m Γ Δ .set) :
    VariableSubstitution signature_m [.set, .set, .set, .set, .set, .set, .set] Γ Δ
  | _, .here => V
  | _, .there .here => E
  | _, .there (.there .here) => D
  | _, .there (.there (.there .here)) => Q
  | _, .there (.there (.there (.there .here))) => R
  | _, .there (.there (.there (.there (.there .here)))) => T
  | _, .there (.there (.there (.there (.there (.there .here))))) => F

def packet_m {Γ Δ : SortContext signature_m} (A : Term signature_m Γ Δ .set)
    (r a : Term signature_m Γ Δ .num) (V E D Q R T F : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  .conj (SecondOrderFormulaParameters.formula_m SecondOrderMemberDefArithmetic.formula_m
    (arithmetic_parameters_m V E D Q R T F)) (atoms_m A r a Q R)

theorem packet_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (A : Term signature_m Γ Δ .set) (r a : Term signature_m Γ Δ .num)
    (V E D Q R T F : Term signature_m Γ Δ .set) : (packet_m A r a V E D Q R T F).satisfies η ↔
      SecondOrderMemberDefPacket.spec_l (A.eval η) (r.eval η) (a.eval η)
        (V.eval η) (E.eval η) (D.eval η) (Q.eval η) (R.eval η) (T.eval η) (F.eval η) := by
  rw [packet_m, Formula.satisfies, SecondOrderFormulaParameters.formula_l,
    SecondOrderMemberDefArithmetic.formula_m, SecondOrderMemberDefArithmetic.packet_formula_l, atoms_formula_l]
  constructor
  · rintro ⟨⟨hV, hE, hD, hT, hF⟩, hQ, hR⟩
    exact ⟨hV, hE, hD, hQ, hR, hT, hF⟩
  · intro h
    exact ⟨⟨h.formula_codes, h.powers, h.domain, h.evaluation, h.family⟩, h.equality, h.membership⟩

abbrev context_m : SortContext signature_m := [.set, .set, .set, .set, .set, .set, .set, .set, .num, .num]

def formula_m : Formula signature_m [] context_m :=
  packet_m (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))

theorem pure_m : language_m formula_m = true := by
  have hArithmetic : language_m (SecondOrderFormulaParameters.formula_m SecondOrderMemberDefArithmetic.formula_m
    (arithmetic_parameters_m (Γ := []) (Δ := context_m)
      (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here))))))))) = true := by
    apply SecondOrderFormulaParameters.pure_m SecondOrderMemberDefArithmetic.formula_m
      (fun v => match v with
        | .here => .fvar .here
        | .there .here => .fvar (.there .here)
        | .there (.there .here) => .fvar (.there (.there .here))
        | .there (.there (.there .here)) => .fvar (.there (.there (.there .here)))
        | .there (.there (.there (.there .here))) => .fvar (.there (.there (.there (.there .here))))
        | .there (.there (.there (.there (.there .here)))) => .fvar (.there (.there (.there (.there (.there .here)))))
        | .there (.there (.there (.there (.there (.there .here))))) =>
          .fvar (.there (.there (.there (.there (.there (.there .here)))))))
      SecondOrderMemberDefArithmetic.pure_m
    intro s v
    match v with
    | .here => rfl
    | .there .here => rfl
    | .there (.there .here) => rfl
    | .there (.there (.there .here)) => rfl
    | .there (.there (.there (.there .here))) => rfl
    | .there (.there (.there (.there (.there .here)))) => rfl
    | .there (.there (.there (.there (.there (.there .here))))) => rfl
  let A : Term signature_m [] context_m .set :=
    .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let r : Term signature_m [] context_m .num :=
    .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let a : Term signature_m [] context_m .num :=
    .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
  have hParams : SecondOrderSubstitution.images_m (atom_parameters_m A r a) := by
    intro s v
    match v with
    | .here => rfl
    | .there .here => rfl
    | .there (.there .here) => rfl
  have hQ := SecondOrderRelationSpecification.pure_m SecondOrderMemberDefAtoms.equality_m
    (.fvar (.there (.there (.there .here)))) (atom_parameters_m A r a)
    SecondOrderMemberDefAtoms.equality_pure_m rfl hParams
  have hR := SecondOrderRelationSpecification.pure_m SecondOrderMemberDefAtoms.membership_m
    (.fvar (.there (.there (.there (.there .here))))) (atom_parameters_m A r a)
    SecondOrderMemberDefAtoms.membership_pure_m rfl hParams
  change (language_m _ && (language_m _ && language_m _)) = true
  rw [hArithmetic, hQ, hR]
  rfl

#print axioms packet_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefPacketFormula
