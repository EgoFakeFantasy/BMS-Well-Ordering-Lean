import BMSConstructibleBridge.PowerlessBoundedAddition
import BMSConstructibleBridge.PowerlessFormulaConstructor
import BMSConstructibleBridge.PowerlessSuccessorBounded
import BMSConstructibleBridge.SecondOrderAxioms

/-! # 原三角配数语法构造子的纯 Δ₀ 检查

保留原 c=T(a+b)+a 配数和节点后继，不偷换为平方配数。给定实际 ω 值
图 T，全部算术见证限制在 ω 和全体有限数值序列集 S；这里只要求 T 是
ω 自映射，三角递推规格由后续实际语法实例另行提供。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaConstructorBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def code_m {Γ Δ : SortContext ℒ} (ω e S T a b c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <|
    .conj (PowerlessBoundedAddition.formula_m (w ω) (w e) (w S) (w a) (w b) (.bvar (.there .here))) <|
      .conj (PowerlessValueBounded.formula_m (w T) (.bvar (.there .here)) (.bvar .here))
        (PowerlessBoundedAddition.formula_m (w ω) (w e) (w S) (.bvar .here) (w a) (w c))

theorem code_delta_l {Γ Δ : SortContext ℒ} (ω e S T a b c : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (code_m ω e S T a b c) :=
  .bounded_exists ω (.bounded_exists (up ω) (.conj (PowerlessBoundedAddition.delta_l _ _ _ _ _ _)
    (.conj (PowerlessValueBounded.delta_l _ _ _) (PowerlessBoundedAddition.delta_l _ _ _ _ _ _))))

def code_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S T a b c : carrier_l 𝒩) : Prop :=
  ∃ s, member_l 𝒩 s ω ∧ ∃ t, member_l 𝒩 t ω ∧
    PowerlessBoundedAddition.holds_l (𝒩 := 𝒩) ω e S a b s ∧ value_l (ℳ := 𝒩) T s t ∧
    PowerlessBoundedAddition.holds_l (𝒩 := 𝒩) ω e S t a c

theorem code_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S T a b c : Term ℒ Γ Δ .set) :
    (code_m ω e S T a b c).satisfies η ↔
      code_l (ω.eval η) (e.eval η) (S.eval η) (T.eval η) (a.eval η) (b.eval η) (c.eval η) := by
  simp only [code_m, code_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedAddition.formula_l,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def node_m {Γ Δ : SortContext ℒ} (ω e S T t p n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (SecondOrderObjectSyntax.member_m t ω) <| .conj (SecondOrderObjectSyntax.member_m p ω) <|
    membershipLevyBound.boundedExists ω <| .conj
      (code_m (up ω) (up e) (up S) (up T) (up t) (up p) (.bvar .here))
      (PowerlessSuccessorBounded.formula_m (.bvar .here) (up n))

theorem node_delta_l {Γ Δ : SortContext ℒ} (ω e S T t p n : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (node_m ω e S T t p n) :=
  .conj (.rel _ _) (.conj (.rel _ _) (.bounded_exists ω
    (.conj (code_delta_l _ _ _ _ _ _ _) (PowerlessSuccessorBounded.delta_l _ _))))

def node_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S T t p n : carrier_l 𝒩) : Prop :=
  member_l 𝒩 t ω ∧ member_l 𝒩 p ω ∧ ∃ c, member_l 𝒩 c ω ∧
    code_l (𝒩 := 𝒩) ω e S T t p c ∧ PowerlessNatural.successor_l (ℳ := 𝒩) c n

theorem node_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S T t p n : Term ℒ Γ Δ .set) :
    (node_m ω e S T t p n).satisfies η ↔
      node_l (ω.eval η) (e.eval η) (S.eval η) (T.eval η) (t.eval η) (p.eval η) (n.eval η) := by
  simp only [node_m, node_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, code_formula_l, PowerlessSuccessorBounded.formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def formula_m {Γ Δ : SortContext ℒ} (ω e S T t a b n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (SecondOrderObjectSyntax.member_m a ω) <| .conj (SecondOrderObjectSyntax.member_m b ω) <|
    membershipLevyBound.boundedExists ω <| .conj
      (code_m (up ω) (up e) (up S) (up T) (up a) (up b) (.bvar .here))
      (node_m (up ω) (up e) (up S) (up T) (up t) (.bvar .here) (up n))

theorem delta_l {Γ Δ : SortContext ℒ} (ω e S T t a b n : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e S T t a b n) :=
  .conj (.rel _ _) (.conj (.rel _ _) (.bounded_exists ω
    (.conj (code_delta_l _ _ _ _ _ _ _) (node_delta_l _ _ _ _ _ _ _))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S T t a b n : carrier_l 𝒩) : Prop :=
  member_l 𝒩 a ω ∧ member_l 𝒩 b ω ∧ ∃ p, member_l 𝒩 p ω ∧
    code_l (𝒩 := 𝒩) ω e S T a b p ∧ node_l (𝒩 := 𝒩) ω e S T t p n

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S T t a b n : Term ℒ Γ Δ .set) :
    (formula_m ω e S T t a b n).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (S.eval η) (T.eval η) (t.eval η) (a.eval η) (b.eval η) (n.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, code_formula_l, node_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

theorem addition_iff_l (K : source_coding_l hℳ) {S a b c : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    (ha : mem_l hℳ a K.omega) (hb : mem_l hℳ b K.omega) :
    PowerlessBoundedAddition.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) S a b c ↔
      PowerlessAddition.addition_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) a b c := by
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨a, ha⟩
  obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨b, hb⟩
  have haEq : a = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
  have hbEq : b = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
  rw [haEq, hbEq]
  exact (PowerlessBoundedAddition.instance_l K hS i j c).trans
    (PowerlessBMSQuotientRecursion.addition_iff_l K i j c).symm

theorem addition_natural_l (K : source_coding_l hℳ) {a b c : type_l hℳ}
    (ha : mem_l hℳ a K.omega) (hb : mem_l hℳ b K.omega)
    (hAdd : PowerlessAddition.addition_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) a b c) :
    mem_l hℳ c K.omega := by
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨a, ha⟩
  obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨b, hb⟩
  have haEq : a = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
  have hbEq : b = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
  rw [haEq, hbEq] at hAdd
  exact ((PowerlessBMSQuotientRecursion.addition_iff_l K i j c).mp hAdd).symm ▸
    (numberCode_l K (SecondOrderModel.add_l i j)).property

theorem code_iff_l (K : source_coding_l hℳ) {S T a b c : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega)
    (ha : mem_l hℳ a K.omega) (hb : mem_l hℳ b K.omega) :
    code_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) S T a b c ↔
      PowerlessPairingCode.code_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T a b c := by
  constructor
  · rintro ⟨s, _, t, ht, hAdd, hValue, hOut⟩
    exact ⟨s, t, (addition_iff_l K hS ha hb).mp hAdd, hValue, (addition_iff_l K hS ht ha).mp hOut⟩
  · rintro ⟨s, t, hAdd, hValue, hOut⟩
    have hs := addition_natural_l K ha hb hAdd
    have ht := (SecondOrderFunctionProperties.value_mem_l hℳ hT hValue).2
    exact ⟨s, hs, t, ht, (addition_iff_l K hS ha hb).mpr hAdd, hValue,
      (addition_iff_l K hS ht ha).mpr hOut⟩

theorem code_natural_l (K : source_coding_l hℳ) {T a b c : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega)
    (ha : mem_l hℳ a K.omega)
    (hCode : PowerlessPairingCode.code_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T a b c) :
    mem_l hℳ c K.omega := by
  obtain ⟨_, t, _, hValue, hOut⟩ := hCode
  exact addition_natural_l K (SecondOrderFunctionProperties.value_mem_l hℳ hT hValue).2 ha hOut

theorem node_iff_l (K : source_coding_l hℳ) {S T t p n : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) :
    node_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) S T t p n ↔
      PowerlessFormulaNode.node_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T t p n := by
  constructor
  · rintro ⟨ht, hp, c, _, hCode, hSucc⟩
    exact ⟨ht, hp, c, (code_iff_l K hS hT ht hp).mp hCode, hSucc⟩
  · rintro ⟨ht, hp, c, hCode, hSucc⟩
    exact ⟨ht, hp, c, code_natural_l K hT ht hCode, (code_iff_l K hS hT ht hp).mpr hCode, hSucc⟩

theorem constructor_iff_l (K : source_coding_l hℳ) {S T t a b n : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) S T t a b n ↔
      PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T t a b n := by
  constructor
  · rintro ⟨ha, hb, p, _, hCode, hNode⟩
    exact ⟨ha, hb, p, (code_iff_l K hS hT ha hb).mp hCode, (node_iff_l K hS hT).mp hNode⟩
  · rintro ⟨ha, hb, p, hCode, hNode⟩
    exact ⟨ha, hb, p, code_natural_l K hT ha hCode, (code_iff_l K hS hT ha hb).mpr hCode,
      (node_iff_l K hS hT).mpr hNode⟩

/-- 实际 ω、空集、全有限数值序列集及 ω 自映射 guard 下的原构造子等价。 -/
def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let e : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let S : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let T : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let t : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let a : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let b : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let n : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (up e)))) <|
      .imp (PowerlessFiniteSequencesSyntax.spec_m ω ω S) <|
        .imp (SecondOrderObjectSyntax.map_m T ω ω) <|
          .iff (formula_m ω e S T t a b n) (PowerlessFormulaConstructor.constructor_m ω e T t a b n)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hω he hS hT
  have hω' := (omega_formula_l η _).mp hω
  have he' : ∀ x, ¬ mem_l hℳ x (η.2 (.there .here)) := by
    exact he
  have hS' := (PowerlessFiniteSequencesSyntax.spec_formula_l η _ _ _).mp hS
  have hT' := (map_formula_l η _ _ _).mp hT
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ hω' K.omega_spec
  have heEq := SecondOrderQuotient.ext_l hℳ _ _ (fun x =>
    iff_of_false (he' x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  have hS'' : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega (η.2 (.there (.there .here))) := by simpa only [Term.eval, hωEq] using hS'
  have hT'' : map_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (η.2 (.there (.there (.there .here)))) K.omega K.omega := by
    simpa only [Term.eval, hωEq] using hT'
  refine (formula_l η _ _ _ _ _ _ _ _).trans
    (Iff.trans ?_ (PowerlessFormulaConstructor.constructor_formula_l η _ _ _ _ _ _ _).symm)
  simp only [Term.eval, hωEq, heEq]
  exact constructor_iff_l K hS'' hT''

#print axioms delta_l
#print axioms constructor_iff_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaConstructorBounded
