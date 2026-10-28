import BMSConstructibleBridge.SecondOrderComparisonReal
import BMSConstructibleBridge.SecondOrderGraphFormulaGuard
import BMSConstructibleBridge.SecondOrderRelationImage

/-! # 比较实数的无选择解码

固定载体和实际枚举后，每张关系实数都给出唯一的完整有序对集合图。
无效图根由理解公式排除；不要求枚举单射，也不抽取图呈现的选择函数。
任意实数均可解码，但重新编码等于输入还须检查重复枚举坐标的相容性。
本模块是原 Z₂ 任意模型中的中间结果，不是最终 BMS 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonDecode

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def read_l (K : source_coding_l hℳ) (C f : type_l hℳ)
    (R : SecondOrderModel.set_l ℳ) (x y : type_l hℳ) : Prop :=
  mem_l hℳ x C ∧ mem_l hℳ y C ∧ ∃ i j,
    SecondOrderPairing.relation_l R i j ∧
    value_l (ℳ := 𝒱) f (numberCode_l K i).val x ∧
    value_l (ℳ := 𝒱) f (numberCode_l K j).val y

/-- 完整成员规格排除不能由比较位产生的额外元素。 -/
def graph_l (K : source_coding_l hℳ) (C f : type_l hℳ)
    (R : SecondOrderModel.set_l ℳ) (P : type_l hℳ) : Prop :=
  ∀ p, mem_l hℳ p P ↔ ∃ x y, read_l K C f R x y ∧
    SecondOrderPairObjects.ordered_l hℳ x y p

private theorem composition_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (L R : SecondOrderModel.set_l ℳ) :
    ∃ T : SecondOrderModel.set_l ℳ, ∀ a b,
      SecondOrderPairing.relation_l T a b ↔ ∃ i j,
        SecondOrderPairing.relation_l L i a ∧
        SecondOrderPairing.relation_l L j b ∧ SecondOrderPairing.relation_l R i j := by
  let φ : Formula SecondOrderSyntax.signature_m [] [.num, .num, .set, .set] :=
    .existsE .num <| .existsE .num <| .conj
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar (.there .here)) (.fvar .here))
      (.conj (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar .here) (.fvar (.there .here)))
        (GraphSyntax.edge_m (.fvar (.there (.there (.there .here))))
          (.bvar (.there .here)) (.bvar .here)))
  obtain ⟨T, hT⟩ := SecondOrderRelations.comprehension_l hℳ φ
    (SecondOrderArithmetic.pure_language_m _ rfl) ((Env.empty.pushFree R).pushFree L)
  refine ⟨T, fun a b => (hT a b).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l]
  rfl

theorem exists_l (K : source_coding_l hℳ) (C f : type_l hℳ)
    (R : SecondOrderModel.set_l ℳ) : ∃ P, graph_l K C f R P := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ C
  let φ : Formula ℒ [] [.set, .set, .set, .set] :=
    .conj (SecondOrderObjectSyntax.member_m (.fvar (.there .here))
      (.fvar (.there (.there (.there .here)))))
      (SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here)))
        (.fvar .here) (.fvar (.there .here)))
  let η : Env 𝒱 [] [.set, .set] :=
    (Env.empty.pushFree (SecondOrderQuotient.mk_l hℳ A)).pushFree f
  obtain ⟨L, hL⟩ := SecondOrderGraphFormulaGuard.exists_l hℳ φ η K.less A.real
  have hRead i a : SecondOrderPairing.relation_l L i a ↔
      ∃ ha : SecondOrderDomain.wf_l A.real a,
        mem_l hℳ (SecondOrderQuotient.mk_l hℳ ⟨A.real, a, ha⟩)
          (SecondOrderQuotient.mk_l hℳ A) ∧
        value_l (ℳ := 𝒱) f (numberCode_l K i).val
          (SecondOrderQuotient.mk_l hℳ ⟨A.real, a, ha⟩) := by
    rw [hL]
    simp only [φ, Formula.satisfies, SecondOrderObjectSyntax.member_m,
      SecondOrderObjectSyntax.value_l, Term.eval, Arguments.eval]
    constructor
    · rintro ⟨_, ha, h⟩
      exact ⟨ha, h⟩
    · rintro ⟨ha, h⟩
      exact ⟨SecondOrderNaturalGraph.wf_l hℳ K.less K.less_spec i, ha, h⟩
  obtain ⟨T, hT⟩ := composition_l hℳ L R
  have hRoots a b (h : SecondOrderPairing.relation_l T a b) :
      SecondOrderDomain.wf_l A.real a ∧ SecondOrderDomain.wf_l A.real b := by
    obtain ⟨i, j, hi, hj, _⟩ := (hT a b).mp h
    obtain ⟨ha, _⟩ := (hRead i a).mp hi
    obtain ⟨hb, _⟩ := (hRead j b).mp hj
    exact ⟨ha, hb⟩
  obtain ⟨P, hP⟩ := SecondOrderRelationImage.quotient_l hℳ A.real T hRoots
  refine ⟨P, fun p => (hP p).trans ?_⟩
  constructor
  · rintro ⟨a, b, h, hp⟩
    obtain ⟨i, j, hi, hj, hij⟩ := (hT a b).mp h
    obtain ⟨ha, hx, hix⟩ := (hRead i a).mp hi
    obtain ⟨hb, hy, hjy⟩ := (hRead j b).mp hj
    exact ⟨_, _, ⟨hx, hy, i, j, hij, hix, hjy⟩, hp⟩
  · rintro ⟨x, y, ⟨hx, hy, i, j, hij, hix, hjy⟩, hp⟩
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    obtain ⟨Y, rfl⟩ := SecondOrderQuotient.surj_l hℳ y
    obtain ⟨a, ha, hXa⟩ := hx
    obtain ⟨b, hb, hYb⟩ := hy
    let U := SecondOrderGraph.child_l hℳ A a ha
    let V := SecondOrderGraph.child_l hℳ A b hb
    have hXU : SecondOrderQuotient.mk_l hℳ X = SecondOrderQuotient.mk_l hℳ U :=
      (SecondOrderQuotient.eq_iff_l hℳ X U).mpr hXa
    have hYV : SecondOrderQuotient.mk_l hℳ Y = SecondOrderQuotient.mk_l hℳ V :=
      (SecondOrderQuotient.eq_iff_l hℳ Y V).mpr hYb
    rw [hXU] at hix
    rw [hYV] at hjy
    rw [hXU, hYV] at hp
    have hi := (hRead i a).mpr ⟨U.wf, SecondOrderGraph.child_mem_l hℳ A a ha, hix⟩
    have hj := (hRead j b).mpr ⟨V.wf, SecondOrderGraph.child_mem_l hℳ A b hb, hjy⟩
    exact ⟨a, b, (hT a b).mpr ⟨i, j, hi, hj, hij⟩, hp⟩

theorem unique_l (K : source_coding_l hℳ) {C f P Q : type_l hℳ}
    {R : SecondOrderModel.set_l ℳ} (hP : graph_l K C f R P) (hQ : graph_l K C f R Q) :
    P = Q := SecondOrderQuotient.ext_l hℳ P Q (fun p => (hP p).trans (hQ p).symm)

theorem exists_unique_l (K : source_coding_l hℳ) (C f : type_l hℳ)
    (R : SecondOrderModel.set_l ℳ) : ∃! P, graph_l K C f R P := by
  obtain ⟨P, hP⟩ := exists_l K C f R
  exact ⟨P, hP, fun Q hQ => unique_l K hQ hP⟩

theorem values_l (K : source_coding_l hℳ) {C f P : type_l hℳ}
    {R : SecondOrderModel.set_l ℳ} (hP : graph_l K C f R P) (x y : type_l hℳ) :
    value_l (ℳ := 𝒱) P x y ↔ read_l K C f R x y := by
  constructor
  · rintro ⟨p, hp, hxy⟩
    obtain ⟨a, b, hab, hp'⟩ := (hP p).mp hp
    obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxy hp').mp rfl
    exact hab
  · intro h
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
    exact ⟨p, (hP p).mpr ⟨x, y, h, hp⟩, hp⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonDecode
