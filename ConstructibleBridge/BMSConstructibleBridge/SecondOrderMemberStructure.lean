import BMSConstructibleBridge.SecondOrderMemberRelations
import BMSConstructibleBridge.SecondOrderDefinableCoverage

/-!
# 非空集合的内部数域结构呈现

实际载体是原图商中该集合的成员。正规化使全部模型数都有成员代表，内部
相等图与成员图均在全数域正确；量词域可取整个内部数域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberStructure

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def type_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ) :=
  {x : SecondOrderQuotient.type_l hℳ // SecondOrderQuotient.mem_l hℳ x (SecondOrderQuotient.mk_l hℳ A)}

def structure_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) : FirstOrder.Structure.{0, 0, 0, u} ℒ where
  Carrier _ := type_l hℳ A
  nonempty _ := ⟨⟨SecondOrderQuotient.mk_l hℳ (SecondOrderGraph.child_l hℳ A a ha),
    SecondOrderGraph.child_mem_l hℳ A a ha⟩⟩
  funcInterp f := nomatch f
  relInterp
    | .membership, .cons x (.cons y .nil) => SecondOrderQuotient.mem_l hℳ x.val y.val

noncomputable def value_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) (n : num_l ℳ) : (structure_l hℳ A a ha).Carrier .set :=
  ⟨SecondOrderQuotient.mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A a ha n),
    SecondOrderMemberNormalizer.code_mem_l hℳ A a ha n⟩

theorem surjective_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) : Function.Surjective (value_l hℳ A a ha) := by
  rintro ⟨b, hb⟩
  obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ b
  obtain ⟨n, hn, h⟩ := hb
  refine ⟨n, ?_⟩
  apply Subtype.ext
  change SecondOrderQuotient.mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A a ha n) = SecondOrderQuotient.mk_l hℳ B
  rw [SecondOrderMemberNormalizer.code_fixed_l hℳ A a ha n hn, SecondOrderQuotient.eq_iff_l]
  exact SecondOrderBisimulation.symm_l hℳ B.real A.real B.root n h

theorem graphs_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) : ∃ D Q R : set_l ℳ, (∀ n, mem_l n D) ∧
      (∀ n m, relation_l Q n m ↔ value_l hℳ A a ha n = value_l hℳ A a ha m) ∧
      ∀ n m, relation_l R n m ↔ SecondOrderSourceSatisfaction.member_l (structure_l hℳ A a ha)
        (value_l hℳ A a ha n) (value_l hℳ A a ha m) := by
  obtain ⟨Q, R, hQ, hR⟩ := SecondOrderMemberRelations.graphs_l hℳ A a ha
  obtain ⟨D, hD⟩ := comprehension_l hℳ (Formula.truth : Formula signature_m [] [.num]) rfl Env.empty
  refine ⟨D, Q, R, fun n => (hD n).mpr trivial, ?_, hR⟩
  intro n m
  refine (hQ n m).trans ?_
  constructor
  · intro h
    exact Subtype.ext ((SecondOrderQuotient.eq_iff_l hℳ _ _).mpr h)
  · intro h
    exact (SecondOrderQuotient.eq_iff_l hℳ _ _).mp (congrArg (fun b : type_l hℳ A => b.val) h)

theorem coverage_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) : ∃ F : set_l ℳ,
      ∀ (Γ Δ : SortContext ℒ) (η : Env (structure_l hℳ A a ha) Γ Δ) (φ : Formula ℒ (.set :: Γ) Δ),
        ∃ i, ∀ n, relation_l F i n ↔ Formula.satisfies (η.pushBound (value_l hℳ A a ha n)) φ := by
  obtain ⟨D, Q, R, hD, hQ, hR⟩ := graphs_l hℳ A a ha
  obtain ⟨E, T, F, _, _, _, h⟩ := SecondOrderDefinableCoverage.exists_l hℳ D Q R (value_l hℳ A a ha)
    (fun y => by obtain ⟨n, hn⟩ := surjective_l hℳ A a ha y; exact ⟨n, hD n, hn⟩)
    (fun n m _ _ => hQ n m) (fun n m _ _ => hR n m)
  refine ⟨F, ?_⟩
  intro Γ Δ η φ
  obtain ⟨l, c, _, _, h⟩ := h Γ Δ η
  exact ⟨SecondOrderDefinableFamily.index_l (SecondOrderFormulaCompilation.formula_l ℳ φ) l c,
    fun n => (h φ n).trans (and_iff_right (hD n))⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberStructure
