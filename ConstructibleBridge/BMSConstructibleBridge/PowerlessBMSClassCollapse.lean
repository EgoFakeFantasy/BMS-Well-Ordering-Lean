import BMSConstructibleBridge.PowerlessBMSClassRelation

/-!
# 传递类像与实际内部图坍缩的对应

输出类若对成员封闭，则类成员图的每个根恰代表其原输出。双模拟见证本身
由原模型理解构造，不用宿主外部递归或预先假定类值域是集合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSClassCollapse

open Logic FirstOrder PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private def swap_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [] (.set :: .set :: Δ)
  | _, .here => .fvar (.there .here)
  | _, .there .here => .fvar .here
  | _, .there (.there v) => .fvar (.there (.there v))

def converse_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ) [] (.set :: .set :: Δ) from
    .map (fun v => nomatch v) swap_m)

theorem converse_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (x y : 𝒩.Carrier .set) :
    (converse_m φ).satisfies ((η.pushFree y).pushFree x) ↔
      φ.satisfies ((η.pushFree x).pushFree y) := by
  refine (Formula.satisfies_substitute _ _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev quotient_l := SecondOrderQuotient.structure_l hℳ

theorem agrees_l (C : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env quotient_l [] Δ)
    (R : SecondOrderModel.set_l ℳ) (hWf : ∀ n, SecondOrderDomain.wf_l R n)
    (hUnique : ∀ n y z,
      φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) →
      φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree z) → y = z)
    (hEdge : ∀ n m, SecondOrderPairing.relation_l R n m ↔ ∃ y z,
      φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) ∧
      φ.satisfies ((η.pushFree (numberCode_l C m).val).pushFree z) ∧
      SecondOrderQuotient.mem_l hℳ y z)
    (hTrans : ∀ n y, φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) →
      ∀ z, SecondOrderQuotient.mem_l hℳ z y →
        ∃ m, φ.satisfies ((η.pushFree (numberCode_l C m).val).pushFree z))
    (n : SecondOrderModel.num_l ℳ) (y : SecondOrderQuotient.type_l hℳ)
    (hy : φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y)) :
    SecondOrderQuotient.mk_l hℳ ⟨R, n, hWf n⟩ = y := by
  obtain ⟨Y, rfl⟩ := SecondOrderQuotient.surj_l hℳ y
  obtain ⟨F, hF⟩ := SecondOrderGraphFormulaGuard.exists_l hℳ (converse_m φ) η C.less Y.real
  have hRead a b : SecondOrderPairing.relation_l F a b ↔
      ∃ hb : SecondOrderDomain.wf_l Y.real b,
        φ.satisfies ((η.pushFree (numberCode_l C a).val).pushFree
          (SecondOrderQuotient.mk_l hℳ ⟨Y.real, b, hb⟩)) := by
    rw [hF]
    constructor
    · rintro ⟨ha, hb, h⟩
      exact ⟨hb, (converse_formula_l φ η _ _).mp h⟩
    · rintro ⟨hb, h⟩
      exact ⟨SecondOrderNaturalGraph.wf_l hℳ C.less C.less_spec a, hb,
        (converse_formula_l φ η _ _).mpr h⟩
  apply (SecondOrderQuotient.eq_iff_l hℳ _ Y).mpr
  refine ⟨F, ?_, (hRead n Y.root).mpr ⟨Y.wf, hy⟩⟩
  intro a b hab
  obtain ⟨hb, hφ⟩ := (hRead a b).mp hab
  let B : SecondOrderGraph.code_l ℳ := ⟨Y.real, b, hb⟩
  constructor
  · intro c hca
    obtain ⟨z, w, hz, hw, hzw⟩ := (hEdge c a).mp hca
    have hwB := hUnique a w (SecondOrderQuotient.mk_l hℳ B) hw hφ
    rw [hwB] at hzw
    obtain ⟨Z, rfl⟩ := SecondOrderQuotient.surj_l hℳ z
    obtain ⟨d, hd, hZd⟩ := hzw
    let D := SecondOrderGraph.child_l hℳ B d hd
    have hZD : SecondOrderQuotient.mk_l hℳ Z = SecondOrderQuotient.mk_l hℳ D :=
      (SecondOrderQuotient.eq_iff_l hℳ Z D).mpr hZd
    refine ⟨d, hd, (hRead c d).mpr ⟨D.wf, ?_⟩⟩
    exact hZD ▸ hz
  · intro d hdb
    let D := SecondOrderGraph.child_l hℳ B d hdb
    have hDB : SecondOrderQuotient.mem_l hℳ (SecondOrderQuotient.mk_l hℳ D)
        (SecondOrderQuotient.mk_l hℳ B) := SecondOrderGraph.child_mem_l hℳ B d hdb
    obtain ⟨c, hc⟩ := hTrans a _ hφ _ hDB
    exact ⟨c, (hEdge c a).mpr ⟨_, _, hc, hφ, hDB⟩, (hRead c d).mpr ⟨D.wf, hc⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSClassCollapse
