import BMSConstructibleBridge.SecondOrderGraphFormulaGuard
import BMSConstructibleBridge.SecondOrderMixedImage
import BMSConstructibleBridge.SecondOrderObjectSyntax

/-!
# 两个给定集合之间的可定义关系本身是集合

实际图根关系通过原二阶理解得到，再用混合有序对像构造对象。源关系公式
的首自由槽为左输入、次槽为右输入。没有以幂集或 Collection 构造笛卡尔积。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableRelationImage

open Logic FirstOrder

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [] (.set :: .set :: .set :: .set :: Δ)
  | _, .here => .fvar .here
  | _, .there .here => .fvar (.there .here)
  | _, .there (.there v) => .fvar (.there (.there (.there (.there v))))

private def bounded_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: .set :: Δ) :=
  .conj (SecondOrderObjectSyntax.member_m (.fvar .here) (.fvar (.there (.there .here))))
    (.conj (SecondOrderObjectSyntax.member_m (.fvar (.there .here)) (.fvar (.there (.there (.there .here)))))
      (φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ) []
        (.set :: .set :: .set :: .set :: Δ) from .map (fun v => nomatch v) insert_m)))

private theorem bounded_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ)
    (a b x y : 𝒩.Carrier .set) :
    (bounded_m φ).satisfies ((((η.pushFree b).pushFree a).pushFree y).pushFree x) ↔
      𝒩.relInterp .membership (.cons x (.cons a .nil)) ∧
      𝒩.relInterp .membership (.cons y (.cons b .nil)) ∧
      φ.satisfies ((η.pushFree y).pushFree x) := by
  simp only [bounded_m, Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  refine (Formula.satisfies_substitute _ _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

private abbrev quotient_l := SecondOrderQuotient.structure_l hℳ

theorem exists_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) (a b : SecondOrderQuotient.type_l hℳ) :
    ∃ f, ∀ p, SecondOrderQuotient.mem_l hℳ p f ↔ ∃ x y,
      SecondOrderQuotient.mem_l hℳ x a ∧ SecondOrderQuotient.mem_l hℳ y b ∧
      φ.satisfies ((η.pushFree y).pushFree x) ∧ SecondOrderPairObjects.ordered_l hℳ x y p := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ b
  obtain ⟨F, hF⟩ := SecondOrderGraphFormulaGuard.exists_l hℳ (bounded_m φ)
    ((η.pushFree (SecondOrderQuotient.mk_l hℳ B)).pushFree (SecondOrderQuotient.mk_l hℳ A)) A.real B.real
  have hRead n m : SecondOrderPairing.relation_l F n m ↔
      ∃ (hn : SecondOrderDomain.wf_l A.real n) (hm : SecondOrderDomain.wf_l B.real m),
        SecondOrderQuotient.mem_l hℳ (SecondOrderQuotient.mk_l hℳ ⟨A.real, n, hn⟩)
          (SecondOrderQuotient.mk_l hℳ A) ∧
        SecondOrderQuotient.mem_l hℳ (SecondOrderQuotient.mk_l hℳ ⟨B.real, m, hm⟩)
          (SecondOrderQuotient.mk_l hℳ B) ∧
        φ.satisfies ((η.pushFree (SecondOrderQuotient.mk_l hℳ ⟨B.real, m, hm⟩)).pushFree
          (SecondOrderQuotient.mk_l hℳ ⟨A.real, n, hn⟩)) := by
    rw [hF]
    exact exists_congr (fun hn => exists_congr (fun hm => bounded_formula_l φ η _ _ _ _))
  have hRoots n m (h : SecondOrderPairing.relation_l F n m) :
      SecondOrderDomain.wf_l A.real n ∧ SecondOrderDomain.wf_l B.real m := by
    obtain ⟨hn, hm, _⟩ := (hRead n m).mp h
    exact ⟨hn, hm⟩
  obtain ⟨f, hf⟩ := SecondOrderMixedImage.exists_l hℳ A.real B.real F hRoots
  refine ⟨f, fun p => (hf p).trans ?_⟩
  constructor
  · rintro ⟨n, m, h, hp⟩
    obtain ⟨hn, hm, hA, hB, hφ⟩ := (hRead n m).mp h
    exact ⟨SecondOrderQuotient.mk_l hℳ ⟨A.real, n, hn⟩,
      SecondOrderQuotient.mk_l hℳ ⟨B.real, m, hm⟩, hA, hB, hφ, hp⟩
  · rintro ⟨x, y, hx, hy, hφ, hp⟩
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    obtain ⟨Y, rfl⟩ := SecondOrderQuotient.surj_l hℳ y
    obtain ⟨n, hn, hXn⟩ := hx
    obtain ⟨m, hm, hYm⟩ := hy
    let N := SecondOrderGraph.child_l hℳ A n hn
    let M := SecondOrderGraph.child_l hℳ B m hm
    have hXN : SecondOrderQuotient.mk_l hℳ X = SecondOrderQuotient.mk_l hℳ N :=
      (SecondOrderQuotient.eq_iff_l hℳ X N).mpr hXn
    have hYM : SecondOrderQuotient.mk_l hℳ Y = SecondOrderQuotient.mk_l hℳ M :=
      (SecondOrderQuotient.eq_iff_l hℳ Y M).mpr hYm
    rw [hXN, hYM] at hφ hp
    have h := (hRead n m).mpr ⟨N.wf, M.wf,
      SecondOrderGraph.child_mem_l hℳ A n hn, SecondOrderGraph.child_mem_l hℳ B m hm, hφ⟩
    exact ⟨n, m, h, hp⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableRelationImage
