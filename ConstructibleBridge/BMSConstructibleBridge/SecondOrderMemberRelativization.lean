import BMSConstructibleBridge.SecondOrderMemberBounded
import BMSConstructibleBridge.PowerlessRelativization

/-! # 原数域成员结构的任意公式相对化

原成员呈现与通用成员结构的空函数解释不必定义相等。本接口直接消费
原成员结构及原投影环境，对原公式作语法归纳，覆盖任意内部量词。
非空来自指定原根证书；没有 Type 函数选择、传递性或 Δ₀ 限制。
这是 Def 切片对象推导所需的语义桥，不单独声称对象分离模式完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberRelativization

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mk_l mem_l)
open SecondOrderMemberBounded (env_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SecondOrderMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {A : SecondOrderGraph.code_l ℳ}
  {a : SecondOrderModel.num_l ℳ} {ha : SecondOrderPairing.relation_l A.real a A.root}

theorem term_l {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) Γ Δ) (t : Term ℒ Γ Δ .set) :
    (t.weakenFree SetTheory.SetSort.set).eval ((env_l η).pushFree (mk_l hℳ A)) = (t.eval η).val := by
  rw [Term.eval_weakenFree, SecondOrderMemberBounded.term_l]

theorem push_l {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) Γ Δ)
    (x : SecondOrderMemberStructure.type_l hℳ A) :
    (env_l (η.pushBound (sort := SetTheory.SetSort.set) x)).pushFree
      (sort := SetTheory.SetSort.set) (mk_l hℳ A) =
        ((env_l η).pushFree (sort := SetTheory.SetSort.set) (mk_l hℳ A)).pushBound
          (sort := SetTheory.SetSort.set) x.val := by
  apply Env.ext
  · intro s v
    cases s
    cases v <;> rfl
  · intro s v
    cases s
    cases v <;> rfl

theorem formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ)
    (η : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) Γ Δ) :
    (PowerlessRelativization.formula_m φ).satisfies ((env_l η).pushFree (mk_l hℳ A)) ↔
      φ.satisfies η := by
  match φ with
  | .falsum => rfl
  | .truth => rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
      change mem_l hℳ ((s.weakenFree SetTheory.SetSort.set).eval ((env_l η).pushFree (mk_l hℳ A)))
        ((t.weakenFree SetTheory.SetSort.set).eval ((env_l η).pushFree (mk_l hℳ A))) ↔
          mem_l hℳ (s.eval η).val (t.eval η).val
      rw [term_l, term_l]
  | .equal (sort := SetTheory.SetSort.set) s t =>
      change (s.weakenFree SetTheory.SetSort.set).eval ((env_l η).pushFree (mk_l hℳ A)) =
        (t.weakenFree SetTheory.SetSort.set).eval ((env_l η).pushFree (mk_l hℳ A)) ↔ s.eval η = t.eval η
      rw [term_l, term_l]
      exact ⟨Subtype.ext, congrArg Subtype.val⟩
  | .neg φ => exact not_congr (formula_l φ η)
  | .conj φ ψ => exact and_congr (formula_l φ η) (formula_l ψ η)
  | .disj φ ψ => exact or_congr (formula_l φ η) (formula_l ψ η)
  | .imp φ ψ => exact imp_congr (formula_l φ η) (formula_l ψ η)
  | .iff φ ψ => exact iff_congr (formula_l φ η) (formula_l ψ η)
  | .forallE .set φ =>
      change (∀ x, mem_l hℳ x (mk_l hℳ A) →
        (PowerlessRelativization.formula_m φ).satisfies (((env_l η).pushFree (mk_l hℳ A)).pushBound x)) ↔
          ∀ x : SecondOrderMemberStructure.type_l hℳ A, φ.satisfies (η.pushBound x)
      have h (x : SecondOrderMemberStructure.type_l hℳ A) := formula_l φ (η.pushBound x)
      simp only [push_l] at h
      exact ⟨fun hφ x => (h x).mp (hφ x.val x.property),
        fun hφ x hx => (h ⟨x, hx⟩).mpr (hφ ⟨x, hx⟩)⟩
  | .existsE .set φ =>
      change (∃ x, mem_l hℳ x (mk_l hℳ A) ∧
        (PowerlessRelativization.formula_m φ).satisfies (((env_l η).pushFree (mk_l hℳ A)).pushBound x)) ↔
          ∃ x : SecondOrderMemberStructure.type_l hℳ A, φ.satisfies (η.pushBound x)
      have h (x : SecondOrderMemberStructure.type_l hℳ A) := formula_l φ (η.pushBound x)
      simp only [push_l] at h
      constructor
      · rintro ⟨x, hx, hφ⟩
        exact ⟨⟨x, hx⟩, (h ⟨x, hx⟩).mp hφ⟩
      · rintro ⟨x, hφ⟩
        exact ⟨x.val, x.property, (h x).mpr hφ⟩

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberRelativization
