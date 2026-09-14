import BMSConstructibleBridge.SecondOrderCollapseFunction

/-!
# 任意模型中的完整内部 Mostowski 坍缩构造

先把 ω 上关系的实际有序对成员公式解码为内部数图，再从正则性证明每个根
属于内部域。原域域、传递值域与满射坍缩函数均是商内集合，不假设关系外延。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMostowski

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A o : SecondOrderQuotient.type_l hℳ)
    (ho : SecondOrderOmega.omega_l hℳ o) (hA : SecondOrderRegularRelation.regular_l hℳ A o) :
    ∃ d u f, (∀ x, SecondOrderQuotient.mem_l hℳ x d ↔ SecondOrderRegularRelation.field_l hℳ A o x) ∧
      SecondOrderCollapseFunction.spec_l hℳ A d u f := by
  obtain ⟨R, hR⟩ := SecondOrderNaturalGraph.relation_exists_l hℳ
  obtain ⟨Ω, hΩ⟩ := SecondOrderNaturalNumbers.range_l hℳ R hR
  have h := SecondOrderOmega.unique_l hℳ ho (SecondOrderOmega.range_l hℳ R hR Ω hΩ)
  subst o
  let N (n : num_l ℳ) := SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR n)
  have h₀ : ∀ x, SecondOrderQuotient.mem_l hℳ x (SecondOrderQuotient.mk_l hℳ Ω) ↔ ∃ n, x = N n := by
    intro x
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact (hΩ X).trans (exists_congr (fun n =>
      (SecondOrderQuotient.eq_iff_l hℳ X (SecondOrderNaturalGraph.code_l hℳ R hR n)).symm))
  obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ A
  obtain ⟨S, hS⟩ := SecondOrderRelationDecode.exists_l hℳ R hR B
  have h₁ := SecondOrderRegularRelation.wf_l hℳ R S hR
    (SecondOrderQuotient.mk_l hℳ B) (SecondOrderQuotient.mk_l hℳ Ω)
    (fun n => (h₀ (N n)).mpr ⟨n, rfl⟩) hS hA
  have h₂ : ∀ x, SecondOrderRegularRelation.field_l hℳ (SecondOrderQuotient.mk_l hℳ B)
      (SecondOrderQuotient.mk_l hℳ Ω) x ↔ ∃ n, SecondOrderCollapseGraph.field_l S n ∧ x = N n := by
    intro x
    constructor
    · rintro ⟨hx, y, hy, h⟩
      obtain ⟨n, rfl⟩ := (h₀ x).mp hx
      obtain ⟨m, rfl⟩ := (h₀ y).mp hy
      exact ⟨n, ⟨m, h.imp ((hS n m).mpr) ((hS m n).mpr)⟩, rfl⟩
    · rintro ⟨n, ⟨m, h⟩, rfl⟩
      exact ⟨(h₀ _).mpr ⟨n, rfl⟩, N m, (h₀ _).mpr ⟨m, rfl⟩,
        h.imp ((hS n m).mp) ((hS m n).mp)⟩
  obtain ⟨P, hP⟩ := SecondOrderCollapseGraph.field_exists_l hℳ S
  obtain ⟨d, hd⟩ := SecondOrderNaturalSubsets.exists_l hℳ R hR P
  have h₃ : ∀ x, SecondOrderQuotient.mem_l hℳ x d ↔
      ∃ n, SecondOrderCollapseGraph.field_l S n ∧ x = N n :=
    fun x => (hd x).trans (exists_congr (fun n => and_congr (hP n) Iff.rfl))
  obtain ⟨u, f, h₄⟩ := SecondOrderCollapseFunction.exists_l hℳ R S hR h₁
    (SecondOrderQuotient.mk_l hℳ B) d hS h₃
  exact ⟨d, u, f, fun x => (h₃ x).trans (h₂ x).symm, h₄⟩

/-- 文献 MostColl 的原域域口径，所有限制来自显式“ω 上关系”前提。 -/
theorem collapse_l (hℳ : Theory.Models ℳ theory_m) (A o : SecondOrderQuotient.type_l hℳ)
    (ho : SecondOrderOmega.omega_l hℳ o) (hR : SecondOrderRegularRelation.relation_l hℳ A o)
    (hA : SecondOrderRegularRelation.wellFounded_l hℳ A) :
    ∃ d u f, (∀ x, SecondOrderQuotient.mem_l hℳ x d ↔ SecondOrderRegularRelation.domain_l hℳ A x) ∧
      SecondOrderCollapseFunction.spec_l hℳ A d u f := by
  obtain ⟨d, u, f, hd, h⟩ := exists_l hℳ A o ho ((SecondOrderRegularRelation.regular_iff_l hℳ A o hR).mpr hA)
  exact ⟨d, u, f, fun x => (hd x).trans (SecondOrderRegularRelation.field_iff_l hℳ A o hR x), h⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMostowski
