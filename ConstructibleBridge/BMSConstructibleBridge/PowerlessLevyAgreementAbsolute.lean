import BMSConstructibleBridge.PowerlessLevyCertificateAbsolute
import BMSConstructibleBridge.PowerlessEvaluationAgreementAbsolute
import BMSConstructibleBridge.PowerlessLevyAgreement

/-!
# 原分层查询一致关系的绝对性

分类证书与全部有限赋值均双向对应，故能比较原全称蕴含而非仅保持
正向查询。内部层号 n 保持对象参数，不换成外部标准自然数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyAgreementAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B} (hBT : PowerlessNaturalOrder.transitive_l B)
  {ω e T A : type_l B} (hω : omega_l ω.val) (he : PowerlessNatural.zero_l e.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hI : ∀ x, member_l ℳ x ω.val → ∀ F,
    PowerlessAddition.iteration_l ω.val e.val x F → member_l ℳ F B)
  (hD : ∀ n, member_l ℳ n ω.val → ∀ D, subset_l D n → member_l ℳ D B)
  (hG : ∀ m, member_l ℳ m ω.val → ∀ f, map_l f m A.val → member_l ℳ f B)

include hℳ hBT hω he hT hI hD hG

theorem agreement_l {t₁ t₂ t₃ F G n : type_l B} :
    PowerlessLevyAgreement.agreement_l (ℳ := structure_l B hB) ω e T t₁ t₂ t₃ A F G n ↔
      PowerlessLevyAgreement.agreement_l ω.val e.val T.val t₁.val t₂.val t₃.val A.val F.val G.val n.val := by
  constructor
  · intro h c p hc
    obtain ⟨hcω, _, hpω, _⟩ := PowerlessLevyCertificate.natural_l hc
    have h₀ := h ⟨c, hBT ω.val c ω.property hcω⟩ ⟨p, hBT ω.val p ω.property hpω⟩
      ((PowerlessLevyCertificateAbsolute.class_l hℳ hBT hω he hT hI hD).mpr hc)
    exact (PowerlessEvaluationAgreementAbsolute.point_l hBT hG).mp h₀
  · intro h c p hc
    exact (PowerlessEvaluationAgreementAbsolute.point_l hBT hG).mpr
      (h c.val p.val ((PowerlessLevyCertificateAbsolute.class_l hℳ hBT hω he hT hI hD).mp hc))

theorem lower_l {t₁ t₂ t₃ F G n : type_l B} :
    PowerlessLevyAgreement.lower_l (ℳ := structure_l B hB) ω e T t₁ t₂ t₃ A F G n ↔
      PowerlessLevyAgreement.lower_l ω.val e.val T.val t₁.val t₂.val t₃.val A.val F.val G.val n.val := by
  constructor
  · intro h m hm
    exact (agreement_l hℳ hBT hω he hT hI hD hG).mp (h ⟨m, hBT n.val m n.property hm⟩ hm)
  · intro h m hm
    exact (agreement_l hℳ hBT hω he hT hI hD hG).mpr (h m.val hm)

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB) Γ Δ)
    (w z U t₁ t₂ t₃ D F G n : Term ℒ Γ Δ .set)
    (hw : w.eval η = ω) (hz : z.eval η = e) (hU : U.eval η = T) (hA : D.eval η = A) :
    Formula.satisfies η (PowerlessLevyAgreement.agreement_m w z U t₁ t₂ t₃ D F G n) ↔
      PowerlessLevyAgreement.agreement_l ω.val e.val T.val
        (t₁.eval η).val (t₂.eval η).val (t₃.eval η).val A.val (F.eval η).val (G.eval η).val (n.eval η).val := by
  rw [PowerlessLevyAgreement.agreement_formula_l, hw, hz, hU, hA]
  exact agreement_l hℳ hBT hω he hT hI hD hG

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyAgreementAbsolute
