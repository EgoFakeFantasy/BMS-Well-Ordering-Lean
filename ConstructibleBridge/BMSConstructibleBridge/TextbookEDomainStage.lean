import BMSConstructibleBridge.TextbookNaturalArithmeticStage
import BMSConstructibleBridge.TextbookEStageBounds

/-!
# textbook E 递归定义域在局部可构造层中的绝对性

本模块把上游仅对完整 `L` 或传递 ZF 模型给出的定义域语义，降到任意严格
越过 `omega` 的后继极限层。这里只使用标准 `omega` 的局部唯一性、层的
传递性以及 `Delta0` 绝对性，不调用 Replacement。
-/

open Set

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open Constructible.FiniteSequenceZF

noncomputable section

/-- 参数无关的定义域公式在局部层中精确识别 `omega × omega`。 -/
theorem satisfiesIn_textbookEDomainFormula_stage_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {key : ZFSet.{u}}
    (hkey : key ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookEFormula.domainFormula ![key] ↔
      key ∈ Constructible.TextbookEDomain := by
  simp only [Constructible.TextbookEFormula.domainFormula,
    Constructible.Model.SatisfiesIn]
  constructor
  · rintro ⟨omega, homegaStage, homegaFormula, hproductFormula⟩
    have homega : omega = Ordinal.omega0.toZFSet :=
      (satisfiesIn_standardOmegaAt_stage_iff_l hθ hω (Fin.last 1)
        ![key, omega] (by
          intro position
          fin_cases position
          · exact hkey
          · exact homegaStage)).mp homegaFormula
    have hAssignment : ∀ position : Fin 2,
        ![key, omega] position ∈ LStageZF θ := by
      intro position
      fin_cases position <;> assumption
    have hdelta :=
      (Constructible.Model.satisfiesIn_delta0_iff
        (LStageZF_isTransitive θ)
        (Constructible.TextbookDefFormula.productMemberDeltaAt
          (0 : Fin 2) (Fin.last 1) (Fin.last 1))
        ![key, omega] hAssignment).mp hproductFormula
    rw [Delta0Formula.satisfies_toFO,
      Constructible.TextbookDefFormula.satisfies_productMemberDeltaAt]
      at hdelta
    change key ∈ ZFSet.prod omega omega at hdelta
    change key ∈ Constructible.textbookEDomainZF
    simpa only [Constructible.textbookEDomainZF,
      Constructible.textbookEOmegaZF, homega] using hdelta
  · intro hdomain
    let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
    have homegaStage : omega ∈ LStageZF θ :=
      omega_toZFSet_mem_stage_l hω
    refine ⟨omega, homegaStage, ?_, ?_⟩
    · exact (satisfiesIn_standardOmegaAt_stage_iff_l hθ hω
        (Fin.last 1) ![key, omega] (by
          intro position
          fin_cases position
          · exact hkey
          · exact homegaStage)).mpr rfl
    · have hAssignment : ∀ position : Fin 2,
          ![key, omega] position ∈ LStageZF θ := by
        intro position
        fin_cases position
        · exact hkey
        · exact homegaStage
      apply (Constructible.Model.satisfiesIn_delta0_iff
        (LStageZF_isTransitive θ)
        (Constructible.TextbookDefFormula.productMemberDeltaAt
          (0 : Fin 2) (Fin.last 1) (Fin.last 1))
        ![key, omega] hAssignment).mpr
      rw [Delta0Formula.satisfies_toFO,
        Constructible.TextbookDefFormula.satisfies_productMemberDeltaAt]
      change key ∈ ZFSet.prod omega omega
      change key ∈ Constructible.textbookEDomainZF at hdomain
      simpa only [Constructible.textbookEDomainZF,
        Constructible.textbookEOmegaZF, omega] using hdomain

/-- 参数无关的递归关系公式在局部层中精确识别 textbook E 的先行关系。 -/
theorem satisfiesIn_textbookERelationFormula_stage_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {left right : ZFSet.{u}}
    (hleft : left ∈ LStageZF θ) (hright : right ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookEFormula.relationFormula ![left, right] ↔
      Constructible.ClassRel Constructible.TextbookERelation left right := by
  simp only [Constructible.TextbookEFormula.relationFormula,
    Constructible.Model.SatisfiesIn]
  constructor
  · rintro ⟨omega, homegaStage, homegaFormula, hrelationFormula⟩
    have homega : omega = Ordinal.omega0.toZFSet :=
      (satisfiesIn_standardOmegaAt_stage_iff_l hθ hω (Fin.last 2)
        ![left, right, omega] (by
          intro position
          fin_cases position
          · exact hleft
          · exact hright
          · exact homegaStage)).mp homegaFormula
    have hAssignment : ∀ position : Fin 3,
        ![left, right, omega] position ∈ LStageZF θ := by
      intro position
      fin_cases position <;> assumption
    have hdelta :=
      (Constructible.Model.satisfiesIn_delta0_iff
        (LStageZF_isTransitive θ)
        (Constructible.TextbookEFormula.relationDeltaAt
          (0 : Fin 3) (1 : Fin 3) (Fin.last 2))
        ![left, right, omega] hAssignment).mp hrelationFormula
    rw [Delta0Formula.satisfies_toFO,
      Constructible.TextbookEFormula.satisfies_relationDeltaAt] at hdelta
    change ∃ i, i ∈ omega ∧ ∃ k, k ∈ omega ∧
      ∃ m, m ∈ omega ∧ ∃ n, n ∈ omega ∧
        left = ZFSet.pair i k ∧ right = ZFSet.pair m n ∧ i ∈ m at hdelta
    rcases hdelta with
      ⟨i, hi, k, hk, m, hm, n, hn, hleftPair, hrightPair, him⟩
    rw [Constructible.classRel_textbookERelation_iff]
    exact ⟨i, k, m, n,
      by simpa only [Constructible.textbookEOmegaZF, homega] using hi,
      by simpa only [Constructible.textbookEOmegaZF, homega] using hk,
      by simpa only [Constructible.textbookEOmegaZF, homega] using hm,
      by simpa only [Constructible.textbookEOmegaZF, homega] using hn,
      hleftPair, hrightPair, him⟩
  · intro hrelation
    let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
    have homegaStage : omega ∈ LStageZF θ :=
      omega_toZFSet_mem_stage_l hω
    refine ⟨omega, homegaStage, ?_, ?_⟩
    · exact (satisfiesIn_standardOmegaAt_stage_iff_l hθ hω
        (Fin.last 2) ![left, right, omega] (by
          intro position
          fin_cases position
          · exact hleft
          · exact hright
          · exact homegaStage)).mpr rfl
    · have hAssignment : ∀ position : Fin 3,
          ![left, right, omega] position ∈ LStageZF θ := by
        intro position
        fin_cases position
        · exact hleft
        · exact hright
        · exact homegaStage
      apply (Constructible.Model.satisfiesIn_delta0_iff
        (LStageZF_isTransitive θ)
        (Constructible.TextbookEFormula.relationDeltaAt
          (0 : Fin 3) (1 : Fin 3) (Fin.last 2))
        ![left, right, omega] hAssignment).mpr
      rw [Delta0Formula.satisfies_toFO,
        Constructible.TextbookEFormula.satisfies_relationDeltaAt]
      change ∃ i, i ∈ omega ∧ ∃ k, k ∈ omega ∧
        ∃ m, m ∈ omega ∧ ∃ n, n ∈ omega ∧
          left = ZFSet.pair i k ∧ right = ZFSet.pair m n ∧ i ∈ m
      rw [Constructible.classRel_textbookERelation_iff] at hrelation
      rcases hrelation with
        ⟨i, k, m, n, hi, hk, hm, hn, hleftPair, hrightPair, him⟩
      exact ⟨i, by simpa only [Constructible.textbookEOmegaZF, omega] using hi,
        k, by simpa only [Constructible.textbookEOmegaZF, omega] using hk,
        m, by simpa only [Constructible.textbookEOmegaZF, omega] using hm,
        n, by simpa only [Constructible.textbookEOmegaZF, omega] using hn,
        hleftPair, hrightPair, him⟩

/-- 带哑参数的定义域公式继承相同的局部语义。 -/
theorem satisfiesIn_textbookEDomainWithParamFormula_stage_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {a key : ZFSet.{u}}
    (_ha : a ∈ LStageZF θ) (hkey : key ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookEFormula.textbookEDomainWithParamFormula
        ![a, key] ↔ key ∈ Constructible.TextbookEDomain := by
  rw [Constructible.Model.satisfiesIn_textbookEDomainWithParamFormula_rename]
  exact satisfiesIn_textbookEDomainFormula_stage_iff_l hθ hω hkey

/-- 带哑参数的递归关系公式继承相同的局部语义。 -/
theorem satisfiesIn_textbookERelationWithParamFormula_stage_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {a left right : ZFSet.{u}}
    (_ha : a ∈ LStageZF θ) (hleft : left ∈ LStageZF θ)
    (hright : right ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookEFormula.textbookERelationWithParamFormula
        ![a, left, right] ↔
      Constructible.ClassRel Constructible.TextbookERelation left right := by
  rw [Constructible.Model.satisfiesIn_textbookERelationWithParamFormula_rename]
  exact satisfiesIn_textbookERelationFormula_stage_iff_l
    hθ hω hleft hright

end

end YesMetaZFC.BMS.ConstructibleBridge
