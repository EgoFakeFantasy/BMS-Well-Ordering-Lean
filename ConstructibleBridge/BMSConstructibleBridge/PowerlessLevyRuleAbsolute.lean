import BMSConstructibleBridge.PowerlessLevyEntryAbsolute
import BMSConstructibleBridge.PowerlessBoundedCertificateAbsolute
import BMSConstructibleBridge.PowerlessLevyRule

/-!
# 原内部层级生成规则的绝对性

分别保持与非、有界存在、无界存在及升层规则。全部层号和极性见证
从原记录的自然数条件取回；有限子集闭包仅用于有界基础证书的存在量词。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyRuleAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B} (hBT : PowerlessNaturalOrder.transitive_l B)
  {ω e T : type_l B} (hω : omega_l ω.val) (he : PowerlessNatural.zero_l e.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hI : ∀ x, member_l ℳ x ω.val → ∀ F,
    PowerlessAddition.iteration_l ω.val e.val x F → member_l ℳ F B)

include hℳ hBT hω he hT hI

theorem boolean_l {t₁ t₂ D c n p : type_l B} :
    PowerlessLevyRule.boolean_l (ℳ := structure_l B hB) ω e T t₁ t₂ D c n p ↔
      PowerlessLevyRule.boolean_l ω.val e.val T.val t₁.val t₂.val D.val c.val n.val p.val := by
  constructor
  · rintro ⟨a, b, k, l, q, hq, hk, hl, ha, hb, hc⟩
    exact ⟨a.val, b.val, k.val, l.val, q.val, PowerlessLevyEntryAbsolute.opposite_l.mp hq,
      (PowerlessSourceNaturalAbsolute.subset_l hBT).mp hk,
      (PowerlessSourceNaturalAbsolute.subset_l hBT).mp hl,
      (PowerlessLevyEntryAbsolute.entry_l hℳ hBT hω he hT hI).mp ha,
      (PowerlessLevyEntryAbsolute.entry_l hℳ hBT hω he hT hI).mp hb,
      (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mp hc⟩
  · rintro ⟨a, b, k, l, q, hq, hk, hl, ha, hb, hc⟩
    obtain ⟨haω, hkω, hqω⟩ := PowerlessLevyEntry.natural_l ha
    obtain ⟨hbω, hlω, _⟩ := PowerlessLevyEntry.natural_l hb
    exact ⟨⟨a, hBT ω.val a ω.property haω⟩, ⟨b, hBT ω.val b ω.property hbω⟩,
      ⟨k, hBT ω.val k ω.property hkω⟩, ⟨l, hBT ω.val l ω.property hlω⟩,
      ⟨q, hBT ω.val q ω.property hqω⟩, PowerlessLevyEntryAbsolute.opposite_l.mpr hq,
      (PowerlessSourceNaturalAbsolute.subset_l hBT).mpr hk,
      (PowerlessSourceNaturalAbsolute.subset_l hBT).mpr hl,
      (PowerlessLevyEntryAbsolute.entry_l hℳ hBT hω he hT hI).mpr ha,
      (PowerlessLevyEntryAbsolute.entry_l hℳ hBT hω he hT hI).mpr hb,
      (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mpr hc⟩

theorem bounded_l {t₂ t₃ D c n p : type_l B} :
    PowerlessLevyRule.bounded_l (ℳ := structure_l B hB) ω e T t₂ t₃ D c n p ↔
      PowerlessLevyRule.bounded_l ω.val e.val T.val t₂.val t₃.val D.val c.val n.val p.val := by
  constructor
  · rintro ⟨i, j, b, m, hm, hb, hc⟩
    exact ⟨i.val, j.val, b.val, m.val, (PowerlessSourceNaturalAbsolute.subset_l hBT).mp hm,
      (PowerlessLevyEntryAbsolute.entry_l hℳ hBT hω he hT hI).mp hb,
      (PowerlessBoundedCodeAbsolute.code_l hℳ hBT hω he hT hI).mp hc⟩
  · rintro ⟨i, j, b, m, hm, hb, hc⟩
    obtain ⟨hbω, hmω, _⟩ := PowerlessLevyEntry.natural_l hb
    have hij : member_l ℳ i ω.val ∧ member_l ℳ j ω.val := by
      obtain ⟨_, d, p, q, hd, _, _, _⟩ := hc
      exact ⟨hd.1, hd.2.1⟩
    exact ⟨⟨i, hBT ω.val i ω.property hij.1⟩, ⟨j, hBT ω.val j ω.property hij.2⟩,
      ⟨b, hBT ω.val b ω.property hbω⟩, ⟨m, hBT ω.val m ω.property hmω⟩,
      (PowerlessSourceNaturalAbsolute.subset_l hBT).mpr hm,
      (PowerlessLevyEntryAbsolute.entry_l hℳ hBT hω he hT hI).mpr hb,
      (PowerlessBoundedCodeAbsolute.code_l hℳ hBT hω he hT hI).mpr hc⟩

theorem quantifier_l {t₁ t₃ D c n p : type_l B} :
    PowerlessLevyRule.quantifier_l (ℳ := structure_l B hB) ω e T t₁ t₃ D c n p ↔
      PowerlessLevyRule.quantifier_l ω.val e.val T.val t₁.val t₃.val D.val c.val n.val p.val := by
  have h₀ (m q : type_l B) :
      ((q = e ∧ subset_l (ℳ := structure_l B hB) m n) ∨ (q = t₁ ∧ member_l (structure_l B hB) m n)) ↔
        ((q.val = e.val ∧ subset_l m.val n.val) ∨ (q.val = t₁.val ∧ member_l ℳ m.val n.val)) :=
    or_congr (and_congr Subtype.ext_iff (PowerlessSourceNaturalAbsolute.subset_l hBT))
      (and_congr Subtype.ext_iff Iff.rfl)
  constructor
  · rintro ⟨hp, hn, i, b, m, q, hb, hm, hc⟩
    exact ⟨congrArg Subtype.val hp, hn, i.val, b.val, m.val, q.val,
      (PowerlessLevyEntryAbsolute.entry_l hℳ hBT hω he hT hI).mp hb, (h₀ m q).mp hm,
      (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mp hc⟩
  · rintro ⟨hp, hn, i, b, m, q, hb, hm, hc⟩
    obtain ⟨hbω, hmω, hqω⟩ := PowerlessLevyEntry.natural_l hb
    exact ⟨Subtype.ext hp, hn, ⟨i, hBT ω.val i ω.property hc.1⟩,
      ⟨b, hBT ω.val b ω.property hbω⟩, ⟨m, hBT ω.val m ω.property hmω⟩,
      ⟨q, hBT ω.val q ω.property hqω⟩,
      (PowerlessLevyEntryAbsolute.entry_l hℳ hBT hω he hT hI).mpr hb,
      (h₀ ⟨m, hBT ω.val m ω.property hmω⟩ ⟨q, hBT ω.val q ω.property hqω⟩).mpr hm,
      (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mpr hc⟩

theorem promotion_l {D c n : type_l B} :
    PowerlessLevyRule.promotion_l (ℳ := structure_l B hB) ω e T D c n ↔
      PowerlessLevyRule.promotion_l ω.val e.val T.val D.val c.val n.val := by
  constructor
  · rintro ⟨m, q, hm, hc⟩
    exact ⟨m.val, q.val, hm, (PowerlessLevyEntryAbsolute.entry_l hℳ hBT hω he hT hI).mp hc⟩
  · rintro ⟨m, q, hm, hc⟩
    obtain ⟨_, hmω, hqω⟩ := PowerlessLevyEntry.natural_l hc
    exact ⟨⟨m, hBT ω.val m ω.property hmω⟩, ⟨q, hBT ω.val q ω.property hqω⟩, hm,
      (PowerlessLevyEntryAbsolute.entry_l hℳ hBT hω he hT hI).mpr hc⟩

theorem step_l {t₁ t₂ t₃ D c n p : type_l B}
    (hD : ∀ n, member_l ℳ n ω.val → ∀ D, subset_l D n → member_l ℳ D B) :
    PowerlessLevyRule.step_l (ℳ := structure_l B hB) ω e T t₁ t₂ t₃ D c n p ↔
      PowerlessLevyRule.step_l ω.val e.val T.val t₁.val t₂.val t₃.val D.val c.val n.val p.val :=
  or_congr (PowerlessBoundedCertificateAbsolute.recognizes_l hℳ hBT hω he hT hI hD)
    (or_congr (boolean_l hℳ hBT hω he hT hI) (or_congr (bounded_l hℳ hBT hω he hT hI)
      (or_congr (quantifier_l hℳ hBT hω he hT hI) (promotion_l hℳ hBT hω he hT hI))))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyRuleAbsolute
