import BMSConstructibleBridge.PowerlessMemberDefImageBoundedReading
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseSubdomain

/-! # 原 Def 数据的全部内部赋值与全部原商指标覆盖

对象语言为纯隶属 ℒ，背景与正式推导关系均为原 Z₂。母界只要求实际
传递性、配对／二元并闭包和真实 ω 成员资格，不要求 Class 或可构造
层资格。原有界数据恢复完整 Seq 和全部 raw 指标；乘积与查询读数
逐字保留。实际坍缩装配消费同一 H 的局部母域像，不把它换成整个 T。
这些条件尚未把查询行认同为原 Def，也不证明完整源 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefImageCoverage

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 反向覆盖量化全部环境对象，不只量化母界已有的指标。 -/
def indices_m {Γ Δ : SortContext ℒ}
    (ω e N F A S P J : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up J))
    (PowerlessLegacyImageIndicesBounded.select_m (up ω) (up e) (up N) (up F)
      (up A) (up S) (up P) (.bvar .here))

def spec_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N F A R S P J Q : carrier_l 𝒩) : Prop :=
  PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω A S ∧
    PowerlessMemberDefImageBounded.product_holds_l (𝒩 := 𝒩) ω S P ∧
      (∀ j, member_l 𝒩 j J ↔
        PowerlessLegacyImageIndicesBounded.select_l (𝒩 := 𝒩) ω e N F A S P j) ∧
          PowerlessMemberDefImageBounded.queries_holds_l (𝒩 := 𝒩) ω A S P R J Q

def spec_m {Γ Δ : SortContext ℒ}
    (ω e N F A R S P J Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessFiniteSequencesSyntax.spec_m ω A S) <|
    .conj (PowerlessMemberDefImageBounded.product_m ω S P) <|
      .conj (indices_m ω e N F A S P J)
        (PowerlessMemberDefImageBounded.queries_m ω A S P R J Q)

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N F A R S P J Q : Term ℒ Γ Δ .set) :
    (spec_m ω e N F A R S P J Q).satisfies η ↔
      spec_l (ω.eval η) (e.eval η) (N.eval η) (F.eval η) (A.eval η)
        (R.eval η) (S.eval η) (P.eval η) (J.eval η) (Q.eval η) := by
  simp only [spec_m, spec_l, indices_m, Formula.satisfies,
    PowerlessFiniteSequencesSyntax.spec_formula_l,
    PowerlessMemberDefImageBounded.product_formula_l,
    PowerlessMemberDefImageBounded.queries_formula_l,
    PowerlessLegacyImageIndicesBounded.select_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 原内部归纳覆盖任意非标准长度；不预供有限函数已经在母界中。 -/
theorem reading_l (K : source_coding_l hℳ) {W ω e N F A R S P J Q : type_l hℳ}
    (hω : ω = K.omega) (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) W)
    (hωW : mem_l hℳ ω W) (hAW : mem_l hℳ A W) (hPW : mem_l hℳ P W)
    (h : PowerlessMemberDefImageBounded.data_l (𝒩 := 𝒱) ω e N F W A R S P J Q) :
    spec_l (𝒩 := 𝒱) ω e N F A R S P J Q := by
  have hCoverage (f : type_l hℳ)
      (hf : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω A f) : mem_l hℳ f W := by
    obtain ⟨n, hn, hf⟩ := hf
    exact PowerlessRelativeFiniteHullAssignments.subset_member_l K
      (fun x hx => hTrans ω x hωW (hω.symm ▸ hx)) hClosed (hω ▸ hn) hf
      (fun x hx => hTrans A x hAW hx)
  exact ⟨(PowerlessFiniteSequencesBounded.spec_iff_of_coverage_l hCoverage).mp h.1,
    h.2.1, PowerlessMemberDefImageBoundedReading.indices_spec_l hTrans hClosed.1
      hωW hPW h.2.2.1, h.2.2.2⟩

/-- 指定局部母界的真实资格均从同一 H 与源操作闭包取得。 -/
theorem collapse_l (K : source_coding_l hℳ) {I T H U V e N F A R S P J Q : type_l hℳ}
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hI : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I)
    (hU : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) U)
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) U)
    (hUI : mem_l hℳ U I) (hUV : SecondOrderFunctionObjects.value_l hℳ H U V)
    (hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I)
    (hω : mem_l hℳ K.omega I) (hωU : mem_l hℳ K.omega U)
    (hAV : mem_l hℳ A V) (hPV : mem_l hℳ P V)
    (h : PowerlessMemberDefImageBounded.data_l (𝒩 := 𝒱) K.omega e N F V A R S P J Q) :
    spec_l (𝒩 := 𝒱) K.omega e N F A R S P J Q :=
  reading_l K rfl
    (PowerlessRelativeMembershipCollapseSubdomain.transitive_l hH.2.2.2.1 hUI hUV hTrans)
    (PowerlessRelativeMembershipCollapseSubdomain.closed_l hH hI hU hUI hUV)
    (PowerlessRelativeMembershipCollapseSubdomain.omega_l K hH hUI hUV hωI hω hωU)
    hAV hPV h

/-- 完整原数据读回模式，不把有界 checker 改称原 Def。 -/
def schema_m {Δ : SortContext ℒ}
    (W ω e N F A R S P J Q : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (PowerlessRelativeHierarchyDerives.transitive_m W) <|
      .imp (PowerlessRelativeFiniteHullAssignments.closed_m W) <|
        .imp (SecondOrderObjectSyntax.member_m ω W) <|
          .imp (SecondOrderObjectSyntax.member_m A W) <|
            .imp (SecondOrderObjectSyntax.member_m P W) <|
              .imp (PowerlessMemberDefImageBounded.data_m ω e N F W A R S P J Q)
                (spec_m ω e N F A R S P J Q)

def sentence_m {Δ : SortContext ℒ}
    (W ω e N F A R S P J Q : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m W ω e N F A R S P J Q)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (W ω e N F A R S P J Q : Term ℒ [] Δ .set) :
    (sentence_m W ω e N F A R S P J Q).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeFiniteHullAssignments.closed_formula_l,
    PowerlessMemberDefImageBounded.data_formula_l, formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro hω hTrans hClosed hωW hAW hPW h
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hW : PowerlessNaturalOrder.transitive_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) (W.eval η) :=
    fun x y hx hy => hTrans x hx y hy
  exact reading_l K hωEq hW hClosed hωW hAW hPW h

theorem derives_m {Δ : SortContext ℒ}
    (W ω e N F A R S P J Q : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m W ω e N F A R S P J Q)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ W ω e N F A R S P J Q)

#print axioms formula_l
#print axioms reading_l
#print axioms collapse_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefImageCoverage
