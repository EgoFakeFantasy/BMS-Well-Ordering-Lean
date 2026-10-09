import BMSConstructibleBridge.PowerlessDefinableFiniteTrace
import BMSConstructibleBridge.PowerlessRelativeClassFunctionAppend
import BMSConstructibleBridge.SecondOrderOmegaOrdinal
import BMSConstructibleBridge.PowerlessRelativeOrdinalCoverage

/-! # Class 中总的可定义关系的内部有限轨迹

任意 raw 原矩阵在 Class 上有 Class 见证，即可从 Class 初值构造每个
内部有限长度的实际 Class 图及 Class 陪域。矩阵可有不属于 Class 的
编码参数；不假定它对所有 raw 对象总，也不假定无限 Class 轨迹存在。
归纳仍是原 Z₂ 图翻译实例，而非相对类完整分离或宿主 Nat 归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassDefinableFiniteTrace

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l)
open PowerlessDefinableFiniteTrace (trace_l trace_m trace_formula_l lift_m lift_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

def finite_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B e a n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    .conj (PowerlessRelativeHierarchySyntax.class_m (up₃ B) (.bvar (.there .here))) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (up₃ B) (.bvar .here)) <|
        trace_m φ (up₃ e) (up₃ a) (up₃ n) (.bvar (.there (.there .here)))
          (.bvar (.there .here)) (.bvar .here)

def point_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B e a : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: Δ) :=
  finite_m (lift_m φ) (B.weakenFree SetTheory.SetSort.set)
    (e.weakenFree SetTheory.SetSort.set) (a.weakenFree SetTheory.SetSort.set) (.fvar .here)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem finite_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (B e a n : Term ℒ Γ Δ .set) :
    (finite_m φ B e a n).satisfies η ↔ ∃ S D f,
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) D ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) f ∧
      trace_l φ (parameters_l η) (e.eval η) (a.eval η) (n.eval η) S D f := by
  simp only [finite_m, Formula.satisfies, trace_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, parameters_pushBound_l,
    up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem point_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (B e a : Term ℒ [] Δ .set) (n : type_l hℳ) :
    (point_m φ B e a).satisfies (η.pushFree n) ↔ ∃ S D f,
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) D ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) f ∧
      trace_l φ η (e.eval η) (a.eval η) n S D f := by
  simp only [point_m, finite_formula_l K, parameters_empty_l,
    Term.eval_weakenFree, Term.eval, trace_l, lift_formula_l, Env.pushFree_here]

theorem induction_derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B e a : Term ℒ [] Δ .set) : Derives SecondOrderArithmetic.theory_m []
      (SecondOrderArithmetic.induction_m (GraphTranslation.form_m (point_m φ B e a))) :=
  GraphTranslation.induction_m (point_m φ B e a)

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (B e a : Term ℒ [] Δ .set)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval η))
    (haC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (a.eval η))
    (he : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hTotal : ∀ x, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) x →
      ∃ y, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y ∧
        φ.satisfies ((η.pushFree x).pushFree y)) (n : SecondOrderModel.num_l ℳ) :
    ∃ S D f, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) D ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) f ∧
      trace_l φ η (e.eval η) (a.eval η) (numberCode_l K n).val S D f := by
  obtain ⟨α, Cω, hCω, hωCω⟩ := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)
  have hωC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) K.omega :=
    ⟨α, Cω, hCω, hωCω⟩
  have hNumberC (i : SecondOrderModel.num_l ℳ) :
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (numberCode_l K i).val :=
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωC (numberCode_l K i).property
  have h := PowerlessBMSQuotientInduction.induction_l K (point_m φ B e a) η ?_ ?_
  · exact (point_formula_l K φ η B e a _).mp (h n)
  · apply (point_formula_l K φ η B e a _).mpr
    let z := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
    let S := (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val
    have hS := PowerlessBMSQuotientSuccessor.successor_l K (SecondOrderModel.zero_l ℳ)
    have hz := PowerlessBMSQuotientSuccessor.zero_l K
    obtain ⟨D, hD⟩ := SecondOrderPairObjects.pair_exists_l hℳ (a.eval η) (a.eval η)
    have hDC := PowerlessRelativeClassPair.pair_l hℳ hBase haC haC hD
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ z (a.eval η)
    have hpC := PowerlessRelativeClassPair.ordered_l hℳ hBase (hNumberC _) haC hp
    obtain ⟨f, hf⟩ := SecondOrderPairObjects.pair_exists_l hℳ p p
    have hFC := PowerlessRelativeClassPair.pair_l hℳ hBase hpC hpC hf
    have hSingleton := SecondOrderFunctionAppend.singleton_l hℳ
      (fun x => (hS x).trans (or_iff_right (hz x)))
      ((hD (a.eval η)).mpr (Or.inl rfl)) hp
      (fun q => by simpa only [or_self] using hf q)
    exact ⟨S, D, f, hDC, hFC, hS, hSingleton.1,
      (hSingleton.2 _ _).mpr ⟨he, rfl⟩, fun i _ _ _ hi => (hz i hi).elim⟩
  · intro i hPrevious
    obtain ⟨S, D, f, hDC, hFC, hF⟩ := (point_formula_l K φ η B e a _).mp hPrevious
    have hSEq : S = (numberCode_l K (SecondOrderModel.succ_l i)).val :=
      SecondOrderQuotient.ext_l hℳ S _ (fun x => (hF.1 x).trans
        (PowerlessBMSQuotientSuccessor.successor_l K i x).symm)
    have hSC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) S :=
      hSEq.symm ▸ hNumberC (SecondOrderModel.succ_l i)
    obtain ⟨z, hz, _⟩ := hF.2.1.2 _ ((hF.1 _).mpr (Or.inr rfl))
    have hzC := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hDC hz.1
    obtain ⟨d, hdC, hd⟩ := hTotal z hzC
    obtain ⟨T, E, g, _, hEC, hGC, hT, _, hG, hRead⟩ :=
      PowerlessRelativeClassFunctionAppend.exists_l hBase hFC hSC hDC hSC hdC hF.2.1
        (fun hSS => SecondOrderNaturalCases.asymmetry_l hℳ hSS hSS)
    apply (point_formula_l K φ η B e a _).mpr
    rw [← hSEq]
    exact ⟨T, E, g, hEC, hGC, PowerlessDefinableFiniteTrace.extension_l K φ η
      (n := (numberCode_l K i).val) (numberCode_l K i).property hF hG hT hRead hz.2 hd⟩

#print axioms finite_formula_l
#print axioms induction_derives_m
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassDefinableFiniteTrace
