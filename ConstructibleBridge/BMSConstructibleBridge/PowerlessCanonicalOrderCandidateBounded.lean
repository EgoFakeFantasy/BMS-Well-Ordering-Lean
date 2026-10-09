import BMSConstructibleBridge.PowerlessCanonicalIndexBounded
import BMSConstructibleBridge.PowerlessCanonicalOrderGraphBounded
import BMSConstructibleBridge.SecondOrderRowFamilyBounded

/-! # 规范后继证书的完整有界数据包

所有辅助对象由调用端放进同一真实母界；C 只覆盖有限赋值，绝不要求
C∈C。指标、查询、精确行族、行序和末端扩张逐项检查。良序性不在
检查器中，须由真实父序与规范构造证明后再恢复原后继步骤。

这里对任意候选图保留全部 raw 规格，不把已存在的 Class、枚举或
Collection 当作证书条件。统一历史及其原 Z₂ 对象推导仍由后续装配。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderCandidateBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def data_m {Γ Δ : SortContext ℒ}
    (C ω A P Sat D E S I J N T K U Q Y L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessCanonicalIndexBounded.formula_m C ω A P S I J N T K U) <|
    .conj (PowerlessRelationBounded.clean_m Q J A) <|
      .conj (PowerlessMemberDefImageBounded.queries_m ω A S I Sat J Q) <|
        .conj (SecondOrderRowFamilyBounded.formula_m J A Q Y) <|
          .conj (membershipLevyBound.boundedForall D
            (SecondOrderObjectSyntax.member_m (.bvar .here) (up Y))) <|
            .conj (PowerlessCanonicalOrderGraphBounded.row_m J U A Q Y L)
              (PowerlessCanonicalOrderGraphBounded.extension_m A P L D E)

theorem data_delta_l {Γ Δ : SortContext ℒ}
    (C ω A P Sat D E S I J N T K U Q Y L : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (data_m C ω A P Sat D E S I J N T K U Q Y L) :=
  .conj (PowerlessCanonicalIndexBounded.delta_l _ _ _ _ _ _ _ _ _ _ _)
    (.conj (PowerlessRelationBounded.clean_delta_l _ _ _)
      (.conj (PowerlessMemberDefImageBounded.queries_delta_l _ _ _ _ _ _ _)
        (.conj (SecondOrderRowFamilyBounded.delta_l _ _ _ _)
          (.conj (.bounded_forall _ (.rel _ _))
            (.conj (PowerlessCanonicalOrderGraphBounded.row_delta_l _ _ _ _ _ _)
              (PowerlessCanonicalOrderGraphBounded.extension_delta_l _ _ _ _ _))))))

def data_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (C ω A P Sat D E S I J N T K U Q Y L : carrier_l 𝒩) : Prop :=
  PowerlessCanonicalIndexBounded.holds_l (𝒩 := 𝒩) C ω A P S I J N T K U ∧
    PowerlessRelationBounded.clean_l (𝒩 := 𝒩) Q J A ∧
      PowerlessMemberDefImageBounded.queries_holds_l (𝒩 := 𝒩) ω A S I Sat J Q ∧
        SecondOrderRowFamilyBounded.holds_l (𝒩 := 𝒩) J A Q Y ∧
          subset_l (ℳ := 𝒩) D Y ∧
            PowerlessCanonicalOrderGraphBounded.row_holds_l (𝒩 := 𝒩) J U A Q Y L ∧
              PowerlessCanonicalOrderGraphBounded.extension_holds_l (𝒩 := 𝒩) A P L D E

theorem data_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ)
    (C ω A P Sat D E S I J N T K U Q Y L : Term ℒ Γ Δ .set) :
    (data_m C ω A P Sat D E S I J N T K U Q Y L).satisfies η ↔ data_l
      (C.eval η) (ω.eval η) (A.eval η) (P.eval η) (Sat.eval η) (D.eval η) (E.eval η)
      (S.eval η) (I.eval η) (J.eval η) (N.eval η) (T.eval η) (K.eval η) (U.eval η)
      (Q.eval η) (Y.eval η) (L.eval η) := by
  simp only [data_m, data_l, Formula.satisfies,
    PowerlessCanonicalIndexBounded.formula_l, PowerlessRelationBounded.clean_formula_l,
    PowerlessMemberDefImageBounded.queries_formula_l, SecondOrderRowFamilyBounded.formula_l,
    PowerlessCanonicalOrderGraphBounded.row_formula_l,
    PowerlessCanonicalOrderGraphBounded.extension_formula_l,
    Formula.LevyBound.boundedForall, Formula.LevyBound.membership, membershipLevyBound,
    SecondOrderObjectSyntax.member_m, ThirdOrderSemantics.subset_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

private abbrev up₁₀ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  up (up (up (up (up (up (up (up (up (up t)))))))))

/-- 十个辅助对象真正有界于 C；待检查的输出 E 不是见证母界。 -/
def formula_m {Γ Δ : SortContext ℒ} (C ω A P Sat D E : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists C <|
    membershipLevyBound.boundedExists (up C) <|
      membershipLevyBound.boundedExists (up (up C)) <|
        membershipLevyBound.boundedExists (up (up (up C))) <|
          membershipLevyBound.boundedExists (up (up (up (up C)))) <|
            membershipLevyBound.boundedExists (up (up (up (up (up C))))) <|
              membershipLevyBound.boundedExists (up (up (up (up (up (up C)))))) <|
                membershipLevyBound.boundedExists (up (up (up (up (up (up (up C))))))) <|
                  membershipLevyBound.boundedExists (up (up (up (up (up (up (up (up C)))))))) <|
                    membershipLevyBound.boundedExists (up (up (up (up (up (up (up (up (up C))))))))) <|
                      data_m (up₁₀ C) (up₁₀ ω) (up₁₀ A) (up₁₀ P) (up₁₀ Sat) (up₁₀ D) (up₁₀ E)
                        (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
                        (.bvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
                        (.bvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
                        (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
                        (.bvar (.there (.there (.there (.there (.there .here))))))
                        (.bvar (.there (.there (.there (.there .here)))))
                        (.bvar (.there (.there (.there .here))))
                        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem delta_l {Γ Δ : SortContext ℒ} (C ω A P Sat D E : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m C ω A P Sat D E) :=
  .bounded_exists _ (.bounded_exists _ (.bounded_exists _ (.bounded_exists _
    (.bounded_exists _ (.bounded_exists _ (.bounded_exists _ (.bounded_exists _
      (.bounded_exists _ (.bounded_exists _ (data_delta_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))))))))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (C ω A P Sat D E : carrier_l 𝒩) : Prop :=
  ∃ S, member_l 𝒩 S C ∧ ∃ I, member_l 𝒩 I C ∧ ∃ J, member_l 𝒩 J C ∧
    ∃ N, member_l 𝒩 N C ∧ ∃ T, member_l 𝒩 T C ∧ ∃ K, member_l 𝒩 K C ∧
      ∃ U, member_l 𝒩 U C ∧ ∃ Q, member_l 𝒩 Q C ∧ ∃ Y, member_l 𝒩 Y C ∧
        ∃ L, member_l 𝒩 L C ∧ data_l (𝒩 := 𝒩) C ω A P Sat D E S I J N T K U Q Y L

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (C ω A P Sat D E : Term ℒ Γ Δ .set) :
    (formula_m C ω A P Sat D E).satisfies η ↔ holds_l
      (C.eval η) (ω.eval η) (A.eval η) (P.eval η) (Sat.eval η) (D.eval η) (E.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    data_formula_l, Arguments.eval, up₁₀, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

/-- 查询保留干净成员；否则完整逐值读数仍不足以识别该图对象。 -/
theorem query_read_l {ω A S I Sat J Q : Raw}
    (hClean : PowerlessRelationBounded.clean_l (𝒩 := 𝒱) Q J A)
    (hQ : PowerlessMemberDefImageBounded.queries_holds_l (𝒩 := 𝒱) ω A S I Sat J Q) :
    ∀ j x, value_l (ℳ := 𝒱) Q j x ↔ SecondOrderQuotient.mem_l hℳ j J ∧
      SecondOrderQuotient.mem_l hℳ x A ∧
        PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒱) ω A S I Sat j x := by
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
    PowerlessRelativeClassSatisfactionAllSlots.query_m
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set] :=
    ((((Env.empty.pushFree Sat).pushFree I).pushFree S).pushFree A).pushFree ω
  have hφ j x : φ.satisfies ((η.pushFree x).pushFree j) ↔
      PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒱) ω A S I Sat j x :=
    PowerlessRelativeClassSatisfactionAllSlots.query_formula_l _ _ _ _ _ _ _ _
  have hLocal : PowerlessRelationBounded.holds_l φ η J A Q :=
    ⟨hClean, fun j hj x hx => (hQ j hj x hx).trans (hφ j x).symm⟩
  intro j x
  exact (PowerlessRelationBounded.value_read_l hLocal j x).trans
    (and_congr Iff.rfl (and_congr Iff.rfl (hφ j x)))

structure rawspec_l (ω A P Sat D E S I J N T K U Q Y L : Raw) : Prop where
  index : PowerlessCanonicalIndexBounded.rawspec_l ω A P S I J N T K U
  queryClean : PowerlessRelationBounded.clean_l (𝒩 := 𝒱) Q J A
  queryRead : ∀ j x, value_l (ℳ := 𝒱) Q j x ↔ SecondOrderQuotient.mem_l hℳ j J ∧
    SecondOrderQuotient.mem_l hℳ x A ∧
      PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒱) ω A S I Sat j x
  family : PowerlessRelativeClassRowOrderCanonical.family_l (ℳ₀ := 𝒱) J A Q Y
  rowGraph : PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒱) J U A Q Y L
  subset : subset_l (ℳ := 𝒱) D Y
  extension : SecondOrderWellOrderEndExtensionUnique.graph_l (ℳ₀ := 𝒱) A D P L E

/-- 独立于候选序列集的实际覆盖界恢复完整证书；不预设候选良序性。 -/
theorem reading_l {C ω A P Sat D E S I J N T K U Q Y L : Raw}
    (hCoverage : ∀ f, PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω A f →
      SecondOrderQuotient.mem_l hℳ f C) :
    data_l (𝒩 := 𝒱) C ω A P Sat D E S I J N T K U Q Y L ↔
      rawspec_l ω A P Sat D E S I J N T K U Q Y L := by
  constructor
  · rintro ⟨hIndex, hClean, hQuery, hFamily, hSub, hRows, hExtension⟩
    exact {
      index := (PowerlessCanonicalIndexBounded.reading_l hCoverage).mp hIndex
      queryClean := hClean
      queryRead := query_read_l hClean hQuery
      family := (SecondOrderRowFamilyBounded.family_iff_l hℳ).mp hFamily
      rowGraph := (PowerlessCanonicalOrderGraphBounded.row_graph_iff_l J U A Q Y L).mp hRows
      subset := hSub
      extension := (PowerlessCanonicalOrderGraphBounded.extension_graph_iff_l A P L D E).mp hExtension }
  · intro h
    refine ⟨(PowerlessCanonicalIndexBounded.reading_l hCoverage).mpr h.index,
      h.queryClean, ?_, (SecondOrderRowFamilyBounded.family_iff_l hℳ).mpr h.family, h.subset,
      (PowerlessCanonicalOrderGraphBounded.row_graph_iff_l J U A Q Y L).mpr h.rowGraph,
      (PowerlessCanonicalOrderGraphBounded.extension_graph_iff_l A P L D E).mpr h.extension⟩
    intro j hj x hx
    exact (h.queryRead j x).trans ⟨fun h => h.2.2, fun h => ⟨hj, hx, h⟩⟩

#print axioms data_delta_l
#print axioms delta_l
#print axioms formula_l
#print axioms query_read_l
#print axioms reading_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderCandidateBounded
