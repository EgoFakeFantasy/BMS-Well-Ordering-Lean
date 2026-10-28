import BMSConstructibleBridge.PowerlessLegacyDefinableQueryBounded
import BMSConstructibleBridge.PowerlessLegacyDefinableRows
import BMSConstructibleBridge.PowerlessLegacyAssignmentRealization
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlots
import BMSConstructibleBridge.PowerlessRelativeClassBounded

/-! # 原 Def 固定内部参数行的有界查询读数

显式翻译图 F 只消费全部内部数字坐标的原 C 读数。前向从 ω、Seq、Idx
中的有界见证取得实际 Class 对象，再以 Δ₀ 绝对性读取指定槽 Sat 查询；
后向使用原翻译域、长度预算和赋值实现取得全部见证。原求值保持性仍是
显式完整证书，不以外部 Formula 的翻译像代替全部内部原旧码。

存在见证均留在 Prop 中，不选择模型、原实数、翻译输出或有限赋值为
宿主 Type 数据。本模块证明固定行的模型语义等价，不宣称原 Def 对象
已属于 Class，亦不替代最终原推导关系 Derives 的正式交付。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableQueryReading

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderQuotient (mem_l)
open SecondOrderModel (num_l set_l zero_l succ_l add_l)
open SecondOrderFiniteAssignmentLift (number_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 翻译查询只使用给定 F 的全内部数字图读数，无须另加原 C 的规格。 -/
theorem translation_reading_l (K : source_coding_l hℳ)
    {N F : SecondOrderQuotient.type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega N) {C : set_l ℳ}
    (hFnumeric : ∀ n m, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F
      (code_l K n) (code_l K m) ↔ SecondOrderPairing.relation_l C n m)
    (p l q : num_l ℳ) :
    PowerlessLegacyDefinableQueryBounded.translation_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega (code_l K (zero_l ℳ)) N F
        (code_l K p) (code_l K l) (code_l K q) ↔
          SecondOrderLegacyFormulaTranslation.query_l C p l q := by
  unfold PowerlessLegacyDefinableQueryBounded.translation_l SecondOrderLegacyFormulaTranslation.query_l
  constructor
  · rintro ⟨a, _haω, hPair, hValue⟩
    rw [(PowerlessBoundedNumericPairing.instance_l K hN l q a).mp hPair] at hValue
    exact (hFnumeric p (SecondOrderPairing.value_l l q)).mp hValue
  · intro hQuery
    exact ⟨code_l K (SecondOrderPairing.value_l l q), (numberCode_l K _).property,
      (PowerlessBoundedNumericPairing.instance_l K hN l q _).mpr rfl,
      (hFnumeric p (SecondOrderPairing.value_l l q)).mpr hQuery⟩

variable {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

/-- 单槽 Sat 查询的完整有界式绝对性，包含赋值与更新的全部有界见证。 -/
theorem satisfaction_query_absolute_l (ω A Seq e Sat t x : type_l hℳ B) :
    PowerlessRelativeClassSatisfactionRows.query_l (ℳ₀ := ClassModel) ω A Seq e Sat t x ↔
      PowerlessRelativeClassSatisfactionRows.query_l (ℳ₀ := SecondOrderQuotient.structure_l hℳ)
        ω.val A.val Seq.val e.val Sat.val t.val x.val := by
  let η : Env ClassModel [] [.set, .set, .set, .set, .set, .set, .set] :=
    (((((((Env.empty).pushFree x).pushFree t).pushFree Sat).pushFree e).pushFree Seq).pushFree A).pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
    PowerlessRelativeClassSatisfactionRows.query_m
      (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
  have hClass : φ.satisfies η ↔
      PowerlessRelativeClassSatisfactionRows.query_l (ℳ₀ := ClassModel) ω A Seq e Sat t x :=
    PowerlessRelativeClassSatisfactionRows.query_formula_l η _ _ _ _ _ _ _
  have hRaw : φ.satisfies (PowerlessRelativeClassRelativization.env_l η) ↔
      PowerlessRelativeClassSatisfactionRows.query_l (ℳ₀ := SecondOrderQuotient.structure_l hℳ)
        ω.val A.val Seq.val e.val Sat.val t.val x.val :=
    PowerlessRelativeClassSatisfactionRows.query_formula_l
      (PowerlessRelativeClassRelativization.env_l η) _ _ _ _ _ _ _
  exact hClass.symm.trans ((PowerlessRelativeClassBounded.formula_l (φ := φ)
    (PowerlessRelativeClassSatisfactionRows.query_delta_l _ _ _ _ _ _ _) η).trans hRaw)

/-- 固定合法旧索引的原行，与有界查询在全部内部原元素码上精确相等。 -/
theorem reading_l (K : source_coding_l hℳ)
    {ω A N P F Seq Idx U Sat x : type_l hℳ B}
    (hΩ : omega_l (ℳ := ClassModel) ω) (hω : ω.val = K.omega)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega N.val) {E C V D T F₀ : set_l ℳ}
    (hPnumeric : ∀ n m, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) P.val
      (code_l K n) (code_l K m) ↔ SecondOrderPairing.relation_l E n m)
    (hFnumeric : ∀ n m, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val
      (code_l K n) (code_l K m) ↔ SecondOrderPairing.relation_l C n m)
    (hE : SecondOrderBinaryPowers.spec_l E)
    (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C)
    (hD : ∀ v, SecondOrderModel.mem_l v D)
    (hRowFamily : SecondOrderDefinableFamily.spec_l E D T F₀)
    {p l c v : num_l ℳ} (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (hLegal : SecondOrderPairing.relation_l V p (succ_l l))
    (hPreservation : ∀ n, PowerlessLegacyEvaluationRow.row_l K B A.val U.val Sat.val E C T n)
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U.val K.omega A.val)
    (hx : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U.val (code_l K v) x.val)
    (hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := ClassModel) ω A Seq)
    (hIdx : ∀ t : type_l hℳ B, mem_l hℳ t.val Idx.val ↔
      ∃ q f : type_l hℳ B, mem_l hℳ q.val ω.val ∧ mem_l hℳ f.val Seq.val ∧
        ordered_l (ℳ := ClassModel) q f t) :
    PowerlessLegacyDefinableQueryBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (zero_l ℳ)) N.val P.val F.val A.val Seq.val Idx.val U.val Sat.val
        (code_l K p) (code_l K l) (code_l K c) x.val ↔
          SecondOrderPairing.relation_l F₀ (SecondOrderDefinableFamily.index_l p l c) v := by
  have hNumber (n : num_l ℳ) : mem_l hℳ (number_l hBase K ω hω n).val ω.val := by
    change mem_l hℳ (code_l K n) ω.val
    rw [hω]
    exact (numberCode_l K n).property
  constructor
  · intro hHolds
    unfold PowerlessLegacyDefinableQueryBounded.holds_l
      PowerlessLegacyDefinableQueryBounded.body_l at hHolds
    obtain ⟨m, _hmω, q, hqω, L, hLω, f, hfSeq, t, htIdx,
      _hValid, hSucc, hTranslation, hBudget, hfRaw, hLinkBound, htRaw, hSatRaw⟩ := hHolds
    have hmEq := (PowerlessNumberSuccessorReading.successor_l K l m).mp hSucc
    obtain ⟨q₀, hq⟩ := numberCode_surjective_l K ⟨q, hqω⟩
    obtain ⟨L₀, hL⟩ := numberCode_surjective_l K ⟨L, hLω⟩
    have hqEq : q = code_l K q₀ := (congrArg Subtype.val hq).symm
    have hLEq : L = code_l K L₀ := (congrArg Subtype.val hL).symm
    rw [hmEq, hqEq] at hTranslation
    rw [hmEq, hLEq] at hBudget
    rw [hLEq] at hfRaw hLinkBound
    rw [hqEq] at htRaw
    have hQuery := (translation_reading_l K hN hFnumeric p (succ_l l) q₀).mp hTranslation
    have hBound := (PowerlessLegacyNumericReading.budget_l K hN (succ_l l) p L₀).mp hBudget
    let f' : type_l hℳ B := ⟨f,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Seq.property hfSeq⟩
    let t' : type_l hℳ B := ⟨t,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Idx.property htIdx⟩
    have hfClass : map_l (ℳ := ClassModel) f' (number_l hBase K ω hω L₀) A :=
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f' _ A).mpr hfRaw
    have htClass : ordered_l (ℳ := ClassModel) (number_l hBase K ω hω q₀) f' t' :=
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) _ f' t').mpr htRaw
    have hLink := (PowerlessLegacyLinkBounded.reading_l K hN hPnumeric c l L₀ (zero_l ℳ)
      hU hfRaw).mp hLinkBound
    have hSatClass : PowerlessRelativeClassSatisfactionRows.query_l (ℳ₀ := ClassModel)
        ω A Seq (number_l hBase K ω hω l) Sat t' x :=
      (satisfaction_query_absolute_l ω A Seq (number_l hBase K ω hω l) Sat t' x).mpr
        (by simpa only [hω, number_l, t'] using hSatRaw)
    exact (PowerlessLegacyDefinableRows.read_l (hBase := hBase) K hΩ hω hE hD hRowFamily
      hc hQuery hBound hPreservation hU hfClass hLink hSeq htClass hx).mpr hSatClass
  · intro hRow
    obtain ⟨q, hQuery⟩ := (SecondOrderLegacyFormulaTranslationDomain.domain_l hℳ hV hC p (succ_l l)).mp hLegal
    let L : num_l ℳ := add_l (succ_l l) p
    have hBound : SecondOrderLegacyFormulaTranslationLength.bound_l (succ_l l) p L := Or.inl rfl
    obtain ⟨f, hfClass, hLink⟩ := PowerlessLegacyAssignmentRealization.exists_l
      (hBase := hBase) K hΩ hω hE hc L (zero_l ℳ) hU
    have hfRaw : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val (code_l K L) A.val := by
      change SecondOrderFunctionObjects.map_l hℳ f.val (code_l K L) A.val
      exact (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase)
        f (number_l hBase K ω hω L) A).mp hfClass
    have hfSeq := (hSeq f).mpr ⟨number_l hBase K ω hω L, hNumber L, hfClass⟩
    obtain ⟨t, htRaw⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (code_l K q) f.val
    let t' : type_l hℳ B := ⟨t, PowerlessRelativeClassPair.ordered_l hℳ hBase
      (number_l hBase K ω hω q).property f.property htRaw⟩
    have htClass : ordered_l (ℳ := ClassModel) (number_l hBase K ω hω q) f t' :=
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) _ f t').mpr htRaw
    have htIdx := (hIdx t').mpr ⟨number_l hBase K ω hω q, f, hNumber q, hfSeq, htClass⟩
    have hSatClass := (PowerlessLegacyDefinableRows.read_l (hBase := hBase) K hΩ hω hE hD hRowFamily
      hc hQuery hBound hPreservation hU hfClass hLink hSeq htClass hx).mp hRow
    have hSatRaw := (satisfaction_query_absolute_l ω A Seq
      (number_l hBase K ω hω l) Sat t' x).mp hSatClass
    unfold PowerlessLegacyDefinableQueryBounded.holds_l PowerlessLegacyDefinableQueryBounded.body_l
    refine ⟨code_l K (succ_l l), (numberCode_l K _).property,
      code_l K q, (numberCode_l K q).property, code_l K L, (numberCode_l K L).property,
      f.val, hfSeq, t, htIdx, ?_⟩
    refine ⟨(PowerlessLegacyAssignmentBounded.valid_reading_l K hN hPnumeric c l).mpr hc,
      (PowerlessNumberSuccessorReading.successor_l K l _).mpr rfl,
      (translation_reading_l K hN hFnumeric p (succ_l l) q).mpr hQuery,
      (PowerlessLegacyNumericReading.budget_l K hN (succ_l l) p L).mpr hBound,
      hfRaw, (PowerlessLegacyLinkBounded.reading_l K hN hPnumeric c l L (zero_l ℳ) hU hfRaw).mpr hLink,
      htRaw, ?_⟩
    simpa only [hω, number_l, t'] using hSatRaw

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableQueryReading
