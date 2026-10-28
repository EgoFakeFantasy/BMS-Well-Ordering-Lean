import BMSConstructibleBridge.PowerlessRelativeMemberSatisfactionAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassStaticCodingReading
import BMSConstructibleBridge.PowerlessMemberBounded

/-! # 同一静态编码包在共尾极限成员域中的完整规格

对象语言为纯 ℒ，背景为原 Z₂。实际类内静态包的八个参数已属于
W=Lβ[B] 时，原完整静态规格在 MemberW 成立。三角递推和构造子中的
无限加法见证使用已证共尾层界；合法性查询只使用纯 Δ₀ 绝对性。
没有假定 MemberW 满足完整源理论，也没有更换编码图或以有界规格
冒充完整规格。这是最终对象推导所需的语义中间接口。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMemberStaticAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessRelativeClassStructure.structure_l

universe u

section Member

variable {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {W : carrier_l 𝒱}
  {h₀ : ∃ x, member_l 𝒱 x W}

local notation "𝒩₁" => PowerlessMemberStructure.structure_l W h₀
local notation "M" => PowerlessMemberStructure.type_l (ℳ := 𝒱) W

/-- 完整合法性图的查询正文是纯 Δ₀；这里只运输查询，不弱化整图规格。 -/
theorem query_l (hW : PowerlessNaturalOrder.transitive_l W)
    (ω e N T t₁ t₂ t₃ c l : M) :
    PowerlessFormulaValidityBounded.query_l (𝒩 := 𝒩₁) ω e N T t₁ t₂ t₃ c l ↔
      PowerlessFormulaValidityBounded.query_l (𝒩 := 𝒱)
        ω.val e.val N.val T.val t₁.val t₂.val t₃.val c.val l.val := by
  let η : Env 𝒩₁ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    (((((((((Env.empty).pushFree l).pushFree c).pushFree t₃).pushFree t₂).pushFree t₁).pushFree T).pushFree N).pushFree e).pushFree ω
  have h := PowerlessMemberBounded.formula_l
    (fun x hx y hy => hW x y hx hy)
    (PowerlessFormulaValidityBounded.query_delta_l (.fvar .here) (.fvar (.there .here))
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) η
  simpa only [PowerlessFormulaValidityBounded.query_formula_l, Term.eval,
    Env.pushFree_here, Env.pushFree_there, PowerlessRelativization.env_l, η] using h

/-- 同一个完整序列集合限制到成员域；长度仍为任意内部自然数。 -/
theorem sequences_l (hW : PowerlessNaturalOrder.transitive_l W) {ω A N : M}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) ω.val A.val N.val) :
    PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩₁) ω A N := by
  intro f
  constructor
  · intro hf
    obtain ⟨n, hn, hMap⟩ := (hN f.val).mp hf
    exact ⟨⟨n, hW ω.val n ω.property hn⟩, hn,
      (PowerlessSourceGraphAbsolute.map_l hW).mpr hMap⟩
  · rintro ⟨n, hn, hMap⟩
    exact (hN f.val).mpr ⟨n.val, hn, (PowerlessSourceGraphAbsolute.map_l hW).mp hMap⟩

end Member

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B β W : SecondOrderQuotient.type_l hℳ}
  {h₀ : ∃ x, mem_l hℳ x W}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₁" => PowerlessMemberStructure.structure_l (ℳ := 𝒱) W h₀
local notation "M" => PowerlessMemberStructure.type_l (ℳ := 𝒱) W

/-- 实际层的成员成为同一相对类的成员；包含映射没有选择数据。 -/
def class_l (hW : level_l hℳ B β W) (a : M) : PowerlessRelativeClassStructure.type_l hℳ B :=
  ⟨a.val, ⟨β, W, hW, a.property⟩⟩

/-- 八个原参数在 W 内时，实际类静态包给出 MemberW 的完整静态包。 -/
theorem spec_l (K : source_coding_l hℳ)
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    {ω e t₁ t₂ t₃ T N F : M} (hω : ω.val = K.omega)
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l
      (𝒩 := PowerlessRelativeClassStructure.structure_l hℳ B hB)
      (class_l hW ω) (class_l hW e) (class_l hW t₁) (class_l hW t₂)
      (class_l hW t₃) (class_l hW T) (class_l hW N) (class_l hW F)) :
    PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒩₁) ω e t₁ t₂ t₃ T N F := by
  have hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W :=
    fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hB hW x hx y hy
  obtain ⟨he, _, _, _, hN, hT, hPair, _⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l (hBase := hB) K hω hStatic
  change PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N.val at hN
  change map_l (ℳ := 𝒱) T.val K.omega K.omega at hT
  change PowerlessBMSQuotientPairingBounds.spec_l K T.val at hPair
  have he' : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := he
  have hT' : map_l (ℳ := 𝒱) T.val ω.val ω.val := by simpa only [hω] using hT
  have hN' : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) ω.val ω.val N.val := by
    simpa only [hω] using hN
  refine ⟨?_, ?_, ?_, sequences_l hTrans hN', ?_⟩
  · refine ⟨(PowerlessSourceNaturalAbsolute.zero_l hTrans).mpr ?_,
      (PowerlessSourceNaturalAbsolute.successor_l hTrans).mpr ?_,
      (PowerlessSourceNaturalAbsolute.successor_l hTrans).mpr ?_,
      (PowerlessSourceNaturalAbsolute.successor_l hTrans).mpr ?_⟩
    · exact (PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hB) (class_l hW e)).mp hStatic.1.1
    · exact (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hB)
        (class_l hW e) (class_l hW t₁)).mp hStatic.1.2.1
    · exact (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hB)
        (class_l hW t₁) (class_l hW t₂)).mp hStatic.1.2.2.1
    · exact (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hB)
        (class_l hW t₂) (class_l hW t₃)).mp hStatic.1.2.2.2
  · refine ⟨(PowerlessSourceGraphAbsolute.map_l hTrans).mpr hT',
      (PowerlessSourceGraphAbsolute.value_l hTrans).mpr ?_, ?_⟩
    · exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hB)
        (class_l hW T) (class_l hW e) (class_l hW e)).mp hStatic.2.1.2.1
    · intro n m x y hn hm hx hy
      have hm' := (PowerlessSourceNaturalAbsolute.successor_l hTrans).mp hm
      obtain ⟨m', hm'ω, hm'S⟩ := K.omega_spec.1.2 n.val (hω ▸ hn)
      have hmω : mem_l hℳ m.val ω.val := hω.symm ▸
        ((PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ)
          (a := n.val) (b := m') (c := m.val) hm'S hm') ▸ hm'ω)
      have hx' := (PowerlessSourceGraphAbsolute.value_l hTrans).mp hx
      have hxω := (SecondOrderFunctionProperties.value_mem_l hℳ hT' hx').2
      have hAdd := hStatic.2.1.2.2 (class_l hW n) (class_l hW m)
        (class_l hW x) (class_l hW y) hn
        ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hB)
          (class_l hW n) (class_l hW m)).mpr hm')
        ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hB)
          (class_l hW T) (class_l hW n) (class_l hW x)).mpr hx')
        ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hB)
          (class_l hW T) (class_l hW m) (class_l hW y)).mpr
            ((PowerlessSourceGraphAbsolute.value_l hTrans).mp hy))
      obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨x.val, hω ▸ hxω⟩
      obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨m.val, hω ▸ hmω⟩
      have hi' : x.val = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
      have hj' : m.val = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
      have hy' := (PowerlessRelativeClassAdditionAbsolute.instance_l (hBase := hB)
        K hω he' hi' hj').mp hAdd
      apply (PowerlessRelativeMemberSatisfactionAbsolute.addition_l
        K hB hβ hW hCofinal hω he' hxω hmω).mpr
      have hRaw := (PowerlessBMSQuotientRecursion.addition_iff_l K i j y.val).mpr hy'
      simpa only [hω, he', hi', hj'] using hRaw
  · intro t ht a ha b hb
    change mem_l hℳ t.val ω.val at ht
    change mem_l hℳ a.val ω.val at ha
    change mem_l hℳ b.val ω.val at hb
    obtain ⟨n, hnω, hn⟩ := PowerlessBMSQuotientConstructorTotal.exists_l
      K hT hPair (hω ▸ ht) (hω ▸ ha) (hω ▸ hb)
    let n' : M := ⟨n, hTrans ω.val n ω.property (hω.symm ▸ hnω)⟩
    have hn' : PowerlessFormulaConstructor.constructor_l (ℳ := 𝒱)
        ω.val e.val T.val t.val a.val b.val n := by simpa only [hω, he'] using hn
    refine ⟨n', (show mem_l hℳ n ω.val from hω.symm ▸ hnω),
      (PowerlessRelativeMemberSatisfactionAbsolute.constructor_l K hB hβ hW hCofinal
        hω he' hT).mpr hn', ?_⟩
    intro m hm
    have hm' := (PowerlessRelativeMemberSatisfactionAbsolute.constructor_l
      K hB hβ hW hCofinal hω he' hT).mp hm
    rw [hω, he'] at hm'
    exact Subtype.ext (PowerlessBMSQuotientConstructorTotal.unique_l K hT hPair hm' hn)
  · intro c l
    exact (PowerlessSourceGraphAbsolute.value_l hTrans).trans
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hB)
        (class_l hW F) (class_l hW c) (class_l hW l)).symm.trans
        ((hStatic.2.2.2.2 (class_l hW c) (class_l hW l)).trans
          ((PowerlessFormulaValiditySpecification.query_absolute_l (hBase := hB)
            (class_l hW ω) (class_l hW e) (class_l hW N) (class_l hW T)
            (class_l hW t₁) (class_l hW t₂) (class_l hW t₃)
            (class_l hW c) (class_l hW l)).trans
              (query_l hTrans ω e N T t₁ t₂ t₃ c l).symm)))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMemberStaticAbsolute
