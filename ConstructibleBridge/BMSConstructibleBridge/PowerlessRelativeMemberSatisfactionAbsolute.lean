import BMSConstructibleBridge.PowerlessRelativeCofinalLimitBounds
import BMSConstructibleBridge.PowerlessAdditionBoundedGraph
import BMSConstructibleBridge.PowerlessRelativeLimitFiniteMaps
import BMSConstructibleBridge.PowerlessSourceGraphAbsolute
import BMSConstructibleBridge.PowerlessValueAbsolute
import BMSConstructibleBridge.PowerlessSatisfactionSpecification
import BMSConstructibleBridge.PowerlessFormulaConstructorBounded
import BMSConstructibleBridge.PowerlessBMSQuotientArithmetic

/-!
# 完整原 Sat 在实际共尾极限成员域中的绝对性

对象语言为纯成员语言 ℒ，背景为原 Z₂。结论运输同一个实际 Sat 图的
原完整规格，不以 Δ₀ 检查器代替成员模型中的原无界 Sat 规格。
原构造子所需的无限加法图先进入严格先前极限层的两次 Def；全部内部
有限赋值及量词分支更新图由原内部归纳留在 W。无需 Seq(ω,W)∈W、
W∈W、完整源理论或外部标准 ω。这里是供对象公式装配调用的语义中间核。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMemberSatisfactionAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B β W : SecondOrderQuotient.type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 同一原无限加法图进入 W；只使用真实共尾层的缓冲界。 -/
theorem addition_member_l (K : source_coding_l hℳ)
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    (hωW : mem_l hℳ K.omega W) {a F : SecondOrderQuotient.type_l hℳ}
    (ha : mem_l hℳ a K.omega)
    (hF : PowerlessAddition.iteration_l (ℳ := 𝒱) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val a F)
    (hMap : map_l (ℳ := 𝒱) F K.omega K.omega) : mem_l hℳ F W := by
  obtain ⟨γ, C, hγ, hC, hLimit, hωC, _⟩ :=
    PowerlessRelativeCofinalLimitBounds.exists_l hB hβ hW hCofinal
      (Env.empty (M := 𝒱)) hωW (fun _ v => nomatch v)
  obtain ⟨δ, D, hδ, hD, hCD⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hB hβ hW hγ hC
  obtain ⟨ε, E, hε, hE, hDE⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hB hβ hW hδ hD
  have hFE := PowerlessAdditionBoundedGraph.member_l K hB hC hLimit hCD hDE hωC ha hF hMap
  exact PowerlessRelativeLevelClosure.subset_l hℳ hB hε hE hW F hFE

variable {h₀ : ∃ x, mem_l hℳ x W}

local notation "𝒩₁" => PowerlessMemberStructure.structure_l (ℳ := 𝒱) W h₀
local notation "M" => PowerlessMemberStructure.type_l (ℳ := 𝒱) W

/-- 成员域中的完整加法迭代读回原商；只需传递性与实际 ω。 -/
theorem iteration_raw_l
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W) {ω e a F : M}
    (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (hF : PowerlessAddition.iteration_l (ℳ := 𝒩₁) ω e a F) :
    PowerlessAddition.iteration_l (ℳ := 𝒱) ω.val e.val a.val F.val := by
  obtain ⟨R, hMap, hZero, hStep⟩ := hF
  have hMap' := (PowerlessSourceGraphAbsolute.map_l hW).mp hMap
  refine ⟨R.val, hMap', (PowerlessSourceGraphAbsolute.value_l hW).mp hZero, ?_⟩
  intro n m x y hn hm hx hy
  obtain ⟨m', hm'ω, hm'⟩ := hω.1.2 n hn
  have hmω : mem_l hℳ m ω.val :=
    (PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ)
      (a := n) (b := m') (c := m) hm' hm) ▸ hm'ω
  let n' : M := ⟨n, hW ω.val n ω.property hn⟩
  let m'' : M := ⟨m, hW ω.val m ω.property hmω⟩
  let x' : M := ⟨x, hW R.val x R.property (SecondOrderFunctionProperties.value_mem_l hℳ hMap' hx).2⟩
  let y' : M := ⟨y, hW R.val y R.property (SecondOrderFunctionProperties.value_mem_l hℳ hMap' hy).2⟩
  apply (PowerlessAddition.step_formula_l (ℳ := 𝒱) ω.val x y).mpr
  apply (PowerlessSourceNaturalAbsolute.successor_l hW (a := x') (b := y')).mp
  exact (PowerlessAddition.step_formula_l (ℳ := 𝒩₁) ω x' y').mp
    (hStep n' m'' x' y' hn ((PowerlessSourceNaturalAbsolute.successor_l hW).mpr hm)
      ((PowerlessSourceGraphAbsolute.value_l hW).mpr hx)
      ((PowerlessSourceGraphAbsolute.value_l hW).mpr hy))

private theorem iteration_from_l
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W) {ω e a F : M}
    (hF : PowerlessAddition.iteration_l (ℳ := 𝒱) ω.val e.val a.val F.val)
    (hMap : map_l (ℳ := 𝒱) F.val ω.val ω.val) :
    PowerlessAddition.iteration_l (ℳ := 𝒩₁) ω e a F := by
  obtain ⟨_, _, hZero, hStep⟩ := hF
  refine ⟨ω, (PowerlessSourceGraphAbsolute.map_l hW).mpr hMap,
    (PowerlessSourceGraphAbsolute.value_l hW).mpr hZero, ?_⟩
  intro n m x y hn hm hx hy
  apply (PowerlessAddition.step_formula_l (ℳ := 𝒩₁) ω x y).mpr
  apply (PowerlessSourceNaturalAbsolute.successor_l hW).mpr
  exact (PowerlessAddition.step_formula_l (ℳ := 𝒱) ω.val x.val y.val).mp
    (hStep n.val m.val x.val y.val hn ((PowerlessSourceNaturalAbsolute.successor_l hW).mp hm)
      ((PowerlessSourceGraphAbsolute.value_l hW).mp hx)
      ((PowerlessSourceGraphAbsolute.value_l hW).mp hy))

/-- 同一实际加法关系在共尾极限成员域与原商中同值。 -/
theorem addition_l (K : source_coding_l hℳ)
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    {ω e a b c : M} (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (ha : mem_l hℳ a.val ω.val) (hb : mem_l hℳ b.val ω.val) :
    PowerlessAddition.addition_l (ℳ := 𝒩₁) ω e a b c ↔
      PowerlessAddition.addition_l (ℳ := 𝒱) ω.val e.val a.val b.val c.val := by
  have hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W :=
    fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hB hW x hx y hy
  constructor
  · rintro ⟨F, hF, hValue⟩
    exact ⟨F.val, iteration_raw_l hTrans (hω.symm ▸ K.omega_spec) hF,
      (PowerlessSourceGraphAbsolute.value_l hTrans).mp hValue⟩
  · intro h
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨a.val, hω ▸ ha⟩
    obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨b.val, hω ▸ hb⟩
    have hi' : (numberCode_l K i).val = a.val := congrArg Subtype.val hi
    have hj' : (numberCode_l K j).val = b.val := congrArg Subtype.val hj
    obtain ⟨F, hF, hMap⟩ := PowerlessBMSQuotientArithmetic.additionIteration_exists_l K i
    have hF' : PowerlessAddition.iteration_l (ℳ := 𝒱) ω.val e.val a.val F := by
      simpa only [hω, he, hi'] using hF
    have hMap' : map_l (ℳ := 𝒱) F ω.val ω.val := by simpa only [hω] using hMap
    have hiω : mem_l hℳ (numberCode_l K i).val K.omega := by
      simpa only [ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l] using
        (numberCode_l K i).property
    have hFW := addition_member_l K hB hβ hW hCofinal (hω ▸ ω.property)
      hiω hF hMap
    let F' : M := ⟨F, hFW⟩
    obtain ⟨y, ⟨_, hy⟩, _⟩ := hMap'.2 b.val hb
    have hc : c.val = (numberCode_l K (SecondOrderModel.add_l i j)).val := by
      apply (PowerlessBMSQuotientRecursion.addition_iff_l K i j c.val).mp
      simpa only [hω, he, hi', hj'] using h
    have hy' : y = (numberCode_l K (SecondOrderModel.add_l i j)).val := by
      apply (PowerlessBMSQuotientRecursion.addition_iff_l K i j y).mp
      simpa only [hω, he, hi', hj'] using
        (show PowerlessAddition.addition_l (ℳ := 𝒱) ω.val e.val a.val b.val y from ⟨F, hF', hy⟩)
    exact ⟨F', iteration_from_l hTrans hF' hMap',
      (PowerlessSourceGraphAbsolute.value_l hTrans).mpr ((hy'.trans hc.symm) ▸ hy)⟩

private theorem code_l (K : source_coding_l hℳ)
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    {ω e T a b c : M} (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hT : map_l (ℳ := 𝒱) T.val K.omega K.omega)
    (ha : mem_l hℳ a.val ω.val) (hb : mem_l hℳ b.val ω.val) :
    PowerlessPairingCode.code_l (ℳ := 𝒩₁) ω e T a b c ↔
      PowerlessPairingCode.code_l (ℳ := 𝒱) ω.val e.val T.val a.val b.val c.val := by
  have hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W :=
    fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hB hW x hx y hy
  constructor
  · rintro ⟨s, t, hs, ht, hc⟩
    have ht' := (PowerlessSourceGraphAbsolute.value_l hTrans).mp ht
    have htω : mem_l hℳ t.val ω.val :=
      hω.symm ▸ (SecondOrderFunctionProperties.value_mem_l hℳ hT ht').2
    exact ⟨s.val, t.val, (addition_l K hB hβ hW hCofinal hω he ha hb).mp hs, ht',
      (addition_l K hB hβ hW hCofinal hω he htω ha).mp hc⟩
  · rintro ⟨s, t, hs, ht, hc⟩
    have hsω : mem_l hℳ s ω.val := hω.symm ▸
      PowerlessFormulaConstructorBounded.addition_natural_l K (hω ▸ ha) (hω ▸ hb)
        (by simpa only [hω, he] using hs)
    have htω : mem_l hℳ t ω.val :=
      hω.symm ▸ (SecondOrderFunctionProperties.value_mem_l hℳ hT ht).2
    let s' : M := ⟨s, hTrans ω.val s ω.property hsω⟩
    let t' : M := ⟨t, hTrans ω.val t ω.property htω⟩
    exact ⟨s', t', (addition_l K hB hβ hW hCofinal hω he ha hb).mpr hs,
      (PowerlessSourceGraphAbsolute.value_l hTrans).mpr ht,
      (addition_l K hB hβ hW hCofinal hω he htω ha).mpr hc⟩

/-- 原公式构造子双向运输，所有中间码仍由实际内部 ω 收回。 -/
theorem constructor_l (K : source_coding_l hℳ)
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    {ω e T t a b n : M} (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hT : map_l (ℳ := 𝒱) T.val K.omega K.omega) :
    PowerlessFormulaConstructor.constructor_l (ℳ := 𝒩₁) ω e T t a b n ↔
      PowerlessFormulaConstructor.constructor_l (ℳ := 𝒱) ω.val e.val T.val t.val a.val b.val n.val := by
  have hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W :=
    fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hB hW x hx y hy
  constructor
  · rintro ⟨ha, hb, p, hp, ht, hpω, c, hc, hn⟩
    exact ⟨ha, hb, p.val, (code_l K hB hβ hW hCofinal hω he hT ha hb).mp hp,
      ht, hpω, c.val, (code_l K hB hβ hW hCofinal hω he hT ht hpω).mp hc,
      (PowerlessSourceNaturalAbsolute.successor_l hTrans).mp hn⟩
  · rintro ⟨ha, hb, p, hp, ht, hpω, c, hc, hn⟩
    have hcω : mem_l hℳ c ω.val := hω.symm ▸
      PowerlessFormulaConstructorBounded.code_natural_l K hT (hω ▸ ht)
        (by simpa only [hω, he] using hc)
    let p' : M := ⟨p, hTrans ω.val p ω.property hpω⟩
    let c' : M := ⟨c, hTrans ω.val c ω.property hcω⟩
    exact ⟨ha, hb, p', (code_l K hB hβ hW hCofinal hω he hT ha hb).mpr hp,
      ht, hpω, c', (code_l K hB hβ hW hCofinal (a := t) (b := p') (c := c')
        hω he hT ht (by
          simpa only [ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l] using hpω)).mpr hc,
      (PowerlessSourceNaturalAbsolute.successor_l hTrans).mpr hn⟩

/-- 任意内部长度的存在分支双向运输，更新图由实际有限函数层界收回。 -/
theorem exists_l (K : source_coding_l hℳ)
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W)
    {ω A R f i b : M} (hω : ω.val = K.omega) :
    PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := 𝒩₁) ω A R f i b ↔
      PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := 𝒱)
        ω.val A.val R.val f.val i.val b.val := by
  have hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W :=
    fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hB hW x hx y hy
  constructor
  · rintro ⟨n, hn, hf, hi, a, ha, g, hg, hUpdate, hValue⟩
    exact ⟨n.val, hn, (PowerlessSourceGraphAbsolute.map_l hTrans).mp hf, hi,
      a.val, ha, g.val, (PowerlessSourceGraphAbsolute.map_l hTrans).mp hg,
      (PowerlessValueAbsolute.update_l hTrans).mp hUpdate,
      (PowerlessSourceGraphAbsolute.value_l hTrans).mp hValue⟩
  · rintro ⟨n, hn, hf, hi, a, ha, g, hg, hUpdate, hValue⟩
    let n' : M := ⟨n, hTrans ω.val n ω.property hn⟩
    let a' : M := ⟨a, hTrans A.val a A.property ha⟩
    let g' : M := ⟨g, PowerlessRelativeLimitFiniteMaps.member_l hℳ hB hβ hW K
      (hω ▸ ω.property) A.property (hω ▸ hn) hg⟩
    exact ⟨n', hn, (PowerlessSourceGraphAbsolute.map_l hTrans).mpr hf, hi,
      a', ha, g', (PowerlessSourceGraphAbsolute.map_l hTrans).mpr hg,
      (PowerlessValueAbsolute.update_l hTrans).mpr hUpdate,
      (PowerlessSourceGraphAbsolute.value_l hTrans).mpr hValue⟩

/-- 环境中的原完整 Sat 规格在 W 中仍为原完整规格，不预供 Sat 对应。 -/
theorem spec_l (K : source_coding_l hℳ)
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    {ω A e t₁ t₂ t₃ T F R : M} (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hT : map_l (ℳ := 𝒱) T.val K.omega K.omega)
    (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒱)
      ω.val A.val e.val t₁.val t₂.val t₃.val T.val F.val R.val) :
    PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒩₁) ω A e t₁ t₂ t₃ T F R := by
  have hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W :=
    fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hB hW x hx y hy
  refine ⟨?_, ?_, ?_⟩
  · intro c f hValue
    obtain ⟨hc, L, hL, hF, hMap⟩ := hSat.1 c.val f.val
      ((PowerlessSourceGraphAbsolute.value_l hTrans).mp hValue)
    let L' : M := ⟨L, hTrans ω.val L ω.property hL⟩
    exact ⟨hc, L', hL, (PowerlessSourceGraphAbsolute.value_l hTrans).mpr hF,
      (PowerlessSourceGraphAbsolute.map_l hTrans).mpr hMap⟩
  · intro f hValue
    exact hSat.2.1 f.val ((PowerlessSourceGraphAbsolute.value_l hTrans).mp hValue)
  · intro c L f hc hL hf a b
    have h := hSat.2.2 c.val L.val f.val hc hL ((PowerlessSourceGraphAbsolute.map_l hTrans).mp hf)
      a.val b.val
    have hValue := PowerlessSourceGraphAbsolute.value_l (hA := h₀) hTrans
      (f := R) (a := c) (b := f)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hCtor ha hb
      exact hValue.trans ((h.1 ((constructor_l K hB hβ hW hCofinal hω he hT).mp hCtor) ha hb).trans
        (PowerlessValueAbsolute.member_l hTrans).symm)
    · intro hCtor ha hb
      exact hValue.trans ((h.2.1 ((constructor_l K hB hβ hW hCofinal hω he hT).mp hCtor) ha hb).trans
        (PowerlessValueAbsolute.equal_l hTrans).symm)
    · intro hCtor ha hb
      exact hValue.trans ((h.2.2.1 ((constructor_l K hB hβ hW hCofinal hω he hT).mp hCtor)
        ((PowerlessSourceGraphAbsolute.value_l hTrans).mp ha)
        ((PowerlessSourceGraphAbsolute.value_l hTrans).mp hb)).trans
          (not_congr (and_congr (PowerlessSourceGraphAbsolute.value_l hTrans).symm
            (PowerlessSourceGraphAbsolute.value_l hTrans).symm)))
    · intro hCtor ha hb
      exact hValue.trans ((h.2.2.2 ((constructor_l K hB hβ hW hCofinal hω he hT).mp hCtor) ha
        ((PowerlessSourceGraphAbsolute.value_l hTrans).mp hb)).trans
          (exists_l K hB hβ hW hω).symm)

/-- 仅消费实际原 ω、空集及配数自映射守卫，编码在 Prop 证明内取得。 -/
theorem guarded_l
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    {ω A e t₁ t₂ t₃ T F R : M} (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (he : ∀ x, ¬mem_l hℳ x e.val) (hT : map_l (ℳ := 𝒱) T.val ω.val ω.val)
    (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒱)
      ω.val A.val e.val t₁.val t₂.val t₃.val T.val F.val R.val) :
    PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒩₁) ω A e t₁ t₂ t₃ T F R := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have heEq : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _
      (fun x => iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  have hT' : map_l (ℳ := 𝒱) T.val K.omega K.omega := by simpa only [hωEq] using hT
  exact spec_l K hB hβ hW hCofinal hωEq heEq hT' hSat

#print axioms addition_member_l
#print axioms iteration_raw_l
#print axioms addition_l
#print axioms constructor_l
#print axioms exists_l
#print axioms spec_l
#print axioms guarded_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMemberSatisfactionAbsolute
