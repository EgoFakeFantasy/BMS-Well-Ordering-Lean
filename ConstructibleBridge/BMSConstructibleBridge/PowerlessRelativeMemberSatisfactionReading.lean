import BMSConstructibleBridge.PowerlessRelativeMemberConstructorAbsolute
import BMSConstructibleBridge.PowerlessRelativeFiniteHullAssignments
import BMSConstructibleBridge.PowerlessRelativeMemberStaticAbsolute

/-! # 传递成员域中的完整 Seq 与 Sat 读回原商

对象语言为纯成员语言 ℒ，背景为原 Z₂。真实配对和二元并闭包给出
全部内部有限赋值；构造子对应消费成员域已经成立的完整总性。
因此 Sat 的定义域、零码及四个分支全部读回原商，包括量词更新图。
不用可构造层资格、完整源公理、外部标准 ω 或 Type 层数据选择。
本模块为实际坍缩后的 Def 精确截迹提供语义读取，不是 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMemberSatisfactionReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {W : SecondOrderQuotient.type_l hℳ} {h₀ : ∃ x, mem_l hℳ x W}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₁" => PowerlessMemberStructure.structure_l (ℳ := 𝒱) W h₀
local notation "M" => PowerlessMemberStructure.type_l (ℳ := 𝒱) W

/-- 任意真实图值的两个坐标属于传递域，不要求图是函数或无垃圾。 -/
theorem coordinates_l (hW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    {R : M} {a b : SecondOrderQuotient.type_l hℳ}
    (h : value_l (ℳ := 𝒱) R.val a b) : mem_l hℳ a W ∧ mem_l hℳ b W := by
  obtain ⟨p, hp, s, t, hs, ht, hp'⟩ := h
  have hpW := hW R.val p R.property hp
  have hsW := hW p s hpW ((hp' s).mpr (Or.inl rfl))
  have htW := hW p t hpW ((hp' t).mpr (Or.inr rfl))
  exact ⟨hW s a hsW ((hs a).mpr (Or.inl rfl)),
    hW t b htW ((ht b).mpr (Or.inr rfl))⟩

/-- 所有内部长度的真实赋值留在域中；从真实闭包推导，不预供有限图闭包。 -/
theorem assignment_l (K : source_coding_l hℳ)
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) W)
    {ω A : M} (hω : ω.val = K.omega) {n f : SecondOrderQuotient.type_l hℳ}
    (hn : mem_l hℳ n ω.val) (hf : map_l (ℳ := 𝒱) f n A.val) : mem_l hℳ f W :=
  PowerlessRelativeFiniteHullAssignments.subset_member_l K
    (I := W) (n := n) (A := A.val) (f := f)
    (fun x hx => hW ω.val x ω.property (hω.symm ▸ hx)) hClosed (hω ▸ hn) hf
    (fun x hx => hW A.val x A.property hx)

/-- 同一完整 Seq 图覆盖全部原商赋值，包含所有非标准内部长度。 -/
theorem sequences_l (K : source_coding_l hℳ)
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) W)
    {ω A S : M} (hω : ω.val = K.omega)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩₁) ω A S) :
    PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) ω.val A.val S.val := by
  intro f
  constructor
  · intro hf
    let f' : M := ⟨f, hW S.val f S.property hf⟩
    obtain ⟨n, hn, hMap⟩ := (hS f').mp hf
    exact ⟨n.val, hn, (PowerlessSourceGraphAbsolute.map_l hW).mp hMap⟩
  · rintro ⟨n, hn, hf⟩
    let n' : M := ⟨n, hW ω.val n ω.property hn⟩
    let f' : M := ⟨f, assignment_l K hW hClosed hω hn hf⟩
    exact (hS f').mpr ⟨n', hn, (PowerlessSourceGraphAbsolute.map_l hW).mpr hf⟩

/-- 存在分支双向读取，原真实更新图由内部有限赋值覆盖收回。 -/
theorem exists_l (K : source_coding_l hℳ)
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) W)
    {ω A R f i b : M} (hω : ω.val = K.omega) :
    PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := 𝒩₁) ω A R f i b ↔
      PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := 𝒱)
        ω.val A.val R.val f.val i.val b.val := by
  constructor
  · rintro ⟨n, hn, hf, hi, a, ha, g, hg, hUpdate, hValue⟩
    exact ⟨n.val, hn, (PowerlessSourceGraphAbsolute.map_l hW).mp hf, hi,
      a.val, ha, g.val, (PowerlessSourceGraphAbsolute.map_l hW).mp hg,
      (PowerlessValueAbsolute.update_l hW).mp hUpdate,
      (PowerlessSourceGraphAbsolute.value_l hW).mp hValue⟩
  · rintro ⟨n, hn, hf, hi, a, ha, g, hg, hUpdate, hValue⟩
    let n' : M := ⟨n, hW ω.val n ω.property hn⟩
    let a' : M := ⟨a, hW A.val a A.property ha⟩
    let g' : M := ⟨g, assignment_l K hW hClosed hω hn hg⟩
    exact ⟨n', hn, (PowerlessSourceGraphAbsolute.map_l hW).mpr hf, hi,
      a', ha, g', (PowerlessSourceGraphAbsolute.map_l hW).mpr hg,
      (PowerlessValueAbsolute.update_l hW).mpr hUpdate,
      (PowerlessSourceGraphAbsolute.value_l hW).mpr hValue⟩

/-- 成员域完整 Sat 的全部原商读数；不弱化为有界检查或域内条件分支。 -/
theorem spec_l (K : source_coding_l hℳ)
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) W)
    {ω A e t₁ t₂ t₃ P F R : M} (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hP : map_l (ℳ := 𝒱) P.val K.omega K.omega)
    (hFunctional : PowerlessRelativeClassConstructorTotal.functional_l (𝒩 := 𝒩₁) ω e P)
    (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒩₁) ω A e t₁ t₂ t₃ P F R) :
    PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒱)
      ω.val A.val e.val t₁.val t₂.val t₃.val P.val F.val R.val := by
  refine ⟨?_, ?_, ?_⟩
  · intro c f hValue
    obtain ⟨hcW, hfW⟩ := coordinates_l hW hValue
    let c' : M := ⟨c, hcW⟩
    let f' : M := ⟨f, hfW⟩
    obtain ⟨hc, L, hL, hF, hf⟩ := hSat.1 c' f'
      ((PowerlessSourceGraphAbsolute.value_l hW).mpr hValue)
    exact ⟨hc, L.val, hL, (PowerlessSourceGraphAbsolute.value_l hW).mp hF,
      (PowerlessSourceGraphAbsolute.map_l hW).mp hf⟩
  · intro f hValue
    let f' : M := ⟨f, (coordinates_l hW hValue).2⟩
    exact hSat.2.1 f' ((PowerlessSourceGraphAbsolute.value_l hW).mpr hValue)
  · intro c L f hc hL hf a b
    let c' : M := ⟨c, hW ω.val c ω.property hc⟩
    let L' : M := ⟨L, hW ω.val L ω.property hL⟩
    let f' : M := ⟨f, assignment_l K hW hClosed hω hL hf⟩
    have hStep (a' b' : M) := hSat.2.2 c' L' f' hc hL
      ((PowerlessSourceGraphAbsolute.map_l hW).mpr hf) a' b'
    have hValue := (PowerlessSourceGraphAbsolute.value_l (hA := h₀) hW
      (f := R) (a := c') (b := f')).symm
    have hCtor (t a' b' : M) :=
      PowerlessRelativeMemberConstructorAbsolute.constructor_l K hW
        (t := t) (a := a') (b := b') (n := c') hω he hP hFunctional
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h ha hb
      let a' : M := ⟨a, hW ω.val a ω.property h.1⟩
      let b' : M := ⟨b, hW ω.val b ω.property h.2.1⟩
      exact hValue.trans (((hStep a' b').1 ((hCtor e a' b').mpr h) ha hb).trans
        (PowerlessValueAbsolute.member_l hW))
    · intro h ha hb
      let a' : M := ⟨a, hW ω.val a ω.property h.1⟩
      let b' : M := ⟨b, hW ω.val b ω.property h.2.1⟩
      exact hValue.trans (((hStep a' b').2.1 ((hCtor t₁ a' b').mpr h) ha hb).trans
        (PowerlessValueAbsolute.equal_l hW))
    · intro h ha hb
      let a' : M := ⟨a, hW ω.val a ω.property h.1⟩
      let b' : M := ⟨b, hW ω.val b ω.property h.2.1⟩
      exact hValue.trans (((hStep a' b').2.2.1 ((hCtor t₂ a' b').mpr h)
        ((PowerlessSourceGraphAbsolute.value_l hW).mpr ha)
        ((PowerlessSourceGraphAbsolute.value_l hW).mpr hb)).trans
          (not_congr (and_congr (PowerlessSourceGraphAbsolute.value_l hW)
            (PowerlessSourceGraphAbsolute.value_l hW))))
    · intro h ha hb
      let a' : M := ⟨a, hW ω.val a ω.property h.1⟩
      let b' : M := ⟨b, hW ω.val b ω.property h.2.1⟩
      exact hValue.trans (((hStep a' b').2.2.2 ((hCtor t₃ a' b').mpr h) ha
        ((PowerlessSourceGraphAbsolute.value_l hW).mpr hb)).trans
          (exists_l K hW hClosed hω))

/-- 直接消费成员域静态包，真实配数自映射取自它，不新增预供正确图守卫。 -/
theorem static_l (K : source_coding_l hℳ)
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) W)
    {ω A e t₁ t₂ t₃ P N F R : M} (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒩₁) ω e t₁ t₂ t₃ P N F)
    (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒩₁) ω A e t₁ t₂ t₃ P F R) :
    PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒱)
      ω.val A.val e.val t₁.val t₂.val t₃.val P.val F.val R.val := by
  have hP : map_l (ℳ := 𝒱) P.val K.omega K.omega := by
    simpa only [hω] using (PowerlessSourceGraphAbsolute.map_l hW).mp hStatic.2.1.1
  exact spec_l K hW hClosed hω he hP hStatic.2.2.1 hSat

/-- 完整静态包也读回原商；三角递推不被有界合法性检查器替代。 -/
theorem static_raw_l (K : source_coding_l hℳ)
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) W)
    {ω e t₁ t₂ t₃ P N F : M} (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (h : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒩₁) ω e t₁ t₂ t₃ P N F) :
    PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒱)
      ω.val e.val t₁.val t₂.val t₃.val P.val N.val F.val := by
  have hωRaw : SecondOrderOmega.omega_l hℳ ω.val := hω.symm ▸ K.omega_spec
  have hP := (PowerlessSourceGraphAbsolute.map_l hW).mp h.2.1.1
  have hPK : map_l (ℳ := 𝒱) P.val K.omega K.omega := by simpa only [hω] using hP
  refine ⟨⟨(PowerlessSourceNaturalAbsolute.zero_l hW).mp h.1.1,
    (PowerlessSourceNaturalAbsolute.successor_l hW).mp h.1.2.1,
    (PowerlessSourceNaturalAbsolute.successor_l hW).mp h.1.2.2.1,
    (PowerlessSourceNaturalAbsolute.successor_l hW).mp h.1.2.2.2⟩,
    ⟨hP, (PowerlessSourceGraphAbsolute.value_l hW).mp h.2.1.2.1, ?_⟩,
    ?_, sequences_l K hW hClosed hω h.2.2.2.1, ?_⟩
  · intro n m x y hn hm hx hy
    obtain ⟨hnW, hxW⟩ := coordinates_l hW hx
    obtain ⟨hmW, hyW⟩ := coordinates_l hW hy
    let n' : M := ⟨n, hnW⟩
    let m' : M := ⟨m, hmW⟩
    let x' : M := ⟨x, hxW⟩
    let y' : M := ⟨y, hyW⟩
    exact PowerlessRelativeMemberConstructorAbsolute.addition_raw_l hW hωRaw
      (h.2.1.2.2 n' m' x' y' hn ((PowerlessSourceNaturalAbsolute.successor_l hW).mpr hm)
        ((PowerlessSourceGraphAbsolute.value_l hW).mpr hx)
        ((PowerlessSourceGraphAbsolute.value_l hW).mpr hy))
  · intro t ht a ha b hb
    let t' : M := ⟨t, hW ω.val t ω.property ht⟩
    let a' : M := ⟨a, hW ω.val a ω.property ha⟩
    let b' : M := ⟨b, hW ω.val b ω.property hb⟩
    obtain ⟨n, hn, hCtor, _⟩ := h.2.2.1 t' ht a' ha b' hb
    have hRaw := PowerlessRelativeMemberConstructorAbsolute.constructor_raw_l hW hωRaw hCtor
    refine ⟨n.val, hn, hRaw, ?_⟩
    intro m hm
    exact PowerlessRelativeMemberConstructorAbsolute.unique_l K hPK
      (by simpa only [hω, he] using hm) (by simpa only [hω, he] using hRaw)
  · intro c l
    constructor
    · intro hValue
      obtain ⟨hcW, hlW⟩ := coordinates_l hW hValue
      let c' : M := ⟨c, hcW⟩
      let l' : M := ⟨l, hlW⟩
      exact (PowerlessRelativeMemberStaticAbsolute.query_l hW ω e N P t₁ t₂ t₃ c' l').mp
        ((h.2.2.2.2 c' l').mp ((PowerlessSourceGraphAbsolute.value_l hW).mpr hValue))
    · intro hQuery
      let c' : M := ⟨c, hW ω.val c ω.property hQuery.1⟩
      let l' : M := ⟨l, hW ω.val l ω.property hQuery.2.1⟩
      exact (PowerlessSourceGraphAbsolute.value_l hW).mp ((h.2.2.2.2 c' l').mpr
        ((PowerlessRelativeMemberStaticAbsolute.query_l hW ω e N P t₁ t₂ t₃ c' l').mpr hQuery))

/-- 不固定 Type 编码包；在 Prop 内取得它并读取同一完整静态与 Sat 包。 -/
theorem guarded_l (hW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) W)
    {ω A e t₁ t₂ t₃ P N F R : M} (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒩₁) ω e t₁ t₂ t₃ P N F)
    (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒩₁) ω A e t₁ t₂ t₃ P F R) :
    PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒱)
      ω.val e.val t₁.val t₂.val t₃.val P.val N.val F.val ∧
    PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒱)
      ω.val A.val e.val t₁.val t₂.val t₃.val P.val F.val R.val := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have heRaw := (PowerlessSourceNaturalAbsolute.zero_l hW).mp hStatic.1.1
  have heEq : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _
      (fun x => iff_of_false (heRaw x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  exact ⟨static_raw_l K hW hClosed hωEq heEq hStatic,
    static_l K hW hClosed hωEq heEq hStatic hSat⟩

#print axioms coordinates_l
#print axioms assignment_l
#print axioms sequences_l
#print axioms exists_l
#print axioms spec_l
#print axioms static_l
#print axioms static_raw_l
#print axioms guarded_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMemberSatisfactionReading
