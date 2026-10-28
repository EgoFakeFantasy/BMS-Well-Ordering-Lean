import BMSConstructibleBridge.PowerlessRelativeClassSelectedImage
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph
import BMSConstructibleBridge.PowerlessRelativeClassNumericGraph
import BMSConstructibleBridge.PowerlessRelativeClassInjectionEnumeration
import BMSConstructibleBridge.PowerlessRelativeOrdinalCutoff
import BMSConstructibleBridge.PowerlessBMSClassRelationDomain
import BMSConstructibleBridge.SecondOrderCollapseFunction
import BMSConstructibleBridge.SecondOrderFunctionGraphComposition
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseInjectivity

/-! # 实际类内成员域的内部编号塌缩

纯隶属语言 ℒ 中，单射图 r 的精确像 D 是内部 ω 的实际类内子集。
类内有界关系图 A 只编码 I 内的成员边；原 Z₂ 模型中的实数 R 与 A 同码。
带默认值逆枚举只用于证明 R 无内部下降链，不把其默认分支加入 R。
上邻居条件保证 R 的端点域恰为 D，随后原图商塌缩函数与 r 复合。

塌缩图 H 与像 T 是原商中的真实集合对象；本文件不声称 H 或 T 属于
相对类，不假定源域传递、内部 ω 外部标准或成员关系宿主良基。
这仍是最终 BMS 对象推导的中间依赖。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapse

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderObjectSyntax (member_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 两个原对象见证均以 I 为界，求值读数采用已有纯 Δ₀ 图。 -/
def edge_m {Γ Δ : SortContext ℒ} (I r n m : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists I <|
    membershipLevyBound.boundedExists (up I) <| .conj
      (PowerlessValueBounded.formula_m (up (up r)) (.bvar (.there .here)) (up (up n)))
      (.conj (PowerlessValueBounded.formula_m (up (up r)) (.bvar .here) (up (up m)))
        (member_m (.bvar (.there .here)) (.bvar .here)))

theorem edge_delta_m {Γ Δ : SortContext ℒ} (I r n m : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (edge_m I r n m) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessValueBounded.delta_l _ _ _)
    (.conj (PowerlessValueBounded.delta_l _ _ _) (.rel _ _))))

def edge_l {𝒩₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (I r n m : carrier_l 𝒩₀) : Prop :=
  ∃ x, member_l 𝒩₀ x I ∧ ∃ y, member_l 𝒩₀ y I ∧
    value_l (ℳ := 𝒩₀) r x n ∧ value_l (ℳ := 𝒩₀) r y m ∧ member_l 𝒩₀ x y

theorem edge_formula_l {𝒩₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩₀ Γ Δ) (I r n m : Term ℒ Γ Δ .set) :
    (edge_m I r n m).satisfies η ↔ edge_l (I.eval η) (r.eval η) (n.eval η) (m.eval η) := by
  simp only [edge_m, edge_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "ClassType" => PowerlessRelativeClassStructure.type_l hℳ B

include hBase in
/-- 同一图 r 的精确像给出实际 used 域；不重新选取编号函数。 -/
theorem domain_l (I r O : ClassType)
    (hR : SecondOrderFunctionObjects.map_l hℳ r.val I.val O.val) :
    ∃ D : ClassType,
      (∀ n, mem_l hℳ n D.val → mem_l hℳ n O.val) ∧
      (∀ n, mem_l hℳ n D.val ↔ ∃ x, mem_l hℳ x I.val ∧
        SecondOrderFunctionObjects.value_l hℳ r.val x n) ∧
      SecondOrderFunctionObjects.map_l hℳ r.val I.val D.val ∧
      (∀ n, mem_l hℳ n D.val → ∃ x, mem_l hℳ x I.val ∧
        SecondOrderFunctionObjects.value_l hℳ r.val x n) := by
  obtain ⟨D, hD⟩ := PowerlessRelativeClassSelectedImage.exists_l (hBase := hBase) r I O
  have hRange (n : SecondOrderQuotient.type_l hℳ) : mem_l hℳ n D.val ↔
      ∃ x, mem_l hℳ x I.val ∧ SecondOrderFunctionObjects.value_l hℳ r.val x n := by
    constructor
    · intro hn
      exact ((hD n).mp hn).2
    · rintro ⟨x, hx, hxn⟩
      exact (hD n).mpr ⟨(SecondOrderFunctionProperties.value_mem_l hℳ hR hxn).2, x, hx, hxn⟩
  have hMap : SecondOrderFunctionObjects.map_l hℳ r.val I.val D.val := by
    constructor
    · intro p hp
      obtain ⟨x, n, hx, _, hxn⟩ := hR.1 p hp
      exact ⟨x, n, hx, (hRange n).mpr ⟨x, hx, p, hp, hxn⟩, hxn⟩
    · intro x hx
      obtain ⟨n, ⟨_, hxn⟩, hUnique⟩ := hR.2 x hx
      refine ⟨n, ⟨(hRange n).mpr ⟨x, hx, hxn⟩, hxn⟩, ?_⟩
      rintro m ⟨hm, hxm⟩
      exact hUnique m ⟨((hD m).mp hm).1, hxm⟩
  exact ⟨D, fun n hn => ((hD n).mp hn).1, hRange, hMap, fun n hn => (hRange n).mp hn⟩

include hBase in
/-- 输出为实际 Class 关系图，其精确读数覆盖全部原商坐标。 -/
theorem relation_l (I r D : ClassType)
    (hR : SecondOrderFunctionObjects.map_l hℳ r.val I.val D.val) :
    ∃ A : ClassType, ∀ n m : SecondOrderQuotient.type_l hℳ,
      SecondOrderFunctionObjects.value_l hℳ A.val n m ↔ edge_l (𝒩₀ := 𝒱) I.val r.val n m := by
  let η : Env 𝒩 [] [.set, .set] := (Env.empty.pushFree I).pushFree r
  let φ : Formula ℒ [] [.set, .set, .set, .set] := edge_m
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
    (.fvar .here) (.fvar (.there .here))
  obtain ⟨A, hA⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l (hBase := hBase)
    (φ := φ) (edge_delta_m _ _ _ _) η D D
  have hBody (n m : SecondOrderQuotient.type_l hℳ) :
      φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree m).pushFree n) ↔
        edge_l (𝒩₀ := 𝒱) I.val r.val n m := edge_formula_l
    (((PowerlessRelativeClassRelativization.env_l η).pushFree m).pushFree n)
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
    (.fvar .here) (.fvar (.there .here))
  refine ⟨A, fun n m => ?_⟩
  change value_l (ℳ := 𝒱) A.val n m ↔ _
  rw [hA n m, hBody n m]
  constructor
  · exact fun h => h.2.2
  · intro h
    obtain ⟨x, hx, y, hy, hxn, hym, hxy⟩ := h
    exact ⟨(SecondOrderFunctionProperties.value_mem_l hℳ hR hxn).2,
      (SecondOrderFunctionProperties.value_mem_l hℳ hR hym).2,
      x, hx, y, hy, hxn, hym, hxy⟩

/-- used 域与单张实数关系的全部规格；没有默认编号产生的额外边。 -/
def coded_spec_l (K : source_coding_l hℳ) (I r D A : ClassType)
    (R : SecondOrderModel.set_l ℳ) : Prop :=
  (∀ n, mem_l hℳ n D.val → mem_l hℳ n K.omega) ∧
  (∀ n, mem_l hℳ n D.val ↔ ∃ x, mem_l hℳ x I.val ∧
    SecondOrderFunctionObjects.value_l hℳ r.val x n) ∧
  SecondOrderFunctionObjects.map_l hℳ r.val I.val D.val ∧
  (∀ n, mem_l hℳ n D.val → ∃ x, mem_l hℳ x I.val ∧
    SecondOrderFunctionObjects.value_l hℳ r.val x n) ∧
  (∀ n m, SecondOrderFunctionObjects.value_l hℳ A.val n m ↔
    edge_l (𝒩₀ := 𝒱) I.val r.val n m) ∧
  (∀ n m, SecondOrderPairing.relation_l R n m ↔
    SecondOrderFunctionObjects.value_l hℳ A.val (numberCode_l K n).val (numberCode_l K m).val) ∧
  (∀ n, SecondOrderDomain.wf_l R n) ∧
  (∀ x, mem_l hℳ x D.val ↔ ∃ n, SecondOrderCollapseGraph.field_l R n ∧ x = (numberCode_l K n).val)

include hBase in
/-- 真实构造 D、A 和 R，并在模型内部证明全部数根良基及精确端点域。 -/
theorem coded_l (K : source_coding_l hℳ) (I r d : ClassType)
    (hR : SecondOrderFunctionObjects.map_l hℳ r.val I.val K.omega)
    (hInjective : SecondOrderFunctionObjects.injective_l hℳ r.val)
    (hd : mem_l hℳ d.val I.val)
    (hUpper : ∀ x, mem_l hℳ x I.val → ∃ p, mem_l hℳ p I.val ∧ mem_l hℳ x p) :
    ∃ D A U : ClassType, ∃ hU : ∀ c, mem_l hℳ c U.val → mem_l hℳ c K.omega,
      ∃ R : SecondOrderModel.set_l ℳ, setRel_l K ⟨U.val, hU⟩ R ∧ coded_spec_l K I r D A R := by
  let O : ClassType := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  obtain ⟨D, hSub, hRange, hMapD, hOnto⟩ := domain_l (hBase := hBase) I r O hR
  obtain ⟨A, hA⟩ := relation_l (hBase := hBase) I r D hMapD
  obtain ⟨U, hU, R, hTrace, hCode⟩ := PowerlessRelativeClassNumericGraph.coded_l (hBase := hBase) K A
  change ∀ n m, SecondOrderPairing.relation_l R n m ↔
    SecondOrderFunctionObjects.value_l hℳ A.val (numberCode_l K n).val (numberCode_l K m).val at hCode
  have hRClass : map_l (ℳ := 𝒩) r I O :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) r I O).mpr hR
  have hInjectiveClass : ∀ x y n : ClassType, value_l (ℳ := 𝒩) r x n →
      value_l (ℳ := 𝒩) r y n → x = y := by
    intro x y n hxn hyn
    exact Subtype.ext (hInjective x.val y.val n.val
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) r x n).mp hxn)
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) r y n).mp hyn))
  obtain ⟨G, hGClass, _, hGRead⟩ := PowerlessRelativeClassInjectionEnumeration.exists_l
    (hBase := hBase) (ω := O) (X := I) (R := r) (d := d) hRClass hInjectiveClass hd
  have hG : SecondOrderFunctionObjects.map_l hℳ G.val K.omega I.val :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) G O I).mp hGClass
  have hInverse (x n : SecondOrderQuotient.type_l hℳ) (hx : mem_l hℳ x I.val)
      (hxn : SecondOrderFunctionObjects.value_l hℳ r.val x n) :
      SecondOrderFunctionObjects.value_l hℳ G.val n x := by
    have hn := (SecondOrderFunctionProperties.value_mem_l hℳ hR hxn).2
    let x' : ClassType := ⟨x,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase I.property hx⟩
    let n' : ClassType := ⟨n,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property hn⟩
    exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) G n' x').mp
      ((hGRead n' x').mpr ⟨hn, hx, Or.inl
        ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) r x' n').mpr hxn)⟩)
  let φ : Formula ℒ [] [.set, .set, .set] :=
    value_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  let η : Env 𝒱 [] [.set] := Env.empty.pushFree G.val
  have hφ (n y : SecondOrderQuotient.type_l hℳ) :
      φ.satisfies ((η.pushFree n).pushFree y) ↔
        SecondOrderFunctionObjects.value_l hℳ G.val n y :=
    SecondOrderObjectSyntax.value_l hℳ ((η.pushFree n).pushFree y)
      (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  have hWF : ∀ n, SecondOrderDomain.wf_l R n := by
    apply PowerlessBMSClassRelationDomain.wf_l K φ η R
    · intro n
      have hn : mem_l hℳ (numberCode_l K n).val K.omega := by
        simpa only [ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l] using
          (numberCode_l K n).property
      obtain ⟨y, ⟨_, hny⟩, _⟩ := hG.2 _ hn
      exact ⟨y, (hφ _ y).mpr hny⟩
    · intro n y z hy hz
      exact SecondOrderFunctionProperties.value_unique_l hℳ hG
        ((hφ _ y).mp hy) ((hφ _ z).mp hz)
    · intro n m hnm
      obtain ⟨x, hx, y, hy, hxn, hym, hxy⟩ := (hA _ _).mp ((hCode n m).mp hnm)
      exact ⟨x, y, (hφ _ x).mpr (hInverse x _ hx hxn),
        (hφ _ y).mpr (hInverse y _ hy hym), hxy⟩
  have hField (n : SecondOrderModel.num_l ℳ) :
      SecondOrderCollapseGraph.field_l R n ↔ mem_l hℳ (numberCode_l K n).val D.val := by
    constructor
    · rintro ⟨m, hnm | hmn⟩
      · obtain ⟨x, hx, _, _, hxn, _, _⟩ := (hA _ _).mp ((hCode n m).mp hnm)
        exact (hRange _).mpr ⟨x, hx, hxn⟩
      · obtain ⟨_, _, y, hy, _, hyn, _⟩ := (hA _ _).mp ((hCode m n).mp hmn)
        exact (hRange _).mpr ⟨y, hy, hyn⟩
    · intro hn
      obtain ⟨x, hx, hxn⟩ := (hRange _).mp hn
      obtain ⟨p, hp, hxp⟩ := hUpper x hx
      obtain ⟨q, ⟨hq, hpq⟩, _⟩ := hR.2 p hp
      obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨q, hq⟩
      have hm' : (numberCode_l K m).val = q := congrArg Subtype.val hm
      refine ⟨m, Or.inl ((hCode n m).mpr ((hA _ _).mpr ?_))⟩
      exact ⟨x, hx, p, hp, hxn, hm'.symm ▸ hpq, hxp⟩
  have hDomain (x : SecondOrderQuotient.type_l hℳ) : mem_l hℳ x D.val ↔
      ∃ n, SecondOrderCollapseGraph.field_l R n ∧ x = (numberCode_l K n).val := by
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x, hSub x hx⟩
      have hn' : (numberCode_l K n).val = x := congrArg Subtype.val hn
      exact ⟨n, (hField n).mpr (hn'.symm ▸ hx), hn'.symm⟩
    · rintro ⟨n, hn, rfl⟩
      exact (hField n).mp hn
  exact ⟨D, A, U, hU, R, hTrace, hSub, hRange, hMapD, hOnto, hA, hCode, hWF, hDomain⟩

/-- 真正复合之后，编号成员递归式回到原 I 成员递归式。 -/
theorem recursive_l (I r D A T f H : SecondOrderQuotient.type_l hℳ)
    (hR : SecondOrderFunctionObjects.map_l hℳ r I D)
    (hInjective : SecondOrderFunctionObjects.injective_l hℳ r)
    (hA : ∀ n m, SecondOrderFunctionObjects.value_l hℳ A n m ↔ edge_l (𝒩₀ := 𝒱) I r n m)
    (hCollapse : SecondOrderCollapseFunction.spec_l hℳ A D T f)
    (hRead : ∀ x u, SecondOrderFunctionObjects.value_l hℳ H x u ↔
      ∃ n, SecondOrderFunctionObjects.value_l hℳ r x n ∧
        SecondOrderFunctionObjects.value_l hℳ f n u) :
    PowerlessRelativeMembershipCollapseInjectivity.recursive_l hℳ I H := by
  intro x u hx hxu z
  obtain ⟨n, hxn, hnu⟩ := (hRead x u).mp hxu
  have hn := (SecondOrderFunctionProperties.value_mem_l hℳ hR hxn).2
  constructor
  · intro hzu
    obtain ⟨j, _, hjn, hjz⟩ := (hCollapse.2.2.2 n u hn hnu z).mp hzu
    obtain ⟨y, hy, w, _, hyj, hwn, hyw⟩ := (hA j n).mp hjn
    have hwx : w = x := hInjective w x n hwn hxn
    exact ⟨y, hy, hwx ▸ hyw, (hRead y z).mpr ⟨j, hyj, hjz⟩⟩
  · rintro ⟨y, hy, hyx, hyz⟩
    obtain ⟨j, hyj, hjz⟩ := (hRead y z).mp hyz
    exact (hCollapse.2.2.2 n u hn hnu z).mpr
      ⟨j, (SecondOrderFunctionProperties.value_mem_l hℳ hR hyj).2,
        (hA j n).mpr ⟨y, hy, x, hx, hyj, hxn, hyx⟩, hjz⟩

/-- 塌缩的输出规格不附加 H 或 T 的相对类成员性。 -/
def spec_l (I T H : SecondOrderQuotient.type_l hℳ) : Prop :=
  (∀ x, mem_l hℳ x T → ∀ y, mem_l hℳ y x → mem_l hℳ y T) ∧
  SecondOrderFunctionObjects.map_l hℳ H I T ∧
  (∀ u, mem_l hℳ u T → ∃ x, mem_l hℳ x I ∧ SecondOrderFunctionObjects.value_l hℳ H x u) ∧
  PowerlessRelativeMembershipCollapseInjectivity.recursive_l hℳ I H ∧
  SecondOrderFunctionObjects.injective_l hℳ H ∧
  (∀ x y u v, mem_l hℳ x I → mem_l hℳ y I →
    SecondOrderFunctionObjects.value_l hℳ H x u → SecondOrderFunctionObjects.value_l hℳ H y v →
    (mem_l hℳ x y ↔ mem_l hℳ u v))

include hBase in
/-- 原商中的实际成员塌缩。当前应用显式提供非空 I 以构造逆枚举默认值。 -/
theorem exists_l (K : source_coding_l hℳ) {ω I : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hCount : PowerlessRelativeOrdinalCutoff.countable_l B ω I)
    (hExt : PowerlessRelativeMembershipCollapseInjectivity.ext_l hℳ I)
    (hUpper : ∀ x, mem_l hℳ x I → ∃ p, mem_l hℳ p I ∧ mem_l hℳ x p)
    (hNonempty : ∃ d, mem_l hℳ d I) :
    ∃ T H : SecondOrderQuotient.type_l hℳ, spec_l I T H := by
  have hωEq : ω = K.omega := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  rw [hωEq] at hCount
  obtain ⟨r, hr, hR, hInjective⟩ := hCount
  change SecondOrderFunctionObjects.map_l hℳ r I K.omega at hR
  change SecondOrderFunctionObjects.injective_l hℳ r at hInjective
  let I' : ClassType := ⟨I, hI⟩
  let r' : ClassType := ⟨r, hr⟩
  obtain ⟨d, hd⟩ := hNonempty
  let d' : ClassType := ⟨d, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hI hd⟩
  obtain ⟨D, A, _, _, R, _, hCoded⟩ :=
    coded_l (hBase := hBase) K I' r' d' hR hInjective hd hUpper
  rcases hCoded with ⟨_, _, hMapD, hOnto, hA, hCode, hWF, hDomain⟩
  obtain ⟨T, f, hCollapse⟩ := SecondOrderCollapseFunction.exists_l hℳ K.less R K.less_spec
    hWF A.val D.val hCode hDomain
  have hR₀ : map_l (ℳ := 𝒱) r I D.val := hMapD
  have hf₀ : map_l (ℳ := 𝒱) f D.val T := hCollapse.2.1
  obtain ⟨H, hH, hRead⟩ := SecondOrderFunctionGraphComposition.exists_l
    (ℳ := ℳ) (hℳ := hℳ) hR₀ hf₀
  change SecondOrderFunctionObjects.map_l hℳ H I T at hH
  change ∀ x u, SecondOrderFunctionObjects.value_l hℳ H x u ↔
    ∃ n, SecondOrderFunctionObjects.value_l hℳ r x n ∧
      SecondOrderFunctionObjects.value_l hℳ f n u at hRead
  have hRec := recursive_l I r D.val A.val T f H hMapD hInjective hA hCollapse hRead
  have hSurj : ∀ u, mem_l hℳ u T → ∃ x, mem_l hℳ x I ∧
      SecondOrderFunctionObjects.value_l hℳ H x u := by
    intro u hu
    obtain ⟨n, hn, hnu⟩ := hCollapse.2.2.1 u hu
    obtain ⟨x, hx, hxn⟩ := hOnto n hn
    exact ⟨x, hx, (hRead x u).mpr ⟨n, hxn, hnu⟩⟩
  exact ⟨T, H, (fun x hx y hy => hCollapse.1 x y hx hy), hH, hSurj, hRec,
    PowerlessRelativeMembershipCollapseInjectivity.injective_l hℳ I T H hH hExt hRec,
    fun _ _ _ _ hx hy hxu hyv =>
      PowerlessRelativeMembershipCollapseInjectivity.member_l hℳ I T H hH hExt hRec hx hy hxu hyv⟩

/-- 无孤立点守卫只要求一个 I 内上邻居，不要求整个单集规格。 -/
def upper_m {Γ Δ : SortContext ℒ} (I : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up I)) <|
    .existsE .set <| .conj (member_m (.bvar .here) (up (up I)))
      (member_m (.bvar (.there .here)) (.bvar .here))

def nonempty_m {Γ Δ : SortContext ℒ} (I : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (member_m (.bvar .here) (up I))

def onto_m {Γ Δ : SortContext ℒ} (I T H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up T)) <|
    .existsE .set <| .conj (member_m (.bvar .here) (up (up I)))
      (value_m (up (up H)) (.bvar .here) (.bvar (.there .here)))

def member_m {Γ Δ : SortContext ℒ} (I H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let x : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
    let y : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let u : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let v : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
    .imp (SecondOrderObjectSyntax.member_m x (up (up (up (up I))))) <|
      .imp (SecondOrderObjectSyntax.member_m y (up (up (up (up I))))) <|
        .imp (value_m (up (up (up (up H)))) x u) <|
          .imp (value_m (up (up (up (up H)))) y v) <|
            .iff (SecondOrderObjectSyntax.member_m x y) (SecondOrderObjectSyntax.member_m u v)

/-- 对象规格保留实际函数图、满射、成员递归、单射与成员同构。 -/
def spec_m {Γ Δ : SortContext ℒ} (I T H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchyDerives.transitive_m T) <|
    .conj (SecondOrderObjectSyntax.map_m H I T) <| .conj (onto_m I T H) <|
      .conj (PowerlessRelativeMembershipCollapseInjectivity.recursive_m I H) <|
        .conj (SecondOrderObjectSyntax.injective_m H) (member_m I H)

theorem upper_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (I : Term ℒ Γ Δ .set) :
    (upper_m I).satisfies η ↔ ∀ x, mem_l hℳ x (I.eval η) →
      ∃ p, mem_l hℳ p (I.eval η) ∧ mem_l hℳ x p := by
  simp only [upper_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem nonempty_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (I : Term ℒ Γ Δ .set) :
    (nonempty_m I).satisfies η ↔ ∃ d, mem_l hℳ d (I.eval η) := by
  simp only [nonempty_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem onto_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (I T H : Term ℒ Γ Δ .set) :
    (onto_m I T H).satisfies η ↔ ∀ u, mem_l hℳ u (T.eval η) →
      ∃ x, mem_l hℳ x (I.eval η) ∧ SecondOrderFunctionObjects.value_l hℳ (H.eval η) x u := by
  simp only [onto_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    SecondOrderObjectSyntax.value_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem member_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (I H : Term ℒ Γ Δ .set) :
    (member_m I H).satisfies η ↔ ∀ x y u v, mem_l hℳ x (I.eval η) →
      mem_l hℳ y (I.eval η) → SecondOrderFunctionObjects.value_l hℳ (H.eval η) x u →
      SecondOrderFunctionObjects.value_l hℳ (H.eval η) y v → (mem_l hℳ x y ↔ mem_l hℳ u v) := by
  simp only [member_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    SecondOrderObjectSyntax.value_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem spec_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (I T H : Term ℒ Γ Δ .set) :
    (spec_m I T H).satisfies η ↔ spec_l (I.eval η) (T.eval η) (H.eval η) := by
  simp only [spec_m, spec_l, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderObjectSyntax.map_l, onto_formula_l,
    PowerlessRelativeMembershipCollapseInjectivity.recursive_formula_l,
    SecondOrderObjectSyntax.injective_l, member_formula_l]

/-- 自由槽依次为传递基集、实际 ω 与原成员域 I。 -/
def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  let I := .fvar (.there (.there .here))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B I) <|
        .imp (PowerlessRelativeOrdinalCutoff.countable_m B ω I) <|
          .imp (PowerlessRelativeMembershipCollapseInjectivity.ext_m I) <|
            .imp (upper_m I) <| .imp (nonempty_m I) <|
              .existsE .set <| .existsE .set <|
                spec_m (up (up I)) (.bvar (.there .here)) (.bvar .here)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

/-- 全部原模型上的实际构造回接纯对象句，没有把未知塌缩存在列为守卫。 -/
theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K,
    PowerlessRelativeMembershipCollapseInjectivity.ext_formula_l,
    upper_formula_l, nonempty_formula_l, spec_formula_l, up, Term.eval_weakenBound, Term.eval]
  intro η hBase hω hI hCount hExt hUpper hNonempty
  exact exists_l (ℳ := ℳ) (hℳ := hℳ) (B := η.freeVal .here) (hBase := hBase)
    (ω := η.freeVal (.there .here)) (I := η.freeVal (.there (.there .here)))
    K hω hI hCount hExt hUpper hNonempty

/-- 带实际 Class、可数、外延、上邻居和非空守卫的原 Z₂ 正式塌缩推导。 -/
theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapse
