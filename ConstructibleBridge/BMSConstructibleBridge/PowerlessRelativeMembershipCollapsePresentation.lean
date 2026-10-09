import BMSConstructibleBridge.PowerlessRelativeMembershipCollapse
import BMSConstructibleBridge.PowerlessBMSClassCollapse

/-! # 同一实际成员坍缩的类内实数图表示

源编号和数值关系确实属于相对类；实际坍缩 H 不要求属于类。用原 Z₂
理解构造的双模拟证明每个编号根精确代表 H 的对应值，并保留同一 T 的
完整根值域。这补回原坍缩存在接口未保留的类内实数代表，不重选 T/H。
本文件仍是对象证明装配的语义中间层；不由此宣称 ClassH、类内可数 T、
严格 J<Ω、Collection 或最终固定高度良序闭句已经成立。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapsePresentation

open Logic FirstOrder StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l mk_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def image_m {Γ Δ : SortContext ℒ} (I r H n y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists I <| .conj
    (PowerlessValueBounded.formula_m (up r) (.bvar .here) (up n))
    (PowerlessValueBounded.formula_m (up H) (.bvar .here) (up y))

theorem image_delta_m {Γ Δ : SortContext ℒ} (I r H n y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (image_m I r H n y) :=
  .bounded_exists _ (.conj (PowerlessValueBounded.delta_l _ _ _)
    (PowerlessValueBounded.delta_l _ _ _))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def image_l (I r H n y : Raw) : Prop :=
  ∃ x, mem_l hℳ x I ∧ SecondOrderFunctionObjects.value_l hℳ r x n ∧
    SecondOrderFunctionObjects.value_l hℳ H x y

theorem image_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (I r H n y : Term ℒ Γ Δ .set) :
    (image_m I r H n y).satisfies η ↔
      image_l (I.eval η) (r.eval η) (H.eval η) (n.eval η) (y.eval η) := by
  simp only [image_m, image_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

include hBase in
/-- 类内实数代表、全部根良基性及同一 T/H 的精确值域一起保留。 -/
theorem exists_l (K : source_coding_l hℳ) (I : type_l hℳ B) {ω T H : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hCount : PowerlessRelativeOrdinalCutoff.countable_l B ω I.val)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I.val T H)
    (hUpper : ∀ x, mem_l hℳ x I.val → ∃ p, mem_l hℳ p I.val ∧ mem_l hℳ x p)
    (hNonempty : ∃ d, mem_l hℳ d I.val) :
    ∃ r D A U : type_l hℳ B,
      ∃ hU : ∀ c, mem_l hℳ c U.val → mem_l hℳ c K.omega,
      ∃ R : SecondOrderModel.set_l ℳ,
      setRel_l K ⟨U.val, hU⟩ R ∧
      SecondOrderFunctionObjects.injective_l hℳ r.val ∧
      PowerlessRelativeMembershipCollapse.coded_spec_l K I r D A R ∧
      ∃ hWF : ∀ n, SecondOrderDomain.wf_l R n,
        (∀ n y, SecondOrderCollapseGraph.field_l R n →
          (image_l I.val r.val H (numberCode_l K n).val y ↔
            mk_l hℳ ⟨R, n, hWF n⟩ = y)) ∧
        ∀ y, mem_l hℳ y T ↔ ∃ n, SecondOrderCollapseGraph.field_l R n ∧
          y = mk_l hℳ ⟨R, n, hWF n⟩ := by
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  rw [hωEq] at hCount
  obtain ⟨r, hr, hR, hInjective⟩ := hCount
  let r' : type_l hℳ B := ⟨r, hr⟩
  obtain ⟨d, hd⟩ := hNonempty
  let d' : type_l hℳ B := ⟨d,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase I.property hd⟩
  obtain ⟨D, A, U, hU, R, hTrace, hCoded⟩ :=
    PowerlessRelativeMembershipCollapse.coded_l (hBase := hBase) K I r' d'
      hR hInjective hd hUpper
  have hData := hCoded
  rcases hData with ⟨hSub, _, hMapD, hOnto, hA, hCode, hWF, hDomain⟩
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := image_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there .here)) (.fvar .here)
  let η : Env 𝒱 [] [.set, .set, .set] :=
    ((Env.empty.pushFree H).pushFree r).pushFree I.val
  have hRead n y : φ.satisfies ((η.pushFree n).pushFree y) ↔ image_l I.val r H n y :=
    image_formula_l ((η.pushFree n).pushFree y) _ _ _ _ _
  have hUnique n y z (hy : φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree y))
      (hz : φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree z)) : y = z := by
    obtain ⟨x, _, hxn, hxy⟩ := (hRead _ _).mp hy
    obtain ⟨a, _, han, haz⟩ := (hRead _ _).mp hz
    have hxa := hInjective x a _ hxn han
    exact SecondOrderFunctionProperties.value_unique_l hℳ hH.2.1 hxy (hxa.symm ▸ haz)
  have hEdge n m : SecondOrderPairing.relation_l R n m ↔ ∃ y z,
      φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree y) ∧
      φ.satisfies ((η.pushFree (numberCode_l K m).val).pushFree z) ∧ mem_l hℳ y z := by
    rw [hCode, hA]
    constructor
    · rintro ⟨x, hx, a, ha, hxn, ham, hxa⟩
      obtain ⟨y, hy, _⟩ := hH.2.1.2 x hx
      obtain ⟨z, hz, _⟩ := hH.2.1.2 a ha
      exact ⟨y, z, (hRead _ _).mpr ⟨x, hx, hxn, hy.2⟩,
        (hRead _ _).mpr ⟨a, ha, ham, hz.2⟩,
        (hH.2.2.2.2.2 x a y z hx ha hy.2 hz.2).mp hxa⟩
    · rintro ⟨y, z, hy, hz, hyz⟩
      obtain ⟨x, hx, hxn, hxy⟩ := (hRead _ _).mp hy
      obtain ⟨a, ha, ham, haz⟩ := (hRead _ _).mp hz
      exact ⟨x, hx, a, ha, hxn, ham,
        (hH.2.2.2.2.2 x a y z hx ha hxy haz).mpr hyz⟩
  have hClosed n y (hy : φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree y))
      z (hzy : mem_l hℳ z y) : ∃ m,
      φ.satisfies ((η.pushFree (numberCode_l K m).val).pushFree z) := by
    obtain ⟨x, hx, _, hxy⟩ := (hRead _ _).mp hy
    obtain ⟨a, ha, _, haz⟩ := (hH.2.2.2.1 x y hx hxy z).mp hzy
    obtain ⟨k, hk, _⟩ := hMapD.2 a ha
    obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨k, hSub k hk.1⟩
    have hm' : (numberCode_l K m).val = k := congrArg Subtype.val hm
    exact ⟨m, (hRead _ _).mpr ⟨a, ha, hm'.symm ▸ hk.2, haz⟩⟩
  have hRoot n y (hy : image_l I.val r H (numberCode_l K n).val y) :
      mk_l hℳ ⟨R, n, hWF n⟩ = y :=
    PowerlessBMSClassCollapse.agrees_l K φ η R hWF hUnique hEdge hClosed n y
      ((hRead _ _).mpr hy)
  have hRootRead n y (hn : SecondOrderCollapseGraph.field_l R n) :
      image_l I.val r H (numberCode_l K n).val y ↔ mk_l hℳ ⟨R, n, hWF n⟩ = y := by
    constructor
    · exact hRoot n y
    · intro hy
      obtain ⟨x, hx, hxn⟩ := hOnto _ ((hDomain _).mpr ⟨n, hn, rfl⟩)
      obtain ⟨z, hz, _⟩ := hH.2.1.2 x hx
      have hzy : z = y := (hRoot n z ⟨x, hx, hxn, hz.2⟩).symm.trans hy
      exact ⟨x, hx, hxn, hzy ▸ hz.2⟩
  refine ⟨r', D, A, U, hU, R, hTrace, hInjective, hCoded, hWF, hRootRead, ?_⟩
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := hH.2.2.1 y hy
    obtain ⟨k, hk, _⟩ := hMapD.2 x hx
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨k, hSub k hk.1⟩
    have hn' : (numberCode_l K n).val = k := congrArg Subtype.val hn
    obtain ⟨m, hm, hnm⟩ := (hDomain _).mp (hn'.symm ▸ hk.1)
    have hEq : n = m := numberCode_injective_l K (Subtype.ext hnm)
    exact ⟨n, hEq.symm ▸ hm, (hRoot n y ⟨x, hx, hn'.symm ▸ hk.2, hxy⟩).symm⟩
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨x, hx, hxn⟩ := hOnto _ ((hDomain _).mpr ⟨n, hn, rfl⟩)
    obtain ⟨y, hy, _⟩ := hH.2.1.2 x hx
    exact (hRoot n y ⟨x, hx, hxn, hy.2⟩).symm ▸ hy.1

#print axioms image_delta_m
#print axioms image_formula_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapsePresentation
