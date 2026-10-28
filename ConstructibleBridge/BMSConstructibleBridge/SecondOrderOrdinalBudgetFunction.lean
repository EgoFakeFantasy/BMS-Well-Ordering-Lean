import BMSConstructibleBridge.SecondOrderOrdinalBudgetFinite
import BMSConstructibleBridge.SecondOrderRootOrdinalRelation
import BMSConstructibleBridge.SecondOrderRootedNumericFunction

/-! # 规范指标到预算尾的实际 raw 集合函数

先以最小内部数代表实际母根 A 的每个成员，再把该代表的固定有限尾 k
通过 MixedImage 收集成真正 raw 函数。根选择集合及值域通过原二阶理解与
Graft 构造，故不要求 Collection、Class 预算图或 Type 层代表选择。

指标母集通常取目标序数 α 的后继，从而函数同时在 a<α 与 a=α 上有值。
本文件仅给原商中的函数；其输出序数性、Class 覆盖及层界另消费实际
RootOrdinalRelation 与 BudgetOrder/Finite 的定理，不冒充前史存在性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalBudgetFunction

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderOrdinalBudgetGraph SecondOrderOrdinalBudgetOrder
open SecondOrderOrdinalDoubleTailGraph (root_l root_m root_formula_l)
open SecondOrderQuotient (type_l mk_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 规范域上的真实对象；这里只封装给定证明，不抽取任何代表。 -/
noncomputable def index_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {Q D : set_l ℳ} (hD : SecondOrderRootRepresentatives.spec_l A.real Q D A.root)
    (n : num_l ℳ) (hn : SecondOrderModel.mem_l n D) : type_l hℳ :=
  mk_l hℳ (SecondOrderGraph.child_l hℳ A n ((hD n).mp hn).1)

theorem index_covers_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {Q D : set_l ℳ}
    (hQ : ∀ i j, SecondOrderPairing.relation_l Q i j ↔
      SecondOrderBisimulation.eq_l A.real A.real i j)
    (hD : SecondOrderRootRepresentatives.spec_l A.real Q D A.root)
    (x : type_l hℳ) :
    SecondOrderQuotient.mem_l hℳ x (mk_l hℳ A) ↔
      ∃ n, ∃ hn : SecondOrderModel.mem_l n D, x = index_l hℳ A hD n hn := by
  constructor
  · intro hx
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    obtain ⟨b, hb, hXb⟩ := hx
    obtain ⟨n, hn, hnb⟩ := SecondOrderRootRepresentatives.covers_l hℳ hQ hD hb
    refine ⟨n, hn, (SecondOrderQuotient.eq_iff_l hℳ _ _).mpr ?_⟩
    exact SecondOrderBisimulation.trans_l hℳ X.real A.real A.real X.root b n hXb
      (SecondOrderBisimulation.symm_l hℳ A.real A.real n b hnb)
  · rintro ⟨n, hn, rfl⟩
    exact SecondOrderGraph.child_mem_l hℳ A n ((hD n).mp hn).1

theorem index_injective_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {Q D : set_l ℳ}
    (hQ : ∀ i j, SecondOrderPairing.relation_l Q i j ↔
      SecondOrderBisimulation.eq_l A.real A.real i j)
    (hD : SecondOrderRootRepresentatives.spec_l A.real Q D A.root)
    {n i : num_l ℳ} (hn : SecondOrderModel.mem_l n D) (hi : SecondOrderModel.mem_l i D)
    (hni : index_l hℳ A hD n hn = index_l hℳ A hD i hi) : n = i :=
  SecondOrderRootRepresentatives.injective_l hℳ hQ hD hn hi
    ((SecondOrderQuotient.eq_iff_l hℳ _ _).mp hni)

theorem from_spec_l (hℳ : Theory.Models ℳ theory_m) {S R G : set_l ℳ} {r : num_l ℳ}
    (hS : ∀ a, SecondOrderDomain.wf_l S a) (A : SecondOrderGraph.code_l ℳ)
    {Q D : set_l ℳ}
    (hQ : ∀ i j, SecondOrderPairing.relation_l Q i j ↔
      SecondOrderBisimulation.eq_l A.real A.real i j)
    (hD : SecondOrderRootRepresentatives.spec_l A.real Q D A.root)
    (hRel : SecondOrderRootOrdinalRelation.spec_l A.real Q D R)
    (hG : spec_l S r R G) (k : num_l ℳ) :
    ∃ Y F : type_l hℳ,
      SecondOrderFunctionObjects.map_l hℳ F (mk_l hℳ A) Y ∧
      ∀ x y, SecondOrderFunctionObjects.value_l hℳ F x y ↔
        ∃ n, ∃ hn : SecondOrderModel.mem_l n D, x = index_l hℳ A hD n hn ∧
          y = tail_l hℳ hG hS (SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hD hRel) n k := by
  let hR := SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hD hRel
  have hGWf := SecondOrderOrdinalBudgetGraph.wf_l hℳ hG hS hR
  let φ : Formula signature_m [] [.num, .num, .set] := .existsE .num <| .conj
    (.rel .mem (.cons (.bvar .here) (.cons (.fvar (.there (.there .here))) .nil)))
    (root_m (.bvar .here) (.fvar (.there .here)) (.fvar .here))
  obtain ⟨P, hP⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree D).pushFree k)
  have hPRead (m : num_l ℳ) : SecondOrderModel.mem_l m P ↔
      ∃ n, SecondOrderModel.mem_l n D ∧ root_l n k = m := by
    refine (hP m).trans ?_
    simp only [φ, Formula.satisfies, root_formula_l, Term.eval]
    rfl
  obtain ⟨Y, hY⟩ := SecondOrderGraftSemantics.exists_l hℳ G P (fun m _ => hGWf m)
  have hRange (n : num_l ℳ) (hn : SecondOrderModel.mem_l n D) :
      SecondOrderQuotient.mem_l hℳ (tail_l hℳ hG hS hR n k) (mk_l hℳ Y) :=
    (hY (code_l hℳ hG hS n (hR n) k)).mpr
      ⟨root_l n k, (hPRead _).mpr ⟨n, hn, rfl⟩, SecondOrderBisimulation.refl_l hℳ G _⟩
  let ψ : Formula signature_m [] [.num, .num, .num, .set] := .conj
    (.rel .mem (.cons (.fvar .here) (.cons (.fvar (.there (.there (.there .here)))) .nil)))
    (root_m (.fvar .here) (.fvar (.there (.there .here))) (.fvar (.there .here)))
  obtain ⟨E, hE⟩ := SecondOrderRelations.comprehension_l hℳ ψ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree D).pushFree k)
  have hERead (n m : num_l ℳ) : SecondOrderPairing.relation_l E n m ↔
      SecondOrderModel.mem_l n D ∧ root_l n k = m := by
    refine (hE n m).trans ?_
    simp only [ψ, Formula.satisfies, root_formula_l, Term.eval]
    rfl
  have hRoots (n m : num_l ℳ) (h : SecondOrderPairing.relation_l E n m) :
      SecondOrderDomain.wf_l A.real n ∧ SecondOrderDomain.wf_l G m :=
    ⟨SecondOrderDomain.child_l hℳ A.real A.root n A.wf
      ((hD n).mp ((hERead n m).mp h).1).1, hGWf m⟩
  obtain ⟨F, hF⟩ := SecondOrderMixedImage.exists_l hℳ A.real G E hRoots
  have hGraph (p : type_l hℳ) : SecondOrderQuotient.mem_l hℳ p F ↔
      ∃ n, ∃ hn : SecondOrderModel.mem_l n D, SecondOrderPairObjects.ordered_l hℳ
        (index_l hℳ A hD n hn) (tail_l hℳ hG hS hR n k) p := by
    refine (hF p).trans ⟨?_, ?_⟩
    · rintro ⟨n, m, hnm, hp⟩
      obtain ⟨hn, rfl⟩ := (hERead n m).mp hnm
      exact ⟨n, hn, hp⟩
    · rintro ⟨n, hn, hp⟩
      exact ⟨n, root_l n k, (hERead n _).mpr ⟨hn, rfl⟩, hp⟩
  have hValue (x y : type_l hℳ) : SecondOrderFunctionObjects.value_l hℳ F x y ↔
      ∃ n, ∃ hn : SecondOrderModel.mem_l n D, x = index_l hℳ A hD n hn ∧
        y = tail_l hℳ hG hS hR n k := by
    constructor
    · rintro ⟨p, hp, hxy⟩
      obtain ⟨n, hn, hnp⟩ := (hGraph p).mp hp
      exact ⟨n, hn, (SecondOrderPairObjects.ordered_eq_l hℳ hxy hnp).mp rfl⟩
    · rintro ⟨n, hn, rfl, rfl⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ
        (index_l hℳ A hD n hn) (tail_l hℳ hG hS hR n k)
      exact ⟨p, (hGraph p).mpr ⟨n, hn, hp⟩, hp⟩
  refine ⟨mk_l hℳ Y, F, ⟨?_, ?_⟩, hValue⟩
  · intro p hp
    obtain ⟨n, hn, hnp⟩ := (hGraph p).mp hp
    exact ⟨index_l hℳ A hD n hn, tail_l hℳ hG hS hR n k,
      (index_covers_l hℳ A hQ hD _).mpr ⟨n, hn, rfl⟩, hRange n hn, hnp⟩
  · intro x hx
    obtain ⟨n, hn, hxn⟩ := (index_covers_l hℳ A hQ hD x).mp hx
    refine ⟨tail_l hℳ hG hS hR n k,
      ⟨hRange n hn, (hValue x _).mpr ⟨n, hn, hxn, rfl⟩⟩, ?_⟩
    rintro y ⟨_, hy⟩
    obtain ⟨i, hi, hxi, hyi⟩ := (hValue x y).mp hy
    have hin : i = n := index_injective_l hℳ A hQ hD hi hn (hxi.symm.trans hxn)
    subst i
    exact hyi

/-- 原理解得到全部规范数码及预算图，再构造实际函数；所有见证均留在 Prop。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) (S : set_l ℳ) (r : num_l ℳ)
    (hS : ∀ a, SecondOrderDomain.wf_l S a) (A : SecondOrderGraph.code_l ℳ) (k : num_l ℳ) :
    ∃ Q D R G : set_l ℳ,
      ∃ hQ : ∀ i j, SecondOrderPairing.relation_l Q i j ↔ SecondOrderBisimulation.eq_l A.real A.real i j,
      ∃ hD : SecondOrderRootRepresentatives.spec_l A.real Q D A.root,
      ∃ hRel : SecondOrderRootOrdinalRelation.spec_l A.real Q D R,
      ∃ hG : spec_l S r R G, ∃ Y F : type_l hℳ,
        SecondOrderFunctionObjects.map_l hℳ F (mk_l hℳ A) Y ∧
        ∀ x y, SecondOrderFunctionObjects.value_l hℳ F x y ↔
          ∃ n, ∃ hn : SecondOrderModel.mem_l n D, x = index_l hℳ A hD n hn ∧
            y = tail_l hℳ hG hS (SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hD hRel) n k := by
  obtain ⟨Q, hQ⟩ := SecondOrderBisimulation.maximum_l hℳ A.real A.real
  obtain ⟨D, hD, _⟩ := SecondOrderRootRepresentatives.exists_l hℳ A.real Q A.root
  obtain ⟨R, hRel, _⟩ := SecondOrderRootOrdinalRelation.exists_l hℳ A.real Q D
  obtain ⟨G, hG⟩ := SecondOrderOrdinalBudgetGraph.exists_l hℳ S r R
  obtain ⟨Y, F, hMap, hRead⟩ := from_spec_l hℳ hS A hQ hD hRel hG k
  exact ⟨Q, D, R, G, hQ, hD, hRel, hG, Y, F, hMap, hRead⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalBudgetFunction
