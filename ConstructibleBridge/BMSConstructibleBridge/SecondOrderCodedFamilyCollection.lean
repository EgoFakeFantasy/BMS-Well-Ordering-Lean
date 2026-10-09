import BMSConstructibleBridge.SecondOrderPredecessorTaggedGraph
import BMSConstructibleBridge.SecondOrderPairSet

/-! # 已编码良基图族的精确收集

对象语言是原双排序算术签名，背景是原 Z₂。族 H 和索引集 I 都是模型内
已有实数；每个选中行的零根满足原内部良基域。标签图把所有这些行放进
互不相交副本，拼接新根得到恰好由整行对象组成的集合，而非各行成员之并。
构造不选择外部行族，也不调用 Collection。输出目前只保证属于环境商，
尚不证明它属于相对构造子域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCodedFamilyCollection

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l value_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def rows_wf_l (H I : set_l ℳ) : Prop :=
  ∀ i, mem_l i I → ∀ Y, SecondOrderSections.spec_l H i Y →
    SecondOrderDomain.wf_l Y (zero_l ℳ)

def member_l (H I : set_l ℳ) (D : SecondOrderGraph.code_l ℳ) : Prop :=
  ∃ i, ∃ Y : SecondOrderGraph.code_l ℳ, mem_l i I ∧
    SecondOrderSections.spec_l H i Y.real ∧ Y.root = zero_l ℳ ∧ SecondOrderGraph.eq_l D Y

private def zero_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

/-- 索引过滤关系在每个第二坐标上都读取同一个 I，不要求索引有共同序数界。 -/
private theorem index_l (hℳ : Theory.Models ℳ theory_m) (I : set_l ℳ) :
    ∃ R : set_l ℳ, ∀ i n, relation_l R i n ↔ mem_l i I := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .rel .mem (.cons (.fvar .here) (.cons (.fvar (.there (.there .here))) .nil))
  obtain ⟨R, hR⟩ := SecondOrderRelations.comprehension_l hℳ φ rfl (Env.empty.pushFree I)
  exact ⟨R, hR⟩

private theorem roots_l (hℳ : Theory.Models ℳ theory_m) (I : set_l ℳ) :
    ∃ P : set_l ℳ, ∀ c, mem_l c P ↔ ∃ i, mem_l i I ∧ value_l i (zero_l ℳ) = c := by
  let φ : Formula signature_m [] [.num, .set] :=
    .existsE .num <| .conj
      (.rel .mem (.cons (.bvar .here) (.cons (.fvar (.there .here)) .nil)))
      (PrimitiveFormulas.pair_m (.bvar .here) zero_m (.fvar .here))
  obtain ⟨P, hP⟩ := comprehension_l hℳ φ (pure_language_m _ rfl) (Env.empty.pushFree I)
  refine ⟨P, fun c => (hP c).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderPairing.formula_l, zero_m, Term.eval, Arguments.eval]
  rfl

/-- 任意选中内部索引均保留整行见证；完整成员规格覆盖任意跨图对象。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) (H I : set_l ℳ) (hRows : rows_wf_l H I) :
    ∃ C : SecondOrderGraph.code_l ℳ, C.root = zero_l ℳ ∧
      ∀ D, SecondOrderGraph.mem_l D C ↔ member_l H I D := by
  obtain ⟨R, hR⟩ := index_l hℳ I
  obtain ⟨G, hG, _⟩ := SecondOrderPredecessorTaggedGraph.exists_l hℳ R H (zero_l ℳ)
  obtain ⟨P, hP⟩ := roots_l hℳ I
  have hRoots c (hc : mem_l c P) : SecondOrderDomain.wf_l G c := by
    obtain ⟨i, hi, rfl⟩ := (hP c).mp hc
    obtain ⟨Y, hY⟩ := SecondOrderSections.exists_l hℳ H i
    exact SecondOrderPredecessorTaggedGraph.wf_l hℳ hG ((hR i _).mpr hi) hY
      (hRows i hi Y hY)
  obtain ⟨W, hW⟩ := SecondOrderGraft.exists_l hℳ G P
  let C := SecondOrderGraftSemantics.code_l hℳ G P W hW hRoots
  have hC D := SecondOrderGraftSemantics.mem_l hℳ G P W hW hRoots D
  refine ⟨C, rfl, fun D => (hC D).trans ?_⟩
  constructor
  · rintro ⟨c, hc, hDc⟩
    obtain ⟨i, hi, rfl⟩ := (hP c).mp hc
    obtain ⟨Y, hY⟩ := SecondOrderSections.exists_l hℳ H i
    have hTag := SecondOrderPairSet.tag_eq_l hℳ i Y G
      (SecondOrderPredecessorTaggedGraph.fiber_l hℳ hG ((hR i _).mpr hi) hY) (zero_l ℳ)
    refine ⟨i, ⟨Y, zero_l ℳ, hRows i hi Y hY⟩, hi, hY, rfl, ?_⟩
    exact SecondOrderBisimulation.trans_l hℳ D.real G Y D.root _ (zero_l ℳ) hDc
      (SecondOrderBisimulation.symm_l hℳ _ _ _ _ hTag)
  · rintro ⟨i, Y, hi, hY, hZero, hDY⟩
    have hTag := SecondOrderPairSet.tag_eq_l hℳ i Y.real G
      (SecondOrderPredecessorTaggedGraph.fiber_l hℳ hG ((hR i _).mpr hi) hY) (zero_l ℳ)
    refine ⟨value_l i (zero_l ℳ), (hP _).mpr ⟨i, hi, rfl⟩, ?_⟩
    exact SecondOrderBisimulation.trans_l hℳ D.real Y.real G D.root (zero_l ℳ) _
      (hZero ▸ hDY) hTag

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {H I : set_l ℳ}
    {C D : SecondOrderGraph.code_l ℳ}
    (hC : ∀ A, SecondOrderGraph.mem_l A C ↔ member_l H I A)
    (hD : ∀ A, SecondOrderGraph.mem_l A D ↔ member_l H I A) : SecondOrderGraph.eq_l C D :=
  (SecondOrderGraph.ext_l hℳ C D).mpr (fun A => (hC A).trans (hD A).symm)

/-- 行的证明证书不影响收集集；不固定商元素的全局代码代表。 -/
theorem row_mem_l (hℳ : Theory.Models ℳ theory_m) {H I : set_l ℳ}
    {C : SecondOrderGraph.code_l ℳ}
    (hC : ∀ A, SecondOrderGraph.mem_l A C ↔ member_l H I A)
    {i : num_l ℳ} (hi : mem_l i I) {Y : set_l ℳ} (hY : SecondOrderSections.spec_l H i Y)
    (hWf : SecondOrderDomain.wf_l Y (zero_l ℳ)) :
    SecondOrderGraph.mem_l ⟨Y, zero_l ℳ, hWf⟩ C :=
  (hC _).mpr ⟨i, ⟨Y, zero_l ℳ, hWf⟩, hi, hY, rfl,
    SecondOrderGraph.refl_l hℳ _⟩

#print axioms exists_l
#print axioms unique_l
#print axioms row_mem_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCodedFamilyCollection
