import BMSConstructibleBridge.TextbookEDomainStage
import ConstructibleUniverse.SetTheory.ZFC.Constructible.DefZFCollapse

/-!
# textbook E 单步操作在局部可构造层中的语义

本模块逐个处理 E 递归步骤使用的集合操作。所有公开定理都以原始
`SatisfiesIn (LStageZF θ)` 陈述，从而可直接送入通用局部递归解码器。
-/

open Set

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open Constructible.FiniteSequenceZF

noncomputable section

/-- 原始受限语义下，全称量词展开为对层内元素的量化。 -/
theorem satisfiesIn_all_stage_iff_l
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (assignment : Tuple ZFSet.{u} n) :
    Constructible.Model.SatisfiesIn M (FOFormula.all formula) assignment ↔
      ∀ value : ZFSet.{u}, value ∈ M →
        Constructible.Model.SatisfiesIn M formula
          (snoc assignment value) := by
  classical
  simp [FOFormula.all, Constructible.Model.SatisfiesIn]

/-- 层内 `Delta0` 有序对公式具有外部 Kuratowski 对语义。 -/
theorem satisfiesIn_kuratowskiPairEqAt_stage_iff_l
    {θ : Ordinal.{u}} {n : Nat} (output left right : Fin n)
    (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Delta0Formula.kuratowskiPairEqAt output left right).toFO
        assignment ↔
      assignment output = ZFSet.pair (assignment left) (assignment right) := by
  exact (Constructible.Model.satisfiesIn_delta0_iff
    (LStageZF_isTransitive θ)
    (Delta0Formula.kuratowskiPairEqAt output left right)
    assignment hAssignment).trans (by
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt])

/-- 层内 `Delta0` 后继公式具有外部 von Neumann 后继语义。 -/
theorem satisfiesIn_successorAt_stage_iff_l
    {θ : Ordinal.{u}} {n : Nat} (output input : Fin n)
    (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Delta0Formula.successorAt output input).toFO assignment ↔
      assignment output = insert (assignment input) (assignment input) := by
  exact (Constructible.Model.satisfiesIn_delta0_iff
    (LStageZF_isTransitive θ)
    (Delta0Formula.successorAt output input)
    assignment hAssignment).trans (by
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt])

/-- 三元公式放到任意三个坐标后只重排赋值。 -/
theorem satisfiesIn_formula3At_stage_iff_l
    (M : Set ZFSet.{u}) (formula : FOFormula 3)
    {n : Nat} (x y z : Fin n) (assignment : Tuple ZFSet.{u} n) :
    Constructible.Model.SatisfiesIn M
        (Constructible.TextbookEFormula.formula3At formula x y z)
        assignment ↔
      Constructible.Model.SatisfiesIn M formula
        ![assignment x, assignment y, assignment z] := by
  rw [Constructible.TextbookEFormula.formula3At,
    Constructible.Model.satisfiesIn_rename]
  have hAssignment : (fun position =>
      assignment (![x, y, z] position)) =
      ![assignment x, assignment y, assignment z] := by
    funext position
    fin_cases position <;> rfl
  rw [hAssignment]

/-- 四元公式放到任意四个坐标后只重排赋值。 -/
theorem satisfiesIn_formula4At_stage_iff_l
    (M : Set ZFSet.{u}) (formula : FOFormula 4)
    {n : Nat} (v w x y : Fin n) (assignment : Tuple ZFSet.{u} n) :
    Constructible.Model.SatisfiesIn M
        (Constructible.TextbookEFormula.formula4At formula v w x y)
        assignment ↔
      Constructible.Model.SatisfiesIn M formula
        ![assignment v, assignment w, assignment x, assignment y] := by
  rw [Constructible.TextbookEFormula.formula4At,
    Constructible.Model.satisfiesIn_rename]
  have hAssignment : (fun position =>
      assignment (![v, w, x, y] position)) =
      ![assignment v, assignment w, assignment x, assignment y] := by
    funext position
    fin_cases position <;> rfl
  rw [hAssignment]

/-- 五元公式放到任意五个坐标后只重排赋值。 -/
theorem satisfiesIn_formula5At_stage_iff_l
    (M : Set ZFSet.{u}) (formula : FOFormula 5)
    {n : Nat} (v w x y z : Fin n) (assignment : Tuple ZFSet.{u} n) :
    Constructible.Model.SatisfiesIn M
        (Constructible.TextbookEFormula.formula5At formula v w x y z)
        assignment ↔
      Constructible.Model.SatisfiesIn M formula
        ![assignment v, assignment w, assignment x,
          assignment y, assignment z] := by
  rw [Constructible.TextbookEFormula.formula5At,
    Constructible.Model.satisfiesIn_rename]
  have hAssignment : (fun position =>
      assignment (![v, w, x, y, z] position)) =
      ![assignment v, assignment w, assignment x,
        assignment y, assignment z] := by
    funext position
    fin_cases position <;> rfl
  rw [hAssignment]

/-- 相对差输出公式在传递层内精确决定外部相对差。 -/
theorem satisfiesIn_relativeDifferenceOutputFormula_stage_iff_l
    {θ : Ordinal.{u}} {space removed output : ZFSet.{u}}
    (hspace : space ∈ LStageZF θ) (_hremoved : removed ∈ LStageZF θ)
    (houtput : output ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookDefFormula.relativeDifferenceOutputFormula
        ![space, removed, output] ↔
      output = Constructible.relativeDifferenceZF space removed := by
  rw [Constructible.TextbookDefFormula.relativeDifferenceOutputFormula]
  rw [satisfiesIn_all_stage_iff_l]
  simp only [Constructible.Model.satisfiesIn_biimp_iff,
    Constructible.Model.SatisfiesIn,
    Constructible.TextbookDefFormula.relativeDifferenceMemberAt]
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    rw [Constructible.mem_relativeDifferenceZF_iff]
    constructor
    · intro hx
      exact (h x ((LStageZF_isTransitive θ).mem_trans hx houtput)).mp hx
    · intro hx
      exact (h x ((LStageZF_isTransitive θ).mem_trans hx.1 hspace)).mpr hx
  · intro houtputEq x _hxStage
    change x ∈ output ↔ x ∈ space ∧ x ∉ removed
    rw [houtputEq, Constructible.mem_relativeDifferenceZF_iff]

/-- 交集输出公式在传递层内精确决定外部交集。 -/
theorem satisfiesIn_intersectionOutputFormula_stage_iff_l
    {θ : Ordinal.{u}} {left right output : ZFSet.{u}}
    (hleft : left ∈ LStageZF θ) (_hright : right ∈ LStageZF θ)
    (houtput : output ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookDefFormula.intersectionOutputFormula
        ![left, right, output] ↔
      output = Constructible.intersectionZF left right := by
  rw [Constructible.TextbookDefFormula.intersectionOutputFormula]
  rw [satisfiesIn_all_stage_iff_l]
  simp only [Constructible.Model.satisfiesIn_biimp_iff,
    Constructible.Model.SatisfiesIn,
    Constructible.TextbookDefFormula.intersectionMemberAt]
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    rw [Constructible.mem_intersectionZF_iff]
    constructor
    · intro hx
      exact (h x ((LStageZF_isTransitive θ).mem_trans hx houtput)).mp hx
    · intro hx
      exact (h x ((LStageZF_isTransitive θ).mem_trans hx.1 hleft)).mpr hx
  · intro houtputEq x _hxStage
    change x ∈ output ↔ x ∈ left ∧ x ∈ right
    rw [houtputEq, Constructible.mem_intersectionZF_iff]

/-- 图值原子在层内保持其外部成员语义。 -/
theorem satisfiesIn_graphValueAt_stage_iff_l
    {θ : Ordinal.{u}} {n : Nat} (graph key value : Fin n)
    (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Constructible.TextbookDefFormula.graphValueAt graph key value)
        assignment ↔
      ZFSet.pair (assignment key) (assignment value) ∈ assignment graph := by
  exact (Constructible.Model.satisfiesIn_delta0_iff
    (LStageZF_isTransitive θ)
    (Constructible.TextbookDefFormula.graphValueDeltaAt graph key value)
    assignment hAssignment).trans
      (Constructible.TextbookDefFormula.satisfies_graphValueAt
        graph key value assignment)

/-- 空集原子在层内保持其外部语义。 -/
theorem satisfiesIn_emptyDeltaAt_stage_iff_l
    {θ : Ordinal.{u}} {n : Nat} (index : Fin n)
    (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Delta0Formula.emptyDeltaAt index).toFO assignment ↔
      assignment index = (∅ : ZFSet.{u}) := by
  exact (Constructible.Model.satisfiesIn_delta0_iff
    (LStageZF_isTransitive θ) (Delta0Formula.emptyDeltaAt index)
    assignment hAssignment).trans (by
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_emptyDeltaAt])

/-- 唯一图值公式在局部层与外部唯一性完全一致。 -/
theorem satisfiesIn_uniqueGraphValueAt_stage_iff_l
    {θ : Ordinal.{u}} {n : Nat} (graph key output : Fin n)
    (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Constructible.TextbookDefFormula.uniqueGraphValueAt
          graph key output) assignment ↔
      Constructible.IsUniqueGraphValue
        (assignment graph) (assignment key) (assignment output) := by
  rw [Constructible.TextbookDefFormula.uniqueGraphValueAt]
  simp only [Constructible.Model.SatisfiesIn]
  rw [satisfiesIn_graphValueAt_stage_iff_l graph key output
    assignment hAssignment, satisfiesIn_all_stage_iff_l]
  simp only [Constructible.Model.satisfiesIn_imp_iff,
    Constructible.Model.SatisfiesIn]
  constructor
  · rintro ⟨hvalue, hunique⟩
    refine ⟨hvalue, ?_⟩
    intro other hother
    have hotherStage : other ∈ LStageZF θ :=
      graphValue_mem_LStageZF_l (hAssignment graph) hother
    have hotherSnoc :
        ZFSet.pair (snoc assignment other key.castSucc)
            (snoc assignment other (Fin.last n)) ∈
          snoc assignment other graph.castSucc := by
      simpa only [snoc_last, snoc_castSucc] using hother
    have hEq := hunique other hotherStage
      ((satisfiesIn_graphValueAt_stage_iff_l
        graph.castSucc key.castSucc (Fin.last n)
        (snoc assignment other) (by
          intro position
          refine Fin.lastCases ?_ (fun earlier => ?_) position
          · simpa using hotherStage
          · simpa using hAssignment earlier)).mpr hotherSnoc)
    simpa only [snoc_last, snoc_castSucc] using hEq
  · rintro ⟨hvalue, hunique⟩
    refine ⟨hvalue, ?_⟩
    intro other hotherStage hotherFormula
    have hotherSnoc := (satisfiesIn_graphValueAt_stage_iff_l
      graph.castSucc key.castSucc (Fin.last n)
      (snoc assignment other) (by
        intro position
        refine Fin.lastCases ?_ (fun earlier => ?_) position
        · simpa using hotherStage
        · simpa using hAssignment earlier)).mp hotherFormula
    have hother : ZFSet.pair (assignment key) other ∈ assignment graph := by
      simpa only [snoc_last, snoc_castSucc] using hotherSnoc
    simpa only [snoc_last, snoc_castSucc] using hunique other hother

/-- “存在唯一图值”在局部层与外部存在唯一值完全一致。 -/
theorem satisfiesIn_hasUniqueGraphValueAt_stage_iff_l
    {θ : Ordinal.{u}} {n : Nat} (graph key : Fin n)
    (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Constructible.TextbookDefFormula.hasUniqueGraphValueAt graph key)
        assignment ↔
      ∃ value : ZFSet.{u}, Constructible.IsUniqueGraphValue
        (assignment graph) (assignment key) value := by
  rw [Constructible.TextbookDefFormula.hasUniqueGraphValueAt]
  simp only [Constructible.Model.SatisfiesIn]
  constructor
  · rintro ⟨value, hvalueStage, hvalue⟩
    refine ⟨value, ?_⟩
    simpa only [snoc_last, snoc_castSucc] using
      (satisfiesIn_uniqueGraphValueAt_stage_iff_l
        graph.castSucc key.castSucc (Fin.last n) (snoc assignment value)
        (by
          intro position
          refine Fin.lastCases ?_ (fun earlier => ?_) position
          · simpa using hvalueStage
          · simpa using hAssignment earlier)).mp hvalue
  · rintro ⟨value, hvalue⟩
    have hvalueStage : value ∈ LStageZF θ :=
      graphValue_mem_LStageZF_l (hAssignment graph) hvalue.1
    refine ⟨value, hvalueStage, ?_⟩
    apply (satisfiesIn_uniqueGraphValueAt_stage_iff_l
      graph.castSucc key.castSucc (Fin.last n) (snoc assignment value)
      (by
        intro position
        refine Fin.lastCases ?_ (fun earlier => ?_) position
        · simpa using hvalueStage
        · simpa using hAssignment earlier)).mpr
    simpa only [snoc_last, snoc_castSucc] using hvalue

/-- 全函数化唯一图查询公式在局部层中精确计算外部查询值。 -/
theorem satisfiesIn_uniqueGraphLookupFormula_stage_iff_l
    {θ : Ordinal.{u}} (_hθ : Order.IsSuccLimit θ)
    {graph key output : ZFSet.{u}}
    (hgraph : graph ∈ LStageZF θ) (hkey : key ∈ LStageZF θ)
    (houtput : output ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookDefFormula.uniqueGraphLookupFormula
        ![graph, key, output] ↔
      output = Constructible.uniqueGraphLookupZF graph key := by
  rw [Constructible.TextbookDefFormula.uniqueGraphLookupFormula]
  rw [Constructible.Model.satisfiesIn_disj_iff]
  simp only [Constructible.Model.SatisfiesIn]
  have hAssignment : ∀ position : Fin 3,
      ![graph, key, output] position ∈ LStageZF θ := by
    intro position
    fin_cases position
    · exact hgraph
    · exact hkey
    · exact houtput
  rw [satisfiesIn_uniqueGraphValueAt_stage_iff_l
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) _ hAssignment,
    satisfiesIn_hasUniqueGraphValueAt_stage_iff_l
      (0 : Fin 3) (1 : Fin 3) _ hAssignment,
    satisfiesIn_emptyDeltaAt_stage_iff_l (2 : Fin 3) _ hAssignment]
  change
    (Constructible.IsUniqueGraphValue graph key output ∨
      ((¬ ∃ value : ZFSet.{u},
          Constructible.IsUniqueGraphValue graph key value) ∧
        output = (∅ : ZFSet.{u}))) ↔
      output = Constructible.uniqueGraphLookupZF graph key
  constructor
  · rintro (hvalue | ⟨hnot, hempty⟩)
    · exact (Constructible.uniqueGraphLookupZF_eq_of_unique
        hvalue.1 hvalue.2).symm
    · have hnotUnique :
          ¬ ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph := by
        simpa only [Constructible.existsUnique_graphValue_iff] using hnot
      rw [hempty,
        Constructible.uniqueGraphLookupZF_eq_empty_of_not_unique hnotUnique]
  · intro houtputEq
    by_cases hunique : ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph
    · rcases hunique with ⟨value, hvalue, hunique⟩
      left
      have hlookup := Constructible.uniqueGraphLookupZF_eq_of_unique
        hvalue hunique
      rw [houtputEq, hlookup]
      exact ⟨hvalue, hunique⟩
    · right
      constructor
      · simpa only [← Constructible.existsUnique_graphValue_iff] using hunique
      · rw [houtputEq,
          Constructible.uniqueGraphLookupZF_eq_empty_of_not_unique hunique]

/-! ## 有限函数空间 -/

/-- “标准有限定义域”公式在局部层中恰好识别自然数码。 -/
theorem satisfiesIn_standardFiniteDomainAt_stage_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {n : Nat} (domain : Fin n)
    (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Constructible.Model.standardFiniteDomainAt domain) assignment ↔
      ∃ k : Nat, assignment domain = natCode k := by
  rw [Constructible.Model.standardFiniteDomainAt]
  simp only [Constructible.Model.SatisfiesIn]
  constructor
  · rintro ⟨omega, homegaStage, homegaFormula, hdomainOmega⟩
    have homega : omega = Ordinal.omega0.toZFSet :=
      by simpa only [snoc_last] using
        (satisfiesIn_standardOmegaAt_stage_iff_l hθ hω (Fin.last n)
        (snoc assignment omega) (by
          intro position
          refine Fin.lastCases ?_ (fun earlier => ?_) position
          · simpa using homegaStage
          · simpa using hAssignment earlier)).mp homegaFormula
    have hdomain : assignment domain ∈ Ordinal.omega0.toZFSet := by
      simpa only [snoc_last, snoc_castSucc, homega] using hdomainOmega
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (assignment domain)).mp hdomain
  · rintro ⟨k, hdomain⟩
    let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
    have homegaStage : omega ∈ LStageZF θ := omega_toZFSet_mem_stage_l hω
    refine ⟨omega, homegaStage, ?_, ?_⟩
    · exact (satisfiesIn_standardOmegaAt_stage_iff_l hθ hω
        (Fin.last n) (snoc assignment omega) (by
          intro position
          refine Fin.lastCases ?_ (fun earlier => ?_) position
          · simpa using homegaStage
          · simpa using hAssignment earlier)).mpr (by simp [omega])
    · simp only [snoc_last, snoc_castSucc, hdomain, omega]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode k)).mpr ⟨k, rfl⟩

/-- 函数图的 `Delta0` 原子在局部层中保持外部函数语义。 -/
theorem satisfiesIn_isFunctionAt_stage_iff_l
    {θ : Ordinal.{u}} {n : Nat} (graph domain codomain : Fin n)
    (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Constructible.TextbookDefFormula.isFunctionAt
          graph domain codomain) assignment ↔
      ZFSet.IsFunc (assignment domain) (assignment codomain)
        (assignment graph) := by
  exact (Constructible.Model.satisfiesIn_delta0_iff
    (LStageZF_isTransitive θ)
    (Constructible.TextbookDefFormula.isFunctionDeltaAt
      graph domain codomain) assignment hAssignment).trans
      (Constructible.TextbookDefFormula.satisfies_isFunctionAt
        graph domain codomain assignment)

/-- 固定自然数定义域的函数空间公式在局部层中决定真实函数空间。 -/
theorem satisfiesIn_functionSpaceGraph_stage_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (n : Nat)
    {codomain space : ZFSet.{u}}
    (hcodomain : codomain ∈ LStageZF θ)
    (hspace : space ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookDefFormula.functionSpaceGraph
        ![natCode n, codomain, space] ↔
      space = ZFSet.funs (natCode n) codomain := by
  rw [Constructible.TextbookDefFormula.functionSpaceGraph,
    Constructible.TextbookDefFormula.functionSpaceAt,
    satisfiesIn_all_stage_iff_l]
  simp only [Constructible.Model.satisfiesIn_biimp_iff,
    Constructible.Model.SatisfiesIn]
  have hcode : (natCode n : ZFSet.{u}) ∈ LStageZF θ :=
    natCode_mem_stage_l hω n
  have hbase : ∀ position : Fin 3,
      ![natCode n, codomain, space] position ∈ LStageZF θ := by
    intro position
    fin_cases position
    · exact hcode
    · exact hcodomain
    · exact hspace
  have hFunction (graph : ZFSet.{u}) (hgraph : graph ∈ LStageZF θ) :=
    satisfiesIn_isFunctionAt_stage_iff_l
      (Fin.last 3) (0 : Fin 3).castSucc (1 : Fin 3).castSucc
      (snoc ![natCode n, codomain, space] graph) (by
        intro position
        refine Fin.lastCases ?_ (fun earlier => ?_) position
        · change graph ∈ LStageZF θ
          exact hgraph
        · simpa using hbase earlier)
  simp only [snoc_last, snoc_castSucc] at hFunction
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    rw [ZFSet.mem_funs]
    constructor
    · intro hgraphSpace
      have hgraphStage : graph ∈ LStageZF θ :=
        (LStageZF_isTransitive θ).mem_trans hgraphSpace hspace
      exact (hFunction graph hgraphStage).mp
        ((h graph hgraphStage).mp hgraphSpace)
    · intro hfunc
      have hgraphTuple : graph ∈ textbookTupleSpace codomain n :=
        mem_textbookTupleSpace_iff.mpr hfunc
      have htupleSpace : textbookTupleSpace codomain n ∈ LStageZF θ :=
        textbookTupleSpace_mem_LStageZF_l hθ hcodomain n
      have hgraphStage : graph ∈ LStageZF θ :=
        (LStageZF_isTransitive θ).mem_trans hgraphTuple htupleSpace
      exact (h graph hgraphStage).mpr
        ((hFunction graph hgraphStage).mpr hfunc)
  · intro hspaceEq graph _hgraphStage
    subst space
    change (graph ∈ ZFSet.funs (natCode n) codomain ↔ _)
    rw [ZFSet.mem_funs]
    simpa using
      (hFunction graph _hgraphStage).symm

/-- 带有限性保护的函数空间公式具有同一局部语义。 -/
theorem satisfiesIn_finiteFunctionSpaceGraph_stage_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (n : Nat)
    {codomain space : ZFSet.{u}}
    (hcodomain : codomain ∈ LStageZF θ)
    (hspace : space ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.Model.finiteFunctionSpaceGraph
        ![natCode n, codomain, space] ↔
      space = ZFSet.funs (natCode n) codomain := by
  rw [Constructible.Model.finiteFunctionSpaceGraph]
  simp only [Constructible.Model.SatisfiesIn]
  have hcode : (natCode n : ZFSet.{u}) ∈ LStageZF θ :=
    natCode_mem_stage_l hω n
  have hAssignment : ∀ position : Fin 3,
      ![natCode n, codomain, space] position ∈ LStageZF θ := by
    intro position
    fin_cases position
    · exact hcode
    · exact hcodomain
    · exact hspace
  constructor
  · rintro ⟨_hfinite, hfunctionSpace⟩
    exact (satisfiesIn_functionSpaceGraph_stage_natCode_iff_l
      hθ hω n hcodomain hspace).mp hfunctionSpace
  · intro hspaceEq
    refine ⟨(satisfiesIn_standardFiniteDomainAt_stage_iff_l
      hθ hω (0 : Fin 3) _ hAssignment).mpr ⟨n, rfl⟩, ?_⟩
    exact (satisfiesIn_functionSpaceGraph_stage_natCode_iff_l
      hθ hω n hcodomain hspace).mpr hspaceEq

/-! ## 存在量词投影 -/

/-- 投影成员的 `Delta0` 核心在局部层中保持外部语义。 -/
theorem satisfiesIn_existsProjMemberDeltaAt_stage_iff_l
    {θ : Ordinal.{u}} {n : Nat} (a arity relation graph : Fin n)
    (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Constructible.TextbookDefFormula.existsProjMemberDeltaAt
          a arity relation graph).toFO assignment ↔
      (∃ index : ZFSet.{u}, index ∈ assignment arity) ∧
        ZFSet.IsFunc (assignment arity) (assignment a) (assignment graph) ∧
          ∃ value : ZFSet.{u}, value ∈ assignment a ∧
            insert (ZFSet.pair (assignment arity) value)
                (assignment graph) ∈ assignment relation := by
  exact (Constructible.Model.satisfiesIn_delta0_iff
    (LStageZF_isTransitive θ)
    (Constructible.TextbookDefFormula.existsProjMemberDeltaAt
      a arity relation graph) assignment hAssignment).trans (by
        rw [Delta0Formula.satisfies_toFO,
          Constructible.TextbookDefFormula.satisfies_existsProjMemberDeltaAt])

/-- 投影输出的逐元素条件在标准自然数码处具有精确语义。 -/
theorem satisfiesIn_existsProjOutputMemberCondition_stage_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (n : Nat)
    {a relation output graph : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hrelation : relation ∈ LStageZF θ)
    (houtput : output ∈ LStageZF θ) (hgraph : graph ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookDefFormula.existsProjOutputMemberCondition
        ![a, natCode n, relation, output, graph] ↔
      graph ∈ Constructible.textbookExistsProjCodeZF a (natCode n) relation := by
  rw [Constructible.TextbookDefFormula.existsProjOutputMemberCondition]
  simp only [Constructible.Model.SatisfiesIn]
  have hcode : (natCode n : ZFSet.{u}) ∈ LStageZF θ :=
    natCode_mem_stage_l hω n
  have hAssignment : ∀ position : Fin 5,
      ![a, natCode n, relation, output, graph] position ∈ LStageZF θ := by
    intro position
    fin_cases position
    · exact ha
    · exact hcode
    · exact hrelation
    · exact houtput
    · exact hgraph
  constructor
  · rintro ⟨_hfinite, hmember⟩
    apply Constructible.mem_textbookExistsProjCodeZF_iff.mpr
    refine ⟨⟨n, rfl⟩, ?_⟩
    exact (satisfiesIn_existsProjMemberDeltaAt_stage_iff_l
      (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (Fin.last 4)
      ![a, natCode n, relation, output, graph] hAssignment).mp hmember
  · intro hgraphResult
    have hcomponents :=
      Constructible.mem_textbookExistsProjCodeZF_iff.mp hgraphResult
    refine ⟨(satisfiesIn_standardFiniteDomainAt_stage_iff_l
      hθ hω (1 : Fin 5) _ hAssignment).mpr ⟨n, rfl⟩, ?_⟩
    exact (satisfiesIn_existsProjMemberDeltaAt_stage_iff_l
      (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (Fin.last 4)
      ![a, natCode n, relation, output, graph] hAssignment).mpr
        hcomponents.2

/-- 存在量词投影输出公式在局部层中唯一决定真实投影集合。 -/
theorem satisfiesIn_existsProjOutputFormula_stage_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (n : Nat)
    {a relation output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hrelation : relation ∈ LStageZF θ)
    (houtput : output ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookDefFormula.existsProjOutputFormula
        ![a, natCode n, relation, output] ↔
      output = Constructible.textbookExistsProjCodeZF a (natCode n) relation := by
  rw [Constructible.TextbookDefFormula.existsProjOutputFormula,
    satisfiesIn_all_stage_iff_l]
  simp only [Constructible.Model.satisfiesIn_biimp_iff,
    Constructible.Model.SatisfiesIn]
  have hcode : (natCode n : ZFSet.{u}) ∈ LStageZF θ :=
    natCode_mem_stage_l hω n
  have hbase : ∀ position : Fin 4,
      ![a, natCode n, relation, output] position ∈ LStageZF θ := by
    intro position
    fin_cases position
    · exact ha
    · exact hcode
    · exact hrelation
    · exact houtput
  have hcondition (graph : ZFSet.{u}) (hgraph : graph ∈ LStageZF θ) :
      Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          Constructible.TextbookDefFormula.existsProjOutputMemberCondition
          (snoc ![a, natCode n, relation, output] graph) ↔
        graph ∈ Constructible.textbookExistsProjCodeZF
          a (natCode n) relation := by
    have hassign : snoc ![a, natCode n, relation, output] graph =
        ![a, natCode n, relation, output, graph] := by
      funext position
      fin_cases position <;> rfl
    rw [hassign]
    exact satisfiesIn_existsProjOutputMemberCondition_stage_natCode_iff_l
      hθ hω n ha hrelation houtput hgraph
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    constructor
    · intro hgraphOutput
      have hgraphStage : graph ∈ LStageZF θ :=
        (LStageZF_isTransitive θ).mem_trans hgraphOutput houtput
      exact (hcondition graph hgraphStage).mp
        ((h graph hgraphStage).mp hgraphOutput)
    · intro hgraphResult
      have hresultStage :
          Constructible.textbookExistsProjCodeZF a (natCode n) relation ∈
            LStageZF θ := by
        rw [Constructible.textbookExistsProjCodeZF_natCode]
        exact textbookExistsProjZF_mem_LStageZF_l hθ ha hrelation n
      have hgraphStage : graph ∈ LStageZF θ :=
        (LStageZF_isTransitive θ).mem_trans hgraphResult hresultStage
      exact (h graph hgraphStage).mpr
        ((hcondition graph hgraphStage).mpr hgraphResult)
  · intro houtputEq
    subst output
    intro graph hgraphStage
    change graph ∈ Constructible.textbookExistsProjCodeZF a (natCode n) relation ↔
      Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookDefFormula.existsProjOutputMemberCondition
        (snoc ![a, natCode n, relation,
          Constructible.textbookExistsProjCodeZF a (natCode n) relation] graph)
    exact (hcondition graph hgraphStage).symm

/-! ## 原子成员与相等关系 -/

/-- 原子成员分支的 `Delta0` 核在传递层内保持其外部语义。 -/
theorem satisfiesIn_dInMemberDeltaAt_stage_iff_l
    {θ : Ordinal.{u}} {n : Nat}
    (a arity left right graph : Fin n)
    (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Constructible.TextbookDefFormula.dInMemberDeltaAt
          a arity left right graph).toFO assignment ↔
      assignment left ∈ assignment arity ∧
        assignment right ∈ assignment arity ∧
          ZFSet.IsFunc (assignment arity) (assignment a) (assignment graph) ∧
            ∃ x : ZFSet.{u}, x ∈ assignment a ∧
              ∃ y : ZFSet.{u}, y ∈ assignment a ∧
                ZFSet.pair (assignment left) x ∈ assignment graph ∧
                  ZFSet.pair (assignment right) y ∈ assignment graph ∧ x ∈ y := by
  exact (Constructible.Model.satisfiesIn_delta0_iff
    (LStageZF_isTransitive θ)
    (Constructible.TextbookDefFormula.dInMemberDeltaAt
      a arity left right graph) assignment hAssignment).trans (by
        rw [Delta0Formula.satisfies_toFO,
          Constructible.TextbookDefFormula.satisfies_dInMemberDeltaAt])

/-- 原子相等分支的 `Delta0` 核在传递层内保持其外部语义。 -/
theorem satisfiesIn_dEqMemberDeltaAt_stage_iff_l
    {θ : Ordinal.{u}} {n : Nat}
    (a arity left right graph : Fin n)
    (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Constructible.TextbookDefFormula.dEqMemberDeltaAt
          a arity left right graph).toFO assignment ↔
      assignment left ∈ assignment arity ∧
        assignment right ∈ assignment arity ∧
          ZFSet.IsFunc (assignment arity) (assignment a) (assignment graph) ∧
            ∃ x : ZFSet.{u}, x ∈ assignment a ∧
              ZFSet.pair (assignment left) x ∈ assignment graph ∧
                ZFSet.pair (assignment right) x ∈ assignment graph := by
  exact (Constructible.Model.satisfiesIn_delta0_iff
    (LStageZF_isTransitive θ)
    (Constructible.TextbookDefFormula.dEqMemberDeltaAt
      a arity left right graph) assignment hAssignment).trans (by
        rw [Delta0Formula.satisfies_toFO,
          Constructible.TextbookDefFormula.satisfies_dEqMemberDeltaAt])

/-- 原子成员输出的逐元素条件在标准自然数码处具有精确语义。 -/
theorem satisfiesIn_dInOutputMemberCondition_stage_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (n i j : Nat)
    {a output graph : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (houtput : output ∈ LStageZF θ)
    (hgraph : graph ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookDefFormula.dInOutputMemberCondition
        ![a, natCode n, natCode i, natCode j, output, graph] ↔
      graph ∈ Constructible.textbookDInZF a n i j := by
  rw [Constructible.TextbookDefFormula.dInOutputMemberCondition]
  simp only [Constructible.Model.SatisfiesIn]
  have hn : (natCode n : ZFSet.{u}) ∈ LStageZF θ := natCode_mem_stage_l hω n
  have hi : (natCode i : ZFSet.{u}) ∈ LStageZF θ := natCode_mem_stage_l hω i
  have hj : (natCode j : ZFSet.{u}) ∈ LStageZF θ := natCode_mem_stage_l hω j
  have hAssignment : ∀ position : Fin 6,
      ![a, natCode n, natCode i, natCode j, output, graph] position ∈
        LStageZF θ := by
    intro position
    fin_cases position
    · exact ha
    · exact hn
    · exact hi
    · exact hj
    · exact houtput
    · exact hgraph
  constructor
  · rintro ⟨_hfinite, hmember⟩
    have hcode : graph ∈ Constructible.textbookDInCodeZF a
        (natCode n) (natCode i) (natCode j) := by
      apply Constructible.mem_textbookDInCodeZF_iff.mpr
      refine ⟨⟨n, rfl⟩, ?_⟩
      exact (satisfiesIn_dInMemberDeltaAt_stage_iff_l
        (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6) (Fin.last 5)
        ![a, natCode n, natCode i, natCode j, output, graph]
        hAssignment).mp hmember
    simpa only [Constructible.textbookDInCodeZF_natCode] using hcode
  · intro hgraphResult
    have hcode : graph ∈ Constructible.textbookDInCodeZF a
        (natCode n) (natCode i) (natCode j) := by
      simpa only [Constructible.textbookDInCodeZF_natCode] using hgraphResult
    have hcomponents := Constructible.mem_textbookDInCodeZF_iff.mp hcode
    refine ⟨(satisfiesIn_standardFiniteDomainAt_stage_iff_l
      hθ hω (1 : Fin 6) _ hAssignment).mpr ⟨n, rfl⟩, ?_⟩
    exact (satisfiesIn_dInMemberDeltaAt_stage_iff_l
      (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6) (Fin.last 5)
      ![a, natCode n, natCode i, natCode j, output, graph]
      hAssignment).mpr hcomponents.2

/-- 原子相等输出的逐元素条件在标准自然数码处具有精确语义。 -/
theorem satisfiesIn_dEqOutputMemberCondition_stage_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (n i j : Nat)
    {a output graph : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (houtput : output ∈ LStageZF θ)
    (hgraph : graph ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookDefFormula.dEqOutputMemberCondition
        ![a, natCode n, natCode i, natCode j, output, graph] ↔
      graph ∈ Constructible.textbookDEqZF a n i j := by
  rw [Constructible.TextbookDefFormula.dEqOutputMemberCondition]
  simp only [Constructible.Model.SatisfiesIn]
  have hn : (natCode n : ZFSet.{u}) ∈ LStageZF θ := natCode_mem_stage_l hω n
  have hi : (natCode i : ZFSet.{u}) ∈ LStageZF θ := natCode_mem_stage_l hω i
  have hj : (natCode j : ZFSet.{u}) ∈ LStageZF θ := natCode_mem_stage_l hω j
  have hAssignment : ∀ position : Fin 6,
      ![a, natCode n, natCode i, natCode j, output, graph] position ∈
        LStageZF θ := by
    intro position
    fin_cases position
    · exact ha
    · exact hn
    · exact hi
    · exact hj
    · exact houtput
    · exact hgraph
  constructor
  · rintro ⟨_hfinite, hmember⟩
    have hcode : graph ∈ Constructible.textbookDEqCodeZF a
        (natCode n) (natCode i) (natCode j) := by
      apply Constructible.mem_textbookDEqCodeZF_iff.mpr
      refine ⟨⟨n, rfl⟩, ?_⟩
      exact (satisfiesIn_dEqMemberDeltaAt_stage_iff_l
        (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6) (Fin.last 5)
        ![a, natCode n, natCode i, natCode j, output, graph]
        hAssignment).mp hmember
    simpa only [Constructible.textbookDEqCodeZF_natCode] using hcode
  · intro hgraphResult
    have hcode : graph ∈ Constructible.textbookDEqCodeZF a
        (natCode n) (natCode i) (natCode j) := by
      simpa only [Constructible.textbookDEqCodeZF_natCode] using hgraphResult
    have hcomponents := Constructible.mem_textbookDEqCodeZF_iff.mp hcode
    refine ⟨(satisfiesIn_standardFiniteDomainAt_stage_iff_l
      hθ hω (1 : Fin 6) _ hAssignment).mpr ⟨n, rfl⟩, ?_⟩
    exact (satisfiesIn_dEqMemberDeltaAt_stage_iff_l
      (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6) (Fin.last 5)
      ![a, natCode n, natCode i, natCode j, output, graph]
      hAssignment).mpr hcomponents.2

/-- 原子成员输出公式在局部层中唯一决定真实结果集。 -/
theorem satisfiesIn_dInOutputFormula_stage_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (n i j : Nat)
    {a output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (houtput : output ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookDefFormula.dInOutputFormula
        ![a, natCode n, natCode i, natCode j, output] ↔
      output = Constructible.textbookDInZF a n i j := by
  rw [Constructible.TextbookDefFormula.dInOutputFormula,
    satisfiesIn_all_stage_iff_l]
  simp only [Constructible.Model.satisfiesIn_biimp_iff,
    Constructible.Model.SatisfiesIn]
  have hcondition (graph : ZFSet.{u}) (hgraph : graph ∈ LStageZF θ) :
      Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          Constructible.TextbookDefFormula.dInOutputMemberCondition
          (snoc ![a, natCode n, natCode i, natCode j, output] graph) ↔
        graph ∈ Constructible.textbookDInZF a n i j := by
    have hassign :
        snoc ![a, natCode n, natCode i, natCode j, output] graph =
          ![a, natCode n, natCode i, natCode j, output, graph] := by
      funext position
      fin_cases position <;> rfl
    rw [hassign]
    exact satisfiesIn_dInOutputMemberCondition_stage_natCode_iff_l
      hθ hω n i j ha houtput hgraph
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    constructor
    · intro hgraphOutput
      have hgraphStage :=
        (LStageZF_isTransitive θ).mem_trans hgraphOutput houtput
      exact (hcondition graph hgraphStage).mp
        ((h graph hgraphStage).mp hgraphOutput)
    · intro hgraphResult
      have hresultStage : Constructible.textbookDInZF a n i j ∈ LStageZF θ :=
        textbookDInZF_mem_LStageZF_l hθ ha n i j
      have hgraphStage :=
        (LStageZF_isTransitive θ).mem_trans hgraphResult hresultStage
      exact (h graph hgraphStage).mpr
        ((hcondition graph hgraphStage).mpr hgraphResult)
  · intro houtputEq
    subst output
    intro graph hgraphStage
    change graph ∈ Constructible.textbookDInZF a n i j ↔
      Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookDefFormula.dInOutputMemberCondition
        (snoc ![a, natCode n, natCode i, natCode j,
          Constructible.textbookDInZF a n i j] graph)
    exact (hcondition graph hgraphStage).symm

/-- 原子相等输出公式在局部层中唯一决定真实结果集。 -/
theorem satisfiesIn_dEqOutputFormula_stage_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (n i j : Nat)
    {a output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (houtput : output ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookDefFormula.dEqOutputFormula
        ![a, natCode n, natCode i, natCode j, output] ↔
      output = Constructible.textbookDEqZF a n i j := by
  rw [Constructible.TextbookDefFormula.dEqOutputFormula,
    satisfiesIn_all_stage_iff_l]
  simp only [Constructible.Model.satisfiesIn_biimp_iff,
    Constructible.Model.SatisfiesIn]
  have hcondition (graph : ZFSet.{u}) (hgraph : graph ∈ LStageZF θ) :
      Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          Constructible.TextbookDefFormula.dEqOutputMemberCondition
          (snoc ![a, natCode n, natCode i, natCode j, output] graph) ↔
        graph ∈ Constructible.textbookDEqZF a n i j := by
    have hassign :
        snoc ![a, natCode n, natCode i, natCode j, output] graph =
          ![a, natCode n, natCode i, natCode j, output, graph] := by
      funext position
      fin_cases position <;> rfl
    rw [hassign]
    exact satisfiesIn_dEqOutputMemberCondition_stage_natCode_iff_l
      hθ hω n i j ha houtput hgraph
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    constructor
    · intro hgraphOutput
      have hgraphStage :=
        (LStageZF_isTransitive θ).mem_trans hgraphOutput houtput
      exact (hcondition graph hgraphStage).mp
        ((h graph hgraphStage).mp hgraphOutput)
    · intro hgraphResult
      have hresultStage : Constructible.textbookDEqZF a n i j ∈ LStageZF θ :=
        textbookDEqZF_mem_LStageZF_l hθ ha n i j
      have hgraphStage :=
        (LStageZF_isTransitive θ).mem_trans hgraphResult hresultStage
      exact (h graph hgraphStage).mpr
        ((hcondition graph hgraphStage).mpr hgraphResult)
  · intro houtputEq
    subst output
    intro graph hgraphStage
    change graph ∈ Constructible.textbookDEqZF a n i j ↔
      Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.TextbookDefFormula.dEqOutputMemberCondition
        (snoc ![a, natCode n, natCode i, natCode j,
          Constructible.textbookDEqZF a n i j] graph)
    exact (hcondition graph hgraphStage).symm

/-! ## 构造器编码守卫 -/

/-- 自然数文字 `Delta0` 公式在传递层内识别标准自然数码。 -/
theorem satisfiesIn_natLiteralDeltaAt_stage_iff_l
    {θ : Ordinal.{u}} (literal : Nat) {n : Nat} (index : Fin n)
    (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Delta0Formula.natLiteralDeltaAt literal index).toFO assignment ↔
      assignment index = (natCode literal : ZFSet.{u}) := by
  exact Constructible.Model.satisfiesIn_natLiteralDeltaAt_iff
    (LStageZF_isTransitive θ) literal index assignment hAssignment

/-- 编码守卫的量词自由主体在标准自然数码处计算构造器编号。 -/
theorem satisfiesIn_codeGuardBody_stage_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (literal : Nat) (bounded : Bool)
    {a key history output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hkey : key ∈ LStageZF θ)
    (hhistory : history ∈ LStageZF θ) (houtput : output ∈ LStageZF θ)
    (m n i j : Nat) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Constructible.TextbookEFormula.codeGuardBody literal bounded)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, natCode literal] ↔
      m = Constructible.textbookECode i j literal ∧
        (if bounded then i < n ∧ j < n else True) := by
  let assignment : Tuple ZFSet.{u} 10 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
      natCode i, natCode j, natCode literal]
  have hAssignment : ∀ position, assignment position ∈ LStageZF θ := by
    intro position
    fin_cases position
    · exact ha
    · exact hkey
    · exact hhistory
    · exact houtput
    · exact omega_toZFSet_mem_stage_l hω
    · exact natCode_mem_stage_l hω m
    · exact natCode_mem_stage_l hω n
    · exact natCode_mem_stage_l hω i
    · exact natCode_mem_stage_l hω j
    · exact natCode_mem_stage_l hω literal
  have htag :
      Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          (Delta0Formula.natLiteralDeltaAt literal (9 : Fin 10)).toFO
          assignment ↔
        (natCode literal : ZFSet.{u}) = natCode literal :=
    satisfiesIn_natLiteralDeltaAt_stage_iff_l literal (9 : Fin 10)
      assignment hAssignment
  have hcode :
      Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          (Constructible.TextbookNatFormula.textbookECodeFormulaAt
            (4 : Fin 10) (7 : Fin 10) (8 : Fin 10)
            (9 : Fin 10) (5 : Fin 10)) assignment ↔
        (natCode m : ZFSet.{u}) =
          natCode (Constructible.textbookECode i j literal) := by
    rw [Constructible.TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt]
    simpa [assignment] using
      (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
        hθ hω i j literal (natCode_mem_stage_l hω m))
  change Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      (Constructible.TextbookEFormula.codeGuardBody literal bounded)
      assignment ↔ _
  rw [Constructible.TextbookEFormula.codeGuardBody]
  cases bounded <;>
    simp [Constructible.Model.SatisfiesIn, htag, hcode, assignment,
      IndexedSequenceZF.mem_omega_iff_exists_natCode,
      natCode_injective.eq_iff]

/-- 三个存在量词组成的完整编码守卫在局部层中只产生标准自然数见证。 -/
theorem satisfiesIn_codeGuard_stage_standard_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (literal : Nat) (bounded : Bool)
    {a key history output : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hkey : key ∈ LStageZF θ)
    (hhistory : history ∈ LStageZF θ) (houtput : output ∈ LStageZF θ)
    (m n : Nat) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Constructible.TextbookEFormula.codeGuard literal bounded)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = Constructible.textbookECode i j literal ∧
        (if bounded then i < n ∧ j < n else True) := by
  rw [Constructible.TextbookEFormula.codeGuard]
  simp only [Constructible.Model.SatisfiesIn]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hassign (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext position
    fin_cases position <;> rfl
  constructor
  · rintro ⟨iSet, hiStage, jSet, hjStage, tagSet, htagStage, hbody⟩
    rw [hassign] at hbody
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet).mp
      hbody.1 with ⟨i, hi⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet).mp
      hbody.2.1 with ⟨j, hj⟩
    subst iSet
    subst jSet
    have hfullAssignment : ∀ position : Fin 10,
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, tagSet] position ∈ LStageZF θ := by
      intro position
      fin_cases position
      · exact ha
      · exact hkey
      · exact hhistory
      · exact houtput
      · exact omega_toZFSet_mem_stage_l hω
      · exact natCode_mem_stage_l hω m
      · exact natCode_mem_stage_l hω n
      · exact hiStage
      · exact hjStage
      · exact htagStage
    have htag : tagSet = (natCode literal : ZFSet.{u}) :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l literal (9 : Fin 10)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, tagSet] hfullAssignment).mp hbody.2.2.1
    subst tagSet
    exact ⟨i, j, (satisfiesIn_codeGuardBody_stage_natCode_iff_l
      hθ hω literal bounded ha hkey hhistory houtput m n i j).mp hbody⟩
  · rintro ⟨i, j, hcode⟩
    refine ⟨(natCode i : ZFSet.{u}), natCode_mem_stage_l hω i,
      (natCode j : ZFSet.{u}), natCode_mem_stage_l hω j,
      (natCode literal : ZFSet.{u}), natCode_mem_stage_l hω literal, ?_⟩
    rw [hassign]
    exact (satisfiesIn_codeGuardBody_stage_natCode_iff_l
      hθ hω literal bounded ha hkey hhistory houtput m n i j).mpr hcode

/-- 编码守卫主体中的三个层内见证必为相应的标准自然数码。 -/
theorem exists_natCode_fields_of_satisfiesIn_codeGuardBody_stage_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    {a key history output iSet jSet tagSet : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hkey : key ∈ LStageZF θ)
    (hhistory : history ∈ LStageZF θ) (houtput : output ∈ LStageZF θ)
    (hiSet : iSet ∈ LStageZF θ) (hjSet : jSet ∈ LStageZF θ)
    (htagSet : tagSet ∈ LStageZF θ)
    (literal : Nat) (bounded : Bool) (m n : Nat)
    (hbody : Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      (Constructible.TextbookEFormula.codeGuardBody literal bounded)
      ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet]) :
    ∃ i j : Nat,
      iSet = natCode i ∧ jSet = natCode j ∧ tagSet = natCode literal ∧
        m = Constructible.textbookECode i j literal ∧
          (if bounded then i < n ∧ j < n else True) := by
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet).mp
    hbody.1 with ⟨i, hi⟩
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet).mp
    hbody.2.1 with ⟨j, hj⟩
  have hAssignment : ∀ position : Fin 10,
      ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet] position ∈ LStageZF θ := by
    intro position
    fin_cases position
    · exact ha
    · exact hkey
    · exact hhistory
    · exact houtput
    · exact omega_toZFSet_mem_stage_l hω
    · exact natCode_mem_stage_l hω m
    · exact natCode_mem_stage_l hω n
    · exact hiSet
    · exact hjSet
    · exact htagSet
  have htag : tagSet = (natCode literal : ZFSet.{u}) :=
    (satisfiesIn_natLiteralDeltaAt_stage_iff_l literal (9 : Fin 10)
      ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet] hAssignment).mp hbody.2.2.1
  subst iSet
  subst jSet
  subst tagSet
  exact ⟨i, j, rfl, rfl, rfl,
    (satisfiesIn_codeGuardBody_stage_natCode_iff_l
      hθ hω literal bounded ha hkey hhistory houtput m n i j).mp hbody⟩

end

end YesMetaZFC.BMS.ConstructibleBridge
