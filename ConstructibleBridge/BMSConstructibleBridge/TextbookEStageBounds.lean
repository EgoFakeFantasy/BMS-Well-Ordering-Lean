import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEConstructible
import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareStageHistoryBounds
import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookELocalDomainLCarrier
import ConstructibleUniverse.SetTheory.ZFC.Constructible.CondensationOmega

/-!
# 后继极限层对 textbook E 的闭包界

`textbookE` 的全局可构造性不足以在局部反射中提供见证：还必须知道输入已经
属于某个后继极限层时，有限元组空间、四个递归操作以及最终的 E 值仍属于同一
层。本文件把全局证明中的有界定义论证局部化；关键是先把有限参数共同下压到
一个严格较小的阶段，再在一次 `Def` 后返回原后继极限层。
-/

open Set

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open Constructible.FiniteSequenceZF

noncomputable section

/-- 后继极限层中的有限元组可共同下降到一个严格较小的阶段。 -/
theorem exists_stageBound_for_tuple_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {n : Nat} (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ LStageZF θ) :
    ∃ γ < θ, ∀ i, s i ∈ LStageZF γ := by
  induction n with
  | zero =>
      obtain ⟨γ, hγ⟩ := not_isMin_iff.mp hθ.1
      exact ⟨γ, hγ, fun i => Fin.elim0 i⟩
  | succ n ih =>
      let s₀ : Tuple ZFSet.{u} n := fun i => s i.castSucc
      obtain ⟨α, hα, hs₀⟩ := ih s₀ (fun i => hs i.castSucc)
      obtain ⟨β, hβ, hlast⟩ :=
        (mem_LStageZF_limit_iff hθ).mp (hs (Fin.last n))
      refine ⟨max α β, max_lt hα hβ, ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact LStageZF_mono (le_max_right α β) hlast
      · exact LStageZF_mono (le_max_left α β) (hs₀ j)

/--
一个由固定有界公式在某个已知界内定义的集合仍属于同一后继极限层。
成员界保证把全部候选一起压到参数阶段，因而只消耗一次 `Def`。
-/
theorem mem_LStageZF_of_delta0_definition_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {z bound : ZFSet.{u}} {n : Nat}
    (params : Tuple ZFSet.{u} n)
    (hparams : ∀ i, params i ∈ LStageZF θ)
    (hbound : bound ∈ LStageZF θ) (hz : z ⊆ bound)
    (φ : Delta0Formula (n + 1))
    (hφ : ∀ q : ZFSet.{u},
      Delta0Formula.Satisfies Delta0Formula.ZFMem φ (snoc params q) ↔
        q ∈ z) :
    z ∈ LStageZF θ := by
  let extended : Tuple ZFSet.{u} (n + 1) := snoc params bound
  have hextended : ∀ i, extended i ∈ LStageZF θ := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [extended] using hbound
    · simpa [extended] using hparams j
  obtain ⟨γ, hγ, hsmall⟩ :=
    exists_stageBound_for_tuple_l hθ extended hextended
  let stageParams : Tuple (ZFCarrier (LStageZF γ)) n :=
    fun i => ⟨params i, by simpa [extended] using hsmall i.castSucc⟩
  have hboundγ : bound ∈ LStageZF γ := by
    simpa [extended] using hsmall (Fin.last n)
  let certificate : Delta0Section (LStageZF γ) z := {
    arity := n
    params := stageParams
    formula := φ
    correct := by
      intro q
      have hvalues : Delta0Formula.val stageParams = params := by
        funext i
        rfl
      simpa only [hvalues] using hφ q.1 }
  have hzγ : z ⊆ LStageZF γ := by
    intro q hq
    exact (LStageZF_isTransitive γ).mem_trans (hz hq) hboundγ
  have hzDef : z ∈ DefZF (LStageZF γ) :=
    certificate.mem_DefZF (LStageZF_isTransitive γ) hzγ
  rw [← LStageZF_succ] at hzDef
  exact LStageZF_mono (hθ.succ_lt hγ).le hzDef

/-- 在显式阶段界上的集合并只消耗两个后继。 -/
theorem union_mem_LStageZF_succ_succ_l
    {α : Ordinal.{u}} {x y : ZFSet.{u}}
    (hx : x ∈ LStageZF α) (hy : y ∈ LStageZF α) :
    x ∪ y ∈ LStageZF (Order.succ (Order.succ α)) := by
  rw [show x ∪ y = ZFSet.sUnion ({x, y} : ZFSet.{u}) by
    ext q
    simp]
  exact sUnion_mem_LStageZF_succ (pair_mem_LStageZF_succ hx hy)

/-- 在显式阶段界上插入一个元素只消耗三个后继。 -/
theorem insert_mem_LStageZF_three_succ_l
    {α : Ordinal.{u}} {x y : ZFSet.{u}}
    (hx : x ∈ LStageZF α) (hy : y ∈ LStageZF α) :
    insert x y ∈
      LStageZF (Order.succ (Order.succ (Order.succ α))) := by
  rw [ZFSet.insert_eq]
  apply union_mem_LStageZF_succ_succ_l
  · simpa using pair_mem_LStageZF_succ hx hx
  · exact LStageZF_subset_succ α hy

/--
固定长度元组的全部规范图同时落在某个严格低于后继极限层的阶段中。
这个统一界随后充当有界定义所需的成员界。
-/
theorem exists_textbookTupleGraph_stageBound_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {a : ZFSet.{u}} (ha : a ∈ LStageZF θ) :
    ∀ n, ∃ γ < θ, ∀ s : Tuple (ZFCarrier a) n,
      textbookTupleGraph s ∈ LStageZF γ := by
  intro n
  induction n with
  | zero =>
      have hempty : (∅ : ZFSet.{u}) ∈ LStageZF θ :=
        empty_mem_LStageZF_of_isSuccLimit hθ
      obtain ⟨γ, hγ, hzero⟩ := (mem_LStageZF_limit_iff hθ).mp hempty
      refine ⟨γ, hγ, ?_⟩
      intro s
      have hs : textbookTupleGraph s = (∅ : ZFSet.{u}) := by
        apply ZFSet.eq_empty _ |>.mpr
        intro q hq
        rcases (mem_textbookTupleGraph_iff s).mp hq with ⟨i, _⟩
        exact Fin.elim0 i
      simpa only [hs] using hzero
  | succ n ih =>
      obtain ⟨α, hα, hprefix⟩ := ih
      obtain ⟨β, hβ, haβ⟩ := (mem_LStageZF_limit_iff hθ).mp ha
      have hcodeθ : (natCode n : ZFSet.{u}) ∈ LStageZF θ :=
        natCode_mem_LStageZF_of_isSuccLimit hθ n
      obtain ⟨δ, hδ, hcodeδ⟩ :=
        (mem_LStageZF_limit_iff hθ).mp hcodeθ
      let κ₀ := max α (max β δ)
      let κ₁ := Order.succ κ₀
      let κ₂ := Order.succ κ₁
      let κ₃ := Order.succ κ₂
      let κ₄ := Order.succ κ₃
      let κ₅ := Order.succ κ₄
      have hκ₀ : κ₀ < θ := max_lt hα (max_lt hβ hδ)
      have hκ₁ : κ₁ < θ := hθ.succ_lt hκ₀
      have hκ₂ : κ₂ < θ := hθ.succ_lt hκ₁
      have hκ₃ : κ₃ < θ := hθ.succ_lt hκ₂
      have hκ₄ : κ₄ < θ := hθ.succ_lt hκ₃
      have hκ₅ : κ₅ < θ := hθ.succ_lt hκ₄
      refine ⟨κ₅, hκ₅, ?_⟩
      intro s
      let s₀ : Tuple (ZFCarrier a) n := fun i => s i.castSucc
      let x : ZFCarrier a := s (Fin.last n)
      have hs : s = snoc s₀ x := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [x]
        · simp [s₀]
      rw [hs, textbookTupleGraph_snoc]
      have hprefix₀ : textbookTupleGraph s₀ ∈ LStageZF κ₀ :=
        LStageZF_mono (le_max_left α (max β δ)) (hprefix s₀)
      have hx₀ : x.1 ∈ LStageZF κ₀ :=
        LStageZF_mono ((le_max_left β δ).trans
          (le_max_right α (max β δ)))
          ((LStageZF_isTransitive β).mem_trans x.2 haβ)
      have hcode₀ : (natCode n : ZFSet.{u}) ∈ LStageZF κ₀ :=
        LStageZF_mono ((le_max_right β δ).trans
          (le_max_right α (max β δ))) hcodeδ
      have hentry : ZFSet.pair (natCode n) x.1 ∈ LStageZF κ₂ := by
        exact orderedPair_mem_LStageZF_succ_succ hcode₀ hx₀
      exact insert_mem_LStageZF_three_succ_l hentry
        (LStageZF_mono (by
          exact (Order.le_succ κ₀).trans (Order.le_succ κ₁)) hprefix₀)

/-- 标准有限元组空间保持在给定后继极限层中。 -/
theorem textbookTupleSpace_mem_LStageZF_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {a : ZFSet.{u}} (ha : a ∈ LStageZF θ) (n : Nat) :
    textbookTupleSpace a n ∈ LStageZF θ := by
  obtain ⟨γ, hγ, hgraphs⟩ :=
    exists_textbookTupleGraph_stageBound_l hθ ha n
  let params : Tuple ZFSet.{u} 2 := ![natCode n, a]
  apply mem_LStageZF_of_delta0_definition_l hθ params
      (by
        intro i
        fin_cases i
        · exact natCode_mem_LStageZF_of_isSuccLimit hθ n
        · exact ha)
      (LStageZF_mem_of_lt hγ)
      (fun graph hgraph => by
        rcases exists_textbookTupleGraph_eq_of_isFunc
            (mem_textbookTupleSpace_iff.mp hgraph) with ⟨s, rfl⟩
        exact hgraphs s)
      (TextbookDefFormula.isFunctionDeltaAt
        (2 : Fin 3) (0 : Fin 3) (1 : Fin 3))
  intro graph
  rw [TextbookDefFormula.satisfies_isFunctionDeltaAt]
  exact mem_textbookTupleSpace_iff.symm

/-! ## `textbookE` 四种构造在局部层中的封闭性 -/

/-- 有限元组空间上的原子成员关系仍属于同一个后继极限层。 -/
theorem textbookDInZF_mem_LStageZF_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {a : ZFSet.{u}} (ha : a ∈ LStageZF θ) (n i j : Nat) :
    textbookDInZF a n i j ∈ LStageZF θ := by
  let params : Tuple ZFSet.{u} 4 :=
    ![a, natCode n, natCode i, natCode j]
  have hspace : textbookTupleSpace a n ∈ LStageZF θ :=
    textbookTupleSpace_mem_LStageZF_l hθ ha n
  apply mem_LStageZF_of_delta0_definition_l hθ params (by
      intro k
      fin_cases k
      · exact ha
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ n
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ i
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ j)
    hspace
    (textbookDInZF_subset_tupleSpace a n i j)
    TextbookDefFormula.dInMemberDelta
  intro graph
  change
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        TextbookDefFormula.dInMemberDelta
        ![a, natCode n, natCode i, natCode j, graph] ↔ _
  rw [TextbookDefFormula.satisfies_dInMemberDelta]
  rw [← textbookDInCodeZF_natCode]
  rw [mem_textbookDInCodeZF_iff]
  constructor
  · intro h
    exact ⟨⟨n, rfl⟩, h⟩
  · rintro ⟨_, h⟩
    exact h

/-- 有限元组空间上的原子相等关系仍属于同一个后继极限层。 -/
theorem textbookDEqZF_mem_LStageZF_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {a : ZFSet.{u}} (ha : a ∈ LStageZF θ) (n i j : Nat) :
    textbookDEqZF a n i j ∈ LStageZF θ := by
  let params : Tuple ZFSet.{u} 4 :=
    ![a, natCode n, natCode i, natCode j]
  have hspace : textbookTupleSpace a n ∈ LStageZF θ :=
    textbookTupleSpace_mem_LStageZF_l hθ ha n
  apply mem_LStageZF_of_delta0_definition_l hθ params (by
      intro k
      fin_cases k
      · exact ha
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ n
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ i
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ j)
    hspace
    (textbookDEqZF_subset_tupleSpace a n i j)
    TextbookDefFormula.dEqMemberDelta
  intro graph
  change
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        TextbookDefFormula.dEqMemberDelta
        ![a, natCode n, natCode i, natCode j, graph] ↔ _
  rw [TextbookDefFormula.satisfies_dEqMemberDelta]
  rw [← textbookDEqCodeZF_natCode]
  rw [mem_textbookDEqCodeZF_iff]
  constructor
  · intro h
    exact ⟨⟨n, rfl⟩, h⟩
  · rintro ⟨_, h⟩
    exact h

/-- 相对差在后继极限层内封闭。 -/
theorem relativeDifferenceZF_mem_LStageZF_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {space removed : ZFSet.{u}}
    (hspace : space ∈ LStageZF θ) (hremoved : removed ∈ LStageZF θ) :
    relativeDifferenceZF space removed ∈ LStageZF θ := by
  simpa [relativeDifferenceZF, Godel.op, Godel.F1] using
    (Godel.op_mem_LStageZF_of_isSuccLimit hθ (1 : Fin 9) hspace hremoved)

/-- 交集在后继极限层内封闭。 -/
theorem intersectionZF_mem_LStageZF_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {left right : ZFSet.{u}}
    (hleft : left ∈ LStageZF θ) (hright : right ∈ LStageZF θ) :
    intersectionZF left right ∈ LStageZF θ := by
  have hleftRight : relativeDifferenceZF left right ∈ LStageZF θ :=
    relativeDifferenceZF_mem_LStageZF_l hθ hleft hright
  have hresult :
      relativeDifferenceZF left (relativeDifferenceZF left right) ∈
        LStageZF θ :=
    relativeDifferenceZF_mem_LStageZF_l hθ hleft hleftRight
  have heq :
      relativeDifferenceZF left (relativeDifferenceZF left right) =
        intersectionZF left right := by
    apply ZFSet.ext
    intro x
    simp only [mem_relativeDifferenceZF_iff, mem_intersectionZF_iff]
    tauto
  rwa [heq] at hresult

/-- 教材式存在量词投影在后继极限层内封闭。 -/
theorem textbookExistsProjZF_mem_LStageZF_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {a relation : ZFSet.{u}}
    (ha : a ∈ LStageZF θ) (hrelation : relation ∈ LStageZF θ)
    (n : Nat) :
    textbookExistsProjZF a n relation ∈ LStageZF θ := by
  let params : Tuple ZFSet.{u} 3 := ![a, natCode n, relation]
  have hspace : textbookTupleSpace a n ∈ LStageZF θ :=
    textbookTupleSpace_mem_LStageZF_l hθ ha n
  apply mem_LStageZF_of_delta0_definition_l hθ params (by
      intro k
      fin_cases k
      · exact ha
      · exact natCode_mem_LStageZF_of_isSuccLimit hθ n
      · exact hrelation)
    hspace
    (textbookExistsProjZF_subset_tupleSpace a n relation)
    TextbookDefFormula.existsProjMemberDelta
  intro graph
  change
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        TextbookDefFormula.existsProjMemberDelta
        ![a, natCode n, relation, graph] ↔ _
  rw [TextbookDefFormula.satisfies_existsProjMemberDelta]
  rw [← textbookExistsProjCodeZF_natCode]
  rw [mem_textbookExistsProjCodeZF_iff]
  constructor
  · intro h
    exact ⟨⟨n, rfl⟩, h⟩
  · rintro ⟨_, h⟩
    exact h

/-! ## 对 E 递归的统一局部封闭定理 -/

/--
只要参数集合已经进入一个后继极限层，任意标准自然数代码处的教材式
枚举值也进入同一层。这是后续在 `L_θ` 内量化 E 图的集合论见证。
-/
theorem textbookEZF_natCode_mem_LStageZF_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {a : ZFSet.{u}} (ha : a ∈ LStageZF θ) (n m : Nat) :
    textbookEZF a (natCode n) (natCode m) ∈ LStageZF θ := by
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
      cases hdecode : textbookEDecode m with
      | none =>
          rw [textbookEZF_eq_empty_of_decode_none a n m hdecode]
          exact empty_mem_LStageZF_of_isSuccLimit hθ
      | some fields =>
          rcases fields with ⟨i, j, tag⟩
          have hdecoded :=
            (textbookEDecode_eq_some_iff m i j tag).mp hdecode
          rcases hdecoded with ⟨htag, hm⟩
          subst m
          have hi : i < textbookECode i j tag :=
            textbookECode_index_lt i j tag
          have htagCases :
              tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 := by
            omega
          rcases htagCases with rfl | rfl | rfl | rfl | rfl
          · by_cases hin : i < n
            · by_cases hjn : j < n
              · rw [textbookEZF_code_zero a n i j hin hjn,
                  textbookDInCodeZF_natCode]
                exact textbookDInZF_mem_LStageZF_l hθ ha n i j
              · rw [textbookEZF_code_zero_eq_empty_of_not_lt_right
                  a n i j hjn]
                exact empty_mem_LStageZF_of_isSuccLimit hθ
            · rw [textbookEZF_code_zero_eq_empty_of_not_lt_left
                a n i j hin]
              exact empty_mem_LStageZF_of_isSuccLimit hθ
          · by_cases hin : i < n
            · by_cases hjn : j < n
              · rw [textbookEZF_code_one a n i j hin hjn,
                  textbookDEqCodeZF_natCode]
                exact textbookDEqZF_mem_LStageZF_l hθ ha n i j
              · rw [textbookEZF_code_one_eq_empty_of_not_lt_right
                  a n i j hjn]
                exact empty_mem_LStageZF_of_isSuccLimit hθ
            · rw [textbookEZF_code_one_eq_empty_of_not_lt_left
                a n i j hin]
              exact empty_mem_LStageZF_of_isSuccLimit hθ
          · rw [textbookEZF_code_two]
            exact relativeDifferenceZF_mem_LStageZF_l hθ
              (textbookTupleSpace_mem_LStageZF_l hθ ha n) (ih i hi n)
          · have hj : j < textbookECode i j 3 := by
              apply lt_of_lt_of_le
                (lt_of_lt_of_le j.lt_two_pow_self
                  (Nat.pow_le_pow_left (by decide : 2 ≤ 3) j))
              simp only [textbookECode]
              have htwo : 0 < 2 ^ i := Nat.pow_pos (by decide)
              have hfive : 0 < 5 ^ 3 := Nat.pow_pos (by decide)
              simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
                Nat.le_mul_of_pos_left (3 ^ j) (Nat.mul_pos htwo hfive)
            rw [textbookEZF_code_three]
            exact intersectionZF_mem_LStageZF_l hθ
              (ih i hi n) (ih j hj n)
          · rw [textbookEZF_code_four,
              textbookExistsProjCodeZF_natCode]
            exact textbookExistsProjZF_mem_LStageZF_l hθ ha
              (ih i hi (n + 1)) n

/-! ## 有限定义域上的函数图 -/

/--
若定义域本身及其全部函数值已经位于一个后继极限层，而且定义域在外部确实
有限，则相应的 Kuratowski 函数图仍位于同一层。这个引理把有限递归证书所需
的集合收集归约为插入闭包，不使用 Replacement。
-/
theorem predecessorRestrictionGraph_mem_LStageZF_of_finite_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {domain : ZFSet.{u}} {value : ZFSet.{u} → ZFSet.{u}}
    (hdomain : domain ∈ LStageZF θ)
    (hfinite : (domain : Set ZFSet.{u}).Finite)
    (hvalue : ∀ x : ZFSet.{u}, x ∈ domain → value x ∈ LStageZF θ) :
    predecessorRestrictionGraph domain value ∈ LStageZF θ := by
  apply Constructible.MostowskiCollapse.OmegaCondensation.mem_of_externallyFinite_of_insert_closed
    (empty_mem_LStageZF_of_isSuccLimit hθ)
    (fun hx hy => by
      rw [ZFSet.insert_eq]
      exact union_mem_LStageZF_of_isSuccLimit hθ
        (singleton_mem_LStageZF_of_isSuccLimit hθ hx) hy)
  · apply hfinite.image (fun x => ZFSet.pair x (value x)) |>.subset
    intro pair hpair
    rcases mem_predecessorRestrictionGraph_iff.mp hpair with
      ⟨input, hinput, rfl⟩
    exact ⟨input, hinput, rfl⟩
  · intro pair hpair
    rcases mem_predecessorRestrictionGraph_iff.mp hpair with
      ⟨input, hinput, rfl⟩
    exact orderedPair_mem_LStageZF_of_isSuccLimit hθ
      ((LStageZF_isTransitive θ).mem_trans hinput hdomain)
      (hvalue input hinput)

/-! ## 单步递归所需的历史查询闭包 -/

/-- 图中公开出现的值属于包含该图的传递层。 -/
theorem graphValue_mem_LStageZF_l
    {θ : Ordinal.{u}} {graph key value : ZFSet.{u}}
    (hgraph : graph ∈ LStageZF θ)
    (hvalue : ZFSet.pair key value ∈ graph) :
    value ∈ LStageZF θ := by
  have hpairStage : ZFSet.pair key value ∈ LStageZF θ :=
    (LStageZF_isTransitive θ).mem_trans hvalue hgraph
  have hunorderedPair : ({key, value} : ZFSet.{u}) ∈
      ZFSet.pair key value := by
    simp [ZFSet.pair]
  have hunorderedPairStage : ({key, value} : ZFSet.{u}) ∈
      LStageZF θ :=
    (LStageZF_isTransitive θ).mem_trans hunorderedPair hpairStage
  exact (LStageZF_isTransitive θ).mem_trans (by simp)
    hunorderedPairStage

/-- 全函数化的唯一图查询保持在任意后继极限层内。 -/
theorem uniqueGraphLookupZF_mem_LStageZF_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {graph key : ZFSet.{u}} (hgraph : graph ∈ LStageZF θ)
    (_hkey : key ∈ LStageZF θ) :
    uniqueGraphLookupZF graph key ∈ LStageZF θ := by
  by_cases hunique : ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph
  · rcases hunique with ⟨value, hvalue, hvalueUnique⟩
    rw [uniqueGraphLookupZF_eq_of_unique hvalue hvalueUnique]
    exact graphValue_mem_LStageZF_l hgraph hvalue
  · rw [uniqueGraphLookupZF_eq_empty_of_not_unique hunique]
    exact empty_mem_LStageZF_of_isSuccLimit hθ

/--
教材式 E 的单步函数在真实递归定义域上保持后继极限层。证明逐项对应五个
构造分支，并把所有历史读取交给前一闭包定理。
-/
theorem textbookEStep_mem_LStageZF_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {a key history : ZFSet.{u}} (ha : a ∈ LStageZF θ)
    (hhistory : history ∈ LStageZF θ)
    (hkeyDomain : key ∈ TextbookEDomain) :
    textbookEStep a key history ∈ LStageZF θ := by
  rcases exists_textbookEKeyDecode_of_mem_textbookEDomain hkeyDomain with
    ⟨m, n, hdecode, _hkeyEq⟩
  unfold textbookEStep
  rw [hdecode]
  simp only
  cases hcode : textbookEDecode m with
  | none =>
      exact empty_mem_LStageZF_of_isSuccLimit hθ
  | some fields =>
      rcases fields with ⟨i, j, tag⟩
      cases tag with
      | zero =>
          simp only
          split_ifs
          · rw [textbookDInCodeZF_natCode]
            exact textbookDInZF_mem_LStageZF_l hθ ha n i j
          · exact empty_mem_LStageZF_of_isSuccLimit hθ
      | succ tag =>
          cases tag with
          | zero =>
              simp only
              split_ifs
              · rw [textbookDEqCodeZF_natCode]
                exact textbookDEqZF_mem_LStageZF_l hθ ha n i j
              · exact empty_mem_LStageZF_of_isSuccLimit hθ
          | succ tag =>
              cases tag with
              | zero =>
                  simp only
                  have hlookup :
                      uniqueGraphLookupZF history
                          (ZFSet.pair (natCode i) (natCode n)) ∈
                        LStageZF θ :=
                    uniqueGraphLookupZF_mem_LStageZF_l hθ hhistory
                      (orderedPair_mem_LStageZF_of_isSuccLimit hθ
                        (natCode_mem_LStageZF_of_isSuccLimit hθ i)
                        (natCode_mem_LStageZF_of_isSuccLimit hθ n))
                  exact relativeDifferenceZF_mem_LStageZF_l hθ
                    (textbookTupleSpace_mem_LStageZF_l hθ ha n) hlookup
              | succ tag =>
                  cases tag with
                  | zero =>
                      simp only
                      have hleft :
                          uniqueGraphLookupZF history
                              (ZFSet.pair (natCode i) (natCode n)) ∈
                            LStageZF θ :=
                        uniqueGraphLookupZF_mem_LStageZF_l hθ hhistory
                          (orderedPair_mem_LStageZF_of_isSuccLimit hθ
                            (natCode_mem_LStageZF_of_isSuccLimit hθ i)
                            (natCode_mem_LStageZF_of_isSuccLimit hθ n))
                      have hright :
                          uniqueGraphLookupZF history
                              (ZFSet.pair (natCode j) (natCode n)) ∈
                            LStageZF θ :=
                        uniqueGraphLookupZF_mem_LStageZF_l hθ hhistory
                          (orderedPair_mem_LStageZF_of_isSuccLimit hθ
                            (natCode_mem_LStageZF_of_isSuccLimit hθ j)
                            (natCode_mem_LStageZF_of_isSuccLimit hθ n))
                      exact intersectionZF_mem_LStageZF_l hθ hleft hright
                  | succ tag =>
                      cases tag with
                      | zero =>
                          simp only
                          have hrelation :
                              uniqueGraphLookupZF history
                                  (ZFSet.pair (natCode i)
                                    (natCode (n + 1))) ∈ LStageZF θ :=
                            uniqueGraphLookupZF_mem_LStageZF_l hθ hhistory
                              (orderedPair_mem_LStageZF_of_isSuccLimit hθ
                                (natCode_mem_LStageZF_of_isSuccLimit hθ i)
                                (natCode_mem_LStageZF_of_isSuccLimit hθ
                                  (n + 1)))
                          rw [textbookExistsProjCodeZF_natCode]
                          exact textbookExistsProjZF_mem_LStageZF_l hθ ha
                            hrelation n
                      | succ tag =>
                exact empty_mem_LStageZF_of_isSuccLimit hθ

/-! ## 标准键的局部递归域 -/

/-- 标准 E 键属于教材递归域。 -/
theorem textbookEKey_mem_domain_l (m n : Nat) :
    ZFSet.pair (natCode m : ZFSet.{u}) (natCode n) ∈
      TextbookEDomain := by
  apply mem_textbookEDomain_iff.mpr
  refine ⟨natCode m, ?_, natCode n, ?_, rfl⟩
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 m)
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 n)

/-- 标准键的教材 E 局部递归域仍属于同一个后继极限层。 -/
theorem textbookE_localRecursionDomain_natCode_mem_LStageZF_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (m n : Nat) :
    localRecursionDomain TextbookEDomain TextbookERelation
        textbookERelation_hasSetPredecessorsOn
        (ZFSet.pair (natCode m : ZFSet.{u}) (natCode n)) ∈
      LStageZF θ := by
  have hmOmega : (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF :=
    Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 m)
  have hnOmega : (natCode n : ZFSet.{u}) ∈ textbookEOmegaZF :=
    Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 n)
  rw [textbookE_localRecursionDomain_eq hmOmega hnOmega]
  have hmStage : (natCode m : ZFSet.{u}) ∈ LStageZF θ :=
    natCode_mem_LStageZF_of_isSuccLimit hθ m
  have hnStage : (natCode n : ZFSet.{u}) ∈ LStageZF θ :=
    natCode_mem_LStageZF_of_isSuccLimit hθ n
  have homegaStage : (textbookEOmegaZF : ZFSet.{u}) ∈ LStageZF θ := by
    simpa only [textbookEOmegaZF] using
      (ordinal_toZFSet_mem_LStageZF_of_lt hω)
  have hkeyStage : ZFSet.pair (natCode m) (natCode n) ∈ LStageZF θ :=
    orderedPair_mem_LStageZF_of_isSuccLimit hθ hmStage hnStage
  have hproductStage : ZFSet.prod (natCode m) textbookEOmegaZF ∈
      LStageZF θ := by
    simpa [Godel.op, Godel.F2] using
      (Godel.op_mem_LStageZF_of_isSuccLimit
        hθ (i := (2 : Fin 9)) hmStage homegaStage)
  rw [ZFSet.insert_eq]
  exact union_mem_LStageZF_of_isSuccLimit hθ
    (singleton_mem_LStageZF_of_isSuccLimit hθ hkeyStage) hproductStage

/-- 教材关系的任一前驱在局部层中仍有标准自然数对编码。 -/
theorem textbookERelation_predecessorsClosedIn_stage_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) :
    PredecessorsClosedIn (LStageZF θ : Set ZFSet.{u})
      TextbookEDomain TextbookERelation := by
  intro x _hxStage y hyDomain hyRelation
  rcases mem_textbookEDomain_iff.mp
      (textbookERelation_isRelationOn.right_mem hyRelation) with
    ⟨m, hm, n, hn, hxPair⟩
  have hyProduct : y ∈ ZFSet.prod m textbookEOmegaZF := by
    apply (textbookE_predecessorSet hm hn y).mpr
    simpa only [hxPair] using And.intro hyDomain hyRelation
  rcases ZFSet.mem_prod.mp hyProduct with
    ⟨i, hi, j, hj, hyPair⟩
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode m).mp hm with
    ⟨mCode, rfl⟩
  rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt i mCode).mp hi with
    ⟨iCode, _hiCode, rfl⟩
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode j).mp hj with
    ⟨jCode, rfl⟩
  rw [hyPair]
  exact orderedPair_mem_LStageZF_of_isSuccLimit hθ
    (natCode_mem_LStageZF_of_isSuccLimit hθ iCode)
    (natCode_mem_LStageZF_of_isSuccLimit hθ jCode)

end

end YesMetaZFC.BMS.ConstructibleBridge
