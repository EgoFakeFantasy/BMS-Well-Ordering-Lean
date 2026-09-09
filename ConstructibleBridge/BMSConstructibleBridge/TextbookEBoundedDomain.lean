import BMSConstructibleBridge.TextbookEStageBounds

/-!
# textbook E 的有限元数截断域

完整教材递归在代码 `m` 以下保留所有自然数元数，因此局部图包含
`m × omega`。单次公式求值只需要一个有限元数窗口。本文件把第二坐标限制在
给定集合 `bound` 中，同时保留原来的代码递减关系；在标准自然数界处，目标键
的局部递归域恰为一个点与有限乘积之并。
-/

open Set

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open Constructible.FiniteSequenceZF

noncomputable section

/-- 元数坐标落在 `bound` 中的教材 E 键。 -/
def TextbookEBoundedDomain_l (bound : ZFSet.{u}) : Set ZFSet.{u} :=
  (ZFSet.prod textbookEOmegaZF bound : Set ZFSet.{u})

/-- 教材代码递减关系在有限元数域上的限制。 -/
def TextbookEBoundedRelation_l (bound : ZFSet.{u}) :
    Set (Tuple ZFSet.{u} 2) :=
  { assignment |
    assignment 0 ∈ TextbookEBoundedDomain_l bound ∧
      assignment 1 ∈ TextbookEBoundedDomain_l bound ∧
        assignment ∈ TextbookERelation }

/-- 当元数界包含于 `omega` 时，受限键仍是真正的教材 E 键。 -/
theorem textbookEBoundedDomain_subset_textbookEDomain_l
    {bound : ZFSet.{u}} (hbound : bound ⊆ textbookEOmegaZF) :
    TextbookEBoundedDomain_l bound ⊆ TextbookEDomain := by
  intro key hKey
  rcases ZFSet.mem_prod.mp hKey with
    ⟨code, hCode, arity, hArity, rfl⟩
  exact mem_textbookEDomain_iff.mpr
    ⟨code, hCode, arity, hbound hArity, rfl⟩

@[simp] theorem classRel_textbookEBoundedRelation_iff_l
    (bound left right : ZFSet.{u}) :
    ClassRel (TextbookEBoundedRelation_l bound) left right ↔
      left ∈ TextbookEBoundedDomain_l bound ∧
        right ∈ TextbookEBoundedDomain_l bound ∧
          ClassRel TextbookERelation left right := by
  rfl

/-- 受限关系确实以受限键类为定义域。 -/
theorem textbookEBoundedRelation_isRelationOn_l (bound : ZFSet.{u}) :
    IsRelationOn (TextbookEBoundedDomain_l bound)
      (TextbookEBoundedRelation_l bound) := by
  intro assignment hAssignment coordinate
  fin_cases coordinate
  · exact hAssignment.1
  · exact hAssignment.2.1

/-- 受限关系继承完整教材关系的集合最小元性质。 -/
theorem textbookEBoundedRelation_hasSetMinimaOn_l
    {bound : ZFSet.{u}} (hbound : bound ⊆ textbookEOmegaZF) :
    HasSetMinimaOn (TextbookEBoundedDomain_l bound)
      (TextbookEBoundedRelation_l bound) := by
  intro set hSetDomain hSetNonempty
  have hSetTextbook : ∀ x, x ∈ set → x ∈ TextbookEDomain := by
    intro x hx
    rcases ZFSet.mem_prod.mp (hSetDomain x hx) with
      ⟨code, hCode, arity, _hArity, rfl⟩
    exact mem_textbookEDomain_iff.mpr
      ⟨code, hCode, arity,
        hbound _hArity,
        rfl⟩
  rcases textbookERelation_hasSetMinimaOn set hSetTextbook hSetNonempty with
    ⟨minimum, hMinimum, hMinimal⟩
  refine ⟨minimum, hMinimum, ?_⟩
  intro predecessor hPredecessor hRelation
  exact hMinimal predecessor hPredecessor
    ((classRel_textbookEBoundedRelation_iff_l bound _ _).mp hRelation).2.2

/--
在受限键 `<m,n>` 处，全部直接前驱正好组成 `m × bound`。
-/
theorem textbookEBounded_predecessorSet_l
    {bound m n : ZFSet.{u}}
    (hm : m ∈ textbookEOmegaZF) (hn : n ∈ bound)
    (hbound : bound ⊆ textbookEOmegaZF) :
    IsPredecessorSet (TextbookEBoundedDomain_l bound)
      (TextbookEBoundedRelation_l bound)
      (ZFSet.pair m n) (ZFSet.prod m bound) := by
  intro predecessor
  constructor
  · intro hPredecessor
    rcases ZFSet.mem_prod.mp hPredecessor with
      ⟨code, hCode, arity, hArity, rfl⟩
    have hCodeOmega :=
      mem_textbookEOmega_of_mem_of_mem_textbookEOmega hCode hm
    have hArityOmega := hbound hArity
    refine ⟨?_, ?_⟩
    · exact ZFSet.mem_prod.mpr ⟨code, hCodeOmega, arity, hArity, rfl⟩
    · apply (classRel_textbookEBoundedRelation_iff_l bound _ _).mpr
      refine ⟨?_, ?_, ?_⟩
      · exact ZFSet.mem_prod.mpr ⟨code, hCodeOmega, arity, hArity, rfl⟩
      · exact ZFSet.mem_prod.mpr ⟨m, hm, n, hn, rfl⟩
      · apply (classRel_textbookERelation_iff _ _).mpr
        exact ⟨code, arity, m, n, hCodeOmega, hArityOmega,
          hm, hbound hn, rfl, rfl, hCode⟩
  · rintro ⟨hDomain, hRelation⟩
    have hTextbook :=
      (classRel_textbookEBoundedRelation_iff_l bound _ _).mp hRelation |>.2.2
    rcases (classRel_textbookERelation_iff _ _).mp hTextbook with
      ⟨code, arity, targetCode, targetArity,
        _hCodeOmega, _hArityOmega, _hTargetCodeOmega,
        _hTargetArityOmega, hPredecessorPair, hTargetPair, hCodeLt⟩
    have hTargetCoordinates := ZFSet.pair_inj.mp hTargetPair
    have hDomainCoordinates := ZFSet.mem_prod.mp hDomain
    rcases hDomainCoordinates with
      ⟨domainCode, _hDomainCode, domainArity, hDomainArity,
        hDomainPair⟩
    have hPredecessorCoordinates :=
      ZFSet.pair_inj.mp (hPredecessorPair.symm.trans hDomainPair)
    apply ZFSet.mem_prod.mpr
    refine ⟨domainCode, ?_, domainArity, hDomainArity, hDomainPair⟩
    simpa only [hPredecessorCoordinates.1, hTargetCoordinates.1] using hCodeLt

/-- 受限关系的每个点都有显式前驱集。 -/
theorem textbookEBoundedRelation_hasSetPredecessorsOn_l
    {bound : ZFSet.{u}} (hbound : bound ⊆ textbookEOmegaZF) :
    HasSetPredecessorsOn (TextbookEBoundedDomain_l bound)
      (TextbookEBoundedRelation_l bound) := by
  intro key hKey
  rcases ZFSet.mem_prod.mp hKey with
    ⟨m, hm, n, hn, rfl⟩
  exact ⟨ZFSet.prod m bound,
    textbookEBounded_predecessorSet_l hm hn hbound⟩

/-- 有限元数限制后的教材关系仍是良基且 set-like 的。 -/
theorem textbookEBoundedRelation_isWellFoundedSetLikeOn_l
    {bound : ZFSet.{u}} (hbound : bound ⊆ textbookEOmegaZF) :
    IsWellFoundedSetLikeOn (TextbookEBoundedDomain_l bound)
      (TextbookEBoundedRelation_l bound) :=
  ⟨textbookEBoundedRelation_isRelationOn_l bound,
    textbookEBoundedRelation_hasSetMinimaOn_l hbound,
    textbookEBoundedRelation_hasSetPredecessorsOn_l hbound⟩

/-- 受限教材关系仍具有传递性。 -/
theorem textbookEBoundedRelation_transitive_l
    {bound left middle right : ZFSet.{u}}
    (hLeftMiddle : ClassRel (TextbookEBoundedRelation_l bound) left middle)
    (hMiddleRight : ClassRel (TextbookEBoundedRelation_l bound) middle right) :
    ClassRel (TextbookEBoundedRelation_l bound) left right := by
  rw [classRel_textbookEBoundedRelation_iff_l] at hLeftMiddle hMiddleRight ⊢
  exact ⟨hLeftMiddle.1, hMiddleRight.2.1,
    textbookERelation_transitive hLeftMiddle.2.2 hMiddleRight.2.2⟩

/-- 受限关系的任意有限前驱层已经包含在第一层 `m × bound` 中。 -/
private theorem textbookEBounded_predecessorLayer_subset_first_l
    {bound m n : ZFSet.{u}}
    (hm : m ∈ textbookEOmegaZF) (hn : n ∈ bound)
    (hbound : bound ⊆ textbookEOmegaZF) :
    ∀ stage : Nat,
      predecessorLayer (TextbookEBoundedDomain_l bound)
          (TextbookEBoundedRelation_l bound)
          (textbookEBoundedRelation_hasSetPredecessorsOn_l hbound)
          (ZFSet.pair m n) stage ⊆
        ZFSet.prod m bound := by
  intro stage
  induction stage with
  | zero =>
      intro key hKey
      rw [predecessorLayer_zero] at hKey
      exact (textbookEBounded_predecessorSet_l hm hn hbound key).mpr
        ((displayedPredecessors_spec
          (textbookEBoundedRelation_hasSetPredecessorsOn_l hbound)
          (ZFSet.mem_prod.mpr ⟨m, hm, n, hn, rfl⟩) key).mp hKey)
  | succ stage inductionHypothesis =>
      intro key hKey
      rcases (mem_predecessorLayer_succ_iff
          (textbookEBoundedRelation_hasSetPredecessorsOn_l hbound)
          (ZFSet.mem_prod.mpr ⟨m, hm, n, hn, rfl⟩) stage).mp hKey with
        ⟨middle, hMiddle, hKeyDomain, hKeyMiddle⟩
      have hMiddleFirst := inductionHypothesis hMiddle
      have hMiddleSpec :=
        (textbookEBounded_predecessorSet_l hm hn hbound middle).mp
          hMiddleFirst
      apply (textbookEBounded_predecessorSet_l hm hn hbound key).mpr
      exact ⟨hKeyDomain,
        textbookEBoundedRelation_transitive_l hKeyMiddle hMiddleSpec.2⟩

/-- 受限关系的全部有限前驱闭包等于第一前驱集。 -/
theorem textbookEBounded_predecessorClosure_eq_l
    {bound m n : ZFSet.{u}}
    (hm : m ∈ textbookEOmegaZF) (hn : n ∈ bound)
    (hbound : bound ⊆ textbookEOmegaZF) :
    predecessorClosure (TextbookEBoundedDomain_l bound)
        (TextbookEBoundedRelation_l bound)
        (textbookEBoundedRelation_hasSetPredecessorsOn_l hbound)
        (ZFSet.pair m n) =
      ZFSet.prod m bound := by
  apply ZFSet.ext
  intro key
  constructor
  · intro hKey
    rcases mem_predecessorClosure_iff.mp hKey with ⟨stage, hStage⟩
    exact textbookEBounded_predecessorLayer_subset_first_l
      hm hn hbound stage hStage
  · intro hKey
    apply mem_predecessorClosure_iff.mpr
    refine ⟨0, ?_⟩
    rw [predecessorLayer_zero]
    apply (displayedPredecessors_spec
      (textbookEBoundedRelation_hasSetPredecessorsOn_l hbound)
      (ZFSet.mem_prod.mpr ⟨m, hm, n, hn, rfl⟩) key).mpr
    exact (textbookEBounded_predecessorSet_l hm hn hbound key).mp hKey

/-- 标准有限序数乘积在外部是有限集合。 -/
theorem textbookNatCodeProduct_externallyFinite_l (left right : Nat) :
    (ZFSet.prod (natCode left : ZFSet.{u}) (natCode right) :
      Set ZFSet.{u}).Finite := by
  let enumerate : Fin left × Fin right → ZFSet.{u} :=
    fun index => ZFSet.pair (natCode index.1.1) (natCode index.2.1)
  apply (Set.finite_range enumerate).subset
  intro key hKey
  rcases ZFSet.mem_prod.mp hKey with
    ⟨leftCode, hLeftCode, rightCode, hRightCode, rfl⟩
  rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt leftCode left).mp
      hLeftCode with ⟨leftIndex, hLeftIndex, rfl⟩
  rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt rightCode right).mp
      hRightCode with ⟨rightIndex, hRightIndex, rfl⟩
  exact ⟨(⟨leftIndex, hLeftIndex⟩, ⟨rightIndex, hRightIndex⟩), rfl⟩

/-- 标准有限界处的规范局部递归域在外部有限。 -/
theorem textbookEBounded_localRecursionDomain_externallyFinite_l
    (m n bound : Nat) (hn : n < bound) :
    (localRecursionDomain
        (TextbookEBoundedDomain_l (natCode bound : ZFSet.{u}))
        (TextbookEBoundedRelation_l (natCode bound : ZFSet.{u}))
        (textbookEBoundedRelation_hasSetPredecessorsOn_l
          (fun _ h => mem_textbookEOmega_of_mem_of_mem_textbookEOmega h
            ((IndexedSequenceZF.mem_omega_iff_exists_natCode
              (natCode bound : ZFSet.{u})).mpr ⟨bound, rfl⟩)))
        (ZFSet.pair (natCode m : ZFSet.{u}) (natCode n)) :
      Set ZFSet.{u}).Finite := by
  have hmOmega : (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF :=
    (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨m, rfl⟩
  have hnBound : (natCode n : ZFSet.{u}) ∈ natCode bound :=
    (IndexedSequenceZF.mem_natCode_iff_exists_lt _ _).mpr ⟨n, hn, rfl⟩
  have hbound : (natCode bound : ZFSet.{u}) ⊆ textbookEOmegaZF := by
    intro code hCode
    exact mem_textbookEOmega_of_mem_of_mem_textbookEOmega hCode
      ((IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨bound, rfl⟩)
  rw [localRecursionDomain, textbookEBounded_predecessorClosure_eq_l
    hmOmega hnBound hbound]
  have hCoe :
      (({ZFSet.pair (natCode m) (natCode n)} ∪
          ZFSet.prod (natCode m) (natCode bound) : ZFSet.{u}) :
        Set ZFSet.{u}) =
      ({ZFSet.pair (natCode m) (natCode n)} : Set ZFSet.{u}) ∪
        (ZFSet.prod (natCode m) (natCode bound) : Set ZFSet.{u}) := by
    ext key
    simp
  rw [hCoe]
  exact (Set.finite_singleton _).union
    (textbookNatCodeProduct_externallyFinite_l m bound)

/-- 标准有限界处的规范局部递归域属于同一个后继极限层。 -/
theorem textbookEBounded_localRecursionDomain_mem_LStageZF_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (m n bound : Nat) (hn : n < bound) :
    localRecursionDomain
        (TextbookEBoundedDomain_l (natCode bound : ZFSet.{u}))
        (TextbookEBoundedRelation_l (natCode bound : ZFSet.{u}))
        (textbookEBoundedRelation_hasSetPredecessorsOn_l
          (fun _ h => mem_textbookEOmega_of_mem_of_mem_textbookEOmega h
            ((IndexedSequenceZF.mem_omega_iff_exists_natCode
              (natCode bound : ZFSet.{u})).mpr ⟨bound, rfl⟩)))
        (ZFSet.pair (natCode m : ZFSet.{u}) (natCode n)) ∈
      LStageZF θ := by
  have hmOmega : (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF :=
    (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨m, rfl⟩
  have hnBound : (natCode n : ZFSet.{u}) ∈ natCode bound :=
    (IndexedSequenceZF.mem_natCode_iff_exists_lt _ _).mpr ⟨n, hn, rfl⟩
  have hbound : (natCode bound : ZFSet.{u}) ⊆ textbookEOmegaZF := by
    intro code hCode
    exact mem_textbookEOmega_of_mem_of_mem_textbookEOmega hCode
      ((IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨bound, rfl⟩)
  rw [localRecursionDomain, textbookEBounded_predecessorClosure_eq_l
    hmOmega hnBound hbound]
  have hCodeStage : (natCode m : ZFSet.{u}) ∈ LStageZF θ :=
    natCode_mem_LStageZF_of_isSuccLimit hθ m
  have hArityStage : (natCode n : ZFSet.{u}) ∈ LStageZF θ :=
    natCode_mem_LStageZF_of_isSuccLimit hθ n
  have hBoundStage : (natCode bound : ZFSet.{u}) ∈ LStageZF θ :=
    natCode_mem_LStageZF_of_isSuccLimit hθ bound
  have hTargetStage : ZFSet.pair (natCode m) (natCode n) ∈ LStageZF θ :=
    orderedPair_mem_LStageZF_of_isSuccLimit hθ hCodeStage hArityStage
  have hProductStage : ZFSet.prod (natCode m) (natCode bound) ∈
      LStageZF θ := by
    simpa [Godel.op, Godel.F2] using
      (Godel.op_mem_LStageZF_of_isSuccLimit
        hθ (i := (2 : Fin 9)) hCodeStage hBoundStage)
  exact union_mem_LStageZF_of_isSuccLimit hθ
    (singleton_mem_LStageZF_of_isSuccLimit hθ hTargetStage) hProductStage

/-- 受限域中任一点的规范前驱集仍属于当前后继极限层。 -/
theorem textbookEBounded_displayedPredecessors_mem_LStageZF_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {bound key : ZFSet.{u}}
    (hBoundStage : bound ∈ LStageZF θ)
    (hbound : bound ⊆ textbookEOmegaZF)
    (hKey : key ∈ TextbookEBoundedDomain_l bound) :
    displayedPredecessors
        (TextbookEBoundedDomain_l bound)
        (TextbookEBoundedRelation_l bound)
        (textbookEBoundedRelation_hasSetPredecessorsOn_l hbound) key ∈
      LStageZF θ := by
  rcases ZFSet.mem_prod.mp hKey with ⟨m, hm, n, hn, rfl⟩
  have hPredecessors :
      displayedPredecessors
          (TextbookEBoundedDomain_l bound)
          (TextbookEBoundedRelation_l bound)
          (textbookEBoundedRelation_hasSetPredecessorsOn_l hbound)
          (ZFSet.pair m n) = ZFSet.prod m bound := by
    apply ZFSet.ext
    intro predecessor
    rw [displayedPredecessors_spec
      (textbookEBoundedRelation_hasSetPredecessorsOn_l hbound)
      (ZFSet.mem_prod.mpr ⟨m, hm, n, hn, rfl⟩)]
    exact (textbookEBounded_predecessorSet_l hm hn hbound predecessor).symm
  rw [hPredecessors]
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode m).mp hm with
    ⟨mCode, rfl⟩
  have hmStage : (natCode mCode : ZFSet.{u}) ∈ LStageZF θ :=
    natCode_mem_LStageZF_of_isSuccLimit hθ mCode
  simpa [Godel.op, Godel.F2] using
    (Godel.op_mem_LStageZF_of_isSuccLimit
      hθ (i := (2 : Fin 9)) hmStage hBoundStage)

/-- 标准有限元数界下的每个规范前驱集在外部有限。 -/
theorem textbookEBounded_displayedPredecessors_externallyFinite_l
    (bound : Nat) {key : ZFSet.{u}}
    (hKey : key ∈ TextbookEBoundedDomain_l (natCode bound)) :
    (displayedPredecessors
        (TextbookEBoundedDomain_l (natCode bound : ZFSet.{u}))
        (TextbookEBoundedRelation_l (natCode bound : ZFSet.{u}))
        (textbookEBoundedRelation_hasSetPredecessorsOn_l
          (fun _ h => mem_textbookEOmega_of_mem_of_mem_textbookEOmega h
            ((IndexedSequenceZF.mem_omega_iff_exists_natCode
              (natCode bound : ZFSet.{u})).mpr ⟨bound, rfl⟩))) key :
      Set ZFSet.{u}).Finite := by
  let hbound : (natCode bound : ZFSet.{u}) ⊆ textbookEOmegaZF := by
    intro arity hArity
    exact mem_textbookEOmega_of_mem_of_mem_textbookEOmega hArity
      ((IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨bound, rfl⟩)
  rcases ZFSet.mem_prod.mp hKey with ⟨m, hm, n, hn, rfl⟩
  have hPredecessors :
      displayedPredecessors
          (TextbookEBoundedDomain_l (natCode bound : ZFSet.{u}))
          (TextbookEBoundedRelation_l (natCode bound : ZFSet.{u}))
          (textbookEBoundedRelation_hasSetPredecessorsOn_l hbound)
          (ZFSet.pair m n) = ZFSet.prod m (natCode bound) := by
    apply ZFSet.ext
    intro predecessor
    rw [displayedPredecessors_spec
      (textbookEBoundedRelation_hasSetPredecessorsOn_l hbound)
      (ZFSet.mem_prod.mpr ⟨m, hm, n, hn, rfl⟩)]
    exact (textbookEBounded_predecessorSet_l hm hn hbound predecessor).symm
  rw [hPredecessors]
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode m).mp hm with
    ⟨mCode, rfl⟩
  exact textbookNatCodeProduct_externallyFinite_l mCode bound

/--
有限元数截断上的任意教材局部解，其定义域内全部值仍位于原后继极限层。
证明按代码坐标强归纳；每一步的前驱图有限，因此只需有限插入闭包。
-/
theorem textbookEBoundedLocalSolution_value_mem_LStageZF_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {a : ZFSet.{u}} (ha : a ∈ LStageZF θ)
    (m n bound : Nat) (hn : n < bound)
    (solution : TextbookLocalSolution
      (TextbookEBoundedDomain_l (natCode bound : ZFSet.{u}))
      (TextbookEBoundedRelation_l (natCode bound : ZFSet.{u}))
      (textbookEBoundedRelation_hasSetPredecessorsOn_l
        (fun _ h => mem_textbookEOmega_of_mem_of_mem_textbookEOmega h
          ((IndexedSequenceZF.mem_omega_iff_exists_natCode
            (natCode bound : ZFSet.{u})).mpr ⟨bound, rfl⟩)))
      (textbookEStep a)
      (ZFSet.pair (natCode m : ZFSet.{u}) (natCode n))) :
    ∀ key, key ∈ localRecursionDomain
        (TextbookEBoundedDomain_l (natCode bound : ZFSet.{u}))
        (TextbookEBoundedRelation_l (natCode bound : ZFSet.{u}))
        (textbookEBoundedRelation_hasSetPredecessorsOn_l
          (fun _ h => mem_textbookEOmega_of_mem_of_mem_textbookEOmega h
            ((IndexedSequenceZF.mem_omega_iff_exists_natCode
              (natCode bound : ZFSet.{u})).mpr ⟨bound, rfl⟩)))
        (ZFSet.pair (natCode m : ZFSet.{u}) (natCode n)) →
      solution.value key ∈ LStageZF θ := by
  let hbound : (natCode bound : ZFSet.{u}) ⊆ textbookEOmegaZF := by
    intro arity hArity
    exact mem_textbookEOmega_of_mem_of_mem_textbookEOmega hArity
      ((IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨bound, rfl⟩)
  let hRelation := textbookEBoundedRelation_isWellFoundedSetLikeOn_l hbound
  have hTarget : ZFSet.pair (natCode m : ZFSet.{u}) (natCode n) ∈
      TextbookEBoundedDomain_l (natCode bound) := by
    apply ZFSet.mem_prod.mpr
    exact ⟨natCode m,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨m, rfl⟩,
      natCode n,
      (IndexedSequenceZF.mem_natCode_iff_exists_lt _ _).mpr ⟨n, hn, rfl⟩,
      rfl⟩
  have hByCode : ∀ code : Nat, ∀ arity : Nat,
      ZFSet.pair (natCode code : ZFSet.{u}) (natCode arity) ∈
          localRecursionDomain
            (TextbookEBoundedDomain_l (natCode bound : ZFSet.{u}))
            (TextbookEBoundedRelation_l (natCode bound : ZFSet.{u}))
            hRelation.2.2
            (ZFSet.pair (natCode m : ZFSet.{u}) (natCode n)) →
        solution.value (ZFSet.pair (natCode code) (natCode arity)) ∈
          LStageZF θ := by
    intro code
    induction code using Nat.strong_induction_on with
    | h code inductionHypothesis =>
      intro arity hKeyLocal
      have hKeyDomain := localRecursionDomain_subset
        hRelation.2.2 hTarget hKeyLocal
      have hPredecessorsStage :=
        textbookEBounded_displayedPredecessors_mem_LStageZF_l
          hθ (natCode_mem_LStageZF_of_isSuccLimit hθ bound) hbound hKeyDomain
      have hPredecessorsFinite :=
        textbookEBounded_displayedPredecessors_externallyFinite_l
          bound hKeyDomain
      have hHistoryStage :
          predecessorRestrictionGraph
              (displayedPredecessors
                (TextbookEBoundedDomain_l (natCode bound : ZFSet.{u}))
                (TextbookEBoundedRelation_l (natCode bound : ZFSet.{u}))
                hRelation.2.2
                (ZFSet.pair (natCode code) (natCode arity)))
              solution.value ∈ LStageZF θ := by
        apply predecessorRestrictionGraph_mem_LStageZF_of_finite_l
          hθ hPredecessorsStage hPredecessorsFinite
        intro predecessor hPredecessor
        have hPredecessorSpec :=
          (displayedPredecessors_spec hRelation.2.2 hKeyDomain predecessor).mp
            hPredecessor
        rcases ZFSet.mem_prod.mp hPredecessorSpec.1 with
          ⟨predecessorCode, hPredecessorCodeOmega,
            predecessorArity, hPredecessorArityBound, hPredecessorPair⟩
        rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode
          predecessorCode).mp hPredecessorCodeOmega with
          ⟨predecessorCodeNat, rfl⟩
        rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt
          predecessorArity bound).mp hPredecessorArityBound with
          ⟨predecessorArityNat, _hPredecessorArity, rfl⟩
        have hCodeLt : predecessorCodeNat < code := by
          have hTextbook :=
            (classRel_textbookEBoundedRelation_iff_l
              (natCode bound : ZFSet.{u}) _ _).mp hPredecessorSpec.2 |>.2.2
          rw [classRel_textbookERelation_iff] at hTextbook
          rcases hTextbook with
            ⟨leftCode, leftArity, rightCode, rightArity,
              _hLeftCode, _hLeftArity, _hRightCode, _hRightArity,
              hLeftPair, hRightPair, hMembership⟩
          have hLeftCoordinates := ZFSet.pair_inj.mp
            (hLeftPair.symm.trans hPredecessorPair)
          have hRightCoordinates := ZFSet.pair_inj.mp hRightPair
          have hCodes : (natCode predecessorCodeNat : ZFSet.{u}) ∈
              natCode code := by
            simpa only [hLeftCoordinates.1, hRightCoordinates.1] using
              hMembership
          exact (natCode_mem_natCode_iff _ _).mp hCodes
        have hPredecessorLocal := localRecursionDomain_predecessorClosed
          hRelation.1 hRelation.2.2 hTarget hKeyLocal hPredecessorSpec.2
        subst predecessor
        exact inductionHypothesis predecessorCodeNat hCodeLt
          predecessorArityNat hPredecessorLocal
      rw [solution.satisfies _ hKeyLocal]
      exact textbookEStep_mem_LStageZF_l hθ ha hHistoryStage
        (textbookEBoundedDomain_subset_textbookEDomain_l hbound hKeyDomain)
  intro key hKeyLocal
  have hKeyDomain := localRecursionDomain_subset
    hRelation.2.2 hTarget hKeyLocal
  rcases ZFSet.mem_prod.mp hKeyDomain with
    ⟨code, hCodeOmega, arity, hArityBound, hKeyPair⟩
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode code).mp
      hCodeOmega with ⟨codeNat, rfl⟩
  rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt arity bound).mp
      hArityBound with ⟨arityNat, _hArityNat, rfl⟩
  subst key
  exact hByCode codeNat arityNat hKeyLocal

/-- 有限元数截断上的任意教材局部解图属于同一个后继极限层。 -/
theorem textbookEBoundedLocalSolution_graph_mem_LStageZF_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {a : ZFSet.{u}} (ha : a ∈ LStageZF θ)
    (m n bound : Nat) (hn : n < bound)
    (solution : TextbookLocalSolution
      (TextbookEBoundedDomain_l (natCode bound : ZFSet.{u}))
      (TextbookEBoundedRelation_l (natCode bound : ZFSet.{u}))
      (textbookEBoundedRelation_hasSetPredecessorsOn_l
        (fun _ h => mem_textbookEOmega_of_mem_of_mem_textbookEOmega h
          ((IndexedSequenceZF.mem_omega_iff_exists_natCode
            (natCode bound : ZFSet.{u})).mpr ⟨bound, rfl⟩)))
      (textbookEStep a)
      (ZFSet.pair (natCode m : ZFSet.{u}) (natCode n))) :
    solution.graph ∈ LStageZF θ := by
  rw [solution.graph_eq]
  apply predecessorRestrictionGraph_mem_LStageZF_of_finite_l hθ
    (textbookEBounded_localRecursionDomain_mem_LStageZF_l hθ m n bound hn)
    (textbookEBounded_localRecursionDomain_externallyFinite_l m n bound hn)
  exact textbookEBoundedLocalSolution_value_mem_LStageZF_l
    hθ ha m n bound hn solution

/-! ## 截断局部解在安全锥中的正确性 -/

/-- 限制函数图在定义域成员处的唯一查询就是原函数值。 -/
theorem uniqueGraphLookupZF_predecessorRestrictionGraph_l
    (domain : ZFSet.{u}) (value : ZFSet.{u} → ZFSet.{u})
    {key : ZFSet.{u}} (hKey : key ∈ domain) :
    uniqueGraphLookupZF (predecessorRestrictionGraph domain value) key =
      value key := by
  apply uniqueGraphLookupZF_eq_of_unique
  · exact pair_mem_predecessorRestrictionGraph value hKey
  · intro other hOther
    rcases mem_predecessorRestrictionGraph_iff.mp hOther with
      ⟨source, _hSource, hPair⟩
    have hCoordinates := ZFSet.pair_inj.mp hPair
    rw [hCoordinates.1] at hCoordinates
    exact hCoordinates.2.symm

/-- 较小代码与界内元数编码的键属于当前键的规范前驱集。 -/
theorem textbookEBounded_earlierKey_mem_predecessors_l
    (bound code arity childCode childArity : Nat)
    (hCode : childCode < code) (hTargetArity : arity < bound)
    (hArity : childArity < bound) :
    ZFSet.pair (natCode childCode : ZFSet.{u}) (natCode childArity) ∈
      displayedPredecessors
        (TextbookEBoundedDomain_l (natCode bound : ZFSet.{u}))
        (TextbookEBoundedRelation_l (natCode bound : ZFSet.{u}))
        (textbookEBoundedRelation_hasSetPredecessorsOn_l
          (fun _ h => mem_textbookEOmega_of_mem_of_mem_textbookEOmega h
            ((IndexedSequenceZF.mem_omega_iff_exists_natCode
              (natCode bound : ZFSet.{u})).mpr ⟨bound, rfl⟩)))
        (ZFSet.pair (natCode code) (natCode arity)) := by
  let hbound : (natCode bound : ZFSet.{u}) ⊆ textbookEOmegaZF := by
    intro value hValue
    exact mem_textbookEOmega_of_mem_of_mem_textbookEOmega hValue
      ((IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨bound, rfl⟩)
  have hTarget : ZFSet.pair (natCode code : ZFSet.{u}) (natCode arity) ∈
      TextbookEBoundedDomain_l (natCode bound) := by
    apply ZFSet.mem_prod.mpr
    exact ⟨natCode code,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨code, rfl⟩,
      natCode arity,
      (IndexedSequenceZF.mem_natCode_iff_exists_lt _ _).mpr
        ⟨arity, hTargetArity, rfl⟩,
      rfl⟩
  apply (displayedPredecessors_spec
    (textbookEBoundedRelation_hasSetPredecessorsOn_l hbound)
    hTarget _).mpr
  have hChildDomain :
      ZFSet.pair (natCode childCode : ZFSet.{u}) (natCode childArity) ∈
        TextbookEBoundedDomain_l (natCode bound) := by
    apply ZFSet.mem_prod.mpr
    exact ⟨natCode childCode,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
        ⟨childCode, rfl⟩,
      natCode childArity,
      (IndexedSequenceZF.mem_natCode_iff_exists_lt _ _).mpr
        ⟨childArity, hArity, rfl⟩,
      rfl⟩
  refine ⟨hChildDomain, ?_⟩
  apply (classRel_textbookEBoundedRelation_iff_l
    (natCode bound : ZFSet.{u}) _ _).mpr
  refine ⟨hChildDomain, hTarget, ?_⟩
  apply (classRel_textbookERelation_iff _ _).mpr
  exact ⟨natCode childCode, natCode childArity,
    natCode code, natCode arity,
    (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
      ⟨childCode, rfl⟩,
    (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
      ⟨childArity, rfl⟩,
    (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
      ⟨code, rfl⟩,
    (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
      ⟨arity, rfl⟩,
    rfl, rfl, (natCode_mem_natCode_iff _ _).mpr hCode⟩

/-- 教材编码的第二个子码也严格小于整个构造器码。 -/
theorem textbookECode_right_lt_l (left right tag : Nat) :
    right < textbookECode left right tag := by
  apply lt_of_lt_of_le
    (lt_of_lt_of_le right.lt_two_pow_self
      (Nat.pow_le_pow_left (by decide : 2 ≤ 3) right))
  simp only [textbookECode]
  have hTwo : 0 < 2 ^ left := Nat.pow_pos (by decide)
  have hFive : 0 < 5 ^ tag := Nat.pow_pos (by decide)
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    Nat.le_mul_of_pos_left (3 ^ right) (Nat.mul_pos hTwo hFive)

/--
截断局部解在安全锥 `arity + code < bound` 内与完整 textbook E 递归一致。
元数每次最多增加一，而代码严格下降，所以该不变量在所有真实依赖上保持。
-/
theorem textbookEBoundedLocalSolution_eq_textbookEZF_of_add_lt_l
    {a : ZFSet.{u}} (m n bound : Nat) (hn : n < bound)
    (solution : TextbookLocalSolution
      (TextbookEBoundedDomain_l (natCode bound : ZFSet.{u}))
      (TextbookEBoundedRelation_l (natCode bound : ZFSet.{u}))
      (textbookEBoundedRelation_hasSetPredecessorsOn_l
        (fun _ h => mem_textbookEOmega_of_mem_of_mem_textbookEOmega h
          ((IndexedSequenceZF.mem_omega_iff_exists_natCode
            (natCode bound : ZFSet.{u})).mpr ⟨bound, rfl⟩)))
      (textbookEStep a)
      (ZFSet.pair (natCode m : ZFSet.{u}) (natCode n))) :
    ∀ code arity,
      ZFSet.pair (natCode code : ZFSet.{u}) (natCode arity) ∈
          localRecursionDomain
            (TextbookEBoundedDomain_l (natCode bound : ZFSet.{u}))
            (TextbookEBoundedRelation_l (natCode bound : ZFSet.{u}))
            (textbookEBoundedRelation_hasSetPredecessorsOn_l
              (fun _ h => mem_textbookEOmega_of_mem_of_mem_textbookEOmega h
                ((IndexedSequenceZF.mem_omega_iff_exists_natCode
                  (natCode bound : ZFSet.{u})).mpr ⟨bound, rfl⟩)))
            (ZFSet.pair (natCode m : ZFSet.{u}) (natCode n)) →
      arity + code < bound →
      solution.value (ZFSet.pair (natCode code) (natCode arity)) =
        textbookEZF a (natCode arity) (natCode code) := by
  let hbound : (natCode bound : ZFSet.{u}) ⊆ textbookEOmegaZF := by
    intro value hValue
    exact mem_textbookEOmega_of_mem_of_mem_textbookEOmega hValue
      ((IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨bound, rfl⟩)
  let hRelation := textbookEBoundedRelation_isWellFoundedSetLikeOn_l hbound
  have hTarget : ZFSet.pair (natCode m : ZFSet.{u}) (natCode n) ∈
      TextbookEBoundedDomain_l (natCode bound) := by
    apply ZFSet.mem_prod.mpr
    exact ⟨natCode m,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨m, rfl⟩,
      natCode n,
      (IndexedSequenceZF.mem_natCode_iff_exists_lt _ _).mpr ⟨n, hn, rfl⟩,
      rfl⟩
  intro code
  induction code using Nat.strong_induction_on with
  | h code inductionHypothesis =>
    intro arity hKeyLocal hSafe
    let history := predecessorRestrictionGraph
      (displayedPredecessors
        (TextbookEBoundedDomain_l (natCode bound : ZFSet.{u}))
        (TextbookEBoundedRelation_l (natCode bound : ZFSet.{u}))
        hRelation.2.2
        (ZFSet.pair (natCode code) (natCode arity)))
      solution.value
    have hTargetArity : arity < bound := by omega
    have childLookup (childCode childArity : Nat)
        (hChildCode : childCode < code)
        (hChildSafe : childArity + childCode < bound) :
        uniqueGraphLookupZF history
            (ZFSet.pair (natCode childCode) (natCode childArity)) =
          textbookEZF a (natCode childArity) (natCode childCode) := by
      have hChildArity : childArity < bound := by omega
      have hChildPredecessor :=
        textbookEBounded_earlierKey_mem_predecessors_l
          bound code arity childCode childArity
          hChildCode hTargetArity hChildArity
      rw [uniqueGraphLookupZF_predecessorRestrictionGraph_l _ _
        hChildPredecessor]
      apply inductionHypothesis childCode hChildCode childArity
      · exact localRecursionDomain_predecessorClosed
          hRelation.1 hRelation.2.2 hTarget hKeyLocal
          ((displayedPredecessors_spec hRelation.2.2
            (localRecursionDomain_subset hRelation.2.2 hTarget hKeyLocal)
            _).mp hChildPredecessor).2
      · exact hChildSafe
    rw [solution.satisfies _ hKeyLocal]
    change textbookEStep a
        (ZFSet.pair (natCode code) (natCode arity)) history = _
    cases hDecode : textbookEDecode code with
    | none =>
        rw [textbookEZF_eq_empty_of_decode_none a arity code hDecode]
        simp [textbookEStep, hDecode]
    | some fields =>
        rcases fields with ⟨left, right, tag⟩
        have hFields := (textbookEDecode_eq_some_iff code left right tag).mp
          hDecode
        rcases hFields with ⟨hTag, hCode⟩
        subst code
        rcases (show tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 by
          omega) with rfl | rfl | rfl | rfl | rfl
        · by_cases hLeft : left < arity
          · by_cases hRight : right < arity
            · rw [textbookEStep_code_zero a history arity left right
                hLeft hRight,
                textbookEZF_code_zero a arity left right hLeft hRight]
            · rw [textbookEStep_code_zero_eq_empty_of_not_lt_right
                a history arity left right hRight,
                textbookEZF_code_zero_eq_empty_of_not_lt_right
                  a arity left right hRight]
          · rw [textbookEStep_code_zero_eq_empty_of_not_lt_left
              a history arity left right hLeft,
              textbookEZF_code_zero_eq_empty_of_not_lt_left
                a arity left right hLeft]
        · by_cases hLeft : left < arity
          · by_cases hRight : right < arity
            · rw [textbookEStep_code_one a history arity left right
                hLeft hRight,
                textbookEZF_code_one a arity left right hLeft hRight]
            · rw [textbookEStep_code_one_eq_empty_of_not_lt_right
                a history arity left right hRight,
                textbookEZF_code_one_eq_empty_of_not_lt_right
                  a arity left right hRight]
          · rw [textbookEStep_code_one_eq_empty_of_not_lt_left
              a history arity left right hLeft,
              textbookEZF_code_one_eq_empty_of_not_lt_left
                a arity left right hLeft]
        · rw [textbookEStep_code_two, textbookEZF_code_two]
          congr 1
          have hLeftCode : left < textbookECode left right 2 :=
            textbookECode_index_lt left right 2
          exact childLookup left arity
            hLeftCode (by omega)
        · rw [textbookEStep_code_three, textbookEZF_code_three]
          congr 1
          · have hLeftCode : left < textbookECode left right 3 :=
              textbookECode_index_lt left right 3
            exact childLookup left arity hLeftCode (by omega)
          · have hRightCode : right < textbookECode left right 3 :=
              textbookECode_right_lt_l left right 3
            exact childLookup right arity hRightCode (by omega)
        · rw [textbookEStep_code_four, textbookEZF_code_four]
          congr 1
          have hLeftCode : left < textbookECode left right 4 :=
            textbookECode_index_lt left right 4
          exact childLookup left (arity + 1)
            hLeftCode (by omega)

/-! ## 规范截断局部解 -/

/-- 标准有限序数界包含于教材自然数集合。 -/
theorem natCode_subset_textbookEOmega_l (bound : Nat) :
    (natCode bound : ZFSet.{u}) ⊆ textbookEOmegaZF := by
  intro arity hArity
  exact mem_textbookEOmega_of_mem_of_mem_textbookEOmega hArity
    ((IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨bound, rfl⟩)

/-- 标准目标键属于其有限元数截断域。 -/
theorem textbookEKey_mem_boundedDomain_l
    (code arity bound : Nat) (hArity : arity < bound) :
    ZFSet.pair (natCode code : ZFSet.{u}) (natCode arity) ∈
      TextbookEBoundedDomain_l (natCode bound) := by
  apply ZFSet.mem_prod.mpr
  exact ⟨natCode code,
    (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨code, rfl⟩,
    natCode arity,
    (IndexedSequenceZF.mem_natCode_iff_exists_lt _ _).mpr
      ⟨arity, hArity, rfl⟩,
    rfl⟩

/-- 在标准有限界上规范选择教材局部递归产生的解图。 -/
noncomputable def textbookEBoundedLocalSolution_l
    (a : ZFSet.{u}) (code arity bound : Nat) (hArity : arity < bound) :
    TextbookLocalSolution
      (TextbookEBoundedDomain_l (natCode bound : ZFSet.{u}))
      (TextbookEBoundedRelation_l (natCode bound : ZFSet.{u}))
      (textbookEBoundedRelation_hasSetPredecessorsOn_l
        (natCode_subset_textbookEOmega_l bound))
      (textbookEStep a)
      (ZFSet.pair (natCode code : ZFSet.{u}) (natCode arity)) :=
  Classical.choice (nonempty_textbookLocalSolution
    (textbookEBoundedRelation_isWellFoundedSetLikeOn_l
      (natCode_subset_textbookEOmega_l bound))
    (textbookEStep a)
    (ZFSet.pair (natCode code : ZFSet.{u}) (natCode arity))
    (textbookEKey_mem_boundedDomain_l code arity bound hArity))

/-- 规范截断解图属于包含参数的任意后继极限层。 -/
theorem textbookEBoundedLocalSolution_graph_mem_stage_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {a : ZFSet.{u}} (ha : a ∈ LStageZF θ)
    (code arity bound : Nat) (hArity : arity < bound) :
    (textbookEBoundedLocalSolution_l a code arity bound hArity).graph ∈
      LStageZF θ :=
  textbookEBoundedLocalSolution_graph_mem_LStageZF_l
    hθ ha code arity bound hArity
      (textbookEBoundedLocalSolution_l a code arity bound hArity)

/-- 安全界 `arity + code + 1` 下，规范截断解在目标键处就是完整 E 值。 -/
theorem textbookEBoundedLocalSolution_target_eq_l
    (a : ZFSet.{u}) (code arity : Nat) :
    (textbookEBoundedLocalSolution_l a code arity
        (arity + code + 1) (by omega)).value
        (ZFSet.pair (natCode code) (natCode arity)) =
      textbookEZF a (natCode arity) (natCode code) := by
  apply textbookEBoundedLocalSolution_eq_textbookEZF_of_add_lt_l
    code arity (arity + code + 1) (by omega)
      (textbookEBoundedLocalSolution_l a code arity
        (arity + code + 1) (by omega))
  · exact mem_localRecursionDomain_iff.mpr (Or.inl rfl)
  · omega

/-- 每个标准自然数码处的 textbook E 值都留在包含参数的后继极限层。 -/
theorem textbookEZF_mem_LStageZF_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {a : ZFSet.{u}} (ha : a ∈ LStageZF θ) (arity code : Nat) :
    textbookEZF a (natCode arity) (natCode code) ∈ LStageZF θ := by
  let solution := textbookEBoundedLocalSolution_l a code arity
    (arity + code + 1) (by omega)
  have hTargetLocal : ZFSet.pair (natCode code : ZFSet.{u}) (natCode arity) ∈
      localRecursionDomain
        (TextbookEBoundedDomain_l (natCode (arity + code + 1)))
        (TextbookEBoundedRelation_l (natCode (arity + code + 1)))
        (textbookEBoundedRelation_hasSetPredecessorsOn_l
          (natCode_subset_textbookEOmega_l (arity + code + 1)))
        (ZFSet.pair (natCode code) (natCode arity)) :=
    mem_localRecursionDomain_iff.mpr (Or.inl rfl)
  rw [← textbookEBoundedLocalSolution_target_eq_l a code arity]
  exact textbookEBoundedLocalSolution_value_mem_LStageZF_l
    hθ ha code arity (arity + code + 1) (by omega) solution
      (ZFSet.pair (natCode code) (natCode arity)) hTargetLocal

end

end YesMetaZFC.BMS.ConstructibleBridge
