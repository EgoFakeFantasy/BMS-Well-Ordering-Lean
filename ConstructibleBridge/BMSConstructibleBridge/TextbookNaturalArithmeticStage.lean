import BMSConstructibleBridge.TextbookLevyTraceBounds

/-!
# 有限自然数算术在可构造层中的绝对性

教科书公式用有限函数图证明加法、乘法、幂与素数幂编码。上游已经给出这些
公式在全体 `L` 中的语义；本文件补足反射论证真正需要的层版本。这里首先
隔离共同的低层闭包与标准 `omega` 语义，随后各级算术只需处理自己的有限图。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 严格越过 `omega` 的层包含标准 `omega` 本身。 -/
theorem omega_toZFSet_mem_stage_l {θ : Ordinal.{u}}
    (hω : Ordinal.omega0 < θ) :
    Ordinal.omega0.toZFSet ∈ LStageZF θ :=
  ordinal_toZFSet_mem_LStageZF_of_lt hω

/-- 严格越过 `omega` 的层包含每个标准自然数码。 -/
theorem natCode_mem_stage_l {θ : Ordinal.{u}}
    (hω : Ordinal.omega0 < θ) (n : Nat) :
    natCode n ∈ LStageZF θ :=
  ordinal_toZFSet_mem_LStageZF_of_lt
    ((Ordinal.natCast_lt_omega0 n).trans hω)

/-- 后继极限层对 von Neumann 后继封闭。 -/
theorem successor_mem_stage_l {θ : Ordinal.{u}}
    (hθ : Order.IsSuccLimit θ) {x : ZFSet.{u}}
    (hx : x ∈ LStageZF θ) :
    insert x x ∈ LStageZF θ := by
  rw [ZFSet.insert_eq]
  exact union_mem_LStageZF_of_isSuccLimit hθ
    (singleton_mem_LStageZF_of_isSuccLimit hθ hx) hx

private theorem satisfiesIn_all_stage_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (assignment : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.all formula) assignment ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        Model.SatisfiesIn M formula (snoc assignment x) := by
  classical
  simp [FOFormula.all, Model.SatisfiesIn]

private theorem satisfiesIn_imp_stage_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (assignment : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.imp left right) assignment ↔
      (Model.SatisfiesIn M left assignment →
        Model.SatisfiesIn M right assignment) := by
  classical
  simp only [FOFormula.imp, FOFormula.disj, Model.SatisfiesIn]
  tauto

private theorem satisfiesIn_boundedAll_stage_iff
    (M : Set ZFSet.{u}) {n : Nat} (set : Fin n)
    (formula : FOFormula (n + 1)) (assignment : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.boundedAll set formula) assignment ↔
      ∀ x : ZFSet.{u}, x ∈ M → x ∈ assignment set →
        Model.SatisfiesIn M formula (snoc assignment x) := by
  classical
  simp only [FOFormula.boundedAll, FOFormula.boundedEx,
    Model.SatisfiesIn]
  constructor
  · intro h x hxM hxSet
    by_contra hFormula
    exact h ⟨x, hxM, by simpa only [snoc_last, snoc_castSucc] using hxSet,
      hFormula⟩
  · rintro h ⟨x, hxM, hxSet, hFormula⟩
    exact hFormula (h x hxM (by
      simpa only [snoc_last, snoc_castSucc] using hxSet))

private theorem satisfiesIn_boundedEx_stage_iff
    (M : Set ZFSet.{u}) {n : Nat} (set : Fin n)
    (formula : FOFormula (n + 1)) (assignment : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.boundedEx set formula) assignment ↔
      ∃ x : ZFSet.{u}, x ∈ M ∧ x ∈ assignment set ∧
        Model.SatisfiesIn M formula (snoc assignment x) := by
  simp only [FOFormula.boundedEx, Model.SatisfiesIn]
  constructor <;> rintro ⟨x, hxM, hxSet, hFormula⟩ <;>
    exact ⟨x, hxM, by simpa only [snoc_last, snoc_castSucc] using hxSet,
      hFormula⟩

private theorem satisfiesIn_rename_stage_iff
    (M : Set ZFSet.{u}) {n m : Nat} (formula : FOFormula n)
    (rename : Fin n → Fin m) (assignment : Tuple ZFSet.{u} m) :
    Model.SatisfiesIn M (FOFormula.rename rename formula) assignment ↔
      Model.SatisfiesIn M formula (fun index => assignment (rename index)) := by
  induction formula generalizing m with
  | mem left right => rfl
  | eq left right => rfl
  | neg formula inductionHypothesis =>
      exact not_congr (inductionHypothesis rename assignment)
  | conj left right leftHypothesis rightHypothesis =>
      exact and_congr (leftHypothesis rename assignment)
        (rightHypothesis rename assignment)
  | ex formula inductionHypothesis =>
      simp only [FOFormula.rename, Model.SatisfiesIn, inductionHypothesis]
      constructor
      · rintro ⟨value, hValue, hFormula⟩
        refine ⟨value, hValue, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hFormula
      · rintro ⟨value, hValue, hFormula⟩
        refine ⟨value, hValue, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hFormula

/--
`standardOmegaAt` 在任意严格越过 `omega` 的后继极限层中仍唯一指定外部标准
`omega`。证明只用传递性、空集与后继闭包，不假设该层是 ZF 模型。
-/
theorem satisfiesIn_standardOmegaAt_stage_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) {n : Nat}
    (index : Fin n) (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ LStageZF θ) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Model.standardOmegaAt index) assignment ↔
      assignment index = Ordinal.omega0.toZFSet := by
  rw [Model.standardOmegaAt]
  simp only [Model.SatisfiesIn, satisfiesIn_all_stage_iff,
    satisfiesIn_imp_stage_iff, satisfiesIn_boundedAll_stage_iff,
    snoc_last, snoc_castSucc]
  have hTransitive : (LStageZF θ).IsTransitive :=
    LStageZF_isTransitive θ
  have hEmpty : (∅ : ZFSet.{u}) ∈ LStageZF θ :=
    empty_mem_LStageZF_of_isSuccLimit hθ
  have hSuccessor : ∀ {x : ZFSet.{u}}, x ∈ LStageZF θ →
      insert x x ∈ LStageZF θ :=
    fun {_} hx => successor_mem_stage_l hθ hx
  have hNaturals : ∀ k : Nat, (k : Ordinal.{u}).toZFSet ∈ LStageZF θ :=
    fun k => natCode_mem_stage_l hω k
  have hOmega : Ordinal.omega0.toZFSet ∈ LStageZF θ :=
    omega_toZFSet_mem_stage_l hω
  constructor
  · rintro ⟨hInductiveFormula, hMinimalFormula⟩
    have hInductive : Model.ZFInductiveSetIn
        (LStageZF θ) (assignment index) :=
      (Model.satisfiesIn_transitiveZFInductiveAt_iff hTransitive
        hEmpty (fun x hx => hSuccessor hx)
        index assignment hAssignment).mp hInductiveFormula
    have hMinimal : ∀ w : ZFSet.{u}, w ∈ LStageZF θ →
        Model.ZFInductiveSetIn (LStageZF θ) w → assignment index ⊆ w := by
      intro w hw hInductiveW x hx
      have hFormulaW :
          Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
            (Model.transitiveZFInductiveAt (Fin.last n))
            (snoc assignment w) := by
        apply (Model.satisfiesIn_transitiveZFInductiveAt_iff hTransitive
          hEmpty (fun z hz => hSuccessor hz)
          (Fin.last n) (snoc assignment w) (by
            intro position
            refine Fin.lastCases ?_ (fun earlier => ?_) position
            · simpa using hw
            · simpa using hAssignment earlier)).mpr
        simpa only [snoc_last] using hInductiveW
      exact hMinimalFormula w hw hFormulaW x
        (hTransitive.mem_trans hx (hAssignment index)) hx
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      exact hMinimal Ordinal.omega0.toZFSet hOmega
        (Model.omegaToZFSet_isInductiveSetIn (LStageZF θ)) hx
    · intro hx
      rcases Ordinal.mem_toZFSet_iff.mp hx with ⟨α, hα, rfl⟩
      rcases Ordinal.lt_omega0.mp hα with ⟨k, rfl⟩
      exact Model.natOrdinal_mem_of_ZFInductiveSetIn hInductive hNaturals k
  · intro hOmegaCode
    constructor
    · apply (Model.satisfiesIn_transitiveZFInductiveAt_iff hTransitive
        hEmpty (fun x hx => hSuccessor hx)
        index assignment hAssignment).mpr
      simpa only [hOmegaCode] using
        Model.omegaToZFSet_isInductiveSetIn (LStageZF θ)
    · intro w hw hFormulaW x hxStage hxOmega
      have hInductiveW : Model.ZFInductiveSetIn (LStageZF θ) w := by
        simpa only [snoc_last] using
          (Model.satisfiesIn_transitiveZFInductiveAt_iff hTransitive
            hEmpty (fun z hz => hSuccessor hz)
            (Fin.last n) (snoc assignment w) (by
              intro position
              refine Fin.lastCases ?_ (fun earlier => ?_) position
              · simpa using hw
              · simpa using hAssignment earlier)).mp hFormulaW
      rw [hOmegaCode] at hxOmega
      rcases Ordinal.mem_toZFSet_iff.mp hxOmega with ⟨α, hα, rfl⟩
      rcases Ordinal.lt_omega0.mp hα with ⟨k, rfl⟩
      exact Model.natOrdinal_mem_of_ZFInductiveSetIn hInductiveW hNaturals k

/-- 标准自然数值的有限元组图已经属于 `L_omega`。 -/
theorem textbookNatTupleGraph_mem_LStageOmega_l {n : Nat}
    (tuple : Tuple (ZFCarrier
      (Ordinal.omega0.toZFSet : ZFSet.{u})) n) :
    textbookTupleGraph tuple ∈ LStageZF Ordinal.omega0 := by
  induction n with
  | zero =>
      have hEmpty : textbookTupleGraph tuple = (∅ : ZFSet.{u}) := by
        apply ZFSet.eq_empty _ |>.mpr
        intro pair hPair
        rcases (mem_textbookTupleGraph_iff tuple).mp hPair with ⟨index, _⟩
        exact Fin.elim0 index
      rw [hEmpty]
      exact empty_mem_LStageZF_of_isSuccLimit Ordinal.isSuccLimit_omega0
  | succ n inductionHypothesis =>
      let initial : Tuple
          (ZFCarrier (Ordinal.omega0.toZFSet : ZFSet.{u})) n :=
        fun index => tuple index.castSucc
      let finalEntry : ZFCarrier
          (Ordinal.omega0.toZFSet : ZFSet.{u}) := tuple (Fin.last n)
      have hTuple : tuple = snoc initial finalEntry := by
        funext index
        refine Fin.lastCases ?_ (fun earlier => ?_) index
        · simp [finalEntry]
        · simp [initial]
      rw [hTuple, textbookTupleGraph_snoc, textbookTupleSnocGraph,
        ZFSet.insert_eq]
      apply union_mem_LStageZF_of_isSuccLimit Ordinal.isSuccLimit_omega0
      · apply singleton_mem_LStageZF_of_isSuccLimit Ordinal.isSuccLimit_omega0
        apply orderedPair_mem_LStageZF_of_isSuccLimit Ordinal.isSuccLimit_omega0
        · exact ordinal_toZFSet_mem_LStageZF_of_lt
            (Ordinal.natCast_lt_omega0 n)
        · rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode
            finalEntry.1).mp finalEntry.2 with
            ⟨value, hValue⟩
          rw [hValue]
          exact ordinal_toZFSet_mem_LStageZF_of_lt
            (Ordinal.natCast_lt_omega0 value)
      · exact inductionHypothesis initial

/-- 规范加法递归图已经在 `L_omega` 中出现。 -/
theorem natAddCanonicalGraph_mem_LStageOmega_l (a b : Nat) :
    TextbookNatFormula.natAddCanonicalGraph a b ∈
      LStageZF Ordinal.omega0 :=
  textbookNatTupleGraph_mem_LStageOmega_l
    (TextbookNatFormula.natAddCanonicalTuple a b)

/-- 严格越过 `omega` 的层包含规范加法递归图。 -/
theorem natAddCanonicalGraph_mem_stage_l {θ : Ordinal.{u}}
    (hω : Ordinal.omega0 < θ) (a b : Nat) :
    TextbookNatFormula.natAddCanonicalGraph a b ∈ LStageZF θ :=
  LStageZF_mono (le_of_lt hω)
    (natAddCanonicalGraph_mem_LStageOmega_l a b)

/--
教科书加法公式在任意严格越过 `omega` 的后继极限层中具有标准语义。
输出成员资格显式列出，供后续乘法递归逐项调用。
-/
theorem satisfiesIn_natAddFormula_stage_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (a b : Nat) {z : ZFSet.{u}}
    (hz : z ∈ LStageZF θ) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookNatFormula.natAddFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b, z] ↔
      z = natCode (a + b) := by
  let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
  let assignment : Tuple ZFSet.{u} 4 :=
    ![omega, natCode a, natCode b, z]
  have hOmega : omega ∈ LStageZF θ := omega_toZFSet_mem_stage_l hω
  have hA : (natCode a : ZFSet.{u}) ∈ LStageZF θ :=
    natCode_mem_stage_l hω a
  have hB : (natCode b : ZFSet.{u}) ∈ LStageZF θ :=
    natCode_mem_stage_l hω b
  have hAssignment : ∀ index, assignment index ∈ LStageZF θ := by
    intro index
    fin_cases index
    · exact hOmega
    · exact hA
    · exact hB
    · exact hz
  change
    ((Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Model.standardOmegaAt (0 : Fin 4)) assignment ∧
      (natCode a : ZFSet.{u}) ∈ omega ∧
      (natCode b : ZFSet.{u}) ∈ omega ∧
      z ∈ omega ∧
      ∃ successor, successor ∈ LStageZF θ ∧
        Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          (Delta0Formula.successorAt
            (Fin.last 4) (2 : Fin 4).castSucc).toFO
          (snoc assignment successor) ∧
        ∃ graph, graph ∈ LStageZF θ ∧
          Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
            TextbookNatFormula.natAddGraphDelta.toFO
            (snoc (snoc assignment successor) graph)) ↔ _)
  constructor
  · rintro ⟨hOmegaFormula, _, _, _, successor, hSuccessor,
      hSuccessorFormula, graph, hGraph, hGraphFormula⟩
    have _hOmegaCode : assignment (0 : Fin 4) =
        Ordinal.omega0.toZFSet :=
      (satisfiesIn_standardOmegaAt_stage_iff_l
        hθ hω (0 : Fin 4) assignment hAssignment).mp hOmegaFormula
    have hSuccessorAssignment : snoc assignment successor =
        ![omega, natCode a, natCode b, z, successor] := by
      funext index
      fin_cases index <;> rfl
    have hSuccessorAssignmentMem : ∀ index,
        snoc assignment successor index ∈ LStageZF θ := by
      rw [hSuccessorAssignment]
      intro index
      fin_cases index
      · exact hOmega
      · exact hA
      · exact hB
      · exact hz
      · exact hSuccessor
    have hSuccessorAmbient :=
      (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc assignment successor) hSuccessorAssignmentMem).mp
          hSuccessorFormula
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt,
      hSuccessorAssignment] at hSuccessorAmbient
    have hSuccessorCode : successor = natCode (b + 1) :=
      hSuccessorAmbient.trans (natCode_succ_eq_insert b).symm
    have hGraphAssignment : snoc (snoc assignment successor) graph =
        ![omega, natCode a, natCode b, z, successor, graph] := by
      funext index
      fin_cases index <;> rfl
    have hGraphAssignmentMem : ∀ index,
        snoc (snoc assignment successor) graph index ∈ LStageZF θ := by
      rw [hGraphAssignment]
      intro index
      fin_cases index
      · exact hOmega
      · exact hA
      · exact hB
      · exact hz
      · exact hSuccessor
      · exact hGraph
    have hGraphAmbient :=
      (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        TextbookNatFormula.natAddGraphDelta
        (snoc (snoc assignment successor) graph)
        hGraphAssignmentMem).mp hGraphFormula
    rw [Delta0Formula.satisfies_toFO, hGraphAssignment] at hGraphAmbient
    exact TextbookNatFormula.natAddGraphDelta_output_unique
      a b z successor graph hSuccessorCode hGraphAmbient
  · intro hResult
    have hSuccessor : (natCode (b + 1) : ZFSet.{u}) ∈ LStageZF θ :=
      natCode_mem_stage_l hω (b + 1)
    have hGraph : TextbookNatFormula.natAddCanonicalGraph a b ∈
        LStageZF θ := natAddCanonicalGraph_mem_stage_l hω a b
    refine ⟨(satisfiesIn_standardOmegaAt_stage_iff_l
      hθ hω (0 : Fin 4) assignment hAssignment).mpr rfl,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode a)).mpr ⟨a, rfl⟩,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode b)).mpr ⟨b, rfl⟩, ?_,
      natCode (b + 1), hSuccessor, ?_,
      TextbookNatFormula.natAddCanonicalGraph a b, hGraph, ?_⟩
    · rw [hResult]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (a + b))).mpr
        ⟨a + b, rfl⟩
    · have hSuccessorAssignment : snoc assignment (natCode (b + 1)) =
          ![omega, natCode a, natCode b, z, natCode (b + 1)] := by
        funext index
        fin_cases index <;> rfl
      have hSuccessorAssignmentMem : ∀ index,
          snoc assignment (natCode (b + 1)) index ∈ LStageZF θ := by
        rw [hSuccessorAssignment]
        intro index
        fin_cases index
        · exact hOmega
        · exact hA
        · exact hB
        · exact hz
        · exact hSuccessor
      apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc assignment (natCode (b + 1)))
        hSuccessorAssignmentMem).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt, hSuccessorAssignment]
      exact natCode_succ_eq_insert b
    · have hGraphAssignment :
          snoc (snoc assignment (natCode (b + 1)))
              (TextbookNatFormula.natAddCanonicalGraph a b) =
            ![omega, natCode a, natCode b, z, natCode (b + 1),
              TextbookNatFormula.natAddCanonicalGraph a b] := by
        funext index
        fin_cases index <;> rfl
      have hGraphAssignmentMem : ∀ index,
          snoc (snoc assignment (natCode (b + 1)))
            (TextbookNatFormula.natAddCanonicalGraph a b) index ∈
              LStageZF θ := by
        rw [hGraphAssignment]
        intro index
        fin_cases index
        · exact hOmega
        · exact hA
        · exact hB
        · exact hz
        · exact hSuccessor
        · exact hGraph
      apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        TextbookNatFormula.natAddGraphDelta
        (snoc (snoc assignment (natCode (b + 1)))
          (TextbookNatFormula.natAddCanonicalGraph a b))
        hGraphAssignmentMem).mpr
      rw [Delta0Formula.satisfies_toFO, hGraphAssignment, hResult]
      exact TextbookNatFormula.natAddCanonicalGraph_satisfies a b

/-- 乘法递归的逐步条件在后继极限层与外部语义一致。 -/
theorem satisfiesIn_natMulTransition_stage_iff_ambient_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (omega x y z successor graph : ZFSet.{u})
    (hOmega : omega ∈ LStageZF θ) (hX : x ∈ LStageZF θ)
    (hY : y ∈ LStageZF θ) (hZ : z ∈ LStageZF θ)
    (hSuccessor : successor ∈ LStageZF θ)
    (hGraph : graph ∈ LStageZF θ)
    (hOmegaCode : omega = Ordinal.omega0.toZFSet)
    (hXOmega : x ∈ omega) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookNatFormula.natMulTransition
        ![omega, x, y, z, successor, graph] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        TextbookNatFormula.natMulTransition
        ![omega, x, y, z, successor, graph] := by
  subst omega
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode x).mp hXOmega with
    ⟨a, rfl⟩
  let assignment : Tuple ZFSet.{u} 6 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a,
      y, z, successor, graph]
  have hAssignment : Model.TupleIn (LStageZF θ : Set ZFSet.{u})
      assignment := by
    intro index
    fin_cases index
    · exact hOmega
    · exact hX
    · exact hY
    · exact hZ
    · exact hSuccessor
    · exact hGraph
  change Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      TextbookNatFormula.natMulTransition assignment ↔
    FOFormula.Satisfies Delta0Formula.ZFMem
      TextbookNatFormula.natMulTransition assignment
  rw [TextbookNatFormula.satisfies_natMulTransition]
  rw [TextbookNatFormula.natMulTransition,
    TextbookNatFormula.natMulTransitionAt,
    satisfiesIn_boundedAll_stage_iff]
  simp only [assignment]
  constructor
  · intro h k hk
    have hkStage : k ∈ LStageZF θ :=
      (LStageZF_isTransitive θ).mem_trans hk hY
    have hBody := h k hkStage hk
    rw [satisfiesIn_boundedEx_stage_iff] at hBody
    rcases hBody with
      ⟨kSucc, hkSuccStage, hkSuccDomain, hkSuccFormula, hRest⟩
    have hskk : Model.TupleIn (LStageZF θ : Set ZFSet.{u})
        (snoc (snoc assignment k) kSucc) :=
      Model.tupleIn_snoc_iff.mpr
        ⟨Model.tupleIn_snoc_iff.mpr ⟨hAssignment, hkStage⟩, hkSuccStage⟩
    have hkSuccAmbient :=
      (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (Delta0Formula.successorAt
          (Fin.last (6 + 1)) (Fin.last 6).castSucc)
        (snoc (snoc assignment k) kSucc) hskk).mp hkSuccFormula
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt] at hkSuccAmbient
    have hkSuccCode : kSucc = insert k k := by
      simpa only [snoc_last, snoc_castSucc] using hkSuccAmbient
    rw [satisfiesIn_boundedEx_stage_iff] at hRest
    rcases hRest with
      ⟨value, hValueStage, hValueOmega, hValueFormula, hNextRest⟩
    have hskkv : Model.TupleIn (LStageZF θ : Set ZFSet.{u})
        (snoc (snoc (snoc assignment k) kSucc) value) :=
      Model.tupleIn_snoc_iff.mpr ⟨hskk, hValueStage⟩
    have hValueAmbient :=
      (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc
          (Fin.last 6).castSucc.castSucc (Fin.last (6 + 2)))
        (snoc (snoc (snoc assignment k) kSucc) value) hskkv).mp
          hValueFormula
    rw [Delta0Formula.satisfies_toFO,
      TextbookDefFormula.satisfies_graphValueDeltaAt] at hValueAmbient
    have hValueGraph : ZFSet.pair k value ∈ graph := by
      change ZFSet.pair k value ∈ graph at hValueAmbient
      exact hValueAmbient
    rw [satisfiesIn_boundedEx_stage_iff] at hNextRest
    rcases hNextRest with
      ⟨nextValue, hNextStage, hNextOmega, hNextFormula, hAddRenamed⟩
    have hskkvn : Model.TupleIn (LStageZF θ : Set ZFSet.{u})
        (snoc (snoc (snoc (snoc assignment k) kSucc) value) nextValue) :=
      Model.tupleIn_snoc_iff.mpr ⟨hskkv, hNextStage⟩
    have hNextAmbient :=
      (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc.castSucc
          (Fin.last (6 + 1)).castSucc.castSucc (Fin.last (6 + 3)))
        (snoc (snoc (snoc (snoc assignment k) kSucc) value) nextValue)
        hskkvn).mp hNextFormula
    rw [Delta0Formula.satisfies_toFO,
      TextbookDefFormula.satisfies_graphValueDeltaAt] at hNextAmbient
    have hNextGraph : ZFSet.pair kSucc nextValue ∈ graph := by
      change ZFSet.pair kSucc nextValue ∈ graph at hNextAmbient
      exact hNextAmbient
    rw [satisfiesIn_rename_stage_iff,
      TextbookNatFormula.comp_natMulAddRenameAt] at hAddRenamed
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode value).mp
      hValueOmega with ⟨c, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nextValue).mp
      hNextOmega with ⟨d, rfl⟩
    have hAddCode : (natCode d : ZFSet.{u}) = natCode (c + a) :=
      (satisfiesIn_natAddFormula_stage_natCode_iff_l
        hθ hω c a hNextStage).mp hAddRenamed
    have hAddAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem
          TextbookNatFormula.natAddFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode c,
            natCode a, natCode d] :=
      (TextbookNatFormula.satisfies_natAddFormula_natCode_iff
        c a (natCode d)).mpr hAddCode
    rw [hkSuccCode] at hkSuccDomain hNextGraph
    exact ⟨hkSuccDomain, natCode c, hValueOmega, hValueGraph,
      natCode d, hNextOmega, hNextGraph, hAddAmbient⟩
  · intro h k hkStage hk
    rcases h k hk with
      ⟨hkSuccDomain, value, hValueOmega, hValueGraph,
        nextValue, hNextOmega, hNextGraph, hAddAmbient⟩
    have hkSuccStage : insert k k ∈ LStageZF θ :=
      (LStageZF_isTransitive θ).mem_trans hkSuccDomain hSuccessor
    have hValueStage : value ∈ LStageZF θ :=
      (LStageZF_isTransitive θ).mem_trans hValueOmega hOmega
    have hNextStage : nextValue ∈ LStageZF θ :=
      (LStageZF_isTransitive θ).mem_trans hNextOmega hOmega
    refine ⟨insert k k, hkSuccStage, hkSuccDomain, ?_,
      value, hValueStage, hValueOmega, ?_,
      nextValue, hNextStage, hNextOmega, ?_, ?_⟩
    · apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (Delta0Formula.successorAt
          (Fin.last (6 + 1)) (Fin.last 6).castSucc)
        (snoc (snoc assignment k) (insert k k))
        (Model.tupleIn_snoc_iff.mpr
          ⟨Model.tupleIn_snoc_iff.mpr ⟨hAssignment, hkStage⟩,
            hkSuccStage⟩)).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      simp only [snoc_last, snoc_castSucc]
    · apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc
          (Fin.last 6).castSucc.castSucc (Fin.last (6 + 2)))
        (snoc (snoc (snoc assignment k) (insert k k)) value)
        (Model.tupleIn_snoc_iff.mpr
          ⟨Model.tupleIn_snoc_iff.mpr
            ⟨Model.tupleIn_snoc_iff.mpr ⟨hAssignment, hkStage⟩,
              hkSuccStage⟩, hValueStage⟩)).mpr
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_graphValueDeltaAt]
      change ZFSet.pair k value ∈ graph
      exact hValueGraph
    · apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc.castSucc
          (Fin.last (6 + 1)).castSucc.castSucc (Fin.last (6 + 3)))
        (snoc (snoc (snoc (snoc assignment k) (insert k k)) value)
          nextValue)
        (Model.tupleIn_snoc_iff.mpr
          ⟨Model.tupleIn_snoc_iff.mpr
            ⟨Model.tupleIn_snoc_iff.mpr
              ⟨Model.tupleIn_snoc_iff.mpr ⟨hAssignment, hkStage⟩,
                hkSuccStage⟩, hValueStage⟩, hNextStage⟩)).mpr
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_graphValueDeltaAt]
      change ZFSet.pair (insert k k) nextValue ∈ graph
      exact hNextGraph
    · rw [satisfiesIn_rename_stage_iff,
        TextbookNatFormula.comp_natMulAddRenameAt]
      rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode value).mp
        hValueOmega with ⟨c, rfl⟩
      rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nextValue).mp
        hNextOmega with ⟨d, rfl⟩
      have hAddCode : (natCode d : ZFSet.{u}) = natCode (c + a) :=
        (TextbookNatFormula.satisfies_natAddFormula_natCode_iff
          c a (natCode d)).mp hAddAmbient
      exact (satisfiesIn_natAddFormula_stage_natCode_iff_l
        hθ hω c a hNextStage).mpr hAddCode

/-- 乘法有限图的完整公式在层内外一致。 -/
theorem satisfiesIn_natMulGraphFormula_stage_iff_ambient_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (omega x y z successor graph : ZFSet.{u})
    (hOmega : omega ∈ LStageZF θ) (hX : x ∈ LStageZF θ)
    (hY : y ∈ LStageZF θ) (hZ : z ∈ LStageZF θ)
    (hSuccessor : successor ∈ LStageZF θ)
    (hGraph : graph ∈ LStageZF θ)
    (hOmegaCode : omega = Ordinal.omega0.toZFSet)
    (hXOmega : x ∈ omega) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookNatFormula.natMulGraphFormula
        ![omega, x, y, z, successor, graph] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        TextbookNatFormula.natMulGraphFormula
        ![omega, x, y, z, successor, graph] := by
  let assignment : Tuple ZFSet.{u} 6 :=
    ![omega, x, y, z, successor, graph]
  have hAssignment : Model.TupleIn (LStageZF θ : Set ZFSet.{u})
      assignment := by
    intro index
    fin_cases index
    · exact hOmega
    · exact hX
    · exact hY
    · exact hZ
    · exact hSuccessor
    · exact hGraph
  change
    (Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookNatFormula.natMulGraphShapeDelta.toFO assignment ∧
      Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookNatFormula.natMulTransition assignment) ↔
    (FOFormula.Satisfies Delta0Formula.ZFMem
        TextbookNatFormula.natMulGraphShapeDelta.toFO assignment ∧
      FOFormula.Satisfies Delta0Formula.ZFMem
        TextbookNatFormula.natMulTransition assignment)
  rw [Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
    TextbookNatFormula.natMulGraphShapeDelta assignment hAssignment]
  have hTransition := satisfiesIn_natMulTransition_stage_iff_ambient_l
    hθ hω omega x y z successor graph hOmega hX hY hZ hSuccessor hGraph
      hOmegaCode hXOmega
  simpa only [assignment] using and_congr Iff.rfl hTransition

/-- 规范乘法递归图已经在 `L_omega` 中出现。 -/
theorem natMulCanonicalGraph_mem_LStageOmega_l (a b : Nat) :
    TextbookNatFormula.natMulCanonicalGraph a b ∈
      LStageZF Ordinal.omega0 :=
  textbookNatTupleGraph_mem_LStageOmega_l
    (TextbookNatFormula.natMulCanonicalTuple a b)

/-- 严格越过 `omega` 的层包含规范乘法递归图。 -/
theorem natMulCanonicalGraph_mem_stage_l {θ : Ordinal.{u}}
    (hω : Ordinal.omega0 < θ) (a b : Nat) :
    TextbookNatFormula.natMulCanonicalGraph a b ∈ LStageZF θ :=
  LStageZF_mono (le_of_lt hω)
    (natMulCanonicalGraph_mem_LStageOmega_l a b)

/-- 教科书乘法公式在后继极限层中精确计算标准自然数乘积。 -/
theorem satisfiesIn_natMulFormula_stage_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (a b : Nat) {z : ZFSet.{u}}
    (hZ : z ∈ LStageZF θ) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookNatFormula.natMulFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b, z] ↔
      z = natCode (a * b) := by
  let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
  let assignment : Tuple ZFSet.{u} 4 :=
    ![omega, natCode a, natCode b, z]
  have hOmega : omega ∈ LStageZF θ := omega_toZFSet_mem_stage_l hω
  have hA : (natCode a : ZFSet.{u}) ∈ LStageZF θ :=
    natCode_mem_stage_l hω a
  have hB : (natCode b : ZFSet.{u}) ∈ LStageZF θ :=
    natCode_mem_stage_l hω b
  have hAssignment : Model.TupleIn (LStageZF θ : Set ZFSet.{u})
      assignment := by
    intro index
    fin_cases index
    · exact hOmega
    · exact hA
    · exact hB
    · exact hZ
  have hAOmega : (natCode a : ZFSet.{u}) ∈ omega :=
    (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode a)).mpr ⟨a, rfl⟩
  change
    ((Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Model.standardOmegaAt (0 : Fin 4)) assignment ∧
      (natCode a : ZFSet.{u}) ∈ omega ∧
      (natCode b : ZFSet.{u}) ∈ omega ∧ z ∈ omega ∧
      ∃ successor, successor ∈ LStageZF θ ∧
        Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          (Delta0Formula.successorAt
            (Fin.last 4) (2 : Fin 4).castSucc).toFO
          (snoc assignment successor) ∧
        ∃ graph, graph ∈ LStageZF θ ∧
          Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
            TextbookNatFormula.natMulGraphFormula
            (snoc (snoc assignment successor) graph)) ↔ _)
  constructor
  · rintro ⟨hOmegaFormula, _, _, _, successor, hSuccessor,
      hSuccessorFormula, graph, hGraph, hGraphFormula⟩
    have _hOmegaCode := (satisfiesIn_standardOmegaAt_stage_iff_l
      hθ hω (0 : Fin 4) assignment hAssignment).mp hOmegaFormula
    have hSuccessorAssignment : snoc assignment successor =
        ![omega, natCode a, natCode b, z, successor] := by
      funext index
      fin_cases index <;> rfl
    have hSuccessorAssignmentMem : Model.TupleIn
        (LStageZF θ : Set ZFSet.{u}) (snoc assignment successor) :=
      Model.tupleIn_snoc_iff.mpr ⟨hAssignment, hSuccessor⟩
    have hSuccessorAmbient :=
      (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc assignment successor) hSuccessorAssignmentMem).mp
          hSuccessorFormula
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt,
      hSuccessorAssignment] at hSuccessorAmbient
    have hSuccessorCode : successor = natCode (b + 1) :=
      hSuccessorAmbient.trans (natCode_succ_eq_insert b).symm
    have hGraphAssignment : snoc (snoc assignment successor) graph =
        ![omega, natCode a, natCode b, z, successor, graph] := by
      funext index
      fin_cases index <;> rfl
    rw [hGraphAssignment] at hGraphFormula
    have hGraphAmbient :=
      (satisfiesIn_natMulGraphFormula_stage_iff_ambient_l
        hθ hω omega (natCode a) (natCode b) z successor graph
        hOmega hA hB hZ hSuccessor hGraph rfl hAOmega).mp hGraphFormula
    exact TextbookNatFormula.natMulGraphFormula_output_unique
      a b z successor graph hSuccessorCode hGraphAmbient
  · intro hResult
    have hSuccessor : (natCode (b + 1) : ZFSet.{u}) ∈ LStageZF θ :=
      natCode_mem_stage_l hω (b + 1)
    have hGraph : TextbookNatFormula.natMulCanonicalGraph a b ∈
        LStageZF θ := natMulCanonicalGraph_mem_stage_l hω a b
    refine ⟨(satisfiesIn_standardOmegaAt_stage_iff_l
      hθ hω (0 : Fin 4) assignment hAssignment).mpr rfl,
      hAOmega,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode b)).mpr ⟨b, rfl⟩, ?_,
      natCode (b + 1), hSuccessor, ?_,
      TextbookNatFormula.natMulCanonicalGraph a b, hGraph, ?_⟩
    · rw [hResult]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (a * b))).mpr ⟨a * b, rfl⟩
    · apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc assignment (natCode (b + 1)))
        (Model.tupleIn_snoc_iff.mpr ⟨hAssignment, hSuccessor⟩)).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      change (natCode (b + 1) : ZFSet.{u}) = insert (natCode b) (natCode b)
      exact natCode_succ_eq_insert b
    · have hGraphAssignment :
          snoc (snoc assignment (natCode (b + 1)))
              (TextbookNatFormula.natMulCanonicalGraph a b) =
            ![omega, natCode a, natCode b, z, natCode (b + 1),
              TextbookNatFormula.natMulCanonicalGraph a b] := by
        funext index
        fin_cases index <;> rfl
      rw [hGraphAssignment, hResult]
      apply (satisfiesIn_natMulGraphFormula_stage_iff_ambient_l
        hθ hω omega (natCode a) (natCode b) (natCode (a * b))
        (natCode (b + 1)) (TextbookNatFormula.natMulCanonicalGraph a b)
        hOmega hA hB (by simpa [hResult] using hZ) hSuccessor hGraph
        rfl hAOmega).mpr
      exact TextbookNatFormula.natMulCanonicalGraph_satisfies a b

/-- 规范幂递归图已经在 `L_omega` 中出现。 -/
theorem natPowCanonicalGraph_mem_LStageOmega_l (base exponent : Nat) :
    TextbookNatFormula.natPowCanonicalGraph base exponent ∈
      LStageZF Ordinal.omega0 :=
  textbookNatTupleGraph_mem_LStageOmega_l
    (TextbookNatFormula.natPowCanonicalTuple base exponent)

/-- 严格越过 `omega` 的层包含规范幂递归图。 -/
theorem natPowCanonicalGraph_mem_stage_l {θ : Ordinal.{u}}
    (hω : Ordinal.omega0 < θ) (base exponent : Nat) :
    TextbookNatFormula.natPowCanonicalGraph base exponent ∈ LStageZF θ :=
  LStageZF_mono (le_of_lt hω)
    (natPowCanonicalGraph_mem_LStageOmega_l base exponent)

/-- 幂递归的逐步条件在后继极限层与外部语义一致。 -/
theorem satisfiesIn_natPowTransition_stage_iff_ambient_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (omega base exponent output successor graph : ZFSet.{u})
    (hOmega : omega ∈ LStageZF θ) (hBase : base ∈ LStageZF θ)
    (hExponent : exponent ∈ LStageZF θ) (hOutput : output ∈ LStageZF θ)
    (hSuccessor : successor ∈ LStageZF θ)
    (hGraph : graph ∈ LStageZF θ)
    (hOmegaCode : omega = Ordinal.omega0.toZFSet)
    (hBaseOmega : base ∈ omega) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookNatFormula.natPowTransition
        ![omega, base, exponent, output, successor, graph] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        TextbookNatFormula.natPowTransition
        ![omega, base, exponent, output, successor, graph] := by
  subst omega
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode base).mp
    hBaseOmega with ⟨a, rfl⟩
  let assignment : Tuple ZFSet.{u} 6 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a,
      exponent, output, successor, graph]
  have hAssignment : Model.TupleIn (LStageZF θ : Set ZFSet.{u})
      assignment := by
    intro index
    fin_cases index
    · exact hOmega
    · exact hBase
    · exact hExponent
    · exact hOutput
    · exact hSuccessor
    · exact hGraph
  change Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      TextbookNatFormula.natPowTransition assignment ↔
    FOFormula.Satisfies Delta0Formula.ZFMem
      TextbookNatFormula.natPowTransition assignment
  rw [TextbookNatFormula.satisfies_natPowTransition]
  rw [TextbookNatFormula.natPowTransition,
    TextbookNatFormula.natPowTransitionAt,
    satisfiesIn_boundedAll_stage_iff]
  simp only [assignment]
  constructor
  · intro h k hk
    have hkStage : k ∈ LStageZF θ :=
      (LStageZF_isTransitive θ).mem_trans hk hExponent
    have hBody := h k hkStage hk
    rw [satisfiesIn_boundedEx_stage_iff] at hBody
    rcases hBody with
      ⟨kSucc, hkSuccStage, hkSuccDomain, hkSuccFormula, hRest⟩
    have hskk : Model.TupleIn (LStageZF θ : Set ZFSet.{u})
        (snoc (snoc assignment k) kSucc) :=
      Model.tupleIn_snoc_iff.mpr
        ⟨Model.tupleIn_snoc_iff.mpr ⟨hAssignment, hkStage⟩, hkSuccStage⟩
    have hkSuccAmbient :=
      (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (Delta0Formula.successorAt
          (Fin.last (6 + 1)) (Fin.last 6).castSucc)
        (snoc (snoc assignment k) kSucc) hskk).mp hkSuccFormula
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt] at hkSuccAmbient
    have hkSuccCode : kSucc = insert k k := by
      simpa only [snoc_last, snoc_castSucc] using hkSuccAmbient
    rw [satisfiesIn_boundedEx_stage_iff] at hRest
    rcases hRest with
      ⟨value, hValueStage, hValueOmega, hValueFormula, hNextRest⟩
    have hskkv : Model.TupleIn (LStageZF θ : Set ZFSet.{u})
        (snoc (snoc (snoc assignment k) kSucc) value) :=
      Model.tupleIn_snoc_iff.mpr ⟨hskk, hValueStage⟩
    have hValueAmbient :=
      (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc
          (Fin.last 6).castSucc.castSucc (Fin.last (6 + 2)))
        (snoc (snoc (snoc assignment k) kSucc) value) hskkv).mp
          hValueFormula
    rw [Delta0Formula.satisfies_toFO,
      TextbookDefFormula.satisfies_graphValueDeltaAt] at hValueAmbient
    have hValueGraph : ZFSet.pair k value ∈ graph := by
      change ZFSet.pair k value ∈ graph at hValueAmbient
      exact hValueAmbient
    rw [satisfiesIn_boundedEx_stage_iff] at hNextRest
    rcases hNextRest with
      ⟨nextValue, hNextStage, hNextOmega, hNextFormula, hMulRenamed⟩
    have hskkvn : Model.TupleIn (LStageZF θ : Set ZFSet.{u})
        (snoc (snoc (snoc (snoc assignment k) kSucc) value) nextValue) :=
      Model.tupleIn_snoc_iff.mpr ⟨hskkv, hNextStage⟩
    have hNextAmbient :=
      (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc.castSucc
          (Fin.last (6 + 1)).castSucc.castSucc (Fin.last (6 + 3)))
        (snoc (snoc (snoc (snoc assignment k) kSucc) value) nextValue)
        hskkvn).mp hNextFormula
    rw [Delta0Formula.satisfies_toFO,
      TextbookDefFormula.satisfies_graphValueDeltaAt] at hNextAmbient
    have hNextGraph : ZFSet.pair kSucc nextValue ∈ graph := by
      change ZFSet.pair kSucc nextValue ∈ graph at hNextAmbient
      exact hNextAmbient
    rw [satisfiesIn_rename_stage_iff,
      TextbookNatFormula.comp_natPowMulRenameAt] at hMulRenamed
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode value).mp
      hValueOmega with ⟨c, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nextValue).mp
      hNextOmega with ⟨d, rfl⟩
    have hMulCode : (natCode d : ZFSet.{u}) = natCode (c * a) :=
      (satisfiesIn_natMulFormula_stage_natCode_iff_l
        hθ hω c a hNextStage).mp hMulRenamed
    have hMulAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem
          TextbookNatFormula.natMulFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode c,
            natCode a, natCode d] :=
      (TextbookNatFormula.satisfies_natMulFormula_natCode_iff
        c a (natCode d)).mpr hMulCode
    rw [hkSuccCode] at hkSuccDomain hNextGraph
    exact ⟨hkSuccDomain, natCode c, hValueOmega, hValueGraph,
      natCode d, hNextOmega, hNextGraph, hMulAmbient⟩
  · intro h k hkStage hk
    rcases h k hk with
      ⟨hkSuccDomain, value, hValueOmega, hValueGraph,
        nextValue, hNextOmega, hNextGraph, hMulAmbient⟩
    have hkSuccStage : insert k k ∈ LStageZF θ :=
      (LStageZF_isTransitive θ).mem_trans hkSuccDomain hSuccessor
    have hValueStage : value ∈ LStageZF θ :=
      (LStageZF_isTransitive θ).mem_trans hValueOmega hOmega
    have hNextStage : nextValue ∈ LStageZF θ :=
      (LStageZF_isTransitive θ).mem_trans hNextOmega hOmega
    refine ⟨insert k k, hkSuccStage, hkSuccDomain, ?_,
      value, hValueStage, hValueOmega, ?_,
      nextValue, hNextStage, hNextOmega, ?_, ?_⟩
    · apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (Delta0Formula.successorAt
          (Fin.last (6 + 1)) (Fin.last 6).castSucc)
        (snoc (snoc assignment k) (insert k k))
        (Model.tupleIn_snoc_iff.mpr
          ⟨Model.tupleIn_snoc_iff.mpr ⟨hAssignment, hkStage⟩,
            hkSuccStage⟩)).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      simp only [snoc_last, snoc_castSucc]
    · apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc
          (Fin.last 6).castSucc.castSucc (Fin.last (6 + 2)))
        (snoc (snoc (snoc assignment k) (insert k k)) value)
        (Model.tupleIn_snoc_iff.mpr
          ⟨Model.tupleIn_snoc_iff.mpr
            ⟨Model.tupleIn_snoc_iff.mpr ⟨hAssignment, hkStage⟩,
              hkSuccStage⟩, hValueStage⟩)).mpr
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_graphValueDeltaAt]
      change ZFSet.pair k value ∈ graph
      exact hValueGraph
    · apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc.castSucc
          (Fin.last (6 + 1)).castSucc.castSucc (Fin.last (6 + 3)))
        (snoc (snoc (snoc (snoc assignment k) (insert k k)) value)
          nextValue)
        (Model.tupleIn_snoc_iff.mpr
          ⟨Model.tupleIn_snoc_iff.mpr
            ⟨Model.tupleIn_snoc_iff.mpr
              ⟨Model.tupleIn_snoc_iff.mpr ⟨hAssignment, hkStage⟩,
                hkSuccStage⟩, hValueStage⟩, hNextStage⟩)).mpr
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_graphValueDeltaAt]
      change ZFSet.pair (insert k k) nextValue ∈ graph
      exact hNextGraph
    · rw [satisfiesIn_rename_stage_iff,
        TextbookNatFormula.comp_natPowMulRenameAt]
      rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode value).mp
        hValueOmega with ⟨c, rfl⟩
      rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nextValue).mp
        hNextOmega with ⟨d, rfl⟩
      have hMulCode : (natCode d : ZFSet.{u}) = natCode (c * a) :=
        (TextbookNatFormula.satisfies_natMulFormula_natCode_iff
          c a (natCode d)).mp hMulAmbient
      exact (satisfiesIn_natMulFormula_stage_natCode_iff_l
        hθ hω c a hNextStage).mpr hMulCode

/-- 幂的有限递归图公式在层内外一致。 -/
theorem satisfiesIn_natPowGraphFormula_stage_iff_ambient_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (omega base exponent output successor graph : ZFSet.{u})
    (hOmega : omega ∈ LStageZF θ) (hBase : base ∈ LStageZF θ)
    (hExponent : exponent ∈ LStageZF θ) (hOutput : output ∈ LStageZF θ)
    (hSuccessor : successor ∈ LStageZF θ)
    (hGraph : graph ∈ LStageZF θ)
    (hOmegaCode : omega = Ordinal.omega0.toZFSet)
    (hBaseOmega : base ∈ omega) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookNatFormula.natPowGraphFormula
        ![omega, base, exponent, output, successor, graph] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        TextbookNatFormula.natPowGraphFormula
        ![omega, base, exponent, output, successor, graph] := by
  let assignment : Tuple ZFSet.{u} 6 :=
    ![omega, base, exponent, output, successor, graph]
  have hAssignment : Model.TupleIn (LStageZF θ : Set ZFSet.{u})
      assignment := by
    intro index
    fin_cases index
    · exact hOmega
    · exact hBase
    · exact hExponent
    · exact hOutput
    · exact hSuccessor
    · exact hGraph
  change
    (Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookNatFormula.natPowGraphShapeDelta.toFO assignment ∧
      Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookNatFormula.natPowTransition assignment) ↔
    (FOFormula.Satisfies Delta0Formula.ZFMem
        TextbookNatFormula.natPowGraphShapeDelta.toFO assignment ∧
      FOFormula.Satisfies Delta0Formula.ZFMem
        TextbookNatFormula.natPowTransition assignment)
  rw [Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
    TextbookNatFormula.natPowGraphShapeDelta assignment hAssignment]
  have hTransition := satisfiesIn_natPowTransition_stage_iff_ambient_l
    hθ hω omega base exponent output successor graph
      hOmega hBase hExponent hOutput hSuccessor hGraph hOmegaCode hBaseOmega
  simpa only [assignment] using and_congr Iff.rfl hTransition

/-- 教科书幂公式在后继极限层中精确计算标准自然数幂。 -/
theorem satisfiesIn_natPowFormula_stage_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (base exponent : Nat) {output : ZFSet.{u}}
    (hOutput : output ∈ LStageZF θ) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookNatFormula.natPowFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode base,
          natCode exponent, output] ↔
      output = natCode (base ^ exponent) := by
  let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
  let assignment : Tuple ZFSet.{u} 4 :=
    ![omega, natCode base, natCode exponent, output]
  have hOmega : omega ∈ LStageZF θ := omega_toZFSet_mem_stage_l hω
  have hBase : (natCode base : ZFSet.{u}) ∈ LStageZF θ :=
    natCode_mem_stage_l hω base
  have hExponent : (natCode exponent : ZFSet.{u}) ∈ LStageZF θ :=
    natCode_mem_stage_l hω exponent
  have hAssignment : Model.TupleIn (LStageZF θ : Set ZFSet.{u})
      assignment := by
    intro index
    fin_cases index
    · exact hOmega
    · exact hBase
    · exact hExponent
    · exact hOutput
  have hBaseOmega : (natCode base : ZFSet.{u}) ∈ omega :=
    (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode base)).mpr ⟨base, rfl⟩
  change
    ((Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Model.standardOmegaAt (0 : Fin 4)) assignment ∧
      (natCode base : ZFSet.{u}) ∈ omega ∧
      (natCode exponent : ZFSet.{u}) ∈ omega ∧ output ∈ omega ∧
      ∃ successor, successor ∈ LStageZF θ ∧
        Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          (Delta0Formula.successorAt
            (Fin.last 4) (2 : Fin 4).castSucc).toFO
          (snoc assignment successor) ∧
        ∃ graph, graph ∈ LStageZF θ ∧
          Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
            TextbookNatFormula.natPowGraphFormula
            (snoc (snoc assignment successor) graph)) ↔ _)
  constructor
  · rintro ⟨hOmegaFormula, _, _, _, successor, hSuccessor,
      hSuccessorFormula, graph, hGraph, hGraphFormula⟩
    have _hOmegaCode := (satisfiesIn_standardOmegaAt_stage_iff_l
      hθ hω (0 : Fin 4) assignment hAssignment).mp hOmegaFormula
    have hSuccessorAssignment : snoc assignment successor =
        ![omega, natCode base, natCode exponent, output, successor] := by
      funext index
      fin_cases index <;> rfl
    have hSuccessorAmbient :=
      (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc assignment successor)
        (Model.tupleIn_snoc_iff.mpr ⟨hAssignment, hSuccessor⟩)).mp
          hSuccessorFormula
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt,
      hSuccessorAssignment] at hSuccessorAmbient
    have hSuccessorCode : successor = natCode (exponent + 1) :=
      hSuccessorAmbient.trans (natCode_succ_eq_insert exponent).symm
    have hGraphAssignment : snoc (snoc assignment successor) graph =
        ![omega, natCode base, natCode exponent, output, successor, graph] := by
      funext index
      fin_cases index <;> rfl
    rw [hGraphAssignment] at hGraphFormula
    have hGraphAmbient :=
      (satisfiesIn_natPowGraphFormula_stage_iff_ambient_l
        hθ hω omega (natCode base) (natCode exponent) output successor graph
        hOmega hBase hExponent hOutput hSuccessor hGraph rfl hBaseOmega).mp
          hGraphFormula
    exact TextbookNatFormula.natPowGraphFormula_output_unique
      base exponent output successor graph hSuccessorCode hGraphAmbient
  · intro hResult
    have hSuccessor : (natCode (exponent + 1) : ZFSet.{u}) ∈ LStageZF θ :=
      natCode_mem_stage_l hω (exponent + 1)
    have hGraph : TextbookNatFormula.natPowCanonicalGraph base exponent ∈
        LStageZF θ := natPowCanonicalGraph_mem_stage_l hω base exponent
    refine ⟨(satisfiesIn_standardOmegaAt_stage_iff_l
      hθ hω (0 : Fin 4) assignment hAssignment).mpr rfl,
      hBaseOmega,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode exponent)).mpr ⟨exponent, rfl⟩, ?_,
      natCode (exponent + 1), hSuccessor, ?_,
      TextbookNatFormula.natPowCanonicalGraph base exponent, hGraph, ?_⟩
    · rw [hResult]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (base ^ exponent))).mpr ⟨base ^ exponent, rfl⟩
    · apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc assignment (natCode (exponent + 1)))
        (Model.tupleIn_snoc_iff.mpr ⟨hAssignment, hSuccessor⟩)).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      change (natCode (exponent + 1) : ZFSet.{u}) =
        insert (natCode exponent) (natCode exponent)
      exact natCode_succ_eq_insert exponent
    · have hGraphAssignment :
          snoc (snoc assignment (natCode (exponent + 1)))
              (TextbookNatFormula.natPowCanonicalGraph base exponent) =
            ![omega, natCode base, natCode exponent, output,
              natCode (exponent + 1),
              TextbookNatFormula.natPowCanonicalGraph base exponent] := by
        funext index
        fin_cases index <;> rfl
      rw [hGraphAssignment, hResult]
      apply (satisfiesIn_natPowGraphFormula_stage_iff_ambient_l
        hθ hω omega (natCode base) (natCode exponent)
        (natCode (base ^ exponent)) (natCode (exponent + 1))
        (TextbookNatFormula.natPowCanonicalGraph base exponent)
        hOmega hBase hExponent (by simpa [hResult] using hOutput)
        hSuccessor hGraph rfl hBaseOmega).mpr
      exact TextbookNatFormula.natPowCanonicalGraph_satisfies base exponent

/-- 素数幂 E-code 公式在后继极限层中精确计算标准构造器码。 -/
theorem satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (i j tag : Nat) {code : ZFSet.{u}}
    (hCode : code ∈ LStageZF θ) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        TextbookNatFormula.textbookECodeFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode i,
          natCode j, natCode tag, code] ↔
      code = natCode (textbookECode i j tag) := by
  let assignment : Tuple ZFSet.{u} 5 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode i,
      natCode j, natCode tag, code]
  have hAssignment : Model.TupleIn (LStageZF θ : Set ZFSet.{u})
      assignment := by
    intro index
    fin_cases index
    · exact omega_toZFSet_mem_stage_l hω
    · exact natCode_mem_stage_l hω i
    · exact natCode_mem_stage_l hω j
    · exact natCode_mem_stage_l hω tag
    · exact hCode
  change Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      TextbookNatFormula.textbookECodeFormula assignment ↔ _
  rw [TextbookNatFormula.textbookECodeFormula, Model.SatisfiesIn]
  constructor
  · rintro ⟨two, hTwoStage, hTwoFormula, hTail⟩
    have hTwoAssignment : Model.TupleIn (LStageZF θ : Set ZFSet.{u})
        (snoc assignment two) :=
      Model.tupleIn_snoc_iff.mpr ⟨hAssignment, hTwoStage⟩
    have hTwo : two = (natCode 2 : ZFSet.{u}) := by
      have h := (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 2 (5 : Fin 6)
        (snoc assignment two) hTwoAssignment).mp hTwoFormula
      change two = (natCode 2 : ZFSet.{u}) at h
      exact h
    rw [TextbookNatFormula.textbookECodeAfterTwoFormula,
      Model.SatisfiesIn] at hTail
    rcases hTail with ⟨three, hThreeStage, hThreeFormula, hTail⟩
    have hThreeAssignment : Model.TupleIn (LStageZF θ : Set ZFSet.{u})
        (snoc (snoc assignment two) three) :=
      Model.tupleIn_snoc_iff.mpr ⟨hTwoAssignment, hThreeStage⟩
    have hThree : three = (natCode 3 : ZFSet.{u}) := by
      have h := (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 3 (6 : Fin 7)
        (snoc (snoc assignment two) three) hThreeAssignment).mp hThreeFormula
      change three = (natCode 3 : ZFSet.{u}) at h
      exact h
    rw [TextbookNatFormula.textbookECodeAfterThreeFormula,
      Model.SatisfiesIn] at hTail
    rcases hTail with ⟨five, hFiveStage, hFiveFormula, hTail⟩
    have hFiveAssignment : Model.TupleIn (LStageZF θ : Set ZFSet.{u})
        (snoc (snoc (snoc assignment two) three) five) :=
      Model.tupleIn_snoc_iff.mpr ⟨hThreeAssignment, hFiveStage⟩
    have hFive : five = (natCode 5 : ZFSet.{u}) := by
      have h := (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 5 (7 : Fin 8)
        (snoc (snoc (snoc assignment two) three) five)
        hFiveAssignment).mp hFiveFormula
      change five = (natCode 5 : ZFSet.{u}) at h
      exact h
    subst two
    subst three
    subst five
    rw [TextbookNatFormula.textbookECodeAfterFiveFormula,
      Model.SatisfiesIn] at hTail
    rcases hTail with ⟨powTwo, hPowTwoStage, hPowTwoFormula, hTail⟩
    rw [TextbookNatFormula.satisfiesIn_natPowFormulaAt,
      TextbookNatFormula.textbookECode_powTwo_assignment] at hPowTwoFormula
    have hPowTwo : powTwo = (natCode (2 ^ i) : ZFSet.{u}) :=
      (satisfiesIn_natPowFormula_stage_natCode_iff_l
        hθ hω 2 i hPowTwoStage).mp hPowTwoFormula
    subst powTwo
    rw [TextbookNatFormula.textbookECodeAfterPowTwoFormula,
      Model.SatisfiesIn] at hTail
    rcases hTail with ⟨powThree, hPowThreeStage, hPowThreeFormula, hTail⟩
    rw [TextbookNatFormula.satisfiesIn_natPowFormulaAt,
      TextbookNatFormula.textbookECode_powThree_assignment] at hPowThreeFormula
    have hPowThree : powThree = (natCode (3 ^ j) : ZFSet.{u}) :=
      (satisfiesIn_natPowFormula_stage_natCode_iff_l
        hθ hω 3 j hPowThreeStage).mp hPowThreeFormula
    subst powThree
    rw [TextbookNatFormula.textbookECodeAfterPowThreeFormula,
      Model.SatisfiesIn] at hTail
    rcases hTail with ⟨powFive, hPowFiveStage, hPowFiveFormula, hTail⟩
    rw [TextbookNatFormula.satisfiesIn_natPowFormulaAt,
      TextbookNatFormula.textbookECode_powFive_assignment] at hPowFiveFormula
    have hPowFive : powFive = (natCode (5 ^ tag) : ZFSet.{u}) :=
      (satisfiesIn_natPowFormula_stage_natCode_iff_l
        hθ hω 5 tag hPowFiveStage).mp hPowFiveFormula
    subst powFive
    rw [TextbookNatFormula.textbookECodeAfterPowFiveFormula,
      Model.SatisfiesIn] at hTail
    rcases hTail with ⟨product, hProductStage, hProductFormula, hFinalFormula⟩
    rw [TextbookNatFormula.satisfiesIn_natMulFormulaAt,
      TextbookNatFormula.textbookECode_product_assignment] at hProductFormula
    have hProduct : product =
        (natCode ((2 ^ i) * (3 ^ j)) : ZFSet.{u}) :=
      (satisfiesIn_natMulFormula_stage_natCode_iff_l
        hθ hω (2 ^ i) (3 ^ j) hProductStage).mp hProductFormula
    subst product
    rw [TextbookNatFormula.satisfiesIn_natMulFormulaAt,
      TextbookNatFormula.textbookECode_final_assignment] at hFinalFormula
    have hFinal : code =
        (natCode (((2 ^ i) * (3 ^ j)) * (5 ^ tag)) : ZFSet.{u}) :=
      (satisfiesIn_natMulFormula_stage_natCode_iff_l
        hθ hω ((2 ^ i) * (3 ^ j)) (5 ^ tag) hCode).mp hFinalFormula
    simpa only [textbookECode, Nat.mul_assoc] using hFinal
  · intro hResult
    have hResult' : code =
        (natCode (((2 ^ i) * (3 ^ j)) * (5 ^ tag)) : ZFSet.{u}) := by
      simpa only [textbookECode, Nat.mul_assoc] using hResult
    have hTwo := natCode_mem_stage_l hω 2
    have hThree := natCode_mem_stage_l hω 3
    have hFive := natCode_mem_stage_l hω 5
    have hPowTwo := natCode_mem_stage_l hω (2 ^ i)
    have hPowThree := natCode_mem_stage_l hω (3 ^ j)
    have hPowFive := natCode_mem_stage_l hω (5 ^ tag)
    have hProduct := natCode_mem_stage_l hω ((2 ^ i) * (3 ^ j))
    refine ⟨natCode 2, hTwo, ?_, ?_⟩
    · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 2 (5 : Fin 6)
        (snoc assignment (natCode 2))
        (Model.tupleIn_snoc_iff.mpr ⟨hAssignment, hTwo⟩)).mpr
      rfl
    · rw [TextbookNatFormula.textbookECodeAfterTwoFormula,
        Model.SatisfiesIn]
      refine ⟨natCode 3, hThree, ?_, ?_⟩
      · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
          (LStageZF_isTransitive θ) 3 (6 : Fin 7) _ ?_).mpr
        · rfl
        · exact Model.tupleIn_snoc_iff.mpr
            ⟨Model.tupleIn_snoc_iff.mpr ⟨hAssignment, hTwo⟩, hThree⟩
      · rw [TextbookNatFormula.textbookECodeAfterThreeFormula,
          Model.SatisfiesIn]
        refine ⟨natCode 5, hFive, ?_, ?_⟩
        · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
            (LStageZF_isTransitive θ) 5 (7 : Fin 8) _ ?_).mpr
          · rfl
          · exact Model.tupleIn_snoc_iff.mpr
              ⟨Model.tupleIn_snoc_iff.mpr
                ⟨Model.tupleIn_snoc_iff.mpr ⟨hAssignment, hTwo⟩,
                  hThree⟩, hFive⟩
        · rw [TextbookNatFormula.textbookECodeAfterFiveFormula,
            Model.SatisfiesIn]
          refine ⟨natCode (2 ^ i), hPowTwo, ?_, ?_⟩
          · rw [TextbookNatFormula.satisfiesIn_natPowFormulaAt,
              TextbookNatFormula.textbookECode_powTwo_assignment]
            exact (satisfiesIn_natPowFormula_stage_natCode_iff_l
              hθ hω 2 i hPowTwo).mpr rfl
          · rw [TextbookNatFormula.textbookECodeAfterPowTwoFormula,
              Model.SatisfiesIn]
            refine ⟨natCode (3 ^ j), hPowThree, ?_, ?_⟩
            · rw [TextbookNatFormula.satisfiesIn_natPowFormulaAt,
                TextbookNatFormula.textbookECode_powThree_assignment]
              exact (satisfiesIn_natPowFormula_stage_natCode_iff_l
                hθ hω 3 j hPowThree).mpr rfl
            · rw [TextbookNatFormula.textbookECodeAfterPowThreeFormula,
                Model.SatisfiesIn]
              refine ⟨natCode (5 ^ tag), hPowFive, ?_, ?_⟩
              · rw [TextbookNatFormula.satisfiesIn_natPowFormulaAt,
                  TextbookNatFormula.textbookECode_powFive_assignment]
                exact (satisfiesIn_natPowFormula_stage_natCode_iff_l
                  hθ hω 5 tag hPowFive).mpr rfl
              · rw [TextbookNatFormula.textbookECodeAfterPowFiveFormula,
                  Model.SatisfiesIn]
                refine ⟨natCode ((2 ^ i) * (3 ^ j)), hProduct, ?_⟩
                rw [TextbookNatFormula.textbookECodeFinalFormula,
                  Model.SatisfiesIn]
                constructor
                · rw [TextbookNatFormula.satisfiesIn_natMulFormulaAt,
                    TextbookNatFormula.textbookECode_product_assignment]
                  exact (satisfiesIn_natMulFormula_stage_natCode_iff_l
                    hθ hω (2 ^ i) (3 ^ j) hProduct).mpr rfl
                · rw [TextbookNatFormula.satisfiesIn_natMulFormulaAt,
                    TextbookNatFormula.textbookECode_final_assignment]
                  exact (satisfiesIn_natMulFormula_stage_natCode_iff_l
                    hθ hω ((2 ^ i) * (3 ^ j)) (5 ^ tag) hCode).mpr hResult'

end YesMetaZFC.BMS.ConstructibleBridge
