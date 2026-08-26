import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics
/-!
# 标准自然数 token 序列
本模块把自然数标签列表实现为对象集合论中的标准有限函数图，并证明其定义域、
逐点求值、映射性与编码字符串空间成员关系。该层只依赖标准有限序列语义，供符号
编码、quotation 与编码级 substitution 共同消费。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
/-- 把标准自然数标签列表实现为对象语言中的标准有限函数图。 -/
def standard_token_sequence (tokens : List Nat) : SetTerm :=
  standard_sequence (tokens.map finite_numeral_term)
private theorem stdtok_elements_admissible (tokens : List Nat) :
    ∀ element, element ∈ tokens.map finite_numeral_term →
      Term.Admissible element SetSort.set := by
  intro element hElement
  rcases List.mem_map.mp hElement with ⟨token, hToken, rfl⟩
  exact finite_numeral_term_admissible token
private theorem stdtok_elements_closed (tokens : List Nat) :
    ∀ element, element ∈ tokens.map finite_numeral_term →
      Term.freeSupport element = [] := by
  intro element hElement
  rcases List.mem_map.mp hElement with ⟨token, hToken, rfl⟩
  exact finite_numeral_term_freeSupport token
private theorem stdtok_elements_fresh
    (tokens : List Nat) (id : FreeVarId) :
    ∀ element, element ∈ tokens.map finite_numeral_term →
      (SetSort.set, id) ∉ Term.freeSupport element := by
  intro element hElement
  rw [stdtok_elements_closed tokens element hElement]
  exact List.not_mem_nil
private theorem stdtok_elements_mem_omega (tokens : List Nat) :
    ∀ element, element ∈ tokens.map finite_numeral_term →
      ⊢ₘ[standard_sequence_semantics_theory] element ∈ₘ ωₘ := by
  intro element hElement
  rcases List.mem_map.mp hElement with ⟨token, hToken, rfl⟩
  exact standard_sequence_finite_numeral_mem_omega token
private theorem stdtok_omega_freeSupport_nil :
    Term.freeSupport (ωₘ : SetTerm) = [] :=
  rfl
/-- 每条标准自然数标签列表都产生 admissible 对象项。 -/
theorem standard_token_sequence_admissible (tokens : List Nat) :
    Term.Admissible (standard_token_sequence tokens) SetSort.set := by
  exact seq_admissible_m 0 (stdtok_elements_admissible tokens)
/-- 标准 token 序列项的纯函数合法性证书。 -/
@[term_check]
theorem standard_token_sequence_check (tokens : List Nat) :
    Term.CheckCertificate (standard_token_sequence tokens) SetSort.set :=
  Term.check_admissible_complete
    (standard_token_sequence_admissible tokens)
/-- 标准 token 序列不含任何对象语言自由变量。 -/
@[simp]
theorem standard_token_sequence_freeSupport_nil (tokens : List Nat) :
    Term.freeSupport (standard_token_sequence tokens) = [] := by
  exact seq_support_nil_m 0 (stdtok_elements_closed tokens)
/-- 每条标准 token 序列本身满足有限序列条件。 -/
theorem standard_token_sequence_finite_sequence_condition (tokens : List Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      finite_sequence_condition (standard_token_sequence tokens) := by
  simpa [standard_token_sequence] using
    (standard_sequence_finite_sequence_condition
      (stdtok_elements_admissible tokens)
      (stdtok_elements_fresh tokens 0)
      (stdtok_elements_fresh tokens 1)
      (stdtok_elements_fresh tokens 2))
/-- 标准 token 序列的对象定义域正好是其长度 numeral。 -/
theorem standard_token_sequence_domain_eq_length (tokens : List Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      domₘ(standard_token_sequence tokens) ≐ₘ
        numₘ(tokens.length) := by
  simpa [standard_token_sequence] using
    (standard_sequence_domain_eq_numeral_length
      (stdtok_elements_admissible tokens)
      (stdtok_elements_fresh tokens 0)
      (stdtok_elements_fresh tokens 1))
/-- 标准 token 序列在每个存在的外部位置上按 token 逐点求值。 -/
theorem standard_token_sequence_apply_getElem? (tokens : List Nat) {index token : Nat} (hGet : tokens[index]? = some token) :
    ⊢ₘ[standard_sequence_semantics_theory] (standard_token_sequence tokens ·ₘ numₘ(index)) ≐ₘ
        numₘ(token) := by
  have hMapped : (tokens.map finite_numeral_term)[index]? =
        some (numₘ(token)) := by
    simpa using congrArg (Option.map finite_numeral_term) hGet
  simpa [standard_token_sequence, standard_sequence] using (standard_sequence_from_apply_getElem?
      0 hMapped (stdtok_elements_admissible tokens) (stdtok_elements_closed tokens) (finite_numeral_term_admissible token))
/--
函数、定义域和标准位置上的逐点值唯一决定一条标准 token 序列。
该定理工作在任意包含标准序列语义的理论与任意 Hilbert 上下文中。证明先把开放
参数的定义域成员关系有限消去为标准 numeral，再由调用方给出的逐点值与标准序列
求值合同建立全称逐点相等，最后使用函数外延性收束为对象等式。
-/
theorem stdtok_source_eq_of_function_domain_pointwise
    {T : SetTheory} {Γ : Context signature} (hTheory :
      ∀ formula,
        standard_sequence_semantics_theory formula → T formula) (hTheorySentence :
      ∀ formula, T formula → Formula.Sentence formula) (source : SetTerm) (tokens : List Nat) (hSource : Term.Admissible source SetSort.set) (hFunction :
      Γ ⊢ₘ[T] is_function_formula source) (hDomain :
      Γ ⊢ₘ[T]
        domₘ(source) ≐ₘ numₘ(tokens.length)) (hPoint :
      ∀ {index token : Nat},
        tokens[index]? = some token →
          Γ ⊢ₘ[T] (source ·ₘ numₘ(index)) ≐ₘ
              numₘ(token)) :
    Γ ⊢ₘ[T]
      source ≐ₘ standard_token_sequence tokens := by
  simpa [standard_token_sequence] using (standard_sequence_eq_of_function_domain_pointwise
      hTheory hTheorySentence source (tokens.map finite_numeral_term) hSource (stdtok_elements_admissible tokens) (stdtok_elements_closed tokens)
      hFunction (by simpa using hDomain) (by
        intro index element hGet
        rcases List.getElem?_eq_some_iff.mp hGet with
          ⟨hIndex, rfl⟩
        have hTokenIndex : index < tokens.length := by
          simpa using hIndex
        let token : Nat := tokens[index]
        have hTokenGet :
            tokens[index]? = some token :=
          List.getElem?_eq_some_iff.mpr
            ⟨hTokenIndex, rfl⟩
        simpa [token] using hPoint hTokenGet))
/--
不同的外部 token 列表在对象理论中给出不相等的标准序列。
长度不同时比较定义域；长度相同时选择首个可见差异位置，并利用函数项等式与逐点
求值把序列等式降为两个不同 numeral 的等式。
-/
theorem standard_token_sequence_ne
    {left right : List Nat} (hNe : left ≠ right) :
    ⊢ₘ[standard_sequence_semantics_theory]
      ¬ₘ (standard_token_sequence left ≐ₘ
        standard_token_sequence right) := by
  let leftSequence := standard_token_sequence left
  let rightSequence := standard_token_sequence right
  let equality : SetFormula :=
    leftSequence ≐ₘ rightSequence
  let Γ : Context signature := [equality]
  have hLeftSequence :
      Term.Admissible leftSequence SetSort.set := by
    simpa [leftSequence] using
      standard_token_sequence_admissible left
  have hRightSequence :
      Term.Admissible rightSequence SetSort.set := by
    simpa [rightSequence] using
      standard_token_sequence_admissible right
  nd_apply FirstOrder.Derives.negIntro
  have hEquality :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        leftSequence ≐ₘ rightSequence := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := standard_sequence_semantics_theory)
        (Γ := Γ) (φ := equality) (by simp [Γ]))
  by_cases hLength : left.length = right.length
  · have hWitness :
        ∃ (index : Nat) (hLeftIndex : index < left.length) (hRightIndex : index < right.length),
          left[index] ≠ right[index] :=
      Classical.byContradiction fun hNoWitness => by
      apply hNe
      apply List.ext_getElem hLength
      intro index hLeftIndex hRightIndex
      exact Classical.byContradiction fun hToken =>
        hNoWitness
          ⟨index, hLeftIndex, hRightIndex, hToken⟩
    rcases hWitness with
      ⟨index, hLeftIndex, hRightIndex, hToken⟩
    let leftToken := left[index]
    let rightToken := right[index]
    have hLeftGet :
        left[index]? = some leftToken := by
      simp [leftToken, hLeftIndex]
    have hRightGet :
        right[index]? = some rightToken := by
      simp [rightToken, hRightIndex]
    have hLeftValue :
        Γ ⊢ₘ[standard_sequence_semantics_theory] (leftSequence ·ₘ numₘ(index)) ≐ₘ
            numₘ(leftToken) := by
      exact FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
          simpa [leftSequence] using
            standard_token_sequence_apply_getElem?
              left hLeftGet
    have hRightValue :
        Γ ⊢ₘ[standard_sequence_semantics_theory] (rightSequence ·ₘ numₘ(index)) ≐ₘ
            numₘ(rightToken) := by
      exact FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
          simpa [rightSequence] using
            standard_token_sequence_apply_getElem?
              right hRightGet
    have hApplicationEquality :
        Γ ⊢ₘ[standard_sequence_semantics_theory] (leftSequence ·ₘ numₘ(index)) ≐ₘ (rightSequence ·ₘ numₘ(index)) :=
      function_application_term_congr_function_of_equality
        leftSequence rightSequence (numₘ(index))
        hLeftSequence hRightSequence (finite_numeral_term_admissible index)
        hEquality
    have hLeftValueSymm :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          numₘ(leftToken) ≐ₘ (leftSequence ·ₘ numₘ(index)) :=
      Metatheory.Derives.equality_symm hLeftValue
    have hLeftToRightApplication :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          numₘ(leftToken) ≐ₘ (rightSequence ·ₘ numₘ(index)) :=
      Metatheory.Derives.equality_trans
        hLeftValueSymm hApplicationEquality
    have hTokenEquality :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          numₘ(leftToken) ≐ₘ numₘ(rightToken) :=
      Metatheory.Derives.equality_trans
        hLeftToRightApplication hRightValue
    exact FirstOrder.Derives.negElim
      hTokenEquality (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) (standard_sequence_finite_numeral_ne
          (by simpa [leftToken, rightToken] using hToken)))
  · have hLeftDomain :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          domₘ(leftSequence) ≐ₘ numₘ(left.length) := by
      exact FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
          simpa [leftSequence] using
            standard_token_sequence_domain_eq_length left
    have hRightDomain :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          domₘ(rightSequence) ≐ₘ numₘ(right.length) := by
      exact FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
          simpa [rightSequence] using
            standard_token_sequence_domain_eq_length right
    have hDomainEquality :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          domₘ(leftSequence) ≐ₘ domₘ(rightSequence) :=
      domain_term_congr_of_equality
        leftSequence rightSequence
        hLeftSequence hRightSequence hEquality
    have hLeftDomainSymm :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          numₘ(left.length) ≐ₘ domₘ(leftSequence) :=
      Metatheory.Derives.equality_symm hLeftDomain
    have hLeftLengthToRightDomain :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          numₘ(left.length) ≐ₘ domₘ(rightSequence) :=
      Metatheory.Derives.equality_trans
        hLeftDomainSymm hDomainEquality
    have hLengthEquality :
        Γ ⊢ₘ[standard_sequence_semantics_theory]
          numₘ(left.length) ≐ₘ numₘ(right.length) :=
      Metatheory.Derives.equality_trans
        hLeftLengthToRightDomain hRightDomain
    exact FirstOrder.Derives.negElim
      hLengthEquality (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) (standard_sequence_finite_numeral_ne hLength))
/-- 标准 token 序列是从长度 numeral 到 `ωₘ` 的映射。 -/
theorem standard_token_sequence_is_mapping_omega (tokens : List Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      is_mapping_formula (standard_token_sequence tokens) (numₘ(tokens.length)) ωₘ := by
  let elements := tokens.map finite_numeral_term
  let sequence := standard_sequence elements
  let source := numₘ(tokens.length)
  have hElements := stdtok_elements_admissible tokens
  have hElementsClosed := stdtok_elements_closed tokens
  have hSequence : Term.Admissible sequence SetSort.set :=
    seq_admissible_m 0 hElements
  have hSource : Term.Admissible source SetSort.set :=
    finite_numeral_term_admissible tokens.length
  have hDomainEq := standard_sequence_domain_eq_numeral_length
    hElements
    (stdtok_elements_fresh tokens 0)
    (stdtok_elements_fresh tokens 1)
  have hSourceDomain :
      ⊢ₘ[standard_sequence_semantics_theory]
        source ≐ₘ domₘ(sequence) :=
    Metatheory.Derives.equality_symm
      (by simpa [sequence, source] using hDomainEq)
  simpa [elements, sequence, source, standard_token_sequence] using (standard_sequence_from_is_mapping
      0 source ωₘ hElements hElementsClosed
      hSource omega_term_admissible stdtok_omega_freeSupport_nil
      hSourceDomain (stdtok_elements_mem_omega tokens))
/-- 标准 token 序列满足有限序列空间的成员条件。 -/
theorem standard_token_sequence_finite_sequence_member (tokens : List Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      finite_sequence_member_condition ωₘ (standard_token_sequence tokens) := by
  simpa [standard_token_sequence] using (standard_sequence_member_condition_derives
      ωₘ (stdtok_elements_admissible tokens) (stdtok_elements_closed tokens)
      omega_term_admissible stdtok_omega_freeSupport_nil (stdtok_elements_mem_omega tokens))
/-- 标准 token 序列属于对象理论的 `ω`-值有限序列空间。 -/
theorem standard_token_sequence_mem_sequence_space (tokens : List Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      standard_token_sequence tokens ∈ₘ seq_spaceₘ(ωₘ) := by
  simpa [standard_token_sequence] using (standard_sequence_mem_sequence_space
      ωₘ (stdtok_elements_admissible tokens) (stdtok_elements_closed tokens)
      omega_term_admissible stdtok_omega_freeSupport_nil
      standard_sequence_omega_ne_empty (stdtok_elements_mem_omega tokens))
/-- `CodeStrₘ` 是 `ωₘ`-值有限序列空间的公开别名。 -/
theorem standard_token_sequence_mem_code_string (tokens : List Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      standard_token_sequence tokens ∈ₘ CodeStrₘ := by
  simpa [code_string_space_term] using (standard_token_sequence_mem_sequence_space tokens)
/-- 编码字符串空间由空 token 串见证为非空。 -/
theorem standard_token_sequence_code_string_ne_empty :
    ⊢ₘ[standard_sequence_semantics_theory]
      CodeStrₘ ≠ₘ ∅ₘ := by
  have hNonempty :=
    member_implies_set_nonempty (standard_token_sequence [])
      CodeStrₘ (standard_token_sequence_admissible [])
      code_string_space_term_admissible
  have hNonempty' :
      ⊢ₘ[standard_sequence_semantics_theory] (standard_token_sequence [] ∈ₘ CodeStrₘ) ⟶ₘ
          CodeStrₘ ≠ₘ ∅ₘ := by
    exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hFormula)))))
      hNonempty
  exact FirstOrder.Derives.impElim hNonempty' (standard_token_sequence_mem_code_string [])
/-! ## 算术轨迹公式的 admissibility -/
/-- 后继递归步公式保持 admissibility。 -/
private theorem stdtok_successor_step_admissible (trace point : SetTerm) (hTrace : Term.Admissible trace SetSort.set)
    (hPoint : Term.Admissible point SetSort.set) :
    Formula.Admissible ((trace ·ₘ Sₘ(point)) ≐ₘ Sₘ(trace ·ₘ point)) := by
  have hAtPoint :=
    function_application_term_admissible trace point hTrace hPoint
  exact Formula.Admissible.equal (function_application_term_admissible
      trace (Sₘ(point)) hTrace (successor_term_admissible point hPoint)) (successor_term_admissible (trace ·ₘ point) hAtPoint)
/-- 加法递归步公式保持 admissibility。 -/
private theorem stdtok_addition_step_admissible (trace point right : SetTerm) (hTrace : Term.Admissible trace SetSort.set)
    (hPoint : Term.Admissible point SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Formula.Admissible ((trace ·ₘ Sₘ(point)) ≐ₘ ((trace ·ₘ point) +ₘ right)) := by
  have hAtPoint :=
    function_application_term_admissible trace point hTrace hPoint
  exact Formula.Admissible.equal (function_application_term_admissible
      trace (Sₘ(point)) hTrace (successor_term_admissible point hPoint)) (natural_addition_term_admissible (trace ·ₘ point) right hAtPoint hRight)
/-- 乘法递归步公式保持 admissibility。 -/
private theorem stdtok_multiplication_step_admissible (trace point right : SetTerm) (hTrace : Term.Admissible trace SetSort.set)
    (hPoint : Term.Admissible point SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Formula.Admissible ((trace ·ₘ Sₘ(point)) ≐ₘ ((trace ·ₘ point) *ₘ right)) := by
  have hAtPoint :=
    function_application_term_admissible trace point hTrace hPoint
  exact Formula.Admissible.equal (function_application_term_admissible
      trace (Sₘ(point)) hTrace (successor_term_admissible point hPoint)) (natural_multiplication_term_admissible (trace ·ₘ point) right hAtPoint hRight)
/-! ## 具体 numeral 加法 -/
/-- `right, right + 1, ..., right + left` 的规范递归轨迹。 -/
private def stdtok_addition_trace_tokens (left right : Nat) : List Nat := (List.range (left + 1)).map (fun index => right + index)
private theorem stdtok_addition_trace_tokens_getElem? (left right index : Nat) (hIndex : index ≤ left) : (stdtok_addition_trace_tokens left right)[index]? =
      some (right + index) := by
  have hIndex' : index < left + 1 := Nat.lt_succ_iff.mpr hIndex
  simp [stdtok_addition_trace_tokens, hIndex']
/-- 加法递归轨迹在具体 numeral 位置满足后继递归式。 -/
private theorem stdtok_addition_step_at_numeral (left right index : Nat) (hIndex : index < left) :
    ⊢ₘ[standard_sequence_semantics_theory] (standard_token_sequence (stdtok_addition_trace_tokens left right) ·ₘ
            Sₘ(numₘ(index))) ≐ₘ
        Sₘ(standard_token_sequence (stdtok_addition_trace_tokens left right) ·ₘ
            numₘ(index)) := by
  let trace :=
    standard_token_sequence (stdtok_addition_trace_tokens left right)
  have hCurrent := standard_token_sequence_apply_getElem? (stdtok_addition_trace_tokens left right) (stdtok_addition_trace_tokens_getElem?
      left right index (Nat.le_of_lt hIndex))
  have hNext := standard_token_sequence_apply_getElem? (stdtok_addition_trace_tokens left right) (stdtok_addition_trace_tokens_getElem?
      left right (index + 1) (Nat.succ_le_iff.mpr hIndex))
  have hCurrentTerm :
      Term.Admissible (trace ·ₘ numₘ(index)) SetSort.set :=
    function_application_term_admissible trace (numₘ(index)) (standard_token_sequence_admissible (stdtok_addition_trace_tokens left right))
      (finite_numeral_term_admissible index)
  have hCurrentNumeral :
      Term.Admissible (numₘ(right + index)) SetSort.set :=
    finite_numeral_term_admissible _
  have hSuccessorCongruence :
      ⊢ₘ[standard_sequence_semantics_theory]
        Sₘ(trace ·ₘ numₘ(index)) ≐ₘ
          Sₘ(numₘ(right + index)) :=
    successor_term_congr_of_equality (trace ·ₘ numₘ(index)) (numₘ(right + index))
      hCurrentTerm hCurrentNumeral (by simpa [trace] using hCurrent)
  have hNextValue :
      ⊢ₘ[standard_sequence_semantics_theory] (trace ·ₘ numₘ(index + 1)) ≐ₘ
          Sₘ(numₘ(right + index)) := by
    simpa [finite_numeral_term, Nat.add_assoc] using hNext
  have hSuccessorBack :
      ⊢ₘ[standard_sequence_semantics_theory]
        Sₘ(numₘ(right + index)) ≐ₘ
          Sₘ(trace ·ₘ numₘ(index)) :=
    Metatheory.Derives.equality_symm hSuccessorCongruence
  have hResult := Metatheory.Derives.equality_trans
    hNextValue hSuccessorBack
  simpa [trace, finite_numeral_term] using hResult
/-- 具体 numeral 的递归式可沿指标等式运输到任意对象项。 -/
private theorem stdtok_addition_step_of_index_equality (left right index : Nat) (point : SetTerm) (hPoint : Term.Admissible point SetSort.set)
    (hIndex : index < left) :
    ⊢ₘ[standard_sequence_semantics_theory] (point ≐ₘ numₘ(index)) ⟶ₘ ((standard_token_sequence (stdtok_addition_trace_tokens left right) ·ₘ
              Sₘ(point)) ≐ₘ
          Sₘ(standard_token_sequence (stdtok_addition_trace_tokens left right) ·ₘ point)) := by
  let trace :=
    standard_token_sequence (stdtok_addition_trace_tokens left right)
  let parameter : FreeVarId := 390
  let body : SetFormula := (trace ·ₘ Sₘ(x#parameter)) ≐ₘ
      Sₘ(trace ·ₘ x#parameter)
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  have hTrace : Term.Admissible trace SetSort.set :=
    standard_token_sequence_admissible (stdtok_addition_trace_tokens left right)
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        point ≐ₘ numₘ(index) := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := standard_sequence_semantics_theory)
        (Γ := Γ) (φ := equality) (by simp [Γ]))
  have hTraceFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement trace = trace := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport trace = [] by
      exact standard_token_sequence_freeSupport_nil (stdtok_addition_trace_tokens left right)]
    simp
  have hIff :=
    Metatheory.Derives.equality_iff_of_equality (T := standard_sequence_semantics_theory) (Γ := Γ) (sort := SetSort.set) (eigen := parameter)
      (left := point) (right := numₘ(index)) (body := body)
      hEquality
  have hTransport :
      Γ ⊢ₘ[standard_sequence_semantics_theory] ((trace ·ₘ Sₘ(point)) ≐ₘ
            Sₘ(trace ·ₘ point)) ↔ₘ ((trace ·ₘ Sₘ(numₘ(index))) ≐ₘ
            Sₘ(trace ·ₘ numₘ(index))) := by
    simpa [body, Formula.substituteFree, Term.substituteFree,
      set_variable, hTraceFixed] using hIff
  have hConcrete :
      Γ ⊢ₘ[standard_sequence_semantics_theory] (trace ·ₘ Sₘ(numₘ(index))) ≐ₘ
          Sₘ(trace ·ₘ numₘ(index)) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) (by
        simpa [trace] using
          stdtok_addition_step_at_numeral
            left right index hIndex)
  simpa [Γ, equality, trace] using
    FirstOrder.Derives.iffElimLeft hTransport hConcrete
/-- 有限 numeral 成员条件蕴含加法轨迹的对应递归式。 -/
private theorem stdtok_addition_step_of_numeral_condition (left right count : Nat) (point : SetTerm) (hPoint : Term.Admissible point SetSort.set)
    (hCount : count ≤ left) :
    ⊢ₘ[standard_sequence_semantics_theory]
      stdseq_numeral_member_condition count point ⟶ₘ ((standard_token_sequence (stdtok_addition_trace_tokens left right) ·ₘ
              Sₘ(point)) ≐ₘ
          Sₘ(standard_token_sequence (stdtok_addition_trace_tokens left right) ·ₘ point)) := by
  let trace :=
    standard_token_sequence (stdtok_addition_trace_tokens left right)
  let conclusion : SetFormula := (trace ·ₘ Sₘ(point)) ≐ₘ Sₘ(trace ·ₘ point)
  simpa [trace, conclusion] using (stdseq_numeral_member_condition_elim
      count point conclusion (fun index hIndex => by
        have hIndexLeft : index < left :=
          Nat.lt_of_lt_of_le hIndex hCount
        simpa [trace, conclusion] using
          stdtok_addition_step_of_index_equality
            left right index point hPoint hIndexLeft))
/--
对象加法在任意两个具体 numeral 上计算为外部自然数加法。
证明使用标准 token 序列作为完整递归图，因而后续序列拼接无需另加算术假设。
-/
theorem standard_token_sequence_finite_numeral_addition (left right : Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      numₘ(left + right) ≐ₘ (numₘ(left) +ₘ numₘ(right)) := by
  let traceTokens := stdtok_addition_trace_tokens left right
  let trace := standard_token_sequence traceTokens
  let result := numₘ(left + right)
  have hLeftOmega :=
    standard_sequence_finite_numeral_mem_omega left
  have hRightOmega :=
    standard_sequence_finite_numeral_mem_omega right
  have hResultOmega :=
    standard_sequence_finite_numeral_mem_omega (left + right)
  have hTraceMapping :
      ⊢ₘ[standard_sequence_semantics_theory]
        is_mapping_formula trace (Sₘ(numₘ(left))) ωₘ := by
    simpa [trace, traceTokens, stdtok_addition_trace_tokens,
      finite_numeral_term] using (standard_token_sequence_is_mapping_omega traceTokens)
  have hInitial :
      ⊢ₘ[standard_sequence_semantics_theory] (trace ·ₘ ∅ₘ) ≐ₘ numₘ(right) := by
    simpa [trace, traceTokens, finite_numeral_term] using (standard_token_sequence_apply_getElem? traceTokens (stdtok_addition_trace_tokens_getElem?
          left right 0 (Nat.zero_le left)))
  have hStepOpen :
      ⊢ₘ[standard_sequence_semantics_theory] (x#390 ∈ₘ numₘ(left)) ⟶ₘ ((trace ·ₘ Sₘ(x#390)) ≐ₘ
            Sₘ(trace ·ₘ x#390)) := by
    let point : SetTerm := x#390
    have hNumeralIff :=
      stdseq_numeral_member_iff left point (set_variable_admissible 390)
    have hCases :=
      stdtok_addition_step_of_numeral_condition
        left right left point (set_variable_admissible 390) (Nat.le_refl left)
    nd_apply FirstOrder.Derives.impIntro
    have hMembership :
        [point ∈ₘ numₘ(left)]
          ⊢ₘ[standard_sequence_semantics_theory]
            point ∈ₘ numₘ(left) :=
      FirstOrder.Derives.assumption (by simp)
    have hCondition := FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hNumeralIff)
      hMembership
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hCases)
      hCondition
  have hStep :
      ⊢ₘ[standard_sequence_semantics_theory]
        ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ numₘ(left)) ⟶ₘ ((trace ·ₘ Sₘ(bₛ#0)) ≐ₘ
              Sₘ(trace ·ₘ bₛ#0)) := by
    have hTheoryFresh :
        ∀ formula, standard_sequence_semantics_theory formula → (SetSort.set, 390) ∉ Formula.freeSupport formula := by
      intro formula hFormula
      rw [(standard_sequence_semantics_theory_sentence hFormula).2]
      intro hMember
      cases hMember
    have hTraceClose :
        Term.closeFreeAt SetSort.set 390 0 trace = trace :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 390 0 trace (standard_token_sequence_admissible traceTokens).2 (by
          rw [show Term.freeSupport trace = [] by
            exact standard_token_sequence_freeSupport_nil traceTokens]
          simp)
    have hLeftClose :
        Term.closeFreeAt SetSort.set 390 0 (numₘ(left)) =
          numₘ(left) :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 390 0 (numₘ(left)) (finite_numeral_term_admissible left).2 (by rw [finite_numeral_term_freeSupport]; simp)
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := 390)
        hTheoryFresh (by simp) hStepOpen
    simpa [Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt, set_variable, hTraceClose, hLeftClose] using
      hGeneralized
  have hTerminal :
      ⊢ₘ[standard_sequence_semantics_theory] (trace ·ₘ numₘ(left)) ≐ₘ result := by
    simpa [trace, traceTokens, result, Nat.add_comm] using (standard_token_sequence_apply_getElem? traceTokens (stdtok_addition_trace_tokens_getElem?
          left right left (Nat.le_refl left)))
  have hGraph :
      ⊢ₘ[standard_sequence_semantics_theory]
        natural_addition_graph_condition (numₘ(left)) (numₘ(right)) result trace := by
    exact FirstOrder.Derives.conjIntro hTraceMapping <|
      FirstOrder.Derives.conjIntro hInitial <|
        FirstOrder.Derives.conjIntro hStep hTerminal
  have hDefinition :
      ⊢ₘ[standard_sequence_semantics_theory]
        natural_addition_definition_instance (numₘ(left)) (numₘ(right)) result := by
    apply standard_sequence_weaken_natural_exponentiation
    apply FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        natural_multiplication_theory_subset_natural_exponentiation_theory (natural_addition_theory_subset_natural_multiplication_theory
            hFormula))
    exact natural_addition_definition_instance_derives (numₘ(left)) (numₘ(right)) result (finite_numeral_term_admissible left)
      (finite_numeral_term_admissible right) (finite_numeral_term_admissible (left + right))
  have hLeftOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement (numₘ(left)) =
        numₘ(left) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (numₘ(left)) (finite_numeral_term_admissible left).2
  have hRightOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement (numₘ(right)) =
        numₘ(right) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (numₘ(right)) (finite_numeral_term_admissible right).2
  have hResultOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement result = result :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement result (finite_numeral_term_admissible (left + right)).2
  have hSpec :
      ⊢ₘ[standard_sequence_semantics_theory]
        natural_addition_spec (numₘ(left)) (numₘ(right)) result := by
    apply FirstOrder.Derives.conjIntro hResultOmega
    nd_apply FirstOrder.Derives.exists_intro (term := trace)
    simpa [natural_addition_bound_graph_condition,
      natural_addition_graph_condition,
      Formula.openAt, Formula.next_depth, Term.openAt,
      hLeftOpen, hRightOpen, hResultOpen] using hGraph
  have hContract := FirstOrder.Derives.impElim hDefinition (FirstOrder.Derives.conjIntro hLeftOmega hRightOmega)
  exact FirstOrder.Derives.iffElimLeft hContract hSpec
/-! ## 固定左参数的开放加法反演 -/
/--
对象加法在左参数 `1` 处按定义计算为后继。
这里右参数可以是任意 admissible 对象项；证明直接反演加法定义给出的递归图，
不诉诸交换律或额外算术公理。
-/
theorem standard_sequence_one_addition_eq_successor (right : SetTerm) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] (right ∈ₘ ωₘ) ⟶ₘ ((numₘ(1) +ₘ right) ≐ₘ Sₘ(right)) := by
  let condition : SetFormula := right ∈ₘ ωₘ
  let result : SetTerm := numₘ(1) +ₘ right
  let conclusion : SetFormula := result ≐ₘ Sₘ(right)
  let Γ : Context signature := [condition]
  nd_apply FirstOrder.Derives.impIntro
  have hRightOmega :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        right ∈ₘ ωₘ := by
    simpa [Γ, condition] using
      (FirstOrder.Derives.assumption
        (T := standard_sequence_semantics_theory)
        (Γ := Γ) (φ := condition) (by simp [Γ]))
  have hOneOmega :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(1) ∈ₘ ωₘ :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) (standard_sequence_finite_numeral_mem_omega 1)
  have hResult :
      Term.Admissible result SetSort.set := by
    simpa [result] using
      natural_addition_term_admissible (numₘ(1)) right (finite_numeral_term_admissible 1) hRight
  have hDefinition :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        natural_addition_definition_instance (numₘ(1)) right result := by
    apply FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ])
    apply standard_sequence_weaken_natural_exponentiation
    apply FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        natural_multiplication_theory_subset_natural_exponentiation_theory (natural_addition_theory_subset_natural_multiplication_theory
            hFormula))
    exact natural_addition_definition_instance_derives (numₘ(1)) right result (finite_numeral_term_admissible 1) hRight hResult
  have hContract :
      Γ ⊢ₘ[standard_sequence_semantics_theory] (result ≐ₘ (numₘ(1) +ₘ right)) ↔ₘ
          natural_addition_spec (numₘ(1)) right result :=
    FirstOrder.Derives.impElim hDefinition (FirstOrder.Derives.conjIntro hOneOmega hRightOmega)
  have hResultReflexive :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        result ≐ₘ (numₘ(1) +ₘ right) := by
    simpa [result] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) result)
  have hSpec :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        natural_addition_spec (numₘ(1)) right result :=
    FirstOrder.Derives.iffElimRight hContract hResultReflexive
  have hExists :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        ∃ₘ[SetSort.set],
          natural_addition_bound_graph_condition (numₘ(1)) right result :=
    FirstOrder.Derives.conjElimRight hSpec
  let graphId : FreeVarId :=
    FreshVariable.fresh_id SetSort.set [condition, conclusion]
  let graph : SetTerm := x#graphId
  let graphCondition : SetFormula :=
    natural_addition_graph_condition (numₘ(1)) right result graph
  have hGraphIdConditionFresh : (SetSort.set, graphId) ∉ Formula.freeSupport condition := by
    exact FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas := [condition, conclusion]) (formula := condition) (by simp)
  have hGraphIdConclusionFresh : (SetSort.set, graphId) ∉ Formula.freeSupport conclusion := by
    exact FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas := [condition, conclusion]) (formula := conclusion) (by simp)
  have hRightFresh : (SetSort.set, graphId) ∉ Term.freeSupport right := by
    intro hMember
    apply hGraphIdConditionFresh
    change (SetSort.set, graphId) ∈
      Formula.freeSupport (right ∈ₘ ωₘ)
    change (SetSort.set, graphId) ∈
      Term.freeSupportList [right, ωₘ]
    exact Term.mem_freeSupportList_of_mem (by simp) hMember
  have hResultFresh : (SetSort.set, graphId) ∉ Term.freeSupport result := by
    intro hMember
    apply hGraphIdConclusionFresh
    change (SetSort.set, graphId) ∈
      Formula.freeSupport (result ≐ₘ Sₘ(right))
    change (SetSort.set, graphId) ∈
      Term.freeSupport result ++ Term.freeSupport (Sₘ(right))
    exact List.mem_append_left _ hMember
  have hRightClose :
      Term.closeFreeAt SetSort.set graphId 0 right = right :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set graphId 0 right hRight.2 hRightFresh
  have hResultClose :
      Term.closeFreeAt SetSort.set graphId 0 result = result :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set graphId 0 result hResult.2 hResultFresh
  have hExists' :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        ∃ₘ[SetSort.set, graphId], graphCondition := by
    simpa [graphCondition, graph,
      natural_addition_bound_graph_condition,
      natural_addition_graph_condition,
      Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt, set_variable, set_bound_variable,
      finite_numeral_term,
      hRightClose, hResultClose] using hExists
  apply FirstOrder.Derives.exists_elim (T := standard_sequence_semantics_theory) (Γ := Γ) (sort := SetSort.set) (eigen := graphId)
      (body := graphCondition) (conclusion := conclusion)
  · intro formula hFormula
    rw [(standard_sequence_semantics_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    exact hGraphIdConditionFresh
  · exact hGraphIdConclusionFresh
  · exact hExists'
  · let Δ : Context signature := [graphCondition, condition]
    have hGraphCondition :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          graphCondition :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hInitial :
        Δ ⊢ₘ[standard_sequence_semantics_theory] (graph ·ₘ ∅ₘ) ≐ₘ right :=
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight <| by
          simpa [graphCondition,
            natural_addition_graph_condition] using
            hGraphCondition
    have hStep :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ numₘ(1)) ⟶ₘ ((graph ·ₘ Sₘ(bₛ#0)) ≐ₘ
                Sₘ(graph ·ₘ bₛ#0)) :=
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight <| by
            simpa [graphCondition,
              natural_addition_graph_condition] using
              hGraphCondition
    have hTerminal :
        Δ ⊢ₘ[standard_sequence_semantics_theory] (graph ·ₘ numₘ(1)) ≐ₘ result :=
      FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight <| by
            simpa [graphCondition,
              natural_addition_graph_condition] using
              hGraphCondition
    have hStepAtZeroRaw :=
      FirstOrder.Derives.forall_elim
        (term := numₘ(0)) hStep
    have hStepAtZero :
        Δ ⊢ₘ[standard_sequence_semantics_theory] (numₘ(0) ∈ₘ numₘ(1)) ⟶ₘ ((graph ·ₘ numₘ(1)) ≐ₘ
              Sₘ(graph ·ₘ numₘ(0))) := by
      simpa [finite_numeral_term, Formula.openAt,
        Term.openAt, graph, set_variable] using hStepAtZeroRaw
    have hZeroMemOne :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          numₘ(0) ∈ₘ numₘ(1) :=
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp [Δ]) (standard_sequence_finite_numeral_mem_of_lt 0 1 (by omega))
    have hGraphStep :
        Δ ⊢ₘ[standard_sequence_semantics_theory] (graph ·ₘ numₘ(1)) ≐ₘ
            Sₘ(graph ·ₘ numₘ(0)) :=
      FirstOrder.Derives.impElim hStepAtZero hZeroMemOne
    have hInitial' :
        Δ ⊢ₘ[standard_sequence_semantics_theory] (graph ·ₘ numₘ(0)) ≐ₘ right := by
      simpa [finite_numeral_term] using hInitial
    have hSuccessorInitial :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          Sₘ(graph ·ₘ numₘ(0)) ≐ₘ Sₘ(right) :=
      successor_term_congr_of_equality (graph ·ₘ numₘ(0)) right (function_application_term_admissible
          graph (numₘ(0)) (set_variable_admissible graphId) (finite_numeral_term_admissible 0))
        hRight hInitial'
    have hGraphOneSuccessor :
        Δ ⊢ₘ[standard_sequence_semantics_theory] (graph ·ₘ numₘ(1)) ≐ₘ Sₘ(right) :=
      Metatheory.Derives.equality_trans
        hGraphStep hSuccessorInitial
    have hResultGraphOne :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          result ≐ₘ (graph ·ₘ numₘ(1)) :=
      Metatheory.Derives.equality_symm hTerminal
    have hConclusion :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          result ≐ₘ Sₘ(right) :=
      Metatheory.Derives.equality_trans
        hResultGraphOne hGraphOneSuccessor
    simpa [conclusion] using hConclusion
/--
对象加法在左参数 `2` 处等于左参数 `1` 结果的后继。
该形式正好对应 quotation 固定前缀中相邻的 `1 + start` 与 `2 + start`。
-/
theorem standard_sequence_two_addition_eq_successor_one (right : SetTerm) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory] (right ∈ₘ ωₘ) ⟶ₘ ((numₘ(2) +ₘ right) ≐ₘ
          Sₘ(numₘ(1) +ₘ right)) := by
  let condition : SetFormula := right ∈ₘ ωₘ
  let oneResult : SetTerm := numₘ(1) +ₘ right
  let result : SetTerm := numₘ(2) +ₘ right
  let conclusion : SetFormula :=
    result ≐ₘ Sₘ(oneResult)
  let Γ : Context signature := [condition]
  nd_apply FirstOrder.Derives.impIntro
  have hRightOmega :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        right ∈ₘ ωₘ := by
    simpa [Γ, condition] using
      (FirstOrder.Derives.assumption
        (T := standard_sequence_semantics_theory)
        (Γ := Γ) (φ := condition) (by simp [Γ]))
  have hTwoOmega :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(2) ∈ₘ ωₘ :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) (standard_sequence_finite_numeral_mem_omega 2)
  have hOneResult :
      Term.Admissible oneResult SetSort.set := by
    simpa [oneResult] using
      natural_addition_term_admissible (numₘ(1)) right (finite_numeral_term_admissible 1) hRight
  have hResult :
      Term.Admissible result SetSort.set := by
    simpa [result] using
      natural_addition_term_admissible (numₘ(2)) right (finite_numeral_term_admissible 2) hRight
  have hDefinition :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        natural_addition_definition_instance (numₘ(2)) right result := by
    apply FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ])
    apply standard_sequence_weaken_natural_exponentiation
    apply FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        natural_multiplication_theory_subset_natural_exponentiation_theory (natural_addition_theory_subset_natural_multiplication_theory
            hFormula))
    exact natural_addition_definition_instance_derives (numₘ(2)) right result (finite_numeral_term_admissible 2) hRight hResult
  have hContract :
      Γ ⊢ₘ[standard_sequence_semantics_theory] (result ≐ₘ (numₘ(2) +ₘ right)) ↔ₘ
          natural_addition_spec (numₘ(2)) right result :=
    FirstOrder.Derives.impElim hDefinition (FirstOrder.Derives.conjIntro hTwoOmega hRightOmega)
  have hResultReflexive :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        result ≐ₘ (numₘ(2) +ₘ right) := by
    simpa [result] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) result)
  have hSpec :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        natural_addition_spec (numₘ(2)) right result :=
    FirstOrder.Derives.iffElimRight hContract hResultReflexive
  have hExists :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        ∃ₘ[SetSort.set],
          natural_addition_bound_graph_condition (numₘ(2)) right result :=
    FirstOrder.Derives.conjElimRight hSpec
  let graphId : FreeVarId :=
    FreshVariable.fresh_id SetSort.set [condition, conclusion]
  let graph : SetTerm := x#graphId
  let graphCondition : SetFormula :=
    natural_addition_graph_condition (numₘ(2)) right result graph
  have hGraphIdConditionFresh : (SetSort.set, graphId) ∉ Formula.freeSupport condition := by
    exact FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas := [condition, conclusion]) (formula := condition) (by simp)
  have hGraphIdConclusionFresh : (SetSort.set, graphId) ∉ Formula.freeSupport conclusion := by
    exact FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas := [condition, conclusion]) (formula := conclusion) (by simp)
  have hRightFresh : (SetSort.set, graphId) ∉ Term.freeSupport right := by
    intro hMember
    apply hGraphIdConditionFresh
    change (SetSort.set, graphId) ∈
      Formula.freeSupport (right ∈ₘ ωₘ)
    change (SetSort.set, graphId) ∈
      Term.freeSupportList [right, ωₘ]
    exact Term.mem_freeSupportList_of_mem (by simp) hMember
  have hResultFresh : (SetSort.set, graphId) ∉ Term.freeSupport result := by
    intro hMember
    apply hGraphIdConclusionFresh
    change (SetSort.set, graphId) ∈
      Formula.freeSupport (result ≐ₘ Sₘ(oneResult))
    change (SetSort.set, graphId) ∈
      Term.freeSupport result ++ Term.freeSupport (Sₘ(oneResult))
    exact List.mem_append_left _ hMember
  have hRightClose :
      Term.closeFreeAt SetSort.set graphId 0 right = right :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set graphId 0 right hRight.2 hRightFresh
  have hResultClose :
      Term.closeFreeAt SetSort.set graphId 0 result = result :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set graphId 0 result hResult.2 hResultFresh
  have hExists' :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        ∃ₘ[SetSort.set, graphId], graphCondition := by
    simpa [graphCondition, graph,
      natural_addition_bound_graph_condition,
      natural_addition_graph_condition,
      Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt, set_variable, set_bound_variable,
      finite_numeral_term,
      hRightClose, hResultClose] using hExists
  apply FirstOrder.Derives.exists_elim (T := standard_sequence_semantics_theory) (Γ := Γ) (sort := SetSort.set) (eigen := graphId)
      (body := graphCondition) (conclusion := conclusion)
  · intro formula hFormula
    rw [(standard_sequence_semantics_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    exact hGraphIdConditionFresh
  · exact hGraphIdConclusionFresh
  · exact hExists'
  · let Δ : Context signature := [graphCondition, condition]
    have hGraphCondition :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          graphCondition :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hInitial :
        Δ ⊢ₘ[standard_sequence_semantics_theory] (graph ·ₘ numₘ(0)) ≐ₘ right := by
      simpa [graphCondition,
        natural_addition_graph_condition,
        finite_numeral_term] using (FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight hGraphCondition)
    have hStep :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ numₘ(2)) ⟶ₘ ((graph ·ₘ Sₘ(bₛ#0)) ≐ₘ
                Sₘ(graph ·ₘ bₛ#0)) :=
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight <| by
            simpa [graphCondition,
              natural_addition_graph_condition] using
              hGraphCondition
    have hTerminal :
        Δ ⊢ₘ[standard_sequence_semantics_theory] (graph ·ₘ numₘ(2)) ≐ₘ result :=
      FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight <| by
            simpa [graphCondition,
              natural_addition_graph_condition] using
              hGraphCondition
    have hStepAtZeroRaw :=
      FirstOrder.Derives.forall_elim
        (term := numₘ(0)) hStep
    have hStepAtZero :
        Δ ⊢ₘ[standard_sequence_semantics_theory] (numₘ(0) ∈ₘ numₘ(2)) ⟶ₘ ((graph ·ₘ numₘ(1)) ≐ₘ
              Sₘ(graph ·ₘ numₘ(0))) := by
      simpa [finite_numeral_term, Formula.openAt,
        Term.openAt, graph, set_variable] using hStepAtZeroRaw
    have hStepAtOneRaw :=
      FirstOrder.Derives.forall_elim
        (term := numₘ(1)) hStep
    have hStepAtOne :
        Δ ⊢ₘ[standard_sequence_semantics_theory] (numₘ(1) ∈ₘ numₘ(2)) ⟶ₘ ((graph ·ₘ numₘ(2)) ≐ₘ
              Sₘ(graph ·ₘ numₘ(1))) := by
      simpa [finite_numeral_term, Formula.openAt,
        Term.openAt, graph, set_variable] using hStepAtOneRaw
    have hZeroMemTwo :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          numₘ(0) ∈ₘ numₘ(2) :=
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp [Δ]) (standard_sequence_finite_numeral_mem_of_lt 0 2 (by omega))
    have hOneMemTwo :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          numₘ(1) ∈ₘ numₘ(2) :=
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp [Δ]) (standard_sequence_finite_numeral_mem_of_lt 1 2 (by omega))
    have hGraphOneStep :
        Δ ⊢ₘ[standard_sequence_semantics_theory] (graph ·ₘ numₘ(1)) ≐ₘ
            Sₘ(graph ·ₘ numₘ(0)) :=
      FirstOrder.Derives.impElim hStepAtZero hZeroMemTwo
    have hGraphTwoStep :
        Δ ⊢ₘ[standard_sequence_semantics_theory] (graph ·ₘ numₘ(2)) ≐ₘ
            Sₘ(graph ·ₘ numₘ(1)) :=
      FirstOrder.Derives.impElim hStepAtOne hOneMemTwo
    have hSuccessorInitial :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          Sₘ(graph ·ₘ numₘ(0)) ≐ₘ Sₘ(right) :=
      successor_term_congr_of_equality (graph ·ₘ numₘ(0)) right (function_application_term_admissible
          graph (numₘ(0)) (set_variable_admissible graphId) (finite_numeral_term_admissible 0))
        hRight hInitial
    have hGraphOne :
        Δ ⊢ₘ[standard_sequence_semantics_theory] (graph ·ₘ numₘ(1)) ≐ₘ Sₘ(right) :=
      Metatheory.Derives.equality_trans
        hGraphOneStep hSuccessorInitial
    have hSuccessorGraphOne :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          Sₘ(graph ·ₘ numₘ(1)) ≐ₘ Sₘ(Sₘ(right)) :=
      successor_term_congr_of_equality (graph ·ₘ numₘ(1)) (Sₘ(right)) (function_application_term_admissible
          graph (numₘ(1)) (set_variable_admissible graphId) (finite_numeral_term_admissible 1)) (successor_term_admissible right hRight)
        hGraphOne
    have hGraphTwo :
        Δ ⊢ₘ[standard_sequence_semantics_theory] (graph ·ₘ numₘ(2)) ≐ₘ Sₘ(Sₘ(right)) :=
      Metatheory.Derives.equality_trans
        hGraphTwoStep hSuccessorGraphOne
    have hResultGraphTwo :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          result ≐ₘ (graph ·ₘ numₘ(2)) :=
      Metatheory.Derives.equality_symm hTerminal
    have hResultTwoSuccessors :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          result ≐ₘ Sₘ(Sₘ(right)) :=
      Metatheory.Derives.equality_trans
        hResultGraphTwo hGraphTwo
    have hOneEquality :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          oneResult ≐ₘ Sₘ(right) := by
      have hImp :=
        standard_sequence_one_addition_eq_successor right hRight
      exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp [Δ]) <| by
            simpa [oneResult] using hImp) (by
          simpa [condition] using
            (FirstOrder.Derives.assumption
              (T := standard_sequence_semantics_theory)
              (Γ := Δ) (φ := condition) (by simp [Δ])))
    have hSuccessorOne :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          Sₘ(oneResult) ≐ₘ Sₘ(Sₘ(right)) :=
      successor_term_congr_of_equality
        oneResult (Sₘ(right))
        hOneResult (successor_term_admissible right hRight)
        hOneEquality
    have hTwoSuccessorsOne :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          Sₘ(Sₘ(right)) ≐ₘ Sₘ(oneResult) :=
      Metatheory.Derives.equality_symm hSuccessorOne
    have hConclusion :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          result ≐ₘ Sₘ(oneResult) :=
      Metatheory.Derives.equality_trans
        hResultTwoSuccessors hTwoSuccessorsOne
    simpa [conclusion] using hConclusion
/-! ## 具体 numeral 乘法 -/
/-- `0, right, 2 * right, ..., left * right` 的规范乘法轨迹。 -/
private def stdtok_multiplication_trace_tokens (left right : Nat) : List Nat := (List.range (left + 1)).map (fun index => index * right)
private theorem stdtok_multiplication_trace_tokens_getElem? (left right index : Nat) (hIndex : index ≤ left) :
    (stdtok_multiplication_trace_tokens left right)[index]? =
      some (index * right) := by
  have hIndex' : index < left + 1 := Nat.lt_succ_iff.mpr hIndex
  simp [stdtok_multiplication_trace_tokens, hIndex']
/-- 乘法轨迹在具体 numeral 位置满足“累加右因子”的递归式。 -/
private theorem stdtok_multiplication_step_at_numeral (left right index : Nat) (hIndex : index < left) :
    ⊢ₘ[standard_sequence_semantics_theory] (standard_token_sequence (stdtok_multiplication_trace_tokens left right) ·ₘ
            Sₘ(numₘ(index))) ≐ₘ ((standard_token_sequence (stdtok_multiplication_trace_tokens left right) ·ₘ
              numₘ(index)) +ₘ
          numₘ(right)) := by
  let trace :=
    standard_token_sequence (stdtok_multiplication_trace_tokens left right)
  let currentValue := index * right
  let nextValue := (index + 1) * right
  have hCurrent := standard_token_sequence_apply_getElem? (stdtok_multiplication_trace_tokens left right) (stdtok_multiplication_trace_tokens_getElem?
      left right index (Nat.le_of_lt hIndex))
  have hNext := standard_token_sequence_apply_getElem? (stdtok_multiplication_trace_tokens left right) (stdtok_multiplication_trace_tokens_getElem?
      left right (index + 1) (Nat.succ_le_iff.mpr hIndex))
  have hCurrentTerm :
      Term.Admissible (trace ·ₘ numₘ(index)) SetSort.set :=
    function_application_term_admissible
      trace (numₘ(index)) (standard_token_sequence_admissible (stdtok_multiplication_trace_tokens left right)) (finite_numeral_term_admissible index)
  have hCurrentNumeral :
      Term.Admissible (numₘ(currentValue)) SetSort.set :=
    finite_numeral_term_admissible currentValue
  have hRightNumeral :
      Term.Admissible (numₘ(right)) SetSort.set :=
    finite_numeral_term_admissible right
  have hRightRefl :
      ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(right) ≐ₘ numₘ(right) :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) (numₘ(right))
  have hAdditionCongruence :
      ⊢ₘ[standard_sequence_semantics_theory] ((trace ·ₘ numₘ(index)) +ₘ numₘ(right)) ≐ₘ (numₘ(currentValue) +ₘ numₘ(right)) :=
    natural_addition_term_congr_of_equalities (trace ·ₘ numₘ(index)) (numₘ(currentValue)) (numₘ(right)) (numₘ(right))
      hCurrentTerm hCurrentNumeral hRightNumeral hRightNumeral (by simpa [trace, currentValue] using hCurrent)
      hRightRefl
  have hNumeralAddition :=
    standard_token_sequence_finite_numeral_addition
      currentValue right
  have hAdditionBack :
      ⊢ₘ[standard_sequence_semantics_theory] (numₘ(currentValue) +ₘ numₘ(right)) ≐ₘ
          numₘ(currentValue + right) :=
    Metatheory.Derives.equality_symm hNumeralAddition
  have hAdditionValue :
      ⊢ₘ[standard_sequence_semantics_theory] ((trace ·ₘ numₘ(index)) +ₘ numₘ(right)) ≐ₘ
          numₘ(currentValue + right) :=
    Metatheory.Derives.equality_trans
      hAdditionCongruence hAdditionBack
  have hAdditionValueBack :
      ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(currentValue + right) ≐ₘ ((trace ·ₘ numₘ(index)) +ₘ numₘ(right)) :=
    Metatheory.Derives.equality_symm hAdditionValue
  have hNextValue :
      ⊢ₘ[standard_sequence_semantics_theory] (trace ·ₘ Sₘ(numₘ(index))) ≐ₘ
          numₘ(currentValue + right) := by
    simpa [trace, currentValue, nextValue,
      finite_numeral_term, Nat.succ_mul] using hNext
  exact Metatheory.Derives.equality_trans
    hNextValue hAdditionValueBack
/-- 具体乘法递归步可沿指标等式运输到任意对象项。 -/
private theorem stdtok_multiplication_step_of_index_equality (left right index : Nat) (point : SetTerm) (hPoint : Term.Admissible point SetSort.set)
    (hIndex : index < left) :
    ⊢ₘ[standard_sequence_semantics_theory] (point ≐ₘ numₘ(index)) ⟶ₘ ((standard_token_sequence (stdtok_multiplication_trace_tokens left right) ·ₘ
              Sₘ(point)) ≐ₘ ((standard_token_sequence (stdtok_multiplication_trace_tokens left right) ·ₘ
                point) +ₘ
            numₘ(right))) := by
  let trace :=
    standard_token_sequence (stdtok_multiplication_trace_tokens left right)
  let parameter : FreeVarId := 388
  let body : SetFormula := (trace ·ₘ Sₘ(x#parameter)) ≐ₘ ((trace ·ₘ x#parameter) +ₘ numₘ(right))
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  have hTrace : Term.Admissible trace SetSort.set :=
    standard_token_sequence_admissible (stdtok_multiplication_trace_tokens left right)
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        point ≐ₘ numₘ(index) := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := standard_sequence_semantics_theory)
        (Γ := Γ) (φ := equality) (by simp [Γ]))
  have hTraceFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement trace = trace := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport trace = [] by
      exact standard_token_sequence_freeSupport_nil (stdtok_multiplication_trace_tokens left right)]
    simp
  have hRightFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement (numₘ(right)) =
        numₘ(right) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    simp
  have hIff :=
    Metatheory.Derives.equality_iff_of_equality (T := standard_sequence_semantics_theory) (Γ := Γ) (sort := SetSort.set) (eigen := parameter)
      (left := point) (right := numₘ(index)) (body := body)
      hEquality
  have hTransport :
      Γ ⊢ₘ[standard_sequence_semantics_theory] ((trace ·ₘ Sₘ(point)) ≐ₘ ((trace ·ₘ point) +ₘ numₘ(right))) ↔ₘ ((trace ·ₘ Sₘ(numₘ(index))) ≐ₘ
            ((trace ·ₘ numₘ(index)) +ₘ numₘ(right))) := by
    simpa [body, Formula.substituteFree, Term.substituteFree,
      set_variable, hTraceFixed, hRightFixed] using hIff
  have hConcrete :
      Γ ⊢ₘ[standard_sequence_semantics_theory] (trace ·ₘ Sₘ(numₘ(index))) ≐ₘ ((trace ·ₘ numₘ(index)) +ₘ numₘ(right)) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) (by
        simpa [trace] using
          stdtok_multiplication_step_at_numeral
            left right index hIndex)
  simpa [Γ, equality, trace] using
    FirstOrder.Derives.iffElimLeft hTransport hConcrete
/-- 对象乘法在任意两个具体 numeral 上计算为外部自然数乘法。 -/
theorem standard_token_sequence_finite_numeral_multiplication (left right : Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      numₘ(left * right) ≐ₘ (numₘ(left) *ₘ numₘ(right)) := by
  let traceTokens := stdtok_multiplication_trace_tokens left right
  let trace := standard_token_sequence traceTokens
  let result := numₘ(left * right)
  have hLeftOmega :=
    standard_sequence_finite_numeral_mem_omega left
  have hRightOmega :=
    standard_sequence_finite_numeral_mem_omega right
  have hResultOmega :=
    standard_sequence_finite_numeral_mem_omega (left * right)
  have hTraceMapping :
      ⊢ₘ[standard_sequence_semantics_theory]
        is_mapping_formula trace (Sₘ(numₘ(left))) ωₘ := by
    simpa [trace, traceTokens, stdtok_multiplication_trace_tokens,
      finite_numeral_term] using (standard_token_sequence_is_mapping_omega traceTokens)
  have hInitial :
      ⊢ₘ[standard_sequence_semantics_theory] (trace ·ₘ ∅ₘ) ≐ₘ ∅ₘ := by
    simpa [trace, traceTokens, finite_numeral_term] using (standard_token_sequence_apply_getElem? traceTokens (stdtok_multiplication_trace_tokens_getElem?
          left right 0 (Nat.zero_le left)))
  have hStepOpen :
      ⊢ₘ[standard_sequence_semantics_theory] (x#387 ∈ₘ numₘ(left)) ⟶ₘ ((trace ·ₘ Sₘ(x#387)) ≐ₘ ((trace ·ₘ x#387) +ₘ numₘ(right))) := by
    let point : SetTerm := x#387
    let conclusion : SetFormula := (trace ·ₘ Sₘ(point)) ≐ₘ ((trace ·ₘ point) +ₘ numₘ(right))
    have hPoint : Term.Admissible point SetSort.set :=
      set_variable_admissible 387
    have hCases :
        ⊢ₘ[standard_sequence_semantics_theory]
          stdseq_numeral_member_condition left point ⟶ₘ conclusion :=
      stdseq_numeral_member_condition_elim
        left point conclusion (fun index hIndex => by
          simpa [conclusion, point, trace] using
            stdtok_multiplication_step_of_index_equality
              left right index point hPoint hIndex)
    have hNumeralIff :=
      stdseq_numeral_member_iff left point hPoint
    nd_apply FirstOrder.Derives.impIntro
    have hMembership :
        [point ∈ₘ numₘ(left)]
          ⊢ₘ[standard_sequence_semantics_theory]
            point ∈ₘ numₘ(left) :=
      FirstOrder.Derives.assumption (by simp)
    have hCondition := FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hNumeralIff)
      hMembership
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hCases)
      hCondition
  have hStep :
      ⊢ₘ[standard_sequence_semantics_theory]
        ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ numₘ(left)) ⟶ₘ ((trace ·ₘ Sₘ(bₛ#0)) ≐ₘ ((trace ·ₘ bₛ#0) +ₘ numₘ(right))) := by
    have hTheoryFresh :
        ∀ formula, standard_sequence_semantics_theory formula → (SetSort.set, 387) ∉ Formula.freeSupport formula := by
      intro formula hFormula
      rw [(standard_sequence_semantics_theory_sentence hFormula).2]
      intro hMember
      cases hMember
    have hTraceClose :
        Term.closeFreeAt SetSort.set 387 0 trace = trace :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 387 0 trace (standard_token_sequence_admissible traceTokens).2 (by
          rw [show Term.freeSupport trace = [] by
            exact standard_token_sequence_freeSupport_nil traceTokens]
          simp)
    have hLeftClose :
        Term.closeFreeAt SetSort.set 387 0 (numₘ(left)) =
          numₘ(left) :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 387 0 (numₘ(left)) (finite_numeral_term_admissible left).2 (by rw [finite_numeral_term_freeSupport]; simp)
    have hRightClose :
        Term.closeFreeAt SetSort.set 387 0 (numₘ(right)) =
          numₘ(right) :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 387 0 (numₘ(right)) (finite_numeral_term_admissible right).2 (by rw [finite_numeral_term_freeSupport]; simp)
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := 387)
        hTheoryFresh (by simp) hStepOpen
    simpa [Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt, set_variable,
      hTraceClose, hLeftClose, hRightClose] using hGeneralized
  have hTerminal :
      ⊢ₘ[standard_sequence_semantics_theory] (trace ·ₘ numₘ(left)) ≐ₘ result := by
    simpa [trace, traceTokens, result] using (standard_token_sequence_apply_getElem? traceTokens (stdtok_multiplication_trace_tokens_getElem?
          left right left (Nat.le_refl left)))
  have hGraph :
      ⊢ₘ[standard_sequence_semantics_theory]
        natural_multiplication_graph_condition (numₘ(left)) (numₘ(right)) result trace :=
    FirstOrder.Derives.conjIntro hTraceMapping <|
      FirstOrder.Derives.conjIntro hInitial <|
        FirstOrder.Derives.conjIntro hStep hTerminal
  have hDefinition :
      ⊢ₘ[standard_sequence_semantics_theory]
        natural_multiplication_definition_instance (numₘ(left)) (numₘ(right)) result := by
    apply standard_sequence_weaken_natural_exponentiation
    apply FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        natural_multiplication_theory_subset_natural_exponentiation_theory
          hFormula)
    exact natural_multiplication_definition_instance_derives (numₘ(left)) (numₘ(right)) result (finite_numeral_term_admissible left)
      (finite_numeral_term_admissible right) (finite_numeral_term_admissible (left * right))
  have hLeftOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement (numₘ(left)) =
        numₘ(left) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (numₘ(left)) (finite_numeral_term_admissible left).2
  have hRightOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement (numₘ(right)) =
        numₘ(right) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (numₘ(right)) (finite_numeral_term_admissible right).2
  have hResultOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement result = result :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement result (finite_numeral_term_admissible (left * right)).2
  have hSpec :
      ⊢ₘ[standard_sequence_semantics_theory]
    natural_multiplication_spec (numₘ(left)) (numₘ(right)) result := by
    apply FirstOrder.Derives.conjIntro hResultOmega
    nd_apply FirstOrder.Derives.exists_intro (term := trace)
    simpa [natural_multiplication_bound_graph_condition,
      natural_multiplication_graph_condition,
      Formula.openAt, Formula.next_depth, Term.openAt,
      hLeftOpen, hRightOpen, hResultOpen] using hGraph
  have hContract := FirstOrder.Derives.impElim hDefinition (FirstOrder.Derives.conjIntro hLeftOmega hRightOmega)
  exact FirstOrder.Derives.iffElimLeft hContract hSpec
/-! ## 具体 numeral 幂运算 -/
/-- `1, base, base², ..., base^exponent` 的规范幂轨迹。 -/
private def stdtok_exponentiation_trace_tokens (base exponent : Nat) : List Nat := (List.range (exponent + 1)).map (fun index => base ^ index)
private theorem stdtok_exponentiation_trace_tokens_getElem? (base exponent index : Nat) (hIndex : index ≤ exponent) :
    (stdtok_exponentiation_trace_tokens base exponent)[index]? =
      some (base ^ index) := by
  have hIndex' : index < exponent + 1 := Nat.lt_succ_iff.mpr hIndex
  simp [stdtok_exponentiation_trace_tokens, hIndex']
/-- 幂轨迹在具体 numeral 位置满足“乘以底数”的递归式。 -/
private theorem stdtok_exponentiation_step_at_numeral (base exponent index : Nat) (hIndex : index < exponent) :
    ⊢ₘ[standard_sequence_semantics_theory] (standard_token_sequence (stdtok_exponentiation_trace_tokens base exponent) ·ₘ
            Sₘ(numₘ(index))) ≐ₘ ((standard_token_sequence (stdtok_exponentiation_trace_tokens base exponent) ·ₘ
              numₘ(index)) *ₘ
          numₘ(base)) := by
  let trace :=
    standard_token_sequence (stdtok_exponentiation_trace_tokens base exponent)
  let currentValue := base ^ index
  have hCurrent := standard_token_sequence_apply_getElem? (stdtok_exponentiation_trace_tokens base exponent) (stdtok_exponentiation_trace_tokens_getElem?
      base exponent index (Nat.le_of_lt hIndex))
  have hNext := standard_token_sequence_apply_getElem? (stdtok_exponentiation_trace_tokens base exponent) (stdtok_exponentiation_trace_tokens_getElem?
      base exponent (index + 1) (Nat.succ_le_iff.mpr hIndex))
  have hCurrentTerm :
      Term.Admissible (trace ·ₘ numₘ(index)) SetSort.set :=
    function_application_term_admissible
      trace (numₘ(index)) (standard_token_sequence_admissible (stdtok_exponentiation_trace_tokens base exponent)) (finite_numeral_term_admissible index)
  have hCurrentNumeral :
      Term.Admissible (numₘ(currentValue)) SetSort.set :=
    finite_numeral_term_admissible currentValue
  have hBaseNumeral :
      Term.Admissible (numₘ(base)) SetSort.set :=
    finite_numeral_term_admissible base
  have hMultiplicationCongruence :
      ⊢ₘ[standard_sequence_semantics_theory] ((trace ·ₘ numₘ(index)) *ₘ numₘ(base)) ≐ₘ (numₘ(currentValue) *ₘ numₘ(base)) := by
    let parameter : FreeVarId := 384
    let leftProduct := (trace ·ₘ numₘ(index)) *ₘ numₘ(base)
    let body : SetFormula :=
      leftProduct ≐ₘ ((x#parameter) *ₘ numₘ(base))
    have hLeftProduct :
        Term.Admissible leftProduct SetSort.set :=
      natural_multiplication_term_admissible (trace ·ₘ numₘ(index)) (numₘ(base))
        hCurrentTerm hBaseNumeral
    have hLeftFixed (replacement : SetTerm) :
        Term.substituteFree SetSort.set parameter replacement leftProduct =
          leftProduct := by
      apply Term.substituteFree_eq_self_of_not_mem
      have hTraceSupport : Term.freeSupport trace = [] := by
        exact standard_token_sequence_freeSupport_nil (stdtok_exponentiation_trace_tokens base exponent)
      rw [show Term.freeSupport leftProduct = [] by
        simp [leftProduct,
          Term.freeSupport, Term.freeSupportList,
          hTraceSupport, finite_numeral_term_freeSupport]]
      simp
    have hBaseFixed (replacement : SetTerm) :
        Term.substituteFree SetSort.set parameter replacement (numₘ(base)) =
          numₘ(base) := by
      apply Term.substituteFree_eq_self_of_not_mem
      rw [finite_numeral_term_freeSupport]
      simp
    have hReflexive :
        ⊢ₘ[standard_sequence_semantics_theory]
          body⟪SetSort.set, parameter ↦ trace ·ₘ numₘ(index)⟫ₘ := by
      simpa [body, leftProduct,
        Formula.substituteFree, Term.substituteFree,
        natural_multiplication_term, set_variable,
        hLeftFixed, hBaseFixed] using
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) leftProduct)
    have hTransport :=
      FirstOrder.Derives.eq_subst_m (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := parameter)
        (left := trace ·ₘ numₘ(index)) (right := numₘ(currentValue)) (body := body)
        (by simpa [trace, currentValue] using hCurrent)
        hReflexive
    simpa [body, leftProduct,
      Formula.substituteFree, Term.substituteFree,
      natural_multiplication_term, set_variable,
      hLeftFixed, hBaseFixed] using hTransport
  have hNumeralMultiplication :=
    standard_token_sequence_finite_numeral_multiplication
      currentValue base
  have hMultiplicationBack :
      ⊢ₘ[standard_sequence_semantics_theory] (numₘ(currentValue) *ₘ numₘ(base)) ≐ₘ
          numₘ(currentValue * base) :=
    Metatheory.Derives.equality_symm hNumeralMultiplication
  have hMultiplicationValue :
      ⊢ₘ[standard_sequence_semantics_theory] ((trace ·ₘ numₘ(index)) *ₘ numₘ(base)) ≐ₘ
          numₘ(currentValue * base) :=
    Metatheory.Derives.equality_trans
      hMultiplicationCongruence hMultiplicationBack
  have hMultiplicationValueBack :
      ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(currentValue * base) ≐ₘ ((trace ·ₘ numₘ(index)) *ₘ numₘ(base)) :=
    Metatheory.Derives.equality_symm hMultiplicationValue
  have hNextValue :
      ⊢ₘ[standard_sequence_semantics_theory] (trace ·ₘ Sₘ(numₘ(index))) ≐ₘ
          numₘ(currentValue * base) := by
    simpa [trace, currentValue, finite_numeral_term,
      Nat.pow_succ] using hNext
  exact Metatheory.Derives.equality_trans
    hNextValue hMultiplicationValueBack
/-- 具体幂递归步可沿指标等式运输到任意对象项。 -/
private theorem stdtok_exponentiation_step_of_index_equality (base exponent index : Nat) (point : SetTerm) (hPoint : Term.Admissible point SetSort.set)
    (hIndex : index < exponent) :
    ⊢ₘ[standard_sequence_semantics_theory] (point ≐ₘ numₘ(index)) ⟶ₘ ((standard_token_sequence (stdtok_exponentiation_trace_tokens base exponent) ·ₘ
              Sₘ(point)) ≐ₘ ((standard_token_sequence (stdtok_exponentiation_trace_tokens base exponent) ·ₘ
                point) *ₘ
            numₘ(base))) := by
  let trace :=
    standard_token_sequence (stdtok_exponentiation_trace_tokens base exponent)
  let parameter : FreeVarId := 386
  let body : SetFormula := (trace ·ₘ Sₘ(x#parameter)) ≐ₘ ((trace ·ₘ x#parameter) *ₘ numₘ(base))
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  have hTrace : Term.Admissible trace SetSort.set :=
    standard_token_sequence_admissible (stdtok_exponentiation_trace_tokens base exponent)
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        point ≐ₘ numₘ(index) := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := standard_sequence_semantics_theory)
        (Γ := Γ) (φ := equality) (by simp [Γ]))
  have hTraceFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement trace = trace := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport trace = [] by
      exact standard_token_sequence_freeSupport_nil (stdtok_exponentiation_trace_tokens base exponent)]
    simp
  have hBaseFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement (numₘ(base)) =
        numₘ(base) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    simp
  have hIff :=
    Metatheory.Derives.equality_iff_of_equality (T := standard_sequence_semantics_theory) (Γ := Γ) (sort := SetSort.set) (eigen := parameter)
      (left := point) (right := numₘ(index)) (body := body)
      hEquality
  have hTransport :
      Γ ⊢ₘ[standard_sequence_semantics_theory] ((trace ·ₘ Sₘ(point)) ≐ₘ ((trace ·ₘ point) *ₘ numₘ(base))) ↔ₘ ((trace ·ₘ Sₘ(numₘ(index))) ≐ₘ
            ((trace ·ₘ numₘ(index)) *ₘ numₘ(base))) := by
    simpa [body, Formula.substituteFree, Term.substituteFree,
      set_variable, hTraceFixed, hBaseFixed] using hIff
  have hConcrete :
      Γ ⊢ₘ[standard_sequence_semantics_theory] (trace ·ₘ Sₘ(numₘ(index))) ≐ₘ ((trace ·ₘ numₘ(index)) *ₘ numₘ(base)) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) (by
        simpa [trace] using
          stdtok_exponentiation_step_at_numeral
            base exponent index hIndex)
  simpa [Γ, equality, trace] using
    FirstOrder.Derives.iffElimLeft hTransport hConcrete
/-- 对象幂运算在具体 numeral 上计算为外部自然数幂。 -/
theorem standard_token_sequence_finite_numeral_exponentiation (base exponent : Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      numₘ(base ^ exponent) ≐ₘ (numₘ(base) ^ₘ numₘ(exponent)) := by
  let traceTokens := stdtok_exponentiation_trace_tokens base exponent
  let trace := standard_token_sequence traceTokens
  let result := numₘ(base ^ exponent)
  have hBaseOmega :=
    standard_sequence_finite_numeral_mem_omega base
  have hExponentOmega :=
    standard_sequence_finite_numeral_mem_omega exponent
  have hResultOmega :=
    standard_sequence_finite_numeral_mem_omega (base ^ exponent)
  have hTraceMapping :
      ⊢ₘ[standard_sequence_semantics_theory]
        is_mapping_formula trace (Sₘ(numₘ(exponent))) ωₘ := by
    simpa [trace, traceTokens, stdtok_exponentiation_trace_tokens,
      finite_numeral_term] using (standard_token_sequence_is_mapping_omega traceTokens)
  have hInitial :
      ⊢ₘ[standard_sequence_semantics_theory] (trace ·ₘ ∅ₘ) ≐ₘ Sₘ(∅ₘ) := by
    simpa [trace, traceTokens, finite_numeral_term] using (standard_token_sequence_apply_getElem? traceTokens (stdtok_exponentiation_trace_tokens_getElem?
          base exponent 0 (Nat.zero_le exponent)))
  have hStepOpen :
      ⊢ₘ[standard_sequence_semantics_theory] (x#385 ∈ₘ numₘ(exponent)) ⟶ₘ ((trace ·ₘ Sₘ(x#385)) ≐ₘ ((trace ·ₘ x#385) *ₘ numₘ(base))) := by
    let point : SetTerm := x#385
    let conclusion : SetFormula := (trace ·ₘ Sₘ(point)) ≐ₘ ((trace ·ₘ point) *ₘ numₘ(base))
    have hPoint : Term.Admissible point SetSort.set :=
      set_variable_admissible 385
    have hCases :
        ⊢ₘ[standard_sequence_semantics_theory]
          stdseq_numeral_member_condition exponent point ⟶ₘ conclusion :=
      stdseq_numeral_member_condition_elim
        exponent point conclusion (fun index hIndex => by
          simpa [conclusion, point, trace] using
            stdtok_exponentiation_step_of_index_equality
              base exponent index point hPoint hIndex)
    have hNumeralIff :=
      stdseq_numeral_member_iff exponent point hPoint
    nd_apply FirstOrder.Derives.impIntro
    have hMembership :
        [point ∈ₘ numₘ(exponent)]
          ⊢ₘ[standard_sequence_semantics_theory]
            point ∈ₘ numₘ(exponent) :=
      FirstOrder.Derives.assumption (by simp)
    have hCondition := FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hNumeralIff)
      hMembership
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hCases)
      hCondition
  have hStep :
      ⊢ₘ[standard_sequence_semantics_theory]
        ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ numₘ(exponent)) ⟶ₘ ((trace ·ₘ Sₘ(bₛ#0)) ≐ₘ ((trace ·ₘ bₛ#0) *ₘ numₘ(base))) := by
    have hTheoryFresh :
        ∀ formula, standard_sequence_semantics_theory formula → (SetSort.set, 385) ∉ Formula.freeSupport formula := by
      intro formula hFormula
      rw [(standard_sequence_semantics_theory_sentence hFormula).2]
      intro hMember
      cases hMember
    have hTraceClose :
        Term.closeFreeAt SetSort.set 385 0 trace = trace :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 385 0 trace (standard_token_sequence_admissible traceTokens).2 (by
          rw [show Term.freeSupport trace = [] by
            exact standard_token_sequence_freeSupport_nil traceTokens]
          simp)
    have hExponentClose :
        Term.closeFreeAt SetSort.set 385 0 (numₘ(exponent)) =
          numₘ(exponent) :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 385 0 (numₘ(exponent)) (finite_numeral_term_admissible exponent).2 (by rw [finite_numeral_term_freeSupport]; simp)
    have hBaseClose :
        Term.closeFreeAt SetSort.set 385 0 (numₘ(base)) =
          numₘ(base) :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 385 0 (numₘ(base)) (finite_numeral_term_admissible base).2 (by rw [finite_numeral_term_freeSupport]; simp)
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := 385)
        hTheoryFresh (by simp) hStepOpen
    simpa [Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt, set_variable,
      hTraceClose, hExponentClose, hBaseClose] using hGeneralized
  have hTerminal :
      ⊢ₘ[standard_sequence_semantics_theory] (trace ·ₘ numₘ(exponent)) ≐ₘ result := by
    simpa [trace, traceTokens, result] using (standard_token_sequence_apply_getElem? traceTokens (stdtok_exponentiation_trace_tokens_getElem?
          base exponent exponent (Nat.le_refl exponent)))
  have hGraph :
      ⊢ₘ[standard_sequence_semantics_theory]
        natural_exponentiation_graph_condition (numₘ(base)) (numₘ(exponent)) result trace :=
    FirstOrder.Derives.conjIntro hTraceMapping <|
      FirstOrder.Derives.conjIntro hInitial <|
        FirstOrder.Derives.conjIntro hStep hTerminal
  have hDefinition :
      ⊢ₘ[standard_sequence_semantics_theory]
        natural_exponentiation_definition_instance (numₘ(base)) (numₘ(exponent)) result := by
    exact standard_sequence_weaken_natural_exponentiation <|
      natural_exponentiation_definition_instance_derives (numₘ(base)) (numₘ(exponent)) result (finite_numeral_term_admissible base)
        (finite_numeral_term_admissible exponent) (finite_numeral_term_admissible (base ^ exponent))
  have hBaseOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement (numₘ(base)) =
        numₘ(base) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (numₘ(base)) (finite_numeral_term_admissible base).2
  have hExponentOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement (numₘ(exponent)) =
        numₘ(exponent) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (numₘ(exponent)) (finite_numeral_term_admissible exponent).2
  have hResultOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement result = result :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement result (finite_numeral_term_admissible (base ^ exponent)).2
  have hSpec :
      ⊢ₘ[standard_sequence_semantics_theory]
    natural_exponentiation_spec (numₘ(base)) (numₘ(exponent)) result := by
    apply FirstOrder.Derives.conjIntro hResultOmega
    nd_apply FirstOrder.Derives.exists_intro (term := trace)
    simpa [natural_exponentiation_bound_graph_condition,
      natural_exponentiation_graph_condition,
      Formula.openAt, Formula.next_depth, Term.openAt,
      hBaseOpen, hExponentOpen, hResultOpen] using hGraph
  have hContract := FirstOrder.Derives.impElim hDefinition (FirstOrder.Derives.conjIntro hBaseOmega hExponentOmega)
  exact FirstOrder.Derives.iffElimLeft hContract hSpec
/-! ## 长度一符号编码 -/
private theorem stdtok_weaken_singleton {φ : SetFormula} (h : ⊢ₘ[singleton_operator_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  exact FirstOrder.Derives.theory_weaken (fun _ hf => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hf)))))))) h
private theorem stdtok_weaken_extensionality {φ : SetFormula} (h : ⊢ₘ[extensionality_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  have hFunction : ⊢ₘ[function_application_theory] φ :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        extensionality_theory_subset_function_application_theory hFormula)
      h
  exact FirstOrder.Derives.theory_weaken (fun _ hf => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hf)))))))))) hFunction
/--
单元素标准序列与语言编码层采用的长度一函数图相等。
这条桥接只使用标准序列的逐成员刻画、单点集规格与外延性；它不把二元并空集
在 Lean 层化简掉，因此保持对象集合论构造的真实性。
-/
theorem standard_singleton_sequence_eq_symbol_code (number : SetTerm) (hNumber : Term.Admissible number SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory]
      standard_sequence [number] ≐ₘ
        singleton_symbol_code_term number := by
  let sequence := standard_sequence [number]
  let symbolCode := singleton_symbol_code_term number
  let pointId :=
    FreshVariable.fresh_id SetSort.set
      [Formula.equal number number]
  let point : SetTerm := x#pointId
  let pair : SetTerm := ⟨numₘ(0), number⟩ₘ
  let agreementBody : SetFormula := (bₛ#0 ∈ₘ sequence) ↔ₘ (bₛ#0 ∈ₘ symbolCode)
  have hElements :
      ∀ element, element ∈ ([number] : List SetTerm) →
        Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_singleton.mp hElement with rfl
    exact hNumber
  have hSequence : Term.Admissible sequence SetSort.set := by
    simpa [sequence] using (seq_admissible_m 0 hElements)
  have hPair : Term.Admissible pair SetSort.set :=
    ordered_pair_term_admissible (numₘ(0)) number (finite_numeral_term_admissible 0) hNumber
  have hSymbolCode : Term.Admissible symbolCode SetSort.set :=
    singleton_symbol_code_term_admissible number hNumber
  have hSequencePointRaw := standard_sequence_from_member_iff
    0 point (elements := [number])
    hElements (by simpa [point] using set_variable_admissible pointId)
  have hSequencePoint :
      ⊢ₘ[standard_sequence_semantics_theory] (point ∈ₘ sequence) ↔ₘ ((point ≐ₘ pair) ∨ₘ Formula.falsum) := by
    simpa [sequence, point, pair,
      standard_sequence_member_condition] using hSequencePointRaw
  have hSingletonSpec :
      ⊢ₘ[standard_sequence_semantics_theory]
        singleton_spec pair symbolCode := by
    simpa [pair, symbolCode, singleton_symbol_code_term] using
      stdtok_weaken_singleton (singleton_term_spec_derives pair hPair)
  have hSymbolPoint :
      ⊢ₘ[standard_sequence_semantics_theory] (point ∈ₘ symbolCode) ↔ₘ (point ≐ₘ pair) :=
    singleton_spec_membership_iff
      pair symbolCode point hPair hSymbolCode (by simpa [point] using set_variable_admissible pointId)
      hSingletonSpec
  have hPointAgreement :
      ⊢ₘ[standard_sequence_semantics_theory] (point ∈ₘ sequence) ↔ₘ (point ∈ₘ symbolCode) := by
    derive_prop
  have hPointFresh : (SetSort.set, pointId) ∉ Term.freeSupport number := by
    dsimp [pointId]
    exact FreshVariable.fresh_term_not_mem_m
      SetSort.set number
  have hAgreementFresh : (SetSort.set, pointId) freshForₘ agreementBody := by
    simp [agreementBody, Formula.freeSupport,
      Term.freeSupport, Term.freeSupportList,
      sequence, symbolCode,
      standard_sequence_from,
      finite_numeral_term_freeSupport]
    intro hMember
    rcases List.mem_append.mp hMember with hMember | hMember
    · exact hPointFresh hMember
    · exact hPointFresh hMember
  have hPointOpened :
      ⊢ₘ[standard_sequence_semantics_theory]
        Formula.openAt SetSort.set 0 point agreementBody := by
    simpa [agreementBody, point, Formula.openAt, Term.openAt,
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 point sequence hSequence.2,
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 point symbolCode hSymbolCode.2] using
      hPointAgreement
  have hTheoryFresh :
      ∀ formula, standard_sequence_semantics_theory formula → (SetSort.set, pointId) freshForₘ formula := by
    intro formula hFormula
    have hSentence := standard_sequence_semantics_theory_sentence hFormula
    rw [hSentence.2]
    intro hMember
    cases hMember
  have hAgreement :
      ⊢ₘ[standard_sequence_semantics_theory]
        membership_agreement sequence symbolCode := by
    have hGeneralized := FirstOrder.Derives.forall_intro (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := pointId)
      (body := Formula.openAt SetSort.set 0 point agreementBody)
      hTheoryFresh (by simp) hPointOpened
    simpa [membership_agreement, agreementBody, point,
      Formula.closeFreeAt_openAt
        SetSort.set pointId 0 agreementBody hAgreementFresh] using
      hGeneralized
  have hExtensionality :
      ⊢ₘ[standard_sequence_semantics_theory]
        extensionality_instance sequence symbolCode :=
    stdtok_weaken_extensionality (extensionality_instance_derives_of_admissible
        sequence symbolCode hSequence hSymbolCode)
  exact FirstOrder.Derives.impElim hExtensionality hAgreement
/--
若一个 closed 对象项表示自然数，则以它为唯一值的长度一符号编码属于
`CodeStrₘ = seq_spaceₘ(ωₘ)`。
-/
theorem singleton_symbol_code_mem_code_string (number : SetTerm) (hNumber : Term.Admissible number SetSort.set) (hNumberClosed : Term.freeSupport number = [])
    (hNumberMem :
      ⊢ₘ[standard_sequence_semantics_theory] number ∈ₘ ωₘ) :
    ⊢ₘ[standard_sequence_semantics_theory]
      singleton_symbol_code_term number ∈ₘ CodeStrₘ := by
  have hElements :
      ∀ element, element ∈ ([number] : List SetTerm) →
        Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_singleton.mp hElement with rfl
    exact hNumber
  have hElementsClosed :
      ∀ element, element ∈ ([number] : List SetTerm) →
        Term.freeSupport element = [] := by
    intro element hElement
    rcases List.mem_singleton.mp hElement with rfl
    exact hNumberClosed
  have hElementsMem :
      ∀ element, element ∈ ([number] : List SetTerm) →
        ⊢ₘ[standard_sequence_semantics_theory] element ∈ₘ ωₘ := by
    intro element hElement
    rcases List.mem_singleton.mp hElement with rfl
    exact hNumberMem
  have hSequenceMem :
      ⊢ₘ[standard_sequence_semantics_theory]
        standard_sequence [number] ∈ₘ seq_spaceₘ(ωₘ) := by
    exact standard_sequence_mem_sequence_space
      ωₘ hElements hElementsClosed
      omega_term_admissible rfl
      standard_sequence_omega_ne_empty hElementsMem
  have hEquality := standard_singleton_sequence_eq_symbol_code
    number hNumber
  have hTransport := membership_left_iff_of_equality (standard_sequence [number]) (singleton_symbol_code_term number) (seq_spaceₘ(ωₘ))
    (seq_admissible_m 0 hElements) (singleton_symbol_code_term_admissible number hNumber) (finite_sequence_space_term_admissible
      ωₘ omega_term_admissible)
    hEquality
  exact FirstOrder.Derives.iffElimRight hTransport (by simpa [code_string_space_term] using hSequenceMem)
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
