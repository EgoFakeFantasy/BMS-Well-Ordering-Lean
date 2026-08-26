import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.CanonicalBinderShift.Sequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemSymbolWitnessBound
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSequenceRejection

/-!
# ZFC 中规范 binder 平移的有限算术反演

本模块只处理二元 binder-shift 关系的对象层函数性。内部自然数见证先由
素数幂编码的增长律压入源 token，再在有限标准自然数中枚举；所需前提只有
对象算术增长律与有限序列位置事实。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open GodelQuotation

set_option autoImplicit false

/-! ## token 数值项的等词运输 -/

/-- 自由变量名字 `2i` 的对象项。 -/
abbrev canonical_binder_free_name_term
    (i : SetTerm) : SetTerm :=
  numₘ(2) *ₘ i

/-- 绑定变量名字 `2d+1` 的对象项。 -/
abbrev canonical_binder_bound_name_term
    (d : SetTerm) : SetTerm :=
  Sₘ(numₘ(2) *ₘ d)

/-- 平移后的绑定变量名字 `2d+3` 的对象项。 -/
abbrev canonical_binder_shifted_bound_name_term
    (d : SetTerm) : SetTerm :=
  Sₘ(Sₘ(Sₘ(numₘ(2) *ₘ d)))

/-- 变量 token 数值项保持 admissibility。 -/
theorem canonical_binder_variable_token_term_admissible
    (name : SetTerm)
    (hName : Term.Admissible name SetSort.set) :
    Term.Admissible
      (variable_symbol_number_term name)
      SetSort.set :=
  variable_symbol_number_term_admissible name hName

/-- 常元 token 数值项保持 admissibility。 -/
theorem canonical_binder_constant_token_term_admissible
    (index : SetTerm)
    (hIndex : Term.Admissible index SetSort.set) :
    Term.Admissible
      (constant_symbol_number_term index)
      SetSort.set :=
  constant_symbol_number_term_admissible index hIndex

/-- 函数 token 数值项保持 admissibility。 -/
theorem canonical_binder_function_token_term_admissible
    (arity index : SetTerm)
    (hArity : Term.Admissible arity SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Term.Admissible
      (coded_function_symbol_number_term arity index)
      SetSort.set :=
  coded_function_symbol_number_term_admissible
    arity index hArity hIndex

/-- 谓词 token 数值项保持 admissibility。 -/
theorem canonical_binder_predicate_token_term_admissible
    (arity index : SetTerm)
    (hArity : Term.Admissible arity SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Term.Admissible
      (coded_predicate_symbol_number_term arity index)
      SetSort.set :=
  coded_predicate_symbol_number_term_admissible
    arity index hArity hIndex

/-- 已证明的名字等式可提升为变量 token 数值项等式。 -/
theorem canonical_binder_variable_token_term_congr_of_equality
    {T : SetTheory}
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEquality :
      Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      variable_symbol_number_term left ≐ₘ
        variable_symbol_number_term right := by
  exact Metatheory.Derives.unary_term_constructor_congr_of_equality
    variable_symbol_number_term
    canonical_binder_variable_token_term_admissible
    (by
      intro parameter replacement term
      simp [variable_symbol_number_term,
        indexed_prime_power_code_term,
        prime_power_code_term,
        natural_exponentiation_term,
        Term.substituteFree,
        GodelQuotation.gq_binder_shift_numeral_substitute])
    left right hLeft hRight hEquality

/-- 已证明的索引等式可提升为常元 token 数值项等式。 -/
theorem canonical_binder_constant_token_term_congr_of_equality
    {T : SetTheory}
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEquality :
      Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      constant_symbol_number_term left ≐ₘ
        constant_symbol_number_term right := by
  exact Metatheory.Derives.unary_term_constructor_congr_of_equality
    constant_symbol_number_term
    canonical_binder_constant_token_term_admissible
    (by
      intro parameter replacement term
      simp [constant_symbol_number_term,
        indexed_prime_power_code_term,
        prime_power_code_term,
        natural_exponentiation_term,
        Term.substituteFree,
        GodelQuotation.gq_binder_shift_numeral_substitute])
    left right hLeft hRight hEquality

/-- 两个参数等式可提升为函数 token 数值项等式。 -/
theorem canonical_binder_function_token_term_congr_of_equalities
    {T : SetTheory}
    {Γ : Context signature}
    (leftArity rightArity leftIndex rightIndex : SetTerm)
    (hLeftArity :
      Term.Admissible leftArity SetSort.set)
    (hRightArity :
      Term.Admissible rightArity SetSort.set)
    (hLeftIndex :
      Term.Admissible leftIndex SetSort.set)
    (hRightIndex :
      Term.Admissible rightIndex SetSort.set)
    (hArityEquality :
      Γ ⊢ₘ[T] leftArity ≐ₘ rightArity)
    (hIndexEquality :
      Γ ⊢ₘ[T] leftIndex ≐ₘ rightIndex) :
    Γ ⊢ₘ[T]
      coded_function_symbol_number_term
          leftArity leftIndex ≐ₘ
        coded_function_symbol_number_term
          rightArity rightIndex := by
  exact
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      coded_function_symbol_number_term
      canonical_binder_function_token_term_admissible
      (by
        intro parameter replacement arity index
        simp [coded_function_symbol_number_term,
          indexed_prime_power_code_term,
          prime_power_code_term,
          natural_exponentiation_term,
          Term.substituteFree,
          GodelQuotation.gq_binder_shift_numeral_substitute])
      leftArity rightArity leftIndex rightIndex
      hLeftArity hRightArity hLeftIndex hRightIndex
      hArityEquality hIndexEquality

/-- 两个参数等式可提升为谓词 token 数值项等式。 -/
theorem canonical_binder_predicate_token_term_congr_of_equalities
    {T : SetTheory}
    {Γ : Context signature}
    (leftArity rightArity leftIndex rightIndex : SetTerm)
    (hLeftArity :
      Term.Admissible leftArity SetSort.set)
    (hRightArity :
      Term.Admissible rightArity SetSort.set)
    (hLeftIndex :
      Term.Admissible leftIndex SetSort.set)
    (hRightIndex :
      Term.Admissible rightIndex SetSort.set)
    (hArityEquality :
      Γ ⊢ₘ[T] leftArity ≐ₘ rightArity)
    (hIndexEquality :
      Γ ⊢ₘ[T] leftIndex ≐ₘ rightIndex) :
    Γ ⊢ₘ[T]
      coded_predicate_symbol_number_term
          leftArity leftIndex ≐ₘ
        coded_predicate_symbol_number_term
          rightArity rightIndex := by
  exact
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      coded_predicate_symbol_number_term
      canonical_binder_predicate_token_term_admissible
      (by
        intro parameter replacement arity index
        simp [coded_predicate_symbol_number_term,
          indexed_prime_power_code_term,
          prime_power_code_term,
          natural_exponentiation_term,
          Term.substituteFree,
          GodelQuotation.gq_binder_shift_numeral_substitute])
      leftArity rightArity leftIndex rightIndex
      hLeftArity hRightArity hLeftIndex hRightIndex
      hArityEquality hIndexEquality

/-- 等式可穿过左乘常数 `2`。 -/
theorem canonical_binder_double_term_congr_of_equality
    {T : SetTheory}
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEquality :
      Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      canonical_binder_free_name_term left ≐ₘ
        canonical_binder_free_name_term right := by
  exact
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      (fun two index => two *ₘ index)
      natural_multiplication_term_admissible
      (by
        intro parameter replacement two index
        simp [Term.substituteFree])
      (numₘ(2)) (numₘ(2)) left right
      (finite_numeral_term_admissible 2)
      (finite_numeral_term_admissible 2)
      hLeft hRight
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(2)))
      hEquality

/-- 深度等式可穿过原始绑定名字 `2d+1`。 -/
theorem canonical_binder_bound_name_term_congr_of_equality
    {T : SetTheory}
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEquality :
      Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      canonical_binder_bound_name_term left ≐ₘ
        canonical_binder_bound_name_term right := by
  have hDouble :=
    canonical_binder_double_term_congr_of_equality
      left right hLeft hRight hEquality
  exact successor_term_congr_of_equality
    (canonical_binder_free_name_term left)
    (canonical_binder_free_name_term right)
    (natural_multiplication_term_admissible _ _
      (finite_numeral_term_admissible 2) hLeft)
    (natural_multiplication_term_admissible _ _
      (finite_numeral_term_admissible 2) hRight)
    hDouble

/-- 深度等式可穿过平移后的绑定名字 `2d+3`。 -/
theorem canonical_binder_shifted_bound_name_term_congr_of_equality
    {T : SetTheory}
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEquality :
      Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      canonical_binder_shifted_bound_name_term left ≐ₘ
        canonical_binder_shifted_bound_name_term right := by
  have hOne :=
    canonical_binder_bound_name_term_congr_of_equality
      left right hLeft hRight hEquality
  have hLeftDouble :
      Term.Admissible
        (canonical_binder_free_name_term left)
        SetSort.set :=
    natural_multiplication_term_admissible _ _
      (finite_numeral_term_admissible 2) hLeft
  have hRightDouble :
      Term.Admissible
        (canonical_binder_free_name_term right)
        SetSort.set :=
    natural_multiplication_term_admissible _ _
      (finite_numeral_term_admissible 2) hRight
  have hTwo :=
    successor_term_congr_of_equality
      (canonical_binder_bound_name_term left)
      (canonical_binder_bound_name_term right)
      (successor_term_admissible _ hLeftDouble)
      (successor_term_admissible _ hRightDouble)
      hOne
  exact successor_term_congr_of_equality
    (Sₘ(canonical_binder_bound_name_term left))
    (Sₘ(canonical_binder_bound_name_term right))
    (successor_term_admissible _
      (successor_term_admissible _ hLeftDouble))
    (successor_term_admissible _
      (successor_term_admissible _ hRightDouble))
    hTwo

/-! ## 有限界运输 -/

/--
若源值同时等于标准 numeral 与一个编码项，则编码项中的任意对象成员可运输回
该标准 numeral。此接口把素数幂增长律与有限 numeral 消去解耦。
-/
theorem fs_zfc_support_raw_member_numeral_of_source_encoding
    {Γ : Context signature}
    {sourceToken : Nat}
    (point sourceValue encodedValue : SetTerm)
    (hPoint : Term.Admissible point SetSort.set)
    (hEncodedValue :
      Term.Admissible encodedValue SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hEncodingEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ encodedValue)
    (hMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        point ∈ₘ encodedValue) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      point ∈ₘ numₘ(sourceToken) := by
  have hNumeralEncoding :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(sourceToken) ≐ₘ encodedValue :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hSourceEquality)
      hEncodingEquality
  exact FirstOrder.Derives.iffElimLeft
    (membership_right_iff_of_equality
      point (numₘ(sourceToken)) encodedValue
      hPoint
      (finite_numeral_term_admissible sourceToken)
      hEncodedValue hNumeralEncoding)
    hMember

/--
单素数幂编码中的对象索引落在已知标准源 token 给出的有限 numeral 内。
-/
theorem fs_zfc_support_raw_index_mem_source_of_prime_power
    {Γ : Context signature}
    {sourceToken : Nat}
    (base : Nat)
    (sourceValue index : SetTerm)
    (hBase : 1 < base)
    (hIndex :
      Term.Admissible index SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hIndexOmega :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        index ∈ₘ ωₘ)
    (hEncodingEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ
          indexed_prime_power_code_term base index) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      index ∈ₘ numₘ(sourceToken) := by
  have hMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        index ∈ₘ
          indexed_prime_power_code_term base index :=
    GodelQuotation.gq_index_mem_indexed_prime_power_of_theory
      (T := fs_zfc_support_raw_theory)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      base index hBase hIndex hIndexOmega
  exact fs_zfc_support_raw_member_numeral_of_source_encoding
    index sourceValue
    (indexed_prime_power_code_term base index)
    hIndex
    (indexed_prime_power_code_term_admissible
      base index hIndex)
    hSourceEquality hEncodingEquality hMember

/--
双素数幂乘积编码中的两个对象索引都落在已知标准源 token 的有限 numeral 内。
-/
theorem fs_zfc_support_raw_indices_mem_source_of_prime_power_product
    {Γ : Context signature}
    {sourceToken : Nat}
    (leftBase rightBase : Nat)
    (sourceValue leftIndex rightIndex : SetTerm)
    (hLeftBase : 1 < leftBase)
    (hRightBase : 1 < rightBase)
    (hLeftIndex :
      Term.Admissible leftIndex SetSort.set)
    (hRightIndex :
      Term.Admissible rightIndex SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hLeftOmega :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        leftIndex ∈ₘ ωₘ)
    (hRightOmega :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        rightIndex ∈ₘ ωₘ)
    (hEncodingEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ
          ((indexed_prime_power_code_term
              leftBase leftIndex) *ₘ
            (indexed_prime_power_code_term
              rightBase rightIndex))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      ((leftIndex ∈ₘ numₘ(sourceToken)) ∧ₘ
        (rightIndex ∈ₘ numₘ(sourceToken))) := by
  have hMembers :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ((leftIndex ∈ₘ
            ((indexed_prime_power_code_term
                leftBase leftIndex) *ₘ
              (indexed_prime_power_code_term
                rightBase rightIndex))) ∧ₘ
          (rightIndex ∈ₘ
            ((indexed_prime_power_code_term
                leftBase leftIndex) *ₘ
              (indexed_prime_power_code_term
                rightBase rightIndex)))) :=
    GodelQuotation.gq_indices_mem_indexed_prime_power_product_of_theory
      (T := fs_zfc_support_raw_theory)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      leftBase rightBase leftIndex rightIndex
      hLeftBase hRightBase hLeftIndex hRightIndex
      hLeftOmega hRightOmega
  have hEncoded :
      Term.Admissible
        ((indexed_prime_power_code_term
            leftBase leftIndex) *ₘ
          (indexed_prime_power_code_term
            rightBase rightIndex))
        SetSort.set :=
    natural_multiplication_term_admissible _ _
      (indexed_prime_power_code_term_admissible
        leftBase leftIndex hLeftIndex)
      (indexed_prime_power_code_term_admissible
        rightBase rightIndex hRightIndex)
  exact FirstOrder.Derives.conjIntro
    (fs_zfc_support_raw_member_numeral_of_source_encoding
      leftIndex sourceValue _ hLeftIndex hEncoded
      hSourceEquality hEncodingEquality
      (FirstOrder.Derives.conjElimLeft hMembers))
    (fs_zfc_support_raw_member_numeral_of_source_encoding
      rightIndex sourceValue _ hRightIndex hEncoded
      hSourceEquality hEncodingEquality
      (FirstOrder.Derives.conjElimRight hMembers))

/-- 一个标准变量 token 的对象数值展开。 -/
theorem canonical_binder_variable_token_value
    (name : Nat) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      numₘ(GodelQuotation.Numbered.variable_token name) ≐ₘ
        variable_symbol_number_term (numₘ(name)) := by
  simpa [GodelQuotation.Numbered.variable_token,
    variable_symbol_number_term] using
    GodelQuotation.gq_binder_shift_indexed_prime_power_value
      3 name (numₘ(name))
      (finite_numeral_term_admissible name)
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(name)))

/-- 一个标准自由变量 token 的对象数值展开。 -/
theorem canonical_binder_free_token_value
    (id : Nat) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      numₘ(GodelQuotation.Numbered.variable_token
          (GodelQuotation.free_name id)) ≐ₘ
        variable_symbol_number_term
          (canonical_binder_free_name_term
            (numₘ(id))) := by
  have hProduct :
      Term.Admissible
        (canonical_binder_free_name_term (numₘ(id)))
        SetSort.set :=
    natural_multiplication_term_admissible _ _
      (finite_numeral_term_admissible 2)
      (finite_numeral_term_admissible id)
  have hName :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(GodelQuotation.free_name id) ≐ₘ
          canonical_binder_free_name_term
            (numₘ(id)) := by
    simpa [canonical_binder_free_name_term,
      GodelQuotation.free_name] using
      (GodelQuotation.gq_weaken_standard_sequence <|
        GodelQuotation.standard_token_sequence_finite_numeral_multiplication
          2 id)
  simpa [GodelQuotation.Numbered.variable_token,
    variable_symbol_number_term] using
    GodelQuotation.gq_binder_shift_indexed_prime_power_value
      3 (GodelQuotation.free_name id)
      (canonical_binder_free_name_term (numₘ(id)))
      hProduct hName

/-- 一个标准绑定变量 token 的对象数值展开。 -/
theorem canonical_binder_bound_token_value
    (depth : Nat) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      numₘ(GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name depth)) ≐ₘ
        variable_symbol_number_term
          (canonical_binder_bound_name_term
            (numₘ(depth))) := by
  let product :=
    canonical_binder_free_name_term (numₘ(depth))
  have hProduct :
      Term.Admissible product SetSort.set :=
    natural_multiplication_term_admissible _ _
      (finite_numeral_term_admissible 2)
      (finite_numeral_term_admissible depth)
  have hProductValue :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(2 * depth) ≐ₘ product := by
    simpa [product,
      canonical_binder_free_name_term] using
      (GodelQuotation.gq_weaken_standard_sequence <|
        GodelQuotation.standard_token_sequence_finite_numeral_multiplication
          2 depth)
  have hNameRaw :=
    successor_term_congr_of_equality
      (numₘ(2 * depth)) product
      (finite_numeral_term_admissible (2 * depth))
      hProduct hProductValue
  have hName :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(GodelQuotation.bound_name depth) ≐ₘ
          canonical_binder_bound_name_term
            (numₘ(depth)) := by
    simpa [GodelQuotation.bound_name,
      canonical_binder_bound_name_term,
      finite_numeral_term, product] using hNameRaw
  simpa [GodelQuotation.Numbered.variable_token,
    variable_symbol_number_term] using
    GodelQuotation.gq_binder_shift_indexed_prime_power_value
      3 (GodelQuotation.bound_name depth)
      (canonical_binder_bound_name_term
        (numₘ(depth)))
      (successor_term_admissible _ hProduct)
      hName

/-- 平移后的标准绑定变量 token 的对象数值展开。 -/
theorem canonical_binder_shifted_bound_token_value
    (depth : Nat) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      numₘ(GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name (depth + 1))) ≐ₘ
        variable_symbol_number_term
          (canonical_binder_shifted_bound_name_term
            (numₘ(depth))) := by
  let product :=
    canonical_binder_free_name_term (numₘ(depth))
  have hProduct :
      Term.Admissible product SetSort.set :=
    natural_multiplication_term_admissible _ _
      (finite_numeral_term_admissible 2)
      (finite_numeral_term_admissible depth)
  have hProductValue :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(2 * depth) ≐ₘ product := by
    simpa [product,
      canonical_binder_free_name_term] using
      (GodelQuotation.gq_weaken_standard_sequence <|
        GodelQuotation.standard_token_sequence_finite_numeral_multiplication
          2 depth)
  have hOne :=
    successor_term_congr_of_equality
      (numₘ(2 * depth)) product
      (finite_numeral_term_admissible (2 * depth))
      hProduct hProductValue
  have hTwo :=
    successor_term_congr_of_equality
      (Sₘ(numₘ(2 * depth))) (Sₘ(product))
      (successor_term_admissible _
        (finite_numeral_term_admissible (2 * depth)))
      (successor_term_admissible _ hProduct)
      hOne
  have hThree :=
    successor_term_congr_of_equality
      (Sₘ(Sₘ(numₘ(2 * depth))))
      (Sₘ(Sₘ(product)))
      (successor_term_admissible _
        (successor_term_admissible _
          (finite_numeral_term_admissible (2 * depth))))
      (successor_term_admissible _
        (successor_term_admissible _ hProduct))
      hTwo
  have hName :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(GodelQuotation.bound_name (depth + 1)) ≐ₘ
          canonical_binder_shifted_bound_name_term
            (numₘ(depth)) := by
    simpa [GodelQuotation.bound_name,
      canonical_binder_shifted_bound_name_term,
      finite_numeral_term, product] using hThree
  simpa [GodelQuotation.Numbered.variable_token,
    variable_symbol_number_term] using
    GodelQuotation.gq_binder_shift_indexed_prime_power_value
      3 (GodelQuotation.bound_name (depth + 1))
      (canonical_binder_shifted_bound_name_term
        (numₘ(depth)))
      (successor_term_admissible _
        (successor_term_admissible _
          (successor_term_admissible _ hProduct)))
      hName

/-- 一个标准常元 token 的对象数值展开。 -/
theorem canonical_binder_constant_token_value
    (index : Nat) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      numₘ(GodelQuotation.Numbered.constant_token index) ≐ₘ
        constant_symbol_number_term (numₘ(index)) := by
  simpa [GodelQuotation.Numbered.constant_token,
    constant_symbol_number_term] using
    GodelQuotation.gq_binder_shift_indexed_prime_power_value
      5 index (numₘ(index))
      (finite_numeral_term_admissible index)
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(index)))

/-- 一个标准函数 token 的对象数值展开。 -/
theorem canonical_binder_function_token_value
    (arity index : Nat) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      numₘ(GodelQuotation.Numbered.function_token
          arity index) ≐ₘ
        coded_function_symbol_number_term
          (numₘ(arity)) (numₘ(index)) := by
  simpa [GodelQuotation.Numbered.function_token,
    coded_function_symbol_number_term] using
    GodelQuotation.gq_binder_shift_binary_symbol_value
      5 arity index

/-- 一个标准谓词 token 的对象数值展开。 -/
theorem canonical_binder_predicate_token_value
    (arity index : Nat) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      numₘ(GodelQuotation.Numbered.predicate_token
          arity index) ≐ₘ
        coded_predicate_symbol_number_term
          (numₘ(arity)) (numₘ(index)) := by
  simpa [GodelQuotation.Numbered.predicate_token,
    coded_predicate_symbol_number_term] using
    GodelQuotation.gq_binder_shift_binary_symbol_value
      7 arity index

/-! ## 标准见证分支的 numeral 冲突 -/

/-- 已知源 token 与某个标准编码 token 不同，则对应对象编码等式导出矛盾。 -/
theorem fs_zfc_support_raw_falsum_of_binder_symbol_value
    {Γ : Context signature}
    (sourceToken encodedToken : Nat)
    (sourceValue encodedValue : SetTerm)
    (hNe : sourceToken ≠ encodedToken)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hEncodingEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ encodedValue)
    (hEncodedValue :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(encodedToken) ≐ₘ encodedValue) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hEncodedAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(encodedToken) ≐ₘ encodedValue :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation
          hEncodedValue
  have hNumeralEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(sourceToken) ≐ₘ numₘ(encodedToken) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hSourceEquality) <|
        Metatheory.Derives.equality_trans
          hEncodingEquality
          (Metatheory.Derives.equality_symm hEncodedAt)
  exact fs_zfc_support_raw_falsum_of_numeral_equality
    hNe hNumeralEquality

/-- 自由变量见证固定为 `index` 后，错误的标准源 token 导出矛盾。 -/
theorem fs_zfc_support_raw_free_source_token_falsum
    {Γ : Context signature}
    (sourceToken index : Nat)
    (sourceValue witness : SetTerm)
    (hNe :
      sourceToken ≠
        GodelQuotation.Numbered.variable_token
          (GodelQuotation.free_name index))
    (hWitness :
      Term.Admissible witness SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hEncodingEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ
          variable_symbol_number_term
            (canonical_binder_free_name_term witness))
    (hWitnessEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        witness ≐ₘ numₘ(index)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hNameEquality :=
    canonical_binder_double_term_congr_of_equality
      witness (numₘ(index))
      hWitness
      (finite_numeral_term_admissible index)
      hWitnessEquality
  have hTermEquality :=
    canonical_binder_variable_token_term_congr_of_equality
      (canonical_binder_free_name_term witness)
      (canonical_binder_free_name_term (numₘ(index)))
      (natural_multiplication_term_admissible _ _
        (finite_numeral_term_admissible 2) hWitness)
      (natural_multiplication_term_admissible _ _
        (finite_numeral_term_admissible 2)
        (finite_numeral_term_admissible index))
      hNameEquality
  apply fs_zfc_support_raw_falsum_of_binder_symbol_value
    sourceToken
    (GodelQuotation.Numbered.variable_token
      (GodelQuotation.free_name index))
    sourceValue
    (variable_symbol_number_term
      (canonical_binder_free_name_term (numₘ(index))))
    hNe hSourceEquality
  · exact Metatheory.Derives.equality_trans
      hEncodingEquality hTermEquality
  · exact canonical_binder_free_token_value index

/-- 绑定变量见证固定为 `index` 后，错误的标准源 token 导出矛盾。 -/
theorem fs_zfc_support_raw_bound_source_token_falsum
    {Γ : Context signature}
    (sourceToken index : Nat)
    (sourceValue witness : SetTerm)
    (hNe :
      sourceToken ≠
        GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name index))
    (hWitness :
      Term.Admissible witness SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hEncodingEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ
          variable_symbol_number_term
            (canonical_binder_bound_name_term witness))
    (hWitnessEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        witness ≐ₘ numₘ(index)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hNameEquality :=
    canonical_binder_bound_name_term_congr_of_equality
      witness (numₘ(index))
      hWitness
      (finite_numeral_term_admissible index)
      hWitnessEquality
  have hTermEquality :=
    canonical_binder_variable_token_term_congr_of_equality
      (canonical_binder_bound_name_term witness)
      (canonical_binder_bound_name_term (numₘ(index)))
      (successor_term_admissible _
        (natural_multiplication_term_admissible _ _
          (finite_numeral_term_admissible 2) hWitness))
      (successor_term_admissible _
        (natural_multiplication_term_admissible _ _
          (finite_numeral_term_admissible 2)
          (finite_numeral_term_admissible index)))
      hNameEquality
  apply fs_zfc_support_raw_falsum_of_binder_symbol_value
    sourceToken
    (GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name index))
    sourceValue
    (variable_symbol_number_term
      (canonical_binder_bound_name_term (numₘ(index))))
    hNe hSourceEquality
  · exact Metatheory.Derives.equality_trans
      hEncodingEquality hTermEquality
  · exact canonical_binder_bound_token_value index

/-- 常元见证固定为 `index` 后，错误的标准源 token 导出矛盾。 -/
theorem fs_zfc_support_raw_constant_source_token_falsum
    {Γ : Context signature}
    (sourceToken index : Nat)
    (sourceValue witness : SetTerm)
    (hNe :
      sourceToken ≠
        GodelQuotation.Numbered.constant_token index)
    (hWitness :
      Term.Admissible witness SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hEncodingEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ
          constant_symbol_number_term witness)
    (hWitnessEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        witness ≐ₘ numₘ(index)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hTermEquality :=
    canonical_binder_constant_token_term_congr_of_equality
      witness (numₘ(index))
      hWitness
      (finite_numeral_term_admissible index)
      hWitnessEquality
  apply fs_zfc_support_raw_falsum_of_binder_symbol_value
    sourceToken
    (GodelQuotation.Numbered.constant_token index)
    sourceValue
    (constant_symbol_number_term (numₘ(index)))
    hNe hSourceEquality
  · exact Metatheory.Derives.equality_trans
      hEncodingEquality hTermEquality
  · exact canonical_binder_constant_token_value index

/-- 函数见证固定后，错误的标准源 token 导出矛盾。 -/
theorem fs_zfc_support_raw_function_source_token_falsum
    {Γ : Context signature}
    (sourceToken arity index : Nat)
    (sourceValue arityWitness indexWitness : SetTerm)
    (hNe :
      sourceToken ≠
        GodelQuotation.Numbered.function_token arity index)
    (hArityWitness :
      Term.Admissible arityWitness SetSort.set)
    (hIndexWitness :
      Term.Admissible indexWitness SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hEncodingEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ
          coded_function_symbol_number_term
            arityWitness indexWitness)
    (hArityEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        arityWitness ≐ₘ numₘ(arity))
    (hIndexEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        indexWitness ≐ₘ numₘ(index)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hTermEquality :=
    canonical_binder_function_token_term_congr_of_equalities
      arityWitness (numₘ(arity))
      indexWitness (numₘ(index))
      hArityWitness
      (finite_numeral_term_admissible arity)
      hIndexWitness
      (finite_numeral_term_admissible index)
      hArityEquality hIndexEquality
  apply fs_zfc_support_raw_falsum_of_binder_symbol_value
    sourceToken
    (GodelQuotation.Numbered.function_token arity index)
    sourceValue
    (coded_function_symbol_number_term
      (numₘ(arity)) (numₘ(index)))
    hNe hSourceEquality
  · exact Metatheory.Derives.equality_trans
      hEncodingEquality hTermEquality
  · exact canonical_binder_function_token_value arity index

/-- 谓词见证固定后，错误的标准源 token 导出矛盾。 -/
theorem fs_zfc_support_raw_predicate_source_token_falsum
    {Γ : Context signature}
    (sourceToken arity index : Nat)
    (sourceValue arityWitness indexWitness : SetTerm)
    (hNe :
      sourceToken ≠
        GodelQuotation.Numbered.predicate_token arity index)
    (hArityWitness :
      Term.Admissible arityWitness SetSort.set)
    (hIndexWitness :
      Term.Admissible indexWitness SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hEncodingEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ
          coded_predicate_symbol_number_term
            arityWitness indexWitness)
    (hArityEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        arityWitness ≐ₘ numₘ(arity))
    (hIndexEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        indexWitness ≐ₘ numₘ(index)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hTermEquality :=
    canonical_binder_predicate_token_term_congr_of_equalities
      arityWitness (numₘ(arity))
      indexWitness (numₘ(index))
      hArityWitness
      (finite_numeral_term_admissible arity)
      hIndexWitness
      (finite_numeral_term_admissible index)
      hArityEquality hIndexEquality
  apply fs_zfc_support_raw_falsum_of_binder_symbol_value
    sourceToken
    (GodelQuotation.Numbered.predicate_token arity index)
    sourceValue
    (coded_predicate_symbol_number_term
      (numₘ(arity)) (numₘ(index)))
    hNe hSourceEquality
  · exact Metatheory.Derives.equality_trans
      hEncodingEquality hTermEquality
  · exact canonical_binder_predicate_token_value arity index

/-- 绑定深度见证固定后，平移目标 token 唯一。 -/
theorem fs_zfc_support_raw_bound_target_token_eq
    {Γ : Context signature}
    (depth : Nat)
    (targetValue witness : SetTerm)
    (hWitness :
      Term.Admissible witness SetSort.set)
    (hTargetEncoding :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ
          variable_symbol_number_term
            (canonical_binder_shifted_bound_name_term witness))
    (hWitnessEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        witness ≐ₘ numₘ(depth)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ
        numₘ(GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name (depth + 1))) := by
  have hNameEquality :=
    canonical_binder_shifted_bound_name_term_congr_of_equality
      witness (numₘ(depth))
      hWitness
      (finite_numeral_term_admissible depth)
      hWitnessEquality
  have hTermEquality :=
    canonical_binder_variable_token_term_congr_of_equality
      (canonical_binder_shifted_bound_name_term witness)
      (canonical_binder_shifted_bound_name_term
        (numₘ(depth)))
      (successor_term_admissible _
        (successor_term_admissible _
          (successor_term_admissible _
            (natural_multiplication_term_admissible _ _
              (finite_numeral_term_admissible 2)
              hWitness))))
      (successor_term_admissible _
        (successor_term_admissible _
          (successor_term_admissible _
            (natural_multiplication_term_admissible _ _
              (finite_numeral_term_admissible 2)
              (finite_numeral_term_admissible depth)))))
      hNameEquality
  have hValue :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name (depth + 1))) ≐ₘ
          variable_symbol_number_term
            (canonical_binder_shifted_bound_name_term
              (numₘ(depth))) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation
          (canonical_binder_shifted_bound_token_value depth)
  exact Metatheory.Derives.equality_trans
    hTargetEncoding <|
      Metatheory.Derives.equality_trans hTermEquality
        (Metatheory.Derives.equality_symm hValue)

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
