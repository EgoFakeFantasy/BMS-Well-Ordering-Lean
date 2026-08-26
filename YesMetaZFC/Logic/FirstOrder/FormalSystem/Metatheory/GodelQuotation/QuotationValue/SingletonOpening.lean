import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.Sequence

/-!
# Gödel quotation 的动态 singleton 开头

本模块给出任意对象自然数项形成的 singleton 符号码的有限性、定义域与零位值。
该事实只属于公共 quotation 序列层，供函数符号、谓词符号及后续有限 parser
反演共同使用。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/--
任意动态自然数项形成的 singleton 符号码都是长度一有限函数，并在零位取该项。
三个新鲜编号只来自标准序列函数性证明的内部坐标 binder，不是对象理论前提。
-/
theorem gq_singleton_symbol_code_opening
    {Γ : Context signature}
    (number : SetTerm)
    (hNumber : Term.Admissible number SetSort.set)
    (hFresh :
      ReservedIdsFresh [0, 1, 2] [number]) :
    Γ ⊢ₘ[godel_quotation_theory]
      (finite_sequence_condition
          (singleton_symbol_code_term number) ∧ₘ
        ((domₘ(singleton_symbol_code_term number) ≐ₘ
            numₘ(1)) ∧ₘ
          ((numₘ(0) ∈ₘ
              domₘ(singleton_symbol_code_term number)) ∧ₘ
            ((singleton_symbol_code_term number ·ₘ
                numₘ(0)) ≐ₘ number)))) := by
  let standard : SetTerm :=
    standard_sequence [number]
  let symbolCode : SetTerm :=
    singleton_symbol_code_term number
  have hElements :
      ∀ element, element ∈ ([number] : List SetTerm) →
        Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_singleton.mp hElement with rfl
    exact hNumber
  have hElementsFresh (id : FreeVarId)
      (hId : id ∈ [0, 1, 2]) :
      ∀ element, element ∈ ([number] : List SetTerm) →
        (SetSort.set, id) ∉
          Term.freeSupport element := by
    intro item hItem
    rcases List.mem_singleton.mp hItem with rfl
    exact hFresh _ (by simp) id hId
  have hStandard :
      Term.Admissible standard SetSort.set := by
    simpa [standard] using
      seq_admissible_m 0 hElements
  have hSymbolCode :
      Term.Admissible symbolCode SetSort.set := by
    simpa [symbolCode] using
      singleton_symbol_code_term_admissible
        number hNumber
  have hStandardFunction :
      Γ ⊢ₘ[godel_quotation_theory]
        is_function_formula standard :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <| by
          simpa [standard] using
            standard_sequence_from_is_function
              0 hElements
              (hElementsFresh 0 (by simp))
              (hElementsFresh 1 (by simp))
              (hElementsFresh 2 (by simp))
  have hStandardFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition standard :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <| by
          simpa [standard] using
            standard_sequence_finite_sequence_condition
              hElements
              (hElementsFresh 0 (by simp))
              (hElementsFresh 1 (by simp))
              (hElementsFresh 2 (by simp))
  have hStandardDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(standard) ≐ₘ numₘ(1) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <| by
          simpa [standard] using
            standard_sequence_domain_eq_numeral_length
              hElements
              (hElementsFresh 0 (by simp))
              (hElementsFresh 1 (by simp))
  have hGraph :
      Γ ⊢ₘ[godel_quotation_theory]
        ⟨numₘ(0), number⟩ₘ ∈ₘ standard :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <| by
          simpa [standard] using
            standard_sequence_from_getElem?_graph_mem
              0 (elements := [number])
              (index := 0) (element := number)
              (by simp) hElements hNumber
  have hStandardRelation :
      Γ ⊢ₘ[godel_quotation_theory]
        is_relation_formula standard :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <|
            stdseq_weaken_function_predicate <|
              is_function_implies_is_relation
                standard hStandard)
      hStandardFunction
  have hZeroDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(0) ∈ₘ domₘ(standard) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            gq_weaken_standard_sequence <|
              stdseq_weaken_function_predicate <|
                relation_member_left_coordinate_mem_domain
                  standard (numₘ(0)) number
                  hStandard
                  (finite_numeral_term_admissible 0)
                  hNumber)
        hStandardRelation)
      hGraph
  have hValueBack :
      Γ ⊢ₘ[godel_quotation_theory]
        number ≐ₘ (standard ·ₘ numₘ(0)) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            gq_weaken_standard_sequence <|
              stdseq_weaken_function_application <|
                function_application_eq_of_graph
                  standard (numₘ(0)) number
                  hStandard
                  (finite_numeral_term_admissible 0)
                  hNumber)
        (FirstOrder.Derives.conjIntro
          hStandardFunction hZeroDomain))
      hGraph
  have hStandardPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(standard)) ∧ₘ
          ((standard ·ₘ numₘ(0)) ≐ₘ number)) :=
    FirstOrder.Derives.conjIntro
      hZeroDomain
      (Metatheory.Derives.equality_symm hValueBack)
  have hStandardToSymbol :
      Γ ⊢ₘ[godel_quotation_theory]
        standard ≐ₘ symbolCode :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [standard, symbolCode] using
          gq_weaken_standard_sequence
            (standard_singleton_sequence_eq_symbol_code
              number hNumber)
  have hSymbolToStandard :
      Γ ⊢ₘ[godel_quotation_theory]
        symbolCode ≐ₘ standard :=
    Metatheory.Derives.equality_symm
      hStandardToSymbol
  have hSymbolFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition symbolCode :=
    FirstOrder.Derives.iffElimLeft
      (finite_sequence_condition_iff_of_equality
        symbolCode standard hSymbolCode hStandard
        hSymbolToStandard)
      hStandardFinite
  have hSymbolDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(symbolCode) ≐ₘ numₘ(1) :=
    Metatheory.Derives.equality_trans
      (domain_term_congr_of_equality
        symbolCode standard hSymbolCode hStandard
        hSymbolToStandard)
      hStandardDomain
  have hSymbolPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(symbolCode)) ∧ₘ
          ((symbolCode ·ₘ numₘ(0)) ≐ₘ number)) :=
    gq_point_inversion_of_equality
      symbolCode standard (numₘ(0)) number
      hSymbolToStandard hStandardPoint
  simpa [symbolCode] using
    FirstOrder.Derives.conjIntro
      hSymbolFinite <|
        FirstOrder.Derives.conjIntro
          hSymbolDomain hSymbolPoint

/--
任意对象自然数项形成的长度一符号码都是代码字符串。

结论写成对象蕴含，因此调用方无需提供上下文新鲜性；内部临时上下文只有
`number ∈ ωₘ`，其对 `0/1` 的新鲜性由精确的保留编号条件直接给出。
-/
theorem gq_singleton_symbol_code_mem_code_string_of_omega
    (number : SetTerm)
    (hNumber : Term.Admissible number SetSort.set)
    (hFresh :
      ReservedIdsFresh [0, 1, 2] [number]) :
    ⊢ₘ[godel_quotation_theory]
      (number ∈ₘ ωₘ) ⟶ₘ
        (singleton_symbol_code_term number ∈ₘ CodeStrₘ) := by
  let membership : SetFormula := number ∈ₘ ωₘ
  let Γ : Context signature := [membership]
  have hMembership :
      Formula.Admissible membership := by
    simpa [membership] using
      membership_formula_admissible
        hNumber omega_term_admissible
  nd_apply FirstOrder.Derives.impIntro
  have hNumberMem :
      Γ ⊢ₘ[godel_quotation_theory]
        number ∈ₘ ωₘ := by
    simpa [membership] using
      (FirstOrder.Derives.assumption
        (T := godel_quotation_theory)
        (Γ := Γ) (φ := membership)
        (by simp [Γ]))
  have hElements :
      ∀ element, element ∈ ([number] : List SetTerm) →
        Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_singleton.mp hElement with rfl
    exact hNumber
  have hElementsFresh
      (id : FreeVarId)
      (hId : id ∈ [0, 1, 2]) :
      ∀ element, element ∈ ([number] : List SetTerm) →
        (SetSort.set, id) ∉
          Term.freeSupport element := by
    intro element hElement
    exact hFresh element hElement id hId
  have hOmegaFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport ωₘ := by
    change (SetSort.set, id) ∉
      ([] : List (SetSort × FreeVarId))
    exact List.not_mem_nil
  have hContextFresh
      (id : FreeVarId)
      (hId : id ∈ [0, 1]) :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, id) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    have hNumberFresh :
        (SetSort.set, id) ∉
          Term.freeSupport number :=
      hFresh number (by simp) id
        (by
          simp only [List.mem_cons,
            List.not_mem_nil, or_false] at hId ⊢
          rcases hId with rfl | rfl <;> simp)
    intro hMember
    simp only [membership, Formula.freeSupport,
      Term.freeSupportList] at hMember
    have hOmegaSupport :
        Term.freeSupport ωₘ = [] := rfl
    rw [hOmegaSupport] at hMember
    simp only [List.append_nil] at hMember
    exact hNumberFresh hMember
  have hOmegaNonempty :
      Γ ⊢ₘ[godel_quotation_theory]
        ωₘ ≠ₘ ∅ₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence
          standard_sequence_omega_ne_empty
  have hStandardMember :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_sequence [number] ∈ₘ
          seq_spaceₘ(ωₘ) := by
    exact
      standard_sequence_mem_sequence_space_of_theory_context
        (T := godel_quotation_theory)
        (Γ := Γ)
        (fun _ hFormula => Or.inl hFormula)
        (fun _ hFormula =>
          godel_quotation_theory_sentence hFormula)
        ωₘ hElements
        (hElementsFresh 0 (by simp))
        (hElementsFresh 1 (by simp))
        (hElementsFresh 2 (by simp))
        omega_term_admissible
        (hOmegaFresh 0) (hOmegaFresh 1)
        (hContextFresh 0 (by simp))
        (hContextFresh 1 (by simp))
        hOmegaNonempty
        (by
          intro element hElement
          rcases List.mem_singleton.mp hElement with rfl
          exact hNumberMem)
  have hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_sequence [number] ≐ₘ
          singleton_symbol_code_term number :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_singleton_sequence_eq_symbol_code
            number hNumber
  have hTransport :=
    membership_left_iff_of_equality
      (standard_sequence [number])
      (singleton_symbol_code_term number)
      (seq_spaceₘ(ωₘ))
      (seq_admissible_m 0 hElements)
      (singleton_symbol_code_term_admissible
        number hNumber)
      (finite_sequence_space_term_admissible
        ωₘ omega_term_admissible)
      hEquality
  exact FirstOrder.Derives.iffElimRight
    hTransport <| by
      simpa [code_string_space_term] using
        hStandardMember

/--
长度一符号码的等式可反演为其唯一值的等式。

证明只在零位读取两边的函数值；不要求值是标准 numeral，也不使用编码互素性。
因此变量、常元以及复合非逻辑符号都可以复用这一注入性接口。
-/
theorem gq_singleton_symbol_code_value_eq_of_equality
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hFresh :
      ReservedIdsFresh [0, 1, 2] [left, right])
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        sym_codeₘ(left) ≐ₘ sym_codeₘ(right)) :
    Γ ⊢ₘ[godel_quotation_theory]
      left ≐ₘ right := by
  have hLeftOpening :=
    gq_singleton_symbol_code_opening
      (Γ := Γ) left hLeft
      (by
        intro term hTerm id hId
        rw [List.mem_singleton] at hTerm
        subst term
        exact hFresh left (by simp) id hId)
  have hRightOpening :=
    gq_singleton_symbol_code_opening
      (Γ := Γ) right hRight
      (by
        intro term hTerm id hId
        rw [List.mem_singleton] at hTerm
        subst term
        exact hFresh right (by simp) id hId)
  have hRightPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(sym_codeₘ(right))) ∧ₘ
          ((sym_codeₘ(right) ·ₘ numₘ(0)) ≐ₘ right)) :=
    FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.conjElimRight
        hRightOpening
  have hLeftAsRight :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(sym_codeₘ(left))) ∧ₘ
          ((sym_codeₘ(left) ·ₘ numₘ(0)) ≐ₘ right)) :=
    gq_point_inversion_of_equality
      (sym_codeₘ(left)) (sym_codeₘ(right))
      (numₘ(0)) right
      hEquality hRightPoint
  have hLeftPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        (sym_codeₘ(left) ·ₘ numₘ(0)) ≐ₘ left :=
    FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight
          hLeftOpening
  exact Metatheory.Derives.equality_trans
    (Metatheory.Derives.equality_symm hLeftPoint)
    (FirstOrder.Derives.conjElimRight hLeftAsRight)

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
