import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Rosser
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuantifier

/-!
# 内在 Rosser 有限比较装配

本层只消费内在 `Core`、`Delta0ProofGraph` 与标准 numeral 的码域证明。有限初始段、
证明码切分和存在见证消去全部在类型化 bound/free 上下文中完成，不再携带变量编号、
admissibility 或关闭自由变量合同。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 否定的二元模板可沿首参数等式直接替换。 -/
private theorem neg_apply_two_eq_subst_left
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (template : FormulaTemplate.Binary)
    (fixed source target : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] source ≐ₘ target)
    (hNegation : Γ ⊢ₘ[T] ¬ₘ template source fixed) :
    Γ ⊢ₘ[T] ¬ₘ template target fixed := by
  let body : SetFormula [SetSort.set] free :=
    ¬ₘ template (.bvar .here) (fixed.weakenBound SetSort.set)
  have hSourceShape :
      Formula.instantiateTop source
          (template (.bvar .here)
            (fixed.weakenBound SetSort.set)) =
        template source fixed :=
    FormulaTemplate.apply_two_instantiateTop_bvar template fixed source
  have hTargetShape :
      Formula.instantiateTop target
          (template (.bvar .here)
            (fixed.weakenBound SetSort.set)) =
        template target fixed :=
    FormulaTemplate.apply_two_instantiateTop_bvar template fixed target
  have hSource : Γ ⊢ₘ[T] body.instantiateTop source := by
    unfold body
    rw [Formula.instantiateTop_neg, hSourceShape]
    exact hNegation
  have hTarget := FirstOrder.Derives.eq_subst
    (body := body) hEquality hSource
  unfold body at hTarget
  rw [Formula.instantiateTop_neg, hTargetShape] at hTarget
  exact hTarget

/-- 全部标准 `index < bound` 的反证装配成对象层有限全称。 -/
theorem rosser_no_smaller
    {T : SetTheory}
    (C : Core T)
    (G : Delta0ProofGraph)
    {free : SetContext}
    {Γ : Context signature free}
    (bound : Nat)
    (right : SetOpenTerm free)
    (hNoSmaller : ∀ index, index < bound →
      Γ ⊢ₘ[T] ¬ₘ G.condition (numₘ(index)) right) :
    Γ ⊢ₘ[T] G.no_smaller (numₘ(bound)) right := by
  let point : SetOpenTerm (SetSort.set :: free) := .fvar .here
  let body : SetOpenFormula (SetSort.set :: free) :=
    (point ∈ₘ (numₘ(bound) : SetOpenTerm (SetSort.set :: free))) ⟶ₘ
      ¬ₘ G.condition point (right.weakenFree SetSort.set)
  have hBody :
      FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T] body := by
    apply FirstOrder.Derives.imp_intro
    let Δ : Context signature (SetSort.set :: free) :=
      (point ∈ₘ numₘ(bound)) ::
        FreshVariable.extendContext SetSort.set Γ
    have hMember : Δ ⊢ₘ[T] point ∈ₘ numₘ(bound) :=
      FirstOrder.Derives.assumption (by simp [Δ])
    apply C.member_elim bound point
      (¬ₘ G.condition point (right.weakenFree SetSort.set)) hMember
    intro index hIndex
    let Ε : Context signature (SetSort.set :: free) :=
      (point ≐ₘ numₘ(index)) :: Δ
    have hEquality : Ε ⊢ₘ[T] point ≐ₘ numₘ(index) :=
      FirstOrder.Derives.assumption (by simp [Ε])
    have hNegationFresh := fresh_context_weaken
      (hNoSmaller index hIndex)
    have hNegation' : Ε ⊢ₘ[T]
        (¬ₘ G.condition (numₘ(index)) right).weakenFree SetSort.set :=
      FirstOrder.Derives.context_weaken
        (Γ := FreshVariable.extendContext SetSort.set Γ) (Δ := Ε)
        (by
          intro formula hFormula
          exact List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hFormula))
        hNegationFresh
    have hNegation : Ε ⊢ₘ[T]
        ¬ₘ G.condition
          ((numₘ(index) : SetOpenTerm free).weakenFree SetSort.set)
          (right.weakenFree SetSort.set) := by
      simpa using hNegation'
    exact neg_apply_two_eq_subst_left G.condition
      (right.weakenFree SetSort.set)
      ((numₘ(index) : SetOpenTerm free).weakenFree SetSort.set)
      point (FirstOrder.Derives.eq_symm (by
        simpa [finite_numeral_term_weakenFree] using hEquality)) hNegation
  simpa [Delta0ProofGraph.no_smaller,
    Formula.LevyBound.boundedForall, Formula.forallFreeTop,
    body, point, Formula.abstractFreeTop,
    Formula.substitute, Substitution.abstractFreeTop,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped,
    FormulaTemplate.apply_two_substituteMapped,
    Formula.LevyBound.membership,
    Term.substituteMapped_abstractFreeTop_weakenFree,
    finite_numeral_term_weakenBound,
    Formula.weakenFree, Formula.renameFree, Renaming.weakenFree,
    VariableSubstitution.abstractBound,
    VariableSubstitution.abstractFreeTop] using!
    FirstOrder.Derives.forall_intro hBody

/-- Rosser 比较体打开到规范 fresh 证明码。 -/
private theorem comparison_body_openBoundTop
    {T : SetTheory}
    (C : Core T)
    (G : Delta0ProofGraph)
    (left right : QuineEncoding.Code) :
    Formula.openBoundTop (σ := signature) SetSort.set
        (C.code_domain.condition (.bvar .here) ∧ₘ
          (G.condition (.bvar .here)
              ((left : SetOpenTerm []).weakenBound SetSort.set) ∧ₘ
            G.no_smaller (.bvar .here)
              ((right : SetOpenTerm []).weakenBound SetSort.set))) =
      (C.code_domain.condition
          (FreshVariable.newest (σ := signature)
            (free := []) SetSort.set) ∧ₘ
        (G.condition
            (FreshVariable.newest (σ := signature)
              (free := []) SetSort.set)
            ((left : SetOpenTerm []).weakenFree SetSort.set) ∧ₘ
          G.no_smaller
            (FreshVariable.newest (σ := signature)
              (free := []) SetSort.set)
            ((right : SetOpenTerm []).weakenFree SetSort.set))) := by
  rw [Formula.openBoundTop_eq_instantiateTop_weakenFree]
  rw [Formula.weakenFree_conj, FormulaTemplate.apply_one_weakenFree,
    Formula.weakenFree_conj, FormulaTemplate.apply_two_weakenFree,
    Delta0ProofGraph.no_smaller_weakenFree]
  simp only [Term.weakenFree_bvar]
  rw [← Term.weakenFree_weakenBound SetSort.set SetSort.set left,
    ← Term.weakenFree_weakenBound SetSort.set SetSort.set right]
  rw [Formula.instantiateTop_conj,
    FormulaTemplate.apply_one_instantiateTop_bvar,
    Formula.instantiateTop_conj,
    FormulaTemplate.apply_two_instantiateTop_bvar,
    Delta0ProofGraph.no_smaller_instantiateTop_bvar]

/-- 标准证明码及其更小反证给出 Rosser 比较的正向分支。 -/
theorem rosser_comparison_positive
    {T : SetTheory}
    (C : Core T)
    (G : Delta0ProofGraph)
    (hNumeral : ∀ number,
      Derives T ([] : Context signature [])
        (C.code_domain.condition (numₘ(number))))
    (proofCode : Nat)
    (left right : QuineEncoding.Code)
    (hCondition : Derives T []
      (G.condition (numₘ(proofCode)) left))
    (hNoSmaller : ∀ code, code < proofCode →
      Derives T [] (¬ₘ G.condition (numₘ(code)) right)) :
    Derives T [] (G.comparison C.code_domain left right) := by
  have hDomain := hNumeral proofCode
  have hBounded := rosser_no_smaller C G proofCode right hNoSmaller
  apply FirstOrder.Derives.exists_intro (numₘ(proofCode))
  rw [Formula.instantiateTop_conj,
    FormulaTemplate.apply_one_instantiateTop_bvar,
    Formula.instantiateTop_conj,
    FormulaTemplate.apply_two_instantiateTop_bvar,
    Delta0ProofGraph.no_smaller_instantiateTop_bvar]
  exact FirstOrder.Derives.conj_intro hDomain
    (FirstOrder.Derives.conj_intro hCondition hBounded)

/-- 右侧标准证明及左侧有限反证排除 Rosser 比较。 -/
theorem rosser_comparison_negative
    {T : SetTheory}
    (C : Core T)
    (G : Delta0ProofGraph)
    (proofCode : Nat)
    (left right : QuineEncoding.Code)
    (hCondition : Derives T []
      (G.condition (numₘ(proofCode)) right))
    (hNoSmaller : ∀ code, code ≤ proofCode →
      Derives T [] (¬ₘ G.condition (numₘ(code)) left)) :
    Derives T [] (¬ₘ G.comparison C.code_domain left right) := by
  apply FirstOrder.Derives.neg_intro
  let rawBody : SetFormula [SetSort.set] [] :=
    C.code_domain.condition (.bvar .here) ∧ₘ
      (G.condition (.bvar .here)
          ((left : SetOpenTerm []).weakenBound SetSort.set) ∧ₘ
        G.no_smaller (.bvar .here)
          ((right : SetOpenTerm []).weakenBound SetSort.set))
  let opened : SetOpenFormula [SetSort.set] :=
    Formula.openBoundTop (σ := signature) SetSort.set rawBody
  have hComparison :
      (G.comparison C.code_domain left right) :: [] ⊢ₘ[T]
        G.comparison C.code_domain left right :=
    FirstOrder.Derives.assumption (by simp)
  have hExistential :
      (G.comparison C.code_domain left right) :: [] ⊢ₘ[T]
        opened.existsFreeTop SetSort.set := by
    simpa [opened, rawBody, Delta0ProofGraph.comparison] using hComparison
  apply FirstOrder.Derives.exists_elim hExistential
  let point : SetOpenTerm [SetSort.set] :=
    FreshVariable.newest (σ := signature) (free := []) SetSort.set
  let Γ : Context signature [SetSort.set] :=
    opened :: FreshVariable.extendContext SetSort.set
      ((G.comparison C.code_domain left right) :: [])
  have hOpened : Γ ⊢ₘ[T] opened :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hOpenedShape : opened =
      (C.code_domain.condition point ∧ₘ
        (G.condition point
            ((left : SetOpenTerm []).weakenFree SetSort.set) ∧ₘ
          G.no_smaller point
            ((right : SetOpenTerm []).weakenFree SetSort.set))) := by
    simpa [opened, rawBody, point] using
      comparison_body_openBoundTop C G left right
  have hConjunction : Γ ⊢ₘ[T]
      (C.code_domain.condition point ∧ₘ
        (G.condition point
            ((left : SetOpenTerm []).weakenFree SetSort.set) ∧ₘ
          G.no_smaller point
            ((right : SetOpenTerm []).weakenFree SetSort.set))) := by
    rw [← hOpenedShape]
    exact hOpened
  have hDomain : Γ ⊢ₘ[T] C.code_domain.condition point :=
    FirstOrder.Derives.conj_elim_left hConjunction
  have hRest := FirstOrder.Derives.conj_elim_right hConjunction
  have hLeft : Γ ⊢ₘ[T]
      G.condition point
        ((left : SetOpenTerm []).weakenFree SetSort.set) :=
    FirstOrder.Derives.conj_elim_left hRest
  have hBounded : Γ ⊢ₘ[T]
      G.no_smaller point
        ((right : SetOpenTerm []).weakenFree SetSort.set) :=
    FirstOrder.Derives.conj_elim_right hRest
  apply C.cut_elim proofCode point (.falsum : SetOpenFormula [SetSort.set])
    hDomain
  · intro index hIndex
    let Δ : Context signature [SetSort.set] :=
      (point ≐ₘ numₘ(index)) :: Γ
    have hEquality : Δ ⊢ₘ[T] point ≐ₘ numₘ(index) :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hNegationFresh := fresh_context_weaken
      (hNoSmaller index hIndex)
    have hNegation : Δ ⊢ₘ[T]
        ¬ₘ G.condition (numₘ(index))
          ((left : SetOpenTerm []).weakenFree SetSort.set) := by
      apply FirstOrder.Derives.context_weaken
        (Γ := FreshVariable.extendContext SetSort.set
          ([] : Context signature []))
        (Δ := Δ)
      · intro formula hFormula
        simp [FreshVariable.extendContext] at hFormula
      · simpa [finite_numeral_term_weakenFree] using hNegationFresh
    have hNegationPoint : Δ ⊢ₘ[T]
        ¬ₘ G.condition point
          ((left : SetOpenTerm []).weakenFree SetSort.set) :=
      neg_apply_two_eq_subst_left G.condition
        ((left : SetOpenTerm []).weakenFree SetSort.set)
        (numₘ(index)) point
        (FirstOrder.Derives.eq_symm hEquality) hNegation
    have hLeft' : Δ ⊢ₘ[T]
        G.condition point
          ((left : SetOpenTerm []).weakenFree SetSort.set) :=
      FirstOrder.Derives.context_weaken_cons hLeft
    exact FirstOrder.Derives.neg_elim hLeft' hNegationPoint
  · let Δ : Context signature [SetSort.set] :=
      (numₘ(proofCode) ∈ₘ point) :: Γ
    have hMember : Δ ⊢ₘ[T] numₘ(proofCode) ∈ₘ point :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hBounded' : Δ ⊢ₘ[T]
        G.no_smaller point
          ((right : SetOpenTerm []).weakenFree SetSort.set) :=
      FirstOrder.Derives.context_weaken_cons hBounded
    let body : SetFormula [SetSort.set] [SetSort.set] :=
      ¬ₘ G.condition (.bvar .here)
        (((right : SetOpenTerm []).weakenFree SetSort.set).weakenBound
          SetSort.set)
    have hNegationAt : Δ ⊢ₘ[T]
        body.instantiateTop (numₘ(proofCode)) := by
      exact bounded_forall_elim point body (numₘ(proofCode))
        (by simpa [body, Delta0ProofGraph.no_smaller] using hBounded')
        hMember
    have hNegation : Δ ⊢ₘ[T]
        ¬ₘ G.condition (numₘ(proofCode))
          ((right : SetOpenTerm []).weakenFree SetSort.set) := by
      have hShape :
          Formula.instantiateTop
              (numₘ(proofCode) : SetOpenTerm [SetSort.set])
              (G.condition (.bvar .here)
                (((right : SetOpenTerm []).weakenFree SetSort.set).weakenBound
                  SetSort.set)) =
            G.condition (numₘ(proofCode))
              ((right : SetOpenTerm []).weakenFree SetSort.set) :=
        FormulaTemplate.apply_two_instantiateTop_bvar G.condition
          ((right : SetOpenTerm []).weakenFree SetSort.set)
          (numₘ(proofCode) : SetOpenTerm [SetSort.set])
      unfold body at hNegationAt
      rw [Formula.instantiateTop_neg, hShape] at hNegationAt
      exact hNegationAt
    have hConditionFresh := fresh_context_weaken hCondition
    have hCondition' : Δ ⊢ₘ[T]
        G.condition (numₘ(proofCode))
          ((right : SetOpenTerm []).weakenFree SetSort.set) := by
      apply FirstOrder.Derives.context_weaken
        (Γ := FreshVariable.extendContext SetSort.set
          ([] : Context signature []))
        (Δ := Δ)
      · intro formula hFormula
        simp [FreshVariable.extendContext] at hFormula
      · simpa [finite_numeral_term_weakenFree] using hConditionFresh
    exact FirstOrder.Derives.neg_elim hCondition' hNegation

/-- 标准 numeral 属于码域即可从 `Core` 构造完整 Rosser 装配。 -/
theorem rosser_assembly_of_core
    {T : SetTheory}
    (C : Core T)
    (G : Delta0ProofGraph)
    (hNumeral : ∀ number,
      Derives T ([] : Context signature [])
        (C.code_domain.condition (numₘ(number)))) :
    RosserAssembly T G C where
  positive proofCode left right hCondition hNoSmaller :=
    rosser_comparison_positive C G hNumeral proofCode
      left right hCondition hNoSmaller
  negative proofCode left right hCondition hNoSmaller :=
    rosser_comparison_negative C G proofCode
      left right hCondition hNoSmaller

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
