import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaBinderCode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaCodeReplay

/-!
# FormalSystem 公式 binder 条件的通用回放

本模块只处理变量 token 的对象层正向证书与等式运输；有限序列装配留给具体对象
元理论层。
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

/-- 有界变量名字解码成功时，对应 numeral 满足对象层变量 token 条件。 -/
theorem gq_fs_variable_token_condition_of_decode
    {token name : Nat}
    (hDecode :
      fs_variable_name_decode token = some name) :
    Derives godel_quotation_theory [] (
      fs_variable_token_condition (numₘ(token))) := by
  have hToken :
      Numbered.variable_token name = token :=
    fs_variable_name_decode_value_of_some hDecode
  rw [← hToken]
  have hNameMember :
      Derives godel_quotation_theory [] (
        numₘ(name) ∈ₘ
          Sₘ(numₘ(Numbered.variable_token name))) :=
    gq_weaken_standard_sequence <| by
      simpa [finite_numeral_term] using
        standard_sequence_finite_numeral_mem_of_lt
          name
          (Numbered.variable_token name + 1)
          (fs_name_lt_variable_token_succ name)
  have hCodeEquality :
      Derives godel_quotation_theory [] (
        sym_codeₘ(numₘ(Numbered.variable_token name)) ≐ₘ
          variable_symbol_code_term (numₘ(name))) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm
        (gq_standard_token_singleton_eq_symbol_code
          (Numbered.variable_token name)))
      (Metatheory.Derives.equality_symm
        (gq_fs_variable_symbol_code_eq_standard_token_sequence
          name))
  have hTokenOpen :
      Term.openAt SetSort.set 0 (numₘ(name))
          (numₘ(Numbered.variable_token name)) =
        numₘ(Numbered.variable_token name) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (numₘ(name))
      (numₘ(Numbered.variable_token name))
      (finite_numeral_term_admissible
        (Numbered.variable_token name)).2
  have hNumeralOpen (number : Nat) :
      Term.openAt SetSort.set 0 (numₘ(name))
          (numₘ(number)) =
        numₘ(number) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (numₘ(name))
      (numₘ(number))
      (finite_numeral_term_admissible number).2
  unfold fs_variable_token_condition
  nd_apply FirstOrder.Derives.exists_intro
    (term := numₘ(name))
  simpa [Formula.openAt, Term.openAt,
    hTokenOpen, hNumeralOpen] using
    FirstOrder.Derives.conjIntro
      hNameMember hCodeEquality

/-- `fs_variable_token_condition` 沿任意已证对象项等式双向运输。 -/
theorem fs_variable_token_condition_iff_of_equality
    {T : SetTheory} {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEquality : Derives T Γ (left ≐ₘ right)) :
    Derives T Γ (
      fs_variable_token_condition left ↔ₘ
        fs_variable_token_condition right) := by
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [left ≐ₘ right]
  let body : SetFormula :=
    fs_variable_token_condition (x#parameter)
  have hBody :
      Formula.Admissible body :=
    fs_variable_token_condition_admissible
      (x#parameter)
      (set_variable_admissible parameter)
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ)
      (sort := SetSort.set)
      (eigen := parameter)
      (left := left) (right := right)
      (body := body)
      hEquality
  have hNumeralFixed
      (replacement : SetTerm) (number : Nat) :
      Term.substituteFree SetSort.set parameter replacement
          (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    simp
  simpa [body, fs_variable_token_condition,
    Formula.substituteFree, Term.substituteFree,
    set_variable, hNumeralFixed] using hCongruence

/--
固定代码时，单个 binder 位置条件沿位置等式双向运输。
后继位置和该位置的序列值由同一个代换同时运输。
-/
theorem
    fs_formula_binder_condition_lifted_iff_of_index_equality
    {T : SetTheory} {Γ : Context signature}
    (code left right : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEquality : Derives T Γ (left ≐ₘ right)) :
    Derives T Γ (
      fs_formula_binder_condition_lifted
          code left (code ·ₘ Sₘ(left)) ↔ₘ
        fs_formula_binder_condition_lifted
          code right (code ·ₘ Sₘ(right))) := by
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [code ≐ₘ code, left ≐ₘ right]
  let point : SetTerm := x#parameter
  let body : SetFormula :=
    fs_formula_binder_condition_lifted
      code point (code ·ₘ Sₘ(point))
  have hParameter :
      Term.Admissible point SetSort.set := by
    simpa [point] using
      set_variable_admissible parameter
  have hDomain :
      Term.Admissible (domₘ(code)) SetSort.set :=
    domain_term_admissible code hCode
  have hValue :
      Term.Admissible
        (code ·ₘ point) SetSort.set :=
    function_application_term_admissible
      code point hCode hParameter
  have hNext :
      Term.Admissible (Sₘ(point)) SetSort.set :=
    successor_term_admissible point hParameter
  have hNextValue :
      Term.Admissible
        (code ·ₘ Sₘ(point)) SetSort.set :=
    function_application_term_admissible
      code (Sₘ(point)) hCode hNext
  have hBody :
      Formula.Admissible body := by
    dsimp [body]
    exact Formula.Admissible.imp
      (Formula.Admissible.equal
        hValue
        (finite_numeral_term_admissible
          (Numbered.logical_token .universal)))
      (Formula.Admissible.conj
        (membership_formula_admissible
          hNext hDomain)
        (fs_variable_token_condition_admissible
          (code ·ₘ Sₘ(point))
          hNextValue))
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ)
      (sort := SetSort.set)
      (eigen := parameter)
      (left := left) (right := right)
      (body := body)
      hEquality
  have hCodeFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement
          code =
        code := by
    apply Term.substituteFree_eq_self_of_not_mem
    have hFresh :
        (SetSort.set, parameter) ∉
          Formula.freeSupport (code ≐ₘ code) := by
      dsimp [parameter]
      exact FreshVariable.fresh_id_not_mem_m
        (sort := SetSort.set)
        (formulas := [code ≐ₘ code, left ≐ₘ right])
        (formula := code ≐ₘ code)
        (by simp)
    intro hMember
    apply hFresh
    simp only [Formula.freeSupport]
    exact List.mem_append_left _ hMember
  have hNumeralFixed
      (replacement : SetTerm) (number : Nat) :
      Term.substituteFree SetSort.set parameter replacement
          (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    simp
  simpa [body, point,
    fs_formula_binder_condition_lifted,
    fs_variable_token_condition,
    Formula.substituteFree, Term.substituteFree,
    set_variable, hCodeFixed,
    hNumeralFixed] using hCongruence

/-- verifier 的完整 replay 词法条件沿任意已证代码等式双向运输。 -/
theorem fs_formula_replay_condition_iff_of_equality
    {T : SetTheory} {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEquality : Derives T Γ (left ≐ₘ right)) :
    Derives T Γ (
      fs_formula_replay_condition left ↔ₘ
        fs_formula_replay_condition right) := by
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [left ≐ₘ right]
  let body : SetFormula :=
    fs_formula_replay_condition (x#parameter)
  have hBody :
      Formula.Admissible body :=
    fs_formula_replay_condition_admissible
      (x#parameter)
      (set_variable_admissible parameter)
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ)
      (sort := SetSort.set)
      (eigen := parameter)
      (left := left) (right := right)
      (body := body)
      (hLeftCheck :=
        Term.check_admissible_complete hLeft)
      (hRightCheck :=
        Term.check_admissible_complete hRight)
      hEquality
  have hLeft :
      Formula.substituteFree SetSort.set parameter left
          body =
        fs_formula_replay_condition left := by
    dsimp [body]
    exact fs_formula_replay_condition_substitute
      (x#parameter) left left parameter (by
        simp [Term.substituteFree, set_variable])
  have hRight :
      Formula.substituteFree SetSort.set parameter right
          body =
        fs_formula_replay_condition right := by
    dsimp [body]
    exact fs_formula_replay_condition_substitute
      (x#parameter) right right parameter (by
        simp [Term.substituteFree, set_variable])
  simpa [hLeft, hRight] using hCongruence

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
