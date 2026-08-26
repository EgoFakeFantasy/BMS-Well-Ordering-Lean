import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCode
/-!
# 公式码生成条件的自由支撑

本模块隔离一步生成条件穿过内部存在 binder 时的自由支撑 bookkeeping，避免该机械
递归拖慢最小闭包反演主体的类型检查。
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

/-- 一步生成条件不会引入候选项与代码项之外的 eigen `600`。 -/
theorem gq_formula_code_generation_condition_fresh_600
    (candidate code : SetTerm)
    (hCandidateFresh :
      (SetSort.set, 600) ∉ Term.freeSupport candidate)
    (hCodeFresh :
      (SetSort.set, 600) ∉ Term.freeSupport code) :
    (SetSort.set, 600) ∉
      Formula.freeSupport
        (formula_code_generation_condition candidate code) := by
  have hNegationBase :
      (SetSort.set, 600) ∉
        Formula.freeSupport
          ((x#306 ∈ₘ candidate) ∧ₘ
            (code ≐ₘ neg_codeₘ(x#306))) := by
    simp only [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList]
    intro hMember
    rcases List.mem_cons.mp hMember with
      hReserved | hTail
    · exact (by decide : (600 : Nat) ≠ 306) <|
        congrArg Prod.snd hReserved
    · rcases List.mem_append.mp hTail with
        hCandidate | hTail
      · exact hCandidateFresh <| by
          simpa using hCandidate
      · rcases List.mem_append.mp hTail with
          hCode | hReserved
        · exact hCodeFresh <| by
            simpa using hCode
        · exact (by decide : (600 : Nat) ≠ 306) <|
            congrArg Prod.snd <|
              List.mem_singleton.mp hReserved
  have hNegation :
      (SetSort.set, 600) ∉
        Formula.freeSupport
          (Formula.closeFreeAt SetSort.set 306 0
            ((x#306 ∈ₘ candidate) ∧ₘ
              (code ≐ₘ neg_codeₘ(x#306)))) :=
    Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      (SetSort.set, 600) SetSort.set 306 0
      ((x#306 ∈ₘ candidate) ∧ₘ
        (code ≐ₘ neg_codeₘ(x#306)))
      hNegationBase
  have hImplicationBase :
      (SetSort.set, 600) ∉
        Formula.freeSupport
          (((x#307 ∈ₘ candidate) ∧ₘ
            (x#308 ∈ₘ candidate)) ∧ₘ
              (code ≐ₘ
                imp_codeₘ(x#307, x#308))) := by
    simp only [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList]
    intro hMember
    rcases List.mem_cons.mp hMember with
      h307 | hTail
    · exact (by decide : (600 : Nat) ≠ 307) <|
        congrArg Prod.snd h307
    · rcases List.mem_append.mp hTail with
        hInputs | hOutput
      · rcases List.mem_append.mp hInputs with
          hCandidate | hRightInput
        · exact hCandidateFresh <| by
            simpa using hCandidate
        · rcases List.mem_cons.mp hRightInput with
            h308 | hCandidate
          · exact (by decide : (600 : Nat) ≠ 308) <|
              congrArg Prod.snd h308
          · exact hCandidateFresh <| by
              simpa using hCandidate
      · rcases List.mem_append.mp hOutput with
          hCode | hReserved
        · exact hCodeFresh hCode
        · rcases List.mem_append.mp hReserved with
            h307 | h308
          · exact (by decide : (600 : Nat) ≠ 307) <|
              congrArg Prod.snd <|
                List.mem_singleton.mp h307
          · exact (by decide : (600 : Nat) ≠ 308) <|
              congrArg Prod.snd <|
                List.mem_singleton.mp h308
  have hImplicationInner :
      (SetSort.set, 600) ∉
        Formula.freeSupport
          (Formula.closeFreeAt SetSort.set 308 0
            (((x#307 ∈ₘ candidate) ∧ₘ
              (x#308 ∈ₘ candidate)) ∧ₘ
                (code ≐ₘ
                  imp_codeₘ(x#307, x#308)))) :=
    Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      (SetSort.set, 600) SetSort.set 308 0
      (((x#307 ∈ₘ candidate) ∧ₘ
        (x#308 ∈ₘ candidate)) ∧ₘ
          (code ≐ₘ
            imp_codeₘ(x#307, x#308)))
      hImplicationBase
  have hImplicationBody :
      (SetSort.set, 600) ∉
        Formula.freeSupport
          (∃ₘ[SetSort.set],
            Formula.closeFreeAt SetSort.set 308 0
              (((x#307 ∈ₘ candidate) ∧ₘ
                (x#308 ∈ₘ candidate)) ∧ₘ
                  (code ≐ₘ
                    imp_codeₘ(x#307, x#308)))) := by
    simpa [Formula.freeSupport] using
      hImplicationInner
  have hImplication :
      (SetSort.set, 600) ∉
        Formula.freeSupport
          (Formula.closeFreeAt SetSort.set 307 0
            (∃ₘ[SetSort.set],
              Formula.closeFreeAt SetSort.set 308 0
                (((x#307 ∈ₘ candidate) ∧ₘ
                  (x#308 ∈ₘ candidate)) ∧ₘ
                    (code ≐ₘ
                      imp_codeₘ(x#307, x#308))))) :=
    Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      (SetSort.set, 600) SetSort.set 307 0
      (∃ₘ[SetSort.set],
        Formula.closeFreeAt SetSort.set 308 0
          (((x#307 ∈ₘ candidate) ∧ₘ
            (x#308 ∈ₘ candidate)) ∧ₘ
              (code ≐ₘ
                imp_codeₘ(x#307, x#308))))
      hImplicationBody
  have hUniversalBase :
      (SetSort.set, 600) ∉
        Formula.freeSupport
          (((x#309 ∈ₘ VarSymₘ) ∧ₘ
            (x#310 ∈ₘ candidate)) ∧ₘ
              (code ≐ₘ
                forall_codeₘ(x#309, x#310))) := by
    simp only [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList]
    intro hMember
    rcases List.mem_cons.mp hMember with
      h309 | hTail
    · exact (by decide : (600 : Nat) ≠ 309) <|
        congrArg Prod.snd h309
    · rcases List.mem_cons.mp hTail with
        h310 | hTail
      · exact (by decide : (600 : Nat) ≠ 310) <|
          congrArg Prod.snd h310
      · rcases List.mem_append.mp hTail with
          hCandidate | hOutput
        · exact hCandidateFresh <| by
            simpa using hCandidate
        · rcases List.mem_append.mp hOutput with
            hCode | hReserved
          · exact hCodeFresh hCode
          · rcases List.mem_append.mp hReserved with
              h309 | h310
            · exact (by decide : (600 : Nat) ≠ 309) <|
                congrArg Prod.snd <|
                  List.mem_singleton.mp h309
            · exact (by decide : (600 : Nat) ≠ 310) <|
                congrArg Prod.snd <|
                  List.mem_singleton.mp h310
  have hUniversalInner :
      (SetSort.set, 600) ∉
        Formula.freeSupport
          (Formula.closeFreeAt SetSort.set 310 0
            (((x#309 ∈ₘ VarSymₘ) ∧ₘ
              (x#310 ∈ₘ candidate)) ∧ₘ
                (code ≐ₘ
                  forall_codeₘ(x#309, x#310)))) :=
    Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      (SetSort.set, 600) SetSort.set 310 0
      (((x#309 ∈ₘ VarSymₘ) ∧ₘ
        (x#310 ∈ₘ candidate)) ∧ₘ
          (code ≐ₘ
            forall_codeₘ(x#309, x#310)))
      hUniversalBase
  have hUniversalBody :
      (SetSort.set, 600) ∉
        Formula.freeSupport
          (∃ₘ[SetSort.set],
            Formula.closeFreeAt SetSort.set 310 0
              (((x#309 ∈ₘ VarSymₘ) ∧ₘ
                (x#310 ∈ₘ candidate)) ∧ₘ
                  (code ≐ₘ
                    forall_codeₘ(x#309, x#310)))) := by
    simpa [Formula.freeSupport] using
      hUniversalInner
  have hUniversal :
      (SetSort.set, 600) ∉
        Formula.freeSupport
          (Formula.closeFreeAt SetSort.set 309 0
            (∃ₘ[SetSort.set],
              Formula.closeFreeAt SetSort.set 310 0
                (((x#309 ∈ₘ VarSymₘ) ∧ₘ
                  (x#310 ∈ₘ candidate)) ∧ₘ
                    (code ≐ₘ
                      forall_codeₘ(x#309, x#310))))) :=
    Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      (SetSort.set, 600) SetSort.set 309 0
      (∃ₘ[SetSort.set],
        Formula.closeFreeAt SetSort.set 310 0
          (((x#309 ∈ₘ VarSymₘ) ∧ₘ
            (x#310 ∈ₘ candidate)) ∧ₘ
              (code ≐ₘ
                forall_codeₘ(x#309, x#310))))
      hUniversalBody
  simp only [formula_code_generation_condition,
    Formula.freeSupport, Term.freeSupport,
    Term.freeSupportList]
  intro hMember
  rcases List.mem_append.mp hMember with
    hCode | hTail
  · exact hCodeFresh <| by
      simpa using hCode
  · rcases List.mem_append.mp hTail with
      hNegationMember | hTail
    · exact hNegation hNegationMember
    · rcases List.mem_append.mp hTail with
        hImplicationMember | hUniversalMember
      · exact hImplication hImplicationMember
      · exact hUniversal hUniversalMember

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
