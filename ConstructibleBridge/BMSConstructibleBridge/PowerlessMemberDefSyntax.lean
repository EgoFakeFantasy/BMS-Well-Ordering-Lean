import BMSConstructibleBridge.SecondOrderMemberDefArithmetic
import BMSConstructibleBridge.PowerlessArithmeticTranslation
import BMSConstructibleBridge.SecondOrderLegalFormulaIndex

/-!
# 相对 Def 的纯隶属语言公式

用实际 ω 满射读取母集，合法性、求值和参数切片由关系式算术翻译给出。
所有辅助实数都显式限制为 ω 子集；函数和母集不作实数变量。空分支精确
输出 {∅}。这里只定义 AST，存在唯一性及与原呈现的语义对应须另行证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefSyntax

open Logic FirstOrder SecondOrderObjectSyntax
open Automation.RelationalTranslation (weakenTerm existsBlock)

set_option autoImplicit false

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def edge_parameters_m {Γ Δ : SortContext ℒ} (Q n m : Term ℒ Γ Δ .set) :
    PowerlessArithmeticTerms.assignment_m [.num, .num, .set] Γ Δ
  | _, .here => n
  | _, .there .here => m
  | _, .there (.there .here) => Q

def edge_m {Γ Δ : SortContext ℒ} (ω e Q n m : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessArithmeticTranslation.formula_m (Γ := []) ω e (fun v => nomatch v) (edge_parameters_m Q n m)
    (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here)))

def legal_parameters_m {Γ Δ : SortContext ℒ} (V E i : Term ℒ Γ Δ .set) :
    PowerlessArithmeticTerms.assignment_m [.num, .set, .set] Γ Δ
  | _, .here => i
  | _, .there .here => V
  | _, .there (.there .here) => E

def legal_m {Γ Δ : SortContext ℒ} (ω e V E i : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessArithmeticTranslation.formula_m (Γ := []) ω e (fun v => nomatch v) (legal_parameters_m V E i)
    SecondOrderLegalFormulaIndex.formula_m

def packet_parameters_m {Γ Δ : SortContext ℒ} (V E D Q R T F : Term ℒ Γ Δ .set) :
    PowerlessArithmeticTerms.assignment_m [.set, .set, .set, .set, .set, .set, .set] Γ Δ
  | _, .here => V
  | _, .there .here => E
  | _, .there (.there .here) => D
  | _, .there (.there (.there .here)) => Q
  | _, .there (.there (.there (.there .here))) => R
  | _, .there (.there (.there (.there (.there .here)))) => T
  | _, .there (.there (.there (.there (.there (.there .here))))) => F

def packet_m {Γ Δ : SortContext ℒ} (ω e V E D Q R T F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessArithmeticTranslation.formula_m (Γ := []) ω e (fun v => nomatch v) (packet_parameters_m V E D Q R T F)
    SecondOrderMemberDefArithmetic.formula_m

def onto_m {Γ Δ : SortContext ℒ} (ω X f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up X)) <|
    .existsE .set <| .conj (member_m (.bvar .here) (up (up ω)))
      (value_m (up (up f)) (.bvar .here) (.bvar (.there .here)))

def atoms_m {Γ Δ : SortContext ℒ} (ω e f Q R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up ω)) <|
    .forallE .set <| .imp (member_m (.bvar .here) (up (up ω))) <|
      .forallE .set <| .forallE .set <| .imp
        (.conj (value_m (up (up (up (up f)))) (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)))
          (value_m (up (up (up (up f)))) (.bvar (.there (.there .here))) (.bvar .here))) <|
        .conj
          (.iff (edge_m (up (up (up (up ω)))) (up (up (up (up e)))) (up (up (up (up Q))))
            (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))))
            (.equal (.bvar (.there .here)) (.bvar .here)))
          (.iff (edge_m (up (up (up (up ω)))) (up (up (up (up e)))) (up (up (up (up R))))
            (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))))
            (member_m (.bvar (.there .here)) (.bvar .here)))

def slice_m {Γ Δ : SortContext ℒ} (ω e f F i x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (member_m (.bvar .here) (up ω)) <|
    .conj (edge_m (up ω) (up e) (up F) (up i) (.bvar .here))
      (value_m (up f) (.bvar .here) (up x))

def collection_m {Γ Δ : SortContext ℒ} (ω e Y f V E F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up Y)) <|
    .existsE .set <| .conj (member_m (.bvar .here) (up (up ω))) <|
      .conj (legal_m (up (up ω)) (up (up e)) (up (up V)) (up (up E)) (.bvar .here)) <|
        .forallE .set <| .iff (member_m (.bvar .here) (.bvar (.there (.there .here))))
          (slice_m (up (up (up ω))) (up (up (up e))) (up (up (up f))) (up (up (up F)))
            (.bvar (.there .here)) (.bvar .here))

def enumeration_m {Γ Δ : SortContext ℒ} (ω e X Y f V E D Q R T F : Term ℒ Γ Δ .set) :
    Formula ℒ Γ Δ :=
  .conj (map_m f ω X) <| .conj (onto_m ω X f) <|
    .conj (PowerlessArithmeticTranslation.domain_m .set ω V) <|
    .conj (PowerlessArithmeticTranslation.domain_m .set ω E) <|
    .conj (PowerlessArithmeticTranslation.domain_m .set ω D) <|
    .conj (PowerlessArithmeticTranslation.domain_m .set ω Q) <|
    .conj (PowerlessArithmeticTranslation.domain_m .set ω R) <|
    .conj (PowerlessArithmeticTranslation.domain_m .set ω T) <|
    .conj (PowerlessArithmeticTranslation.domain_m .set ω F) <|
    .conj (packet_m ω e V E D Q R T F) <|
      .conj (atoms_m ω e f Q R) (collection_m ω e Y f V E F)

def nonempty_m {Γ Δ : SortContext ℒ} (ω e X Y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let Ξ : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set]
  existsBlock Ξ <| enumeration_m (weakenTerm Ξ ω) (weakenTerm Ξ e) (weakenTerm Ξ X) (weakenTerm Ξ Y)
    (.bvar .here) (.bvar (.there .here)) (.bvar (.there (.there .here)))
    (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there .here)))))
    (.bvar (.there (.there (.there (.there (.there .here))))))
    (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there .here))))))))

def formula_m {Γ Δ : SortContext ℒ} (ω e X Y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (.forallE .set (.neg (member_m (.bvar .here) (up X)))) (pair_m X X Y))
    (nonempty_m ω e X Y)

/-- 隐藏唯一的 ω 与空对象证书，公开接口只保留母集和输出两个参数。 -/
def global_m {Γ Δ : SortContext ℒ} (X Y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <|
    .conj (SecondOrderOmegaSyntax.omega_m (.bvar (.there .here))) <|
      .conj (.forallE .set (.neg (member_m (.bvar .here) (.bvar (.there .here)))))
        (formula_m (.bvar (.there .here)) (.bvar .here) (up (up X)) (up (up Y)))

/-- 待验证的纯对象存在唯一句；定义此 AST 本身不构成其推导。 -/
def total_unique_m : Sentence ℒ :=
  .forallE .set <| .existsE .set <| .conj
    (global_m (.bvar (.there .here)) (.bvar .here))
    (.forallE .set <| .imp (global_m (.bvar (.there (.there .here))) (.bvar .here))
      (.equal (.bvar .here) (.bvar (.there .here))))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefSyntax
