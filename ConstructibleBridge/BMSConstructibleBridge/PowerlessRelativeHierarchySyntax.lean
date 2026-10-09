import BMSConstructibleBridge.PowerlessMemberDefDerives
import BMSConstructibleBridge.SecondOrderGraphOrdinalFormula

/-! # 相对层次的纯隶属语言历史公式

层次是模型内的集合函数，不是编码实数族或宿主函数。基集、阶段、函数和
值域界均显式保留；此文件只构造实际 AST，其可推导性由后续语义桥证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeHierarchySyntax

open Logic FirstOrder SecondOrderObjectSyntax

set_option autoImplicit false

abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def empty_m {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .neg (member_m (.bvar .here) (up a))

def ordinal_substitution_m {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) :
    Substitution ℒ [.set] [] Γ Δ :=
  .map (fun v => match v with | .here => a) (fun v => nomatch v)

def ordinal_m {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  SecondOrderGraphOrdinalFormula.source_m.substitute (ordinal_substitution_m a)

def successor_m {Γ Δ : SortContext ℒ} (a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up b))
    (.disj (member_m (.bvar .here) (up a)) (.equal (.bvar .here) (up a)))

def limit_m {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (.existsE .set (member_m (.bvar .here) (up a))) <|
    .forallE .set <| .imp (member_m (.bvar .here) (up a)) <|
      .existsE .set <| .conj (member_m (.bvar .here) (up (up a)))
        (member_m (.bvar (.there .here)) (.bvar .here))

def union_m {Γ Δ : SortContext ℒ} (f a c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up c)) <|
    .existsE .set <| .existsE .set <|
      .conj (member_m (.bvar (.there .here)) (up (up (up a)))) <|
        .conj (value_m (up (up (up f))) (.bvar (.there .here)) (.bvar .here))
          (member_m (.bvar (.there (.there .here))) (.bvar .here))

def successor_step_m {Γ Δ : SortContext ℒ} (f a c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <|
    .conj (successor_m (.bvar (.there .here)) (up (up a))) <|
      .conj (value_m (up (up f)) (.bvar (.there .here)) (.bvar .here))
        (PowerlessMemberDefSyntax.global_m (.bvar .here) (up (up c)))

def step_m {Γ Δ : SortContext ℒ} (B f a c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (empty_m a) (.equal c B)) <|
    .disj (successor_step_m f a c) (.conj (limit_m a) (union_m f a c))

def history_m {Γ Δ : SortContext ℒ} (B A f r : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (map_m f A r) <|
    .forallE .set <| .forallE .set <| .imp
      (.conj (member_m (.bvar (.there .here)) (up (up A)))
        (value_m (up (up f)) (.bvar (.there .here)) (.bvar .here)))
      (step_m (up (up B)) (up (up f)) (.bvar (.there .here)) (.bvar .here))

def level_m {Γ Δ : SortContext ℒ} (B a c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    .conj (ordinal_m (.bvar (.there (.there .here)))) <|
      .conj (member_m (up (up (up a))) (.bvar (.there (.there .here)))) <|
        .conj (history_m (up (up (up B))) (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
          (value_m (.bvar (.there .here)) (up (up (up a))) (up (up (up c))))

def class_m {Γ Δ : SortContext ℒ} (B x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <|
    .conj (level_m (up (up B)) (.bvar (.there .here)) (.bvar .here))
      (member_m (up (up x)) (.bvar .here))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeHierarchySyntax
