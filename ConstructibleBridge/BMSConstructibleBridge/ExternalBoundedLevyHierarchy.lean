import BMSConstructibleBridge.ExternalDelta0Translation

/-!
# 保留有界量词的外部有限 Lévy 层级

普通 `FOFormula` 用 `neg-ex-neg` 表示全称量词，若忽略成员界便会错误提高
复杂度。本文件给出与原生层级对应的外部分类：任意真正的 `Delta0Formula`
可作为零层基底，其余规则保持通常的累积 Sigma/Pi 层级。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

open Logic FirstOrder
open Constructible

mutual
  /-- 保留真正有界底层的外部累积 `Sigma` 分类。 -/
  inductive ExternalBoundedIsSigmaFinite_l :
      {arity : Nat} → Nat → FOFormula arity → Prop where
    | delta0 {arity level : Nat} (formula : Delta0Formula arity) :
        ExternalBoundedIsSigmaFinite_l level formula.toFO
    | neg {arity level : Nat} {body : FOFormula arity} :
        ExternalBoundedIsPiFinite_l level body →
          ExternalBoundedIsSigmaFinite_l level (.neg body)
    | conj {arity level : Nat} {left right : FOFormula arity} :
        ExternalBoundedIsSigmaFinite_l level left →
        ExternalBoundedIsSigmaFinite_l level right →
          ExternalBoundedIsSigmaFinite_l level (.conj left right)
    | disj {arity level : Nat} {left right : FOFormula arity} :
        ExternalBoundedIsSigmaFinite_l level left →
        ExternalBoundedIsSigmaFinite_l level right →
          ExternalBoundedIsSigmaFinite_l level (FOFormula.disj left right)
    | imp {arity level : Nat} {left right : FOFormula arity} :
        ExternalBoundedIsPiFinite_l level left →
        ExternalBoundedIsSigmaFinite_l level right →
          ExternalBoundedIsSigmaFinite_l level (FOFormula.imp left right)
    | ex {arity level : Nat} {body : FOFormula (arity + 1)} :
        ExternalBoundedIsSigmaFinite_l level body →
          ExternalBoundedIsSigmaFinite_l level (.ex body)
    | lift {arity level : Nat} {formula : FOFormula arity} :
        ExternalBoundedIsSigmaFinite_l level formula →
          ExternalBoundedIsSigmaFinite_l (level + 1) formula
    | ofPi {arity level : Nat} {formula : FOFormula arity} :
        ExternalBoundedIsPiFinite_l level formula →
          ExternalBoundedIsSigmaFinite_l (level + 1) formula

  /-- 保留真正有界底层的外部累积 `Pi` 分类。 -/
  inductive ExternalBoundedIsPiFinite_l :
      {arity : Nat} → Nat → FOFormula arity → Prop where
    | delta0 {arity level : Nat} (formula : Delta0Formula arity) :
        ExternalBoundedIsPiFinite_l level formula.toFO
    | neg {arity level : Nat} {body : FOFormula arity} :
        ExternalBoundedIsSigmaFinite_l level body →
          ExternalBoundedIsPiFinite_l level (.neg body)
    | conj {arity level : Nat} {left right : FOFormula arity} :
        ExternalBoundedIsPiFinite_l level left →
        ExternalBoundedIsPiFinite_l level right →
          ExternalBoundedIsPiFinite_l level (.conj left right)
    | disj {arity level : Nat} {left right : FOFormula arity} :
        ExternalBoundedIsPiFinite_l level left →
        ExternalBoundedIsPiFinite_l level right →
          ExternalBoundedIsPiFinite_l level (FOFormula.disj left right)
    | imp {arity level : Nat} {left right : FOFormula arity} :
        ExternalBoundedIsSigmaFinite_l level left →
        ExternalBoundedIsPiFinite_l level right →
          ExternalBoundedIsPiFinite_l level (FOFormula.imp left right)
    | all {arity level : Nat} {body : FOFormula (arity + 1)} :
        ExternalBoundedIsPiFinite_l level body →
          ExternalBoundedIsPiFinite_l level (FOFormula.all body)
    | lift {arity level : Nat} {formula : FOFormula arity} :
        ExternalBoundedIsPiFinite_l level formula →
          ExternalBoundedIsPiFinite_l (level + 1) formula
    | ofSigma {arity level : Nat} {formula : FOFormula arity} :
        ExternalBoundedIsSigmaFinite_l level formula →
          ExternalBoundedIsPiFinite_l (level + 1) formula
end

/-- 真正有界的外部 `Sigma` 层级对级别单调。 -/
theorem ExternalBoundedIsSigmaFinite_l.mono
    {arity lowerLevel upperLevel : Nat} {formula : FOFormula arity}
    (hFormula : ExternalBoundedIsSigmaFinite_l lowerLevel formula)
    (hLevels : lowerLevel ≤ upperLevel) :
    ExternalBoundedIsSigmaFinite_l upperLevel formula := by
  obtain ⟨difference, rfl⟩ := Nat.exists_eq_add_of_le hLevels
  induction difference with
  | zero => simpa using hFormula
  | succ difference ih =>
      have hPrior := ih (Nat.le_add_right lowerLevel difference)
      simpa [Nat.add_assoc] using
        ExternalBoundedIsSigmaFinite_l.lift hPrior

/-- 真正有界的外部 `Pi` 层级对级别单调。 -/
theorem ExternalBoundedIsPiFinite_l.mono
    {arity lowerLevel upperLevel : Nat} {formula : FOFormula arity}
    (hFormula : ExternalBoundedIsPiFinite_l lowerLevel formula)
    (hLevels : lowerLevel ≤ upperLevel) :
    ExternalBoundedIsPiFinite_l upperLevel formula := by
  obtain ⟨difference, rfl⟩ := Nat.exists_eq_add_of_le hLevels
  induction difference with
  | zero => simpa using hFormula
  | succ difference ih =>
      have hPrior := ih (Nat.le_add_right lowerLevel difference)
      simpa [Nat.add_assoc] using
        ExternalBoundedIsPiFinite_l.lift hPrior

/-- 变量重命名保持真正有界的外部 `Sigma` 层级。 -/
theorem ExternalBoundedIsSigmaFinite_l.rename
    {arity targetArity level : Nat} {formula : FOFormula arity}
    (hFormula : ExternalBoundedIsSigmaFinite_l level formula)
    (rename : Fin arity → Fin targetArity) :
    ExternalBoundedIsSigmaFinite_l level (formula.rename rename) := by
  exact ExternalBoundedIsSigmaFinite_l.rec
    (motive_1 := fun {arity} level formula _ =>
      ∀ {targetArity}, (rename : Fin arity → Fin targetArity) →
        ExternalBoundedIsSigmaFinite_l level (formula.rename rename))
    (motive_2 := fun {arity} level formula _ =>
      ∀ {targetArity}, (rename : Fin arity → Fin targetArity) →
        ExternalBoundedIsPiFinite_l level (formula.rename rename))
    (fun formula _ rename => by
      rw [← externalDelta0_toFO_rename_l]
      exact .delta0 (formula.rename rename))
    (fun _ hBody _ rename => .neg (hBody rename))
    (fun _ _ hLeft hRight _ rename =>
      .conj (hLeft rename) (hRight rename))
    (fun _ _ hLeft hRight _ rename =>
      .disj (hLeft rename) (hRight rename))
    (fun _ _ hLeft hRight _ rename =>
      .imp (hLeft rename) (hRight rename))
    (fun _ hBody _ rename => .ex (hBody (FOFormula.liftRename rename)))
    (fun _ hBody _ rename => .lift (hBody rename))
    (fun _ hBody _ rename => .ofPi (hBody rename))
    (fun formula _ rename => by
      rw [← externalDelta0_toFO_rename_l]
      exact .delta0 (formula.rename rename))
    (fun _ hBody _ rename => .neg (hBody rename))
    (fun _ _ hLeft hRight _ rename =>
      .conj (hLeft rename) (hRight rename))
    (fun _ _ hLeft hRight _ rename =>
      .disj (hLeft rename) (hRight rename))
    (fun _ _ hLeft hRight _ rename =>
      .imp (hLeft rename) (hRight rename))
    (fun _ hBody _ rename => .all (hBody (FOFormula.liftRename rename)))
    (fun _ hBody _ rename => .lift (hBody rename))
    (fun _ hBody _ rename => .ofSigma (hBody rename))
    hFormula rename

/-- 变量重命名保持真正有界的外部 `Pi` 层级。 -/
theorem ExternalBoundedIsPiFinite_l.rename
    {arity targetArity level : Nat} {formula : FOFormula arity}
    (hFormula : ExternalBoundedIsPiFinite_l level formula)
    (rename : Fin arity → Fin targetArity) :
    ExternalBoundedIsPiFinite_l level (formula.rename rename) := by
  exact ExternalBoundedIsPiFinite_l.rec
    (motive_1 := fun {arity} level formula _ =>
      ∀ {targetArity}, (rename : Fin arity → Fin targetArity) →
        ExternalBoundedIsSigmaFinite_l level (formula.rename rename))
    (motive_2 := fun {arity} level formula _ =>
      ∀ {targetArity}, (rename : Fin arity → Fin targetArity) →
        ExternalBoundedIsPiFinite_l level (formula.rename rename))
    (fun formula _ rename => by
      rw [← externalDelta0_toFO_rename_l]
      exact .delta0 (formula.rename rename))
    (fun _ hBody _ rename => .neg (hBody rename))
    (fun _ _ hLeft hRight _ rename =>
      .conj (hLeft rename) (hRight rename))
    (fun _ _ hLeft hRight _ rename =>
      .disj (hLeft rename) (hRight rename))
    (fun _ _ hLeft hRight _ rename =>
      .imp (hLeft rename) (hRight rename))
    (fun _ hBody _ rename => .ex (hBody (FOFormula.liftRename rename)))
    (fun _ hBody _ rename => .lift (hBody rename))
    (fun _ hBody _ rename => .ofPi (hBody rename))
    (fun formula _ rename => by
      rw [← externalDelta0_toFO_rename_l]
      exact .delta0 (formula.rename rename))
    (fun _ hBody _ rename => .neg (hBody rename))
    (fun _ _ hLeft hRight _ rename =>
      .conj (hLeft rename) (hRight rename))
    (fun _ _ hLeft hRight _ rename =>
      .disj (hLeft rename) (hRight rename))
    (fun _ _ hLeft hRight _ rename =>
      .imp (hLeft rename) (hRight rename))
    (fun _ hBody _ rename => .all (hBody (FOFormula.liftRename rename)))
    (fun _ hBody _ rename => .lift (hBody rename))
    (fun _ hBody _ rename => .ofSigma (hBody rename))
    hFormula rename

/-- 加入一个未使用的末变量保持真正有界的外部 `Sigma` 层级。 -/
theorem ExternalBoundedIsSigmaFinite_l.weaken_l
    {arity level : Nat} {formula : FOFormula arity}
    (hFormula : ExternalBoundedIsSigmaFinite_l level formula) :
    ExternalBoundedIsSigmaFinite_l level formula.weaken :=
  hFormula.rename Fin.castSucc

/-- 真正有界的外部 `Sigma` 证书翻译为新版内在类型语法的同层证书。 -/
theorem ExternalBoundedIsSigmaFinite_l.translate
    {arity level : Nat} {formula : FOFormula arity}
    (hFormula : ExternalBoundedIsSigmaFinite_l level formula) :
    FirstOrder.Formula.IsSigmaFinite membershipLevyBound level
      (translateExternalFormula formula) := by
  exact ExternalBoundedIsSigmaFinite_l.rec
    (motive_1 := fun {arity} level formula _ =>
      FirstOrder.Formula.IsSigmaFinite membershipLevyBound level
        (translateExternalFormula formula))
    (motive_2 := fun {arity} level formula _ =>
      FirstOrder.Formula.IsPiFinite membershipLevyBound level
        (translateExternalFormula formula))
    (fun formula => .delta0 (translateExternalDelta0_isDelta0_l formula))
    (fun _ hBody => .neg hBody)
    (fun _ _ hLeft hRight => .conj hLeft hRight)
    (fun _ _ hLeft hRight => by
      simpa only [FOFormula.disj, translateExternalFormula] using
        FirstOrder.Formula.IsSigmaFinite.neg
          (FirstOrder.Formula.IsPiFinite.conj
            (FirstOrder.Formula.IsPiFinite.neg hLeft)
            (FirstOrder.Formula.IsPiFinite.neg hRight)))
    (fun _ _ hLeft hRight => by
      simpa only [FOFormula.imp, FOFormula.disj, translateExternalFormula] using
        FirstOrder.Formula.IsSigmaFinite.neg
          (FirstOrder.Formula.IsPiFinite.conj
            (FirstOrder.Formula.IsPiFinite.neg
              (FirstOrder.Formula.IsSigmaFinite.neg hLeft))
            (FirstOrder.Formula.IsPiFinite.neg hRight)))
    (fun _ hBody => by
      simpa only [translateExternalFormula, externalBoundContext] using
        FirstOrder.Formula.IsSigmaFinite.existsE
          (ℬ := membershipLevyBound) SetTheory.SetSort.set hBody)
    (fun _ hBody => .lift hBody)
    (fun _ hBody => .ofPi hBody)
    (fun formula => .delta0 (translateExternalDelta0_isDelta0_l formula))
    (fun _ hBody => .neg hBody)
    (fun _ _ hLeft hRight => .conj hLeft hRight)
    (fun _ _ hLeft hRight => by
      simpa only [FOFormula.disj, translateExternalFormula] using
        FirstOrder.Formula.IsPiFinite.neg
          (FirstOrder.Formula.IsSigmaFinite.conj
            (FirstOrder.Formula.IsSigmaFinite.neg hLeft)
            (FirstOrder.Formula.IsSigmaFinite.neg hRight)))
    (fun _ _ hLeft hRight => by
      simpa only [FOFormula.imp, FOFormula.disj, translateExternalFormula] using
        FirstOrder.Formula.IsPiFinite.neg
          (FirstOrder.Formula.IsSigmaFinite.conj
            (FirstOrder.Formula.IsSigmaFinite.neg
              (FirstOrder.Formula.IsPiFinite.neg hLeft))
            (FirstOrder.Formula.IsSigmaFinite.neg hRight)))
    (fun _ hBody => by
      simpa only [FOFormula.all, translateExternalFormula,
          externalBoundContext] using
        FirstOrder.Formula.IsPiFinite.neg
          (ℬ := membershipLevyBound)
          (FirstOrder.Formula.IsSigmaFinite.existsE
            (ℬ := membershipLevyBound) SetTheory.SetSort.set
            (FirstOrder.Formula.IsSigmaFinite.neg
              (ℬ := membershipLevyBound) hBody)))
    (fun _ hBody => .lift hBody)
    (fun _ hBody => .ofSigma hBody)
    hFormula

/-- 真正有界的外部 `Pi` 证书翻译为新版内在类型语法的同层证书。 -/
theorem ExternalBoundedIsPiFinite_l.translate
    {arity level : Nat} {formula : FOFormula arity}
    (hFormula : ExternalBoundedIsPiFinite_l level formula) :
    FirstOrder.Formula.IsPiFinite membershipLevyBound level
      (translateExternalFormula formula) := by
  exact ExternalBoundedIsPiFinite_l.rec
    (motive_1 := fun {arity} level formula _ =>
      FirstOrder.Formula.IsSigmaFinite membershipLevyBound level
        (translateExternalFormula formula))
    (motive_2 := fun {arity} level formula _ =>
      FirstOrder.Formula.IsPiFinite membershipLevyBound level
        (translateExternalFormula formula))
    (fun formula => .delta0 (translateExternalDelta0_isDelta0_l formula))
    (fun _ hBody => .neg hBody)
    (fun _ _ hLeft hRight => .conj hLeft hRight)
    (fun _ _ hLeft hRight => by
      simpa only [FOFormula.disj, translateExternalFormula] using
        FirstOrder.Formula.IsSigmaFinite.neg
          (FirstOrder.Formula.IsPiFinite.conj
            (FirstOrder.Formula.IsPiFinite.neg hLeft)
            (FirstOrder.Formula.IsPiFinite.neg hRight)))
    (fun _ _ hLeft hRight => by
      simpa only [FOFormula.imp, FOFormula.disj, translateExternalFormula] using
        FirstOrder.Formula.IsSigmaFinite.neg
          (FirstOrder.Formula.IsPiFinite.conj
            (FirstOrder.Formula.IsPiFinite.neg
              (FirstOrder.Formula.IsSigmaFinite.neg hLeft))
            (FirstOrder.Formula.IsPiFinite.neg hRight)))
    (fun _ hBody => by
      simpa only [translateExternalFormula, externalBoundContext] using
        FirstOrder.Formula.IsSigmaFinite.existsE
          (ℬ := membershipLevyBound) SetTheory.SetSort.set hBody)
    (fun _ hBody => .lift hBody)
    (fun _ hBody => .ofPi hBody)
    (fun formula => .delta0 (translateExternalDelta0_isDelta0_l formula))
    (fun _ hBody => .neg hBody)
    (fun _ _ hLeft hRight => .conj hLeft hRight)
    (fun _ _ hLeft hRight => by
      simpa only [FOFormula.disj, translateExternalFormula] using
        FirstOrder.Formula.IsPiFinite.neg
          (FirstOrder.Formula.IsSigmaFinite.conj
            (FirstOrder.Formula.IsSigmaFinite.neg hLeft)
            (FirstOrder.Formula.IsSigmaFinite.neg hRight)))
    (fun _ _ hLeft hRight => by
      simpa only [FOFormula.imp, FOFormula.disj, translateExternalFormula] using
        FirstOrder.Formula.IsPiFinite.neg
          (FirstOrder.Formula.IsSigmaFinite.conj
            (FirstOrder.Formula.IsSigmaFinite.neg
              (FirstOrder.Formula.IsPiFinite.neg hLeft))
            (FirstOrder.Formula.IsSigmaFinite.neg hRight)))
    (fun _ hBody => by
      simpa only [FOFormula.all, translateExternalFormula,
          externalBoundContext] using
        FirstOrder.Formula.IsPiFinite.neg
          (ℬ := membershipLevyBound)
          (FirstOrder.Formula.IsSigmaFinite.existsE
            (ℬ := membershipLevyBound) SetTheory.SetSort.set
            (FirstOrder.Formula.IsSigmaFinite.neg
              (ℬ := membershipLevyBound) hBody)))
    (fun _ hBody => .lift hBody)
    (fun _ hBody => .ofSigma hBody)
    hFormula

end YesMetaZFC.BMS.ConstructibleBridge
