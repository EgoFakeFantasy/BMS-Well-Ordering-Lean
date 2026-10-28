import BMSConstructibleBridge.PowerlessRelativeFiniteHullCodedCoverage

/-! # 同一 I 的见证与 W 中完整资格的对象公式

纯隶属 ℒ 中的十七个见证都受同一个 I 的隶属守卫限制，完整点矩阵
另相对化到 W；域 W 不须属于自身，I 不须传递或外延。精确语义保留
完整静态、Sat、Def、旧数字读数、序数、历史和全部有限赋值覆盖。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedHistoryCaptureSyntax

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev context_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set]

private def body_m : Formula ℒ [] context_m :=
  PowerlessCodedHistoryCoverageSyntax.point_m
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar (.there (.there (.there (.there (.there (.there .here))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))

private def assignment_m {Γ Δ : SortContext ℒ}
    (B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : Term ℒ Γ Δ .set) :
    Variable context_m SetTheory.SetSort.set → Term ℒ Γ Δ .set
  | .here => B
  | (.there .here) => ω
  | (.there (.there .here)) => x
  | (.there (.there (.there .here))) => a
  | (.there (.there (.there (.there .here)))) => y
  | (.there (.there (.there (.there (.there .here))))) => A
  | (.there (.there (.there (.there (.there (.there .here)))))) => U
  | (.there (.there (.there (.there (.there (.there (.there .here))))))) => D
  | (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) => f
  | (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) => e
  | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) => t₁
  | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) => t₂
  | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) => t₃
  | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) => t₄
  | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) => P
  | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) => N
  | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) => F
  | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) => V
  | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) => Q
  | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) => G

def point_m {Γ Δ : SortContext ℒ}
    (W B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : Term ℒ Γ Δ .set) :
    Formula ℒ Γ Δ :=
  PowerlessRelativeParameters.instance_m body_m W
    (assignment_m B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G)

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₁₇ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up t))))))))))))))))

def formula_m {Γ Δ : SortContext ℒ} (I W B ω x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  let G : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
  let Q := (.bvar (.there .here))
  let V := (.bvar (.there (.there .here)))
  let F := (.bvar (.there (.there (.there .here))))
  let N := (.bvar (.there (.there (.there (.there .here)))))
  let P := (.bvar (.there (.there (.there (.there (.there .here))))))
  let t₄ := (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
  let t₃ := (.bvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let t₂ := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
  let t₁ := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
  let e := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
  let f := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
  let D := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))
  let U := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))
  let A := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))
  let y := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))
  let a := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))
  .conj (member_m a (up₁₇ I)) <|
  .conj (member_m y (up₁₇ I)) <|
  .conj (member_m A (up₁₇ I)) <|
  .conj (member_m U (up₁₇ I)) <|
  .conj (member_m D (up₁₇ I)) <|
  .conj (member_m f (up₁₇ I)) <|
  .conj (member_m e (up₁₇ I)) <|
  .conj (member_m t₁ (up₁₇ I)) <|
  .conj (member_m t₂ (up₁₇ I)) <|
  .conj (member_m t₃ (up₁₇ I)) <|
  .conj (member_m t₄ (up₁₇ I)) <|
  .conj (member_m P (up₁₇ I)) <|
  .conj (member_m N (up₁₇ I)) <|
  .conj (member_m F (up₁₇ I)) <|
  .conj (member_m V (up₁₇ I)) <|
  .conj (member_m Q (up₁₇ I)) <|
  .conj (member_m G (up₁₇ I)) <|
  point_m (up₁₇ W) (up₁₇ B) (up₁₇ ω) (up₁₇ x) a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {I₀ W₀ : carrier_l ℳ} {hI : ∃ z, member_l ℳ z I₀}
  {hW : ∃ z, member_l ℳ z W₀}

local notation "𝒲" => structure_l (ℳ := ℳ) W₀ hW

private theorem point_read_l {Γ Δ : SortContext ℒ} (ζ : Env ℳ Γ Δ)
    (W B ω x : Term ℒ Γ Δ .set)
    (hIW : subset_l (ℳ := ℳ) I₀ W₀) (hW₀ : W.eval ζ = W₀)
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒲))
    (B₀ ω₀ x₀ : type_l (ℳ := ℳ) I₀)
    (hB : B.eval ζ = B₀.val) (hω : ω.eval ζ = ω₀.val) (hx : x.eval ζ = x₀.val)
    (a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : type_l (ℳ := ℳ) I₀) :
    (point_m (up₁₇ W)
    (up₁₇ B) (up₁₇ ω) (up₁₇ x) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.bvar (.there (.there (.there (.there (.there (.there .here))))))) (.bvar (.there (.there (.there (.there (.there .here))))))
    (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).satisfies (ζ |>.pushBound (sort := SetTheory.SetSort.set) a.val |>.pushBound (sort := SetTheory.SetSort.set) y.val |>.pushBound (sort := SetTheory.SetSort.set) A.val |>.pushBound (sort := SetTheory.SetSort.set) U.val |>.pushBound (sort := SetTheory.SetSort.set) D.val |>.pushBound (sort := SetTheory.SetSort.set) f.val |>.pushBound (sort := SetTheory.SetSort.set) e.val |>.pushBound (sort := SetTheory.SetSort.set) t₁.val |>.pushBound (sort := SetTheory.SetSort.set) t₂.val |>.pushBound (sort := SetTheory.SetSort.set) t₃.val |>.pushBound (sort := SetTheory.SetSort.set) t₄.val |>.pushBound (sort := SetTheory.SetSort.set) P.val |>.pushBound (sort := SetTheory.SetSort.set) N.val |>.pushBound (sort := SetTheory.SetSort.set) F.val |>.pushBound (sort := SetTheory.SetSort.set) V.val |>.pushBound (sort := SetTheory.SetSort.set) Q.val |>.pushBound (sort := SetTheory.SetSort.set) G.val) ↔
      PowerlessCodedHistoryCoverageSyntax.point_l (𝒩 := 𝒲)
      (PowerlessSourceInclusion.inclusion_l hIW B₀) (PowerlessSourceInclusion.inclusion_l hIW ω₀) (PowerlessSourceInclusion.inclusion_l hIW x₀) (PowerlessSourceInclusion.inclusion_l hIW a) (PowerlessSourceInclusion.inclusion_l hIW y)
      (PowerlessSourceInclusion.inclusion_l hIW A) (PowerlessSourceInclusion.inclusion_l hIW U) (PowerlessSourceInclusion.inclusion_l hIW D) (PowerlessSourceInclusion.inclusion_l hIW f) (PowerlessSourceInclusion.inclusion_l hIW e)
      (PowerlessSourceInclusion.inclusion_l hIW t₁) (PowerlessSourceInclusion.inclusion_l hIW t₂) (PowerlessSourceInclusion.inclusion_l hIW t₃) (PowerlessSourceInclusion.inclusion_l hIW t₄) (PowerlessSourceInclusion.inclusion_l hIW P)
      (PowerlessSourceInclusion.inclusion_l hIW N) (PowerlessSourceInclusion.inclusion_l hIW F) (PowerlessSourceInclusion.inclusion_l hIW V) (PowerlessSourceInclusion.inclusion_l hIW Q) (PowerlessSourceInclusion.inclusion_l hIW G) := by
  let ν : Env 𝒲 [] context_m := Env.empty |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW G) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW Q) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW V) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW F) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW N) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW P) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW t₄) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW t₃) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW t₂) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW t₁) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW e) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW f) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW D) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW U) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW A) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW y) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW a) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW x₀) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW ω₀) |>.pushFree (PowerlessSourceInclusion.inclusion_l hIW B₀)
  have hRead := PowerlessRelativeParameters.instance_l body_m (ζ |>.pushBound (sort := SetTheory.SetSort.set) a.val |>.pushBound (sort := SetTheory.SetSort.set) y.val |>.pushBound (sort := SetTheory.SetSort.set) A.val |>.pushBound (sort := SetTheory.SetSort.set) U.val |>.pushBound (sort := SetTheory.SetSort.set) D.val |>.pushBound (sort := SetTheory.SetSort.set) f.val |>.pushBound (sort := SetTheory.SetSort.set) e.val |>.pushBound (sort := SetTheory.SetSort.set) t₁.val |>.pushBound (sort := SetTheory.SetSort.set) t₂.val |>.pushBound (sort := SetTheory.SetSort.set) t₃.val |>.pushBound (sort := SetTheory.SetSort.set) t₄.val |>.pushBound (sort := SetTheory.SetSort.set) P.val |>.pushBound (sort := SetTheory.SetSort.set) N.val |>.pushBound (sort := SetTheory.SetSort.set) F.val |>.pushBound (sort := SetTheory.SetSort.set) V.val |>.pushBound (sort := SetTheory.SetSort.set) Q.val |>.pushBound (sort := SetTheory.SetSort.set) G.val)
    (up₁₇ W) (assignment_m
    (up₁₇ B) (up₁₇ ω) (up₁₇ x) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.bvar (.there (.there (.there (.there (.there (.there .here))))))) (.bvar (.there (.there (.there (.there (.there .here))))))
    (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)) ν (by simpa only [up₁₇, up, Term.eval_weakenBound] using hW₀) (by
    intro v
    match v with
    | .here =>
      rw [show (ν.freeVal (.here : Variable context_m .set)).val = B₀.val from rfl]
      simpa only [assignment_m, up₁₇, up, Term.eval_weakenBound] using hB
    | (.there .here) =>
      rw [show (ν.freeVal ((.there .here) : Variable context_m .set)).val = ω₀.val from rfl]
      simpa only [assignment_m, up₁₇, up, Term.eval_weakenBound] using hω
    | (.there (.there .here)) =>
      rw [show (ν.freeVal ((.there (.there .here)) : Variable context_m .set)).val = x₀.val from rfl]
      simpa only [assignment_m, up₁₇, up, Term.eval_weakenBound] using hx
    | (.there (.there (.there .here))) => rfl
    | (.there (.there (.there (.there .here)))) => rfl
    | (.there (.there (.there (.there (.there .here))))) => rfl
    | (.there (.there (.there (.there (.there (.there .here)))))) => rfl
    | (.there (.there (.there (.there (.there (.there (.there .here))))))) => rfl
    | (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) => rfl
    | (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) => rfl
    | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) => rfl
    | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) => rfl
    | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) => rfl
    | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) => rfl
    | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) => rfl
    | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) => rfl
    | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) => rfl
    | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) => rfl
    | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) => rfl
    | (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) => rfl)
  simpa only [ν, Term.eval, Env.pushFree_here, Env.pushFree_there, point_m] using
    hRead.trans (PowerlessCodedHistoryCoverageSyntax.point_formula_l hExt ν
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar (.there (.there (.there (.there (.there (.there .here))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))

/-- 精确对应同一 I 内见证以及同一 MemberW 中的完整资格。 -/
theorem formula_l {Γ Δ : SortContext ℒ} (ζ : Env ℳ Γ Δ)
    (I W B ω x : Term ℒ Γ Δ .set)
    (hIW : subset_l (ℳ := ℳ) I₀ W₀) (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒲))
    (B₀ ω₀ x₀ : type_l (ℳ := ℳ) I₀)
    (hB : B.eval ζ = B₀.val) (hω : ω.eval ζ = ω₀.val) (hx : x.eval ζ = x₀.val) :
    (formula_m I W B ω x).satisfies ζ ↔
      ∃ a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : type_l (ℳ := ℳ) I₀,
        PowerlessCodedHistoryCoverageSyntax.point_l (𝒩 := 𝒲)
      (PowerlessSourceInclusion.inclusion_l hIW B₀) (PowerlessSourceInclusion.inclusion_l hIW ω₀) (PowerlessSourceInclusion.inclusion_l hIW x₀) (PowerlessSourceInclusion.inclusion_l hIW a) (PowerlessSourceInclusion.inclusion_l hIW y)
      (PowerlessSourceInclusion.inclusion_l hIW A) (PowerlessSourceInclusion.inclusion_l hIW U) (PowerlessSourceInclusion.inclusion_l hIW D) (PowerlessSourceInclusion.inclusion_l hIW f) (PowerlessSourceInclusion.inclusion_l hIW e)
      (PowerlessSourceInclusion.inclusion_l hIW t₁) (PowerlessSourceInclusion.inclusion_l hIW t₂) (PowerlessSourceInclusion.inclusion_l hIW t₃) (PowerlessSourceInclusion.inclusion_l hIW t₄) (PowerlessSourceInclusion.inclusion_l hIW P)
      (PowerlessSourceInclusion.inclusion_l hIW N) (PowerlessSourceInclusion.inclusion_l hIW F) (PowerlessSourceInclusion.inclusion_l hIW V) (PowerlessSourceInclusion.inclusion_l hIW Q) (PowerlessSourceInclusion.inclusion_l hIW G) := by
  unfold formula_m
  simp only [Formula.satisfies, member_m, Arguments.eval, up₁₇, up,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  change (∃ a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : carrier_l ℳ,
      member_l ℳ a (I.eval ζ) ∧
      member_l ℳ y (I.eval ζ) ∧
      member_l ℳ A (I.eval ζ) ∧
      member_l ℳ U (I.eval ζ) ∧
      member_l ℳ D (I.eval ζ) ∧
      member_l ℳ f (I.eval ζ) ∧
      member_l ℳ e (I.eval ζ) ∧
      member_l ℳ t₁ (I.eval ζ) ∧
      member_l ℳ t₂ (I.eval ζ) ∧
      member_l ℳ t₃ (I.eval ζ) ∧
      member_l ℳ t₄ (I.eval ζ) ∧
      member_l ℳ P (I.eval ζ) ∧
      member_l ℳ N (I.eval ζ) ∧
      member_l ℳ F (I.eval ζ) ∧
      member_l ℳ V (I.eval ζ) ∧
      member_l ℳ Q (I.eval ζ) ∧
      member_l ℳ G (I.eval ζ) ∧
      (point_m (up₁₇ W)
    (up₁₇ B) (up₁₇ ω) (up₁₇ x) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.bvar (.there (.there (.there (.there (.there (.there .here))))))) (.bvar (.there (.there (.there (.there (.there .here))))))
    (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).satisfies (ζ |>.pushBound (sort := SetTheory.SetSort.set) a |>.pushBound (sort := SetTheory.SetSort.set) y |>.pushBound (sort := SetTheory.SetSort.set) A |>.pushBound (sort := SetTheory.SetSort.set) U |>.pushBound (sort := SetTheory.SetSort.set) D |>.pushBound (sort := SetTheory.SetSort.set) f |>.pushBound (sort := SetTheory.SetSort.set) e |>.pushBound (sort := SetTheory.SetSort.set) t₁ |>.pushBound (sort := SetTheory.SetSort.set) t₂ |>.pushBound (sort := SetTheory.SetSort.set) t₃ |>.pushBound (sort := SetTheory.SetSort.set) t₄ |>.pushBound (sort := SetTheory.SetSort.set) P |>.pushBound (sort := SetTheory.SetSort.set) N |>.pushBound (sort := SetTheory.SetSort.set) F |>.pushBound (sort := SetTheory.SetSort.set) V |>.pushBound (sort := SetTheory.SetSort.set) Q |>.pushBound (sort := SetTheory.SetSort.set) G)) ↔ _
  constructor
  · rintro ⟨a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G, ha, hy, hA, hU, hD, hf, he, ht₁, ht₂, ht₃, ht₄, hP, hN, hF, hV, hQ, hG, hPoint⟩
    rw [hI₀] at ha hy hA hU hD hf he ht₁ ht₂ ht₃ ht₄ hP hN hF hV hQ hG
    refine ⟨⟨a, ha⟩, ⟨y, hy⟩, ⟨A, hA⟩, ⟨U, hU⟩, ⟨D, hD⟩, ⟨f, hf⟩, ⟨e, he⟩, ⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩, ⟨t₃, ht₃⟩, ⟨t₄, ht₄⟩, ⟨P, hP⟩, ⟨N, hN⟩, ⟨F, hF⟩, ⟨V, hV⟩, ⟨Q, hQ⟩, ⟨G, hG⟩, ?_⟩
    exact (point_read_l ζ W B ω x hIW hW₀ hExt B₀ ω₀ x₀ hB hω hx
      ⟨a, ha⟩ ⟨y, hy⟩ ⟨A, hA⟩ ⟨U, hU⟩ ⟨D, hD⟩ ⟨f, hf⟩ ⟨e, he⟩ ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ ⟨t₃, ht₃⟩ ⟨t₄, ht₄⟩ ⟨P, hP⟩ ⟨N, hN⟩ ⟨F, hF⟩ ⟨V, hV⟩ ⟨Q, hQ⟩ ⟨G, hG⟩).mp hPoint
  · rintro ⟨a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G, hPoint⟩
    refine ⟨a.val, y.val, A.val, U.val, D.val, f.val, e.val, t₁.val, t₂.val, t₃.val, t₄.val, P.val, N.val, F.val, V.val, Q.val, G.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hI₀]; exact a.property
    · rw [hI₀]; exact y.property
    · rw [hI₀]; exact A.property
    · rw [hI₀]; exact U.property
    · rw [hI₀]; exact D.property
    · rw [hI₀]; exact f.property
    · rw [hI₀]; exact e.property
    · rw [hI₀]; exact t₁.property
    · rw [hI₀]; exact t₂.property
    · rw [hI₀]; exact t₃.property
    · rw [hI₀]; exact t₄.property
    · rw [hI₀]; exact P.property
    · rw [hI₀]; exact N.property
    · rw [hI₀]; exact F.property
    · rw [hI₀]; exact V.property
    · rw [hI₀]; exact Q.property
    · rw [hI₀]; exact G.property
    · exact (point_read_l ζ W B ω x hIW hW₀ hExt B₀ ω₀ x₀ hB hω hx
        a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G).mpr hPoint

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedHistoryCaptureSyntax
