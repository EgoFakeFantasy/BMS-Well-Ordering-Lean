import BMSConstructibleBridge.PowerlessCanonicalIndexAbsolute
import BMSConstructibleBridge.SecondOrderRowOrderCanonical

/-! # 完整模型中的规范指标唯一性及原 Z₂ 推导

唯一性量词不带相对类守卫。辅助比较图只比较读值；最终图还须具有
无垃圾成员规格。本文件证明唯一性条件句，不宣称无条件存在或最终 BMS 句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalIndexUnique

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeClassSatisfactionIndexCanonical (spec_l proper_l lex_congr_l)
open PowerlessCanonicalIndexSyntax (spec_m spec_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem proper_unique_l {R S : type_l hℳ} (hR : proper_l (ℳ₀ := 𝒱) R)
    (hS : proper_l (ℳ₀ := 𝒱) S)
    (hRead : ∀ x y, value_l (ℳ := 𝒱) R x y ↔ value_l (ℳ := 𝒱) S x y) : R = S := by
  have transfer {P Q : type_l hℳ} (hP : proper_l (ℳ₀ := 𝒱) P)
      (h : ∀ x y, value_l (ℳ := 𝒱) P x y ↔ value_l (ℳ := 𝒱) Q x y)
      (p : type_l hℳ) (hp : mem_l hℳ p P) : mem_l hℳ p Q := by
    obtain ⟨x, y, hxy⟩ := hP p hp
    obtain ⟨q, hq, hPair⟩ := (h x y).mp ⟨p, hp, hxy⟩
    have hEq : q = p := SecondOrderPairObjects.ordered_unique_l hℳ hPair hxy
    exact hEq ▸ hq
  exact SecondOrderQuotient.ext_l hℳ R S
    (fun p => ⟨transfer hR hRead p, transfer hS (fun x y => (hRead x y).symm) p⟩)

theorem unique_l {ω A P S I J U S' I' J' U' : type_l hℳ}
    (h : spec_l (ℳ₀ := 𝒱) ω A P S I J U) (h' : spec_l (ℳ₀ := 𝒱) ω A P S' I' J' U') :
    S = S' ∧ I = I' ∧ J = J' ∧ U = U' := by
  obtain ⟨hS, hI, hJ, hProper, N, T, K, hN, hT, hK, hU⟩ := h
  obtain ⟨hS', hI', hJ', hProper', N', T', K', hN', hT', hK', hU'⟩ := h'
  have hSEq : S' = S := SecondOrderQuotient.ext_l hℳ S' S (fun f => (hS' f).trans (hS f).symm)
  subst S'
  have hIEq : I' = I := SecondOrderQuotient.ext_l hℳ I' I (fun p => (hI' p).trans (hI p).symm)
  subst I'
  have hJEq : J' = J := SecondOrderQuotient.ext_l hℳ J' J (fun p => (hJ' p).trans (hJ p).symm)
  subst J'
  have hNValues x y := (hN x y).trans (hN' x y).symm
  have hTValues f g := (hT f g).trans (hT' f g).symm
  have hKValues p q := (hK p q).trans ((lex_congr_l hNValues hTValues p q).trans (hK' p q).symm)
  have hUValues p q := (hU p q).trans ((lex_congr_l hNValues hKValues p q).trans (hU' p q).symm)
  exact ⟨rfl, rfl, rfl, proper_unique_l hProper hProper' hUValues⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def unique_m {Γ Δ : SortContext ℒ} (ω A P S I J U : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
  .imp (spec_m ω A P S I J U) <|
    .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
      .imp (spec_m (w ω) (w A) (w P) (.bvar (.there (.there (.there .here))))
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)) <|
        .conj (.equal (w S) (.bvar (.there (.there (.there .here))))) <|
          .conj (.equal (w I) (.bvar (.there (.there .here)))) <|
            .conj (.equal (w J) (.bvar (.there .here))) (.equal (w U) (.bvar .here))

theorem unique_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω A P S I J U : Term ℒ Γ Δ .set) :
    (unique_m ω A P S I J U).satisfies η ↔
      (spec_l (ω.eval η) (A.eval η) (P.eval η) (S.eval η) (I.eval η) (J.eval η) (U.eval η) →
        ∀ S' I' J' U', spec_l (ω.eval η) (A.eval η) (P.eval η) S' I' J' U' →
          S.eval η = S' ∧ I.eval η = I' ∧ J.eval η = J' ∧ U.eval η = U') := by
  simp only [unique_m, Formula.satisfies, spec_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
  unique_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, unique_formula_l]
  exact fun h _ _ _ _ h' => unique_l (hℳ := hℳ) h h'

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalIndexUnique
