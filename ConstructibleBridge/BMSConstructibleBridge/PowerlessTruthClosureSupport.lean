import BMSConstructibleBridge.PowerlessTruthClosure
import BMSConstructibleBridge.PowerlessFiniteSupport
import YesMetaZFC.Automation.ModelClosure

/-!
# 证书收集闭句的有限核心支持

先对原纯检查公式证明收集闭句，再取得实际 Hilbert 推导及其有限公理列表。
满足该列表的小结构获得原闭句，不要求它满足完整核心。
尚未证明指定可构造层满足此列表；不能将有限支持的存在当作反射完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthClosureSupport

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

def collection_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  let v (s : Term ℒ Γ Δ .set) := (q s).weakenBound SetTheory.SetSort.set
  .imp
    (.forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (q A))
      (.existsE .set (.conj
        (PowerlessTruthCertificate.certificate_m (v ω) (v e) (v T) (v t₁) (v t₂) (v t₃) (.bvar .here))
        (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here))))))
    (.existsE .set (.conj
      (PowerlessTruthCertificate.certificate_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (.bvar .here))
      (ThirdOrderTheory.subset_m (q A) (.bvar .here))))

theorem collection_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ A : Term ℒ Γ Δ .set) :
    (collection_m ω e T t₁ t₂ t₃ A).satisfies η := by
  simp only [collection_m, Formula.satisfies, PowerlessTruthClosure.certificate_formula_l hℳ,
    subset_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  exact PowerlessTruthClosure.collect_l hℳ

def formula_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
  collection_m (.fvar .here) (.fvar (.there .here))
    (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close formula_m

theorem sentence_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : sentence_m.TrueIn ℳ := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff formula_m).mpr
  intro η
  exact collection_l hℳ η _ _ _ _ _ _ _

theorem finite_m : Nonempty (Derives.FiniteTheorySupport PowerlessTheory.theory_m [] sentence_m) :=
  PowerlessFiniteSupport.finite_m (fun _ hℳ => sentence_l hℳ)

noncomputable def support_m : Derives.FiniteTheorySupport PowerlessTheory.theory_m [] sentence_m :=
  Classical.choice finite_m

def theory_m : Theory ℒ := Theory.ofList support_m.sentences

theorem core_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : Theory.Models ℳ theory_m :=
  fun φ hφ => hℳ φ (support_m.subset φ hφ)

/-- 小结构只需满足实际有限支持，即可使用原检查公式的证书收集闭句。 -/
theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ theory_m) : sentence_m.TrueIn ℳ :=
  support_m.derivation.semantically_entails ℳ hℳ

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthClosureSupport
