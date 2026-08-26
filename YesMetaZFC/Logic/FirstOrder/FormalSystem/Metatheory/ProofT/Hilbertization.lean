import YesMetaZFC.Logic.FirstOrder.Hilbert.Hilbertization
import YesMetaZFC.Logic.FirstOrder.Hilbert.Adequacy
import YesMetaZFC.Logic.FirstOrder.Derivation.Consistency

/-!
# Hilbert 化理论的一致性反射

本模块把已有的公式 Hilbert 化严格等价与二次理论压平组合起来。若 Hilbert 化理论
在自然演绎中推出原生假式，则原理论也推出原生假式；全程只使用证明翻译，不经过
模型、完备性或选择。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace Hilbertization

universe u v w

set_option autoImplicit false

variable
  {σ : Signature.{u, v, w}}
  [DecidableEq σ.SortSymbol]

/-- Hilbert 化理论中的自然演绎矛盾可回传到原理论。 -/
theorem derives_falsum
    {anchorSort : σ.SortSymbol}
    {T : Theory σ}
    (h :
      Derives (Theory.hilbertize anchorSort T) []
        Formula.falsum) :
    Derives T [] Formula.falsum := by
  have hEncoded :=
    h.to_hilbert anchorSort
  have hCollapsed :
      HilbertDerives
        (Theory.hilbertize anchorSort T)
        (Formula.hilbert_falsum anchorSort) := by
    exact hEncoded.theory_weakening <| by
      simpa [Theory.hilbertize_context] using
        (Theory.hilbertize_hilbertize_context_subset
          (anchorSort := anchorSort)
          (theory := T) (context := []))
  have hRawEncoded :
      Derives T []
        (Formula.hilbert_falsum anchorSort) := by
    apply hCollapsed.interpret_m
    intro encoded hEncoded hAdmissible
    rcases hEncoded with
      ⟨source, hSource, rfl⟩
    have hSourceAdmissible :
        Formula.Admissible source :=
      Formula.Admissible.hilbertize_source
        hAdmissible
    have hSourceDerives :
        Derives T [] source :=
      .theoryAxiom hSource
        (Formula.check_admissible_complete
          hSourceAdmissible)
    exact
      (DerivationEquivalent.hilbertize
        anchorSort source hSourceAdmissible).forward.imp_elim
          hSourceDerives
  exact
    (DerivationEquivalent.Encoding.falsum_hilbert
      (theory := T) (context := [])
      anchorSort).backward.imp_elim hRawEncoded

/-- 原理论一致则其 Hilbert 化理论仍一致。 -/
theorem consistent
    {anchorSort : σ.SortSymbol}
    {T : Theory σ}
    (hT : Derives.Consistent T []) :
    Derives.Consistent
      (Theory.hilbertize anchorSort T) [] := by
  intro hEncoded
  exact hT (derives_falsum hEncoded)

end Hilbertization
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
