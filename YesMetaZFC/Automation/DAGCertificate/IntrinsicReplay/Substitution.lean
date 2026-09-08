import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay.Core
import YesMetaZFC.Automation.DAGCertificate.CompileSubstitution

/-!
# 内在字句替换语义

源字句的全称有效性允许把任意目标赋值沿 typed substitution 拉回，因此 raw 字句替换
不再需要 bound-closed、well-sorted 或 admissible 语义桥。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace Compile

open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder

universe x

variable {σ : Signature}

/-- 全称有效的开公式在任意 typed free substitution 下仍全称有效。 -/
theorem universallyValid_substituteFree
    {M : Structure.{0, 0, 0, x} σ}
    {free : SortContext σ} {formula : OpenFormula σ free}
    (hValid : UniversallyValid M formula)
    (substitution : VariableSubstitution σ free [] free) :
    UniversallyValid M (formula.substituteFree substitution) := by
  intro assignment
  apply (Formula.satisfies_substituteFree
    (openEnv assignment) substitution formula).mpr
  let pulledAssignment : Assignment M free :=
    fun entry => (substitution entry).eval (openEnv assignment)
  have hPulled := hValid pulledAssignment
  have hEnv :
      openEnv pulledAssignment =
        (openEnv assignment).pullback
          (Substitution.free_map substitution) := by
    apply Env.ext
    · intro sort entry
      cases entry
    · intro sort entry
      rfl
  rw [← hEnv]
  exact hPulled

/-- raw 替换关系把源 compiled clause 的全称真实性传给目标。 -/
theorem CompiledClause.trueIn_applySubstitution
    [DecidableEq σ.SortSymbol]
    (M : Structure.{0, 0, 0, x} σ)
    {registry : FreeRegistry σ}
    (source targetClause : CompiledClause registry)
    (rawSubstitution : TermSubstitution σ)
    {substitution : VariableSubstitution σ
      registry.context [] registry.context}
    (hCompile : compileSubstitution? registry rawSubstitution =
      @some (VariableSubstitution σ
        registry.context [] registry.context) substitution)
    (hRaw : targetClause.raw =
      source.raw.applySubstitution rawSubstitution)
    (hSource : source.TrueIn M) :
    targetClause.TrueIn M := by
  apply (forallFree_trueIn_iff targetClause.formula).mpr
  rw [source.formula_eq_substituteFree targetClause rawSubstitution
    hCompile hRaw]
  apply universallyValid_substituteFree
  exact (forallFree_trueIn_iff source.formula).mp hSource

end Compile
end DAGCertificate
end Automation
end YesMetaZFC
