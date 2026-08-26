import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFC
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.InternalEncodingChain

/-!
# ZFC 内部支持理论的函数图消去实例

本模块把通用 `InternalEncodingChain` 实例化到嵌入后的 ZFC 基础理论。当前已有
真实图实例的十二类函数符号全部从一致性前提逐层移除；尚未建立图实例的递归算术、
关系投影与有限序列函数仍显式保留在 `support_reduct_theory` 中。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFC
namespace SupportElimination

open Nonlogical.BasicSetTheory

set_option autoImplicit false

private abbrev project_zfc : FsProjectTheory :=
  _root_.YesMetaZFC.SetTheory.ZFC

private theorem project_base_sentence
    {φ : SetFormula}
    (hφ :
      fs_project_base_theory project_zfc φ) :
    Formula.Sentence φ :=
  fs_project_base_theory_sentence hφ

/--
当前函数图基础设施全部应用后得到的 ZFC 内部支持理论。

该理论是可继续施工的明确中间边界，不声称已经等于裸 ZFC。
-/
def support_reduct_theory : SetTheory :=
  FunctionGraphElimination.InternalEncodingChain.reduct_theory
    (fs_project_base_theory project_zfc)
    project_base_sentence

/-! ## 任意公式的证明级消去 -/

/-- ZFC raw 支撑理论的当前函数图组合编译。 -/
def compile_formula (φ : SetFormula) : SetFormula :=
  FunctionGraphElimination.InternalEncodingChain.compile_formula
    φ

/-- ZFC raw 支撑理论中的任意 checked 闭证明可翻译到关系化支持理论。 -/
theorem derives
    {φ : SetFormula}
    (h :
      Derives fs_zfc_support_raw_theory [] φ) :
    Derives support_reduct_theory [] (compile_formula φ) := by
  have hRaw :
      Derives
        (fs_internal_raw_theory
          (fs_project_base_theory project_zfc)) [] φ := by
    simpa [fs_zfc_support_raw_theory,
      fs_internal_project_raw_theory] using h
  have hCompiled :=
    FunctionGraphElimination.InternalEncodingChain.derives
      (fs_project_base_theory project_zfc)
      project_base_sentence hRaw
  simpa [compile_formula, support_reduct_theory] using hCompiled

/--
ZFC raw 支持理论中的 checked 矛盾可回传到当前关系化支持理论。
-/
theorem support_raw_derives_falsum
    (h :
      Derives fs_zfc_support_raw_theory []
        Formula.falsum) :
    Derives support_reduct_theory []
      Formula.falsum := by
  simpa [compile_formula,
    FunctionGraphElimination.InternalEncodingChain.compile_formula,
    FunctionGraphElimination.formula] using
    derives (φ := Formula.falsum) h

/--
当前关系化支持理论一致时，原 ZFC raw 支持理论保持 checked 一致。
-/
theorem support_raw_consistent
    (h :
      Derives.Consistent
        support_reduct_theory []) :
    Derives.Consistent
      fs_zfc_support_raw_theory [] := by
  intro hRaw
  exact h (support_raw_derives_falsum hRaw)

end SupportElimination
end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
