/-!
# 证明无关的 checker 封印

`CheckerSeal check input` 的类型同时固定 checker 函数与具体输入；其唯一逻辑内容是
最终布尔判定为真。由于该结构位于 `Prop`，下游可以只传播封印，而不携带生成真值时的
大型证明树。
-/

namespace YesMetaZFC
namespace Automation

/--
绑定 checker、输入与最终真值的证明无关接口。

这里不保存字符串形式的函数名或外部成功标志；checker 本身是类型索引，因此无法把一个
checker 的成功结果挪作另一个 checker 使用。
-/
structure CheckerSeal {α : Sort u} (check : α → Bool) (input : α) : Prop where
  private mkInternal ::
  checked : check input = true

namespace CheckerSeal

/-- 由内核已经核验的 checker 真值建立封印。 -/
theorem ofTrue {α : Sort u} {check : α → Bool} {input : α}
    (checked : check input = true) : CheckerSeal check input :=
  ⟨checked⟩

end CheckerSeal
end Automation
end YesMetaZFC
