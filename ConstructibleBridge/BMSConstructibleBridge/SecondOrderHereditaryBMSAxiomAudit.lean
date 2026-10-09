import BMSConstructibleBridge.SecondOrderHereditaryBMSWellOrder

/-! # 原 Z₂ 固定高度 BMS 最终接口的机器公理审计

只检查最终原闭句推导和任意原模型真值的实际声明依赖。
这里不是样本实例核验，也不改变原 ZFC 终局的旧审计接口。
新增公理、sorryAx 或未经列明的可信依赖会使本模块构建失败。
-/

/--
info: 'YesMetaZFC.BMS.ConstructibleBridge.SecondOrderHereditaryBMSWellOrder.models_l' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderHereditaryBMSWellOrder.models_l

/--
info: 'YesMetaZFC.BMS.ConstructibleBridge.SecondOrderHereditaryBMSWellOrder.derives_m' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms YesMetaZFC.BMS.ConstructibleBridge.SecondOrderHereditaryBMSWellOrder.derives_m
