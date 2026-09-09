import BMSConstructibleBridge.FinalAssembly

/-!
# BMS 最终定理公理审计

`#guard_msgs` 将预期公理集合变成机器检查：最终定理一旦引入 `sorryAx`、
自定义公理或其他未列出的公理，本文件就无法通过编译。
-/

/--
info: 'YesMetaZFC.BMS.ConstructibleBridge.bm4_strictWellOrder_l' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms YesMetaZFC.BMS.ConstructibleBridge.bm4_strictWellOrder_l

/--
info: 'YesMetaZFC.BMS.ConstructibleBridge.bm4_no_infinite_descent_l' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms YesMetaZFC.BMS.ConstructibleBridge.bm4_no_infinite_descent_l
