(* ============================================================ *)
(* UpReqSquareWallEquiv.v *)
(* *)
(* 使命： 第四面墙定理化——平方非负 plain 墙的「B 形提升器」缺口闭合。 *)
(* 主件： snw_square_wall_lpo：墙/提升器/受限 LPO 三者双向归约四槽账。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqLpoEquiv、UpRealLeB。 *)
(* 构造性注记： 零公理、零假设负载；反向可达（与 AA23 降档不同），交付完整等价。 *)
(* 编译配方： Rocq 9.1 coqc -Q . "" UpReqSquareWallEquiv.v。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqSquareWallEquiv.v —— 第四面墙定理化                          *)
(*   （平方非负 plain 墙 × B 形提升器缺口 ⟺ 受限 LPO）                *)
(*                                                              *)
(* 公理面：本件零公理、零假设负载。墙坐标在案：                      *)
(*   G09_MiscSmall.v:328（plain 形在柯西层构造性不可证——要求对任意   *)
(*   t 给出 t·t 严格正或 t·t==0 的析取判定，等价零分离判定）；        *)
(*   G09_MiscSmall.v:357（plain 槽在 Real 层不可证明：构造性判定性     *)
(*   阻塞，非缺件可拼）。                                            *)
(*                                                              *)
(* 缺口的两侧（在盘事实）：                                          *)
(*   B 侧可达：UpRealLeB:432 real_square_nonneg_B——Bishop 余量形      *)
(*     （forall eps>0, 0 < 0+t·t+eps 的 real_le_b 编码）全称可证；    *)
(*   Or 侧为墙：real_le real_zero (t·t)（real_le = Or (real_lt)       *)
(*     (real_eq) 析取强序，CW219 L3521 编码）全称不可供给。           *)
(*   单向桥 real_le_to_le_b（UpRealLeB:87）仅 Or⟹B；反向提升器        *)
(*   （B⟹Or）恰为缺口的全部厚度——SqWallCorrMark 只登记未定理化。      *)
(*                                                              *)
(* 本件新数学（负形定理族，AA15/AA22/AA23 谱系）：                    *)
(*   snw_b_lift : Set := 对一切 t 把 B 形证书抬为 Or 精确分支——       *)
(*     「第四面墙」的语句本体（缺口的显形）。                          *)
(*   snw_b_lift_to_rlpo（正向）：提升器 + 在盘全称 B 证书 ⟹ 素颜墙     *)
(*     ⟹ lpn_forward ⟹ rLPO——缺口厚度恰好等于判定器。                *)
(*   snw_rlpo_to_b_lift（反向·可达）：rLPO 逐点供分支，B 证书参数      *)
(*     冗余丢弃——「提升器=判定器换皮」的机器表达。与 AA23 钉定墙的    *)
(*     反向障碍降档不同，本墙反向可达，交付完整双向。                  *)
(*   snw_square_wall_lpo（主件闭合）：四槽账                           *)
(*     And (wall->rLPO) (And (rLPO->wall) (And (lift->rLPO)           *)
(*            (rLPO->lift)))——墙、提升器、rLPO 三者等价的循环等价式。  *)
(*   snw_wall_iff_lift（同构账）：墙 ⟺ 提升器——正向 B 证书免费复合，   *)
(*     反向逐点直供：B/Or 缺口与墙同构，零厚度差。                     *)
(*   snw_iface_slot_resolve（G3 泛型槽段·UpReqAlign:1122 位1 指针）：  *)
(*     rLPO 证书消解接口泛型 req_square_nonneg 槽（RealEnhancedReal    *)
(*     实例字段 le/zero/mult 的 delta 换形）——使用位升级参形           *)
(*     G09:490 sqp_fisher_zero_implies_pointwise_real 的 Hsq 参数位    *)
(*     从此有判定器消解通道。                                          *)
(*                                                              *)
(* 谱系：AA15（UpReqLpoEquiv，SqWall⟺rLPO 首创面）⟶ AA22（Gibbs 泛型   *)
(*   槽范式）⟶ AA23（PinWall 反向障碍账降档）⟶ 本件（第四面墙：缺口    *)
(*   显形+完整双向）。与 UpReqLogZWallEquiv（EXPL2 领地，未 Require）  *)
(*   的谱系关系：同以 UpReqLpoEquiv 的 rLPO 为判定基座，独立成件。      *)
(*                                                              *)
(* 纪律：纯构造性 Set 层、语句面全 Set/自定义 And/Or，零 Prop 泄露；    *)
(*       墙语句作蕴含前件参数化，全程零经典逻辑；两面均机器检验完整。    *)
(* ------------------------------------------------------------ *)
(* 前缀 snw_（全库 grep 零撞名）。                                    *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqLpoEquiv.
Require Import UpRealLeB.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Part 1：两面语句（全 Set 零 Prop）                              *)
(* ============================================================ *)

(* 素颜墙：平方非负全称形（Or 编码精确序；与 UpReqLpoEquiv SqWall
   定义性同面，独立定形并给互证桥——第四面墙的墙语本体） *)
Definition snw_wall : Set :=
  forall t : Real, real_le real_zero (real_mult t t).

(* B 形提升器：对一切 t 把 Bishop 余量证书抬为 Or 精确序分支。
   B 侧证书全称免费（real_square_nonneg_B 在盘），Or 侧不可供给——
   本型即「B 形可达、Or 精确形不可证」判定性缺口的显形。 *)
Definition snw_b_lift : Set :=
  forall t : Real,
    real_le_b real_zero (real_mult t t) ->
    real_le real_zero (real_mult t t).

(* 互证桥：素颜墙与 SqWall（UpReqLpoEquiv:239）定义性同面 *)
Theorem snw_wall_sq_wall : snw_wall -> SqWall.
Proof.
  exact (fun H => H).
Qed.

Theorem snw_sq_wall_wall : SqWall -> snw_wall.
Proof.
  exact (fun H => H).
Qed.

(* ============================================================ *)
(* Part 2：正向——提升器 ⟹ 受限 LPO（缺口厚度 = 判定器）            *)
(*   证法：三段复合——在盘全称 B 证书（real_square_nonneg_B）        *)
(*   × 提升器 ⟹ 素颜墙 ⟹ lpn_forward（AA15 正向腿）⟹ rLPO。        *)
(*   非平凡账：B 侧免费 + 提升器恰补余下全部缺口，故提升器的供给     *)
(*   力与「逐实数符号判定器」等价——缺口厚度的测量定理。              *)
(* ============================================================ *)

Theorem snw_b_lift_to_rlpo : snw_b_lift -> rLPO.
Proof.
  intros Hlift.
  apply lpn_forward.
  intros t.
  apply Hlift.
  apply real_square_nonneg_B.
Qed.

(* ============================================================ *)
(* Part 3：反向——受限 LPO ⟹ 提升器（可达性定理·本件关键新事实）     *)
(*   证法：rLPO（经 AA15 反向腿 lpn_backward）逐点给出 Or 精确分支， *)
(*   提升器的 B 证书参数整体冗余——直接丢弃。「提升器=判定器换皮」    *)
(*   的机器表达：缺口不是独立障碍，只是判定器的另一种签名。           *)
(*   对照 AA23：钉定墙反向撞障碍须降档，本墙反向可达——两面墙的       *)
(*   结构性分野（接口不可满足型 vs 编码余量型）在此显形。              *)
(* ============================================================ *)

Theorem snw_rlpo_to_b_lift : rLPO -> snw_b_lift.
Proof.
  intros Hdec t _HB.
  exact (lpn_backward Hdec t).
Qed.

(* ============================================================ *)
(* Part 4：主件闭合——四槽账（墙/提升器/rLPO 三者等价循环）        *)
(* ============================================================ *)

Definition snw_square_wall_lpo :
  And (snw_wall -> rLPO)
      (And (rLPO -> snw_wall)
           (And (snw_b_lift -> rLPO) (rLPO -> snw_b_lift))) :=
  ((fun H => lpn_forward (snw_wall_sq_wall H)),
   ((fun H => snw_sq_wall_wall (lpn_backward H)),
    ((fun H => snw_b_lift_to_rlpo H),
     (fun H => snw_rlpo_to_b_lift H)))).

(* ============================================================ *)
(* Part 5：同构账——墙 ⟺ 提升器（缺口与墙零厚度差）                 *)
(*   正向：墙逐点直供分支，B 证书冗余丢弃；                          *)
(*   反向：提升器 + 免费全称 B 证书 ⟹ 墙——B 形可达性把缺口表面积      *)
(*   压缩到零提升器，墙即提升器换签名。                              *)
(* ============================================================ *)

Theorem snw_wall_to_b_lift : snw_wall -> snw_b_lift.
Proof.
  intros Hwall t _HB.
  exact (Hwall t).
Qed.

Theorem snw_b_lift_to_wall : snw_b_lift -> snw_wall.
Proof.
  intros Hlift t.
  apply Hlift.
  apply real_square_nonneg_B.
Qed.

Definition snw_wall_iff_lift :
  And (snw_wall -> snw_b_lift) (snw_b_lift -> snw_wall) :=
  (snw_wall_to_b_lift, snw_b_lift_to_wall).

(* ============================================================ *)
(* Part 6（G3 泛型槽段）：接口槽消解件——UpReqAlign:1122 位1 指针     *)
(*   接口泛型槽 req_square_nonneg（RealEnhancedReal 实例字段         *)
(*   le:=real_le / zero:=real_zero / mult:=real_mult）在 rLPO 证书    *)
(*   下的消解通道：G09:490 升参形 sqp_fisher_zero_implies_pointwise_  *)
(*   real 的 Hsq 参数位（本件结论面即该位）从判定器一步供给。          *)
(*   换形面仅实例字段的 delta 展开（SqWallCorrMark 衔接件一同款面）。  *)
(* ============================================================ *)

Theorem snw_iface_slot_resolve :
  rLPO ->
  (forall t : Real,
     @le Real RealEnhancedReal (@zero Real RealEnhancedReal)
         (@mult Real RealEnhancedReal t t)).
Proof.
  exact (fun Hdec => lpn_backward Hdec).
Qed.

(* ============================================================ *)
(* 提取检验与假设审计面                                           *)
(* ============================================================ *)

(* 提取检验：主四件素颜面全量提取。本四件证明体均为纯组合子复合
   （lpn 系纯 S01/S02/Q 层；B 形证书纯 real_* 顶层函数链），
   实证 Obj.magic 计数=0。
   提取面排除件账：snw_iface_slot_resolve 不入提取面——其返回类型
   为模块内类型别名（RealEnhancedReal 字段 le 的 delta 面），内核
   转换可达而 ML 提取的类型语法不可同一，提取器会插 Obj.magic 伪影
   （单点定位实证：magic 唯一落点即该件的类型别名返回位，非计算
   内容）。处置与 SqWallCorrMark 同款：接口转换件不进提取面，其正确性
   由 Print Assumptions Closed + coqchk 承载。 *)
Extraction "_thv3twall1.ml" snw_square_wall_lpo
  snw_b_lift_to_rlpo snw_rlpo_to_b_lift snw_wall_iff_lift.

Print Assumptions snw_wall_sq_wall.
Print Assumptions snw_sq_wall_wall.
Print Assumptions snw_b_lift_to_rlpo.
Print Assumptions snw_rlpo_to_b_lift.
Print Assumptions snw_square_wall_lpo.
Print Assumptions snw_wall_iff_lift.
Print Assumptions snw_iface_slot_resolve.
