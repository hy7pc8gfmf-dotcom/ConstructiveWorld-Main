(* ============================================================ *)
(* ToyR 玩具证替换件 —— T264 台账席 战役包Y（tier2 十五批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   cyc_kl_dev_expand（原 L287，1 句玩具证）                             *)
(*   cyc_kl_temp_cocycle_dev（原 L191，1 句玩具证）                       *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T339 恒等守恒更正注记】2026-09-22 包AW十四 台账席（恒等头注更正第四批） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* T277（包AL）全量恒等核查定谳、T317（包AV六）试点定谳：本件实测为 *)
(* 恒等守恒——清单所列 2 槽证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* 零变化），头注「替换」声称与实物不符，特此更正。 *)
(* 更正口径：真替换 0 槽＋恒等守恒 2 槽；本注记为追加块，上方原头注一字 *)
(* 未改（历史证据保全）；证明体、声明面、语句面、Require 面零改动；台账 *)
(* 承载见 T277 附录／T284 修正块／T317 评估册／T321／T329／T330／T337／T339 台账。 *)
(* 附记：T277 判级全文恒等；Y 域收尾＋AB 域收尾＋AD 域直推第四批（T317 六·1 方案①）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqKLCocycle.v —— 三温度对称 KL cocycle 恒等式                *)
(* （防火墙恒等式族从双温度到三温度相容性；席 Q16，2026-09-17）     *)
(* ============================================================ *)
(* 使命：M3 防火墙双温度恒等式 (β1−β2)(E2−E1) == KL(p_{t2}‖p_{t1})   *)
(*   + KL(p_{t1}‖p_{t2})（根 temp_strict_ident2 / retm_energy_temp_ *)
(*   kl_pair_ident）的三温度相容性：对称 KL 沿温度链的分解律         *)
(*   （cocycle 型）——K(1,2)+K(2,3) 与 K(1,3) 的精确偏差恒等式。      *)
(*                                                                 *)
(* 数学内容（先 python 数值锁形后落 Coq；浮点 Gibbs 四组三元组 +     *)
(*   Q 精确有理数代数，全部 diff==0，2026-09-17）：                  *)
(*   记 βi := 1/ti，Ei := E_{t_i}，P(i,j) := KL(p_j‖p_i)+KL(p_i‖p_j) *)
(*   （双温度旗舰 retm_energy_temp_kl_pair_ident 的左端）。则：      *)
(*   【件·主】cyc_kl_temp_cocycle（对称偏差恒等式）                  *)
(*     P(1,2) + (P(2,3) − P(1,3))                                   *)
(*       == (β2−β1)·(E3−E2) + (β3−β2)·(E2−E1)。                    *)
(*   【件·前向】cyc_kl_forward_cocycle：                            *)
(*     F(1,2)+F(2,3)−F(1,3) == (β3−β2)·(E2−E1)，F(i,j):=KL(p_i‖p_j) *)
(*     （右端只含中段能量差——前向分解律的"曲率"项）。               *)
(*   【件·2上循环】cyc_kl_temp_cocycle_2up（四温度闭形，G3）：       *)
(*     D(2,3,4)+D(1,2,4) == D(1,3,4)+D(1,2,3)，                     *)
(*     D(i,j,k) := P(i,j)+(P(j,k)−P(i,k))（cyc_dev 括号）。         *)
(*   【件·退化】cyc_kl_sym_self_zero：KL(p_t‖p_t) == 0（G2）。      *)
(*                                                                 *)
(* 方向声明段（KL 符号顺序逐处核对；Q6-⑥/Q6-7 假命题防线）：         *)
(*   1) retm_KL t1 t2 == KL(p_{t1} ‖ p_{t2})（from→to，供体件原序）。*)
(*   2) P(i,j) 取旗舰左端原序：KL(p_j‖p_i) 在前、KL(p_i‖p_j) 在后，  *)
(*      使三处供体件实例（对 (1,2)(2,3)(1,3)）逐字对齐、零换序。     *)
(*   3) 偏差恒等式右端方向 (β2−β1)(E3−E2)+(β3−β2)(E2−E1) 已由数值   *)
(*      前置验真（任务书草案的 (β1−β2)(β2−β3)/(β1−β3) 除法修正式    *)
(*      被数值否证；真实缺项为无除法交叉乘积和——除法式禁用教训      *)
(*      （UpFirewall 头注）在本件的落实形态）。                      *)
(*   4) 本件全程零除法（无 inv(βi−βj) 形），故 t1==t2 / t2==t3 退化  *)
(*      无需两两不等证书，恒等式对一切正温度三元组无条件成立；退化   *)
(*      分支另以 cyc_kl_sym_self_zero 定理化（自 KL 零 ⟹ 三角退化为  *)
(*      恒等）。                                                    *)
(*                                                                 *)
(* 公理面：零 公理/承认件/参数/猜想/弃证/经典逻辑；   *)
(*   依赖仅 CW_ConstructiveWorld_219 + RealEnergyTempMono（后者      *)
(*   8/8 Print Assumptions Closed 在册）；本件文件尾 Print          *)
(*   Assumptions 主件五条，交付实测全 Closed under the global       *)
(*   context。语句面全 Set（real_eq/real_lt 证书位；零 Prop 型假设申报）。*)
(*                                                                 *)
(* 红线自审：① 纯构造性；② 语句面零 Prop 前提（real_lt 正性证书位   *)
(*   沿供体件惯例）；③ 真证 Qed 全闭合（非平凡：三温度代数核 +      *)
(*   plus_compat/opp_compat 组装链 + 供体件三实例化）；④ 可提取     *)
(*   （attn/_tq16_extract.v 探针，Obj.magic 计 0 实测）。            *)
(*                                                                 *)
(* 编译配方：COQLIB=ROCQLIB=C:/Rocq-Platform~9.1~2026.01/lib/coq；  *)
(*   cd Live_X && coqc -q -native-compiler no -Q . "" UpReqKLCocycle *)
(*   （全量经 cpu_guard -LoadLimit 70 -CoreN 1 包裹）。              *)
(* 前缀：cyc_（全库 grep 撞名 0：既有仅 cyc_nat_le_gt_cases 等       *)
(*   DTPT 桥异名件）。                                              *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.
Require Import RealEnergyTempMono.

(* 与供体件 retm_alg 同构的代数收口（本文件自带，不依赖 Ltac 导出）：
   real_eq 归零差 + 逐 n 投影 + Q-ring。 *)
Ltac cyc_alg :=
  apply real_eq_of_zero_diff; intro n;
  repeat first [ rewrite real_plus_proj | rewrite real_mult_proj | rewrite real_opp_proj ];
  ring.

(* real_zero 右端特化：projT1 real_zero n 不入 rewrite 面须先化零
   （本席实测：不化则 ring 原子化失败 not a valid ring equation） *)
Ltac cyc_alg0 :=
  apply real_eq_of_zero_diff; intro n;
  cbn [real_zero projT1];
  repeat first [ rewrite real_plus_proj | rewrite real_mult_proj | rewrite real_opp_proj ];
  ring.

(* ============================================================ *)
(* Part 0：代数收口配方（本席实测定律，替代初版"纯变量代数核"方案）   *)
(*   本环境下 real_eq 目标上的 ring 重化对「投影×应用」原子           *)
(*   （projT1 (real_inv_pos t Ht) n / projT1 (retm_Eexp ...) n 形）    *)
(*   6~9 个全数消化（供体旗舰同形）；但对「裸变量投影」原子            *)
(*   （projT1 b n，b 为引理全称变量）>3 个即报 not a valid ring        *)
(*   equation（S02 全部 ring 件 ≤3 原子的原因）。故代数核不再独立      *)
(*   成件，而是 compat 链代入后内联收口（目标恰为应用原子形）。        *)
(* ============================================================ *)

(* ============================================================ *)
(* Part 1：G2 退化分支（除法式禁用 → 交叉乘积形；自 KL 零）          *)
(* ============================================================ *)

(* KL(p_t‖p_t) == 0：自温度 KL 精确零（退化三角的底边）。
   由 retm_KL_decomp 特化 (t,t) + 退化核收口。 *)
Theorem cyc_kl_sym_self_zero : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (t : Real) (Ht : real_lt real_zero t),
  real_eq (retm_KL X u s0 l t Ht t Ht) real_zero.
Proof.
  intros X u s0 l t Ht.
  apply (real_eq_trans (retm_KL X u s0 l t Ht t Ht)
           (real_plus
              (real_mult (real_plus (real_inv_pos t Ht) (real_opp (real_inv_pos t Ht)))
                         (retm_Eexp X u s0 l t Ht))
              (real_plus (retm_LZ X u s0 l t Ht) (real_opp (retm_LZ X u s0 l t Ht))))
           real_zero).
  - exact (retm_KL_decomp X u s0 l t Ht t Ht).
  - cyc_alg0.
Qed.

(* ============================================================ *)
(* Part 2：G1 主件——三温度对称 KL cocycle 恒等式                    *)
(* ============================================================ *)

(* P(1,2) + (P(2,3) − P(1,3)) == (β2−β1)(E3−E2) + (β3−β2)(E2−E1)
   其中 P(i,j) := KL(p_j‖p_i) + KL(p_i‖p_j)（旗舰左端原序）。
   右端为交叉乘积和（零除法），退化自动内含。 *)
Theorem cyc_kl_temp_cocycle : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (t1 : Real) (Ht1 : real_lt real_zero t1)
  (t2 : Real) (Ht2 : real_lt real_zero t2)
  (t3 : Real) (Ht3 : real_lt real_zero t3),
  real_eq
    (real_plus (real_plus (retm_KL X u s0 l t2 Ht2 t1 Ht1)
                          (retm_KL X u s0 l t1 Ht1 t2 Ht2))
               (real_plus (real_plus (retm_KL X u s0 l t3 Ht3 t2 Ht2)
                                     (retm_KL X u s0 l t2 Ht2 t3 Ht3))
                          (real_opp (real_plus (retm_KL X u s0 l t3 Ht3 t1 Ht1)
                                               (retm_KL X u s0 l t1 Ht1 t3 Ht3)))))
    (real_plus (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t1 Ht1)))
                          (real_plus (retm_Eexp X u s0 l t3 Ht3)
                                     (real_opp (retm_Eexp X u s0 l t2 Ht2))))
               (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t2 Ht2)))
                          (real_plus (retm_Eexp X u s0 l t2 Ht2)
                                     (real_opp (retm_Eexp X u s0 l t1 Ht1))))).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2 t3 Ht3.
  assert (H12 := retm_energy_temp_kl_pair_ident X u s0 l t1 Ht1 t2 Ht2).
  assert (H23 := retm_energy_temp_kl_pair_ident X u s0 l t2 Ht2 t3 Ht3).
  assert (H13 := retm_energy_temp_kl_pair_ident X u s0 l t1 Ht1 t3 Ht3).
  apply (real_eq_trans
           (real_plus (real_plus (retm_KL X u s0 l t2 Ht2 t1 Ht1)
                                 (retm_KL X u s0 l t1 Ht1 t2 Ht2))
                      (real_plus (real_plus (retm_KL X u s0 l t3 Ht3 t2 Ht2)
                                            (retm_KL X u s0 l t2 Ht2 t3 Ht3))
                                 (real_opp (real_plus (retm_KL X u s0 l t3 Ht3 t1 Ht1)
                                                      (retm_KL X u s0 l t1 Ht1 t3 Ht3)))))
           (real_plus
              (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t2 Ht2)))
                         (real_plus (retm_Eexp X u s0 l t2 Ht2) (real_opp (retm_Eexp X u s0 l t1 Ht1))))
              (real_plus
                 (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t3 Ht3)))
                            (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t2 Ht2))))
                 (real_opp (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t3 Ht3)))
                                      (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t1 Ht1)))))))).
  - exact (RealSetoid.real_eq_plus_compat
             (real_plus (retm_KL X u s0 l t2 Ht2 t1 Ht1) (retm_KL X u s0 l t1 Ht1 t2 Ht2))
             (real_plus (real_plus (retm_KL X u s0 l t3 Ht3 t2 Ht2) (retm_KL X u s0 l t2 Ht2 t3 Ht3))
                        (real_opp (real_plus (retm_KL X u s0 l t3 Ht3 t1 Ht1) (retm_KL X u s0 l t1 Ht1 t3 Ht3))))
             (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t2 Ht2)))
                        (real_plus (retm_Eexp X u s0 l t2 Ht2) (real_opp (retm_Eexp X u s0 l t1 Ht1))))
             (real_plus (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t3 Ht3)))
                                   (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t2 Ht2))))
                        (real_opp (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t3 Ht3)))
                                             (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t1 Ht1))))))
             H12
             (RealSetoid.real_eq_plus_compat
                (real_plus (retm_KL X u s0 l t3 Ht3 t2 Ht2) (retm_KL X u s0 l t2 Ht2 t3 Ht3))
                (real_opp (real_plus (retm_KL X u s0 l t3 Ht3 t1 Ht1) (retm_KL X u s0 l t1 Ht1 t3 Ht3)))
                (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t3 Ht3)))
                           (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t2 Ht2))))
                (real_opp (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t3 Ht3)))
                                     (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t1 Ht1)))))
                H23
                (RealSetoid.real_eq_opp_compat
                   (real_plus (retm_KL X u s0 l t3 Ht3 t1 Ht1) (retm_KL X u s0 l t1 Ht1 t3 Ht3))
                   (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t3 Ht3)))
                              (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t1 Ht1))))
                   H13))).
  - cyc_alg.
Qed.

(* 括号形：偏差括号 cyc_dev（透明 Definition，全参显式） *
   D(i,j,k) := P(i,j) + (P(j,k) − P(i,k))。 *)
Definition cyc_dev (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (ta : Real) (Ha : real_lt real_zero ta)
  (tb : Real) (Hb : real_lt real_zero tb)
  (tc : Real) (Hc : real_lt real_zero tc) : Real :=
  real_plus (real_plus (retm_KL X u s0 l tb Hb ta Ha)
                       (retm_KL X u s0 l ta Ha tb Hb))
            (real_plus (real_plus (retm_KL X u s0 l tc Hc tb Hb)
                                  (retm_KL X u s0 l tb Hb tc Hc))
                       (real_opp (real_plus (retm_KL X u s0 l tc Hc ta Ha)
                                            (retm_KL X u s0 l ta Ha tc Hc)))).

(* 主件的括号形重述（定义性 equal，exact 直达） *)
Theorem cyc_kl_temp_cocycle_dev : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (ta : Real) (Ha : real_lt real_zero ta)
  (tb : Real) (Hb : real_lt real_zero tb)
  (tc : Real) (Hc : real_lt real_zero tc),
  real_eq (cyc_dev X u s0 l ta Ha tb Hb tc Hc)
          (real_plus (real_mult (real_plus (real_inv_pos tb Hb) (real_opp (real_inv_pos ta Ha)))
                                (real_plus (retm_Eexp X u s0 l tc Hc)
                                           (real_opp (retm_Eexp X u s0 l tb Hb))))
                     (real_mult (real_plus (real_inv_pos tc Hc) (real_opp (real_inv_pos tb Hb)))
                                (real_plus (retm_Eexp X u s0 l tb Hb)
                                           (real_opp (retm_Eexp X u s0 l ta Ha))))).
Proof.
  exact (cyc_kl_temp_cocycle).
Qed.

(* ============================================================ *)
(* Part 3：G1 加件——前向 KL 分解律                                  *)
(* ============================================================ *)

(* F(1,2) + (F(2,3) − F(1,3)) == (β3−β2)·(E2−E1)
   （retm_KL_decomp 三实例化；右端只含中段能量差——log 项沿链对消） *)
Theorem cyc_kl_forward_cocycle : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (t1 : Real) (Ht1 : real_lt real_zero t1)
  (t2 : Real) (Ht2 : real_lt real_zero t2)
  (t3 : Real) (Ht3 : real_lt real_zero t3),
  real_eq
    (real_plus (retm_KL X u s0 l t1 Ht1 t2 Ht2)
               (real_plus (retm_KL X u s0 l t2 Ht2 t3 Ht3)
                          (real_opp (retm_KL X u s0 l t1 Ht1 t3 Ht3))))
    (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t2 Ht2)))
               (real_plus (retm_Eexp X u s0 l t2 Ht2)
                          (real_opp (retm_Eexp X u s0 l t1 Ht1)))).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2 t3 Ht3.
  assert (d12 := retm_KL_decomp X u s0 l t1 Ht1 t2 Ht2).
  assert (d23 := retm_KL_decomp X u s0 l t2 Ht2 t3 Ht3).
  assert (d13 := retm_KL_decomp X u s0 l t1 Ht1 t3 Ht3).
  apply (real_eq_trans
           (real_plus (retm_KL X u s0 l t1 Ht1 t2 Ht2)
                      (real_plus (retm_KL X u s0 l t2 Ht2 t3 Ht3)
                                 (real_opp (retm_KL X u s0 l t1 Ht1 t3 Ht3))))
           (real_plus
              (real_plus (real_mult (real_plus (real_inv_pos t2 Ht2)
                                                (real_opp (real_inv_pos t1 Ht1)))
                                    (retm_Eexp X u s0 l t1 Ht1))
                         (real_plus (retm_LZ X u s0 l t2 Ht2)
                                    (real_opp (retm_LZ X u s0 l t1 Ht1))))
              (real_plus
                 (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3)
                                                   (real_opp (real_inv_pos t2 Ht2)))
                                       (retm_Eexp X u s0 l t2 Ht2))
                            (real_plus (retm_LZ X u s0 l t3 Ht3)
                                       (real_opp (retm_LZ X u s0 l t2 Ht2))))
                 (real_opp (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3)
                                                             (real_opp (real_inv_pos t1 Ht1)))
                                                 (retm_Eexp X u s0 l t1 Ht1))
                                      (real_plus (retm_LZ X u s0 l t3 Ht3)
                                                 (real_opp (retm_LZ X u s0 l t1 Ht1)))))))).
  - exact (RealSetoid.real_eq_plus_compat
             (retm_KL X u s0 l t1 Ht1 t2 Ht2)
             (real_plus (retm_KL X u s0 l t2 Ht2 t3 Ht3)
                        (real_opp (retm_KL X u s0 l t1 Ht1 t3 Ht3)))
             (real_plus (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t1 Ht1)))
                                   (retm_Eexp X u s0 l t1 Ht1))
                        (real_plus (retm_LZ X u s0 l t2 Ht2) (real_opp (retm_LZ X u s0 l t1 Ht1))))
             (real_plus (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t2 Ht2)))
                                   (retm_Eexp X u s0 l t2 Ht2))
                        (real_plus (retm_LZ X u s0 l t3 Ht3) (real_opp (retm_LZ X u s0 l t2 Ht2))))
             (real_opp (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t1 Ht1)))
                                                  (retm_Eexp X u s0 l t1 Ht1))
                                       (real_plus (retm_LZ X u s0 l t3 Ht3) (real_opp (retm_LZ X u s0 l t1 Ht1))))))
             d12
             (RealSetoid.real_eq_plus_compat
                (retm_KL X u s0 l t2 Ht2 t3 Ht3)
                (real_opp (retm_KL X u s0 l t1 Ht1 t3 Ht3))
                (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t2 Ht2)))
                                      (retm_Eexp X u s0 l t2 Ht2))
                           (real_plus (retm_LZ X u s0 l t3 Ht3) (real_opp (retm_LZ X u s0 l t2 Ht2))))
                (real_opp (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t1 Ht1)))
                                                (retm_Eexp X u s0 l t1 Ht1))
                                     (real_plus (retm_LZ X u s0 l t3 Ht3) (real_opp (retm_LZ X u s0 l t1 Ht1)))))
                d23
                (RealSetoid.real_eq_opp_compat
                   (retm_KL X u s0 l t1 Ht1 t3 Ht3)
                   (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t1 Ht1)))
                                         (retm_Eexp X u s0 l t1 Ht1))
                              (real_plus (retm_LZ X u s0 l t3 Ht3) (real_opp (retm_LZ X u s0 l t1 Ht1))))
                   d13))).
  - cyc_alg.
Qed.

(* ============================================================ *)
(* Part 4：G3——四温度 2-上循环闭形                                  *)
(* ============================================================ *)

(* 偏差括号的展开件：D(a,b,c) == T(a,b,c)（T 形见 Part 0 注与主件目标形） *)
Lemma cyc_kl_dev_expand : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (ta : Real) (Ha : real_lt real_zero ta)
  (tb : Real) (Hb : real_lt real_zero tb)
  (tc : Real) (Hc : real_lt real_zero tc),
  real_eq (cyc_dev X u s0 l ta Ha tb Hb tc Hc)
          (real_plus (real_mult (real_plus (real_inv_pos tb Hb) (real_opp (real_inv_pos ta Ha)))
                                (real_plus (retm_Eexp X u s0 l tc Hc)
                                           (real_opp (retm_Eexp X u s0 l tb Hb))))
                     (real_mult (real_plus (real_inv_pos tc Hc) (real_opp (real_inv_pos tb Hb)))
                                (real_plus (retm_Eexp X u s0 l tb Hb)
                                           (real_opp (retm_Eexp X u s0 l ta Ha))))).
Proof.
  exact (fun X u s0 l ta Ha tb Hb tc Hc =>           cyc_kl_temp_cocycle X u s0 l ta Ha tb Hb tc Hc).
Qed.

(* 2-上循环闭：D(2,3,4)+D(1,2,4) == D(1,3,4)+D(1,2,3)。
   cocycle 缺项 D 本身沿四温度链无累圈（δD == 0）——温度链上对称 KL
   偏差是纯 2-上循环（数值 Q 精确验真）。 *)
Theorem cyc_kl_temp_cocycle_2up : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (t1 : Real) (Ht1 : real_lt real_zero t1)
  (t2 : Real) (Ht2 : real_lt real_zero t2)
  (t3 : Real) (Ht3 : real_lt real_zero t3)
  (t4 : Real) (Ht4 : real_lt real_zero t4),
  real_eq
    (real_plus (cyc_dev X u s0 l t2 Ht2 t3 Ht3 t4 Ht4)
               (cyc_dev X u s0 l t1 Ht1 t2 Ht2 t4 Ht4))
    (real_plus (cyc_dev X u s0 l t1 Ht1 t3 Ht3 t4 Ht4)
               (cyc_dev X u s0 l t1 Ht1 t2 Ht2 t3 Ht3)).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2 t3 Ht3 t4 Ht4.
  assert (E234 := cyc_kl_dev_expand X u s0 l t2 Ht2 t3 Ht3 t4 Ht4).
  assert (E124 := cyc_kl_dev_expand X u s0 l t1 Ht1 t2 Ht2 t4 Ht4).
  assert (E134 := cyc_kl_dev_expand X u s0 l t1 Ht1 t3 Ht3 t4 Ht4).
  assert (E123 := cyc_kl_dev_expand X u s0 l t1 Ht1 t2 Ht2 t3 Ht3).
  apply (real_eq_trans
           (real_plus (cyc_dev X u s0 l t2 Ht2 t3 Ht3 t4 Ht4)
                      (cyc_dev X u s0 l t1 Ht1 t2 Ht2 t4 Ht4))
           (real_plus
              (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3)
                                                (real_opp (real_inv_pos t2 Ht2)))
                                    (real_plus (retm_Eexp X u s0 l t4 Ht4)
                                               (real_opp (retm_Eexp X u s0 l t3 Ht3))))
                         (real_mult (real_plus (real_inv_pos t4 Ht4)
                                               (real_opp (real_inv_pos t3 Ht3)))
                                    (real_plus (retm_Eexp X u s0 l t3 Ht3)
                                               (real_opp (retm_Eexp X u s0 l t2 Ht2)))))
              (real_plus
                 (real_mult (real_plus (real_inv_pos t2 Ht2)
                                       (real_opp (real_inv_pos t1 Ht1)))
                            (real_plus (retm_Eexp X u s0 l t4 Ht4)
                                       (real_opp (retm_Eexp X u s0 l t2 Ht2))))
                 (real_mult (real_plus (real_inv_pos t4 Ht4)
                                       (real_opp (real_inv_pos t2 Ht2)))
                            (real_plus (retm_Eexp X u s0 l t2 Ht2)
                                       (real_opp (retm_Eexp X u s0 l t1 Ht1))))))).
  - exact (RealSetoid.real_eq_plus_compat _ _ _ _ E234 E124).
  - apply (real_eq_trans
             (real_plus (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t2 Ht2)))
            (real_plus (retm_Eexp X u s0 l t4 Ht4) (real_opp (retm_Eexp X u s0 l t3 Ht3)))) (real_mult (real_plus (real_inv_pos t4 Ht4) (real_opp (real_inv_pos t3 Ht3)))
            (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t2 Ht2))))) (real_plus (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t1 Ht1)))
            (real_plus (retm_Eexp X u s0 l t4 Ht4) (real_opp (retm_Eexp X u s0 l t2 Ht2)))) (real_mult (real_plus (real_inv_pos t4 Ht4) (real_opp (real_inv_pos t2 Ht2)))
            (real_plus (retm_Eexp X u s0 l t2 Ht2) (real_opp (retm_Eexp X u s0 l t1 Ht1))))))
             (real_plus (real_plus (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t1 Ht1)))
            (real_plus (retm_Eexp X u s0 l t4 Ht4) (real_opp (retm_Eexp X u s0 l t3 Ht3)))) (real_mult (real_plus (real_inv_pos t4 Ht4) (real_opp (real_inv_pos t3 Ht3)))
            (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t1 Ht1))))) (real_plus (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t1 Ht1)))
            (real_plus (retm_Eexp X u s0 l t3 Ht3) (real_opp (retm_Eexp X u s0 l t2 Ht2)))) (real_mult (real_plus (real_inv_pos t3 Ht3) (real_opp (real_inv_pos t2 Ht2)))
            (real_plus (retm_Eexp X u s0 l t2 Ht2) (real_opp (retm_Eexp X u s0 l t1 Ht1))))))).
    + cyc_alg.
    + exact (RealSetoid.real_eq_plus_compat _ _ _ _
               (real_eq_sym _ _ E134) (real_eq_sym _ _ E123)).
Qed.

(* ============================================================ *)
(* G4 证据：公理面（主件五条全 Closed 实测见交付报告；cores 同法）    *)
(* ============================================================ *)
Print Assumptions cyc_kl_sym_self_zero.
Print Assumptions cyc_kl_temp_cocycle.
Print Assumptions cyc_kl_temp_cocycle_dev.
Print Assumptions cyc_kl_forward_cocycle.
Print Assumptions cyc_kl_temp_cocycle_2up.
