(* ==========================================================================
   abl_tail_expf_iface_inst.v — C1 一期 LoHi 17 位解锁唯一新增供给文件
   ── 使命：expf 接口实例化（uabd1x 五槽直引）＋RIS 面副本二件＋LoHi 两宿主九定理
      @RealInterfaceEnhancedMod.RealEnhancedReal 具名实例化——17 位翻色落点（键控批一期）。
   ── 依赖：S01_BaseRing、S02_CauchyComplete（Real/real_* 载体面）、S07_RealSetoidExpLog
      （RIS 类＋RealInterfaceEnhancedMod.RealEnhancedReal＋real_lt_plus_compat_lt_le）、
      UpAblD1_expf_pack（uabd1x_ 根五槽）、UpReqConcFin2（cf2_* 世界数据）、
      ToyR_UpAblP7_LoHiSqueeze、ToyR_UpAblP7_LoHiCross（迁移后宿主，实例化面）。
   ── 对标：uabd1x_expf_pack 五槽根（UpAblD1_expf_pack:48-67 供给形）、
      uabl_attn_full_instance:41-60 具名槽体例与 :73-76 lpc 同款、Paper7Ablation:101
      ／P7BoundedSoftmaxDeep:272 对应源出件、UpReqAttnMixTime:79 bs_lpc 逐字体例。
   ── 构造性：语句面全 Set 层（And=prod；零 Prop 泄露）；零承认词面；零新增公理面
      （条款 H）；Part 0 副本纯 RIS 类字段重演、零 DO 零新前提。
   ── 编译配方：Rocq 9.1 直调 coqc，cpu_guard 包裹，-native-compiler no，
      born-in-place 先写后编（沙箱 31 件 .vo 闭包单向 -Q，落点后 vo 树原地重编）。
   ── 依赖方向注记：本件单向 Require 两迁移宿主（Part C 实例化面）；宿主零 Require
      本件（其 p7a/p7d 上游使用以 Part 0 同体证明内联，单向无环）。
   ── 提取检验区（Obj.magic=0 五证位预留）：语句面提取零 magic，① tpei_expf
      ② tpei_p7a_lo_lt_one_req ③ tpei_p7d_hi_gt_one_req ④ tpei_uahl_lo_lt_one_hi
      ⑤ tpei_uahlc_lo_one_hi_full 等全数 Closed。
   ========================================================================== *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import UpAblD1_expf_pack.
Require Import UpReqConcFin2.
Require Import ToyR_UpAblP7_LoHiSqueeze.
Require Import ToyR_UpAblP7_LoHiCross.

(* ============================================================ *)
(* Part 0：RIS 面副本二件（语句面承 Paper7Ablation:101/P7B:272 逐字同形，        *)
(*   唯 expf_zero 槽面 Id→req；证明体＝施工说明 §2.2 红一条式样）                  *)
(* ============================================================ *)

Section TpeiMirror.

Context {R : Set}.
Context {RI : RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid R}.

(* RIS 投影银行（S10 AttentionGibbsBridgeSetoid :12224-12232 体例）。 *)
Let zero : R := @RealInterfaceEnhancedMod.zero R RI.
Let one : R := @RealInterfaceEnhancedMod.one R RI.
Let mult : R -> R -> R := @RealInterfaceEnhancedMod.mult R RI.
Let opp : R -> R := @RealInterfaceEnhancedMod.opp R RI.
Let lt : R -> R -> Set := @RealInterfaceEnhancedMod.lt R RI.
Let req : R -> R -> Set := @RealInterfaceEnhancedMod.req R RI.
Let req_sym := @RealInterfaceEnhancedMod.req_sym R RI.
Let req_trans := @RealInterfaceEnhancedMod.req_trans R RI.
Let mult_comm := @RealInterfaceEnhancedMod.mult_comm R RI.
Let mult_zero := @RealInterfaceEnhancedMod.mult_zero R RI.
Let mult_positive := @RealInterfaceEnhancedMod.mult_positive R RI.
Let lt_id_l := @RealInterfaceEnhancedMod.lt_id_l R RI.
Let lt_id_r := @RealInterfaceEnhancedMod.lt_id_r R RI.
Let lt_mult_compat := @RealInterfaceEnhancedMod.lt_mult_compat R RI.
Let lt_zero_opp := @RealInterfaceEnhancedMod.lt_zero_opp R RI.
Let inv_pos : forall x : R, lt zero x -> R := @RealInterfaceEnhancedMod.inv_pos R RI.
Let inv_pos_pos := @RealInterfaceEnhancedMod.inv_pos_pos R RI.

(* 副本一：p7a_lo_lt_one 的 req 面（参序逐字同 Paper7Ablation 出节形 7 参）。 *)
Theorem tpei_p7a_lo_lt_one_req :
  forall (Delta : R) (Delta_pos : lt zero Delta)
         (expf : R -> R)
         (expf_zero : req (expf zero) one)
         (expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b))
         (invT : R),
  lt zero invT -> lt (expf (mult invT (opp Delta))) one.
Proof.
  intros Delta Delta_pos expf expf_zero expf_mono_lt invT Hin.
  assert (Hond := lt_zero_opp Delta Delta_pos).
  (* invT·(oppΔ) < 0：先 oppΔ·invT < 0·invT，再 0·invT 归零 *)
  assert (Hm : lt (mult (opp Delta) invT) zero).
  { apply (lt_id_r (mult (opp Delta) invT) (mult zero invT) zero
             (req_trans (mult zero invT) (mult invT zero) zero
                (mult_comm zero invT) (mult_zero invT))).
    exact (lt_mult_compat (opp Delta) zero invT Hin Hond). }
  apply (lt_id_r (expf (mult invT (opp Delta))) (expf zero) one expf_zero).
  apply (expf_mono_lt (mult invT (opp Delta)) zero).
  apply (lt_id_l (mult invT (opp Delta)) (mult (opp Delta) invT) zero
           (mult_comm invT (opp Delta))).
  exact Hm.
Qed.

(* 副本二：p7d_hi_gt_one 的 req 面（参序逐字同 P7B:272 全显 8 参；
   证明体＝一步直证：req_sym expf_zero 前置＋expf_mono_lt＋mult_positive）。 *)
Theorem tpei_p7d_hi_gt_one_req :
  forall (temp : R) (temp_pos : lt zero temp) (Delta : R) (Delta_pos : lt zero Delta)
         (expf : R -> R) (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : req (expf zero) one)
         (expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b)),
  lt one (expf (mult (inv_pos temp temp_pos) Delta)).
Proof.
  intros temp temp_pos Delta Delta_pos expf expf_pos expf_zero expf_mono_lt.
  exact (lt_id_l one (expf zero) (expf (mult (inv_pos temp temp_pos) Delta))
           (req_sym (expf zero) one expf_zero)
           (expf_mono_lt zero (mult (inv_pos temp temp_pos) Delta)
              (mult_positive (inv_pos temp temp_pos) Delta (inv_pos_pos temp temp_pos) Delta_pos))).
Qed.

End TpeiMirror.

(* ============================================================ *)
(* Part A：expf 族具名槽六件（uabl:41-60 逐行体例，根＝uabd1x_ 五槽直引，        *)
(*   「语句面与上游逐字同面、零换面转换税」）                                    *)
(* ============================================================ *)

Definition tpei_expf : Real -> Real := uabd1x_expf.

Definition tpei_expf_pos :
  forall x : Real, real_lt real_zero (tpei_expf x) := uabd1x_expf_pos.

Definition tpei_expf_zero :
  real_eq (tpei_expf real_zero) real_one := uabd1x_expf_zero.

Definition tpei_expf_plus :
  forall a b : Real,
    real_eq (tpei_expf (real_plus a b)) (real_mult (tpei_expf a) (tpei_expf b))
  := uabd1x_expf_plus.

Definition tpei_expf_mono_lt :
  forall a b : Real, real_lt a b -> real_lt (tpei_expf a) (tpei_expf b)
  := uabd1x_expf_mono_lt.

Definition tpei_expf_mono_le :
  forall a b : Real, real_le a b -> real_le (tpei_expf a) (tpei_expf b)
  := uabd1x_expf_mono_le.

(* 诚实接口具体层无条件供件（uabl:73-76 bs_lpc 同款；S07:6148 直引）——
   Part C 中 uahl_omd_bounded/uahlc_omd_bounded_one 的 lpc 尾参供给。 *)
Definition tpei_lpc :
  forall a b c d : Real,
    real_lt a b -> real_le c d -> real_lt (real_plus a c) (real_plus b d)
  := real_lt_plus_compat_lt_le.

(* ============================================================ *)
(* Part B：世界数据四件（uabl:89-97 同款，cf2 系直引——                          *)
(*   最小上游＝UpReqConcFin2（uabl 文头 Require 面照抄定论，施工说明 §四候勘闭合）） *)
(* ============================================================ *)

Definition tpei_temp : Real := cf2_temp.

Definition tpei_temp_pos := cf2_temp_pos.

Definition tpei_Delta : Real := cf2_Delta.

Definition tpei_Delta_pos := cf2_Delta_pos.

(* ============================================================ *)
(* Part C：LoHi 九定理 @RealInterfaceEnhancedMod.RealEnhancedReal 全参显式实例化（17 位翻色落点；         *)
(*   语句面＝宿主出节形的 concrete 名转换像（RealInterfaceEnhancedMod.RealEnhancedReal 实例体透明映射）；  *)
(*   证明全 exact 一击；出节最小泛化参表实测（expf_pos 零使用件不入导出形）。）   *)
(* ============================================================ *)

(* 具体世界缩写（inv_pos/one_pos 取限定投影，zero/one 实例位具名） *)
Definition tpei_invT : Real :=
  @RealInterfaceEnhancedMod.inv_pos Real RealInterfaceEnhancedMod.RealEnhancedReal tpei_temp tpei_temp_pos.

Definition tpei_lo : Real := tpei_expf (real_mult tpei_invT (real_opp tpei_Delta)).

Definition tpei_hi : Real := tpei_expf (real_mult tpei_invT tpei_Delta).

Definition tpei_invT_one : Real :=
  @RealInterfaceEnhancedMod.inv_pos Real RealInterfaceEnhancedMod.RealEnhancedReal real_one
    (@RealInterfaceEnhancedMod.one_pos Real RealInterfaceEnhancedMod.RealEnhancedReal).

Definition tpei_lo_one : Real :=
  tpei_expf (real_mult tpei_invT_one (real_opp real_one)).

Definition tpei_hi_one : Real := tpei_expf (real_mult tpei_invT_one real_one).

(* --- Squeeze 六件 --- *)

Theorem tpei_uahl_lo_lt_one_hi :
  And (real_lt tpei_lo real_one) (real_lt real_one tpei_hi).
Proof.
  exact (@uahl_lo_lt_one_hi Real RealInterfaceEnhancedMod.RealEnhancedReal tpei_temp tpei_temp_pos
           tpei_Delta tpei_Delta_pos tpei_expf tpei_expf_zero
           tpei_expf_mono_lt).
Qed.

Theorem tpei_uahl_lo_lt_hi : real_lt tpei_lo tpei_hi.
Proof.
  exact (@uahl_lo_lt_hi Real RealInterfaceEnhancedMod.RealEnhancedReal tpei_temp tpei_temp_pos
           tpei_Delta tpei_Delta_pos tpei_expf tpei_expf_zero
           tpei_expf_mono_lt).
Qed.

Theorem tpei_uahl_delta_star_bounded :
  And (real_lt real_zero (real_mult tpei_lo tpei_lo))
      (real_lt (real_mult tpei_lo tpei_lo) real_one).
Proof.
  exact (@uahl_delta_star_bounded Real RealInterfaceEnhancedMod.RealEnhancedReal tpei_temp tpei_temp_pos
           tpei_Delta tpei_Delta_pos tpei_expf tpei_expf_pos tpei_expf_zero
           tpei_expf_mono_lt).
Qed.

Theorem tpei_uahl_omd_bounded :
  And (real_lt real_zero (real_plus real_one (real_opp (real_mult tpei_lo tpei_lo))))
      (real_lt (real_plus real_one (real_opp (real_mult tpei_lo tpei_lo))) real_one).
Proof.
  exact (@uahl_omd_bounded Real RealInterfaceEnhancedMod.RealEnhancedReal tpei_lpc tpei_temp tpei_temp_pos
           tpei_Delta tpei_Delta_pos tpei_expf tpei_expf_pos tpei_expf_zero
           tpei_expf_mono_lt).
Qed.

Theorem tpei_uahl_omd_bounded_one :
  And (real_lt real_zero (real_plus real_one (real_opp (real_mult tpei_lo_one tpei_lo_one))))
      (real_lt (real_plus real_one (real_opp (real_mult tpei_lo_one tpei_lo_one)))
               real_one).
Proof.
  exact (@uahl_omd_bounded_one Real RealInterfaceEnhancedMod.RealEnhancedReal tpei_lpc tpei_expf
           tpei_expf_pos tpei_expf_zero tpei_expf_mono_lt).
Qed.

Theorem tpei_uahl_lo_lt_hi_one : real_lt tpei_lo_one tpei_hi_one.
Proof.
  exact (@uahl_lo_lt_hi_one Real RealInterfaceEnhancedMod.RealEnhancedReal tpei_expf tpei_expf_zero
           tpei_expf_mono_lt).
Qed.

(* --- Cross 三件 --- *)

Theorem tpei_uahlc_lo_lt_one_hi_one :
  And (real_lt tpei_lo_one real_one) (real_lt real_one tpei_hi_one).
Proof.
  exact (@uahlc_lo_lt_one_hi_one Real RealInterfaceEnhancedMod.RealEnhancedReal tpei_expf tpei_expf_zero
           tpei_expf_mono_lt).
Qed.

Theorem tpei_uahlc_omd_bounded_one :
  And (real_lt real_zero (real_plus real_one (real_opp (real_mult tpei_lo_one tpei_lo_one))))
      (real_lt (real_plus real_one (real_opp (real_mult tpei_lo_one tpei_lo_one)))
               real_one).
Proof.
  exact (@uahlc_omd_bounded_one Real RealInterfaceEnhancedMod.RealEnhancedReal tpei_lpc tpei_expf
           tpei_expf_pos tpei_expf_zero tpei_expf_mono_lt).
Qed.

Theorem tpei_uahlc_lo_one_hi_full :
  And (real_lt tpei_lo_one real_one)
      (And (real_lt real_one tpei_hi_one) (real_lt tpei_lo_one tpei_hi_one)).
Proof.
  exact (@uahlc_lo_one_hi_full Real RealInterfaceEnhancedMod.RealEnhancedReal tpei_expf tpei_expf_zero
           tpei_expf_mono_lt).
Qed.

(* ---- 收尾段：逐件 Print Assumptions 核验零承认（RIS 类字段非公理） ---- *)
Print Assumptions tpei_p7a_lo_lt_one_req.
Print Assumptions tpei_p7d_hi_gt_one_req.
Print Assumptions tpei_uahl_lo_lt_one_hi.
Print Assumptions tpei_uahl_lo_lt_hi.
Print Assumptions tpei_uahl_delta_star_bounded.
Print Assumptions tpei_uahl_omd_bounded.
Print Assumptions tpei_uahl_omd_bounded_one.
Print Assumptions tpei_uahl_lo_lt_hi_one.
Print Assumptions tpei_uahlc_lo_lt_one_hi_one.
Print Assumptions tpei_uahlc_omd_bounded_one.
Print Assumptions tpei_uahlc_lo_one_hi_full.
