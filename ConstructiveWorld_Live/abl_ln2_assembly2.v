(* ===================================================================== *)
(*  abl_ln2_assembly2.v —— ln2 无理性链·第二段装配回接件                     *)
(*  （lna 系换序恒等式＋尾隙界的回接装配）                                   *)
(*  使命: 把 DE 新闭合的换序恒等式真族件（lns_bsum/lnf_bterm 载体、          *)
(*        lns_identity_leg_bterm_transfer 肢迁移）回接进 lna 装配件，        *)
(*        完成路线③(ⅲ) 全链更新。三层:                                      *)
(*        ①载体订正：lna_supply_rem' 装配的载体位按真族订正——               *)
(*          旧载体 lnr_psum 位以分离锚订正注记替换（lnb3_sep_carrier_       *)
(*          erratum，旧载体分离锚的回接位重述）；真族载体正性肢（旧 lnr_    *)
(*          Ireal_pos 位的真族重述 lnb3_Ireal_pack_pos）、真族尾界两档      *)
(*          绝对值形模量（p≥1 几何档 lnb3_bsum_tail_dock / p=0 档           *)
(*          lnb3_bsum_tail_dock0，其中 p=0 档的新数学=真族首档双倍恒等      *)
(*          lnb3_bterm0_double：lnf_bterm 0 k == 2·lnt_pterm 0 k）⟹        *)
(*          六肢一线订正链核 lnb3_supply_chain_core2（lna_supply_          *)
(*          chain_core 的真族版：肢①②③沿 lna 原肢、肢④⑤⑥按真族重述）；    *)
(*        ②连接肢：lns_identity_leg_bterm_transfer 接入 lna 链——          *)
(*          挂点真族化 lnb3_leg_hook_true（替换 lna_leg_transfer_hook      *)
(*          的旧载体位）、rem'×换序合链桥 lnb3_rem_reorder_bridge           *)
(*          （lna_supply_rem' 与换序恒等式在 sigT 面的合取封装）、真族载体× *)
(*          BH 线对象桥 lnb3_Ibreal_lineL_bridge（经卷积参数位）；           *)
(*        ③全链状态更新件：路线③(ⅲ) 完成度——换序✓+回接✓ 的机器验证面      *)
(*          lnb3_chain_status（条件形全装配），无条件形余项如实分解为两     *)
(*          显式参数位（θ 上肢 lnb3_theta_slot、卷积参数位                   *)
(*          lnb3_conv_slot），两参数位供形后即得无条件形。                   *)
(*  载体订正记录: 旧链核肢④⑤⑥载体位（lnr_Ireal/lnr_psum）                  *)
(*        系非真族载体，与 I_n 真身面分离已由 lns_sep_old_carrier 机器证明  *)
(*        （1/6≠1/2）；本件 §0 在回接位复核该分离锚（lnb3_sep_carrier_     *)
(*        erratum），旧载体位就此在第二段装配作废，链核按真族重述。         *)
(*  边界声明: ①Cb（真族 Cauchy 见证）仍为显式参数位（义务如实悬置）；        *)
(*        ②无条件形=θ 上肢+卷积两参数位，                                   *)
(*        本件以条件形如实承载；③j<n 支语义归位沿用已注册口径。             *)
(*  依赖: Stdlib QArith/Qabs/Arith/ZArith/Lia；S01_BaseRing S02_Cauchy-    *)
(*        Complete S03_QExp；PolyIntegral PadeErrorIntegral BeukersLists    *)
(*        HansonLcm BeukersVariant PintMono；PsQReindex RealIdentity；      *)
(*        Ln2Escape Ln2Bridge UpReqLn2Irrational；池内链序前件              *)
(*        abl_ln2_tail_bound → abl_ln2_numer_int → abl_ln2_sharp_weight    *)
(*        → abl_ln2_ireal → abl_ln2_reorder → abl_ln2_reorder_assembly    *)
(*        → abl_ln2_assembly → 本件。                                       *)
(*  对标: 本库 ln2 塔模块族（abl_ln2_tail_bound 前件链至 abl_ln2_assembly）； *)
(*        文献路线＝Beukers 型有理积分核与 Padé 逼近无理性证明              *)
(*        （BeukersLists/PadeErrorIntegral/PintMono 模块所承）；泛型换序机   *)
(*        与 lnr_Ireal_pos 形互为平行形基准；                                *)
(*        本件为路线③(ⅲ) 之回接装配段。                                    *)
(*  构造性: 全件 Qed、零承认；语句面全 Set（sigT/S01.And/QeqT/QleT'/       *)
(*        real_eq/real_lt/cauchy）；Qeq/Qle 仅 Prop 面作推理（Qeq 桥一律   *)
(*        setoid_rewrite——DA/池件同款纪律）；文尾 Print Assumptions 全     *)
(*        Closed＋Separate Extraction 闭合（提取四件）。                    *)
(*  编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&      *)
(*        ulimit -s 65532 && nice -19 rocq c -native-compiler no -Q        *)
(*        vo_local_world_unified_0930 ""（链序：tail_bound→numer_int→      *)
(*        sharp_weight→ireal→reorder→reorder_assembly→assembly→本件；      *)
(*        单进程串行编译）。                                                 *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral PadeErrorIntegral BeukersLists HansonLcm BeukersVariant PintMono.
Require Import PsQReindex RealIdentity.
Require Import Ln2Escape Ln2Bridge.
Require Import UpReqLn2Irrational.
Require Import abl_ln2_tail_bound.
Require Import abl_ln2_numer_int.
Require Import abl_ln2_sharp_weight.
Require Import abl_ln2_ireal.
Require Import abl_ln2_reorder.
Require Import abl_ln2_reorder_assembly.
Require Import abl_ln2_assembly.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 载体订正·分离锚：旧载体位作废注记的机器取证（回接位复核）               *)
(* ============================================================ *)

(* ★ 订正注记（本件自证复核）：真族头项 ≠ 旧载体头项（1/6 ≠ 1/2）——
   lna 链核肢④⑤⑥的载体位（lnr_Ireal/lnr_psum，非真族）与真族载体
   lns_bsum（Beta 加权）头项机器分离，旧载体位就此在第二段装配作废
   （DA lnf_sep_carrier_bterm / DE lns_sep_old_carrier 判例的回接位转世） *)
Theorem lnb3_sep_carrier_erratum : Not (QeqT (lns_bsum 1 0) (lnr_psum 1 0)).
Proof.
  intro H.
  assert (Heq : (lns_bsum 1 0)%Q == (lnr_psum 1 0)%Q)
    by (apply qeqT_imp_qeq; exact H).
  vm_compute in Heq. discriminate Heq.
Qed.

(* ============================================================ *)
(* §1 ①载体订正：真族载体位（正性肢＋尾界两档＋订正链核）                    *)
(* ============================================================ *)

(* 尾界模量两形（计算内容定义件，供无条件形装配使用） *)
Definition lnb3_gapb_bound (p M : nat) : Q :=
  (q_pow (2 # 1)%Q (Datatypes.S p) * q_pow (3 # 4)%Q (Datatypes.S M - 2 * p))%Q.
Definition lnb3_gap0_bound (M : nat) : Q :=
  ((8 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q.

(* ★ 肢④重锚（lnr_Ireal_pos 的真族转世）：真族载体包装严格正——
   分离见证 eps := (1/2)·b(p,0)，头项正＋部分和单调（lnf_bterm_pos＋   *)
(*   lns_bsum_head＋lns_bsum_mono），包装证明位（Cb）不入读数            *)
Theorem lnb3_Ireal_pack_pos : forall (Cb : forall p : nat, cauchy (lns_bsum p))
    (p : nat), real_lt real_zero (lns_Ibreal Cb p).
Proof.
  intros Cb p.
  assert (Hb0 : Qlt 0 (lnf_bterm p 0)) by apply lnf_bterm_pos.
  exists ((1 # 2)%Q * lnf_bterm p 0)%Q.
  split.
  - apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    + apply rx_Qlt_Z1. lia.
    + exact Hb0.
  - exists 0%nat. intros k Hk.
    apply NatLe_drop in Hk.
    unfold lns_Ibreal, lnr_Ireal_pack, real_zero. cbn [projT1].
    assert (Ez : lns_bsum p k == (lns_bsum p k - 0)%Q) by ring.
    apply (lnr_qltT_transfer_r _ _ _ Ez).
    apply Qlt_to_QltT.
    apply (Qlt_le_trans ((1 # 2)%Q * lnf_bterm p 0)%Q (lnf_bterm p 0)
                        (lns_bsum p k)).
    + apply lnr_qhalf_lt. exact Hb0.
    + rewrite <- (lns_bsum_head p). apply lns_bsum_mono. lia.
Qed.

(* 等式交叉乘判据（Prop 面）：0 < b、0 < d 且 a·d == c·b ⟹ a/b == c/d
   （lns_qdiv_le 的等式版：两向 Qle＋Qle_antisym 闭合） *)
Lemma lnb3_qdiv_eq : forall a b c d : Q,
  Qlt 0 b -> Qlt 0 d -> (a * d)%Q == (c * b)%Q ->
  (a * Qinv b)%Q == (c * Qinv d)%Q.
Proof.
  intros a b c d Hb Hd H.
  apply Qle_antisym.
  - apply lns_qdiv_le; [exact Hb | exact Hd | apply qeq_le; exact H].
  - apply lns_qdiv_le; [exact Hd | exact Hb | apply qeq_le; apply Qeq_sym; exact H].
Qed.

(* ★ p=0 档 Q 桥（本件新数学）：真族首档双倍恒等——
   lnf_bterm 0 k == 2·lnt_pterm 0 k（bkC(k,0)=1、B(k+1,1)=1/(k+1) 的
   Q 层代数：q_fact 步进（S03 q_fact_succ）＋Qinv 积拆分（stdlib
   Qinv_mult_distr）＋单分数化后交叉乘判据（lnb3_qdiv_eq）判定） *)
Lemma lnb3_bterm0_double : forall k : nat,
  QeqT (lnf_bterm 0 k) ((2 # 1)%Q * lnt_pterm 0 k)%Q.
Proof.
  intro k. apply qeq_imp_qeqT.
  unfold lnf_bterm, lnt_pterm, Qdiv.
  assert (Eb : forall j : nat, bkC j 0 = 1%nat)
    by (intro j; destruct j; reflexivity).
  rewrite Eb.
  assert (Ez1 : Z.of_nat 1 = 1%Z) by reflexivity.
  rewrite Ez1.
  replace (2 * 0 + k + 1) with (Datatypes.S k) by lia.
  replace (0 + k) with k by lia.
  assert (E0 : (q_fact 0)%Q == (1 # 1)%Q) by reflexivity.
  setoid_rewrite E0.
  setoid_rewrite (q_fact_succ k).
  (* LHS 单分数化：分子 q_fact k 保留、分母并积（Qinv 拆分后 ring 形） *)
  assert (EL : ((1 # 1)%Q * Qinv (q_pow (2 # 1)%Q k))
               * (((1 # 1)%Q * q_fact k)
                  * Qinv ((Z.of_nat (Datatypes.S k) # 1) * q_fact k))
               == (((1 # 1)%Q * (1 # 1)%Q) * q_fact k)
                  * Qinv (q_pow (2 # 1)%Q k
                          * ((Z.of_nat (Datatypes.S k) # 1) * q_fact k))).
  { setoid_rewrite Qinv_mult_distr. setoid_rewrite Qinv_mult_distr. ring. }
  assert (ER : ((2 # 1)%Q) * (((1 # 1)%Q)
               * Qinv ((Z.of_nat (Datatypes.S k) # 1)
                       * q_pow (2 # 1)%Q (Datatypes.S k)))
               == (((2 # 1)%Q * (1 # 1)%Q))
                  * Qinv ((Z.of_nat (Datatypes.S k) # 1)
                          * q_pow (2 # 1)%Q (Datatypes.S k))).
  { ring. }
  apply (Qeq_trans _ ((((1 # 1)%Q * (1 # 1)%Q) * q_fact k)
                      * Qinv (q_pow (2 # 1)%Q k
                              * ((Z.of_nat (Datatypes.S k) # 1) * q_fact k)))%Q).
  - exact EL.
  - apply (Qeq_trans _ ((((2 # 1)%Q * (1 # 1)%Q))
                        * Qinv ((Z.of_nat (Datatypes.S k) # 1)
                                * q_pow (2 # 1)%Q (Datatypes.S k)))%Q).
    + apply (lnb3_qdiv_eq
               (((1 # 1)%Q * (1 # 1)%Q) * q_fact k)
               (q_pow (2 # 1)%Q k
                * ((Z.of_nat (Datatypes.S k) # 1) * q_fact k))
               (((2 # 1)%Q * (1 # 1)%Q))
               ((Z.of_nat (Datatypes.S k) # 1)
                * q_pow (2 # 1)%Q (Datatypes.S k))).
      * apply Qmult_lt_0_compat.
        -- apply lnt_pow2_pos.
        -- apply Qmult_lt_0_compat.
           ++ apply rx_Qlt_Z1. apply (proj1 (Nat2Z.inj_lt 0 (Datatypes.S k))). lia.
           ++ apply q_fact_pos.
      * apply Qmult_lt_0_compat.
        -- apply rx_Qlt_Z1. apply (proj1 (Nat2Z.inj_lt 0 (Datatypes.S k))). lia.
        -- apply lnt_pow2_pos.
      * setoid_rewrite (q_pow_succ (2 # 1)%Q k). ring.
    + apply Qeq_sym. exact ER.
Qed.

(* ★ 肢⑤重锚（lna_ireal_tail_dock 的真族转世）：真族部分和绝对值形模量
   |S^b_{M+d} − S^b_M| ≤ 2^{p+1}·(3/4)^{SM−2p}（p≥1）——
   单调性（lns_bsum_mono）＋Qabs_pos＋范围劈分（lns_bsum_range）＋
   DE lns_btail_geo 几何尾隙 *)
Theorem lnb3_bsum_tail_dock : forall (p M d : nat),
  (1 <= p)%nat -> (2 * p <= M + 1)%nat ->
  QleT' (Qabs (lns_bsum p (M + d) - lns_bsum p M)%Q)
        (lnb3_gapb_bound p M).
Proof.
  intros p M d Hp HM.
  assert (Hmono : Qle (lns_bsum p M) (lns_bsum p (M + d)))
    by (apply lns_bsum_mono; lia).
  assert (H0 : Qle 0 ((lns_bsum p (M + d) - lns_bsum p M)%Q)).
  { apply (Qle_trans 0%Q ((lns_bsum p M - lns_bsum p M)%Q)
                      ((lns_bsum p (M + d) - lns_bsum p M)%Q)).
    - apply qeq_le. ring.
    - apply (Qplus_le_compat (lns_bsum p M) (lns_bsum p (M + d))
                             (- lns_bsum p M)%Q (- lns_bsum p M)%Q
                             Hmono (Qle_refl ((- lns_bsum p M)%Q))). }
  apply Qle_to_QleT'.
  setoid_rewrite (Qabs_pos (lns_bsum p (M + d) - lns_bsum p M)%Q H0).
  setoid_rewrite (lns_bsum_range p M d).
  apply (Qle_trans _ (sum_upto d (fun i : nat => lnf_bterm p (M + Datatypes.S i)))).
  - apply qeq_le. ring.
  - apply QleT'_to_Qle. apply lns_btail_geo; assumption.
Qed.

(* ★ 肢⑥重锚（lna_ireal_tail_dock0 的真族转世）：p=0 档绝对值形模量
   |S^b_0,{M+d} − S^b_0,M| ≤ 8·u(0,SM)——经 lnb3_bterm0_double（双倍
   恒等）＋AP lnt_pterm_tail（n=0 窗平凡）×2 闭合 *)
Theorem lnb3_bsum_tail_dock0 : forall (M d : nat),
  QleT' (Qabs (lns_bsum 0 (M + d) - lns_bsum 0 M)%Q)
        (lnb3_gap0_bound M).
Proof.
  intros M d.
  assert (Hmono : Qle (lns_bsum 0 M) (lns_bsum 0 (M + d)))
    by (apply lns_bsum_mono; lia).
  assert (H0 : Qle 0 ((lns_bsum 0 (M + d) - lns_bsum 0 M)%Q)).
  { apply (Qle_trans 0%Q ((lns_bsum 0 M - lns_bsum 0 M)%Q)
                      ((lns_bsum 0 (M + d) - lns_bsum 0 M)%Q)).
    - apply qeq_le. ring.
    - apply (Qplus_le_compat (lns_bsum 0 M) (lns_bsum 0 (M + d))
                             (- lns_bsum 0 M)%Q (- lns_bsum 0 M)%Q
                             Hmono (Qle_refl ((- lns_bsum 0 M)%Q))). }
  assert (Ediff : (lns_bsum 0 (M + d) - lns_bsum 0 M)%Q
                  == sum_upto d (fun i : nat => lnf_bterm 0 (M + Datatypes.S i))).
  { setoid_rewrite (lns_bsum_range 0 M d). ring. }
  assert (Edouble : sum_upto d (fun i : nat => lnf_bterm 0 (M + Datatypes.S i))
                    == ((2 # 1)%Q * sum_upto d (fun i : nat => lnt_pterm 0 (M + Datatypes.S i)))%Q).
  { apply (Qeq_trans _ (sum_upto d
                        (fun i : nat => ((2 # 1)%Q * lnt_pterm 0 (M + Datatypes.S i))%Q))).
    - apply lnf_sum_ext. intro i.
      exact (qeqT_imp_qeq _ _ (lnb3_bterm0_double (M + Datatypes.S i))).
    - apply lnf_sum_scale_l. }
  assert (Ht : Qle (sum_upto d (fun i : nat => lnt_pterm 0 (M + Datatypes.S i)))
                   (((4 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q))
    by (apply QleT'_to_Qle; apply lnt_pterm_tail; lia).
  apply Qle_to_QleT'.
  setoid_rewrite (Qabs_pos (lns_bsum 0 (M + d) - lns_bsum 0 M)%Q H0).
  setoid_rewrite Ediff.
  setoid_rewrite Edouble.
  apply (Qle_trans _ (((2 # 1)%Q * ((4 # 1)%Q * lnt_pterm 0 (Datatypes.S M)))%Q)).
  - apply lnt_Qmult_le_compat_l.
    + apply Qlt_le_weak. apply rx_Qlt_Z1. lia.
    + exact Ht.
  - apply qeq_le. unfold lnb3_gap0_bound. ring.
Qed.

(* ★ 订正链核（lna_supply_chain_core 的真族版，六肢一线）：
   ①A 侧 Z 闭合 ②B 侧 Z 闭合 ③supply×Ireal 线面对接（沿 lna 原肢），
   ④真族载体严格正 ⑤真族尾界 p≥1 几何档 ⑥真族尾界 p=0 档——
   肢④⑤⑥的载体位已按 §0 分离锚订正（Cb 显式参数位） *)
Theorem lnb3_supply_chain_core2 : forall (Cb : forall p : nat, cauchy (lns_bsum p)),
  sigT (fun A : nat -> Z =>
    sigT (fun B : nat -> Z =>
      And (forall n : nat, QeqT (lnr_lA n) ((A n) # 1)%Q)
        (And (forall n : nat, QeqT (lnr_lB n) ((B n) # 1)%Q)
          (And (forall n : nat, real_eq (lnr_lineL n) (ln2b_line A B n))
            (And (forall p : nat, real_lt real_zero (lns_Ibreal Cb p))
              (And (forall (p M d : nat),
                      (1 <= p)%nat -> (2 * p <= M + 1)%nat ->
                      QleT' (Qabs (lns_bsum p (M + d) - lns_bsum p M)%Q)
                            (lnb3_gapb_bound p M))
                   (forall (M d : nat),
                      QleT' (Qabs (lns_bsum 0 (M + d) - lns_bsum 0 M)%Q)
                            (lnb3_gap0_bound M)))))))).
Proof.
  intro Cb.
  exists lna_Amod. exists lna_Bmod. split.
  - apply lna_lA_z.
  - split.
    + apply lna_lB_z.
    + split.
      * intro n. apply lna_supply_pair_dock.
      * split.
        -- intro p. apply (lnb3_Ireal_pack_pos Cb).
        -- split.
           ++ intros p M d Hp HM. apply lnb3_bsum_tail_dock; assumption.
           ++ intros M d. apply lnb3_bsum_tail_dock0.
Qed.

(* 数值锚①（p=0 双倍恒等首项）：b(0,0)=1 = 2·u(0,0)（vm_compute 判定） *)
Theorem lnb3_bterm00_anchor : QeqT (lnf_bterm 0 0) (1 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 数值锚②（真族 p=0 前两项和）：1 + 1/4 = 5/4（vm_compute 判定） *)
Theorem lnb3_bsum01_anchor : QeqT (lns_bsum 0 1) (5 # 4)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 数值锚③（p=0 档模量实例）：|S^b_0,2 − S^b_0,1| = b(0,2)=1/12 ≤ 8·u(0,2)=1/3 *)
Theorem lnb3_dock01_anchor : forall d : nat,
  QleT' (Qabs (lns_bsum 0 (1 + d) - lns_bsum 0 1)%Q) (lnb3_gap0_bound 1).
Proof. intro d. apply lnb3_bsum_tail_dock0. Qed.

(* 数值锚④（p≥1 档模量实例）：|S^b_1,2 − S^b_1,1| = b(1,2)=3/16 ≤ g(1,1)=4 *)
Theorem lnb3_dock11_anchor : forall d : nat,
  QleT' (Qabs (lns_bsum 1 (1 + d) - lns_bsum 1 1)%Q) (lnb3_gapb_bound 1 1).
Proof. intro d. apply lnb3_bsum_tail_dock; lia. Qed.

(* ============================================================ *)
(* §2 ②连接肢：lns_identity_leg_bterm_transfer 接入 lna 链                  *)
(* ============================================================ *)

(* ★ 连接肢一（挂点真族化）：lna_leg_transfer_hook 的旧载体位（穿
   lnr_Ireal）按 §0 订正作废，改用真族迁移件——任意取形 I 一经供得
   与真族载体包装的族形 real_eq，即自真族肢得 I 上的肢 *)
Theorem lnb3_leg_hook_true : forall (I : ri_Iface)
    (Cb : forall p : nat, cauchy (lns_bsum p)),
  (forall p : nat, real_eq (I p) (lnr_Ireal_pack (lns_bsum p) (Cb p))) ->
  ri_identity_leg (lns_Ibreal Cb) -> ri_identity_leg I.
Proof.
  intros I Cb HI Hleg. exact (lns_identity_leg_bterm_transfer I Cb HI Hleg).
Qed.

(* ★ 连接肢二（rem'×换序合链桥）：lna_supply_rem' 装配（供给两肢）与
   换序恒等式真族腿在 sigT 面焊接——供给前提＋腿 ⟹ I 上的腿＋供给
   装配面保全（lna_supply_rem' 与换序恒等式的连接肢主形） *)
Theorem lnb3_rem_reorder_bridge : forall (I : ri_Iface)
    (Cb : forall p : nat, cauchy (lns_bsum p)),
  lna_supply_rem' ->
  (forall p : nat, real_eq (I p) (lnr_Ireal_pack (lns_bsum p) (Cb p))) ->
  ri_identity_leg (lns_Ibreal Cb) ->
  And (ri_identity_leg I) lna_supply_rem'.
Proof.
  intros I Cb [B [Hlo Hup]] HI Hleg.
  split.
  - exact (lns_identity_leg_bterm_transfer I Cb HI Hleg).
  - exists B. split; assumption.
Qed.

(* 参数位二（卷积参数位；定义自 §3 前移至此——§2 连接肢三
   的挂钩前提须先于其使用定义）：真族载体与规范 A 面线对象的族形恒等肢
   （Σ_k lnf_bterm n k = A_n·ln2 − B_n 的有限 M 形，DE 勘录②同款登记） *)
Definition lnb3_conv_slot : Set :=
  forall (Cb : forall p : nat, cauchy (lns_bsum p)) (n : nat),
    real_eq (lns_Ibreal Cb n) (ln2b_line lna_Aface lna_Bmod n).

(* ★ 连接肢三（真族载体×BH 线对象桥）：卷积参数位（上方声明）一经供给，
   真族载体包装与 lna 线对象（经 lna_supply_pair_dock_face 规范 A 面）
   实数相等——换序恒等式腿自此沿 real_eq 直达 lna 线面 *)
Theorem lnb3_Ibreal_lineL_bridge : forall (Cb : forall p : nat, cauchy (lns_bsum p))
    (n : nat), lnb3_conv_slot -> real_eq (lns_Ibreal Cb n) (lnr_lineL n).
Proof.
  intros Cb n Hconv.
  apply (real_eq_trans (lns_Ibreal Cb n) (ln2b_line lna_Aface lna_Bmod n)
                       (lnr_lineL n)).
  - apply Hconv.
  - apply real_eq_sym. apply lna_supply_pair_dock_face.
Qed.

(* ============================================================ *)
(* §3 ③全链状态更新件：路线③(ⅲ) 完成度（换序✓+回接✓；两参数位如实悬置）      *)
(* ============================================================ *)

(* 参数位一（θ 上肢）：供给上界肢 |A·X−B| ≤ θ^n 面的显式悬置——
   无条件形余项即此参数位；义务如实声明，禁虚报 *)
Definition lnb3_theta_slot : Set :=
  ln2b_line_upper lna_Amod lna_Bmod lna_theta_mod.

(* 参数位二（卷积参数位）已于 §2 连接肢三前定义（定义前移注记：
   挂钩前提的定义须先于使用位）——本节不再重复。 *)

(* ★ 全链状态件：换序✓（真族矩形换序+尾界两档机器在案）＋回接✓（连接肢
   三件）后的链面实况——肢前提与两参数位（θ 上肢、卷积）及供给下界肢
   如实为前提，到货即得：I 上的腿、真族尾界两档、供给装配面
   （lna_supply_rem' 经 lna_supply_rem'_assemble 由下界肢＋θ 槽填充）、
   真族载体×BH 线对象焊面 *)
Theorem lnb3_chain_status : forall (Cb : forall p : nat, cauchy (lns_bsum p))
    (I : ri_Iface),
  ri_identity_leg (lns_Ibreal Cb) ->
  (forall p : nat, real_eq (I p) (lnr_Ireal_pack (lns_bsum p) (Cb p))) ->
  lnb3_theta_slot ->
  lnb3_conv_slot ->
  ln2b_line_lower lna_Amod lna_Bmod lna_clo_mod ->
  And (ri_identity_leg I)
    (And (forall (p M d : nat),
            (1 <= p)%nat -> (2 * p <= M + 1)%nat ->
            QleT' (Qabs (lns_bsum p (M + d) - lns_bsum p M)%Q)
                  (lnb3_gapb_bound p M))
      (And (forall (M d : nat),
              QleT' (Qabs (lns_bsum 0 (M + d) - lns_bsum 0 M)%Q)
                    (lnb3_gap0_bound M))
        (And lna_supply_rem'
             (forall n : nat, real_eq (lns_Ibreal Cb n) (lnr_lineL n))))).
Proof.
  intros Cb I Hleg HI Htheta Hconv Hlo.
  split.
  - exact (lns_identity_leg_bterm_transfer I Cb HI Hleg).
  - split.
    + exact lnb3_bsum_tail_dock.
    + split.
      * exact lnb3_bsum_tail_dock0.
      * split.
        -- exact (lna_supply_rem'_assemble (Hlo, Htheta)).
        -- intro n. apply (lnb3_Ibreal_lineL_bridge Cb n Hconv).
Qed.

(* ============================================================ *)
(* 可提取出口（Set 层 witness 面：订正尾界模量两形——装配的计算接入口）    *)
(* ============================================================ *)

Separate Extraction lnb3_gapb_bound lnb3_gap0_bound.

(* ============================================================ *)
(* 假设审计：以下 Print Assumptions 输出应为零依赖（零承认复核）。            *)
(* ============================================================ *)

Print Assumptions lnb3_sep_carrier_erratum.
Print Assumptions lnb3_Ireal_pack_pos.
Print Assumptions lnb3_qdiv_eq.
Print Assumptions lnb3_bterm0_double.
Print Assumptions lnb3_bsum_tail_dock.
Print Assumptions lnb3_bsum_tail_dock0.
Print Assumptions lnb3_supply_chain_core2.
Print Assumptions lnb3_bterm00_anchor.
Print Assumptions lnb3_bsum01_anchor.
Print Assumptions lnb3_dock01_anchor.
Print Assumptions lnb3_dock11_anchor.
Print Assumptions lnb3_leg_hook_true.
Print Assumptions lnb3_rem_reorder_bridge.
Print Assumptions lnb3_Ibreal_lineL_bridge.
Print Assumptions lnb3_chain_status.
