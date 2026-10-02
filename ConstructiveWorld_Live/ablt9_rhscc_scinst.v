(* ==========================================================================)
   ablt9_rhscc_scinst.v — 第九批·新增域普查批 批三施工组（B5 具体实例供给文件）
   ── 件名/使命：abl9 域 B5 缺口（abl9b_rhs_chain_59 L416 abl9b_rhs_sc_close
      Hconv 参数位）具体实例供给——件54 abl9b_ext_ws_conv 缩放对适配三件：
      ①Q 侧缩放常量桥 ablt9_rhscc_km_ksc（件54 ext_km(S m) 与件53 ksc m
      同值引理——两族坐标系的合流点，深勘 §四.2「缺中间件」之中间件一）；
      ②逐点桥 ablt9_rhscc_ws_pt_eq（件59 rhs_ws 族与件54 ext_ws 族逐点尾
      等价——中间件二）；
      ③B 型全参喂 ablt9_rhscc_sc_close_feed（Hconv 位经逐点桥 Hpt 显式
      前提适配 discharges——供给形态=适配引理形，任务说明明列形态）；
      ④伴生具名件 ablt9_rhscc_ext_close（件56 a2 L1890 案一槽内联使用
      的具名化：abl9b_rhs_close 抽象槽在件54 缩放族上的具名实例闭合）。
   ── 令源：第九批新增域普查批批三工作说明＋三态定论册（attn/
      _ttail3_三态定论册.md §四 批三行）＋abl9 主式深勘
      （attn/_ttail3_abl9主式深勘.md §四.2 B5 段）。
   ── 语句面锚（ Live 现档逐字实拍）：槽=abl9b_rhs_chain_59.v
      L416-429（Hconv：forall d, Qlt 0 d -> sigT M Nv，均匀 Nv 量序）；
      根=abl9b_ext_chain_54.v L1323-1352 abl9b_ext_ws_conv。Live/统一
      缓存同代（md5 件59=a16c30b2／件54=a0a7c3e8 双向相等）。
   ── 依赖：S01–S11 基座链＋abl_arctan_diff_20/45＋abl9b_skeleton_30＋
      abl9b_rho_chain_53（只读）＋abl9b_ext_chain_54（只读）＋
      abl9b_rhs_chain_59（只读）——三宿主零 Require 增量零字节动。
   ── 构造性注记（原工法与诚实登记）：①R9 复拍=rhs_sc_close 全库零活码使用者（仅件54
      预留注释面＋件59 自身），供给价值=接口具体化，照常施工；
      ②工程墙响亮登记（条款 G）：槽 Hconv 之 Nv 对 m 均匀，而件53
      abl9b_sca_Hd 系 Qed 不透明（real_lt 见证 N53(m) 不可见且随 m），
      real_inv_proj（S09:1446）见证即该隐藏 N0——故 Hpt 之无条件均匀形
      本批不可构（宿主零字节动红线内无解），精确 remedy=B6 手术（件53
      sca_Hd Qed→Defined 化，候用户令，深勘 §四.2 已判「不建自作施工」）
      ——B5 与 B6 耦合为本文件新见，候定论清单补录；本件将墙隔离到
      sc_close_feed 的单条 Hpt 前提（语句面显式、零藏匿），Hpt 取得后
      ④即闭。③红线四条自检：零 Axiom/Admitted/Parameter/Conjecture/
      Abort/经典逻辑；语句面 sigT/QltT 承载、比较位 Qle/Qlt 系槽面
      照录形（件54 接口逐字对拍）；Qed 全真实现；PA 见件尾。编译配方：cpu_guard 包裹 coqc -native-compiler no、COQPATH 指验证缓存树，四关=EXIT 0／vo 魔数 90100／零 Error／公理位 none（单件核验）。
 ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import abl_arctan_diff_20.
Require Import abl9b_skeleton_30.
Require Import abl_arctan_diff_45.
Require Import abl9b_rho_chain_53.
Require Import abl9b_ext_chain_54.
Require Import abl9b_rhs_chain_59.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
  QArith.Qreduction QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import ZArith Extraction.

(* ── ① Q 侧缩放常量桥：件54 ext_km(S m)=1-1/(m+1) 与件53 ksc m=m/(m+1)
      同值（两缩放坐标系合流点；深勘「缺中间件」之中间件一）──────── *)
Lemma ablt9_rhscc_km_ksc : forall m : nat,
  abl9b_ext_km (Datatypes.S m) == abl9b_ksc m.
Proof.
  intros m. unfold abl9b_ext_km, abl9b_ksc, Qdiv, Qeq.
  cbn [Z.of_nat Pos.mul Qnum Qden Qmult Qplus Qopp Qminus Qinv].
  rewrite ?abl9b_zpos_succ. ring.
Qed.

(* ── ② 逐点桥（中间件二）：件53 缩放族 rhs_ws 与件54 缩放族 ext_ws
      在双见证尾域逐点相等。见证 Ni 系件53 sca_Hd（Qed 不透明）经
      real_inv_proj 之隐藏 N0，随 m——故本件按 sigT 存在形陈述（每 m
      自取见证），均匀形=工程墙（见头注②），非本件可谎称形。──────── *)
Lemma ablt9_rhscc_ws_pt_eq : forall (m : nat) (x h : Real) (N4 : nat)
  (HN4 : forall n : nat, NatLe N4 n -> Qlt (Qabs (projT1 h n)) (1#4))
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  sigT (fun Nb : nat => forall n : nat, (Nb <= n)%nat ->
    projT1 (abl9b_rhs_ws m x h Hx Hxh) n
    == projT1 (abl9b_ext_ws m x h N4 HN4 Hx Hxh) n).
Proof.
  intros m x h N4 HN4 Hx Hxh.
  destruct (real_inv_proj
              (real_plus real_one
                 (real_mult (real_plus (abl9b_xsc m x) (abl9b_hsc m h))
                            (abl9b_xsc m x)))
              (abl9b_sca_Hd m x h Hx Hxh)) as [Ni HNi].
  exists (Nat.max Ni N4). intros n Hn.
  assert (Hni : (Ni <= n)%nat) by lia.
  assert (Hn4 : NatLe N4 n) by (apply NatLe_lift; lia).
  (* hsc 与 xsc 同体：xsc_proj 转换即合 *)
  assert (Hh : projT1 (abl9b_hsc m h) n == abl9b_ksc m * projT1 h n)
    by (unfold abl9b_hsc; exact (abl9b_xsc_proj m h n)).
  (* 件53 侧 D_m 投影（件53 sca_Hd 证明内 HD 链之导出重排） *)
  assert (HD : projT1 (real_plus real_one
                 (real_mult (real_plus (abl9b_xsc m x) (abl9b_hsc m h))
                            (abl9b_xsc m x))) n
            == 1 + (abl9b_ksc m * projT1 x n + abl9b_ksc m * projT1 h n)
                   * (abl9b_ksc m * projT1 x n)).
  { rewrite (real_plus_proj real_one
               (real_mult (real_plus (abl9b_xsc m x) (abl9b_hsc m h))
                          (abl9b_xsc m x)) n).
    rewrite (real_mult_proj (real_plus (abl9b_xsc m x) (abl9b_hsc m h))
                            (abl9b_xsc m x) n).
    rewrite (real_plus_proj (abl9b_xsc m x) (abl9b_hsc m h) n).
    rewrite (abl9b_xsc_proj m x n). rewrite Hh.
    rewrite (b3r_one_proj n). ring. }
  (* 左肢：rhs_ws 逐点（real_inv_proj 于隐藏见证之上精确展开） *)
  unfold abl9b_rhs_ws, abl9b_w.
  rewrite (real_mult_proj (abl9b_hsc m h)
             (real_inv_pos (real_plus real_one
                (real_mult (real_plus (abl9b_xsc m x) (abl9b_hsc m h))
                           (abl9b_xsc m x)))
             (abl9b_sca_Hd m x h Hx Hxh)) n).
  rewrite (HNi n Hni). rewrite Hh. rewrite HD.
  (* 右肢：ext_ws 逐点（件54 ws_proj 直拆）＋①常量桥合流 *)
  rewrite (abl9b_ext_ws_proj m x h N4 HN4 Hx Hxh n Hn4).
  rewrite ablt9_rhscc_km_ksc.
  (* Qinv 内环恒等（件56 a2 ws_dom_eq HD2 同款：ring 于 Qinv 原子内失效） *)
  assert (HD2 : 1 + (abl9b_ksc m * projT1 x n + abl9b_ksc m * projT1 h n)
                   * (abl9b_ksc m * projT1 x n)
             == 1 + (abl9b_ksc m * (projT1 x n + projT1 h n))
                    * (abl9b_ksc m * projT1 x n)) by ring.
  rewrite HD2. reflexivity.
Qed.

(* ── ③ 伴生具名件：abl9b_rhs_close 抽象槽在件54 缩放族上的具名实例
      闭合（件56 a2_56 L1890 案一内联使用之具名化——ws_conv 真实证书
      直接配置，头注四字段⑤「54→59 对接面终裁形」的独立可复用形）──── *)
Theorem ablt9_rhscc_ext_close : forall (x h : Real) (N4 : nat)
  (HN4 : forall n : nat, NatLe N4 n -> Qlt (Qabs (projT1 h n)) (1#4))
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (Hd : real_lt real_zero (real_plus real_one
          (real_mult (real_plus x h) x))),
  forall (eps : Q), QltT 0 eps ->
  sigT (fun M1 : nat => sigT (fun M2 : nat =>
    forall m : nat, (M1 <= m)%nat -> forall n : nat, NatLe M2 n ->
    QltT (Qabs (projT1 (cauchy_real_arctan
                   (abl9b_rhs_clamp1 (abl9b_ext_ws m x h N4 HN4 Hx Hxh))
                   (abl9b_rhs_dom1 (abl9b_ext_ws m x h N4 HN4 Hx Hxh))) n
                - projT1 (cauchy_real_arctan
                   (abl9b_rhs_clamp1 (abl9b_w x h Hd))
                   (abl9b_rhs_dom1 (abl9b_w x h Hd))) n)) eps)).
Proof.
  intros x h N4 HN4 Hx Hxh Hd eps Heps.
  exact (abl9b_rhs_close (fun m : nat => abl9b_ext_ws m x h N4 HN4 Hx Hxh)
           (abl9b_w x h Hd)
           (abl9b_ext_ws_conv x h N4 HN4 Hx Hxh Hd) eps Heps).
Qed.

(* ── ④ B 型全参喂·适配引理形（B5 主交付）：abl9b_rhs_sc_close 具体
      实例——Hconv 槽经逐点桥前提 Hpt 显式适配 discharges。Hpt 之
      无条件均匀形=B6 门工程墙（头注②），取得后本件即 B5 全闭。──── *)
Theorem ablt9_rhscc_sc_close_feed : forall (x h : Real) (N4 : nat)
  (HN4 : forall n : nat, NatLe N4 n -> Qlt (Qabs (projT1 h n)) (1#4))
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (Hd : real_lt real_zero (real_plus real_one
          (real_mult (real_plus x h) x)))
  (Hpt : forall (m n : nat),
    projT1 (abl9b_rhs_ws m x h Hx Hxh) n
    == projT1 (abl9b_ext_ws m x h N4 HN4 Hx Hxh) n),
  forall (eps : Q), QltT 0 eps ->
  sigT (fun M1 : nat => sigT (fun M2 : nat =>
    forall m : nat, (M1 <= m)%nat -> forall n : nat, NatLe M2 n ->
    QltT (Qabs (projT1 (abl9b_rhs_sc m x h Hx Hxh) n
                - projT1 (abl9b_rhs0 x h Hd) n)) eps)).
Proof.
  intros x h N4 HN4 Hx Hxh Hd Hpt eps Heps.
  apply (abl9b_rhs_sc_close x h Hx Hxh Hd).
  intros d Hd0.
  destruct (abl9b_ext_ws_conv x h N4 HN4 Hx Hxh Hd d Hd0)
    as [M1 [Nv HM1]].
  exists M1. exists Nv. intros m Hm n Hn.
  rewrite (Hpt m n). exact (HM1 m Hm n Hn).
  exact Heps.
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                        *)
(*   Lemma/Theorem 名清单 4 = Qed 计数 4 = PA 语句 4，零差；         *)
(*   ①纯 Q 引理提取安全形直测（Obj.magic 计 0 判据）；②③④涉 Real   *)
(*   闭包沿件59 前例以 PA 判据承载（prod 实例化提取器硬错豁免形态）。 *)
(* ============================================================ *)
Print Assumptions ablt9_rhscc_km_ksc.
Print Assumptions ablt9_rhscc_ws_pt_eq.
Print Assumptions ablt9_rhscc_ext_close.
Print Assumptions ablt9_rhscc_sc_close_feed.
Recursive Extraction ablt9_rhscc_km_ksc.
