(* ==========================================================================
   abl_dte_core4.v —— DTPT_Entropy 前件参数消解供给·卷四收尾（参数 116–150）。
   ── 使命：宿主 DTPT_Entropy.v 前件参数登记序收尾段（语句坐标 :2022–:3090，
   22 条语句 35 参数）逐参数消解供给。复核订正如实登记：名义区间第 115–150
   位中第 115 位系卷三已随条交付之溢出参数（:2012 整条已供），本卷实际区间自
   :2022 H_min_q_perm（第 116 位）起，与卷一至卷三零重叠零双供。T＝A 直供
   形（就地构造真构造、零宿主 Entropy 定理使用）；P′ 1 枚；辅助件 17 枚
   （其中 11 枚系卷一/卷二同面就地构造重演，属辅助件非参数位）。35 参数＝32 供给
   ＋3 登记（mkMEval_notHsh0_notHms1／qmul_neq0 前提或结论位否定形，内核
   证体构造性重演；xqz_plus_eq0 结论面与 align_lambda_opt_min 前提面
   （0<=lam<=1 记号位）各以拆分双单向／currying 拆分供给并如实申报）。39 件
   ＝21 T＋17 辅助＋1 P′，全 Qed；宿主件零字节动，零 Require 宿主。
   ── 依赖：stdlib（QArith.QArith／Qabs、List、Arith Lia、Permutation、
   Extraction）＋基座 DTPT（xq_Qle_bool_le／xq_abs 系／P0_sorted／SortedQ／
   H_adj／dedup／Qmem／Qeqb 系等在役件即产路出处，同构宿主件头依赖面）。
   ── 对标行：A 直供形正本＝abl_dtd_core1／abl_dte_core1／abl_dte_core2；
   混载旗登记与内核证体重演工艺＝卷二先例；合取位拆分双单向＝卷一先例。
   ── 构造性注记：零承认式声明、零悬置前提、零经典逻辑、零节变量声明位；
   语句面全 Set 层离散可判定形态；<> 全件两处＝NEQ 参数面逐字透传（非自造，
   证体内 Z 层断言系证明体面非语句位）；名面全 dte_c4_ 前缀；尾置逐件
   Print Assumptions Closed＋定理桶单命令 Separate Extraction，Obj.magic
   零判据。
   ── 编译配方：池 cwd＝沙箱/现役/abl_r85_supply_pool；source Live 库根
   toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 后 nice -19
   rocq c -native-compiler no
   -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
   abl_dte_core4.v；绿判＝EXIT=0／日志零 Error／.vo 头 8 字节
   436f7121 00015ff4／.vo 新于 .v；第五证 rocq check；产物只落本池。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

Require DTPT.
Import DTPT.DTPT.

(* ============================================================ *)
(* 〇 数据层承载副本（宿主 :34/:44/:47/:921/:1058/:1126/:1193/:1250/          *)
(*    :1662/:1752/:1809/:1811/:1937/:1939/:2285/:2900/:62-:76 现档逐字       *)
(*    同构，dte_c4_ 前缀隔离；H_ms/H_adj/P0/Pinf/dedup 系经基座 DTPT          *)
(*    只读直消不另副本。宿主 :1195 all_same 承载副本随 :2012 双供件复核撤除    *)
(*    一并撤除（参数 114-115 归  卷三，承载义务随条归其已交付件））          *)
(* ============================================================ *)
(* ── 勘注·例外B（ 续编·   修改；标注层追加，上方      *)
(*    〇区原文零改动）：①:2900 应为 :2875——宿主 :2900 系 align_lambda_opt_min      *)
(*    前注记行、:2875 始为 Definition align_lambda_opt 定义位（ 报告 §十一.B 行＋    *)
(*    现档实拍同）。②R5 同行另称 :1058/:1126 系节头邻位松锚（freq_q 实 :1062、      *)
(*    nsum 实 :1132）及 :2285 邻位（me_total 实 :2286）三条，现档实拍相左：宿主      *)
(*    :1058＝Fixpoint freq_q 语句行、:1126＝Fixpoint nsum 语句行、:2285＝Definition     *)
(*    me_total 语句行（节头注释在其上方 :1056/:1124/:2281-2283；:1062/:2286 系构造       *)
(*    末行、:1132 系邻位 Lemma nsum_ext_in 语句行），与本件①总表及例外A 勘注所用        *)
(*    「语句行锚」公约一致——原锚 :1058/:1126/:2285 维持不勘， 三值不按原件转录，口径         *)
(*    差留账候复谳（执行记录＝）。承载副本 18 枚         *)
(*    本体  亲验零漂，仅注记锚位漂； 交付报告 §一.2 同源锚位行随本勘注同口径        *)
(*    留账、报告面零写入。本勘注仅注记面，语句面零动。                            *)

Fixpoint dte_c4_qn (n : nat) : Q :=
  match n with
  | O => 0%Q
  | S k => (1 + dte_c4_qn k)%Q
  end.

Fixpoint dte_c4_freq_q (x : Q) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if Qeq_bool x y then S (dte_c4_freq_q x ys) else dte_c4_freq_q x ys
  end.

Fixpoint dte_c4_nsum (f : Q -> nat) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => (f y + dte_c4_nsum f ys)%nat
  end.

Definition dte_c4_sqsum (l : list Q) : nat :=
  dte_c4_nsum (fun x => dte_c4_freq_q x l) l.

Fixpoint dte_c4_nmax (f : Q -> nat) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => Nat.max (f y) (dte_c4_nmax f ys)
  end.

Definition dte_c4_collide (l : list Q) : Q :=
  dte_c4_qn (dte_c4_sqsum l) / (dte_c4_qn (length l) * dte_c4_qn (length l)).

Definition dte_c4_maxcount (l : list Q) : nat := dte_c4_nmax (fun x => dte_c4_freq_q x l) l.

Definition dte_c4_maxfreq (l : list Q) : Q := dte_c4_qn (dte_c4_maxcount l) / dte_c4_qn (length l).

Definition dte_c4_H_max_q (l : list Q) : Q := 1 - dte_c4_maxfreq l.

Definition dte_c4_H_min_q (l : list Q) : Q := 1 - dte_c4_collide l.

Fixpoint dte_c4_H_devsum (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => Qabs (x - hd 0 (P0 l)) + dte_c4_H_devsum xs
  end.

Definition dte_c4_H_cond (l : list Q) (ctx : list Q) : Q :=
  dte_c4_H_devsum l - dte_c4_H_devsum ctx.

Definition dte_c4_H_freq (l : list Q) : Q :=
  (dte_c4_qn (length l) * dte_c4_qn (length l) - dte_c4_qn (dte_c4_sqsum l))
    / (dte_c4_qn (length l) * dte_c4_qn (length l)).

Definition dte_c4_H_lam (l : list Q) (s : nat) (lam : Q) : Q :=
  lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s).

Definition dte_c4_align_lambda_opt (h0 h1 : Q) : Q :=
  if Qle_bool h0 h1 then 1 else 0.

Record dte_c4_MultiEntropyEval : Type := dte_c4_mkME {
  dte_c4_me_carrier : list Q;        (* 评估承载 *)
  dte_c4_me_Hadj    : Q;             (* 序列熵（相邻差） *)
  dte_c4_me_Hms     : Q;             (* 多重集熵（相异值计数） *)
  dte_c4_me_Hsh     : Q;             (* 香农熵（频域计数） *)
  dte_c4_me_Hcond   : Q              (* 条件熵（上下文依赖度） *)
}.

Definition dte_c4_mkMEval (l : list Q) (ctx : list Q) : dte_c4_MultiEntropyEval :=
  dte_c4_mkME l (H_adj l) (H_ms l) (dte_c4_H_devsum l) (dte_c4_H_cond l ctx).

Definition dte_c4_me_total (m : dte_c4_MultiEntropyEval) : Q :=
  (1 # 4)%Q * (dte_c4_me_Hadj m + dte_c4_me_Hms m + dte_c4_me_Hsh m + dte_c4_me_Hcond m)%Q.

(* ============================================================ *)
(* 一 辅助件区（17 枚·宿主 :123/:171/:187/:275/:308/:314/:475/:513/:632/      *)
(*    :927/:936/:951/:1067/:1083/:1097/:1132/:1141/:1198 现档同构副本——       *)
(*    非参数位，供本件供给定理证明体使用；就地构造 真构造，序工具面        *)
(*    使用基座 DTPT qadd_nonneg/qadd_le（同构宿主 §1 证明体使用面）；          *)
(*    其中 11 枚系卷一/卷二/卷三同面 就地构造 重演（查重登记块（一）      *)
(*    逐枚登记，不入本卷参数账））                         *)
(* ============================================================ *)
(* ── 勘注·例外A（ 续编·   修改；标注层追加，上方      *)
(*    辅助件区锚位表原文零改动）：本表 18 锚对 17 枚，差一系 :275 悬空锚——宿主        *)
(*    :275＝xq_sortQ_insert（ 报告 §十一.A 行＋现档实拍同），本件无该副本；      *)
(*    freq_q_le_length 实锚宿主 :1064、freq_q_app 实锚宿主 :1073，表内 :1067/:1097      *)
(*    系松位（:1067 系 freq_q_le_length 证体首行、:1097 系 freq_q_perm 证体行）；        *)
(*    勘后实效锚集 17 枚与  §二 亲验清单逐位吻合。17 枚语句面本体逐字同构零漂，        *)
(*    参数账/编译/红线零影响；本勘注仅注记面，语句面零动。                            *)

Lemma dte_c4_qn_nonneg : forall n : nat, 0 <= dte_c4_qn n.
Proof.
  induction n as [| k IH].
  - apply Qle_refl.
  - simpl. apply qadd_nonneg.
    + apply (Qlt_le_weak 0 1). reflexivity.
    + exact IH.
Qed.

Lemma dte_c4_qn_S_pos : forall k : nat, 0 < dte_c4_qn (S k).
Proof.
  intros k. simpl. apply (Qlt_le_trans 0 1 (1 + dte_c4_qn k)%Q).
  - reflexivity.
  - pose proof (qadd_le 1 1 0 (dte_c4_qn k) (Qle_refl 1) (dte_c4_qn_nonneg k))
      as HH. simpl in HH. exact HH.
Qed.

Lemma dte_c4_qn_add : forall a b : nat, dte_c4_qn (a + b)%nat == dte_c4_qn a + dte_c4_qn b.
Proof.
  induction a as [| a IH]; intros b.
  - simpl. rewrite Qplus_0_l. reflexivity.
  - simpl. rewrite IH. ring.
Qed.

Lemma dte_c4_freq_q_le_length : forall (x : Q) (l : list Q),
  (dte_c4_freq_q x l <= length l)%nat.
Proof.
  intros x. induction l as [| y ys IH].
  - simpl. lia.
  - simpl. destruct (Qeq_bool x y); lia.
Qed.

Lemma dte_c4_freq_q_app : forall (x : Q) (l p : list Q),
  dte_c4_freq_q x (l ++ p) = (dte_c4_freq_q x l + dte_c4_freq_q x p)%nat.
Proof.
  intros x l p. induction l as [| a l IH].
  - reflexivity.
  - simpl. destruct (Qeq_bool x a); rewrite IH; lia.
Qed.

(* 卷二参数 53 面同面重演（freq_q 置换不变；辅助件非参数位） *)
Lemma dte_c4_freq_q_perm : forall (x : Q) (l p : list Q),
  Permutation l p -> dte_c4_freq_q x l = dte_c4_freq_q x p.
Proof.
  intros x l p H.
  induction H as [ | y l' p' Hy IH | y z l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. destruct (Qeq_bool x y); rewrite IH; reflexivity.
  - simpl. destruct (Qeq_bool x y); destruct (Qeq_bool x z); reflexivity.
  - rewrite IH1. exact IH2.
Qed.

(* 卷二参数 57 面同面重演（nsum 逐点外延；辅助件非参数位） *)
Lemma dte_c4_nsum_ext_in : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> f x = g x) -> dte_c4_nsum f l = dte_c4_nsum g l.
Proof.
  intros f g l. induction l as [| y ys IH]; simpl; intros H.
  - reflexivity.
  - rewrite (H y (or_introl eq_refl)).
    rewrite (IH (fun x Hx => H x (or_intror Hx))). reflexivity.
Qed.

(* 卷二参数 58 面同面重演（nsum 置换不变；辅助件非参数位） *)
Lemma dte_c4_nsum_perm : forall (f : Q -> nat) (l p : list Q),
  Permutation l p -> dte_c4_nsum f l = dte_c4_nsum f p.
Proof.
  intros f l p H.
  induction H as [ | x l' p' Hx IH | x y l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. lia.
  - rewrite IH1. exact IH2.
Qed.

(* 卷二参数 65 面同面重演（sqsum 置换不变；辅助件非参数位） *)
Lemma dte_c4_sqsum_perm : forall l p : list Q,
  Permutation l p -> dte_c4_sqsum l = dte_c4_sqsum p.
Proof.
  intros l p H. unfold dte_c4_sqsum.
  rewrite (dte_c4_nsum_ext_in (fun x => dte_c4_freq_q x l) (fun x => dte_c4_freq_q x p) l
             (fun x _ => dte_c4_freq_q_perm x l p H)).
  exact (dte_c4_nsum_perm (fun x => dte_c4_freq_q x p) l p H).
Qed.

(* 宿主 :123 零前提在役件同构副本（非参数位） *)
Lemma dte_c4_H_shannon_q_nonneg : forall l : list Q, 0 <= dte_c4_H_devsum l.
Proof.
  induction l as [| x xs IH]; simpl.
  - apply Qle_refl.
  - apply qadd_nonneg.
    + apply (abs_nonneg (x - hd 0 (P0 (x :: xs)))).
    + exact IH.
Qed.

(* 卷一参数 29 面同面重演（Qeq→Qle；辅助件非参数位） *)
Lemma dte_c4_xq_Qeq_le : forall x y : Q, x == y -> (x <= y)%Q.
Proof.
  intros [nx dx] [ny dy] Hxy. unfold Qeq in Hxy; simpl in Hxy.
  unfold Qle; simpl. lia.
Qed.

(* 卷一参数 7-8 面同面重演（Qle 反对称；辅助件非参数位） *)
Lemma dte_c4_xq_Qle_antisym : forall x y : Q, (x <= y)%Q -> (y <= x)%Q -> x == y.
Proof.
  intros [nx dx] [ny dy] H1 H2. unfold Qle in H1, H2; simpl in H1, H2.
  unfold Qeq; simpl. lia.
Qed.

(* 卷一参数 21-22 面同面重演（乘法非负；辅助件非参数位） *)
Lemma dte_c4_xq_mul_nonneg : forall a b : Q, (0 <= a)%Q -> (0 <= b)%Q -> (0 <= a * b)%Q.
Proof.
  intros [an ad] [bn bd] Ha Hb. unfold Qle in Ha, Hb; simpl in Ha, Hb.
  unfold Qle, Qmult; simpl. lia.
Qed.

(* 卷一参数 5 面同面重演（Qle→判定真；辅助件非参数位） *)
Lemma dte_c4_xq_Qle_bool_true : forall x y : Q, (x <= y)%Q -> Qle_bool x y = true.
Proof.
  intros [nx dx] [ny dy]. unfold Qle, Qle_bool; simpl. intros H.
  destruct (Z.leb (nx * Z.pos dy) (ny * Z.pos dx)) eqn:E.
  - reflexivity.
  - apply Z.leb_gt in E. lia.
Qed.

(* 卷一参数 13 面同面重演（insert_q 置首；辅助件非参数位） *)
Lemma dte_c4_xq_insert_q_head_aux : forall (a b : Q) (bs : list Q),
  (a <= b)%Q -> insert_q a (b :: bs) = a :: b :: bs.
Proof.
  intros a b bs H. simpl. rewrite (dte_c4_xq_Qle_bool_true _ _ H). reflexivity.
Qed.

(* 卷一参数 14 面同面重演（SortedQ 面 P0 幂等；辅助件非参数位——基座 DTPT 的      *)
(* sorted_P0_id 系 StronglySorted 面，SortedQ 归纳版宿主侧独有故重演） *)
Lemma dte_c4_xq_sortQ_P0_id : forall l : list Q, SortedQ l -> P0 l = l.
Proof.
  induction l as [| a rest IH]; intro HS.
  - reflexivity.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    change (P0 (a :: rest)) with (insert_q a (P0 rest)).
    rewrite (IH HSr). destruct rest as [| b bs].
    + reflexivity.
    + apply dte_c4_xq_insert_q_head_aux. apply HFa. left. reflexivity.
Qed.

(* 卷一参数 25 面同面重演（升序⟹偏差熵零化；辅助件非参数位；xq_abs_zero 消基座） *)
Lemma dte_c4_xq_H_shannon_sortQ : forall l : list Q,
  SortedQ l -> dte_c4_H_devsum l == 0.
Proof.
  induction l as [| a rest IH]; intro HS.
  - reflexivity.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    cbn [dte_c4_H_devsum].
    rewrite (dte_c4_xq_sortQ_P0_id (a :: rest) HS).
    change (hd 0 (a :: rest)) with a.
    rewrite (IH HSr). rewrite xq_abs_zero. ring.
Qed.

(* ============================================================ *)
(* 二 卷四供给定理区（21 枚·底册 §一.4 Entropy 登记序参数 116-150 逐位，        *)
(*    语句面＝宿主现档经 dte_c4_ 前缀映射逐字；合取位拆分两件响亮申报见       *)
(*    头注①／交付报告 §三；混载旗 2 条 ：2250/:2968 只登记不在本区；        *)
(*    参数 114-115 系  卷三已交付位，本区零双供）                          *)
(* ============================================================ *)

(* 参数 114-115＝:2012 H_max_q_all_same_zero ——【复核撤除·不供登记】：该语句双参数
   （114-115，第 115 位系本卷名义区跨界位）已由  在盘件 abl_dte_core3.v 整条
   供给（dte_c3_H_max_q_all_same_zero_pair；其交付报告响亮登记「参数 115 随条溢出
   本卷交付、下卷自 :2022 起禁重复供给」）。本稿前版误判「 无在盘件」构成
   双供，复核撤除整语句（ 查重先例：禁重复供给声明）；其使用面 P′
   dte_c4_p_Hmaxq_const_sing 改 就地构造 直证（见三区）。 *)

(* 参数 116＝:2022 H_min_q_perm *)
Theorem dte_c4_H_min_q_perm : forall l p : list Q,
  Permutation l p -> dte_c4_H_min_q l == dte_c4_H_min_q p.
Proof.
  intros l p H. unfold dte_c4_H_min_q.
  (* 卷三参数 104 面（collide_perm）证体内 就地构造 重演 *)
  assert (Hc : dte_c4_collide l == dte_c4_collide p).
  { unfold dte_c4_collide.
    rewrite (dte_c4_sqsum_perm l p H). rewrite (Permutation_length H). reflexivity. }
  rewrite Hc. reflexivity.
Qed.

(* 参数 117＝:2028 H_max_q_perm *)
Theorem dte_c4_H_max_q_perm : forall l p : list Q,
  Permutation l p -> dte_c4_H_max_q l == dte_c4_H_max_q p.
Proof.
  intros l p H. unfold dte_c4_H_max_q.
  (* 卷三参数 109 面（maxfreq_perm）＋参数 108 面（maxcount_perm）＋参数 99/100 面
     （nmax_ext_in/nmax_perm）证体内 就地构造 重演（辅助件非参数位） *)
  assert (Hmf : dte_c4_maxfreq l == dte_c4_maxfreq p).
  { unfold dte_c4_maxfreq. rewrite (Permutation_length H).
    assert (Hmc : dte_c4_maxcount l = dte_c4_maxcount p).
    { unfold dte_c4_maxcount.
      assert (He : forall (f g : Q -> nat) (ys : list Q),
                  (forall x : Q, In x ys -> f x = g x) ->
                  dte_c4_nmax f ys = dte_c4_nmax g ys).
      { intros f g ys. induction ys as [| u us IH]; simpl; intros Hd.
        - reflexivity.
        - rewrite (Hd u (or_introl eq_refl)).
          rewrite (IH (fun x Hx => Hd x (or_intror Hx))). reflexivity. }
      rewrite (He (fun x => dte_c4_freq_q x l) (fun x => dte_c4_freq_q x p) l
                 (fun x _ => dte_c4_freq_q_perm x l p H)).
      assert (Hp : forall (f : Q -> nat) (ys zs : list Q),
                  Permutation ys zs -> dte_c4_nmax f ys = dte_c4_nmax f zs).
      { intros f ys zs Hy.
        induction Hy as [ | x ys' zs' Hx IH | x z ys' | ys' ys'' zs' Ha IH1 Hb IH2 ].
        - reflexivity.
        - simpl. rewrite IH. reflexivity.
        - simpl. lia.
        - rewrite IH1. exact IH2. }
      exact (Hp (fun x => dte_c4_freq_q x p) l p H). }
    rewrite Hmc. reflexivity. }
  rewrite Hmf. reflexivity.
Qed.

(* 参数 118-119＝:2082 me2_abs_sub_triangle *)
Theorem dte_c4_me2_abs_sub_triangle : forall a b : Q,
  (0 <= a)%Q -> (0 <= b)%Q -> (Qabs (a - b) <= a + b)%Q.
Proof.
  intros a b Ha Hb.
  destruct (Qle_dec' a b) as [Hab | Hba].
  - (* 支一 a <= b：|a-b| = -(a-b) = b-a，经 (a+b)-(b-a) = 2a >= 0 *)
    assert (Hneg : (a - b <= 0)%Q).
    { apply (proj2 (Qle_0_sub' (a - b) 0)).
      assert (Hr : (0 - (a - b))%Q == b - a) by ring.
      rewrite Hr. apply (proj1 (Qle_0_sub' a b)). exact Hab. }
    rewrite (abs_neg (a - b) Hneg).
    assert (Heq : (- (a - b))%Q == b - a) by ring.
    rewrite Heq.
    apply (proj2 (Qle_0_sub' (b - a) (a + b))).
    assert (Hr2 : ((a + b) - (b - a))%Q == a + a) by ring.
    rewrite Hr2. apply qadd_nonneg; exact Ha.
  - (* 支二 b <= a：|a-b| = a-b，经 (a+b)-(a-b) = 2b >= 0 *)
    assert (Hpos : (0 <= a - b)%Q).
    { apply (proj1 (Qle_0_sub' b a)). exact Hba. }
    rewrite (abs_eq (a - b) Hpos).
    apply (proj2 (Qle_0_sub' (a - b) (a + b))).
    assert (Hr3 : ((a + b) - (a - b))%Q == b + b) by ring.
    rewrite Hr3. apply qadd_nonneg; exact Hb.
Qed.

(* 参数 120＝:2115 me2_dedup_len_ge1（<> 参数面逐字透传） *)
Theorem dte_c4_me2_dedup_len_ge1 : forall l : list Q,
  l <> [] -> (1 <= length (dedup l))%nat.
Proof.
  intros [| x xs] H.
  - exfalso. apply H. reflexivity.
  - cbn [dedup length]. lia.
Qed.

(* 参数 121＝:2217 mkMEval_Hms_ge1（<> 参数面逐字透传） *)
Theorem dte_c4_mkMEval_Hms_ge1 : forall (l ctx : list Q),
  l <> [] -> (1 <= dte_c4_me_Hms (dte_c4_mkMEval l ctx))%Q.
Proof.
  intros l ctx Hl.
  unfold dte_c4_mkMEval. cbn [dte_c4_me_Hms].
  unfold H_ms.
  assert (Hn : (1 <= length (dedup l))%nat)
    by (apply dte_c4_me2_dedup_len_ge1; exact Hl).
  assert (Hz : (1 <= Z.of_nat (length (dedup l)))%Z) by lia.
  unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* 参数 123＝:2306 me_total_nonneg_guarded *)
Theorem dte_c4_me_total_nonneg_guarded : forall (l ctx : list Q),
  (dte_c4_H_devsum ctx <= dte_c4_H_devsum l)%Q ->
  (0 <= dte_c4_me_total (dte_c4_mkMEval l ctx))%Q.
Proof.
  intros l ctx Hle.
  unfold dte_c4_me_total. unfold dte_c4_mkMEval.
  cbn [dte_c4_me_Hadj dte_c4_me_Hms dte_c4_me_Hsh dte_c4_me_Hcond].
  (* 卷一参数 27 面（H_cond_nonneg_guarded）证体内 就地构造 重演 *)
  assert (Hc : (0 <= dte_c4_H_cond l ctx)%Q).
  { unfold dte_c4_H_cond.
    apply (proj1 (Qle_0_sub' (dte_c4_H_devsum ctx) (dte_c4_H_devsum l))).
    exact Hle. }
  assert (Hms : (0 <= H_ms l)%Q).
  { unfold H_ms. unfold Qle. simpl. lia. }
  assert (Hsum : (0 <= H_adj l + H_ms l + dte_c4_H_devsum l + dte_c4_H_cond l ctx)%Q).
  { apply qadd_nonneg.
    - apply qadd_nonneg.
      + apply qadd_nonneg; [apply xq_H_adj_nonneg | exact Hms].
      + apply dte_c4_H_shannon_q_nonneg.
    - exact Hc. }
  apply dte_c4_xq_mul_nonneg.
  - (* me2_weight_nonneg 内核（宿主 :2151 零前提件证体内重演） *)
    change (Z.le (0 * 4) (1 * 1))%Z. lia.
  - exact Hsum.
Qed.

(* 参数 124＝:2423 xqz_abs0_eq *)
Lemma dte_c4_xqz_abs0_eq : forall x : Q, Qabs x == 0 -> x == 0.
Proof.
  intros [n d] H. unfold Qeq. destruct n as [| p | p].
  - reflexivity.
  - unfold Qabs in H. simpl in H. discriminate H.
  - unfold Qabs in H. simpl in H. discriminate H.
Qed.

(* 参数 125＝:2432 xqz_sub_eq0 *)
Lemma dte_c4_xqz_sub_eq0 : forall x y : Q, (x - y == 0)%Q -> x == y.
Proof.
  intros x y H.
  assert (Hyx : (y - x == 0)%Q).
  { assert (Hmo : y - x == - (x - y)) by apply xq_minus_opp.
    rewrite Hmo, H. reflexivity. }
  apply (dte_c4_xq_Qle_antisym x y).
  - apply (proj2 (Qle_0_sub' x y)).
    apply dte_c4_xq_Qeq_le. apply Qeq_sym. exact Hyx.
  - apply (proj2 (Qle_0_sub' y x)).
    apply dte_c4_xq_Qeq_le. apply Qeq_sym. exact H.
Qed.

(* 参数 126-128＝:2446 xqz_plus_eq0_le *)
Lemma dte_c4_xqz_plus_eq0_le : forall a b : Q,
  (a + b == 0)%Q -> (0 <= a)%Q -> (0 <= b)%Q -> a == 0.
Proof.
  intros a b Hab Ha Hb.
  assert (Hle : (a + 0 <= a + b)%Q)
    by (apply qadd_le; [apply Qle_refl | exact Hb]).
  rewrite Qplus_0_r in Hle. rewrite Hab in Hle.
  apply (dte_c4_xq_Qle_antisym a 0 Hle Ha).
Qed.

(* 参数 129-131＝:2457 xqz_plus_eq0（结论面 Prop 合取位拆分双单向——  :481
   先例同款，响亮申报见交付报告 §三；_l 系参数 126-128 拆分件复用） *)
Lemma dte_c4_xqz_plus_eq0_l : forall a b : Q,
  (a + b == 0)%Q -> (0 <= a)%Q -> (0 <= b)%Q -> a == 0.
Proof.
  intros a b Hab Ha Hb. exact (dte_c4_xqz_plus_eq0_le a b Hab Ha Hb).
Qed.

Lemma dte_c4_xqz_plus_eq0_r : forall a b : Q,
  (a + b == 0)%Q -> (0 <= a)%Q -> (0 <= b)%Q -> b == 0.
Proof.
  intros a b Hab Ha Hb. rewrite Qplus_comm in Hab.
  exact (dte_c4_xqz_plus_eq0_le b a Hab Hb Ha).
Qed.

(* 参数 132-133＝:2469 xqz_sorted_hd_min *)
Lemma dte_c4_xqz_sorted_hd_min : forall (l : list Q) (z : Q),
  SortedQ l -> In z l -> (hd 0 l <= z)%Q.
Proof.
  intros [| a rest] z HS Hin.
  - destruct Hin.
  - inversion HS as [| c1 c2 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    change (hd 0 (a :: rest)) with a.
    destruct Hin as [Heq | Hin].
    + subst. apply Qle_refl.
    + apply HFa. exact Hin.
Qed.

(* 参数 134＝:2483 xqz_P0_hd_min_all *)
Lemma dte_c4_xqz_P0_hd_min_all : forall (l : list Q) (z : Q),
  In z l -> (hd 0 (P0 l) <= z)%Q.
Proof.
  intros l z Hin.
  apply (dte_c4_xqz_sorted_hd_min (P0 l) z).
  - apply xq_P0_sorted.
  - apply Permutation_in with (l := l).
    + apply D5_P0_perm.
    + exact Hin.
Qed.

(* 参数 135＝:2495 H_shannon_q_zero_sorted（使用参数 129-131 拆分件：合取位
   不重建，双向各取一支） *)
Theorem dte_c4_H_shannon_q_zero_sorted : forall l : list Q,
  dte_c4_H_devsum l == 0 -> SortedQ l.
Proof.
  induction l as [| x xs IH]; intro H.
  - apply sortQ_nil.
  - cbn [dte_c4_H_devsum] in H.
    assert (Ha : Qabs (x - hd 0 (P0 (x :: xs))) == 0).
    { apply (dte_c4_xqz_plus_eq0_l _ _ H
               (abs_nonneg (x - hd 0 (P0 (x :: xs))))
               (dte_c4_H_shannon_q_nonneg xs)). }
    assert (Hs : dte_c4_H_devsum xs == 0).
    { apply (dte_c4_xqz_plus_eq0_r _ _ H
               (abs_nonneg (x - hd 0 (P0 (x :: xs))))
               (dte_c4_H_shannon_q_nonneg xs)). }
    assert (Hxm : x == hd 0 (P0 (x :: xs))).
    { apply dte_c4_xqz_sub_eq0. apply dte_c4_xqz_abs0_eq. exact Ha. }
    apply sortQ_cons.
    + apply IH. exact Hs.
    + rewrite Forall_forall. intros z Hz.
      apply (Qle_trans x (hd 0 (P0 (x :: xs))) z).
      * apply dte_c4_xq_Qeq_le. exact Hxm.
      * apply dte_c4_xqz_P0_hd_min_all. simpl. right. exact Hz.
Qed.

(* 参数 136＝:2550 xqz_dedup_aux_nil *)
Lemma dte_c4_xqz_dedup_aux_nil : forall (x : Q) (m : list Q),
  (forall z : Q, Qmem z m -> x == z) -> dedup_aux x m = [].
Proof.
  intros x m. induction m as [| y ys IH]; intro Hall.
  - reflexivity.
  - cbn [dedup_aux].
    assert (Hxy : Qeq_bool x y = true).
    { apply Qeqb_true_of. apply Hall. apply Qmem_refl_cons. }
    rewrite Hxy. apply IH.
    intros z Hz. apply Hall. rewrite Qmem_cons. right. exact Hz.
Qed.

(* 参数 137-139＝:2564 H_ms1_all_eq（卷一参数 33 混载旗位 :749 xq_len1_el 存在形
   不透传——证体内以 dedup 表构造子两分等价重演， 参数 44 先例同款） *)
Theorem dte_c4_H_ms1_all_eq : forall l : list Q,
  (H_ms l == 1)%Q -> forall a b : Q, Qmem a l -> Qmem b l -> a == b.
Proof.
  intro l. intro H.
  assert (Hlen : length (dedup l) = 1%nat).
  { unfold H_ms in H. unfold Qeq in H. simpl in H. lia. }
  destruct (dedup l) as [| c cs] eqn:Hdc.
  - simpl in Hlen. discriminate Hlen.
  - destruct cs as [| d ds].
    + intros a b Ha Hb.
      assert (Qa : Qmem a (dedup l)) by (apply dedup_Qmem_r; exact Ha).
      assert (Qb : Qmem b (dedup l)) by (apply dedup_Qmem_r; exact Hb).
      rewrite Hdc in Qa. rewrite Hdc in Qb.
      rewrite Qmem_cons in Qa. rewrite Qmem_cons in Qb.
      destruct Qa as [Qa | Qa]; [ | unfold Qmem in Qa; simpl in Qa;
                                 discriminate Qa ].
      destruct Qb as [Qb | Qb]; [ | unfold Qmem in Qb; simpl in Qb;
                                 discriminate Qb ].
      rewrite (Qeqb_sym b c) in Qb.
      apply Qeq_bool_eq. apply (Qeqb_trans a c b Qa Qb).
    + simpl in Hlen. discriminate Hlen.
Qed.

(* 参数 140-142＝:2652 H_shannon_q_perm_inv_if_sorted *)
Theorem dte_c4_H_shannon_q_perm_inv_if_sorted : forall l p : list Q,
  Permutation l p -> SortedQ l -> SortedQ p -> dte_c4_H_devsum l == dte_c4_H_devsum p.
Proof.
  intros l p _Hp Hl Hpp.
  rewrite (dte_c4_xq_H_shannon_sortQ l Hl).
  rewrite (dte_c4_xq_H_shannon_sortQ p Hpp).
  reflexivity.
Qed.

(* 参数 143＝:2787 nmax_mono *)
Lemma dte_c4_nmax_mono : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> (f x <= g x)%nat) -> (dte_c4_nmax f l <= dte_c4_nmax g l)%nat.
Proof.
  intros f g l. induction l as [| a t IH]; simpl; intros H.
  - lia.
  - assert (H1 : (f a <= g a)%nat) by (apply H; left; reflexivity).
    assert (H2 : (dte_c4_nmax f t <= dte_c4_nmax g t)%nat)
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    lia.
Qed.

(* 参数 144＝:2905 align_lambda_opt_min（源前提 (0 <= lam <= 1)%Q 系 Qle 合取
   记号位，currying 等价拆双前提，响亮申报见交付报告 §三） *)
Theorem dte_c4_align_lambda_opt_min : forall (l : list Q) (s : nat) (lam : Q),
  (0 <= lam)%Q -> (lam <= 1)%Q ->
  (dte_c4_H_lam l s (dte_c4_align_lambda_opt (H_adj (P0 l)) (H_adj (Pinf l s)))
   <= dte_c4_H_lam l s lam)%Q.
Proof.
  intros l s lam Hlam0 Hlam1.
  unfold dte_c4_H_lam, dte_c4_align_lambda_opt.
  destruct (Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s))) eqn:E.
  - (* h0 <= h1：λ* = 1，最优值 = h0 *)
    assert (Hd : (0 <= lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                       - (1 * H_adj (P0 l) + (1 - 1) * H_adj (Pinf l s)))%Q).
    { assert (Er : lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                 - (1 * H_adj (P0 l) + (1 - 1) * H_adj (Pinf l s))
                 == (1 - lam) * (H_adj (Pinf l s) - H_adj (P0 l))) by ring.
      rewrite Er. apply dte_c4_xq_mul_nonneg.
      + apply (proj1 (Qle_0_sub' lam 1)). exact Hlam1.
      + apply (proj1 (Qle_0_sub' _ _)). apply xq_Qle_bool_le. exact E. }
    apply (proj2 (Qle_0_sub' _ _)). exact Hd.
  - (* h0 > h1：λ* = 0，最优值 = h1 *)
    assert (Hge : (H_adj (Pinf l s) <= H_adj (P0 l))%Q)
      by (apply Qle_bool_false_le; exact E).
    assert (Hd : (0 <= lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                       - (0 * H_adj (P0 l) + (1 - 0) * H_adj (Pinf l s)))%Q).
    { assert (Er : lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                 - (0 * H_adj (P0 l) + (1 - 0) * H_adj (Pinf l s))
                 == lam * (H_adj (P0 l) - H_adj (Pinf l s))) by ring.
      rewrite Er. apply dte_c4_xq_mul_nonneg.
      + exact Hlam0.
      + apply (proj1 (Qle_0_sub' _ _)). exact Hge. }
    apply (proj2 (Qle_0_sub' _ _)). exact Hd.
Qed.

(* 参数 147-148＝:3050 collide_app_eq（卷三参数 113 同面桥与 ：1000/:1008/:2968
   否定内核于证体内 Hk/Hkq/Hkm 局部量化断言 就地构造 重演） *)
Theorem dte_c4_collide_app_eq : forall l1 l2 : list Q,
  (0 < length l1)%nat -> (0 < length l2)%nat ->
  dte_c4_collide (l1 ++ l2) ==
    (dte_c4_qn (length l1) / dte_c4_qn (length l1 + length l2)%nat)
      * (dte_c4_qn (length l1) / dte_c4_qn (length l1 + length l2)%nat) * dte_c4_collide l1
    + (dte_c4_qn (length l2) / dte_c4_qn (length l1 + length l2)%nat)
      * (dte_c4_qn (length l2) / dte_c4_qn (length l1 + length l2)%nat) * dte_c4_collide l2
    + (dte_c4_qn (dte_c4_nsum (fun x => dte_c4_freq_q x l2) l1)
       + dte_c4_qn (dte_c4_nsum (fun x => dte_c4_freq_q x l1) l2))
      / (dte_c4_qn (length l1 + length l2)%nat * dte_c4_qn (length l1 + length l2)%nat).
Proof.
  intros l1 l2 H1 H2.
  (* 否定形混载旗位（宿主 :1000/:1008/:2968）之证体内构造性内核重演 *)
  assert (Hk : forall y : Q, (0 < y)%Q -> ~ (y == 0)).
  { intros y Hpy Heq. rewrite Heq in Hpy. exact (Qlt_irrefl 0 Hpy). }
  assert (Hkq : forall n : nat, (0 < n)%nat -> (0 < dte_c4_qn n)%Q).
  { intros n Hn. destruct n as [| m].
    - exfalso. lia.
    - apply dte_c4_qn_S_pos. }
  assert (Hkm : forall x y : Q, ~ (x == 0) -> ~ (y == 0) -> ~ (x * y == 0)).
  { intros [xn xd] [yn yd] Hx Hy Hxy.
    assert (Hxn : (xn <> 0)%Z).
    { intros Hz. apply Hx. unfold Qeq. simpl. rewrite Hz. reflexivity. }
    assert (Hyn : (yn <> 0)%Z).
    { intros Hz. apply Hy. unfold Qeq. simpl. rewrite Hz. reflexivity. }
    unfold Qeq, Qmult in Hxy. simpl in Hxy.
    rewrite ? Z.mul_1_r in Hxy.
    apply Z.mul_eq_0 in Hxy.
    destruct Hxy as [E | E]; [exact (Hxn E) | exact (Hyn E)]. }
  (* 卷二参数 57 面 sqsum 拼接精确分解内核（nsum_app/nsum_ext_in 辅助件链） *)
  assert (Hsq : dte_c4_sqsum (l1 ++ l2) =
    (dte_c4_sqsum l1 + dte_c4_sqsum l2
     + dte_c4_nsum (fun x => dte_c4_freq_q x l2) l1
     + dte_c4_nsum (fun x => dte_c4_freq_q x l1) l2)%nat).
  { (* nsum_app 内核（宿主 :2685 零前提件）证体内量化重演 *)
    assert (Hap : forall (f : Q -> nat) (ys zs : list Q),
                dte_c4_nsum f (ys ++ zs)
                = (dte_c4_nsum f ys + dte_c4_nsum f zs)%nat).
    { intros f ys zs. induction ys as [| u us IH].
      - reflexivity.
      - simpl. rewrite IH. lia. }
    unfold dte_c4_sqsum. rewrite Hap.
    rewrite (dte_c4_nsum_ext_in (fun x => dte_c4_freq_q x (l1 ++ l2))
                       (fun x => (dte_c4_freq_q x l1 + dte_c4_freq_q x l2)%nat) l1
             (fun x _ => dte_c4_freq_q_app x l1 l2)).
    rewrite (dte_c4_nsum_ext_in (fun x => dte_c4_freq_q x (l1 ++ l2))
                       (fun x => (dte_c4_freq_q x l1 + dte_c4_freq_q x l2)%nat) l2
             (fun x _ => dte_c4_freq_q_app x l1 l2)).
    (* nsum_add 内核（宿主 :2695 零前提件）证体内量化重演 *)
    assert (Hna : forall (f g : Q -> nat) (ys : list Q),
                dte_c4_nsum (fun x => (f x + g x)%nat) ys
                = (dte_c4_nsum f ys + dte_c4_nsum g ys)%nat).
    { intros f g ys. induction ys as [| u us IH].
      - reflexivity.
      - simpl. rewrite IH. lia. }
    rewrite (Hna (fun x => dte_c4_freq_q x l1) (fun x => dte_c4_freq_q x l2) l1).
    rewrite (Hna (fun x => dte_c4_freq_q x l1) (fun x => dte_c4_freq_q x l2) l2).
    lia. }
  assert (Hnn : (0 < length l1 + length l2)%nat) by lia.
  assert (HN : ~ (dte_c4_qn (length l1 + length l2)%nat == 0))
    by (apply (Hk _ (Hkq _ Hnn))).
  assert (Ha : ~ (dte_c4_qn (length l1) == 0)) by (apply (Hk _ (Hkq _ H1))).
  assert (Hb : ~ (dte_c4_qn (length l2) == 0)) by (apply (Hk _ (Hkq _ H2))).
  assert (HPP1 : ~ (dte_c4_qn (length l1) * dte_c4_qn (length l1) == 0))
    by (apply Hkm; assumption).
  assert (HPP2 : ~ (dte_c4_qn (length l2) * dte_c4_qn (length l2) == 0))
    by (apply Hkm; assumption).
  assert (HN2 : ~ (dte_c4_qn (length l1) + dte_c4_qn (length l2) == 0)).
  { intros Zc. apply HN. rewrite dte_c4_qn_add. exact Zc. }
  assert (HNN2 : ~ ((dte_c4_qn (length l1) + dte_c4_qn (length l2))
                    * (dte_c4_qn (length l1) + dte_c4_qn (length l2)) == 0))
    by (apply Hkm; exact HN2).
  unfold dte_c4_collide.
  rewrite length_app.
  rewrite Hsq.
  rewrite ! dte_c4_qn_add.
  field; repeat split; assumption.
Qed.

(* 参数 149-150＝:3090 H_freq_app_eq（卷三参数 113 H_freq_eq_bridge 同面桥证体内
   重演——150 参数收尾位） *)
Theorem dte_c4_H_freq_app_eq : forall l1 l2 : list Q,
  (0 < length l1)%nat -> (0 < length l2)%nat ->
  dte_c4_H_freq (l1 ++ l2) ==
    (dte_c4_qn (length l1) / dte_c4_qn (length l1 + length l2)%nat)
      * (dte_c4_qn (length l1) / dte_c4_qn (length l1 + length l2)%nat) * dte_c4_H_freq l1
    + (dte_c4_qn (length l2) / dte_c4_qn (length l1 + length l2)%nat)
      * (dte_c4_qn (length l2) / dte_c4_qn (length l1 + length l2)%nat) * dte_c4_H_freq l2
    + 2 * (dte_c4_qn (length l1) / dte_c4_qn (length l1 + length l2)%nat)
        * (dte_c4_qn (length l2) / dte_c4_qn (length l1 + length l2)%nat)
    - (dte_c4_qn (dte_c4_nsum (fun x => dte_c4_freq_q x l2) l1)
       + dte_c4_qn (dte_c4_nsum (fun x => dte_c4_freq_q x l1) l2))
      / (dte_c4_qn (length l1 + length l2)%nat * dte_c4_qn (length l1 + length l2)%nat).
Proof.
  intros l1 l2 H1 H2.
  assert (Hk : forall y : Q, (0 < y)%Q -> ~ (y == 0)).
  { intros y Hpy Heq. rewrite Heq in Hpy. exact (Qlt_irrefl 0 Hpy). }
  assert (Hkq : forall n : nat, (0 < n)%nat -> (0 < dte_c4_qn n)%Q).
  { intros n Hn. destruct n as [| m].
    - exfalso. lia.
    - apply dte_c4_qn_S_pos. }
  assert (Hkm : forall x y : Q, ~ (x == 0) -> ~ (y == 0) -> ~ (x * y == 0)).
  { intros [xn xd] [yn yd] Hx Hy Hxy.
    assert (Hxn : (xn <> 0)%Z).
    { intros Hz. apply Hx. unfold Qeq. simpl. rewrite Hz. reflexivity. }
    assert (Hyn : (yn <> 0)%Z).
    { intros Hz. apply Hy. unfold Qeq. simpl. rewrite Hz. reflexivity. }
    unfold Qeq, Qmult in Hxy. simpl in Hxy.
    rewrite ? Z.mul_1_r in Hxy.
    apply Z.mul_eq_0 in Hxy.
    destruct Hxy as [E | E]; [exact (Hxn E) | exact (Hyn E)]. }
  assert (Hnn : (0 < length (l1 ++ l2))%nat) by (rewrite length_app; lia).
  (* 卷三参数 113 面（H_freq_eq_bridge）证体内 就地构造 重演 *)
  assert (HB : forall t : list Q, (0 < length t)%nat ->
               dte_c4_H_freq t == 1 - dte_c4_collide t).
  { intros t Ht. unfold dte_c4_H_freq, dte_c4_collide.
    assert (HPne : ~ (dte_c4_qn (length t) == 0))
      by (apply (Hk _ (Hkq _ Ht))).
    field; assumption. }
  rewrite (HB (l1 ++ l2) Hnn).
  rewrite (dte_c4_collide_app_eq l1 l2 H1 H2).
  assert (B1 : dte_c4_collide l1 == 1 - dte_c4_H_freq l1).
  { pose proof (HB l1 H1) as T. rewrite T. ring. }
  assert (B2 : dte_c4_collide l2 == 1 - dte_c4_H_freq l2).
  { pose proof (HB l2 H2) as T. rewrite T. ring. }
  rewrite B1, B2.
  rewrite (dte_c4_qn_add (length l1) (length l2)).
  assert (HN2 : ~ (dte_c4_qn (length l1) + dte_c4_qn (length l2) == 0)).
  { intros Zc.
    assert (Hpos : (0 < dte_c4_qn (length l1 + length l2)%nat)%Q)
      by (apply (Hkq _); lia).
    rewrite <- dte_c4_qn_add in Zc.
    apply (Hk _ Hpos). exact Zc. }
  assert (HNN2 : ~ ((dte_c4_qn (length l1) + dte_c4_qn (length l2))
                    * (dte_c4_qn (length l1) + dte_c4_qn (length l2)) == 0))
    by (apply Hkm; exact HN2).
  field; repeat split; assumption.
Qed.

(* ============================================================ *)
(* 三 P′ 规范实例区（1 枚·收尾 P′ 形态二实例：就地构造 直证——原稿        *)
(*    使用 :2012 双供件的应用形随复核撤除一并修订，零参数位；余 P′ 因 Qed          *)
(*    预算 41 封顶让位辅助件链，响亮申报见交付报告 §三）                    *)
(* ============================================================ *)

Lemma dte_c4_p_Hmaxq_const_sing : forall a : Q, dte_c4_H_max_q [a; a] == 0.
Proof.
  intro a. unfold dte_c4_H_max_q, dte_c4_maxfreq, dte_c4_maxcount.
  cbn [dte_c4_nmax dte_c4_freq_q dte_c4_qn length].
  rewrite ! Qeq_bool_refl. cbn [dte_c4_freq_q dte_c4_qn Nat.max].
  compute. reflexivity.
Qed.

(* ============================================================ *)
(* 四 检验区（逐定理 Print Assumptions 全 Closed＋定理桶单命令提取）           *)
(* ============================================================ *)

Check dte_c4_qn_nonneg.
Check dte_c4_qn_S_pos.
Check dte_c4_qn_add.
Check dte_c4_freq_q_le_length.
Check dte_c4_freq_q_app.
Check dte_c4_freq_q_perm.
Check dte_c4_nsum_ext_in.
Check dte_c4_nsum_perm.
Check dte_c4_sqsum_perm.
Check dte_c4_H_shannon_q_nonneg.
Check dte_c4_xq_Qeq_le.
Check dte_c4_xq_Qle_antisym.
Check dte_c4_xq_mul_nonneg.
Check dte_c4_xq_Qle_bool_true.
Check dte_c4_xq_insert_q_head_aux.
Check dte_c4_xq_sortQ_P0_id.
Check dte_c4_xq_H_shannon_sortQ.
Check dte_c4_H_min_q_perm.
Check dte_c4_H_max_q_perm.
Check dte_c4_me2_abs_sub_triangle.
Check dte_c4_me2_dedup_len_ge1.
Check dte_c4_mkMEval_Hms_ge1.
Check dte_c4_me_total_nonneg_guarded.
Check dte_c4_xqz_abs0_eq.
Check dte_c4_xqz_sub_eq0.
Check dte_c4_xqz_plus_eq0_le.
Check dte_c4_xqz_plus_eq0_l.
Check dte_c4_xqz_plus_eq0_r.
Check dte_c4_xqz_sorted_hd_min.
Check dte_c4_xqz_P0_hd_min_all.
Check dte_c4_H_shannon_q_zero_sorted.
Check dte_c4_xqz_dedup_aux_nil.
Check dte_c4_H_ms1_all_eq.
Check dte_c4_H_shannon_q_perm_inv_if_sorted.
Check dte_c4_nmax_mono.
Check dte_c4_align_lambda_opt_min.
Check dte_c4_collide_app_eq.
Check dte_c4_H_freq_app_eq.
Check dte_c4_p_Hmaxq_const_sing.

Print Assumptions dte_c4_qn_nonneg.
Print Assumptions dte_c4_qn_S_pos.
Print Assumptions dte_c4_qn_add.
Print Assumptions dte_c4_freq_q_le_length.
Print Assumptions dte_c4_freq_q_app.
Print Assumptions dte_c4_freq_q_perm.
Print Assumptions dte_c4_nsum_ext_in.
Print Assumptions dte_c4_nsum_perm.
Print Assumptions dte_c4_sqsum_perm.
Print Assumptions dte_c4_H_shannon_q_nonneg.
Print Assumptions dte_c4_xq_Qeq_le.
Print Assumptions dte_c4_xq_Qle_antisym.
Print Assumptions dte_c4_xq_mul_nonneg.
Print Assumptions dte_c4_xq_Qle_bool_true.
Print Assumptions dte_c4_xq_insert_q_head_aux.
Print Assumptions dte_c4_xq_sortQ_P0_id.
Print Assumptions dte_c4_xq_H_shannon_sortQ.
Print Assumptions dte_c4_H_min_q_perm.
Print Assumptions dte_c4_H_max_q_perm.
Print Assumptions dte_c4_me2_abs_sub_triangle.
Print Assumptions dte_c4_me2_dedup_len_ge1.
Print Assumptions dte_c4_mkMEval_Hms_ge1.
Print Assumptions dte_c4_me_total_nonneg_guarded.
Print Assumptions dte_c4_xqz_abs0_eq.
Print Assumptions dte_c4_xqz_sub_eq0.
Print Assumptions dte_c4_xqz_plus_eq0_le.
Print Assumptions dte_c4_xqz_plus_eq0_l.
Print Assumptions dte_c4_xqz_plus_eq0_r.
Print Assumptions dte_c4_xqz_sorted_hd_min.
Print Assumptions dte_c4_xqz_P0_hd_min_all.
Print Assumptions dte_c4_H_shannon_q_zero_sorted.
Print Assumptions dte_c4_xqz_dedup_aux_nil.
Print Assumptions dte_c4_H_ms1_all_eq.
Print Assumptions dte_c4_H_shannon_q_perm_inv_if_sorted.
Print Assumptions dte_c4_nmax_mono.
Print Assumptions dte_c4_align_lambda_opt_min.
Print Assumptions dte_c4_collide_app_eq.
Print Assumptions dte_c4_H_freq_app_eq.
Print Assumptions dte_c4_p_Hmaxq_const_sing.

(* ============================================================ *)
(* 五 提取检验区（红线四：可提取验证，Obj.magic 计数＝0 判据）            *)
(*    定理桶：单条 Separate Extraction（  避坑——本件          *)
(*    仅此一条命令；39 结论面全数 Prop 离散承载，按家族提取擦除          *)
(*    惯例归约占位）。数据层真提取面＝19 承载/记录副本（qn/freq_q/       *)
(*    nsum/sqsum/nmax/H_devsum/H_freq 真实现），归                      *)
(*    独立检验件 _dte_c4_probe.v 定向  另桶（分桶       *)
(*    工艺执行位，Obj.magic 双桶分桶归因见交付报告）。                   *)
(* ============================================================ *)

Set Extraction Output Directory "_log/dte_t12".
Separate Extraction dte_c4_qn_nonneg dte_c4_qn_S_pos dte_c4_qn_add
  dte_c4_freq_q_le_length dte_c4_freq_q_app dte_c4_freq_q_perm
  dte_c4_nsum_ext_in dte_c4_nsum_perm dte_c4_sqsum_perm
  dte_c4_H_shannon_q_nonneg dte_c4_xq_Qeq_le dte_c4_xq_Qle_antisym
  dte_c4_xq_mul_nonneg dte_c4_xq_Qle_bool_true dte_c4_xq_insert_q_head_aux
  dte_c4_xq_sortQ_P0_id dte_c4_xq_H_shannon_sortQ
  dte_c4_H_min_q_perm dte_c4_H_max_q_perm
  dte_c4_me2_abs_sub_triangle dte_c4_me2_dedup_len_ge1
  dte_c4_mkMEval_Hms_ge1 dte_c4_me_total_nonneg_guarded
  dte_c4_xqz_abs0_eq dte_c4_xqz_sub_eq0 dte_c4_xqz_plus_eq0_le
  dte_c4_xqz_plus_eq0_l dte_c4_xqz_plus_eq0_r dte_c4_xqz_sorted_hd_min
  dte_c4_xqz_P0_hd_min_all dte_c4_H_shannon_q_zero_sorted
  dte_c4_xqz_dedup_aux_nil dte_c4_H_ms1_all_eq
  dte_c4_H_shannon_q_perm_inv_if_sorted dte_c4_nmax_mono
  dte_c4_align_lambda_opt_min dte_c4_collide_app_eq dte_c4_H_freq_app_eq
  dte_c4_p_Hmaxq_const_sing.
