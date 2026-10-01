(* ==========================================================================)
   abl_arctan_diff_45.v — 9a-乙 主公式闭合推进（X45 形：③N 等步链）         
   消融批 · arctan 差公式件四片（依赖：自包含新件 Require 件 20/件 21）           
   ── 选型自主申明·构造性注记（切片规格两案择一）：────────────────────────────────
   择新件案：件 20（X19'''' 正本 674 行 md5 d8111457）与件 21（X24' 正本 689 行
   md5 c4fdf205）各系前任认证闭合件（对账三联零差）；原地续作将扰动其 PA 清单、
   对账三联与编译证据链并强制重编两正本。现以 Require 直耗两正本（零触碰）， 
   两正本 md5 池内与落件区逐一 SAME 实证（E12）。
   ── 件21 互补关系判定（切片规格指定先实读）────────────────────────────────
   件21=X19' 登记册 §四·1 (a)(b)(c) 三点名全数落件：w 构造/投影/证书无关对齐+
   1+w² 恒等桥（除法形+核形）+w 增量恒等桥（除法形+核形）+8/15 界域证书——
   分段点②「Real证书桥」已由件 21 闭合，主公式装配直接 Require 使用，本件不重做。
   ── 本片范围·数学使命（切片规格 ≤1h；②桥既闭，按序推 ③N 等步链+装配供给）：────
   1. 基建 abl9_arctan_arg_wd：arctan 实参终近逐点相等 → real_eq 结果相等
      （abl9_brg_pt_eq 使用形；装配 T_N↔h 运输与 real_inv_pos_ext 换证所必需
      ——证书不同则 real_inv_pos 早项不同，逐点等失效，必走终近等+本件升层）。
   2. 遗留①补齐 abl9_Hcert_real（X19''''登记册 遗留① 点名「Real 层单发包装
      未交付」）：Hx/Hh4 → real_lt real_zero (1+(x+h)x)——eps:=1/2、N:=Hh4
      见证（非 0：Hh4 系终近界，早项无控；D1 于 n≥N 支单发）。
   3. ③N 等步链【本片闭合】abl9_const_chain：一致步估计（const_crit 原生形，
      基点走 abl9_powN s i 迭代和）+ |s|<delta → real_eq (phi (N 步和)) (phi 0)
      ——对 N 归纳+real_eq_trans 链；逐步=abl9_const_crit 单发（其结论
      real_eq (phi (a+s)) (phi a) 中 a+s 与 abl9_powN s (S i) 经 iota 转换同
      一）。诚实申明：登记册「eps/(2N)预算」系直接多步估计路线之预算；本件改
      走逐步 const_crit 链（每步恰等化，无 1/N 预算需求），数学上更强且更短。
   ── 主定理分段点【续登记】：phi 步界件→装配（详案见登记册 §四）───────────────
   phi 步界件（①b×2+②桥+三角复合）勘定数学核：phi(a+s)−phi(a) 的误差分解=
   err₁−err₂+[s/(1+u²)−Δw·inv(1+w̄²)]，方括号经件 20 abl9_slope_id==s²x/((1+u²)
   (1+(u+s)x))（|·|≤(16/9)|s|²≤(4/9)|s| 预算内）；err₂=①b 于 w 点应用——
   【勘定硬墙】w 点 real_inv_pos 复合的早项含 h 早项（无控），逐点域证书
   （①b 基点界）不可构造——装配陈述须走「路径逐点域证书假设束」形（拟文
   <w 域证书> 占位符的诚实填充=显式假设，Hcert 同理为实参占位符）。
   ── 编译配方：──────────────────────────────────────────────────────────────
   source Live/toolchain/env.sh && bash cpu_guard.sh --
     rocq c -q -native-compiler no -Q /tmp/x45pool "" /tmp/x45pool/abl_arctan_diff_45.v
   （隔离池 /tmp/x45pool=x24pool 链真拷（S01–S11+件16/19/21 就地成段 绿
   vo，S11 md5 d571b0c0与登记册认证 SAME）+x19pool 件20 .v/.vo 真拷（md5
   d8111457 与落件 SAME）；cwd=/tmp/x45work 异地空目录——承 X19'''' 殁因勘定
   禁 cwd 残留 .vo 与池根二义。Require 链退回 S11 单链，S12 出锥。）
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
Require Import abl_arctan_cert_bridge_21.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* 基建 1：arctan 实参终近逐点相等 → 结果 real_eq。                    *)
(*   cauchy_real_arctan 的投影=arctan_partial n (u_n)（arctan_real_proj  *)
(*   reflexivity 单发），故尾部逐点等⟹结果投影尾部逐点等⟹brg_pt_eq。   *)
(*   使用位：装配中 real_inv_pos 换证（brg_w_ext 系 real_eq 非逐点等，  *)
(*   复合 A 后的升降层必经本件）；T_N ↔ h 点态运输。                    *)
(* ============================================================ *)
Lemma abl9_arctan_arg_wd : forall (u v : Real)
  (Hu : forall n : nat, QleT' (Qabs (projT1 u n)) 1)
  (Hv : forall n : nat, QleT' (Qabs (projT1 v n)) 1)
  (N : nat),
  (forall n : nat, (N <= n)%nat -> projT1 u n == projT1 v n) ->
  real_eq (cauchy_real_arctan u Hu) (cauchy_real_arctan v Hv).
Proof.
  intros u v Hu Hv N Hpt.
  apply (abl9_brg_pt_eq _ _ N). intros n Hn.
  rewrite (arctan_real_proj u Hu n).
  rewrite (arctan_real_proj v Hv n).
  rewrite (Hpt n Hn).
  reflexivity.
Qed.

(* ============================================================ *)
(* 遗留①补齐：装配正性证书 Real 层单发包装。                            *)
(*   Hx：|x_n|≤1（拟文逐字）；Hh4：|h|<1/4（real_lt 终近形）。           *)
(*   构造：eps:=1/2、N:=Hh4 见证（早项无控，N 非 0——诚实修正 X19''''    *)
(*   登记册「N:=0」笔误）；n≥N 支：D1（abl9_q_path_den）单发             *)
(*   1+(x_n+h_n)x_n ≥ 3/4 > 1/2。                                       *)
(* ============================================================ *)
Lemma abl9_Hcert_real : forall (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hh4 : real_lt (real_abs h) (real_const (1 # 4))),
  real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x)).
Proof.
  intros x h Hx Hh4.
  destruct Hh4 as [e [He [N HN]]].
  exists (1 # 2). split.
  - assert (Hq : Qlt 0 (1 # 2)) by (unfold Qlt; simpl; lia).
    apply Qlt_to_QltT. exact Hq.
  - exists N. intros n Hn.
    assert (Hlt1 : Qlt e (Qminus (projT1 (real_const (1 # 4)) n)
                                  (projT1 (real_abs h) n)))
      by (apply QltT_to_Qlt; exact (HN n Hn)).
    rewrite (real_const_proj (1 # 4) n) in Hlt1.
    rewrite (real_abs_proj h n) in Hlt1.
    assert (Hlt2 : Qlt (Qabs (projT1 h n)) ((1 # 4) - e)).
    { apply (q_lt_minus_shift e (1 # 4) (Qabs (projT1 h n))). exact Hlt1. }
    assert (Hhn4 : Qle (Qabs (projT1 h n)) (1 # 4)).
    { apply (Qle_trans (Qabs (projT1 h n)) ((1 # 4) - e) (1 # 4)).
      - apply Qlt_le_weak. exact Hlt2.
      - assert (He0 : Qle 0 e) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact He).
        apply (Qle_trans ((1 # 4) - e) (((1 # 4) - e) + 0) (1 # 4)).
        + apply qeq_imp_qle. ring.
        + apply (Qle_trans (((1 # 4) - e) + 0) (((1 # 4) - e) + e) (1 # 4)).
          * apply Qplus_le_compat. apply Qle_refl. exact He0.
          * apply qeq_imp_qle. ring. }
    assert (Hxa : Qle (Qabs (projT1 x n)) 1)
      by (apply (QleT'_to_Qle (Qabs (projT1 x n)) 1); exact (Hx n)).
    pose proof (abl9_q_path_den (projT1 x n) (projT1 h n) Hxa Hhn4) as Hd.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans (1 # 2) (3 # 4)
             (Qminus (projT1 (real_plus real_one
                         (real_mult (real_plus x h) x)) n)
                     (projT1 real_zero n))).
    + unfold Qlt. simpl. lia.
    + assert (HY : projT1 (real_plus real_one (real_mult (real_plus x h) x)) n
                   == 1 + (projT1 x n + projT1 h n) * projT1 x n).
      { rewrite (real_plus_proj real_one (real_mult (real_plus x h) x) n).
        rewrite (real_mult_proj (real_plus x h) x n).
        rewrite (real_plus_proj x h n).
        rewrite (b3r_one_proj n). reflexivity. }
      assert (H0 : Qminus (projT1 (real_plus real_one
                             (real_mult (real_plus x h) x)) n)
                    (projT1 real_zero n)
                   == 1 + (projT1 x n + projT1 h n) * projT1 x n).
      { rewrite HY. cbn [projT1 real_zero]. ring. }
      apply (Qle_trans (3 # 4) (1 + (projT1 x n + projT1 h n) * projT1 x n)
             (Qminus (projT1 (real_plus real_one
                         (real_mult (real_plus x h) x)) n)
                     (projT1 real_zero n))).
      * exact (QleT'_to_Qle (3 # 4)
                 (1 + (projT1 x n + projT1 h n) * projT1 x n) Hd).
      * apply qeq_imp_qle. apply Qeq_sym. exact H0.
Qed.

(* ============================================================ *)
(* ③·N 等步链：迭代和基点 + 逐步常值判据链                              *)
(*   abl9_powN s i := s 的 i 迭代和（t_0=0，t_{i+1}=t_i+s）；            *)
(*   假设=一致步估计（abl9_const_crit 原生使用形，逐基点 i<N）；         *)
(*   结论=real_eq (phi (N 步和)) (phi 0)。                              *)
(*   工法：对 N 归纳；S 步=abl9_const_crit 单发（a+s 与 abl9_powN s      *)
(*   (S N) 经 iota 转换同一，exact 全显式代入）；链=real_eq_trans。      *)
(* ============================================================ *)
Fixpoint abl9_powN (s : Real) (i : nat) : Real :=
  match i with
  | O => real_zero
  | Datatypes.S i' => real_plus (abl9_powN s i') s
  end.

Lemma abl9_const_chain : forall (phi : Real -> Real) (N : nat) (s delta : Real),
  real_lt real_zero delta ->
  real_lt (real_abs s) delta ->
  (forall i : nat, (i < N)%nat ->
     forall (eps eps' : Real), real_lt real_zero eps -> real_lt real_zero eps' ->
     real_le (real_abs (real_plus (phi (real_plus (abl9_powN s i) s))
                        (real_opp (phi (abl9_powN s i)))))
             (real_plus (real_mult eps (real_abs s)) eps')) ->
  real_eq (phi (abl9_powN s N)) (phi real_zero).
Proof.
  intros phi N s delta Hdelta Hspan.
  induction N as [| N IH].
  - intros Hstep. cbn [abl9_powN]. apply real_eq_refl.
  - intros Hstep.
    apply (real_eq_trans (phi (abl9_powN s (Datatypes.S N)))
                         (phi (abl9_powN s N)) (phi real_zero)).
    + exact (abl9_const_crit phi (abl9_powN s N) s delta Hdelta Hspan
               (fun eps eps' Heps Heps' =>
                  Hstep N (Nat.lt_succ_diag_r N) eps eps' Heps Heps')).
    + exact (IH (fun i Hi eps eps' Heps Heps' =>
                   Hstep i (Nat.lt_lt_succ_r _ _ Hi) eps eps' Heps Heps')).
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                            *)
(*   对账三联：Lemma 名清单 3 = Qed 计数 3 = PA 语句 3，零差。          *)
(* ============================================================ *)
Print Assumptions abl9_arctan_arg_wd.
Print Assumptions abl9_Hcert_real.
Print Assumptions abl9_const_chain.

(* 提取检验（判据 = 输出 Obj.magic 计数 0） *)
Recursive Extraction abl9_arctan_arg_wd abl9_Hcert_real abl9_const_chain.
