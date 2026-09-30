(* ==========================================================================)
   abl_arctan_diff_20.v — X19'' 施工段（消融交付·9a-乙 三片：接 X19' 断点）  
   消融批 · arctan 差公式件三片（依赖：自包含新件 Require 件 19）           
   ── 本片范围·数学使命（切片规格 ≤1h，②③推进+主定理，1h到点即停断点登记）：───────
   ②Real 证书桥【推进】：斜率合成精确恒等 abl9_slope_id——链式规则复合斜率的
   除法形 Q 层恒等式（=X19'登记册 §四·4 点名「斜率合成精确恒等=wsq_ring_id 的
   除法形」）：w:=（u−v)/(1+uv) 的 (u+s) 处增量乘 (1+uv)²/((1+u²)(1+v²))
   （=1/(1+w²)，abl9_wsq_div_id 之逆）与复合斜率替换 s/(1+u²) 之差==
   s²v/((1+(u+s)v)(1+u²))——phi'(t)=0 的精确代数核（O(s²) 小项显式）；
   分母非零旁支经 abl9_q_pos_sq（1+q² 非零，Q 平方非负构造）+两给定直立。
   ③常值判据【推进：小跨度版闭合】：abl9_real_tail_bnd（柯西实数的逐点终近
   上界——构造性，cauchy eps=1 单发+abs_shift 三角）＋abl9_const_crit（小跨度
   常值判据：「基点 a 处增量估计对任意 eps/eps' 成立（步长 |s|<delta 一致）→
   real_eq (phi(a+s)) (phi a)」）——real_eq 逐点终近形直拆：尾界 B+跨度预算
   c:=eps/(8(B+1))，real_le 双分支（real_lt/real_eq）各产逐点界（real_eq
   分支以 abs_shift三角收敛），单步 3eps/4<eps 闭合。构造性注记：③本片系
   小跨度版（|s|<delta）；N 等步链版（跨 [0,h] 多步+Q→nat ceiling+min/max
   折叠）登记册断点，构造分析随登记。 
   主定理 abl9_atan_diff_formula【断点登记，拟文逐字不动】（X16 件头注）：
   装配剩余=phi 步界件（①b 两次应用+②桥+三角复合）、arctan 合同
   （b5c_arctan_partial_wd 升 real 层）、端点值 phi(0)==0、W(x+h) 与
   h·inv(1+x(x+h)) 的 real_inv_pos_ext对齐；另勘定内点域缺口（见登记册）。
   ── X19'''' 续作登记（第二轮断点推进）─────────────────────────────────
   断点态验定（E12 实文判定）：池副本 414 行版【红】于 abl9_const_crit·
   Htri——unfold AB 全位展开致 Qle_trans 中项缺外层 Qabs（前任停刀点，
   与落件 394 行版差异=本件+Hden+HcB 除法形重证，池版为最新迭代）。
   此番修复 Htri（三角链改走 ||Δ|−MID|+|MID|：abl9_Qabs_wd 配平+
   Qabs_triangle+abl9_Qabs_le_self）。装配供给六件闭合：
   D0 abl9_q_abs_two_sided_le（|t|≤b 双侧解，Qabs 无乘法分配件的两支拆）/
   D1 abl9_q_path_den（路径分母下界 3/4 ≤ 1+(a+t)a 于 |a|≤1、|t|≤1/4
   ——sign a 两支、(a∓1/8)²≥0 配平，63/64 中转）/
   A abl9_arctan_wd_real（b5c_arctan_partial_wd 升 real 层：逐点投影
   路线 arctan_real_proj reflexivity+real_eq_of_zero_diff，免逼近链）/
   C abl9_arctan_zero_pt（零实参 arctan==0）/
   B abl9_w_align（w 复合实参==拟文 RHS 实参：eq_mult_compat+mult_comm
   对齐链，(x+h)+(−x)==h 逐点）/
   C2 abl9_wx_zero（w(x)==0，端点件 phi(0) 之 w 侧）。
   主定理断点【续登记】：剩余=phi 步界件（①b×2+②桥 Real 升层——
   real_inv_pos 近似倒数误差项吸收为真难点——+三角复合）→③ N 等步链
   （h/N 剖分+eps/(2N) 预算）→装配。接续首刀建议=②桥 Real 升层件
   （real_inv_pos_ext 对齐 1+w² 恒等，Q 层输入形 abl9_slope_id 已备）；
   D1 供装配域证书（1+x(x+h) 逐点 ≥3/4→real_lt real_zero 单发）、
   D0 供 |h_n|<1/4 双侧解包。
   ── X19'''' 编译证据（10 轮迭代收敛，FRONT 位，节流合规）──────────────
   source Live/toolchain/env.sh && bash cpu_guard.sh --
     rocq c -q -native-compiler no -Q /tmp/x19pool "" /tmp/x19pool/abl_arctan_diff_20.v
   （cwd=/tmp/x19w4 异地空目录——X19'' 末轮殁因勘定：cwd x19work 残留
   19.vo 与池 -Q 单根二义「matches several files in path」；隔离池
   /tmp/x19pool S01–S11+件16+件19 born-in-place 在链，vo 新鲜度逐一验）。
   绿判四件套：①EXIT=0；②Error 计 0；③vo 魔数=436f7121 00015ff4
   （xxd 实读）；④vo 新于 v。红线四证：PA 语句 17→Closed under the
   global context ×17；Recursive Extraction 输出 Obj.magic 计 0；禁词面
   零 Admitted/Axiom 命中；对账三联 Lemma 17=Qed 17=PA 17 零差。      
   迭代 10 轮（症状→处置）：1 Htri 前任遗留 unfold AB 双位展错→幂等链
   重构；2 Qlt_le_trans 严格/弱型差→Qle_lt_trans；3 Qle_gt_dec 此带
   无名→Qlt_le_dec（S02 房法）；4 Habs 方向→Qeq_sym；5 目标 QleT'
   漏 Qle_to_QleT' 桥；6-8 trans 结构错位/ring 非环等（3/4≤63/64 走
   unfold Qle;simpl;lia）→三分重排；9 replace 产 Leibniz 等式 ring 拒
   →assert-Qeq+Qle_trans桥；10 EXIT=0 全通过。
   ── 编译配方：──────────────────────────────────────────────────────────────
   source Live/toolchain/env.sh && bash cpu_guard.sh --
     rocq c -q -native-compiler no -Q /tmp/x19pool "" /tmp/x19pool/abl_arctan_diff_20.v
   （隔离池 /tmp/x19pool：S01–S11+abl_arctan_diff_16+abl_arctan_diff_19
   born-in-place 绿验（EXIT=0/Closed×6/魔数 436f7121 0001 5ff4/vo 新于 v，
   S11 md5 d571b0c0抽查与登记册 SAME）；Require 链退回 S11 单链，S12 出锥
   ——承 X15''/X16 判定。）
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
Require Import abl_arctan_diff_19.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* ③·基建：Qeq 在 QltT/Id(Qlt_bool) 下不可直接改写——本件新坑，         *)
(*   四传递助手全片复用（QltT 版先行，Qlt 版经 Qlt_to_QltT 复用）        *)
(* ============================================================ *)
Lemma abl9_QltT_transfer_l : forall x y z : Q, x == y -> QltT x z -> QltT y z.
Proof.
  intros x y z Hxy Hlt.
  assert (Hx : Qlt x z) by (apply QltT_to_Qlt; exact Hlt).
  apply Qlt_to_QltT. apply (Qle_lt_trans y x z).
  - apply qeq_imp_qle. apply Qeq_sym. exact Hxy.
  - exact Hx.
Qed.

Lemma abl9_QltT_transfer_r : forall x y z : Q, y == z -> QltT x y -> QltT x z.
Proof.
  intros x y z Hyz Hlt.
  apply Qlt_to_QltT. apply (Qlt_le_trans x y z).
  - apply QltT_to_Qlt. exact Hlt.
  - apply qeq_imp_qle. exact Hyz.
Qed.

Lemma abl9_Qlt_transfer_l : forall x y z : Q, x == y -> Qlt x z -> Qlt y z.
Proof.
  intros x y z Hxy Hlt.
  apply (Qle_lt_trans y x z).
  - apply qeq_imp_qle. apply Qeq_sym. exact Hxy.
  - exact Hlt.
Qed.

Lemma abl9_Qlt_transfer_r : forall x y z : Q, y == z -> Qlt x y -> Qlt x z.
Proof.
  intros x y z Hyz Hlt.
  apply (Qlt_le_trans x y z).
  - exact Hlt.
  - apply qeq_imp_qle. exact Hyz.
Qed.

(* Qeq 在 Qabs 内的正则化 *)
Lemma abl9_Qabs_wd : forall x y : Q, x == y -> Qabs x == Qabs y.
Proof. intros x y H. apply (Qabs_wd x y). exact H. Qed.

(* ============================================================ *)
(* ②·基建：Q 平方非负 → 1+q² 非零（内核复用 S02 Qsquare_nonneg）        *)
(* ============================================================ *)
Lemma abl9_q_pos_sq : forall q : Q, ~ (1 + q * q == 0).
Proof.
  intros q Hp.
  assert (Hs : Qle 0 (q * q)) by apply Qsquare_nonneg.
  assert (H1 : Qle 1 (1 + q * q)).
  { apply (Qle_trans 1 (1 + 0) (1 + q * q)).
    - apply qeq_imp_qle. ring.
    - apply Qplus_le_compat. apply Qle_refl. exact Hs. }
  assert (H2 : Qle (1 + q * q) 0) by (apply qeq_imp_qle; exact Hp).
  assert (H3 : Qle 1 0) by (apply (Qle_trans 1 (1 + q * q) 0); [exact H1 | exact H2]).
  exfalso.
  assert (H01 : Qlt 0 1) by (unfold Qlt; simpl; lia).
  assert (H00 : Qlt 0 0) by (apply (Qlt_le_trans 0 1 0); [exact H01 | exact H3]).
  exact (Qlt_not_le 0 0 H00 (Qle_refl 0)).
Qed.

(* ============================================================ *)
(* ②·斜率合成精确恒等（除法形，phi'(t)=0 的精确代数核）                *)
(* ============================================================ *)
Lemma abl9_slope_id : forall u v s : Q,
  ~ (1 + (u + s) * v == 0) -> ~ (1 + u * v == 0) ->
  s / (1 + u * u)
  - ((u + s - v) / (1 + (u + s) * v) - (u - v) / (1 + u * v))
    * ((1 + u * v) * (1 + u * v) / ((1 + u * u) * (1 + v * v))) ==
  s * s * v / ((1 + (u + s) * v) * (1 + u * u)).
Proof.
  intros u v s H1 H2.
  assert (Hu2 : ~ (1 + u * u == 0)) by apply abl9_q_pos_sq.
  assert (Hv2 : ~ (1 + v * v == 0)) by apply abl9_q_pos_sq.
  field. repeat split; assumption.
Qed.

(* ============================================================ *)
(* ③·辅助：Q 绝对值位移三角（|a| ≤ |a−b|+|b|）                        *)
(* ============================================================ *)
Lemma abl9_abs_shift : forall a b : Q, Qle (Qabs a) (Qabs (a - b) + Qabs b).
Proof.
  intros a b.
  apply (Qle_trans (Qabs a) (Qabs ((a - b) + b)) (Qabs (a - b) + Qabs b)).
  - apply qeq_imp_qle. apply abl9_Qabs_wd. ring.
  - apply Qabs_triangle.
Qed.

(* ============================================================ *)
(* ③·辅助：|x| ≤ x（x ≥ 0 时；Qabs_pos 直立——Htri 预算闭合使用）       *)
(* ============================================================ *)
Lemma abl9_Qabs_le_self : forall x : Q, Qle 0 x -> Qle (Qabs x) x.
Proof. intros x H. apply qeq_imp_qle. apply (Qabs_pos x H). Qed.

(* ============================================================ *)
(* ③·辅助：柯西实数的逐点终近上界（构造性；cauchy eps=1 单发）         *)
(* ============================================================ *)
Lemma abl9_real_tail_bnd : forall x : Real,
  sigT (fun B : Q => And (QltT 0 B)
    (sigT (fun N : nat => forall n : nat, NatLe N n ->
       Qle (Qabs (projT1 x n)) B))).
Proof.
  intros x. destruct x as [u Hu].
  assert (H1 : QltT 0 1) by reflexivity.
  destruct (Hu 1 H1) as [N HN].
  exists (Qabs (u N) + 1).
  split.
  - apply Qlt_to_QltT.
    assert (H1le : Qle 1 (Qabs (u N) + 1)).
    { apply (Qle_trans 1 (1 + 0) (Qabs (u N) + 1)).
      - apply qeq_imp_qle. ring.
      - apply (Qle_trans (1 + 0) (1 + Qabs (u N)) (Qabs (u N) + 1)).
        + apply Qplus_le_compat. apply Qle_refl. apply Qabs_nonneg.
        + apply qeq_imp_qle. ring. }
    apply (Qlt_le_trans 0 1 (Qabs (u N) + 1)).
    + unfold Qlt. simpl. lia.
    + exact H1le.
  - exists N. intros n Hn.
    apply (Qle_trans (Qabs (u n)) (Qabs (u n - u N) + Qabs (u N))
                     (Qabs (u N) + 1)).
    + apply (abl9_abs_shift (u n) (u N)).
    + apply (Qle_trans (Qabs (u n - u N) + Qabs (u N))
                       (1 + Qabs (u N)) (Qabs (u N) + 1)).
      * apply Qplus_le_compat.
        -- apply Qlt_le_weak. apply QltT_to_Qlt.
           apply (HN n N).
           ++ exact Hn.
           ++ apply NatLe_lift. apply Nat.le_refl.
        -- apply Qle_refl.
      * apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* ③·小跨度常值判据：一致增量估计 → real_eq                           *)
(* ============================================================ *)
Lemma abl9_const_crit :
  forall (phi : Real -> Real) (a s delta : Real),
  real_lt real_zero delta ->
  real_lt (real_abs s) delta ->
  (forall (eps eps' : Real), real_lt real_zero eps -> real_lt real_zero eps' ->
     real_le (real_abs (real_plus (phi (real_plus a s)) (real_opp (phi a))))
             (real_plus (real_mult eps (real_abs s)) eps')) ->
  real_eq (phi (real_plus a s)) (phi a).
Proof.
  intros phi a s delta Hdelta Hspan Hstep eps Heps.
  assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  destruct (abl9_real_tail_bnd s) as [B [HB0 [Nb HB]]].
  assert (HBQ : Qlt 0 B) by (apply QltT_to_Qlt; exact HB0).
  assert (HB1 : Qlt 0 (B + 1)).
  { apply (Qlt_le_trans 0 B (B + 1)).
    - exact HBQ.
    - apply (Qle_trans B (B + 0) (B + 1)).
      + apply qeq_imp_qle. ring.
      + apply Qplus_le_compat. apply Qle_refl. unfold Qle. simpl. lia. }
  set (c := (eps / (8 * (B + 1)))%Q).
  assert (Hc0 : Qlt 0 c).
  { unfold c. unfold Qdiv. apply Qmult_lt_0_compat.
    - exact HepsQ.
    - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat.
      + unfold Qlt. simpl. lia.
      + exact HB1. }
  (* 跨度预算：c·B ≤ eps/8 *)
  assert (HB1le : Qle B (B + 1)).
  { apply (Qle_trans B (B + 0) (B + 1)).
    - apply qeq_imp_qle. ring.
    - apply Qplus_le_compat. apply Qle_refl. unfold Qle. simpl. lia. }
  assert (Hden : ~ (B + 1 == 0)).
  { intros Hz.
    assert (H00 : Qlt 0 0) by (apply (Qlt_le_trans 0 (B + 1) 0); [exact HB1 | apply qeq_imp_qle; exact Hz]).
    exact (Qlt_not_le 0 0 H00 (Qle_refl 0)). }
  assert (HcB : Qle (c * B) ((1 # 8) * eps)).
  { apply (Qle_trans (c * B) (c * (B + 1)) ((1 # 8) * eps)).
    - rewrite (Qmult_comm c B). rewrite (Qmult_comm c (B + 1)).
      apply Qmult_le_compat_r.
      + exact HB1le.
      + apply Qlt_le_weak. exact Hc0.
    - apply qeq_imp_qle. unfold c. unfold Qdiv. field. assumption. }
  assert (Hc' : real_lt real_zero (real_const c))
    by (apply real_const_pos_f1; exact Hc0).
  assert (He2 : real_lt real_zero (real_const (eps / 2))).
  { apply real_const_pos_f1. apply Qlt_shift_div_l.
    - reflexivity.
    - simpl. apply QltT_to_Qlt. exact Heps. }
  assert (Hcsn : forall n : nat, NatLe Nb n ->
            Qle (c * Qabs (projT1 s n)) ((1 # 8) * eps)).
  { intros n Hn. apply (Qle_trans (c * Qabs (projT1 s n)) (c * B) ((1 # 8) * eps)).
    - rewrite (Qmult_comm c (Qabs (projT1 s n))). rewrite (Qmult_comm c B).
      apply Qmult_le_compat_r.
      + apply (HB n). exact Hn.
      + apply Qlt_le_weak. exact Hc0.
    - exact HcB. }
  destruct (Hstep (real_const c) (real_const (eps / 2)) Hc' He2) as [Hr | Hr].
  - (* real_lt 分支：∃q>0, ∃M: ∀n≥M: q < bound_n − |Δ_n| *)
    destruct Hr as [q [Hq0 [M Hq]]].
    exists (Nat.max Nb M).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hnb : (Nb <= n)%nat) by lia.
    assert (Hm : (M <= n)%nat) by lia.
    assert (HnNb : NatLe Nb n) by (apply NatLe_lift; exact Hnb).
    set (dn := projT1 (phi (real_plus a s)) n).
    set (an := projT1 (phi a) n).
    assert (Hqn : Qlt q (c * Qabs (projT1 s n) + eps / 2 - Qabs (dn - an))).
    { apply (Qlt_le_trans q
        (projT1 (real_plus (real_mult (real_const c) (real_abs s))
                           (real_const (eps / 2))) n
         - projT1 (real_abs (real_plus (phi (real_plus a s))
                                        (real_opp (phi a)))) n)
        (c * Qabs (projT1 s n) + eps / 2 - Qabs (dn - an))).
      - apply QltT_to_Qlt. apply (Hq n). apply NatLe_lift. exact Hm.
      - apply qeq_imp_qle.
        rewrite (real_plus_proj (real_mult (real_const c) (real_abs s))
                   (real_const (eps / 2)) n).
        rewrite (real_mult_proj (real_const c) (real_abs s) n).
        rewrite (real_const_proj c n).
        rewrite (real_abs_proj s n).
        rewrite (real_abs_proj (real_plus (phi (real_plus a s)) (real_opp (phi a))) n).
        rewrite (real_plus_proj (phi (real_plus a s)) (real_opp (phi a)) n).
        rewrite (real_opp_proj (phi a) n).
        cbn [projT1 real_const real_zero].
        unfold dn, an. reflexivity. }
    assert (Hqn2 : Qlt 0 ((c * Qabs (projT1 s n) + eps / 2 - q) - Qabs (dn - an))).
    { apply (abl9_Qlt_transfer_r 0
               ((c * Qabs (projT1 s n) + eps / 2) - Qabs (dn - an) - q)
               ((c * Qabs (projT1 s n) + eps / 2 - q) - Qabs (dn - an))).
      - field.
      - apply (proj1 (Qlt_minus_iff q
                 (c * Qabs (projT1 s n) + eps / 2 - Qabs (dn - an)))).
        exact Hqn. }
    assert (Hd1 : Qlt (Qabs (dn - an)) (c * Qabs (projT1 s n) + eps / 2)).
    { apply (Qlt_trans (Qabs (dn - an))
             (c * Qabs (projT1 s n) + eps / 2 - q)
             (c * Qabs (projT1 s n) + eps / 2)).
      - apply (proj2 (Qlt_minus_iff (Qabs (dn - an))
                 (c * Qabs (projT1 s n) + eps / 2 - q))). exact Hqn2.
      - apply (proj2 (Qlt_minus_iff (c * Qabs (projT1 s n) + eps / 2 - q)
                 (c * Qabs (projT1 s n) + eps / 2))).
        apply QltT_to_Qlt.
        apply (abl9_QltT_transfer_r 0 q
                 ((c * Qabs (projT1 s n) + eps / 2)
                  - (c * Qabs (projT1 s n) + eps / 2 - q))).
        + apply Qeq_sym.
          assert (Heqq : (c * Qabs (projT1 s n) + eps / 2)
                         - (c * Qabs (projT1 s n) + eps / 2 - q) == q) by ring.
          exact Heqq.
        + exact Hq0. }
    apply Qlt_to_QltT.
    apply (Qlt_le_trans (Qabs (dn - an))
                        (c * Qabs (projT1 s n) + eps / 2) eps).
    + exact Hd1.
    + apply (Qle_trans (c * Qabs (projT1 s n) + eps / 2)
                       ((1 # 8) * eps + (1 # 2) * eps) eps).
      * apply Qplus_le_compat.
        -- apply (Hcsn n HnNb).
        -- apply qeq_imp_qle. field.
      * apply (Qle_trans ((1 # 8) * eps + (1 # 2) * eps) (1 * eps)).
        -- apply (Qle_trans ((1 # 8) * eps + (1 # 2) * eps) ((5 # 8) * eps) (1 * eps)).
           ++ apply qeq_imp_qle. field.
           ++ apply Qmult_le_compat_r.
              ** unfold Qle. simpl. lia.
              ** apply Qlt_le_weak. exact HepsQ.
        -- apply qeq_imp_qle. ring.
  - (* real_eq 分支：| |Δ_n| − bound_n | < eps/8 终近；三角+预算闭合 *)
    assert (He8q : QltT 0 (eps / 8)).
    { apply Qlt_to_QltT. apply Qlt_shift_div_l.
      - reflexivity.
      - simpl. apply QltT_to_Qlt. exact Heps. }
    destruct (Hr (eps / 8) He8q) as [N2 H2].
    exists (Nat.max Nb N2).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hnb : (Nb <= n)%nat) by lia.
    assert (Hn2 : (N2 <= n)%nat) by lia.
    assert (HnNb : NatLe Nb n) by (apply NatLe_lift; exact Hnb).
    set (dn := projT1 (phi (real_plus a s)) n).
    set (an := projT1 (phi a) n).
    set (MID := (c * Qabs (projT1 s n) + eps / 2)%Q).
    set (AB := Qabs (Qabs (dn - an) - MID)%Q).
    assert (H2' : QltT AB (eps / 8)).
    { apply (abl9_QltT_transfer_l
        (Qabs (projT1 (real_abs (real_plus (phi (real_plus a s))
                          (real_opp (phi a)))) n
               - projT1 (real_plus (real_mult (real_const c) (real_abs s))
                                   (real_const (eps / 2))) n))).
      - rewrite (real_abs_proj (real_plus (phi (real_plus a s))
                                  (real_opp (phi a))) n).
        rewrite (real_plus_proj (phi (real_plus a s)) (real_opp (phi a)) n).
        rewrite (real_opp_proj (phi a) n).
        rewrite (real_plus_proj (real_mult (real_const c) (real_abs s))
                   (real_const (eps / 2)) n).
        rewrite (real_mult_proj (real_const c) (real_abs s) n).
        rewrite (real_const_proj c n).
        rewrite (real_abs_proj s n).
        cbn [projT1 real_const real_zero].
        unfold AB, MID, dn, an. apply abl9_Qabs_wd. reflexivity.
      - exact (H2 n (NatLe_lift _ _ Hn2)). }
    assert (HY0 : Qle 0 MID).
    { apply (Qle_trans 0 (c * Qabs (projT1 s n)) MID).
      - apply (Qmult_le_0_compat c (Qabs (projT1 s n))).
        + apply Qlt_le_weak. exact Hc0.
        + apply Qabs_nonneg.
      - unfold MID. apply (Qle_plus_nonneg_r (c * Qabs (projT1 s n)) (eps / 2)).
        apply Qlt_le_weak. apply Qlt_shift_div_l.
        * reflexivity.
        * simpl. apply QltT_to_Qlt. exact Heps. }
    assert (Htri : Qle (Qabs (dn - an)) (AB + MID)).
    { (* X19'''' 修复：|Δ| = Qabs(|Δ|)（幂等）= |(|Δ|−MID)+MID|（环等）
         ≤ ||Δ|−MID|+|MID| = AB+|MID| ≤ AB+MID
         （前任 unfold AB 全位展错致 trans 中项缺外层 Qabs） *)
      assert (Hid : Qabs (dn - an) == Qabs (Qabs (dn - an))).
      { apply Qeq_sym. exact (Qabs_pos (Qabs (dn - an)) (Qabs_nonneg (dn - an))). }
      apply (Qle_trans (Qabs (dn - an))
             (Qabs (Qabs (dn - an) - MID) + Qabs MID)
             (AB + MID)).
      - apply (Qle_trans (Qabs (dn - an))
               (Qabs (Qabs (dn - an)))
               (Qabs (Qabs (dn - an) - MID) + Qabs MID)).
        + apply qeq_imp_qle. exact Hid.
        + apply (Qle_trans (Qabs (Qabs (dn - an)))
                 (Qabs ((Qabs (dn - an) - MID) + MID))
                 (Qabs (Qabs (dn - an) - MID) + Qabs MID)).
          * apply qeq_imp_qle. apply abl9_Qabs_wd. ring.
          * apply Qabs_triangle.
      - unfold AB. apply Qplus_le_compat.
        + apply Qle_refl.
        + apply abl9_Qabs_le_self. exact HY0. }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans (Qabs (dn - an)) (AB + MID) eps).
    + exact Htri.
    + (* AB + MID < eps/8 + MID（经 Qlt_minus_iff 原语），再预算 ≤ eps *)
      assert (Hstep1 : Qlt (AB + MID) (eps / 8 + MID)).
      { apply (proj2 (Qlt_minus_iff (AB + MID) (eps / 8 + MID))).
        apply (abl9_Qlt_transfer_r 0 (eps / 8 - AB) ((eps / 8 + MID) - (AB + MID))).
        - field.
        - apply (proj1 (Qlt_minus_iff AB (eps / 8))).
          apply QltT_to_Qlt. exact H2'. }
      apply (Qlt_le_trans (AB + MID) (eps / 8 + MID) eps).
      * exact Hstep1.
      * apply (Qle_trans (eps / 8 + MID)
                         (eps / 8 + ((1 # 8) * eps + (1 # 2) * eps)) eps).
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply Qplus_le_compat.
              ** unfold MID. apply (Hcsn n HnNb).
              ** apply qeq_imp_qle. field.
        -- apply (Qle_trans (eps / 8 + ((1 # 8) * eps + (1 # 2) * eps))
                            ((3 # 4) * eps) eps).
           ++ apply qeq_imp_qle.
              assert (Heq : eps / 8 + ((1 # 8) * eps + (1 # 2) * eps)
                            == (3 # 4) * eps) by field.
              exact Heq.
           ++ apply (Qle_trans ((3 # 4) * eps) (1 * eps)).
              ** apply Qmult_le_compat_r.
                 --- unfold Qle. simpl. lia.
                 --- apply Qlt_le_weak. exact HepsQ.
              ** apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* X19'''' 续作·装配供给六件（主定理 phi 装配的直接前件）                *)
(*   域件两件（Q 层逐点使用形）+合同/对齐/零件三件（Setoid 层）          *)
(* ============================================================ *)

(* —— 域件 D0：|t| ≤ b 的双侧解（Qabs 无乘法分配件，两支拆） —— *)
Lemma abl9_q_abs_two_sided_le : forall t b : Q,
  Qle (Qabs t) b -> Qle (- b) t /\ Qle t b.
Proof.
  intros t b Hab.
  assert (Hb0 : Qle 0 b)
    by (apply (Qle_trans 0 (Qabs t) b); [apply Qabs_nonneg | exact Hab]).
  destruct (Qlt_le_dec 0 t) as [Htp | Htn].
  - assert (Ht0 : Qle 0 t) by (apply Qlt_le_weak; exact Htp).
    assert (Habs : Qabs t == t) by exact (Qabs_pos t Ht0).
    split.
    + apply (Qle_trans (- b) 0 t).
      * apply (Qle_trans (- b) (- 0) 0).
        -- apply (Qopp_le_compat 0 b). exact Hb0.
        -- apply qeq_imp_qle. ring.
      * exact Ht0.
    + apply (Qle_trans t (Qabs t) b).
      * apply qeq_imp_qle. apply Qeq_sym. exact Habs.
      * exact Hab.
  - assert (Ht0' : Qle t 0) by exact Htn.
    assert (Hnt0 : Qle 0 (- t)) by (apply (Qopp_le_compat t 0); exact Ht0').
    assert (Habs : Qabs t == - t).
    { apply (Qeq_trans (Qabs t) (Qabs (- t))).
      - apply Qeq_sym. apply Qabs_opp.
      - exact (Qabs_pos (- t) Hnt0). }
    split.
    + apply (Qle_trans (- b) (- (- t)) t).
      * apply (Qopp_le_compat (- t) b).
        apply (Qle_trans (- t) (Qabs t) b).
        -- apply qeq_imp_qle. apply Qeq_sym. exact Habs.
        -- exact Hab.
      * apply qeq_imp_qle. ring.
    + apply (Qle_trans t 0 b).
      * exact Ht0'.
      * exact Hb0.
Qed.

(* —— 域件 D1：路径分母下界——|a| ≤ 1、|t| ≤ 1/4 → 3/4 ≤ 1+(a+t)a
     （配平域 1+x(x+h) 沿路径逐点 ≥ 3/4 的 Q 层算术核：
       a²+ta ≥ −a/4 或 a/4（sign a 两支），平方配 (a∓1/8)² ≥ 0） —— *)
Lemma abl9_q_path_den : forall a t : Q,
  Qle (Qabs a) 1 -> Qle (Qabs t) (1 # 4) ->
  QleT' (3 # 4) (1 + (a + t) * a).
Proof.
  intros a t Ha Ht.
  apply Qle_to_QleT'.
  destruct (abl9_q_abs_two_sided_le t (1 # 4) Ht) as [Htl Htu].
  destruct (abl9_q_abs_two_sided_le a 1 Ha) as [Hal Hau].
  destruct (Qlt_le_dec 0 a) as [Hap | Han].
  - (* a > 0：ta ≥ (−1/4)a；1+a²−a/4 = (a−1/8)² + 63/64 ≥ 63/64 ≥ 3/4 *)
    assert (Ha0 : Qle 0 a) by (apply Qlt_le_weak; exact Hap).
    assert (H34 : Qle (3 # 4) (63 # 64)) by (unfold Qle; simpl; lia).
    assert (Hta : Qle ((-1#4) * a) (t * a)).
    { apply (Qmult_le_compat_r (- (1#4)) t a). exact Htl. exact Ha0. }
    apply (Qle_trans (3#4) (0 + (63#64)) (1 + (a + t) * a)).
    + apply (Qle_trans (3#4) (63#64) (0 + (63#64))).
      * exact H34.
      * apply qeq_imp_qle. ring.
    + apply (Qle_trans (0 + (63#64))
                       ((a - (1#8)) * (a - (1#8)) + (63#64))
                       (1 + (a + t) * a)).
      * apply Qplus_le_compat.
        -- apply Qsquare_nonneg.
        -- apply Qle_refl.
      * apply (Qle_trans ((a - (1#8)) * (a - (1#8)) + (63#64))
                       (1 + a * a + (-1#4) * a) (1 + (a + t) * a)).
        -- apply qeq_imp_qle. ring.
        -- apply (Qle_trans (1 + a * a + (-1#4) * a)
                         (1 + a * a + t * a) (1 + (a + t) * a)).
           ++ apply Qplus_le_compat. apply Qle_refl. exact Hta.
           ++ apply qeq_imp_qle. ring.
  - (* a ≤ 0：t ≤ 1/4 乘负翻转 ta ≥ (1/4)a；1+a²+a/4 = (a+1/8)² + 63/64 *)
    assert (Ha0' : Qle a 0) by exact Han.
    assert (H34 : Qle (3 # 4) (63 # 64)) by (unfold Qle; simpl; lia).
    assert (Hta : Qle ((1#4) * a) (t * a)).
    { assert (E1 : t * a == (- t) * (- a)) by ring.
      assert (E2 : (1#4) * a == (- (1#4)) * (- a)) by ring.
      apply (Qle_trans ((1#4) * a) ((- (1#4)) * (- a)) (t * a)).
      - apply qeq_imp_qle. exact E2.
      - apply (Qle_trans ((- (1#4)) * (- a)) ((- t) * (- a)) (t * a)).
        + apply (Qmult_le_compat_r (- (1#4)) (- t) (- a)).
          * exact (Qopp_le_compat t (1#4) Htu).
          * apply (Qle_trans 0 (- 0) (- a)).
            -- apply qeq_imp_qle. ring.
            -- apply (Qopp_le_compat a 0). exact Ha0'.
        + apply qeq_imp_qle. apply Qeq_sym. exact E1. }
    apply (Qle_trans (3#4) (0 + (63#64)) (1 + (a + t) * a)).
    + apply (Qle_trans (3#4) (63#64) (0 + (63#64))).
      * exact H34.
      * apply qeq_imp_qle. ring.
    + apply (Qle_trans (0 + (63#64))
                       ((a + (1#8)) * (a + (1#8)) + (63#64))
                       (1 + (a + t) * a)).
      * apply Qplus_le_compat.
        -- apply Qsquare_nonneg.
        -- apply Qle_refl.
      * apply (Qle_trans ((a + (1#8)) * (a + (1#8)) + (63#64))
                       (1 + a * a + (1#4) * a) (1 + (a + t) * a)).
        -- apply qeq_imp_qle. ring.
        -- apply (Qle_trans (1 + a * a + (1#4) * a)
                         (1 + a * a + t * a) (1 + (a + t) * a)).
           ++ apply Qplus_le_compat. apply Qle_refl. exact Hta.
           ++ apply qeq_imp_qle. ring.
Qed.

(* —— 合同件 A：b5c_arctan_partial_wd 升 real 层（逐点投影路线：
     arctan_real_proj（reflexivity）+逐点 Qeq+real_eq_of_zero_diff 升层，
     免全 real_eq 逼近链——域证书随实参各带） —— *)
Lemma abl9_arctan_wd_real : forall (u v : Real)
  (Hu : forall n : nat, QleT' (Qabs (projT1 u n)) 1)
  (Hv : forall n : nat, QleT' (Qabs (projT1 v n)) 1),
  (forall n : nat, projT1 u n == projT1 v n) ->
  real_eq (cauchy_real_arctan u Hu) (cauchy_real_arctan v Hv).
Proof.
  intros u v Hu Hv Hpt.
  apply real_eq_of_zero_diff.
  intros n.
  rewrite (arctan_real_proj u Hu n).
  rewrite (arctan_real_proj v Hv n).
  rewrite (b5c_arctan_partial_wd n (projT1 u n) (projT1 v n) (Hpt n)).
  ring.
Qed.

(* —— 零件 C：零实参 arctan == 0（phi(0)==0 的使用形；
     根 b5c_arctan_partial_wd + b5c_arctan_partial_zero） —— *)
Lemma abl9_arctan_zero_pt : forall (u : Real)
  (Hu : forall n : nat, QleT' (Qabs (projT1 u n)) 1),
  (forall n : nat, projT1 u n == 0) ->
  real_eq (cauchy_real_arctan u Hu) real_zero.
Proof.
  intros u Hu Hpt.
  apply real_eq_of_zero_diff.
  intros n.
  rewrite (arctan_real_proj u Hu n).
  rewrite (b5c_arctan_partial_wd n (projT1 u n) 0 (Hpt n)).
  cbn [projT1 real_zero].
  rewrite (b5c_arctan_partial_zero n).
  ring.
Qed.

(* —— 对齐件 B：w 复合实参 == 拟文 RHS 实参（除法形对乘法形的
     real_mult comm+compat 对齐链；(x+h)+(−x) == h 逐点） —— *)
Lemma abl9_w_align : forall (x h : Real)
  (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x))),
  real_eq (real_mult (real_plus (real_plus x h) (real_opp x))
                     (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x h) x)) Hd))
          (real_mult (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x h) x)) Hd) h).
Proof.
  intros x h Hd.
  apply (real_eq_trans
          (real_mult (real_plus (real_plus x h) (real_opp x))
                     (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x h) x)) Hd))
          (real_mult h (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x h) x)) Hd))
          (real_mult (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x h) x)) Hd) h)).
  - apply (RealSetoid.real_eq_mult_compat
             (real_plus (real_plus x h) (real_opp x))
             (real_inv_pos (real_plus real_one (real_mult (real_plus x h) x)) Hd)
             h
             (real_inv_pos (real_plus real_one (real_mult (real_plus x h) x)) Hd)).
    + apply real_eq_of_zero_diff. intros n.
      rewrite (real_plus_proj (real_plus x h) (real_opp x) n).
      rewrite (real_plus_proj x h n).
      rewrite (real_opp_proj x n).
      cbn [projT1]. ring.
    + apply real_eq_refl.
  - exact (real_mult_comm h (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x h) x)) Hd)).
Qed.

(* —— 零件 C2：w(x) == 0（端点 phi(0)==0 的 w 侧；t:=real_zero 处
     w 实参逐点投影 0·inv_n == 0） —— *)
Lemma abl9_wx_zero : forall (x : Real)
  (Hd : real_lt real_zero
          (real_plus real_one (real_mult (real_plus x real_zero) x))),
  real_eq (real_mult (real_plus (real_plus x real_zero) (real_opp x))
                     (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x real_zero) x)) Hd))
          real_zero.
Proof.
  intros x Hd.
  apply real_eq_of_zero_diff.
  intros n.
  rewrite (real_mult_proj (real_plus (real_plus x real_zero) (real_opp x))
             (real_inv_pos (real_plus real_one
                (real_mult (real_plus x real_zero) x)) Hd) n).
  rewrite (real_plus_proj (real_plus x real_zero) (real_opp x) n).
  rewrite (real_plus_proj x real_zero n).
  rewrite (real_opp_proj x n).
  cbn [projT1 real_zero].
  ring.
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                            *)
(*   对账三联：Lemma 名清单 17 = Qed 计数 17 = PA 语句 17，零差。       *)
(*   （接续注：X19'' 段已把原稿 9/8 误计勘为 10；X19'''' 段续作六件     *)
(*    （D0/D1 域件+A 合同+C 零件+B 对齐+C2 w 零件）后为 17，            *)
(*    并补前任 414 行版新增 abl9_Qabs_le_self 之漏 PA 行，              *)
(*    红线「全 Closed」逐件可查；提取检验另附。）                       *)
(* ============================================================ *)
Print Assumptions abl9_QltT_transfer_l.
Print Assumptions abl9_QltT_transfer_r.
Print Assumptions abl9_Qlt_transfer_l.
Print Assumptions abl9_Qlt_transfer_r.
Print Assumptions abl9_Qabs_wd.
Print Assumptions abl9_q_pos_sq.
Print Assumptions abl9_slope_id.
Print Assumptions abl9_abs_shift.
Print Assumptions abl9_real_tail_bnd.
Print Assumptions abl9_const_crit.
Print Assumptions abl9_Qabs_le_self.
Print Assumptions abl9_q_abs_two_sided_le.
Print Assumptions abl9_q_path_den.
Print Assumptions abl9_arctan_wd_real.
Print Assumptions abl9_arctan_zero_pt.
Print Assumptions abl9_w_align.
Print Assumptions abl9_wx_zero.

(* 提取检验（判据 = 输出 Obj.magic 计数 0） *)
Recursive Extraction abl9_q_pos_sq abl9_slope_id abl9_real_tail_bnd.
Recursive Extraction abl9_q_path_den abl9_arctan_wd_real abl9_arctan_zero_pt.
