(* ============================================================ *)
(* UpRealLeB3.v *)
(* *)
(* 目的： Bishop 序代数引擎固化层（B 形扩展第一队列）。 *)
(* 主件： leb3_le_b_refl / leb3_le_b_pos_scale 等 ≤_B 序代数定律族。 *)
(* 依赖： CW_ConstructiveWorld_219、UpRealLeB、UpRealLeB2。 *)
(* 备注： 纯序代数：零 eps 拆分底座，双右侧加成对消去直连第二段完成器。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpRealLeB3.v —— ≤_B 序代数引擎固化层（B 形扩展建造队列 T1）         *)
(*                                                                *)
(* 立项：侦察席「B形扩展建造队列-20260910」目标 1。运输四件原困于邻席    *)
(* 领地中间态文件（只读参考、勿依赖），本库以 leb3_ 前缀独立真证固化，    *)
(* 双形并存零 Require 关系；反序/正缩放/严格对照锚三件为 ≤_B 序代数      *)
(* 第三面（负号反变 / 数乘兼容 / 恒等严格元）新构造。                   *)
(* 基座：UpRealLeB（谓词 / 单向桥 / 完成器）+ UpRealLeB2（加法兼容       *)
(* 组合器）+ 锚点（opp 严格反序 real_opp_lt_compat、opp 分配       *)
(* real_opp_plus、乘法保序 real_mult_lt_compat、逐点投影                *)
(* real_plus_proj / real_abs_proj、混合加法 real_lt_plus_compat_lt_le）。*)
(* 侦察勘误两则：①opp 严格反序 / opp 分配 Real 层在案（原判「缺位」），  *)
(* 件 5 直连免自证；②件 5 双侧右加成对消去，免 eps/2 拆分底座。          *)
(*                                                                *)
(* 七件清单：1 refl 自反 / 2 eq_l 左运输 / 3 eq_r 右运输 /                *)
(*   4 plus_nonneg_r 非负右加 x≤_B y+c / 5 opp_rev 反序 −y≤_B−x /         *)
(*   6 pos_scale 正缩放 x·c≤_B y·c（完成器反用 D:=c；伴生 pos_scale_l     *)
(*     左因子形＝任务书 c·x≤_B c·y 方向）/ 7 abs_plus_one_pos 0<|a|+1     *)
(*     （冻结筛余唯一 Real 层可对照行@L549 的对照锚；见证 1/2、     *)
(*      N:=0 逐点 Q 层直构）                                             *)
(*                                                                *)
(* 红线自检口径：                                                      *)
(*   —— 禁词全零（按全文件计含头注）；                                  *)
(*   —— 全件 Qed 真证，term-mode 显式组装（real_eq 非 Id 禁改写，        *)
(*      全链 real_eq_trans / sym / compat 族），无任何降级占位；          *)
(*   —— 结论位全 Set 层：real_le_b 为 Set 值 forall 型、real_lt 为       *)
(*      sigT 见证型，零 Prop 泄露；                                      *)
(*   —— 前提位零新增（正性 / 非负证书全由既有件直供）；                   *)
(*   —— 提取探针 Obj.magic=0（独立小探针，验后删）；                     *)
(*   —— Print Assumptions 全件 Closed（文末八连打，证据在编译日志）。     *)
(* 编译配方：cpu_guard 包装零裸调（9.0 同轨）：                          *)

(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.

(* ============================================================ *)
(* 一、运输四件（自反 / 左右端等式运输 / 非负右加）                      *)
(* ============================================================ *)

(* 件 1：≤_B 自反（单向桥 + real_le_refl 单步） *)
Lemma leb3_le_b_refl : forall x : Real, real_le_b x x.
Proof.
  intros x. apply real_le_to_le_b. apply real_le_refl.
Qed.

(* 件 2：左端等式运输：x1≈x2 且 x1 ≤_B y 给 x2 ≤_B y *)
Lemma leb3_le_b_eq_l : forall x1 x2 y : Real,
  real_eq x1 x2 -> real_le_b x1 y -> real_le_b x2 y.
Proof.
  intros x1 x2 y Heq H. unfold real_le_b in H. unfold real_le_b.
  intros eps Heps.
  apply (RealSetoid.real_lt_id_l x2 x1 (real_plus y eps)).
  - apply real_eq_sym. exact Heq.
  - exact (H eps Heps).
Qed.

(* 件 3：右端等式运输：x ≤_B y1 且 y1≈y2 给 x ≤_B y2
   （逐 eps 加法兼容换形 y1+e == y2+e） *)
Lemma leb3_le_b_eq_r : forall x y1 y2 : Real,
  real_le_b x y1 -> real_eq y1 y2 -> real_le_b x y2.
Proof.
  intros x y1 y2 H Heq. unfold real_le_b in H. unfold real_le_b.
  intros eps Heps.
  apply (RealSetoid.real_lt_id_r x (real_plus y1 eps) (real_plus y2 eps)).
  - apply (RealSetoid.real_eq_plus_compat y1 eps y2 eps).
    + exact Heq.
    + apply real_eq_refl.
  - exact (H eps Heps).
Qed.

(* 件 4：非负右加：x ≤_B y 且 0 ≤ c 给 x ≤_B y+c
   （加法兼容组合器 + x+0==x 左端运输） *)
Lemma leb3_le_b_plus_nonneg_r : forall x y c : Real,
  real_le_b x y -> real_le real_zero c -> real_le_b x (real_plus y c).
Proof.
  intros x y c H Hc.
  apply (leb3_le_b_eq_l (real_plus x real_zero) x (real_plus y c)).
  - apply real_plus_zero.
  - apply (real_le_b_plus_compat x y real_zero c).
    + exact H.
    + apply real_le_to_le_b. exact Hc.
Qed.

(* ============================================================ *)
(* 二、反序件（≤_B 的负号反变）                                        *)
(* ============================================================ *)

(* 件 5：反序：x ≤_B y 给 −y ≤_B −x。
   给 d>0：H 直取 x<y+d ⟹ −(y+d)<−x（opp 严格反序基元）
   ⟹ 换形 −y+−d<−x（opp 分配）⟹ 双侧右加 d（lt_le 混合加法保序）
   ⟹ 左端 (−y+−d)+d == −y 恒等完成（结合 + −d+d==0 + +0）。
   d 在两侧成对消去，免 eps/2 拆分。 *)
Lemma leb3_le_b_opp_rev : forall x y : Real,
  real_le_b x y -> real_le_b (real_opp y) (real_opp x).
Proof.
  intros x y H. unfold real_le_b in H. unfold real_le_b.
  intros d Hd.
  pose proof (H d Hd) as H1.
  pose proof (real_opp_lt_compat x (real_plus y d) H1) as H2.
  assert (H3 : real_lt (real_plus (real_opp y) (real_opp d)) (real_opp x)).
  { apply (RealSetoid.real_lt_id_l (real_plus (real_opp y) (real_opp d))
                                   (real_opp (real_plus y d)) (real_opp x)).
    - apply real_eq_sym. exact (real_opp_plus y d).
    - exact H2. }
  assert (H4 : real_lt (real_plus (real_plus (real_opp y) (real_opp d)) d)
                       (real_plus (real_opp x) d)).
  { exact (real_lt_plus_compat_lt_le (real_plus (real_opp y) (real_opp d))
                                     (real_opp x) d d H3 (real_le_refl d)). }
  assert (Heq5 : real_eq (real_plus (real_plus (real_opp y) (real_opp d)) d)
                         (real_opp y)).
  { apply (real_eq_trans _
             (real_plus (real_opp y) (real_plus (real_opp d) d)) _).
    - apply real_eq_sym. apply real_plus_assoc.
    - apply (real_eq_trans _ (real_plus (real_opp y) real_zero) _).
      + apply (RealSetoid.real_eq_plus_compat (real_opp y)
                 (real_plus (real_opp d) d) (real_opp y) real_zero).
        * apply real_eq_refl.
        * apply (real_eq_trans (real_plus (real_opp d) d)
                   (real_plus d (real_opp d)) real_zero).
          -- apply real_plus_comm.
          -- apply real_plus_opp.
      + apply real_plus_zero. }
  apply (RealSetoid.real_lt_id_l (real_opp y)
           (real_plus (real_plus (real_opp y) (real_opp d)) d)
           (real_plus (real_opp x) d)).
  - apply real_eq_sym. exact Heq5.
  - exact H4.
Qed.

(* ============================================================ *)
(* 三、正缩放件（完成器反用）                                           *)
(* ============================================================ *)

(* 件 6：正缩放：x ≤_B y 且 0<c 给 x·c ≤_B y·c。
   完成器反用（D:=c）：给 e>0 只需 Or 形 x·c ≤ y·c+c·e——
   x<y+e 经乘法保序 ⟹ x·c<(y+e)·c，再 (y+e)·c==y·c+c·e 换形。 *)
Lemma leb3_le_b_pos_scale : forall x y c : Real,
  real_le_b x y -> real_lt real_zero c ->
  real_le_b (real_mult x c) (real_mult y c).
Proof.
  intros x y c H Hc.
  apply (real_le_closure_b (real_mult x c) (real_mult y c) c Hc).
  intros eps Heps. unfold real_le. left.
  apply (RealSetoid.real_lt_id_r (real_mult x c)
           (real_mult (real_plus y eps) c)
           (real_plus (real_mult y c) (real_mult c eps))).
  - apply (real_eq_trans _ (real_mult c (real_plus y eps)) _).
    + apply real_mult_comm.
    + apply (real_eq_trans _
               (real_plus (real_mult c y) (real_mult c eps)) _).
      * apply real_distrib.
      * apply (RealSetoid.real_eq_plus_compat (real_mult c y)
                 (real_mult c eps) (real_mult y c) (real_mult c eps)).
        -- apply real_mult_comm.
        -- apply real_eq_refl.
  - exact (real_mult_lt_compat x (real_plus y eps) c (H eps Heps) Hc).
Qed.

(* 件 6 伴生：左因子形（任务书 c·x ≤_B c·y 方向），
   等式运输两步平移（comm 换形各一） *)
Lemma leb3_le_b_pos_scale_l : forall x y c : Real,
  real_le_b x y -> real_lt real_zero c ->
  real_le_b (real_mult c x) (real_mult c y).
Proof.
  intros x y c H Hc.
  apply (leb3_le_b_eq_l (real_mult x c) (real_mult c x) (real_mult c y)).
  - apply real_mult_comm.
  - apply (leb3_le_b_eq_r (real_mult x c) (real_mult y c) (real_mult c y)).
    + apply (leb3_le_b_pos_scale x y c H Hc).
    + apply real_mult_comm.
Qed.

(* ============================================================ *)
(* 四、严格对照锚件（冻结 72 筛余唯一 Real 层可对照行）                  *)
(* ============================================================ *)

(* 件 7：0 < |a|+1。语句自足直构：见证 eps0:=1/2、N:=0，
   逐点 1/2 < 1 ≤ |aₙ|+1−0（Qabs 非负 + Q 加法保非严格序）。 *)
Lemma leb3_abs_plus_one_pos : forall a : Real,
  real_lt real_zero (real_plus (real_abs a) real_one).
Proof.
  intro a. unfold real_lt.
  exists (1 / 2)%Q. split.
  - apply Qlt_to_QltT. compute. reflexivity.
  - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
    rewrite (real_plus_proj (real_abs a) real_one n).
    rewrite (real_abs_proj a n).
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    assert (Ho : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
    setoid_rewrite Hz. setoid_rewrite Ho.
    assert (Habsn : Qle 0 (Qabs (projT1 a n))) by apply Qabs_nonneg.
    apply (Qlt_le_trans (1 / 2)%Q (0 + 1)%Q
             ((Qabs (projT1 a n) + 1 - 0)%Q)).
    + compute. reflexivity.
    + apply (Qle_trans (0 + 1)%Q (Qabs (projT1 a n) + 1)%Q
               (Qabs (projT1 a n) + 1 - 0)%Q).
      * apply (Qplus_le_compat 0 (Qabs (projT1 a n)) 1 1).
        -- exact Habsn.
        -- apply Qle_refl.
      * apply qeq_le. unfold Qminus.
        assert (Hn0 : (- 0)%Q == 0) by (compute; reflexivity).
        rewrite Hn0. apply Qeq_sym. apply Qplus_0_r.
Qed.

(* ============================================================ *)
(* 五、假设审计（全件 Closed，证据在编译日志）                           *)
(* ============================================================ *)

Print Assumptions leb3_le_b_refl.
Print Assumptions leb3_le_b_eq_l.
Print Assumptions leb3_le_b_eq_r.
Print Assumptions leb3_le_b_plus_nonneg_r.
Print Assumptions leb3_le_b_opp_rev.
Print Assumptions leb3_le_b_pos_scale.
Print Assumptions leb3_le_b_pos_scale_l.
Print Assumptions leb3_abs_plus_one_pos.
