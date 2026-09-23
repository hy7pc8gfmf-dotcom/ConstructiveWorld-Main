(* ============================================================ *)
(* ToyR 玩具证替换件 —— T269 台账席 战役包AD（tier2 末批二）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   mixe_cf_select_cap（原 L640，3 句玩具证）                            *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T339 恒等守恒更正注记】2026-09-22 包AW十四 台账席（恒等头注更正第四批） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* T277（包AL）全量恒等核查已证结论、T317（包AV六）试点已证结论：本件实测为 *)
(* 恒等守恒——清单所列 1 参数位证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* 零变化），头注「替换」声称与实物不符，特此更正。 *)
(* 更正口径：真替换 0 参数位＋恒等守恒 1 参数位；本注记为追加块，上方原头注一字 *)
(* 未改（历史证据保全）；证明体、声明面、语句面、Require 面零改动；台账 *)
(* 承载见 T277 附录／T284 修正块／T317 评估册／T321／T329／T330／T337／T339 台账。 *)
(* 附记：T277 判级全文恒等；Y 域收尾＋AB 域收尾＋AD 域直推第四批（T317 六·1 方案①）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqMixLogE.v —— 赛马 E 席 · 路径四：代数锐化封顶定理            *)
(* （「为什么必须搜索」的方法论论证件）2026-09-18                    *)
(* ============================================================ *)
(* Path E 裁决（承 AT11 分析）：Bernoulli 族闭式估计的量级封顶——        *)
(* 任何只经本族闭式不等式闭合（无搜索、纯代数解出 k）的构造，其返回值    *)
(* 被                                                                  *)
(*     k > (TV0'/b0 - 1)/w                                             *)
(* 的线性下界封死。Q 层精确形（本件 mixe_cf_cap）：                      *)
(*     tv0 < b0*(1+k*w)  的可判定闭合  强制  tv0-b0 < k*(w*b0)，         *)
(* 即「1/(1+kw)*TV0' < b0 ⟹ w*k > TV0'/b0 - 1」的逆否构造性形。          *)
(* 对数量级必须经可判定搜索（A 席二分 / B 席倍增 / D 席平方阶梯在产）    *)
(* 达成——同一谓词族上 O(log) 次可判定比较，换取闭式反解所需的超越函数   *)
(* 豁免（反解 (1+w)^k = TV0'/b0 需要 ln）。                              *)
(*                                                                    *)
(* 公理面：本件零新增公理；全部前提为 Q 层显式序假设（Qlt/Qle/bool），   *)
(* 文末 Print Assumptions 预期全 Closed。                               *)
(* 依赖面：纯 Stdlib QArith（QArith + Qround + ZArith + Lia），零 CW 基座*)
(* 依赖、零 Real 层接触——Q 层无 zify，手工循环依赖清单按 AT8/IR3 卡纪律。        *)
(* 红线自审：语句面量词 nat/Q、比较 Qlt/Qle、证书 bool——全 Set 层；      *)
(* 计算件（mixe_qpow/mixe_qlt_bool/mixe_qofnat/mixe_cf_accept/           *)
(* mixe_cf_accept_sharp/mixe_cf_select）全 Defined 且 Set 值             *)
(*（sumbool-if 分支合法，Defined 体零 Prop 消去）；封顶/健全性定理为     *)
(* Qed 依存件，不进提取签名。                                           *)
(* 诚实边界：封顶定理只对本「闭式族内可代数反解（affine 形）」的构造     *)
(* 声明（generic 斜率形 mixe_cf_cap_gen 覆盖一切常数锐化成员）；不声明   *)
(* 全域不可达（任何算法都无法超越线性——那是另一量级的独立研究）。        *)
(* 锐化成员 (1+w)^k 的接受谓词单调可判定、其最小通过站（数值 demo        *)
(* k=25）正是可判定搜索路线的对数量级来源；其反解超越、不可闭式代数      *)
(* 化——此点如实标注为方法论论证而非本件形式定理（形式部分 = cap 定理 +  *)
(* 选择器封顶 + 数值对照 91 vs 25 vs 真最小 22）。                       *)
(* 编译配方：cd Live_X && C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe      *)
(*   -Q . "" UpReqMixLogE.v（.cmd 内 set COQLIB/ROCQLIB）                 *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qround.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 0：基础工具（mixe_ 前缀，全树 grep 零撞名）                       *)
(* ============================================================ *)

(* nat-尺度有理化：stdlib Q.of_nat 缺位，自建（vm_compute 直算、提取零依赖） *)
Definition mixe_qofnat (k : nat) : Q := (Z.of_nat k # 1)%Q.

(* Q 严格比较 bool 判定器（stdlib Qlt_bool 缺位；经 Set 值 sumbool 自建，  *)
(* Defined 体零 Prop 消去） *)
Definition mixe_qlt_bool (x y : Q) : bool :=
  if Qlt_le_dec x y then true else false.

(* ---- Qeq 传输件（Qeq 目标内 rewrite 稳定；Qlt/Qle 目标内禁 rewrite——  *)
(*      一律项式传输，AT8 卡§1 纪律） ---- *)

(* Qeq→Qle 项式桥（stdlib qeq_le 在 9.1 缺位，自建——AT8 卡§同款手法） *)
Lemma mixe_qeq_le : forall a b : Q, Qeq a b -> Qle a b.
Proof.
  intros a b Hab. unfold Qle, Qeq in *. rewrite Hab. apply Z.le_refl.
Qed.

Lemma mixe_qle_eq_l : forall a b c : Q, Qeq a b -> Qle b c -> Qle a c.
Proof.
  intros a b c Hab Hbc. apply (Qle_trans a b c).
  - exact (mixe_qeq_le _ _ Hab).
  - exact Hbc.
Qed.

Lemma mixe_qle_eq_r : forall a b c : Q, Qle a b -> Qeq b c -> Qle a c.
Proof.
  intros a b c Hab Hbc. apply (Qle_trans a b c).
  - exact Hab.
  - exact (mixe_qeq_le _ _ Hbc).
Qed.

Lemma mixe_qlt_eq_l : forall a b c : Q, Qeq a b -> Qlt b c -> Qlt a c.
Proof.
  intros a b c Hab Hbc. apply (Qle_lt_trans a b c).
  - exact (mixe_qeq_le _ _ Hab).
  - exact Hbc.
Qed.

Lemma mixe_qlt_eq_r : forall a b c : Q, Qeq a b -> Qlt c a -> Qlt c b.
Proof.
  intros a b c Hab Hca. apply (Qlt_le_trans c a b).
  - exact Hca.
  - exact (mixe_qeq_le _ _ Hab).
Qed.

(* ---- 常量序与 bool 桥 ---- *)

Lemma mixe_qle_01 : Qle 0 1.
Proof. unfold Qle. cbn [Qnum Qden Z.mul Pos.mul]. lia. Qed.

Lemma mixe_qlt_01 : Qlt 0 1.
Proof. unfold Qlt. cbn [Qnum Qden Z.mul Pos.mul]. lia. Qed.

Lemma mixe_qlt_bool_true : forall x y : Q, Qlt x y -> mixe_qlt_bool x y = true.
Proof.
  intros x y H. unfold mixe_qlt_bool.
  destruct (Qlt_le_dec x y) as [Hd | Hd].
  - reflexivity.
  - exfalso. exact (Qlt_not_le x y H Hd).
Qed.

Lemma mixe_qlt_bool_of_true : forall x y : Q, mixe_qlt_bool x y = true -> Qlt x y.
Proof.
  intros x y H. unfold mixe_qlt_bool in H.
  destruct (Qlt_le_dec x y) as [Hd | Hd].
  - exact Hd.
  - discriminate.
Qed.

(* ---- 乘法序账（stdlib 乘数只挂右；左挂经 comm-Qeq 项式传输——IR3 卡坑 b） *)

Lemma mixe_qmult_nonneg : forall x y : Q, Qle 0 x -> Qle 0 y -> Qle 0 (x * y).
Proof.
  intros x y Hx Hy.
  apply (mixe_qle_eq_l 0 (0 * y) (x * y)).
  - ring.
  - exact (Qmult_le_compat_r 0 x y Hx Hy).
Qed.

Lemma mixe_qmult_le_l : forall z x y : Q,
  Qle 0 z -> Qle x y -> Qle (z * x) (z * y).
Proof.
  intros z x y Hz Hxy.
  apply (mixe_qle_eq_l (z * x) (x * z) (z * y)).
  - ring.
  - apply (mixe_qle_eq_r (x * z) (y * z) (z * y)).
    + exact (Qmult_le_compat_r x y z Hxy Hz).
    + ring.
Qed.

Lemma mixe_qmult_pos : forall x y : Q, Qlt 0 x -> Qlt 0 y -> Qlt 0 (x * y).
Proof.
  intros x y Hx Hy.
  apply (mixe_qlt_eq_l 0 (0 * y) (x * y)).
  - ring.
  - exact (Qmult_lt_compat_r 0 x y Hy Hx).
Qed.

(* 「x - c ≤ x」（c ≥ 0）——封顶与 Bernoulli 步进的辅助引理；零消去零除法 *)
Lemma mixe_le_sub : forall x c : Q, Qle 0 c -> Qle (x - c) x.
Proof.
  intros x c Hc. unfold Qminus.
  apply (mixe_qle_eq_l (x + Qopp c) (0 + (x + Qopp c)) x).
  - ring.
  - apply (mixe_qle_eq_r (0 + (x + Qopp c)) (c + (x + Qopp c)) x).
    + apply (Qplus_le_compat 0 c (x + Qopp c) (x + Qopp c)).
      * exact Hc.
      * apply Qle_refl.
    + ring.
Qed.

(* 「1 - w ≥ 0」（w ≤ 1）——Bernoulli 幂底非负 *)
Lemma mixe_sub_nonneg : forall w : Q, Qle w 1 -> Qle 0 (1 - w).
Proof.
  intros w Hw1. unfold Qminus.
  apply (mixe_qle_eq_l 0 (Qopp 1 + 1) (1 + Qopp w)).
  - ring.
  - apply (mixe_qle_eq_r (Qopp 1 + 1) (Qopp w + 1) (1 + Qopp w)).
    + apply (Qplus_le_compat (Qopp 1) (Qopp w) 1 1).
      * exact (Qopp_le_compat w 1 Hw1).
      * apply Qle_refl.
    + ring.
Qed.

(* 「1 + q ≥ 0」（q ≥ 0） *)
Lemma mixe_one_plus_nonneg : forall q : Q, Qle 0 q -> Qle 0 (1 + q).
Proof.
  intros q Hq.
  apply (Qle_trans 0 1).
  - exact mixe_qle_01.
  - apply (mixe_qle_eq_l 1 (1 + 0) (1 + q)).
    + ring.
    + apply (Qplus_le_compat 1 1 0 q).
      * apply Qle_refl.
      * exact Hq.
Qed.

(* Q 逆元正性 *)
Lemma mixe_qinv_pos : forall x : Q, Qlt 0 x -> Qlt 0 (Qinv x).
Proof.
  intros x Hx.
  destruct (Qlt_le_dec 0 (Qinv x)) as [Hd | Hd].
  - exact Hd.
  - exfalso.
    assert (Hle : Qle (Qinv x * x) 0).
    { apply (mixe_qle_eq_r (Qinv x * x) (0 * x) 0).
      - exact (Qmult_le_compat_r (Qinv x) 0 x Hd (Qlt_le_weak 0 x Hx)).
      - ring. }
    assert (Hone : Qinv x * x == 1).
    { apply (Qeq_trans (Qinv x * x) (x * Qinv x) 1).
      - ring.
      - apply (Qmult_inv_r x).
        intro Heq. exact (Qlt_irrefl 0 (mixe_qlt_eq_r x 0 0 Heq Hx)). }
    exact (Qlt_irrefl 0
             (Qlt_le_trans 0 1 0 mixe_qlt_01
                (mixe_qle_eq_l 1 (Qinv x * x) 0
                   (Qeq_sym (Qinv x * x) 1 Hone) Hle))).
Qed.

(* ---- nat-尺度账 ---- *)

Lemma mixe_qofnat_S : forall k : nat,
  Qeq (mixe_qofnat (Datatypes.S k)) (1 + mixe_qofnat k)%Q.
Proof.
  intro k.
  unfold mixe_qofnat, Qeq, Qplus.
  cbn [Qnum Qden Z.mul Pos.mul].
  replace (Z.of_nat (Datatypes.S k)) with (Z.of_nat k + 1)%Z by lia.
  lia.
Qed.

Lemma mixe_qofnat_nonneg : forall k : nat, Qle 0 (mixe_qofnat k).
Proof.
  intro k. induction k as [| k IH].
  - unfold mixe_qofnat, Qle.
    cbn [Qnum Qden Z.of_nat Z.mul Pos.mul]. lia.
  - apply (mixe_qle_eq_r 0 (1 + mixe_qofnat k)
             (mixe_qofnat (Datatypes.S k))).
    + apply mixe_one_plus_nonneg. exact IH.
    + exact (Qeq_sym _ _ (mixe_qofnat_S k)).
Qed.

Lemma mixe_qofnat_succ_pos : forall k : nat, Qle 0 (1 + mixe_qofnat k).
Proof.
  intro k.
  apply (Qle_trans 0 (mixe_qofnat (Datatypes.S k))).
  - apply mixe_qofnat_nonneg.
  - exact (mixe_qeq_le _ _ (mixe_qofnat_S k)).
Qed.

(* ---- Z→Q 保序（select 封顶链） ---- *)

Lemma mixe_qofZ_le : forall z1 z2 : Z, (z1 <= z2)%Z -> Qle (z1 # 1) (z2 # 1).
Proof.
  intros z1 z2 Hz.
  unfold Qle. cbn [Qnum Qden Z.mul Pos.mul]. lia.
Qed.

(* Q 上单侧严格平移（Z 层 replace+ring 归一 + Zplus_lt_compat_r 闭合——    *)
(* 闭式选择器健全性 converse 承重件） *)
Lemma mixe_qlt_plus_r : forall x y z : Q, Qlt x y -> Qlt (x + z) (y + z).
Proof.
  intros [a da] [b db] [c dc] Hxy.
  unfold Qlt in *.
  cbn [Qnum Qden Qplus] in *.
  replace (Z.pos (db * dc)%positive)%Z
    with (Z.pos db * Z.pos dc)%Z by reflexivity.
  replace (Z.pos (da * dc)%positive)%Z
    with (Z.pos da * Z.pos dc)%Z by reflexivity.
  replace ((a * Z.pos dc + c * Z.pos da) * (Z.pos db * Z.pos dc))%Z
    with ((a * Z.pos db) * (Z.pos dc * Z.pos dc)
          + (c * Z.pos db) * (Z.pos da * Z.pos dc))%Z by ring.
  replace ((b * Z.pos dc + c * Z.pos db) * (Z.pos da * Z.pos dc))%Z
    with ((b * Z.pos da) * (Z.pos dc * Z.pos dc)
          + (c * Z.pos db) * (Z.pos da * Z.pos dc))%Z by ring.
  apply (Zplus_lt_compat_r _ _ ((c * Z.pos db) * (Z.pos da * Z.pos dc))).
  assert (Hdc2 : (0 < Z.pos dc * Z.pos dc)%Z) by nia.
  apply Z.mul_lt_mono_pos_r.
  - exact Hdc2.
  - exact Hxy.
Qed.

(* ---- Qfloor 上界桥（闭式 k-公式的 ceil 行为） ---- *)

Lemma mixe_qfloor_lt : forall r : Q,
  Qlt r (mixe_qofnat (Datatypes.S (Z.to_nat (Qfloor r)))).
Proof.
  intro r.
  destruct (Z_le_gt_dec 0 (Qfloor r)) as [Hz | Hz].
  - assert (Hshift : Qeq (inject_Z (Qfloor r + 1))
                         (1 + mixe_qofnat (Z.to_nat (Qfloor r)))).
    { unfold mixe_qofnat, Qeq, Qplus, inject_Z.
      cbn [Qnum Qden Z.mul Pos.mul]. rewrite (Z2Nat.id (Qfloor r) Hz). lia. }
    apply (mixe_qlt_eq_r (inject_Z (Qfloor r + 1))
             (mixe_qofnat (Datatypes.S (Z.to_nat (Qfloor r)))) r).
    + exact (Qeq_trans (inject_Z (Qfloor r + 1))
               (1 + mixe_qofnat (Z.to_nat (Qfloor r)))
               (mixe_qofnat (Datatypes.S (Z.to_nat (Qfloor r))))
               Hshift (Qeq_sym _ _ (mixe_qofnat_S (Z.to_nat (Qfloor r))))).
    + exact (Qlt_floor r).
  - assert (Hz1 : (Qfloor r + 1 <= 0)%Z) by lia.
    assert (Hstep_a : Qle (inject_Z (Qfloor r + 1)) 1%Q).
    { apply (mixe_qle_eq_l (inject_Z (Qfloor r + 1))
               ((Qfloor r + 1) # 1)%Q 1%Q).
      - reflexivity.
      - assert (Hz1b : (Qfloor r + 1 <= 1)%Z) by lia.
        exact (mixe_qofZ_le (Qfloor r + 1) 1 Hz1b).
      }
    assert (Hstep_b : Qle 1%Q
               (mixe_qofnat (Datatypes.S (Z.to_nat (Qfloor r))))).
    { apply (mixe_qle_eq_l 1%Q (1 + 0)%Q).
      - ring.
      - apply (mixe_qle_eq_r (1 + 0)%Q
                 (1 + mixe_qofnat (Z.to_nat (Qfloor r)))
                 (mixe_qofnat (Datatypes.S (Z.to_nat (Qfloor r))))).
        + apply (Qplus_le_compat 1 1 0 (mixe_qofnat (Z.to_nat (Qfloor r)))).
          * apply Qle_refl.
          * apply mixe_qofnat_nonneg.
        + exact (Qeq_sym _ _ (mixe_qofnat_S (Z.to_nat (Qfloor r)))). }
    apply (Qlt_le_trans r (inject_Z (Qfloor r + 1))).
    + exact (Qlt_floor r).
    + exact (Qle_trans _ _ _ Hstep_a Hstep_b).
Qed.

(* ============================================================ *)
(* Part 1：锐化闭式族（Q 层 cross-mult 精确形清单）                       *)
(*   F1 mixe_bern_sharp  ：(1-w)^k * (1+k*w) ≤ 1                          *)
(*        =「(1-w)^k ≤ 1/(1+kw)」cross-mult 可判定精确形                   *)
(*   F2 mixe_bern_lower  ：1 + k*w ≤ (1+w)^k                              *)
(*        = Bernoulli 下形，即「(1+w)^(-k) ≤ (1+kw)^(-1)」族内对比项       *)
(*        （证明 (1+w)^k 成员点态更锐：最优常数变体）                      *)
(*   F3 mixe_sharp_pair  ：(1-w)^k * (1+w)^k ≤ 1                          *)
(*        =「(1-w)^k ≤ (1+w)^(-k)」最优常数变体 cross-mult 形              *)
(* ============================================================ *)

Fixpoint mixe_qpow (w : Q) (k : nat) : Q :=
  match k with
  | Datatypes.O => 1%Q
  | Datatypes.S m => w * mixe_qpow w m
  end.

Lemma mixe_qpow_nonneg : forall (x : Q) (k : nat),
  Qle 0 x -> Qle 0 (mixe_qpow x k).
Proof.
  intros x k Hx. induction k as [| k IH].
  - exact mixe_qle_01.
  - cbn [mixe_qpow]. exact (mixe_qmult_nonneg x (mixe_qpow x k) Hx IH).
Qed.

Lemma mixe_qpow_le_one : forall (x : Q) (k : nat),
  Qle 0 x -> Qle x 1 -> Qle (mixe_qpow x k) 1.
Proof.
  intros x k Hx0 Hx1. induction k as [| k IH].
  - exact (Qle_refl 1).
  - cbn [mixe_qpow].
    apply (Qle_trans _ x).
    + apply (mixe_qle_eq_r (x * mixe_qpow x k) (x * 1) x).
      * exact (mixe_qmult_le_l x (mixe_qpow x k) 1 Hx0 IH).
      * ring.
    + exact Hx1.
Qed.

Lemma mixe_qpow_mul : forall (a b : Q) (k : nat),
  Qeq (mixe_qpow a k * mixe_qpow b k) (mixe_qpow (a * b) k).
Proof.
  intros a b k. induction k as [| k IH].
  - reflexivity.
  - cbn [mixe_qpow].
    apply (Qeq_trans
             (a * mixe_qpow a k * (b * mixe_qpow b k))
             (a * b * (mixe_qpow a k * mixe_qpow b k))).
    + ring.
    + rewrite IH. apply Qeq_refl.
Qed.

(* F1：锐化 Bernoulli 上形（只需 0 ≤ w ≤ 1，弱于现行 mix_bernoulli_upper   *)
(* 的 0<w<1 前提——锐化） *)
Lemma mixe_bern_sharp : forall (w : Q) (k : nat),
  Qle 0 w -> Qle w 1 ->
  Qle (mixe_qpow (1 - w) k * (1 + mixe_qofnat k * w)) 1.
Proof.
  intros w k Hw0 Hw1. induction k as [| k IH].
  - cbn [mixe_qpow].
    apply (mixe_qle_eq_l (1 + mixe_qofnat 0 * w) 1 1).
    + change (mixe_qofnat 0) with 0%Q. ring.
    + apply Qle_refl.
  - cbn [mixe_qpow].
    assert (HeqAB : Qeq
              ((1 - w) * mixe_qpow (1 - w) k
                 * (1 + mixe_qofnat (Datatypes.S k) * w))
              ((1 - w) * mixe_qpow (1 - w) k
                 * (1 + (1 + mixe_qofnat k) * w))).
    { rewrite (mixe_qofnat_S k). apply Qeq_refl. }
    assert (Hpw : Qle 0 (mixe_qpow (1 - w) k))
      by exact (mixe_qpow_nonneg (1 - w) k (mixe_sub_nonneg w Hw1)).
    assert (HC : Qle 0 ((1 + mixe_qofnat k) * w * w)).
    { apply (mixe_qmult_nonneg ((1 + mixe_qofnat k) * w) w).
      - exact (mixe_qmult_nonneg (1 + mixe_qofnat k) w
                 (mixe_qofnat_succ_pos k) Hw0).
      - exact Hw0. }
    assert (Haux : Qle ((1 - w) * (1 + (1 + mixe_qofnat k) * w))
                            (1 + mixe_qofnat k * w)).
    { apply (mixe_qle_eq_l
               ((1 - w) * (1 + (1 + mixe_qofnat k) * w))
               ((1 + mixe_qofnat k * w) - (1 + mixe_qofnat k) * w * w)
               (1 + mixe_qofnat k * w)).
      - ring.
      - exact (mixe_le_sub _ _ HC). }
    assert (Hmul : Qle ((1 - w) * mixe_qpow (1 - w) k
                          * (1 + (1 + mixe_qofnat k) * w))
                            (mixe_qpow (1 - w) k * (1 + mixe_qofnat k * w))).
    { apply (mixe_qle_eq_l _ (mixe_qpow (1 - w) k
               * ((1 - w) * (1 + (1 + mixe_qofnat k) * w)))).
      - ring.
      - exact (mixe_qmult_le_l _ _ _ Hpw Haux). }
    exact (mixe_qle_eq_l _ _ _ HeqAB
             (Qle_trans _ _ _ Hmul IH)).
Qed.

(* F2：Bernoulli 下形（族内对比：1+kw ≤ (1+w)^k ⟹ 1/(1+w)^k ≤ 1/(1+kw)） *)
Lemma mixe_bern_lower : forall (w : Q) (k : nat),
  Qle 0 w -> Qle (1 + mixe_qofnat k * w) (mixe_qpow (1 + w) k).
Proof.
  intros w k Hw0. induction k as [| k IH].
  - cbn [mixe_qpow].
    apply (mixe_qle_eq_l (1 + mixe_qofnat 0 * w) 1 1).
    + change (mixe_qofnat 0) with 0%Q. ring.
    + apply Qle_refl.
  - cbn [mixe_qpow].
    assert (Hp1 : Qle 0 (1 + w)) by exact (mixe_one_plus_nonneg w Hw0).
    assert (Haux0 : Qeq (1 + (1 + mixe_qofnat k) * w)
                         ((1 + (1 + mixe_qofnat k) * w) + 0)) by ring.
    assert (Hq2 : Qle 0 (mixe_qofnat k * w * w)).
    { exact (mixe_qmult_nonneg (mixe_qofnat k * w) w
               (mixe_qmult_nonneg (mixe_qofnat k) w
                  (mixe_qofnat_nonneg k) Hw0) Hw0). }
    assert (Haux1 : Qle ((1 + (1 + mixe_qofnat k) * w) + 0)
                         ((1 + (1 + mixe_qofnat k) * w) + mixe_qofnat k * w * w))
      by exact (Qplus_le_compat (1 + (1 + mixe_qofnat k) * w)
                  (1 + (1 + mixe_qofnat k) * w) 0 (mixe_qofnat k * w * w)
                  (Qle_refl (1 + (1 + mixe_qofnat k) * w)) Hq2).
    assert (Haux2 : Qeq ((1 + (1 + mixe_qofnat k) * w) + mixe_qofnat k * w * w)
                         ((1 + w) * (1 + mixe_qofnat k * w))) by ring.
    assert (Haux : Qle (1 + (1 + mixe_qofnat k) * w)
                            ((1 + w) * (1 + mixe_qofnat k * w))).
    { exact (mixe_qle_eq_r
               (1 + (1 + mixe_qofnat k) * w)
               ((1 + (1 + mixe_qofnat k) * w) + mixe_qofnat k * w * w)
               ((1 + w) * (1 + mixe_qofnat k * w))
               (mixe_qle_eq_l (1 + (1 + mixe_qofnat k) * w)
                  ((1 + (1 + mixe_qofnat k) * w) + 0)
                  ((1 + (1 + mixe_qofnat k) * w) + mixe_qofnat k * w * w)
                  Haux0 Haux1)
               Haux2). }
    assert (Hshift : Qeq (1 + mixe_qofnat (Datatypes.S k) * w)
                         (1 + (1 + mixe_qofnat k) * w)).
    { rewrite (mixe_qofnat_S k). apply Qeq_refl. }
    exact (mixe_qle_eq_l _ _ _ Hshift
             (Qle_trans _ _ _ Haux (mixe_qmult_le_l (1 + w) _ _ Hp1 IH))).
Qed.

(* F3：最优常数变体：(1-w)^k (1+w)^k == (1-w^2)^k ≤ 1 *)
Lemma mixe_sharp_pair : forall (w : Q) (k : nat),
  Qle 0 w -> Qle w 1 ->
  Qle (mixe_qpow (1 - w) k * mixe_qpow (1 + w) k) 1.
Proof.
  intros w k Hw0 Hw1.
  assert (Hx0 : Qle 0 ((1 - w) * (1 + w))).
  { apply (mixe_qmult_nonneg (1 - w) (1 + w)).
    - exact (mixe_sub_nonneg w Hw1).
    - exact (mixe_one_plus_nonneg w Hw0). }
  assert (Hx1 : Qle ((1 - w) * (1 + w)) 1).
  { apply (mixe_qle_eq_l ((1 - w) * (1 + w)) (1 - w * w) 1).
    - ring.
    - exact (mixe_le_sub 1 (w * w) (mixe_qmult_nonneg w w Hw0 Hw0)). }
  apply (mixe_qle_eq_l
           (mixe_qpow (1 - w) k * mixe_qpow (1 + w) k)
           (mixe_qpow ((1 - w) * (1 + w)) k) 1).
  - exact (mixe_qpow_mul (1 - w) (1 + w) k).
  - exact (mixe_qpow_le_one ((1 - w) * (1 + w)) k Hx0 Hx1).
Qed.

(* ============================================================ *)
(* Part 2：闭式选择器（Defined 可提取）· 健全性 · 封顶定理（本席核心）      *)
(* ============================================================ *)

(* affine 成员的闭式接受谓词：tv0 < b0*(1+k*w)                            *)
(*   =「1/(1+kw) * TV0' < b0」的 cross-mult 可判定闭合形                   *)
Definition mixe_cf_accept (w b0 tv0 : Q) (k : nat) : bool :=
  mixe_qlt_bool tv0 (b0 * (1 + mixe_qofnat k * w)).

(* 最优常数成员的接受谓词：tv0 < b0*(1+w)^k（同族锐化证书） *)
Definition mixe_cf_accept_sharp (w b0 tv0 : Q) (k : nat) : bool :=
  mixe_qlt_bool tv0 (b0 * mixe_qpow (1 + w) k).

(* ---- 健全性：族接受 ⟹ 真值证书 (1-w)^k * tv0 < b0 ---- *)

Lemma mixe_cf_sound_affine : forall (w b0 tv0 : Q) (k : nat),
  Qle 0 w -> Qle w 1 -> Qle 0 tv0 ->
  mixe_cf_accept w b0 tv0 k = true ->
  Qlt (mixe_qpow (1 - w) k * tv0) b0.
Proof.
  intros w b0 tv0 k Hw0 Hw1 Htv0 Hacc.
  destruct (Qlt_le_dec (mixe_qpow (1 - w) k * tv0) b0) as [Hd | Hbad].
  - exact Hd.
  - exfalso.
    assert (Hlt : Qlt tv0 (b0 * (1 + mixe_qofnat k * w)))
      by exact (mixe_qlt_bool_of_true _ _ Hacc).
    assert (HB : Qle (mixe_qpow (1 - w) k * (1 + mixe_qofnat k * w)) 1)
      by exact (mixe_bern_sharp w k Hw0 Hw1).
    assert (Hzle : Qle 0 (1 + mixe_qofnat k * w)).
    { apply mixe_one_plus_nonneg.
      exact (mixe_qmult_nonneg (mixe_qofnat k) w
               (mixe_qofnat_nonneg k) Hw0). }
    assert (Hs1 : Qle (b0 * (1 + mixe_qofnat k * w))
                       ((mixe_qpow (1 - w) k * tv0) * (1 + mixe_qofnat k * w)))
      by exact (Qmult_le_compat_r b0 (mixe_qpow (1 - w) k * tv0)
                  (1 + mixe_qofnat k * w) Hbad Hzle).
    assert (Hs2a : Qeq ((mixe_qpow (1 - w) k * tv0) * (1 + mixe_qofnat k * w))
                       ((mixe_qpow (1 - w) k * (1 + mixe_qofnat k * w)) * tv0))
      by ring.
    assert (Hs2b : Qle ((mixe_qpow (1 - w) k * (1 + mixe_qofnat k * w)) * tv0)
                       (1 * tv0))
      by exact (Qmult_le_compat_r
                  (mixe_qpow (1 - w) k * (1 + mixe_qofnat k * w)) 1 tv0
                  HB Htv0).
    assert (Hs2c : Qeq (1 * tv0) tv0) by ring.
    assert (Hs2 : Qle ((mixe_qpow (1 - w) k * tv0) * (1 + mixe_qofnat k * w)) tv0).
    { exact (Qle_trans _ _ _
               (Qle_trans _ _ _ (mixe_qeq_le _ _ Hs2a) Hs2b)
               (mixe_qeq_le _ _ Hs2c)). }
    exact (Qlt_irrefl tv0
             (Qlt_le_trans tv0 (b0 * (1 + mixe_qofnat k * w)) tv0 Hlt
                (Qle_trans _ _ _ Hs1 Hs2))).
Qed.

Lemma mixe_cf_sound_sharp : forall (w b0 tv0 : Q) (k : nat),
  Qle 0 w -> Qle w 1 -> Qle 0 tv0 ->
  mixe_cf_accept_sharp w b0 tv0 k = true ->
  Qlt (mixe_qpow (1 - w) k * tv0) b0.
Proof.
  intros w b0 tv0 k Hw0 Hw1 Htv0 Hacc.
  destruct (Qlt_le_dec (mixe_qpow (1 - w) k * tv0) b0) as [Hd | Hbad].
  - exact Hd.
  - exfalso.
    assert (Hlt : Qlt tv0 (b0 * mixe_qpow (1 + w) k))
      by exact (mixe_qlt_bool_of_true _ _ Hacc).
    assert (HB : Qle (mixe_qpow (1 - w) k * mixe_qpow (1 + w) k) 1)
      by exact (mixe_sharp_pair w k Hw0 Hw1).
    assert (Hzle : Qle 0 (mixe_qpow (1 + w) k))
      by exact (mixe_qpow_nonneg (1 + w) k (mixe_one_plus_nonneg w Hw0)).
    assert (Hs1 : Qle (b0 * mixe_qpow (1 + w) k)
                       ((mixe_qpow (1 - w) k * tv0) * mixe_qpow (1 + w) k))
      by exact (Qmult_le_compat_r b0 (mixe_qpow (1 - w) k * tv0)
                  (mixe_qpow (1 + w) k) Hbad Hzle).
    assert (Hs2a : Qeq ((mixe_qpow (1 - w) k * tv0) * mixe_qpow (1 + w) k)
                       ((mixe_qpow (1 - w) k * mixe_qpow (1 + w) k) * tv0))
      by ring.
    assert (Hs2b : Qle ((mixe_qpow (1 - w) k * mixe_qpow (1 + w) k) * tv0)
                       (1 * tv0))
      by exact (Qmult_le_compat_r
                  (mixe_qpow (1 - w) k * mixe_qpow (1 + w) k) 1 tv0
                  HB Htv0).
    assert (Hs2c : Qeq (1 * tv0) tv0) by ring.
    assert (Hs2 : Qle ((mixe_qpow (1 - w) k * tv0) * mixe_qpow (1 + w) k) tv0).
    { exact (Qle_trans _ _ _
               (Qle_trans _ _ _ (mixe_qeq_le _ _ Hs2a) Hs2b)
               (mixe_qeq_le _ _ Hs2c)). }
    exact (Qlt_irrefl tv0
             (Qlt_le_trans tv0 (b0 * mixe_qpow (1 + w) k) tv0 Hlt
                (Qle_trans _ _ _ Hs1 Hs2))).
Qed.

(* ---- 封顶定理（本席核心） ---- *)

(* generic 斜率形：任何保持代数可反解（affine 形 b0 + k*c）的族成员/常数    *)
(* 锐化，接受即封顶——常数改进只缩放斜率 c，量级仍线性                      *)
Theorem mixe_cf_cap_gen : forall (b0 c tv0 : Q) (k : nat),
  Qlt tv0 (b0 + mixe_qofnat k * c) ->
  Qlt (Qminus tv0 b0) (mixe_qofnat k * c).
Proof.
  intros b0 c tv0 k Hlt.
  unfold Qminus.
  assert (Hle : Qle (tv0 + Qopp b0) (mixe_qofnat k * c)).
  { apply (mixe_qle_eq_r (tv0 + Qopp b0)
             ((b0 + mixe_qofnat k * c) + Qopp b0) (mixe_qofnat k * c)).
    - apply (Qplus_le_compat tv0 (b0 + mixe_qofnat k * c) (Qopp b0) (Qopp b0)).
      + exact (Qlt_le_weak tv0 (b0 + mixe_qofnat k * c) Hlt).
      + apply Qle_refl.
    - ring. }
  destruct (Qlt_le_dec (tv0 + Qopp b0) (mixe_qofnat k * c)) as [Hd | Hb].
  - exact Hd.
  - exfalso.
    assert (Hle2 : Qle (b0 + mixe_qofnat k * c) (b0 + (tv0 + Qopp b0))).
    { apply (Qplus_le_compat b0 b0 (mixe_qofnat k * c) (tv0 + Qopp b0)).
      - apply Qle_refl.
      - exact Hb. }
    apply (Qlt_irrefl tv0).
    apply (mixe_qlt_eq_r (b0 + (tv0 + Qopp b0)) tv0 tv0).
    + ring.
    + exact (Qlt_le_trans tv0 (b0 + mixe_qofnat k * c)
               (b0 + (tv0 + Qopp b0)) Hlt Hle2).
Qed.

(* 主封顶定理：affine 成员闭式接受 ⟹ tv0-b0 < k*(w*b0)                     *)
Theorem mixe_cf_cap : forall (w b0 tv0 : Q) (k : nat),
  Qlt 0 w -> Qlt 0 b0 ->
  mixe_cf_accept w b0 tv0 k = true ->
  Qlt (Qminus tv0 b0) (mixe_qofnat k * (w * b0)).
Proof.
  intros w b0 tv0 k Hw Hb0 Hacc.
  apply (mixe_cf_cap_gen b0 (w * b0) tv0 k).
  apply (mixe_qlt_eq_r
           (b0 * (1 + mixe_qofnat k * w))
           (b0 + mixe_qofnat k * (w * b0)) tv0).
  - ring.
  - exact (mixe_qlt_bool_of_true _ _ Hacc).
Qed.

(* 任务书除法精确形：k > (TV0'/b0 - 1)/w，即 (tv0-b0)/(w*b0) < k           *)
Theorem mixe_cf_cap_div : forall (w b0 tv0 : Q) (k : nat),
  Qlt 0 w -> Qlt 0 b0 ->
  mixe_cf_accept w b0 tv0 k = true ->
  Qlt ((Qminus tv0 b0) * Qinv (w * b0)) (mixe_qofnat k).
Proof.
  intros w b0 tv0 k Hw Hb0 Hacc.
  assert (Hzwb : Qlt 0 (w * b0)) by exact (mixe_qmult_pos w b0 Hw Hb0).
  assert (Hinv : Qlt 0 (Qinv (w * b0))) by exact (mixe_qinv_pos _ Hzwb).
  apply (mixe_qlt_eq_r
           (mixe_qofnat k * (w * b0) * Qinv (w * b0))
           (mixe_qofnat k)
           ((Qminus tv0 b0) * Qinv (w * b0))).
  - apply (Qeq_trans (mixe_qofnat k * (w * b0) * Qinv (w * b0))
             (mixe_qofnat k * ((w * b0) * Qinv (w * b0)))).
    + ring.
    + assert (Hone2 : (w * b0) * Qinv (w * b0) == 1).
      { apply (Qmult_inv_r (w * b0)).
        intro Heq. exact (Qlt_irrefl 0 (mixe_qlt_eq_r (w * b0) 0 0 Heq Hzwb)). }
      rewrite Hone2.
      apply (Qmult_1_r _).
  - exact (Qmult_lt_compat_r (Qminus tv0 b0) (mixe_qofnat k * (w * b0))
             (Qinv (w * b0)) Hinv (mixe_cf_cap w b0 tv0 k Hw Hb0 Hacc)).
Qed.

(* ============================================================ *)
(* Part 3：闭式 k-公式选择器（无搜索、Defined 可提取——封顶对象本体）       *)
(*   k := 1 + floor( (TV0'-b0)/(w*b0) )：纯代数解出，零谓词迭代            *)
(* ============================================================ *)

Definition mixe_cf_select (w b0 tv0 : Q) : nat :=
  Datatypes.S (Z.to_nat (Qfloor (Qminus tv0 b0 * Qinv (w * b0)))).

(* 封顶于选择器返回值：k > (TV0'-b0)/(w*b0) = (TV0'/b0 - 1)/w（下界封死） *)
Theorem mixe_cf_select_cap : forall (w b0 tv0 : Q),
  Qlt ((Qminus tv0 b0) * Qinv (w * b0)) (mixe_qofnat (mixe_cf_select w b0 tv0)).
Proof.
  intros w b0 tv0.
  unfold mixe_cf_select.
  exact (mixe_qfloor_lt (Qminus tv0 b0 * Qinv (w * b0))).
Qed.

(* 闭式选择器自证：返回的 k 使 affine 接受闭合（公式即解） *)
Theorem mixe_cf_select_accept : forall (w b0 tv0 : Q),
  Qlt 0 w -> Qlt 0 b0 ->
  mixe_cf_accept w b0 tv0 (mixe_cf_select w b0 tv0) = true.
Proof.
  intros w b0 tv0 Hw Hb0.
  assert (Hzwb : Qlt 0 (w * b0)) by exact (mixe_qmult_pos w b0 Hw Hb0).
  assert (Hrk : Qlt ((Qminus tv0 b0) * Qinv (w * b0))
                    (mixe_qofnat (mixe_cf_select w b0 tv0)))
    by exact (mixe_cf_select_cap w b0 tv0).
  assert (Hmult : Qlt ((Qminus tv0 b0 * Qinv (w * b0)) * (w * b0))
                      (mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0)))
    by exact (Qmult_lt_compat_r _ _ _ Hzwb Hrk).
  assert (HeqL : Qeq ((Qminus tv0 b0 * Qinv (w * b0)) * (w * b0))
                     (Qminus tv0 b0)).
  { apply (Qeq_trans ((Qminus tv0 b0 * Qinv (w * b0)) * (w * b0))
             (Qminus tv0 b0 * ((w * b0) * Qinv (w * b0)))).
    - ring.
    - assert (Hone2 : (w * b0) * Qinv (w * b0) == 1).
      { apply (Qmult_inv_r (w * b0)).
        intro Heq. exact (Qlt_irrefl 0 (mixe_qlt_eq_r (w * b0) 0 0 Heq Hzwb)). }
      rewrite Hone2.
      apply (Qmult_1_r _). }
  assert (Hlt2 : Qlt (Qminus tv0 b0)
                     (mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0))).
  { apply (mixe_qlt_eq_l (Qminus tv0 b0)
             ((Qminus tv0 b0) * Qinv (w * b0) * (w * b0))
             (mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0))).
    - exact (Qeq_sym _ _ HeqL).
    - exact Hmult. }
  assert (Hplus : Qlt (b0 + Qminus tv0 b0)
                      (b0 + mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0))).
  { apply (mixe_qlt_eq_r
             (mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0) + b0)
             (b0 + mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0))
             (b0 + Qminus tv0 b0)).
    - ring.
    - apply (mixe_qlt_eq_l (b0 + Qminus tv0 b0)
               (Qminus tv0 b0 + b0)
               (mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0) + b0)).
      + ring.
      + exact (mixe_qlt_plus_r (Qminus tv0 b0)
                 (mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0)) b0 Hlt2). }
  apply mixe_qlt_bool_true.
  apply (mixe_qlt_eq_r
           (b0 + mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0))
           (b0 * (1 + mixe_qofnat (mixe_cf_select w b0 tv0) * w))
           tv0).
  - ring.
  - apply (mixe_qlt_eq_l tv0 (b0 + Qminus tv0 b0)
             (b0 + mixe_qofnat (mixe_cf_select w b0 tv0) * (w * b0))).
    + ring.
    + exact Hplus.
Qed.

(* 闭式路线完整健全性：返回 k 携带真值证书 (1-w)^k * tv0 < b0 *)
Theorem mixe_cf_select_cert : forall (w b0 tv0 : Q),
  Qlt 0 w -> Qle w 1 -> Qle 0 tv0 -> Qlt 0 b0 ->
  Qlt (mixe_qpow (1 - w) (mixe_cf_select w b0 tv0) * tv0) b0.
Proof.
  intros w b0 tv0 Hw Hw1 Htv0 Hb0.
  apply (mixe_cf_sound_affine w b0 tv0 (mixe_cf_select w b0 tv0)).
  - exact (Qlt_le_weak 0 w Hw).
  - exact Hw1.
  - exact Htv0.
  - exact (mixe_cf_select_accept w b0 tv0 Hw Hb0).
Qed.

(* ============================================================ *)
(* Part 4：自检锚（vm_compute 直验，w = 1#10；Qle/Qlt 侧以 bool 面直算） *)
(*   ① 族两侧 k=9 vs k=10：接受谓词 39/20 界两侧                           *)
(*   ② 封顶两侧：cap 实例 9 侧违反 / 10 侧满足                            *)
(*   ③ 线性 vs 对数对照：闭式 k=91（TV0'=1, b0=1/10）——                    *)
(*      真值最小站 k=22（可判定搜索域），锐化成员站 k=25                   *)
(* ============================================================ *)

Example mixe_smoke_bern_sharp_9 :
  Qle_bool (mixe_qpow (9 # 10) 9 * (1 + mixe_qofnat 9 * (1 # 10))) 1 = true.
Proof. vm_compute. reflexivity. Qed.

Example mixe_smoke_bern_sharp_10 :
  Qle_bool (mixe_qpow (9 # 10) 10 * (1 + mixe_qofnat 10 * (1 # 10))) 1 = true.
Proof. vm_compute. reflexivity. Qed.

Example mixe_smoke_accept_9_false :
  mixe_cf_accept (1 # 10) 1 (39 # 20) 9%nat = false.
Proof. vm_compute. reflexivity. Qed.

Example mixe_smoke_accept_10_true :
  mixe_cf_accept (1 # 10) 1 (39 # 20) 10%nat = true.
Proof. vm_compute. reflexivity. Qed.

Example mixe_smoke_cap_9_side :
  mixe_qlt_bool ((39 # 20) - 1) (mixe_qofnat 9 * ((1 # 10) * 1)) = false.
Proof. vm_compute. reflexivity. Qed.

Example mixe_smoke_cap_10_side :
  mixe_qlt_bool ((39 # 20) - 1) (mixe_qofnat 10 * ((1 # 10) * 1)) = true.
Proof. vm_compute. reflexivity. Qed.

(* 闭式 k-公式返回 91：k = 1 + floor((1 - 1/10)/(1/10 * 1)) = 1 + 90 *)
Example mixe_smoke_select_91 :
  mixe_cf_select (1 # 10) (1 # 10) 1 = 91%nat.
Proof. vm_compute. reflexivity. Qed.

Example mixe_smoke_select_cert_91 :
  mixe_qlt_bool (mixe_qpow (9 # 10) 91 * 1) (1 # 10) = true.
Proof. vm_compute. reflexivity. Qed.

(* 对照：真值最小站 k=22（(9/10)^22 < 1/10）——affine 闭式接受在 k=22        *)
(* 尚未闭合：线性 91 vs 真最小 22 的方法论差距为可计算见证 *)
Example mixe_smoke_true_min_22 :
  mixe_qlt_bool (mixe_qpow (9 # 10) 22 * 1) (1 # 10) = true.
Proof. vm_compute. reflexivity. Qed.

Example mixe_smoke_affine_not_22 :
  mixe_cf_accept (1 # 10) (1 # 10) 1 22%nat = false.
Proof. vm_compute. reflexivity. Qed.

(* 锐化成员接受站：1 < (1/10)(11/10)^25（k=24 假 / k=25 真）——              *)
(* 单调可判定谓词的最小通过站 = 可判定搜索（A/B/D 席）的对数量级来源 *)
Example mixe_smoke_sharp_24_false :
  mixe_cf_accept_sharp (1 # 10) (1 # 10) 1 24%nat = false.
Proof. vm_compute. reflexivity. Qed.

Example mixe_smoke_sharp_25_true :
  mixe_cf_accept_sharp (1 # 10) (1 # 10) 1 25%nat = true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* G4 审计口（全 Closed 预期：零新增公理）                                *)
(* ============================================================ *)

Print Assumptions mixe_bern_sharp.
Print Assumptions mixe_bern_lower.
Print Assumptions mixe_sharp_pair.
Print Assumptions mixe_cf_sound_affine.
Print Assumptions mixe_cf_sound_sharp.
Print Assumptions mixe_cf_cap_gen.
Print Assumptions mixe_cf_cap.
Print Assumptions mixe_cf_cap_div.
Print Assumptions mixe_cf_select_cap.
Print Assumptions mixe_cf_select_accept.
Print Assumptions mixe_cf_select_cert.
Print Assumptions mixe_cf_select.
