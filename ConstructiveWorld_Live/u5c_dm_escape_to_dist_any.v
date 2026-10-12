(* 五字段指针｜使命：√2 闭式分离常元件的边距参数化桥引理——
   把 u5c_bridge 的 u5c_escape_to_dist（逃逸→分离）泛化为任意合格常元：
   分离常数 c 首次成为显式参数而非源定理内构的折半值（原版 c := (|q−x(n0)|−e(n0))/2），
   改配两条边距假设：正性 QltT 0 c 与余量下界 QleT' (c+c) (|q−x(n0)|−e(n0))。
   结论与源定理同形：real_const c 与柯西极限 X（real_metric (lic_seq_cauchy …) (real_const q)）
   之间有 real_lt 分离（见证 ε:=c、逃逸点 n0）。证明链为 u5c_escape_to_dist 的逐字改造：
   源定理的 Qlt_bool 分裂段（lic_qlt_dec_le + lic_qlt_bool 两分支反证）由直链严格推理替代——
   A == (A − e n0) + e n0 改写入 Qlt A (Bk + e n0) 后经 lic_qlt_add_r_cancel_r
   右端消去得 Qlt (A − e n0) Bk，再以 Qle_lt_trans 接边距假设得 Qlt (c+c) Bk，
   全程无 Qlt_bool 分裂；边距假设经自携微转换 dmec_qleT'_qle（QleT' 展开
   Qle_bool/Qcompare 降 Qle 层，同 S02 QleT'_to_Qle 技艺）接入，禁引他件。
   依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、SumInvFactEscape、
   UpReqBanachNormOpp、UpReqIrrationalCriterion；Stdlib QArith、Qabs、
   ZArith、Arith、Bool、Setoid、Morphisms、Qfield。
   对标行：u5c_bridge.v u5c_escape_to_dist（源定理）；
   UpReqIrrationalCriterion.v lic_irrational_criterion。
   构造性注记：语句面全 Set 层（sigT/prod/QltT/QleT'/real_lt），零 Prop 前提位；
   分离常数正性来自显式参数假设 QltT 0 c，严格性由尾控 lic_tail_bounded
   与边距 QleT' (c+c) (|q−x(n0)| − e(n0)) 直链导出；证明链全构造、零承认、零经典逻辑。
   编译配方：source Live/toolchain/env.sh 后
   rocq c -native-compiler no -q -Q . "" u5c_dm_escape_to_dist_any.v。 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Setoid Morphisms Qfield.

(* ============================================================ *)
(* S0：自携微转换：QleT' 降 Qle 层（边距假设接入用，不引他件）     *)
(* ============================================================ *)

Lemma dmec_qleT'_qle : forall x y : Q, QleT' x y -> Qle x y.
Proof.
  intros x y H.
  unfold QleT' in H.
  (* 本件 Require 序同 u5c_bridge（在册库件在前、Stdlib 在后），
     裸名 Qle_bool 归 Stdlib，体内 S02 自建常元须以全名展开 *)
  unfold S02_CauchyComplete.Qle_bool in H.
  unfold Qcompare in H.
  unfold Qle.
  change ((Qnum x * QDen y ?= Qnum y * QDen x)%Z <> Gt).
  destruct (Qnum x * QDen y ?= Qnum y * QDen x)%Z eqn:E; simpl in H;
    try (inversion H); try (intro Hc; inversion Hc).
Qed.

(* ============================================================ *)
(* S1：边距参数化分离引理（常元 c 显式参数版）                          *)
(* ============================================================ *)

(* 边距参数化逃逸分离：q 在 n0 ≥ 1 处逃出 e(n0) 窗，且常元 c 满足
   0 < c 与 2c ≤ |q − x(n0)| − e(n0)，则 real_const c 与
   x 的柯西极限（尾控 + 消失导出）和 real_const q 之度量之间有 real_lt 分离。 *)
Lemma dmec_escape_to_dist_any :
  forall (x e : nat -> Q)
    (Ht : lic_tail_bounded x e) (Hv : lic_vanish e),
  forall (q : Q) (n0 : nat), (1 <= n0)%nat ->
    QltT (e n0) (Qabs ((q - x n0)%Q)) ->
    forall c : Q, QltT 0 c ->
    QleT' ((c + c)%Q) ((Qabs ((q - x n0)%Q) - e n0)%Q) ->
    sigT (fun c : Q => And (QltT 0 c)
      (real_lt (real_const c)
         (real_metric (existT (fun u : Qseq => cauchy u) x
                          (lic_seq_cauchy x e Ht Hv))
                      (real_const q)))).
Proof.
  intros x e Ht Hv q n0 Hn01 Hesc c Hc0 Hmarg.
  remember (Qabs ((q - x n0)%Q)) as A eqn:HA.
  pose proof (dmec_qleT'_qle (c + c) (A - e n0) Hmarg) as Hmarg'.
  exists c.
  split.
  - exact Hc0.
  - unfold real_lt.
    exists c.
    split.
    + exact Hc0.
    + exists n0. intros k HkN.
      apply NatLe_drop in HkN.
      pose proof (QltT_to_Qlt _ _ (Ht n0 k Hn01 HkN)) as Ht0'.
      assert (Hpre : (q - x n0)%Q == ((q - x k) + (x k - x n0))%Q)
        by exact (lic_qlt_tri_decomp q (x n0) (x k)).
      assert (Htri : Qle (Qabs ((q - x n0)%Q))
                         (Qabs ((q - x k)%Q) + Qabs ((x k - x n0)%Q))).
      { pose proof (Qabs_triangle ((q - x k)%Q) ((x k - x n0)%Q)) as HT.
        apply (Qle_trans (Qabs ((q - x n0)%Q))
                 (Qabs (((q - x k) + (x k - x n0))%Q))).
        - apply qeq_le. setoid_rewrite Hpre. apply Qeq_refl.
        - exact HT. }
      rewrite <- HA in Htri.
      remember (Qabs ((q - x k)%Q)) as Bk eqn:HB.
      remember (Qabs ((x k - x n0)%Q)) as Ek eqn:HE.
      assert (Hlt1 : Qlt (Bk + Ek) (Bk + e n0))
        by (apply (lic_qlt_add_l Bk Ek (e n0)); exact Ht0').
      assert (Hlt2 : Qlt A (Bk + e n0))
        by (apply (Qle_lt_trans A (Bk + Ek)); [exact Htri | exact Hlt1]).
      (* 泛化替代段：A == (A − e n0) + e n0 改写后右端消去——直链严格，
         替代源定理的 Qlt_bool 分裂反证 *)
      assert (HA2 : A == ((A - e n0) + e n0)%Q).
      { symmetry. apply lic_qlt_minus_add_r. }
      rewrite HA2 in Hlt2.
      assert (Hltm : Qlt (A - e n0) Bk)
        by (apply (lic_qlt_add_r_cancel_r (A - e n0) Bk (e n0)); exact Hlt2).
      assert (HltQ : Qlt (c + c) Bk).
      { apply (Qle_lt_trans (c + c) (A - e n0) Bk).
        - exact Hmarg'.
        - exact Hltm. }
      (* 收尾段沿用源定理 u5c_escape_to_dist *)
      assert (Hfin : Qlt c (Bk - c)%Q).
      { apply (lic_qlt_add_r_cancel_r c (Bk - c) c).
        rewrite (lic_qlt_minus_add_r Bk c). exact HltQ. }
      assert (HPr : projT1 (real_metric (existT (fun u : Qseq => cauchy u) x
                                   (lic_seq_cauchy x e Ht Hv)) (real_const q)) k
                  == Qabs ((x k - q)%Q))
        by apply lic_metric_proj.
      apply (lic_qltt_comp_r ((Qabs ((q - x k)%Q)) - c)
               (projT1 (real_metric (existT (fun u : Qseq => cauchy u) x
                                      (lic_seq_cauchy x e Ht Hv)) (real_const q)) k
                - projT1 (real_const c) k) c).
      -- rewrite real_const_proj. rewrite HPr.
         rewrite (Qabs_Qminus q (x k)). reflexivity.
      -- rewrite HB in Hfin. apply Qlt_to_QltT. exact Hfin.
(* 语句面修复申报：Qed→Defined（sigT 见证须透明，以支撑下游以 Qeq 确定常元的装配） *)
Defined.

From Stdlib Require Import Extraction.
Separate Extraction dmec_qleT'_qle dmec_escape_to_dist_any.

Print Assumptions dmec_escape_to_dist_any.
