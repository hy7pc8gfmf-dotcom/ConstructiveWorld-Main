(* ============================================================ *)
(* UpReqBanachInstEMult.v —— 席E2：ConstructiveWorld 路径 B       *)
(*   E-载体乘法群席（20260913，后台独立作业）                      *)
(* ============================================================ *)
(* 使命：消费 UpReqBanachInstB 的 E-载体正件（bxib_E 自由项树 +    *)
(*   bxib_ev 求值 + bxib_bae 规范形 Leibniz 判据），补齐 INSTB     *)
(*   挂账①的乘法群：                                              *)
(*   保底三件 = bxem_mult（定义）+ bxem_mult_wd（bae-良定义）      *)
(*            + bxem_mult_assoc（结合律，R2L 向对齐类字段）。      *)
(*   主件     = bxem_one + 单位律 l/r + 分配律 l/r + 交换律        *)
(*            + bxem_mult_zero（类字段 bmult_zero 位）。           *)
(*   席间回赠 = bxem_bplus_wd / bxem_bopp_wd（INSTB 挂账 ⓪′/⓪的   *)
(*            wd 位——本席双 qnorm 塌缩技术同款即可闭合）。         *)
(* 选型账：乘法定义取载体既有构造子位 bxib_emult（E 是自由项树，   *)
(*   ev 在 emult 位已按 qnorm∘Qmult 复合，零新算术）；全部代数律    *)
(*   = stdlib Qmult 引擎（Qmult_assoc/1_l/1_r/0_r/comm/plus_distr）*)
(*   + bxib_qnorm_fix（换心）+ bxib_qnorm_fix_id（双 qnorm 塌缩）  *)
(*   + bxib_qnorm_id_of_qeqT（Id 收口）三件套，与 INSTB bplus 同款。 *)
(* 铁律自审：公理面零命中；语句面全 Set（bae/Id/QeqT）；冻结件与   *)
(*   Pre/ExpAddEq/CauchyD 零改动（仅 Require 消费）；前缀 bxem_    *)
(*   零撞名。                                                     *)
(* 工程注：目标内含 bxib_qnorm（Z.gcd/Z.div）的子项一律禁 simpl，   *)
(*   走 change 显式 iota + 引理改写；Qeq 改写面与 INSTB 同款。      *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpReqBanachInstB.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* E0：乘法定义与单位元（构造子位选型，零新算术）                   *)
(* ============================================================ *)

Definition bxem_mult (a b : bxib_E) : bxib_E := bxib_emult a b.

Definition bxem_one : bxib_E := bxib_esc 1%Q.

(* ---- QeqT 乘法cong（镜像 INSTB bxib_qeqT_cong_plus，stdlib 缺口） ---- *)

Lemma bxem_qeqT_cong_mult : forall a b c d : Q,
  QeqT a b -> QeqT c d -> QeqT (Qmult a c) (Qmult b d).
Proof.
  intros a b c d Hab Hcd. apply qeq_imp_qeqT.
  apply qeqT_imp_qeq in Hab. apply qeqT_imp_qeq in Hcd.
  rewrite <- Hab, <- Hcd. apply Qeq_refl.
Qed.

(* ---- 通用桥：bae x y -> QeqT (ev x) (ev y)（bae 判据开锁件） ---- *)

Lemma bxem_qeqT_of_bae : forall a b : bxib_E,
  bxib_bae a b -> QeqT (bxib_ev a) (bxib_ev b).
Proof.
  intros a b H.
  apply (bxib_qeqT_trans _ (bxib_qnorm (bxib_ev a)) _).
  - apply bxib_qeqT_sym. apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxib_ev b)) _).
    + exact (bxib_qeqT_of_id _ _ H).
    + apply bxib_qnorm_fix.
Qed.

(* ============================================================ *)
(* E1：保底件②——bxem_mult_wd（bae-良定义）                        *)
(*   双 qnorm 塌缩（fix_id）+ 求值像 Q 层 cong_mult + id_of_qeqT。  *)
(* ============================================================ *)

Lemma bxem_mult_wd : forall a b c d : bxib_E,
  bxib_bae a c -> bxib_bae b d ->
  bxib_bae (bxem_mult a b) (bxem_mult c d).
Proof.
  intros a b c d Hac Hbd. unfold bxem_mult, bxib_bae.
  change (bxib_ev (bxib_emult a b))
    with (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev b))).
  change (bxib_ev (bxib_emult c d))
    with (bxib_qnorm (Qmult (bxib_ev c) (bxib_ev d))).
  pose proof (bxem_qeqT_cong_mult (bxib_ev a) (bxib_ev c)
                (bxib_ev b) (bxib_ev d)
                (bxem_qeqT_of_bae a c Hac) (bxem_qeqT_of_bae b d Hbd)) as H.
  exact (id_trans
    (id_trans (bxib_qnorm_fix_id (Qmult (bxib_ev a) (bxib_ev b)))
              (bxib_qnorm_id_of_qeqT _ _ H))
    (id_sym (bxib_qnorm_fix_id (Qmult (bxib_ev c) (bxib_ev d))))).
Qed.

(* ============================================================ *)
(* E2：保底件③——bxem_mult_assoc（结合律，R2L 向对齐               *)
(*   bxin_bmult_assoc：bae (mult a (mult b c)) (mult (mult a b) c)） *)
(* ============================================================ *)

Lemma bxem_mult_assoc : forall a b c : bxib_E,
  bxib_bae (bxem_mult a (bxem_mult b c))
           (bxem_mult (bxem_mult a b) c).
Proof.
  intros a b c. unfold bxem_mult, bxib_bae.
  change (bxib_ev (bxib_emult a (bxib_emult b c)))
    with (bxib_qnorm (Qmult (bxib_ev a)
            (bxib_qnorm (Qmult (bxib_ev b) (bxib_ev c))))).
  change (bxib_ev (bxib_emult (bxib_emult a b) c))
    with (bxib_qnorm (Qmult (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev b)))
                            (bxib_ev c))).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _
    (Qmult (bxib_ev a) (Qmult (bxib_ev b) (bxib_ev c))) _).
  - apply (bxib_qeqT_trans _
      (Qmult (bxib_ev a)
             (bxib_qnorm (Qmult (bxib_ev b) (bxib_ev c)))) _).
    + apply bxib_qnorm_fix.
    + apply bxem_qeqT_cong_mult.
      * apply bxib_qeqT_refl.
      * apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _
      (Qmult (Qmult (bxib_ev a) (bxib_ev b)) (bxib_ev c)) _).
    + apply qeq_imp_qeqT. apply Qmult_assoc.
    + apply (bxib_qeqT_trans _
        (Qmult (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev b)))
               (bxib_ev c)) _).
      * apply bxem_qeqT_cong_mult.
        -- apply bxib_qeqT_sym. apply bxib_qnorm_fix.
        -- apply bxib_qeqT_refl.
      * apply bxib_qeqT_sym. apply bxib_qnorm_fix.
Qed.

(* ============================================================ *)
(* E3：主件——单位律 / 分配律 / 交换律 / 零吸收（乘法群成套）        *)
(* ============================================================ *)

Lemma bxem_mult_one_l : forall a : bxib_E,
  bxib_bae (bxem_mult bxem_one a) a.
Proof.
  intro a. unfold bxem_mult, bxem_one, bxib_bae.
  change (bxib_ev (bxib_emult (bxib_esc 1%Q) a))
    with (bxib_qnorm (Qmult 1%Q (bxib_ev a))).
  apply (id_trans (bxib_qnorm_fix_id (Qmult 1%Q (bxib_ev a)))).
  apply bxib_qnorm_id_of_qeqT. apply qeq_imp_qeqT. apply Qmult_1_l.
Qed.

Lemma bxem_mult_one_r : forall a : bxib_E,
  bxib_bae (bxem_mult a bxem_one) a.
Proof.
  intro a. unfold bxem_mult, bxem_one, bxib_bae.
  change (bxib_ev (bxib_emult a (bxib_esc 1%Q)))
    with (bxib_qnorm (Qmult (bxib_ev a) 1%Q)).
  apply (id_trans (bxib_qnorm_fix_id (Qmult (bxib_ev a) 1%Q))).
  apply bxib_qnorm_id_of_qeqT. apply qeq_imp_qeqT. apply Qmult_1_r.
Qed.

Lemma bxem_distrib_l : forall a b c : bxib_E,
  bxib_bae (bxem_mult a (bxib_eplus b c))
           (bxib_eplus (bxem_mult a b) (bxem_mult a c)).
Proof.
  intros a b c. unfold bxem_mult, bxib_bae.
  change (bxib_ev (bxib_emult a (bxib_eplus b c)))
    with (bxib_qnorm (Qmult (bxib_ev a)
            (bxib_qnorm (Qplus (bxib_ev b) (bxib_ev c))))).
  change (bxib_ev (bxib_eplus (bxib_emult a b) (bxib_emult a c)))
    with (bxib_qnorm (Qplus (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev b)))
                            (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev c))))).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _
    (Qmult (bxib_ev a) (Qplus (bxib_ev b) (bxib_ev c))) _).
  - apply (bxib_qeqT_trans _
      (Qmult (bxib_ev a)
             (bxib_qnorm (Qplus (bxib_ev b) (bxib_ev c)))) _).
    + apply bxib_qnorm_fix.
    + apply bxem_qeqT_cong_mult.
      * apply bxib_qeqT_refl.
      * apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _
      (Qplus (Qmult (bxib_ev a) (bxib_ev b))
             (Qmult (bxib_ev a) (bxib_ev c))) _).
    + apply qeq_imp_qeqT. apply Qmult_plus_distr_r.
    + apply (bxib_qeqT_trans _
        (Qplus (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev b)))
               (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev c)))) _).
      * apply bxib_qeqT_cong_plus.
        -- apply bxib_qeqT_sym. apply bxib_qnorm_fix.
        -- apply bxib_qeqT_sym. apply bxib_qnorm_fix.
      * apply bxib_qeqT_sym. apply bxib_qnorm_fix.
Qed.

Lemma bxem_distrib_r : forall a b c : bxib_E,
  bxib_bae (bxem_mult (bxib_eplus a b) c)
           (bxib_eplus (bxem_mult a c) (bxem_mult b c)).
Proof.
  intros a b c. unfold bxem_mult, bxib_bae.
  change (bxib_ev (bxib_emult (bxib_eplus a b) c))
    with (bxib_qnorm (Qmult (bxib_qnorm (Qplus (bxib_ev a) (bxib_ev b)))
                            (bxib_ev c))).
  change (bxib_ev (bxib_eplus (bxib_emult a c) (bxib_emult b c)))
    with (bxib_qnorm (Qplus (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev c)))
                            (bxib_qnorm (Qmult (bxib_ev b) (bxib_ev c))))).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _
    (Qmult (Qplus (bxib_ev a) (bxib_ev b)) (bxib_ev c)) _).
  - apply (bxib_qeqT_trans _
      (Qmult (bxib_qnorm (Qplus (bxib_ev a) (bxib_ev b)))
             (bxib_ev c)) _).
    + apply bxib_qnorm_fix.
    + apply bxem_qeqT_cong_mult.
      * apply bxib_qnorm_fix.
      * apply bxib_qeqT_refl.
  - apply (bxib_qeqT_trans _
      (Qplus (Qmult (bxib_ev a) (bxib_ev c))
             (Qmult (bxib_ev b) (bxib_ev c))) _).
    + apply qeq_imp_qeqT. apply Qmult_plus_distr_l.
    + apply (bxib_qeqT_trans _
        (Qplus (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev c)))
               (bxib_qnorm (Qmult (bxib_ev b) (bxib_ev c)))) _).
      * apply bxib_qeqT_cong_plus.
        -- apply bxib_qeqT_sym. apply bxib_qnorm_fix.
        -- apply bxib_qeqT_sym. apply bxib_qnorm_fix.
      * apply bxib_qeqT_sym. apply bxib_qnorm_fix.
Qed.

Lemma bxem_mult_comm : forall a b : bxib_E,
  bxib_bae (bxem_mult a b) (bxem_mult b a).
Proof.
  intros a b. unfold bxem_mult, bxib_bae.
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qnorm_qeqT_of_qeqT. apply qeq_imp_qeqT. apply Qmult_comm.
Qed.

Lemma bxem_mult_zero : forall a : bxib_E,
  bxib_bae (bxem_mult a bxib_ez) bxib_ez.
Proof.
  intro a. unfold bxem_mult, bxib_bae.
  change (bxib_ev (bxib_emult a bxib_ez))
    with (bxib_qnorm (Qmult (bxib_ev a) 0%Q)).
  change (bxib_ev bxib_ez) with (0#1)%Q.
  apply (id_trans (bxib_qnorm_fix_id (Qmult (bxib_ev a) 0%Q))).
  apply bxib_qnorm_id_of_qeqT. apply qeq_imp_qeqT. apply Qmult_0_r.
Qed.

(* ============================================================ *)
(* E4：席间回赠——INSTB 挂账 ⓪′/⓪ 的 wd 位（同款塌缩技术顺收）      *)
(*   （bxem_bplus_wd / bxem_bopp_wd：装配位与类字段 bplus_wd/       *)
(*    bopp_wd 逐字同形，W6 可直取。）                              *)
(* ============================================================ *)

Lemma bxem_bplus_wd : forall a b c d : bxib_E,
  bxib_bae a c -> bxib_bae b d ->
  bxib_bae (bxib_eplus a b) (bxib_eplus c d).
Proof.
  intros a b c d Hac Hbd. unfold bxib_bae.
  change (bxib_ev (bxib_eplus a b))
    with (bxib_qnorm (Qplus (bxib_ev a) (bxib_ev b))).
  change (bxib_ev (bxib_eplus c d))
    with (bxib_qnorm (Qplus (bxib_ev c) (bxib_ev d))).
  pose proof (bxib_qeqT_cong_plus (bxib_ev a) (bxib_ev c)
                (bxib_ev b) (bxib_ev d)
                (bxem_qeqT_of_bae a c Hac) (bxem_qeqT_of_bae b d Hbd)) as H.
  exact (id_trans
    (id_trans (bxib_qnorm_fix_id (Qplus (bxib_ev a) (bxib_ev b)))
              (bxib_qnorm_id_of_qeqT _ _ H))
    (id_sym (bxib_qnorm_fix_id (Qplus (bxib_ev c) (bxib_ev d))))).
Qed.

Lemma bxem_bopp_wd : forall a b : bxib_E,
  bxib_bae a b -> bxib_bae (bxib_eopp a) (bxib_eopp b).
Proof.
  intros a b H. unfold bxib_bae.
  change (bxib_ev (bxib_eopp a)) with (Qopp (bxib_ev a)).
  change (bxib_ev (bxib_eopp b)) with (Qopp (bxib_ev b)).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_opp. apply bxem_qeqT_of_bae. exact H.
Qed.

(* ============================================================ *)
(* 提取探针（G3 面）                                              *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction bxem_mult bxem_one bxem_mult_wd bxem_mult_assoc
  bxem_mult_one_l bxem_mult_one_r bxem_distrib_l bxem_distrib_r
  bxem_mult_comm bxem_mult_zero bxem_bplus_wd bxem_bopp_wd.

Print Assumptions bxem_mult_wd.
Print Assumptions bxem_mult_assoc.
Print Assumptions bxem_mult_one_l.
Print Assumptions bxem_mult_one_r.
Print Assumptions bxem_distrib_l.
Print Assumptions bxem_distrib_r.
Print Assumptions bxem_mult_comm.
Print Assumptions bxem_mult_zero.
Print Assumptions bxem_bplus_wd.
Print Assumptions bxem_bopp_wd.
