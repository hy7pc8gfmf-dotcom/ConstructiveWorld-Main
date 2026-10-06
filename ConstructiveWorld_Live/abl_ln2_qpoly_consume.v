(* ===================================================================== *)
(*  abl_ln2_qpoly_consume.v —— ln2 无理性链路线③·除法使用件（CO·ln2）    *)
(*                                                                        *)
(*  ①使命: 使用已闭合除法引擎（CC 线性特例 abl_qpoly_divmod + CK 一般形     *)
(*     abl_qpoly_divmod_gen）于 AE 报告路线③ Beukers 载体恒等式除法位:     *)
(*     被除式 t^n(1-t)^n（QPoly 稠密编码 lnc_bk_num）÷ 除式 (1-t/2)^(n+1)   *)
(*     （编码 lnc_bk_den = 幂底 1 + t·(-(1#2)) 之 lnc_pow；真首项非零，     *)
(*     qpg_divisor_ok 良态成立），产出链级三肢:                             *)
(*     (a) 分解恒等式 lnc_consume_id_*（qpd_divmod_gen_pred 双肢投影，      *)
(*         QeqT/Id Set 面）；                                              *)
(*     (b) 极点残值 lnc_residue_pole_*: 余式 R 在极点 t=2 处 R(2)=(−2)^n    *)
(*         （QeqT Set 面；u=1−t/2 坐标下即尾系数 d_{n+1}=(−2)^n）；          *)
(*     (c) 残数整性 lnc_d1_int_*: d_1 := [u^n]R（lnc_comp2 坐标代入后       *)
(*         nth n）满足 d_1 == 2^n·q̃_n（bk_Qn_qtilde，BeukersLists 在树锚），*)
(*         sigT z + QeqT 交付——与 BD 前件 lni_bvp_lcm_int 同型（Z 面衔接）， *)
(*         数值锚: d_1: 6/52/504（n=1/2/3），q̃_n: 3/13/63，A_3=2·504=1008   *)
(*         与 AE 报告 I_3=1008·ln2−2096/3 残数锚衔接。                      *)
(*  ②依赖: abl_tmine04_pool/ln2_consume/（独占自建；引擎双件    *)
(*     + ln2_numer 前件 abl_ln2_numer_int.v 拷入，链序编译）。              *)
(*  ③编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&         *)
(*     ulimit -s 65532 && nice -19 rocq c -native-compiler no              *)
(*     -Q vo_local_world_unified_0930 "" 本件；起编前道闸 ps rocq 计 0。    *)
(*  ④构造性: 零公理零承认零放弃零经典（G1 禁词面零命中）；交付定理面         *)
(*     sigT/QeqT/Id（Set 层）；数值锚（lnc_pin_* 之 eq/Qeq_bool 形）沿 CC    *)
(*     BF 烟测既定形态；工具引理 Qeq 面为证内脚手架（E236 工艺: 闭合恒等式   *)
(*     一律抽纯变量 ring 引理独立 Qed）；经验卡 FRACDIVSHAPE 工艺: 计算定装  *)
(*     一律 Qeq_bool 可计算相等桥，不以 Qmake 字面硬统一；文尾 Separate     *)
(*     Extraction + PA 全 Closed 取证（红线四条）。                          *)
(*  ⑤边界: 一般 n 的良态/分解/残数三肢登记接口（lnc_den_ok_type /          *)
(*     lnc_div_gen_type / lnc_d1_gen_type）不施工（首件策略 45 分钟切片）； *)
(*     数值定装 n=0,1,2,3 四实例（含线性因式 n=1÷(1−t/2) 通链实例）；       *)
(*     唯一性肢/一般 u 展开声音性已由 lnc_comp2_eval 闭合，指数衰减上界    *)
(*     与 Ireal 装配不在本件面（AE 路线③(ⅲ) 后续件）。                     *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qfield.
From Stdlib Require Import Lists.List Arith.Arith ZArith.ZArith Lia Extraction.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp PolyIntegral.
Require Import BeukersLists.
Require Import abl_qpoly_divmod abl_qpoly_divmod_gen.
Require Import abl_ln2_numer_int.

Open Scope Q_scope.

(* ============================================================ *)
(* §0 QPoly 运算件（稠密表头=常数项，PolyIntegral 惯例）           *)
(*    经验卡 COEFSTRUCT: 卷积定义形即归纳母题；                    *)
(*    经验卡 E236: 闭合恒等式抽纯变量 ring 引理独立 Qed。          *)
(* ============================================================ *)

Definition lnc_scale (a : Q) (p : list Q) : list Q :=
  map (fun z : Q => a * z) p.

(* Cauchy 卷积：(cons c p')·q = c·q + x·(p'·q) *)
Fixpoint lnc_mul (p q : list Q) : list Q :=
  match p with
  | nil => nil
  | cons c p' => pint_add (lnc_scale c q) (cons 0 (lnc_mul p' q))
  end.

Fixpoint lnc_pow (p : list Q) (k : nat) : list Q :=
  match k with
  | 0%nat => cons 1 nil
  | Datatypes.S k' => lnc_mul p (lnc_pow p k')
  end.

(* 纯变量 ring 闭合引理（E236 工艺） *)
Lemma lnc_ring_scale_step : forall a b e x : Q,
  a * b + x * (a * e) == a * (b + x * e).
Proof. intros a b e x. ring. Qed.

Lemma lnc_ring_mul_step : forall c e z t : Q,
  c * z + (0 + t * (e * z)) == (c + t * e) * z.
Proof. intros c e z t. ring. Qed.

Lemma lnc_eval_map_scale : forall (a : Q) (p : list Q) (x : Q),
  pint_eval (map (fun z : Q => a * z) p) x == a * pint_eval p x.
Proof.
  intros a p x. induction p as [|b p' IH].
  - cbn [map pint_eval]. ring.
  - cbn [map pint_eval]. rewrite IH. apply lnc_ring_scale_step.
Qed.

Lemma lnc_eval_scale : forall (a : Q) (p : list Q) (x : Q),
  pint_eval (lnc_scale a p) x == a * pint_eval p x.
Proof. intros a p x. unfold lnc_scale. apply lnc_eval_map_scale. Qed.

Lemma lnc_eval_mul : forall (p q : list Q) (x : Q),
  pint_eval (lnc_mul p q) x == pint_eval p x * pint_eval q x.
Proof.
  induction p as [|c p' IH]; intros q x.
  - cbn [lnc_mul]. rewrite qpd_eval_nil. ring.
  - cbn [lnc_mul].
    rewrite qpd_eval_add, lnc_eval_scale.
    rewrite (qpd_eval_cons 0 (lnc_mul p' q) x).
    rewrite IH.
    rewrite (qpd_eval_cons c p' x).
    apply lnc_ring_mul_step.
Qed.

Lemma lnc_eval_pow : forall (p : list Q) (k : nat) (x : Q),
  pint_eval (lnc_pow p k) x == q_pow (pint_eval p x) k.
Proof.
  intros p k x. induction k as [|k' IH].
  - cbn [lnc_pow q_pow]. rewrite qpd_eval_const. apply Qeq_refl.
  - cbn [lnc_pow]. rewrite lnc_eval_mul, IH. cbn [q_pow]. apply Qeq_refl.
Qed.

(* ============================================================ *)
(* §1 Beukers 编码件: 被除式 t^n(1-t)^n，除式 (1-t/2)^(n+1)        *)
(*    （u=1−t/2 坐标读法见头注；编码面 1 + t·(-(1#2)) 同一多项式）  *)
(* ============================================================ *)

Definition lnc_lin_t : list Q := cons 0 (cons 1 nil).
Definition lnc_lin_1mt : list Q := cons 1 (cons (-1) nil).
Definition lnc_den_lin : list Q := cons 1 (cons (-(1 # 2)) nil).

Fixpoint lnc_bk_num (n : nat) : list Q :=
  match n with
  | 0%nat => cons 1 nil
  | Datatypes.S n' => lnc_mul (lnc_mul lnc_lin_t lnc_lin_1mt) (lnc_bk_num n')
  end.

Definition lnc_bk_den (n : nat) : list Q := lnc_pow lnc_den_lin (Datatypes.S n).

Lemma lnc_eval_lin_t : forall x : Q, pint_eval lnc_lin_t x == x.
Proof. intros x. cbn [lnc_lin_t pint_eval]. ring. Qed.

Lemma lnc_eval_lin_1mt : forall x : Q, pint_eval lnc_lin_1mt x == 1 - x.
Proof. intros x. cbn [lnc_lin_1mt pint_eval]. ring. Qed.

Lemma lnc_eval_den_lin : forall x : Q,
  pint_eval lnc_den_lin x == 1 + x * (-(1 # 2)).
Proof. intros x. cbn [lnc_den_lin pint_eval]. ring. Qed.

Lemma lnc_bk_num_eval : forall (n : nat) (x : Q),
  pint_eval (lnc_bk_num n) x == q_pow (x * (1 - x)) n.
Proof.
  induction n as [|n' IH]; intros x.
  - cbn [lnc_bk_num q_pow]. rewrite qpd_eval_const. apply Qeq_refl.
  - cbn [lnc_bk_num]. rewrite lnc_eval_mul, lnc_eval_mul.
    rewrite lnc_eval_lin_t, lnc_eval_lin_1mt, IH.
    cbn [q_pow]. apply Qeq_refl.
Qed.

Lemma lnc_bk_den_eval : forall (n : nat) (x : Q),
  pint_eval (lnc_bk_den n) x == q_pow (1 + x * (-(1 # 2))) (Datatypes.S n).
Proof.
  intros n x. unfold lnc_bk_den.
  rewrite lnc_eval_pow, lnc_eval_den_lin. apply Qeq_refl.
Qed.

(* u=1−t/2 坐标代入: R(2−2u)（声音性 lnc_comp2_eval；d_1 = nth n） *)
Fixpoint lnc_comp2 (R : list Q) : list Q :=
  match R with
  | nil => nil
  | cons c R' =>
      pint_add (cons c nil)
        (lnc_scale (2 # 1) (lnc_mul lnc_lin_1mt (lnc_comp2 R')))
  end.

Definition lnc_d1 (n : nat) (R : list Q) : Q := nth n (lnc_comp2 R) 0.

Lemma lnc_ring_comp_step : forall c E u : Q,
  c + (2 # 1) * ((1 - u) * E) == c + (2 - 2 * u) * E.
Proof. intros c E u. ring. Qed.

Lemma lnc_comp2_eval : forall (R : list Q) (u : Q),
  pint_eval (lnc_comp2 R) u == pint_eval R (2 - 2 * u).
Proof.
  induction R as [|c R' IH]; intros u.
  - cbn [lnc_comp2 pint_eval]. apply Qeq_refl.
  - cbn [lnc_comp2].
    rewrite qpd_eval_add, qpd_eval_const, lnc_eval_scale, lnc_eval_mul.
    rewrite lnc_eval_lin_1mt, IH.
    rewrite (qpd_eval_cons c R' (2 - 2 * u)).
    apply lnc_ring_comp_step.
Qed.

(* ============================================================ *)
(* §2 除子良态实证（vm_compute 面；CK qpg_ok_xp1 同款工艺）        *)
(* ============================================================ *)

Lemma lnc_den_ok0 : qpg_divisor_ok (lnc_bk_den 0).
Proof.
  unfold qpg_divisor_ok. split.
  - vm_compute. exact id_refl.
  - vm_compute. exact tt.
Defined.

Lemma lnc_den_ok1 : qpg_divisor_ok (lnc_bk_den 1).
Proof.
  unfold qpg_divisor_ok. split.
  - vm_compute. exact id_refl.
  - vm_compute. exact tt.
Defined.

Lemma lnc_den_ok2 : qpg_divisor_ok (lnc_bk_den 2).
Proof.
  unfold qpg_divisor_ok. split.
  - vm_compute. exact id_refl.
  - vm_compute. exact tt.
Defined.

Lemma lnc_den_ok3 : qpg_divisor_ok (lnc_bk_den 3).
Proof.
  unfold qpg_divisor_ok. split.
  - vm_compute. exact id_refl.
  - vm_compute. exact tt.
Defined.

(* ============================================================ *)
(* §3 分解使用实例（qpg_divmod_gen 双肢直投影）                    *)
(*    实例一 n=0：1 ÷ (1−t/2)（线性因式链基例：商 0 余 1）          *)
(* ============================================================ *)

Definition lnc_w0 : list Q * list Q :=
  projT1 (qpg_divmod_gen (lnc_bk_num 0) (lnc_bk_den 0) lnc_den_ok0).

Theorem lnc_consume_id_n0 : forall x : Q,
  QeqT (pint_eval (lnc_bk_num 0) x)
       (pint_eval (lnc_bk_den 0) x * pint_eval (fst lnc_w0) x
        + pint_eval (snd lnc_w0) x).
Proof.
  intros x.
  exact (fst (projT2 (qpg_divmod_gen (lnc_bk_num 0) (lnc_bk_den 0)
                                     lnc_den_ok0)) x).
Qed.

Lemma lnc_pin_w0 :
  length (fst lnc_w0) = 0%nat /\
  Qeq_bool (nth 0%nat (snd lnc_w0) 0) (1 # 1) = true.
Proof. vm_compute. split; reflexivity. Qed.

(* 实例二（线性因式通链，首件策略②）：t(1−t) ÷ (1−t/2) ⟹ 商 2+2t 余 −2 *)
Definition lnc_w1lin : list Q * list Q :=
  projT1 (qpg_divmod_gen (lnc_bk_num 1) (lnc_bk_den 0) lnc_den_ok0).

Theorem lnc_consume_id_n1lin : forall x : Q,
  QeqT (pint_eval (lnc_bk_num 1) x)
       (pint_eval (lnc_bk_den 0) x * pint_eval (fst lnc_w1lin) x
        + pint_eval (snd lnc_w1lin) x).
Proof.
  intros x.
  exact (fst (projT2 (qpg_divmod_gen (lnc_bk_num 1) (lnc_bk_den 0)
                                     lnc_den_ok0)) x).
Qed.

Lemma lnc_pin_w1lin :
  length (fst lnc_w1lin) = 2%nat /\ length (snd lnc_w1lin) = 1%nat /\
  Qeq_bool (nth 0%nat (fst lnc_w1lin) 0) 2 = true /\
  Qeq_bool (nth 1%nat (fst lnc_w1lin) 0) 2 = true /\
  Qeq_bool (nth 0%nat (snd lnc_w1lin) 0) (-2) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* 实例三（路线③形 n=1）：t(1−t) ÷ (1−t/2)^2 ⟹ 商 −4 余 4−3t *)
Definition lnc_w1 : list Q * list Q :=
  projT1 (qpg_divmod_gen (lnc_bk_num 1) (lnc_bk_den 1) lnc_den_ok1).

Theorem lnc_consume_id_n1 : forall x : Q,
  QeqT (pint_eval (lnc_bk_num 1) x)
       (pint_eval (lnc_bk_den 1) x * pint_eval (fst lnc_w1) x
        + pint_eval (snd lnc_w1) x).
Proof.
  intros x.
  exact (fst (projT2 (qpg_divmod_gen (lnc_bk_num 1) (lnc_bk_den 1)
                                     lnc_den_ok1)) x).
Qed.

Theorem lnc_consume_deg_n1 : qpd_deglt (snd lnc_w1) (lnc_bk_den 1).
Proof.
  exact (snd (projT2 (qpg_divmod_gen (lnc_bk_num 1) (lnc_bk_den 1)
                                     lnc_den_ok1))).
Qed.

Lemma lnc_pin_w1 :
  length (fst lnc_w1) = 1%nat /\ length (snd lnc_w1) = 2%nat /\
  Qeq_bool (nth 0%nat (fst lnc_w1) 0) (-4) = true /\
  Qeq_bool (nth 0%nat (snd lnc_w1) 0) 4 = true /\
  Qeq_bool (nth 1%nat (snd lnc_w1) 0) (-3) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* 实例四（路线③形 n=2）：t²(1−t)² ÷ (1−t/2)^3 ⟹ 商 −32−8t 余 32−40t+13t² *)
Definition lnc_w2 : list Q * list Q :=
  projT1 (qpg_divmod_gen (lnc_bk_num 2) (lnc_bk_den 2) lnc_den_ok2).

Theorem lnc_consume_id_n2 : forall x : Q,
  QeqT (pint_eval (lnc_bk_num 2) x)
       (pint_eval (lnc_bk_den 2) x * pint_eval (fst lnc_w2) x
        + pint_eval (snd lnc_w2) x).
Proof.
  intros x.
  exact (fst (projT2 (qpg_divmod_gen (lnc_bk_num 2) (lnc_bk_den 2)
                                     lnc_den_ok2)) x).
Qed.

Theorem lnc_consume_deg_n2 : qpd_deglt (snd lnc_w2) (lnc_bk_den 2).
Proof.
  exact (snd (projT2 (qpg_divmod_gen (lnc_bk_num 2) (lnc_bk_den 2)
                                     lnc_den_ok2))).
Qed.

Lemma lnc_pin_w2 :
  length (fst lnc_w2) = 2%nat /\ length (snd lnc_w2) = 3%nat /\
  Qeq_bool (nth 0%nat (fst lnc_w2) 0) (-32) = true /\
  Qeq_bool (nth 1%nat (fst lnc_w2) 0) (-8) = true /\
  Qeq_bool (nth 0%nat (snd lnc_w2) 0) 32 = true /\
  Qeq_bool (nth 1%nat (snd lnc_w2) 0) (-40) = true /\
  Qeq_bool (nth 2%nat (snd lnc_w2) 0) 13 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* 实例五（路线③形 n=3）：t³(1−t)³ ÷ (1−t/2)^4 ⟹ 商 −304−80t−16t²
   余 304−528t+312t²−63t³；A_3 = 2·d_1(3) = 1008 与 AE 报告残数锚衔接 *)
Definition lnc_w3 : list Q * list Q :=
  projT1 (qpg_divmod_gen (lnc_bk_num 3) (lnc_bk_den 3) lnc_den_ok3).

Theorem lnc_consume_id_n3 : forall x : Q,
  QeqT (pint_eval (lnc_bk_num 3) x)
       (pint_eval (lnc_bk_den 3) x * pint_eval (fst lnc_w3) x
        + pint_eval (snd lnc_w3) x).
Proof.
  intros x.
  exact (fst (projT2 (qpg_divmod_gen (lnc_bk_num 3) (lnc_bk_den 3)
                                     lnc_den_ok3)) x).
Qed.

Theorem lnc_consume_deg_n3 : qpd_deglt (snd lnc_w3) (lnc_bk_den 3).
Proof.
  exact (snd (projT2 (qpg_divmod_gen (lnc_bk_num 3) (lnc_bk_den 3)
                                     lnc_den_ok3))).
Qed.

Lemma lnc_pin_w3 :
  length (fst lnc_w3) = 3%nat /\ length (snd lnc_w3) = 4%nat /\
  Qeq_bool (nth 0%nat (fst lnc_w3) 0) (-304) = true /\
  Qeq_bool (nth 1%nat (fst lnc_w3) 0) (-80) = true /\
  Qeq_bool (nth 2%nat (fst lnc_w3) 0) (-16) = true /\
  Qeq_bool (nth 0%nat (snd lnc_w3) 0) 304 = true /\
  Qeq_bool (nth 1%nat (snd lnc_w3) 0) (-528) = true /\
  Qeq_bool (nth 2%nat (snd lnc_w3) 0) 312 = true /\
  Qeq_bool (nth 3%nat (snd lnc_w3) 0) (-63) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ============================================================ *)
(* §4 极点残值肢: R(2) = (−2)^n（u 坐标尾系数 d_{n+1}）             *)
(*    使用位: 分解恒等式在 x:=2 处特化（除式求值为 0）。            *)
(* ============================================================ *)

Lemma lnc_ring_pole : forall e r : Q, r == 0 * e + r.
Proof. intros e r. ring. Qed.

Theorem lnc_residue_pole_n1 : QeqT (pint_eval (snd lnc_w1) (2 # 1))
                                   ((-2) # 1).
Proof.
  assert (H := lnc_consume_id_n1 (2 # 1)).
  apply qeqT_imp_qeq in H.
  assert (Hn : pint_eval (lnc_bk_num 1) (2 # 1) == ((-2) # 1)).
  { apply (proj1 (Qeq_bool_iff _ _)). vm_compute. reflexivity. }
  assert (Hd : pint_eval (lnc_bk_den 1) (2 # 1) == 0).
  { apply (proj1 (Qeq_bool_iff _ _)). vm_compute. reflexivity. }
  rewrite Hn, Hd in H.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (0 * pint_eval (fst lnc_w1) (2 # 1)
                        + pint_eval (snd lnc_w1) (2 # 1)) _).
  - apply lnc_ring_pole.
  - exact (Qeq_sym _ _ H).
Qed.

Theorem lnc_residue_pole_n2 : QeqT (pint_eval (snd lnc_w2) (2 # 1))
                                   ((2 ^ 2) # 1).
Proof.
  assert (H := lnc_consume_id_n2 (2 # 1)).
  apply qeqT_imp_qeq in H.
  assert (Hn : pint_eval (lnc_bk_num 2) (2 # 1) == ((2 ^ 2) # 1)).
  { apply (proj1 (Qeq_bool_iff _ _)). vm_compute. reflexivity. }
  assert (Hd : pint_eval (lnc_bk_den 2) (2 # 1) == 0).
  { apply (proj1 (Qeq_bool_iff _ _)). vm_compute. reflexivity. }
  rewrite Hn, Hd in H.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (0 * pint_eval (fst lnc_w2) (2 # 1)
                        + pint_eval (snd lnc_w2) (2 # 1)) _).
  - apply lnc_ring_pole.
  - exact (Qeq_sym _ _ H).
Qed.

Theorem lnc_residue_pole_n3 : QeqT (pint_eval (snd lnc_w3) (2 # 1))
                                   ((-8) # 1).
Proof.
  assert (H := lnc_consume_id_n3 (2 # 1)).
  apply qeqT_imp_qeq in H.
  assert (Hn : pint_eval (lnc_bk_num 3) (2 # 1) == ((-8) # 1)).
  { apply (proj1 (Qeq_bool_iff _ _)). vm_compute. reflexivity. }
  assert (Hd : pint_eval (lnc_bk_den 3) (2 # 1) == 0).
  { apply (proj1 (Qeq_bool_iff _ _)). vm_compute. reflexivity. }
  rewrite Hn, Hd in H.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (0 * pint_eval (fst lnc_w3) (2 # 1)
                        + pint_eval (snd lnc_w3) (2 # 1)) _).
  - apply lnc_ring_pole.
  - exact (Qeq_sym _ _ H).
Qed.

(* ============================================================ *)
(* §5 残数 d_1 整性肢（AE 路线③(ii)）: d_1 == 2^n·q̃_n              *)
(*    d_1 := [u^n]R = nth n (lnc_comp2 R)（lnc_comp2_eval 声音）；   *)
(*    q̃_n := bk_Qn_qtilde（BeukersLists 在树锚）。                  *)
(*    数值锚: d_1 = 6/52/504；u 展开表 [−2;6]/[4;−24;52]/           *)
(*    [−8;72;−264;504]（首项即极点残值 (−2)^n，与 §4 互证）。        *)
(* ============================================================ *)

Lemma lnc_pin_comp2_w1 :
  Qeq_bool (nth 0%nat (lnc_comp2 (snd lnc_w1)) 0) (-2) = true /\
  Qeq_bool (nth 1%nat (lnc_comp2 (snd lnc_w1)) 0) 6 = true.
Proof. vm_compute. split; reflexivity. Qed.

Lemma lnc_pin_comp2_w2 :
  Qeq_bool (nth 0%nat (lnc_comp2 (snd lnc_w2)) 0) 4 = true /\
  Qeq_bool (nth 1%nat (lnc_comp2 (snd lnc_w2)) 0) (-24) = true /\
  Qeq_bool (nth 2%nat (lnc_comp2 (snd lnc_w2)) 0) 52 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma lnc_pin_comp2_w3 :
  Qeq_bool (nth 0%nat (lnc_comp2 (snd lnc_w3)) 0) (-8) = true /\
  Qeq_bool (nth 1%nat (lnc_comp2 (snd lnc_w3)) 0) 72 = true /\
  Qeq_bool (nth 2%nat (lnc_comp2 (snd lnc_w3)) 0) (-264) = true /\
  Qeq_bool (nth 3%nat (lnc_comp2 (snd lnc_w3)) 0) 504 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma lnc_qtilde_pin_1 : bk_Qn_qtilde 1 = 3%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma lnc_qtilde_pin_2 : bk_Qn_qtilde 2 = 13%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma lnc_qtilde_pin_3 : bk_Qn_qtilde 3 = 63%nat.
Proof. vm_compute. reflexivity. Qed.

(* 整性见证（BD lni_bvp_lcm_int 同型：sigT z + QeqT (… == z#1)，Set 面）
   见证取 2^n·q̃_n 的 Z 像——链级形（q̃_n 衔接）直书于见证项。 *)
Theorem lnc_d1_int_n1 : sigT (fun z : Z => QeqT (lnc_d1 1 (snd lnc_w1))
                                                ((z # 1))).
Proof.
  exists (Z.of_nat (Nat.pow 2 1 * bk_Qn_qtilde 1)%nat).
  apply qeq_imp_qeqT.
  apply (proj1 (Qeq_bool_iff _ _)).
  vm_compute. reflexivity.
Qed.

Theorem lnc_d1_int_n2 : sigT (fun z : Z => QeqT (lnc_d1 2 (snd lnc_w2))
                                                ((z # 1))).
Proof.
  exists (Z.of_nat (Nat.pow 2 2 * bk_Qn_qtilde 2)%nat).
  apply qeq_imp_qeqT.
  apply (proj1 (Qeq_bool_iff _ _)).
  vm_compute. reflexivity.
Qed.

Theorem lnc_d1_int_n3 : sigT (fun z : Z => QeqT (lnc_d1 3 (snd lnc_w3))
                                                ((z # 1))).
Proof.
  exists (Z.of_nat (Nat.pow 2 3 * bk_Qn_qtilde 3)%nat).
  apply qeq_imp_qeqT.
  apply (proj1 (Qeq_bool_iff _ _)).
  vm_compute. reflexivity.
Qed.

(* BD 前件衔接位：lni_bvp_lcm_int（BD 真分子族 L_n·bv_p n ∈ Z 主件）
   在 n=2 处的本池直使用——两整性面（本件 d_1 面 × BD L_n·p_n 面）
   于同一 sigT/QeqT 载体形并置，链面焊接留痕。 *)
Definition lnc_bd_face_n2 : sigT (fun z : Z => QeqT (lni_lbvp 2) (z # 1)) :=
  lni_bvp_lcm_int 2.

(* ============================================================ *)
(* §6 一般分解接口（只登记不施工——首件策略 45 分钟切片既定）        *)
(* ============================================================ *)

(* 一般 n 的带余分解容器：sigT (qpd_divmod_gen_pred (num n) (den n)) *)
Definition lnc_div_gen_type (n : nat) : Set :=
  sigT (qpd_divmod_gen_pred (lnc_bk_num n) (lnc_bk_den n)).

(* 一般 n 的除子良态前提（CK 诚实扩题面：deg ≥ 1 ∧ 真首项非零） *)
Definition lnc_den_ok_type (n : nat) : Set := qpg_divisor_ok (lnc_bk_den n).

(* 一般残数肢：分解正确性前提 ⟹ d_1 == 2^n·q̃_n 的整性见证 *)
Definition lnc_d1_gen_type (n : nat) : Set :=
  forall w : list Q * list Q,
    qpd_divmod_gen_pred (lnc_bk_num n) (lnc_bk_den n) w ->
    sigT (fun z : Z =>
            QeqT (lnc_d1 n (snd w))
                 ((Z.of_nat (Nat.pow 2 n * bk_Qn_qtilde n)%nat # 1))).

(* ============================================================ *)
(* §7 闭合：提取面 + Print Assumptions（红线四条逐条 PA）          *)
(* ============================================================ *)

Separate Extraction lnc_scale lnc_mul lnc_pow lnc_comp2 lnc_d1
  lnc_bk_num lnc_bk_den.

Print Assumptions lnc_eval_scale.
Print Assumptions lnc_eval_map_scale.
Print Assumptions lnc_eval_mul.
Print Assumptions lnc_eval_pow.
Print Assumptions lnc_eval_lin_t.
Print Assumptions lnc_eval_lin_1mt.
Print Assumptions lnc_eval_den_lin.
Print Assumptions lnc_bk_num_eval.
Print Assumptions lnc_bk_den_eval.
Print Assumptions lnc_comp2_eval.
Print Assumptions lnc_den_ok0.
Print Assumptions lnc_den_ok1.
Print Assumptions lnc_den_ok2.
Print Assumptions lnc_den_ok3.
Print Assumptions lnc_consume_id_n0.
Print Assumptions lnc_consume_id_n1lin.
Print Assumptions lnc_consume_id_n1.
Print Assumptions lnc_consume_deg_n1.
Print Assumptions lnc_consume_id_n2.
Print Assumptions lnc_consume_deg_n2.
Print Assumptions lnc_consume_id_n3.
Print Assumptions lnc_consume_deg_n3.
Print Assumptions lnc_residue_pole_n1.
Print Assumptions lnc_residue_pole_n2.
Print Assumptions lnc_residue_pole_n3.
Print Assumptions lnc_d1_int_n1.
Print Assumptions lnc_d1_int_n2.
Print Assumptions lnc_d1_int_n3.
Print Assumptions lnc_bd_face_n2.
Print Assumptions lnc_div_gen_type.
Print Assumptions lnc_den_ok_type.
Print Assumptions lnc_d1_gen_type.
