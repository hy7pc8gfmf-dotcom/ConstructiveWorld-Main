(* ================================================================== *)
(* LeibsepNselHCoupling —— n_sel/h 耦合引理件（W1-α'' 带域形前置件一）    *)
(*                                                                    *)
(* 使命：将 leibsep_q_kernel 链内 Niven 选取级 n_sel 对有理高度 h 显式    *)
(*   闭式化：n_sel(q) = lw0_n_select(10·lw0_pi_d0_of b0, 0)+1 = 20·h+23， *)
(*   h = lw1m_height q = S(Pos.to_nat(Qden(Qred q)))，并交付 2·n_sel+2    *)
(*   = 40·h+48 逐字化＋Qden 单调肢＋h=2..12 精确对照表。                  *)
(*   本件全 nat/Q 闭式计算与辅助引理，零新公理。                          *)
(*                                                                    *)
(* 依赖清单：Stdlib QArith/Qabs/Qminmax/Qround/ZArith/Lia；               *)
(*   S01_BaseRing；LW0PiIrrational（lw0_n_select :5521/lw0_pi_d0_of :9528）； *)
(*   LW1PiMeasure（lw1m_height :48）。                                   *)
(*                                                                    *)
(* 对标行：LW0LeibSeparation :5465-5466（b0/n_sel set 形·本件语句面基准）；  *)
(*   LW0PiIrrational :5521（lw0_n_select）/ :9528（lw0_pi_d0_of）；         *)
(*   LW1PiMeasure :48（lw1m_height）/ :729（lw1m_fface 阀形引用面）。       *)
(*   施工图源：PIU1862 §5（n_sel = 20h+23 画像）为本件使命书。             *)
(*                                                                    *)
(* 构造性注记：全 Set/Type 层承载（nat 等式＋Q 闭式）；零 Axiom/Admitted；   *)
(*   Qceiling 正整数闭式走 Qfloor 逐字定义展开（change 定点＋cbv beta iota）； *)
(*   对照表为 vm_compute 级 reflexivity 闭式计算。                        *)
(*                                                                    *)
(* 编译配方：coqc -native-compiler no -q -Q <vo树> "" -Q . ""              *)
(*   leibsep_nsel_h_coupling.v                                          *)
(* ================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qminmax QArith.Qround.
From Stdlib Require Import Lia ZArith Arith.Arith.
Require Import S01_BaseRing.
Require Import LW0PiIrrational.
Require Import LW1PiMeasure.

(* ---------- §1 链内 n_sel 表达式（与 kernel set 形逐字对齐） ---------- *)

Definition piu1864_nsel (q : Q) : nat :=
  (lw0_n_select (10 * lw0_pi_d0_of ((Z.pos (Qden q) # 1)%Q)) 0 + 1)%nat.

(* kernel set 形逐字系（b0 展开 delta 像·reflexivity 级） *)
Lemma piu1864_nsel_kernel_face : forall q : Q,
  (lw0_n_select (10 * lw0_pi_d0_of ((Z.pos (Qden q) # 1)%Q)) 0 + 1)%nat
  = piu1864_nsel q.
Proof. intros q. reflexivity. Qed.

(* ---------- §2 Qceiling/Qabs 正整数闭式（d0 吸收核） ---------- *)

Lemma piu1864_qabs_pos_int : forall d : positive,
  Qabs ((Z.pos d # 1)%Q) = (Z.pos d # 1)%Q.
Proof. intros d. reflexivity. Qed.

Lemma piu1864_qceiling_pos_int : forall d : positive,
  Qceiling ((Z.pos d # 1)%Q) = Z.pos d.
Proof.
  intros d. unfold Qceiling, Qfloor.
  change (Qopp ((Z.pos d # 1)%Q)) with ((Z.neg d # 1)%Q).
  cbv beta iota.
  rewrite Z.div_1_r.
  reflexivity.
Qed.

(* d0 吸收核：正整数 b0 = d#1 的 d0 = d+1 *)
Lemma piu1864_d0_of_pos_int : forall d : positive,
  lw0_pi_d0_of ((Z.pos d # 1)%Q) = Datatypes.S (Pos.to_nat d).
Proof.
  intros d. unfold lw0_pi_d0_of.
  rewrite piu1864_qabs_pos_int.
  rewrite piu1864_qceiling_pos_int.
  assert (Hz : (0 <= Z.pos d)%Z)
    by (apply Z.lt_le_incl; apply Pos2Z.is_pos).
  rewrite (Z2Nat.inj_succ (Z.pos d) Hz).
  rewrite Z2Nat.inj_pos.
  reflexivity.
Qed.

(* ---------- §3 n_sel 闭式（raw Qden 面＋lw1m_height 桥） ---------- *)

Lemma piu1864_nsel_of_d0 : forall d0 : nat,
  (1 <= d0)%nat ->
  (lw0_n_select (10 * d0) 0 + 1)%nat = (20 * d0 + 23)%nat.
Proof. intros d0 Hd. unfold lw0_n_select. lia. Qed.

Lemma piu1864_nsel_qden : forall q : Q,
  piu1864_nsel q = (20 * Datatypes.S (Pos.to_nat (Qden q)) + 23)%nat.
Proof.
  intros q. unfold piu1864_nsel.
  rewrite piu1864_d0_of_pos_int.
  rewrite piu1864_nsel_of_d0 by (pose proof (Pos2Nat.is_pos (Qden q)); lia).
  reflexivity.
Qed.

(* 高度桥：Qred q 的 raw 分母＝q 的既约分母，无需 Qred 幂等 *)
Lemma piu1864_nsel_height : forall q : Q,
  piu1864_nsel (Qred q) = (20 * lw1m_height q + 23)%nat.
Proof.
  intros q. unfold lw1m_height. apply piu1864_nsel_qden.
Qed.

(* ---------- §4 单调肢与 2·n_sel+2 逐字化 ---------- *)

Lemma piu1864_nsel_mono_qden : forall p q : Q,
  (Qden p <= Qden q)%positive ->
  (piu1864_nsel p <= piu1864_nsel q)%nat.
Proof.
  intros p q Hpq. rewrite !piu1864_nsel_qden.
  pose proof (proj1 (Pos2Nat.inj_le _ _) Hpq) as Hle.
  lia.
Qed.

Lemma piu1864_two_nsel_qden : forall q : Q,
  (2 * piu1864_nsel q + 2 = 40 * Datatypes.S (Pos.to_nat (Qden q)) + 48)%nat.
Proof. intros q. rewrite piu1864_nsel_qden. lia. Qed.

Lemma piu1864_two_nsel_height : forall q : Q,
  (2 * piu1864_nsel (Qred q) + 2 = 40 * lw1m_height q + 48)%nat.
Proof. intros q. rewrite piu1864_nsel_height. lia. Qed.

(* ---------- §5 born 对照表（h=2..12 ＋ Qred 敏感点取样） ---------- *)

Lemma piu1864_nsel_table :
  piu1864_nsel ((1 # 1)%Q) = 63%nat /\
  piu1864_nsel ((1 # 2)%Q) = 83%nat /\
  piu1864_nsel ((1 # 3)%Q) = 103%nat /\
  piu1864_nsel ((1 # 4)%Q) = 123%nat /\
  piu1864_nsel ((1 # 5)%Q) = 143%nat /\
  piu1864_nsel ((1 # 6)%Q) = 163%nat /\
  piu1864_nsel ((1 # 7)%Q) = 183%nat /\
  piu1864_nsel ((1 # 8)%Q) = 203%nat /\
  piu1864_nsel ((1 # 9)%Q) = 223%nat /\
  piu1864_nsel ((1 # 10)%Q) = 243%nat /\
  piu1864_nsel ((1 # 11)%Q) = 263%nat.
Proof. repeat split; reflexivity. Qed.

(* Qred 敏感点：raw 面与 height 桥在非既约点分流（6/4：raw=123·height=83） *)
Lemma piu1864_nsel_qred_spot :
  piu1864_nsel ((6 # 4)%Q) = 123%nat /\
  piu1864_nsel (Qred ((6 # 4)%Q)) = 83%nat /\
  (piu1864_nsel (Qred ((6 # 4)%Q)) = 20 * lw1m_height ((6 # 4)%Q) + 23)%nat.
Proof. repeat split; reflexivity. Qed.

(* ---------- §6 PA 锚 ---------- *)
Print Assumptions piu1864_d0_of_pos_int.
Print Assumptions piu1864_nsel_qden.
Print Assumptions piu1864_nsel_height.
Print Assumptions piu1864_nsel_mono_qden.
Print Assumptions piu1864_two_nsel_height.
Print Assumptions piu1864_nsel_table.
