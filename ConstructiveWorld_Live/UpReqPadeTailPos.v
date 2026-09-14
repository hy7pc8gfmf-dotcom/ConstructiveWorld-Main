(* ============================================================ *)
(* UpReqPadeTailPos.v —— 席C-T1a：Padé 正尾恒等式主件（C 路闭合     *)
(*                        主轨第一切片，Set 层承重墙）               *)
(* 日期：2026-09-14                                                *)
(*                                                                 *)
(* 使命（修正令对表后）：把 S3/S1 数值实锤的「有限 Q 前缀 × 符号因子  *)
(*   (−1)^n × 正系数级数」余项恒等式落成 Set 层 Coq 件。             *)
(*   符号面勘误（C-T1a 修正令 20260914）：尾系数符号 = (−1)^n，      *)
(*   非恒正——本件语句全部显式携带符号因子（n=1 切片为 −(1#2)，      *)
(*   n=2 实例为正号），β_m 本身的全正闭式单独成件（ptp_beta_pos）。  *)
(*                                                                 *)
(* 主件降档（诚实标注，60 分钟预算 + 平台损伤双重止损）：
   ptp_tail_series 全称形（n=1、∀N≥3、∀y）归纳骨架已完备设计——
   归纳步合并恒等式 β_m/m! == 1/(m+2)! − 2/(m+3)!（q_fact 链展开后
   为 q_fact m 的多项式恒等式，ring 可收）；但主步收口需 field 于
   「原子分母」目标，实测本平台 9.0 的 field 对原子分母一律报
   not a valid field equation（最小复现见 E-STAGING-CT1A 卡），
   E268/E293「归一再 field」教义已用尽（目标已纯环项仍炸）。
   交叉相乘 + 乘法消去路线挂账下一席（骨架见交付报告）。            *)
(*                                                                 *)
(* 降档声明（诚实标注）：                                             *)
(*   ① 主件为 n=1 切片的全称 N 形；全称 n 的逐项系数等式（柯西积      *)
(*      重排 + 配对引理）未及落盘，挂账下一席（S1 报告已给配对比值    *)
(*      (n−2j)/((2n−2j)(2j+1)) ≤ 1/2 的正性路线）。                  *)
(*   ② n=2 仅交付截断多项式实例恒等式（S1 定值变体同构），非全称 N。  *)
(*   ③ 平台损伤实锤：field 原子分母全拒（E268/E293 归一教义不适用，  *)
(*      新坑沉淀 E-STAGING-CT1A 卡）；④ 语句面等式用 Qeq（库内        *)
(*      UpReqPadeExp 同款先例）；正性语句面     *)
(*      一律 QltT（Set 层），证内 Prop 仅作桥（Qlt_to_QltT）。        *)
(*                                                                 *)
(* 消费面：S03_QExp（exp_partial/q_pow/q_fact/sum_upto/q_fact_pos/    *)
(*   q_neq_of_lt）、UpReqPadeExp（pade_coeff/pade_num/pade_den）、    *)
(*   S02_CauchyComplete（QltT/Qlt_to_QltT）。                        *)
(*                                                                 *)
(* 公理面自审：本件不新增任何公理依赖，全部结论构造性直证；四关审计    *)
(*   以 Print Assumptions = Closed 与提取产物 Obj.magic 零命中为准。   *)
(*                                                                 *)
(* 编译配方（温控协议，cpu_guard CoreN 1）：                          *)
(*   秒审: coqc -vos -Q . "" UpReqPadeTailPos.v                      *)
(*   全量: coqc -Q . "" UpReqPadeTailPos.v                           *)
(*   G4  : coqchk -Q . "" -o UpReqPadeTailPos                        *)
(* ============================================================ *)

Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqPadeExp.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

(* ===== 定义面 ===== *)

(* β_m = n!·(n+m)!/(2n+m+1)!——S3 探针 beta_term 同式，全正闭式 *)
Definition ptp_beta (n m : nat) : Q :=
  q_fact n * q_fact (n + m) / q_fact (2 * n + m + 1).

(* 带符号正尾前缀：Σ_{m=0}^{M} β_m·y^{2n+1+m}/m!（幂次在项内） *)
Definition ptp_beta_prefix (n M : nat) (y : Q) : Q :=
  sum_upto (Datatypes.S M)
    (fun m => ptp_beta n m / q_fact m * q_pow y (2 * n + 1 + m)).

(* ===== 小引擎 ===== *)

(* sum_upto 尾部展开：定义性（sum_upto (S K) f = sum_upto K f + f K） *)
Lemma ptp_sum_S : forall (K : nat) (f : nat -> Q),
  sum_upto (Datatypes.S K) f == sum_upto K f + f K.
Proof. intro K. intro f. reflexivity. Qed.

(* 前缀步进：prefix (S M) = prefix M + f (S M) *)
Lemma ptp_prefix_S : forall (n M : nat) (y : Q),
  ptp_beta_prefix n (Datatypes.S M) y ==
  ptp_beta_prefix n M y +
  (ptp_beta n (Datatypes.S M) / q_fact (Datatypes.S M)
     * q_pow y (2 * n + 1 + Datatypes.S M)).
Proof.
  intros n M y. unfold ptp_beta_prefix.
  rewrite (ptp_sum_S (Datatypes.S M)
             (fun m => ptp_beta n m / q_fact m * q_pow y (2 * n + 1 + m))).
  reflexivity.
Qed.

(* Q₁(y) = 1 − y/2、P₁(y) = 1 + y/2（系数闭式展开） *)
Lemma ptp_den1 : forall y : Q, pade_den 1 y == 1 + - (1#2) * y.
Proof.
  intro y. unfold pade_den, pade_coeff. cbn. field.
Qed.

Lemma ptp_num1 : forall y : Q, pade_num 1 y == 1 + (1#2) * y.
Proof.
  intro y. unfold pade_num, pade_coeff. cbn. field.
Qed.

(* ===== 正性件（全称 n,m，Set 层 QltT 出口） ===== *)

Theorem ptp_beta_pos : forall (n m : nat), QltT 0 (ptp_beta n m).
Proof.
  intros n m. apply Qlt_to_QltT.
  unfold ptp_beta. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; apply q_fact_pos.
  - apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* ===== β 哨兵族（S3 探针 fractions 精确对表） ===== *)

Lemma ptp_beta_n1_0 : ptp_beta 1 0%nat == (1#6).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_1 : ptp_beta 1 1%nat == (1#12).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_2 : ptp_beta 1 2%nat == (1#20).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_3 : ptp_beta 1 3%nat == (1#30).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_4 : ptp_beta 1 4%nat == (1#42).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_0 : ptp_beta 2 0%nat == (1#30).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_1 : ptp_beta 2 1%nat == (1#60).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_2 : ptp_beta 2 2%nat == (1#105).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

(* 首项闭式实例：(n!)^2/((2n)!(2n+1)!)——n=1 得 1/12（y^3 位首系数
   带 (−1)^1 符号），n=2 得 1/720（y^5 位首系数偶号正），与修正令②对表 *)
Lemma ptp_beta_n1_first : ptp_beta 1 0%nat / q_fact 2 == (1#12).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_first : ptp_beta 2 0%nat / q_fact 4 == (1#720).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

(* ===== 保底件一：n=1 截断多项式恒等式（全称 y） =====
   系数 −1/12, −1/24 与全级数 −β_m/(2!·m!) 精确对表（m=0,1），
   y^5 项 −1/48 为 exp_partial 4 的截断窄条。 *)
Lemma ptp_n1_poly : forall y : Q,
  exp_partial 4 y * pade_den 1 y - pade_num 1 y
  == - ((1#12)*q_pow y 3 + (1#24)*q_pow y 4 + (1#48)*q_pow y 5).
Proof.
  intro y.
  unfold exp_partial, pade_den, pade_num, pade_coeff.
  cbn. field.
Qed.

(* ===== 保底件二：n=2 偶号正尾实例（S1 g2_poly 同款，全称 y） =====
   十个 Padé 匹配条件（y^0..y^4 系数全零）由右端无低次项读出；
   y^7 系数恰零（右端无 y^7 项）；首项 y^5/720 = (2!)^2/(4!·5!)。 *)
Lemma ptp_n2_poly : forall y : Q,
  exp_partial 6 y * pade_den 2 y - pade_num 2 y
  == (1#720)*q_pow y 5 + (1#1440)*q_pow y 6 + (1#8640)*q_pow y 8.
Proof.
  intro y.
  unfold exp_partial, pade_den, pade_num, pade_coeff.
  cbn. field.
Qed.

(* ===== 数值哨兵（y = 1/2 对账；vm_compute + Qeq 交叉乘 lia） ===== *)

Lemma ptp_sentinel_n1_half :
  exp_partial 4 (1#2) * pade_den 1 (1#2) - pade_num 1 (1#2) == - (7#512).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_sentinel_n2_half :
  exp_partial 6 (1#2) * pade_den 2 (1#2) - pade_num 2 (1#2)
  == (1#720)*(1#32) + (1#1440)*(1#64) + (1#8640)*(1#256).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

(* ===== 审计与提取 ===== *)

Print Assumptions ptp_beta_pos.
Print Assumptions ptp_n1_poly.
Print Assumptions ptp_n2_poly.

From Stdlib Require Import Extraction.
Separate Extraction ptp_beta_pos ptp_beta ptp_beta_prefix
  ptp_n1_poly ptp_n2_poly.

(* ============================================================ *)
(* 席C-T1c 增量（append-only，2026-09-14）：全称 N 形收口           *)
(*   ptp_tail_series——按 T1a 报告④配方：归纳不变式                  *)
(*     Φ_k : exp_partial (3+k) y·Q₁(y) − P₁(y)                    *)
(*       == −((1#2)·prefix_1 k y) − ((1#2)·y^{S(3+k)}/(3+k)!)     *)
(*   两处 (−1#2) 即 (−1)^1 符号面显式（奇 n 负尾）；偶 n 对偶形由    *)
(*   ptp_n2_poly 正号实例承贴。N=3/N=4 闭式与 ptp_n1_poly 逐系数    *)
(*   对表（ptp_series_n1_N3/N4 + recheck + y=1/2 数值对账）。       *)
(*   绕损伤路线（E-STAGING-CT1A 教义）：全程不触原子分母 field——     *)
(*   merge 乘法形（纯变元 field）→ ptp_div_clear_r 交叉乘消去       *)
(*   （Qmult_inj_r + q_fact_pos 正性）→ 清分母后 field 收口。       *)
(* ============================================================ *)

(* —— 0. 纯变元小引擎（ring/field 只见自由变元与字面常量）—— *)

Lemma ptp_AC_swap_m : forall a b c : Q, a + b - c == a - c + b.
Proof. intros a b c. unfold Qminus. ring. Qed.

Lemma ptp_opp_plus : forall a b : Q, - (a + b) == - a + - b.
Proof. intros a b. unfold Qminus. ring. Qed.

Lemma ptp_opp_mul_move : forall a b : Q, (- a) * b == - (a * b).
Proof. intros a b. ring. Qed.

Lemma ptp_G_alg : forall a b c p : Q, (a + b) + c == (a + (- p)) + ((b + p) + c).
Proof. intros a b c p. ring. Qed.

Lemma ptp_Qmake_plus : forall a b : Z, (a + b) # 1 == (a # 1) + (b # 1).
Proof. intros a b. unfold Qeq. simpl. lia. Qed.

(* —— 1. 分母消去（Qmult_inj_r 型交叉乘，正性在场）—— *)

Lemma ptp_div_clear_r : forall x d D E : Q,
  ~ (d == 0) -> D == E * d -> x / d * D == x * E.
Proof.
  intros x d D E Hd HDE. unfold Qdiv. rewrite HDE.
  rewrite (Qmult_comm E d).
  rewrite <- (Qmult_assoc x (Qinv d) (d * E)).
  rewrite (Qmult_assoc (Qinv d) d E).
  rewrite (Qmult_comm (Qinv d) d). rewrite (Qmult_inv_r d Hd).
  rewrite Qmult_1_l. reflexivity.
Qed.

(* —— 2. merge 乘法形（T1a 报告④骨架照抄；q_fact 链 lia 归一）—— *)

Lemma ptp_n1_merge : forall m : nat,
  q_fact 1 * q_fact (Datatypes.S m) * q_fact (Datatypes.S (Datatypes.S m))
  == (q_fact (Datatypes.S (Datatypes.S (Datatypes.S m)))
      - (1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S m))) * q_fact m.
Proof.
  intro m.
  rewrite (q_fact_succ (Datatypes.S (Datatypes.S m))).
  rewrite (q_fact_succ (Datatypes.S m)).
  rewrite (q_fact_succ m).
  rewrite (q_fact_succ 0%nat).
  cbn [q_fact].
  replace (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S m))))
    with (Z.of_nat m + 3)%Z by lia.
  replace (Z.of_nat (Datatypes.S (Datatypes.S m)))
    with (Z.of_nat m + 2)%Z by lia.
  replace (Z.of_nat (Datatypes.S m)) with (Z.of_nat m + 1)%Z by lia.
  replace (Z.of_nat 1) with 1%Z by lia.
  rewrite (ptp_Qmake_plus (Z.of_nat m) 3%Z).
  rewrite (ptp_Qmake_plus (Z.of_nat m) 2%Z).
  rewrite (ptp_Qmake_plus (Z.of_nat m) 1%Z).
  field.
Qed.

(* —— 3. 双侧步进展开（rewrite-only，不触原子分母收口）—— *)

Definition ptp_F (k : nat) (y : Q) : Q :=
  exp_partial (3 + k) y * pade_den 1 y - pade_num 1 y.

Definition ptp_G (k : nat) (y : Q) : Q :=
  - ((1#2) * ptp_beta_prefix 1 k y)
    - (1#2) * (q_pow y (4 + k) / q_fact (3 + k)).

Lemma ptp_exp_S : forall (n : nat) (y : Q),
  exp_partial (Datatypes.S n) y
  == exp_partial n y + q_pow y (Datatypes.S n) / q_fact (Datatypes.S n).
Proof. intros n y. reflexivity. Qed.

Lemma ptp_G_eq : forall k y,
  ptp_G k y
  == - ((1#2) * ptp_beta_prefix 1 k y)
     + - ((1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k))).
Proof.
  intros k y. unfold ptp_G, Qminus.
  replace (4%nat + k)%nat with (Datatypes.S (3 + k)%nat) by lia.
  reflexivity.
Qed.

Lemma ptp_F_step : forall k y,
  ptp_F (Datatypes.S k) y
  == ptp_F k y
     + ((q_pow y (Datatypes.S (3 + k)) / q_fact (Datatypes.S (3 + k)))
        * (1 + - (1#2) * y)).
Proof.
  intros k y. unfold ptp_F.
  replace (3%nat + Datatypes.S k)%nat with (Datatypes.S (3 + k)%nat) by lia.
  rewrite ptp_exp_S. rewrite ptp_den1. rewrite ptp_num1.
  rewrite (Qmult_plus_distr_l (exp_partial (3 + k) y)
             (q_pow y (Datatypes.S (3 + k)) / q_fact (Datatypes.S (3 + k)))
             (1 + - (1#2) * y)).
  rewrite (ptp_AC_swap_m
             (exp_partial (3 + k) y * (1 + - (1#2) * y))
             ((q_pow y (Datatypes.S (3 + k)) / q_fact (Datatypes.S (3 + k)))
              * (1 + - (1#2) * y))
             (1 + (1#2) * y)).
  reflexivity.
Qed.

Lemma ptp_G_step : forall k y,
  ptp_G (Datatypes.S k) y
  == - ((1#2) * ptp_beta_prefix 1 k y)
     + - ((1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k)))
     + (- ((1#2) * (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
                    * q_pow y (Datatypes.S (3 + k))))
        + (1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k))
        + - ((1#2) * (y * q_pow y (Datatypes.S (3 + k))
                      / q_fact (Datatypes.S (3 + k))))).
Proof.
  intros k y. unfold ptp_G.
  replace (4%nat + Datatypes.S k)%nat
    with (Datatypes.S (Datatypes.S (3%nat + k)%nat)) by lia.
  replace (3%nat + Datatypes.S k)%nat with (Datatypes.S (3 + k)%nat) by lia.
  rewrite ptp_prefix_S.
  replace (2%nat * 1%nat + 1%nat + Datatypes.S k)%nat with (Datatypes.S (3%nat + k)%nat) by lia.
  rewrite (q_pow_succ y (Datatypes.S (3 + k))).
  rewrite (Qmult_plus_distr_r (1#2) (ptp_beta_prefix 1 k y)
             (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
              * q_pow y (Datatypes.S (3 + k)))).
  rewrite (ptp_opp_plus ((1#2) * ptp_beta_prefix 1 k y)
             ((1#2) * (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
                       * q_pow y (Datatypes.S (3 + k))))).
  rewrite (ptp_G_alg (- ((1#2) * ptp_beta_prefix 1 k y))
             (- ((1#2) * (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
                          * q_pow y (Datatypes.S (3 + k)))))
             (- ((1#2) * (y * q_pow y (Datatypes.S (3 + k))
                          / q_fact (Datatypes.S (3 + k)))))
             ((1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k)))).
  reflexivity.
Qed.

(* —— 4. 清分母核心：归纳步差恒等式（ΔL == ΔR）——
   路线：Qmult_inj_r 两侧同乘 D = 2·u3·v4·w（正性 q_fact_pos 在场）
   → ptp_div_clear_r 逐商消去 → merge 乘法形回代 → field 收口。 *)

Lemma ptp_step_core : forall k y,
  (q_pow y (Datatypes.S (3 + k)) / q_fact (Datatypes.S (3 + k)))
    * (1 + - (1#2) * y)
  == - ((1#2) * (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
                 * q_pow y (Datatypes.S (3 + k))))
     + (1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k))
     + - ((1#2) * (y * q_pow y (Datatypes.S (3 + k))
                   / q_fact (Datatypes.S (3 + k)))).
Proof.
  intros k y.
  unfold ptp_beta. cbn [Nat.add Nat.mul].
  replace (k%nat + 1%nat)%nat with (Datatypes.S k) by lia.
  remember (q_pow y (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))))
    as Aeq eqn:HA.
  assert (Hw0 : ~ (q_fact (Datatypes.S k) == 0))
    by (apply q_neq_of_lt; apply q_fact_pos).
  assert (Hu0 : ~ (q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))) == 0))
    by (apply q_neq_of_lt; apply q_fact_pos).
  assert (Hv0 : ~ (q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))) == 0))
    by (apply q_neq_of_lt; apply q_fact_pos).
  assert (HD : ~ (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))
                   * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                       (Datatypes.S k)))))
                  * q_fact (Datatypes.S k) == 0)).
  { apply q_neq_of_lt. apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat.
      + apply Qmult_lt_0_compat; [exact Q2_pos | apply q_fact_pos].
      + apply q_fact_pos.
    - apply q_fact_pos. }
  apply (proj1 (Qmult_inj_r _ _ _ HD)).
  (* LHS 消去 *)
  rewrite <- (Qmult_assoc (Aeq / q_fact (Datatypes.S (Datatypes.S
              (Datatypes.S (Datatypes.S k)))))
              (1 + - (1#2) * y)
              (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
                * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))))
               * q_fact (Datatypes.S k))).
  assert (HcL : (Aeq / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k)))))
                * ((1 + - (1#2) * y)
                   * (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                        (Datatypes.S k)))
                       * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                           (Datatypes.S k)))))
                      * q_fact (Datatypes.S k)))
                == Aeq * ((1 + - (1#2) * y)
                          * ((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                              (Datatypes.S k)))
                             * q_fact (Datatypes.S k)))).
  { apply (ptp_div_clear_r Aeq
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))))
             ((1 + - (1#2) * y)
              * (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))
                  * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                      (Datatypes.S k)))))
                 * q_fact (Datatypes.S k)))
             ((1 + - (1#2) * y)
              * ((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))
                 * q_fact (Datatypes.S k))));
    [ exact Hv0 | ring ]. }
  rewrite HcL.
  (* RHS：D 逐块分摊 + 消去（显式实例，防 LHS 误分摊） *)
  rewrite (Qmult_plus_distr_l
             (- ((1#2) * (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                              (Datatypes.S k))))
                          / q_fact (Datatypes.S k) * Aeq))
              + (1#2) * (Aeq / q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))))
             (- ((1#2) * (y * Aeq
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                              (Datatypes.S k))))))
              )
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  rewrite (Qmult_plus_distr_l
             (- ((1#2) * (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                              (Datatypes.S k))))
                          / q_fact (Datatypes.S k) * Aeq)))
             ((1#2) * (Aeq / q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  (* 块 B：β/w·A·D *)
  rewrite (ptp_opp_mul_move ((1#2) * (q_fact 1 * q_fact (Datatypes.S
             (Datatypes.S k))
             / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                 (Datatypes.S k))))
             / q_fact (Datatypes.S k) * Aeq))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  rewrite <- (Qmult_assoc (1#2)
             (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
              / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k))))
              / q_fact (Datatypes.S k) * Aeq)
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  rewrite <- (Qmult_assoc (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
              / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k))))
              / q_fact (Datatypes.S k))
             Aeq
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  assert (HcB1 : (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                  / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                      (Datatypes.S k))))
                  / q_fact (Datatypes.S k))
                 * (Aeq * (((1 + 1)%Q
                            * q_fact (Datatypes.S (Datatypes.S
                                (Datatypes.S k)))
                            * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                                (Datatypes.S k)))))
                           * q_fact (Datatypes.S k)))
                 == (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                     / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                         (Datatypes.S k)))))
                    * (Aeq * ((1 + 1)%Q
                              * q_fact (Datatypes.S (Datatypes.S
                                  (Datatypes.S k)))
                              * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                                  (Datatypes.S k))))))).
  { apply (ptp_div_clear_r
             (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
              / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k)))))
             (q_fact (Datatypes.S k))
             (Aeq * (((1 + 1)%Q
                      * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
                      * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                          (Datatypes.S k)))))
                     * q_fact (Datatypes.S k)))
             (Aeq * ((1 + 1)%Q
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                         (Datatypes.S k)))))));
    [ exact Hw0 | ring ]. }
  rewrite HcB1.
  assert (HcB2 : (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                  / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                      (Datatypes.S k)))))
                 * (Aeq * ((1 + 1)%Q
                           * q_fact (Datatypes.S (Datatypes.S
                               (Datatypes.S k)))
                           * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                               (Datatypes.S k))))))
                 == (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k)))
                    * (Aeq * ((1 + 1)%Q
                              * q_fact (Datatypes.S (Datatypes.S
                                  (Datatypes.S k)))))).
  { apply (ptp_div_clear_r
             (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k)))
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                 (Datatypes.S k)))))
             (Aeq * ((1 + 1)%Q
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                         (Datatypes.S k))))))
             (Aeq * ((1 + 1)%Q
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))));
    [ exact Hv0 | ring ]. }
  rewrite HcB2.
  (* 块 C：A/u3·D *)
  rewrite <- (Qmult_assoc (1#2)
             (Aeq / q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  assert (HcC : (Aeq / q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
                * (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                      (Datatypes.S k)))
                    * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                        (Datatypes.S k)))))
                   * q_fact (Datatypes.S k))
                == Aeq * ((1 + 1)%Q
                          * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                              (Datatypes.S k))))
                          * q_fact (Datatypes.S k))).
  { apply (ptp_div_clear_r Aeq
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))
             (((1 + 1)%Q
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k))))
               * q_fact (Datatypes.S k))));
    [ exact Hu0 | ring ]. }
  rewrite HcC.
  (* 块 D：y·A/v4·D *)
  rewrite (ptp_opp_mul_move ((1#2) * (y * Aeq
             / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                 (Datatypes.S k))))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  rewrite <- (Qmult_assoc (1#2)
             (y * Aeq / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                 (Datatypes.S k)))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  assert (HcD : ((y * Aeq) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k)))))
                * (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                      (Datatypes.S k)))
                    * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                        (Datatypes.S k)))))
                   * q_fact (Datatypes.S k))
                == (y * Aeq) * ((1 + 1)%Q
                                * q_fact (Datatypes.S (Datatypes.S
                                    (Datatypes.S k)))
                                * q_fact (Datatypes.S k))).
  { apply (ptp_div_clear_r (y * Aeq)
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))
             ((1 + 1)%Q
              * q_fact (Datatypes.S (Datatypes.S
                  (Datatypes.S k)))
               * q_fact (Datatypes.S k)));
    [ exact Hv0 | ring ]. }
  rewrite HcD.
  (* merge 回代（乘法形，括号对齐） *)
  rewrite (Qmult_comm Aeq
             ((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))).
  rewrite (Qmult_assoc (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k)))
             ((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
             Aeq).
  rewrite (Qmult_comm (1 + 1)%Q
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))).
  rewrite (Qmult_assoc (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k)))
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
             (1 + 1)%Q).
  rewrite (ptp_n1_merge (Datatypes.S k)).
  field.
Qed.

(* —— 5. 主件：全称 N 形恒等式（归纳收口）—— *)

Lemma ptp_main_fg : forall k : nat, forall y : Q, ptp_F k y == ptp_G k y.
Proof.
  induction k as [| k IH].
  - intro y. unfold ptp_F, ptp_G.
    unfold ptp_beta_prefix, ptp_beta, pade_den, pade_num, pade_coeff.
    cbn. field.
  - intro y. rewrite ptp_F_step. rewrite ptp_G_step.
    rewrite <- ptp_G_eq. rewrite IH. rewrite (ptp_step_core k y).
    reflexivity.
Qed.

Theorem ptp_tail_series_k : forall (k : nat) (y : Q),
  exp_partial (3 + k) y * pade_den 1 y - pade_num 1 y
  == - ((1#2) * ptp_beta_prefix 1 k y)
     - (1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k)).
Proof.
  intros k y. change (ptp_F k y == ptp_G k y). apply ptp_main_fg.
Qed.

Theorem ptp_tail_series : forall (N : nat) (y : Q), (3 <= N)%nat ->
  exp_partial N y * pade_den 1 y - pade_num 1 y
  == - ((1#2) * ptp_beta_prefix 1 (N - 3) y)
     - (1#2) * (q_pow y (Datatypes.S N) / q_fact N).
Proof.
  intros N y HN.
  replace N with (3%nat + (N - 3)%nat)%nat by lia.
  replace (3%nat + (N - 3)%nat - 3%nat)%nat with (N - 3)%nat by lia.
  apply (ptp_tail_series_k (N - 3) y).
Qed.

(* —— 6. 对账哨兵：N=3/N=4 闭式与 ptp_n1_poly 逐系数对表；
   y=1/2 数值两侧同值（reflexively 一致）。 —— *)

Lemma ptp_series_n1_N3 : forall y : Q,
  - ((1#2) * ptp_beta_prefix 1 0 y)
    + - ((1#2) * (q_pow y (4 + 0) / q_fact (3 + 0)))
  == - ((1#12) * q_pow y 3 + (1#12) * q_pow y 4).
Proof. intro y. unfold ptp_beta_prefix, ptp_beta. cbn. field. Qed.

Lemma ptp_series_n1_N4 : forall y : Q,
  - ((1#2) * ptp_beta_prefix 1 1 y)
    + - ((1#2) * (q_pow y (4 + 1) / q_fact (3 + 1)))
  == - ((1#12) * q_pow y 3 + (1#24) * q_pow y 4 + (1#48) * q_pow y 5).
Proof. intro y. unfold ptp_beta_prefix, ptp_beta. cbn. field. Qed.

(* N=4 特例与 T1a 定值件 ptp_n1_poly 的语句面逐字一致 *)
Lemma ptp_n1_poly_recheck : forall y : Q,
  exp_partial 4 y * pade_den 1 y - pade_num 1 y
  == - ((1#12) * q_pow y 3 + (1#24) * q_pow y 4 + (1#48) * q_pow y 5).
Proof.
  intro y.
  change (ptp_F 1 y
          == - ((1#12) * q_pow y 3 + (1#24) * q_pow y 4
                + (1#48) * q_pow y 5)).
  transitivity (ptp_G 1 y).
  - apply ptp_main_fg.
  - unfold ptp_G. apply ptp_series_n1_N4.
Qed.

(* 全称件实例与定值件数值对账：同一 y=1/2 两侧同值 −(7#512) *)
Lemma ptp_tail_sentinel_F_half : ptp_F 1 (1#2) == -(7#512).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_tail_sentinel_G_half : ptp_G 1 (1#2) == -(7#512).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_tail_FG_agree_half : ptp_F 1 (1#2) == ptp_G 1 (1#2).
Proof. apply ptp_main_fg. Qed.

(* —— 审计与提取（T1c 增量）—— *)

Print Assumptions ptp_tail_series.
Print Assumptions ptp_tail_series_k.
Print Assumptions ptp_main_fg.
Print Assumptions ptp_step_core.
Print Assumptions ptp_n1_merge.
Print Assumptions ptp_n1_poly_recheck.

Separate Extraction ptp_tail_series ptp_step_core ptp_n1_merge.
