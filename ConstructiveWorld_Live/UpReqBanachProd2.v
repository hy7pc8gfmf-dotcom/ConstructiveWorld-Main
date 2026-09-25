(* ============================================================ *)
(* UpReqBanachProd2.v —— 席B2Tv2：路径 B B 类引理第二批量移植席  *)
(* （20260912，重启位；前席 B2T 零足迹）                          *)
(* ============================================================ *)
(* 任务：使用 B3Sv2 映射表（attn/_tb3s_交付报告-20260912.md S1）  *)
(*   剩余 B 类引理——排除域（二项式/双和/卷积/尾界）之外：        *)
(*   #23 sum_upto_div（除系数拉出）、#27 q_choose_div_fact       *)
(*   （阶乘比分裂）、#29 exp_term_split（逐项系数分裂）。         *)
(* 每条 B 类双层交付：                                           *)
(*   Q 引擎层 = 001/ConstructiveWorld.v ExpPlusStage2 原文照抄    *)
(*     （bpr2_ 前缀防与 S07_RealSetoidExpLog 同名件撞名）；       *)
(*   Banach 面 = bae/bmult 语境改写（标量中心 bcoef_comm 换位 +   *)
(*     bcoef_mult 闭口；类无 Q 等值到 bae 的标量函子字段，        *)
(*     故 B 面语句不走 bcoef 内部 Q 重写，只取可构方向）。        *)
(* 附赠 wd 族两件：bmult_wd 四槽形的 l/r 便捷面（语句面新增      *)
(*   结构引理；二项式配对清项链与对角折叠将反复使用）。           *)
(* 依赖复用：S01/S02/S03（q_fact/q_pow/sum_upto/q_fact_pos/      *)
(*   q_neq_of_lt）+ UpReqBanachExp（Class BanachAlg/bpow 出口）   *)
(*   + UpReqBanachProd（bsum/bsum_scal，冻结只读 Require 复用，   *)
(*   禁重定义其任何名）。                                        *)
(* 红线自审：语句面全 Set 层（bae 面）或纯 Q 引擎面（Prop 仅      *)
(*   ~c==0 前提位，Q 层引擎在案先例）；证内无经典逻辑；           *)
(*   无遗留承认件（G1 grep 自审见交付报告）。                    *)
(* 工程注（沿 UpReqBanachProd 同款）：类字段投影一律 @显式喂实例； *)
(*   bae 面 Set 承载等词无 rewrite 实例——一律 change(定义形)/    *)
(*   定义形闭合 + bae_trans 显式中件（中件在 y 槽第 3 参）；      *)
(*   Q 层 Qeq 重写走 setoid_rewrite（S03/S07 在案先例）；         *)
(*   Q 除法为 Infix Qdiv 定义（非展开记号）——ring 视其为原子，    *)
(*   重排前须 unfold Qdiv（001 源与 S07 同款）。                 *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachProd.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Setoid.
From Stdlib Require Import Lia.

Open Scope Q_scope.

(* ============================================================ *)
(* 一、Q 引擎层（ExpPlusStage2 原文照抄，bpr2_ 前缀）             *)
(* ============================================================ *)

(* 组合数：n!/(k!·(n−k)!)（k ≤ n 标准意义；源段 q_choose 同款） *)
Definition bpr2_q_choose (n k : nat) : Q :=
  q_fact n / (q_fact k * q_fact (Nat.sub n k)).

(* ---- #23 sum_upto_div：Σ(f/c) = (Σf)/c（除系数拉出） ---- *)
(* 原文照抄（001 L33910 同款语句与证法；Q 层，~c==0 前提位）。   *)
Lemma bpr2_sum_upto_div : forall (n : nat) (c : Q) (f : nat -> Q),
  ~ c == 0 -> sum_upto n (fun j : nat => f j / c) == (sum_upto n f) / c.
Proof.
  intros n c f Hc.
  induction n as [| n' IH]; simpl.
  - unfold Qdiv. ring.
  - setoid_rewrite IH. unfold Qdiv. ring.
Qed.

(* ---- #27 q_choose_div_fact：C(n,k)/n! == 1/k! · 1/(n−k)! ---- *)
(* 原文照抄（001 L33921 同款语句）；证法同源分两步：先重排原子    *)
(* 消 n!（Qmult_inv_r + q_fact_pos），再 Qinv_mult_distr 分拆。   *)
Lemma bpr2_q_choose_div_fact : forall (n k : nat),
  bpr2_q_choose n k / q_fact n == Qinv (q_fact k) * Qinv (q_fact (Nat.sub n k)).
Proof.
  intros n k.
  unfold bpr2_q_choose. unfold Qdiv.
  transitivity (Qinv (q_fact k * q_fact (Nat.sub n k))).
  - transitivity
      ((q_fact n * Qinv (q_fact n)) * Qinv (q_fact k * q_fact (Nat.sub n k))).
    + (* 原子重排：Qinv 视为原子，交换/结合由 ring 闭合 *)
      ring.
    + assert (Hn : ~ q_fact n == 0).
      { apply q_neq_of_lt. apply q_fact_pos. }
      rewrite (Qmult_inv_r (q_fact n) Hn).
      apply Qmult_1_l.
  - apply Qinv_mult_distr.
Qed.

(* ---- #29 exp_term_split：逐项系数分裂 ---- *)
(* C(k,j)·x^j·y^(k−j)/k! == (x^j/j!)·(y^(k−j)/(k−j)!)            *)
(* 原文照抄（001 L33955 同款语句）；证法同源：先拉出 C/k!，       *)
(* 再代入 #27 分裂式，ring 分配闭合。                            *)
Lemma bpr2_exp_term_split : forall (x y : Q) (k j : nat),
  bpr2_q_choose k j * q_pow x j * q_pow y (Nat.sub k j) / q_fact k ==
  (q_pow x j / q_fact j) * (q_pow y (Nat.sub k j) / q_fact (Nat.sub k j)).
Proof.
  intros x y k j.
  transitivity
    ((bpr2_q_choose k j / q_fact k) * q_pow x j * q_pow y (Nat.sub k j)).
  - unfold Qdiv. ring.
  - rewrite bpr2_q_choose_div_fact. unfold Qdiv. ring.
Qed.

(* ============================================================ *)
(* 二、wd 族：bmult_wd 四槽形的 l/r 便捷面（语句面结构引理）      *)
(* （UpReqBanachExp 类字段只有 bmult_wd 四槽形；加法侧已有        *)
(*   bplus_wd_l/r，乘法侧为空缺——本件补齐。二项式配对清项链      *)
(*   （席 BA 交付①）与对角折叠反复使用。）                       *)
(* ============================================================ *)

Lemma bpr2_bmult_wd_l : forall (B : BanachAlg) (a b c : (@BA B)),
  @bae B a b -> @bae B (@bmult B a c) (@bmult B b c).
Proof.
  intros B a b c H. exact (@bmult_wd B a c b c H (@bae_refl B c)).
Qed.

Lemma bpr2_bmult_wd_r : forall (B : BanachAlg) (a b c : (@BA B)),
  @bae B a b -> @bae B (@bmult B c a) (@bmult B c b).
Proof.
  intros B a b c H. exact (@bmult_wd B c a c b (@bae_refl B c) H).
Qed.

(* ============================================================ *)
(* 三、Banach 面（bae/bmult 语境改写）                            *)
(* ============================================================ *)

(* ---- #23 Banach 面：Σ(f·bcoef(/c)) == (Σf)·bcoef(/c) ---- *)
(* 语境改写：/c 换 bcoef(Qinv c)；右乘标量位与 bsum_scal 同形，   *)
(* 即 bsum_scal 在 c := /c 处的对接实例（冻结件出口使用）。       *)
Lemma bpr2_bsum_div : forall (B : BanachAlg) (n : nat) (c : Q)
                             (f : nat -> (@BA B)),
  @bae B (bsum B n (fun j : nat => @bmult B (f j) (@bcoef B (Qinv c))))
         (@bmult B (bsum B n f) (@bcoef B (Qinv c))).
Proof.
  intros B n c f. exact (bsum_scal B n (Qinv c) f).
Qed.

(* ---- #29 Banach 面主件：对角系数折叠（标量中心重排） ---- *)
(* (a^j·/j!)·(b^i·/(k−j)!) == (a^j·b^i)·bcoef(/j!·/(k−j)!)       *)
(* 七步链：sym assoc → assoc → 标量 c1 与 b^i 经 bcoef_comm 换位  *)
(* → sym assoc → assoc → 闭口 bcoef_mult。全程 a^j 与 b^i 乘序    *)
(* 不动（无乘法交换需求）；Q 恒等式只经 bcoef_mult 可构方向进      *)
(* bae 面（类无 Q 等值标量函子字段，禁走 bcoef 内部重写）。       *)
(* 使用位：交付①（席 BA q_binom_S 蓝图）逐项二项式 + 方块→对角   *)
(* 合并步（esp_prod_square 的第 j+i=k 对角线）。                  *)
Lemma bpr2_bterm_split : forall (B : BanachAlg) (a b : (@BA B)) (k j : nat),
  @bae B
    (@bmult B (@bmult B (bpow B a j) (@bcoef B (Qinv (q_fact j))))
              (@bmult B (bpow B b (Nat.sub k j))
                        (@bcoef B (Qinv (q_fact (Nat.sub k j))))))
    (@bmult B (@bmult B (bpow B a j) (bpow B b (Nat.sub k j)))
              (@bcoef B
                 (Qinv (q_fact j) * Qinv (q_fact (Nat.sub k j)))%Q)).
Proof.
  intros B a b k j.
  (* G0 = (A·c1)·(Bb·c2) → M1 = A·(c1·(Bb·c2)) *)
  apply (@bae_trans B _
    (@bmult B (bpow B a j)
       (@bmult B (@bcoef B (Qinv (q_fact j)))
          (@bmult B (bpow B b (Nat.sub k j))
                   (@bcoef B (Qinv (q_fact (Nat.sub k j))))))) _).
  { apply (@bae_sym B).
    exact (@bmult_assoc B (bpow B a j) (@bcoef B (Qinv (q_fact j)))
             (@bmult B (bpow B b (Nat.sub k j))
                      (@bcoef B (Qinv (q_fact (Nat.sub k j)))))). }
  (* M1 → M2 = A·((c1·Bb)·c2)：内层 assoc，外层公共左元 A *)
  apply (@bae_trans B _
    (@bmult B (bpow B a j)
       (@bmult B (@bmult B (@bcoef B (Qinv (q_fact j)))
                           (bpow B b (Nat.sub k j)))
                 (@bcoef B (Qinv (q_fact (Nat.sub k j)))))) _).
  { apply (@bpr2_bmult_wd_r B _ _ (@bpow B a j)).
    exact (@bmult_assoc B (@bcoef B (Qinv (q_fact j)))
             (bpow B b (Nat.sub k j))
             (@bcoef B (Qinv (q_fact (Nat.sub k j))))). }
  (* M2 → M3 = A·((Bb·c1)·c2)：标量 c1 中心换位过 b^i *)
  apply (@bae_trans B _
    (@bmult B (bpow B a j)
       (@bmult B (@bmult B (bpow B b (Nat.sub k j))
                           (@bcoef B (Qinv (q_fact j))))
                 (@bcoef B (Qinv (q_fact (Nat.sub k j)))))) _).
  { apply (@bpr2_bmult_wd_r B _ _ (@bpow B a j)).
    apply (@bpr2_bmult_wd_l B (@bmult B (@bcoef B (Qinv (q_fact j)))
                                       (bpow B b (Nat.sub k j)))
                             (@bmult B (bpow B b (Nat.sub k j))
                                       (@bcoef B (Qinv (q_fact j))))
                             (@bcoef B (Qinv (q_fact (Nat.sub k j))))).
    apply (@bae_sym B).
    exact (@bcoef_comm B (Qinv (q_fact j)) (bpow B b (Nat.sub k j))). }
  (* M3 → M4 = A·(Bb·(c1·c2))：内层 sym assoc *)
  apply (@bae_trans B _
    (@bmult B (bpow B a j)
       (@bmult B (bpow B b (Nat.sub k j))
          (@bmult B (@bcoef B (Qinv (q_fact j)))
                   (@bcoef B (Qinv (q_fact (Nat.sub k j))))))) _).
  { apply (@bpr2_bmult_wd_r B _ _ (@bpow B a j)).
    apply (@bae_sym B).
    exact (@bmult_assoc B (bpow B b (Nat.sub k j))
             (@bcoef B (Qinv (q_fact j)))
             (@bcoef B (Qinv (q_fact (Nat.sub k j))))). }
  (* M4 → M5 = (A·Bb)·(c1·c2)：assoc 正向 *)
  apply (@bae_trans B _
    (@bmult B (@bmult B (bpow B a j) (bpow B b (Nat.sub k j)))
             (@bmult B (@bcoef B (Qinv (q_fact j)))
                       (@bcoef B (Qinv (q_fact (Nat.sub k j)))))) _).
  { exact (@bmult_assoc B (bpow B a j) (bpow B b (Nat.sub k j))
             (@bmult B (@bcoef B (Qinv (q_fact j)))
                       (@bcoef B (Qinv (q_fact (Nat.sub k j)))))). }
  (* M5 → RHS = (A·Bb)·bcoef(/j!·/(k−j)!)：bcoef_mult 闭口 *)
  apply (@bpr2_bmult_wd_r B _ _ (@bmult B (bpow B a j)
                                        (bpow B b (Nat.sub k j)))).
  apply (@bae_sym B).
  exact (@bcoef_mult B (Qinv (q_fact j)) (Qinv (q_fact (Nat.sub k j)))).
Qed.

(* ============================================================ *)
(* 对接注记（S3 加分层，详交付报告）：                            *)
(*   bpr2_bsum_div ← UpReqBanachProd.bsum_scal（/c 位实例）；     *)
(*   bpr2_q_choose_div_fact/bpr2_exp_term_split = exp_cauchy_    *)
(*     double（席 BA）对角收集步 C(k,j)/k! = 1/j!·1/(k−j)! 的     *)
(*     Q 引擎（注意 S07_RealSetoidExpLog 已有 Q 层同名件，        *)
(*     Require 复用与 bpr2_ 自持二选一，混载时用 bpr2_ 名）；     *)
(*   bpr2_bterm_split = 方块→对角折叠 Banach 面引理，交付①        *)
(*     逐项使用；bpr2_bmult_wd_l/r = 乘法 wd 便捷面。            *)
(* 遗留登记（对称遗留，不落承认件）：                             *)
(*   #14–19/#28/#32 二项式与 e^(a+b) 主链 → 席 BA；               *)
(*   #24/#25/#31 双和拆分/三角转置 → 席 BT 已闭合（bd2_ 族）；     *)
(*   #34–36 带尾截断 → S3 装配批（esp_diff_le_tail 对接）。       *)
(* ============================================================ *)
