(* ============================================================ *)
(* UpAblAbsQFeedB2.v —— S10 清单外 Qabs 同族槽 15 处二批直配件（O5 席·20260920） *)
(*                                                                *)
(* 零承认件：无承认词面、无经典逻辑、全件 Qed 闭合；                        *)
(*   全部交付语句 Set 层值（QleT'＝S02 Id(Qle_bool,true) 形），             *)
(*   语句面无裸命题；证明全构造（仅消费供体件已 Closed 语句）。             *)
(*                                                                *)
(* 槽位来源（O4 席覆盖审计）：S10_KVQuantTrig.v 内 Qabs_triangle 消费共     *)
(*   21 处，M3/N4R 清单收 6 处（:1411/:1426/:2015/:2074/:2265/:2350），     *)
(*   清单外 15 处由本席二批直配收口：                                      *)
(*   :6282 :7633 :8224 :8485 :10642 :10643 :10644 :10852 :11009            *)
(*   :11195 :11220 :11938 :11944 :12138 :12168。                           *)
(* 本席逐处上下文全量实读定谳：15/15 均＋形三角                             *)
(*   Qabs(a+b) ≤ Qabs a + Qabs b ＝供体件 A.1 uaq_abs_triangle_plus        *)
(*   可承接形；其中 :11195/:12138（rs_add_sin/rs_add_cos 之 HsumMT 步）     *)
(*   语句面即 A.1 逐字同形 QleT' (Qabs (u n + v n)) (Qabs (u n)+Qabs (v n))。*)
(* 无变体（减法形/reverse 形）、无注释、无墙域——四选一定谳全落「可承接」。  *)
(*                                                                *)
(* 直配体例（诚实定性·适配消费级）：槽内 S10 局部实参（sum_upto/cos_term/   *)
(*   sin_term/cos_partial/projT1 等复合表达式）抽象为 Q 变量记槽形，        *)
(*   一槽一件 Corollary、槽行编号入名；证明面＝A.1 逐点实例直喂             *)
(*   （exact/apply 单步），证明增量零——本席价值在清单外槽形的 Set 层       *)
(*   常备直配位，非新证明增量，如实定性不虚报。                            *)
(*                                                                *)
(* 禁触声明：S10_KVQuantTrig.v／UpAblAbsQFeed.v 及一切既有文件零改动；      *)
(*   本件不入 order.txt／_CoqProject，新独立件交付。                       *)
(* 依赖：CW_ConstructiveWorld_219（Export S02 转换层）＋UpAblAbsQFeed       *)
(*   （N4R 交付件，四关绿在册，.vo 在盘）。                                *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
Require Import CW_ConstructiveWorld_219.
Require Import UpAblAbsQFeed.

(* ============================================================ *)
(* Part 0 · 冻结现态打表（签名漂移即响亮失败）                              *)
(* ============================================================ *)

Check QleT'. Check Qabs. Check Qplus. Check Qminus. Check Qopp.
Check uaq_abs_triangle_plus.

(* ============================================================ *)
(* Part A · 清单外 15 槽逐件直配（槽形语句面全 QleT' Set 层）               *)
(* ============================================================ *)

(* 槽 :6282（sc_cs_sq_err_le 三角步骤｜实参 xs:=cos 双重和, ys:=sin 双重和） *)
Corollary uaq2_s10_6282_band : forall xs ys : Q,
  QleT' (Qabs (xs + ys)) (Qabs xs + Qabs ys).
Proof. exact uaq_abs_triangle_plus. Qed.

(* 槽 :7633（cos 中点缺陷和分解｜实参 x:=cauchy_real_cos 投影项, q:=cos_partial K1 m） *)
Corollary uaq2_s10_7633_mid_err : forall x q : Q,
  QleT' (Qabs ((x - q) + q)) (Qabs (x - q) + Qabs q).
Proof. intros x q. apply uaq_abs_triangle_plus. Qed.

(* 槽 :8224（cos_inv_pt 差和链｜实参 a:=cos_partial k u, b:=cos_partial k v, c:=projT1 real_zero k） *)
Corollary uaq2_s10_8224_inv_pt : forall a b c : Q,
  QleT' (Qabs ((a - c) + (c - b))) (Qabs (a - c) + Qabs (c - b)).
Proof. intros a b c. apply uaq_abs_triangle_plus. Qed.

(* 槽 :8485（根收敛柯西链｜实参 p:=cos_partial n (cos_zero_seq n),
   m:=cos_partial n (cos_zero_seq N0), z:=projT1 real_zero n） *)
Corollary uaq2_s10_8485_root_cauchy : forall p m z : Q,
  QleT' (Qabs ((p - m) + (m - z))) (Qabs (p - m) + Qabs (m - z)).
Proof. intros p m z. apply uaq_abs_triangle_plus. Qed.

(* 槽 :10642（sc_add_sin_err 四带 Ht1｜实参 b1..b4：四条带和） *)
Corollary uaq2_s10_10642_h4 : forall b1 b2 b3 b4 : Q,
  QleT' (Qabs (((b1 + b2) + b3) + b4)) (Qabs ((b1 + b2) + b3) + Qabs b4).
Proof. intros b1 b2 b3 b4. apply uaq_abs_triangle_plus. Qed.

(* 槽 :10643（同引理 Ht2） *)
Corollary uaq2_s10_10643_h3 : forall b1 b2 b3 : Q,
  QleT' (Qabs ((b1 + b2) + b3)) (Qabs (b1 + b2) + Qabs b3).
Proof. intros b1 b2 b3. apply uaq_abs_triangle_plus. Qed.

(* 槽 :10644（同引理 Ht3） *)
Corollary uaq2_s10_10644_h2 : forall b1 b2 : Q,
  QleT' (Qabs (b1 + b2)) (Qabs b1 + Qabs b2).
Proof. exact uaq_abs_triangle_plus. Qed.

(* 槽 :10852（sc_add_band_abs 带和三角｜实参 up:=上带和, r:=右带和） *)
Corollary uaq2_s10_10852_bands : forall up r : Q,
  QleT' (Qabs (up + r)) (Qabs up + Qabs r).
Proof. exact uaq_abs_triangle_plus. Qed.

(* 槽 :11009（sc_add_sin_err_bound 三角｜实参 d1:=cs 族带, d2:=余带） *)
Corollary uaq2_s10_11009_d1d2 : forall d1 d2 : Q,
  QleT' (Qabs (d1 + d2)) (Qabs d1 + Qabs d2).
Proof. exact uaq_abs_triangle_plus. Qed.

(* 槽 :11195（rs_add_sin HsumMT 步｜A.1 逐字同形，实参 un:=u n, vn:=v n 序列项） *)
Corollary uaq2_s10_11195_seq_plus : forall un vn : Q,
  QleT' (Qabs (un + vn)) (Qabs un + Qabs vn).
Proof. exact uaq_abs_triangle_plus. Qed.

(* 槽 :11220（rs_add_sin 代数拆分和三角｜实参 e1:=逐项残差, e2:=2n 项残差） *)
Corollary uaq2_s10_11220_split : forall e1 e2 : Q,
  QleT' (Qabs (e1 + e2)) (Qabs e1 + Qabs e2).
Proof. exact uaq_abs_triangle_plus. Qed.

(* 槽 :11938（sc_add_cos_err_abs 双三角外层｜实参 dc:=Dc 带, ds:=Ds 带, an:=An 反对称带） *)
Corollary uaq2_s10_11938_outer : forall dc ds an : Q,
  QleT' (Qabs ((dc - ds) + an)) (Qabs (dc - ds) + Qabs an).
Proof. intros dc ds an. apply uaq_abs_triangle_plus. Qed.

(* 槽 :11944（同引理内嵌负带三角｜实参 dc:=Dc, ds:=Ds；b 实例化为 Qopp ds） *)
Corollary uaq2_s10_11944_inner : forall dc ds : Q,
  QleT' (Qabs (dc + Qopp ds)) (Qabs dc + Qabs (Qopp ds)).
Proof. intros dc ds. apply uaq_abs_triangle_plus. Qed.

(* 槽 :12138（rs_add_cos HsumMT 步｜A.1 逐字同形，实参 un:=u n, vn:=v n 序列项） *)
Corollary uaq2_s10_12138_seq_plus : forall un vn : Q,
  QleT' (Qabs (un + vn)) (Qabs un + Qabs vn).
Proof. exact uaq_abs_triangle_plus. Qed.

(* 槽 :12168（rs_add_cos 代数拆分和三角｜实参 e1:=逐项残差, e2:=2n 项残差） *)
Corollary uaq2_s10_12168_split : forall e1 e2 : Q,
  QleT' (Qabs (e1 + e2)) (Qabs e1 + Qabs e2).
Proof. exact uaq_abs_triangle_plus. Qed.

(* ============================================================ *)
(* 公理面自审：全件 Closed（零外部未证假设）                                *)
(* ============================================================ *)

Print Assumptions uaq2_s10_6282_band.
Print Assumptions uaq2_s10_7633_mid_err.
Print Assumptions uaq2_s10_8224_inv_pt.
Print Assumptions uaq2_s10_8485_root_cauchy.
Print Assumptions uaq2_s10_10642_h4.
Print Assumptions uaq2_s10_10643_h3.
Print Assumptions uaq2_s10_10644_h2.
Print Assumptions uaq2_s10_10852_bands.
Print Assumptions uaq2_s10_11009_d1d2.
Print Assumptions uaq2_s10_11195_seq_plus.
Print Assumptions uaq2_s10_11220_split.
Print Assumptions uaq2_s10_11938_outer.
Print Assumptions uaq2_s10_11944_inner.
Print Assumptions uaq2_s10_12138_seq_plus.
Print Assumptions uaq2_s10_12168_split.
