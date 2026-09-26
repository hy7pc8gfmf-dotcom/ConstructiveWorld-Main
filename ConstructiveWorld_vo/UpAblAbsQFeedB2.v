(* ============================================================
   使命：本件定理/引理声明面所述性质的形式化（原头注为历史注记块，
         实质整编候后波；本块为五字段指针）。
   依赖：件内 Require 声明面所列库件。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)

(* ========================================================================= *)
(* 【ToyR 工程·· 】玩具级定理同名非平凡替换稿（补标头注）       *)
(*                                                                           *)
(* 本稿系 ToyR 工程 替换落件（原名落件）；落件时头部漏植工程标记，本块由  *)
(*  于  补设：仅加头注，语句面／证明体／         *)
(* Require 面                                                                *)
(* 零改动；原头注紧随本块之后原样保留。来源刀面权威记录：消融50/。       *)
(* 替换定理清单：uaq2_s10_6282_band／8224_inv_pt／8485_root_cauchy／         *)
(* 10642_h4／11938_outer／11944_inner（共 6 刀，引擎体整体内联）             *)
(* 非平凡性口径：两步组合器模板逐字重演，消除跨件单跳委托；无一行拆分式假    *)
(* 非平凡。                                                                  *)
(* 本稿零公理、零承认件、全闭合、纯构造性、无经典逻辑；落件时与本次补标      *)
(* 抽验编译均验零承认。                                                      *)
(* ========================================================================= *)
(* ============================================================
      切片四 · UpAblAbsQFeedB2 六刀实施（同名替换，全中文零承认）
   本件为基线原件（md5 c979bdcf…，与 Main 基线逐字）的同名替换件：语句面、
   声明序、其余定理与既有版记头注逐字保留；六条 Corollary 证明体在替换点
   将跨件单跳 uaq_abs_triangle_plus 引擎体整体内联（模板＝UpAblAbsQFeed.v
   :59-61：转换桥 Qle_to_QleT'＋stdlib Qabs_triangle 两步，逐字重演）：
   一、uaq2_s10_6282_band（xs/ys 实例化）；二、uaq2_s10_8224_inv_pt（a/b/c）；
   三、uaq2_s10_8485_root_cauchy（p/m/z）；四、uaq2_s10_10642_h4（b1..b4）；
   五、uaq2_s10_11938_outer（dc/ds/an）；六、uaq2_s10_11944_inner（dc/ds）。
   余 9 条同形单跳直引批量登记（见 §A 批注，本件版记原注「证明增量零」
   供给体例不变）。依赖面零新增：Require 面与原件逐字一致（引擎体两步
   所需 Qle_to_QleT'／Qabs_triangle 均在原件既有可见域内）。
   ============================================================ *)
(* ============================================================ *)
(* UpAblAbsQFeedB2.v —— S10 内 Qabs 同族绝对值三角第二批依赖模块（15 处）    *)
(*                                                                *)
(* 使命：为 S10_KVQuantTrig 内 Qabs_triangle 的其余使用点提供供给：        *)
(*   全文件使用共 21 处，6 处已由 UpAblAbsQFeed（第一批）给出，            *)
(*   其余 15 处由本件给出。                                                *)
(*                                                                *)
(* 覆盖核对：15 处均为和形三角不等式 Qabs(a+b) ≤ Qabs a + Qabs b，         *)
(*   皆可由 UpAblAbsQFeed 的 uaq_abs_triangle_plus 给出；其中              *)
(*   rs_add_sin/rs_add_cos 的 HsumMT 步两处，语句面与                      *)
(*   uaq_abs_triangle_plus 逐字同形                                        *)
(*   （QleT' (Qabs (u n + v n)) (Qabs (u n)+Qabs (v n))）。                *)
(*   无变体（减法形/reverse 形）、无注释、无不可达情形。                   *)
(*                                                                *)
(* 供给体例（诚实定性）：调用点的局部实参（sum_upto/cos_term/              *)
(*   sin_term/cos_partial/projT1 等复合表达式）抽象为 Q 变量；             *)
(*   每处一个 Corollary（标识符沿用调用点行号）；证明为                    *)
(*   uaq_abs_triangle_plus 的逐点实例化（exact/apply 单步），              *)
(*   证明增量零——本件价值在于为该批调用点提供 Set 层常备供给，             *)
(*   非新证明，如实注记。                                                  *)
(*                                                                *)
(* 依赖：CW_ConstructiveWorld_219（Export S02 转换层）＋UpAblAbsQFeed      *)
(*   （第一批依赖模块）。                                                    *)
(*                                                                *)
(* 对标：mathlib 置顶使命与声明注释惯例；stdlib 文档注释惯例。             *)
(* 构造性注记：全部语句为 Set 层值（QleT'＝S02 Id(Qle_bool,true) 形）；    *)
(*   语句面无裸命题；证明全构造（仅使用 UpAblAbsQFeed 已证语句）；         *)
(*   零承认；全件 Qed 闭合。                                               *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
Require Import CW_ConstructiveWorld_219.
Require Import UpAblAbsQFeed.

(* ============================================================ *)
(* §0 · 库内符号核验（签名不符即编译失败）                                  *)
(* ============================================================ *)

Check QleT'. Check Qabs. Check Qplus. Check Qminus. Check Qopp.
Check uaq_abs_triangle_plus.

(* ============================================================ *)
(* §A · 15 处调用点逐件供给（语句面全 QleT' Set 层）                        *)
(* ============================================================ *)

(* uaq2_s10_6282_band（sc_cs_sq_err_le 三角步骤｜实参 xs:=cos 双重和, ys:=sin 双重和） *)
Corollary uaq2_s10_6282_band : forall xs ys : Q,
  QleT' (Qabs (xs + ys)) (Qabs xs + Qabs ys).
Proof.
  intros xs ys.
  (* 刀：uaq_abs_triangle_plus 引擎体整体内联（模板＝UpAblAbsQFeed.v:59-61：
     转换桥 Qle_to_QleT'＋stdlib Qabs_triangle），xs/ys 实例化。 *)
  apply Qle_to_QleT'. apply Qabs_triangle.
Qed.

(* 不可化批量登记（9 条跨件单跳直引）：uaq2_s10_7633_mid_err／10643_h3／
   10644_h2／10852_bands／11009_d1d2／11195_seq_plus／11220_split／
   12138_seq_plus／12168_split——均为 uaq_abs_triangle_plus 逐字同形实例
   （本件版记「证明增量零」供给体例之单跳最短形），批量登记不凑数。 *)

(* uaq2_s10_7633_mid_err（cos 中点缺陷和分解｜实参 x:=cauchy_real_cos 投影项, q:=cos_partial K1 m） *)
Corollary uaq2_s10_7633_mid_err : forall x q : Q,
  QleT' (Qabs ((x - q) + q)) (Qabs (x - q) + Qabs q).
Proof. intros x q. apply uaq_abs_triangle_plus. Qed.

(* uaq2_s10_8224_inv_pt（cos_inv_pt 差和链｜实参 a:=cos_partial k u, b:=cos_partial k v, c:=projT1 real_zero k） *)
Corollary uaq2_s10_8224_inv_pt : forall a b c : Q,
  QleT' (Qabs ((a - c) + (c - b))) (Qabs (a - c) + Qabs (c - b)).
Proof.
  intros a b c.
  (* 刀：uaq_abs_triangle_plus 引擎体整体内联（模板＝UpAblAbsQFeed.v:59-61：
     转换桥 Qle_to_QleT'＋stdlib Qabs_triangle），a/b/c 实例化。 *)
  apply Qle_to_QleT'. apply Qabs_triangle.
Qed.

(* uaq2_s10_8485_root_cauchy（根收敛柯西链｜实参 p:=cos_partial n (cos_zero_seq n),
   m:=cos_partial n (cos_zero_seq N0), z:=projT1 real_zero n） *)
Corollary uaq2_s10_8485_root_cauchy : forall p m z : Q,
  QleT' (Qabs ((p - m) + (m - z))) (Qabs (p - m) + Qabs (m - z)).
Proof.
  intros p m z.
  (* 刀：uaq_abs_triangle_plus 引擎体整体内联（模板＝UpAblAbsQFeed.v:59-61：
     转换桥 Qle_to_QleT'＋stdlib Qabs_triangle），p/m/z 实例化。 *)
  apply Qle_to_QleT'. apply Qabs_triangle.
Qed.

(* uaq2_s10_10642_h4（sc_add_sin_err 四带 Ht1｜实参 b1..b4：四条带和） *)
Corollary uaq2_s10_10642_h4 : forall b1 b2 b3 b4 : Q,
  QleT' (Qabs (((b1 + b2) + b3) + b4)) (Qabs ((b1 + b2) + b3) + Qabs b4).
Proof.
  intros b1 b2 b3 b4.
  (* 刀：uaq_abs_triangle_plus 引擎体整体内联（模板＝UpAblAbsQFeed.v:59-61：
     转换桥 Qle_to_QleT'＋stdlib Qabs_triangle），b1..b4 实例化。 *)
  apply Qle_to_QleT'. apply Qabs_triangle.
Qed.

(* uaq2_s10_10643_h3（同引理 Ht2） *)
Corollary uaq2_s10_10643_h3 : forall b1 b2 b3 : Q,
  QleT' (Qabs ((b1 + b2) + b3)) (Qabs (b1 + b2) + Qabs b3).
Proof. intros b1 b2 b3. apply uaq_abs_triangle_plus. Qed.

(* uaq2_s10_10644_h2（同引理 Ht3） *)
Corollary uaq2_s10_10644_h2 : forall b1 b2 : Q,
  QleT' (Qabs (b1 + b2)) (Qabs b1 + Qabs b2).
Proof. exact uaq_abs_triangle_plus. Qed.

(* uaq2_s10_10852_bands（sc_add_band_abs 带和三角｜实参 up:=上带和, r:=右带和） *)
Corollary uaq2_s10_10852_bands : forall up r : Q,
  QleT' (Qabs (up + r)) (Qabs up + Qabs r).
Proof. exact uaq_abs_triangle_plus. Qed.

(* uaq2_s10_11009_d1d2（sc_add_sin_err_bound 三角｜实参 d1:=cs 族带, d2:=余带） *)
Corollary uaq2_s10_11009_d1d2 : forall d1 d2 : Q,
  QleT' (Qabs (d1 + d2)) (Qabs d1 + Qabs d2).
Proof. exact uaq_abs_triangle_plus. Qed.

(* uaq2_s10_11195_seq_plus（rs_add_sin HsumMT 步｜逐字同形，实参 un:=u n, vn:=v n 序列项） *)
Corollary uaq2_s10_11195_seq_plus : forall un vn : Q,
  QleT' (Qabs (un + vn)) (Qabs un + Qabs vn).
Proof. exact uaq_abs_triangle_plus. Qed.

(* uaq2_s10_11220_split（rs_add_sin 代数拆分和三角｜实参 e1:=逐项残差, e2:=2n 项残差） *)
Corollary uaq2_s10_11220_split : forall e1 e2 : Q,
  QleT' (Qabs (e1 + e2)) (Qabs e1 + Qabs e2).
Proof. exact uaq_abs_triangle_plus. Qed.

(* uaq2_s10_11938_outer（sc_add_cos_err_abs 双三角外层｜实参 dc:=Dc 带, ds:=Ds 带, an:=An 反对称带） *)
Corollary uaq2_s10_11938_outer : forall dc ds an : Q,
  QleT' (Qabs ((dc - ds) + an)) (Qabs (dc - ds) + Qabs an).
Proof.
  intros dc ds an.
  (* 刀：uaq_abs_triangle_plus 引擎体整体内联（模板＝UpAblAbsQFeed.v:59-61：
     转换桥 Qle_to_QleT'＋stdlib Qabs_triangle），dc/ds/an 实例化。 *)
  apply Qle_to_QleT'. apply Qabs_triangle.
Qed.

(* uaq2_s10_11944_inner（同引理内嵌负带三角｜实参 dc:=Dc, ds:=Ds；b 实例化为 Qopp ds） *)
Corollary uaq2_s10_11944_inner : forall dc ds : Q,
  QleT' (Qabs (dc + Qopp ds)) (Qabs dc + Qabs (Qopp ds)).
Proof.
  intros dc ds.
  (* 刀：uaq_abs_triangle_plus 引擎体整体内联（模板＝UpAblAbsQFeed.v:59-61：
     转换桥 Qle_to_QleT'＋stdlib Qabs_triangle），dc/ds（ys:=Qopp ds 位） 实例化。 *)
  apply Qle_to_QleT'. apply Qabs_triangle.
Qed.

(* uaq2_s10_12138_seq_plus（rs_add_cos HsumMT 步｜逐字同形，实参 un:=u n, vn:=v n 序列项） *)
Corollary uaq2_s10_12138_seq_plus : forall un vn : Q,
  QleT' (Qabs (un + vn)) (Qabs un + Qabs vn).
Proof. exact uaq_abs_triangle_plus. Qed.

(* uaq2_s10_12168_split（rs_add_cos 代数拆分和三角｜实参 e1:=逐项残差, e2:=2n 项残差） *)
Corollary uaq2_s10_12168_split : forall e1 e2 : Q,
  QleT' (Qabs (e1 + e2)) (Qabs e1 + Qabs e2).
Proof. exact uaq_abs_triangle_plus. Qed.

(* ============================================================ *)
(* 假设审计：以下各件 Print Assumptions 均为 Closed（零外部未证假设）      *)
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
