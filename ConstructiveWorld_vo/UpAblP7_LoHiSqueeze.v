(* ============================================================ *)
(* ToyR 玩具证替换件 —— T263 台账席 战役包X（tier2 十四批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   uahl_lo_lt_hi_one（原 L185，1 句玩具证）                             *)
(*   uahl_lo_lt_hi（原 L76，1 句玩具证）                                  *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAblP7_LoHiSqueeze.v —— 源模块 LoHiSqueeze.v 四定理的独立对偶与三件实例形。 *)
(* 使命：源模块（LhsPair/LhsStar 两节）的编译产物与 Paper7Ablation 摘要不一致，   *)
(*   本件不装设源模块，仅依赖其上游 S01_BaseRing＋Paper7Ablation＋               *)
(*   P7BoundedSoftmaxDeep，对源模块四定理独立重证并实例化。                      *)
(* 使用面（上游出口真名）：p7a_lo_lt_one —— lo<1（利差 Delta/Delta_pos 与      *)
(*   指数字段 expf/expf_zero/expf_mono_lt 五参＋invT 正性位）；                *)
(*   p7d_hi_gt_one —— hi>1 全称八参形；p7a_delta_star_pos —— 0<δ*:=lo²；       *)
(*   p7a_omd_pos / p7a_omd_lt_one —— κ:=1−δ*∈(0,1) 两支，出口带可判定序        *)
(*   隐式参，须以 @ 全参显式应用。                                            *)
(*                                                                *)
(* 定理面（七件，全 Qed，前缀 uahl_）：                                       *)
(*   uahl_lo_lt_one_hi —— 合取 lo<1 ∧ 1<hi（Set 层 And）；左支经                *)
(*       p7a_lo_lt_one，右支经 p7d_hi_gt_one；invT 正性由 inv_pos_pos 提供；    *)
(*   uahl_lo_lt_hi —— 夹逼推论 lo<hi（lt_trans 两步，两支取自                  *)
(*       uahl_lo_lt_one_hi 的 fst/snd）；                                     *)
(*   uahl_delta_star_bounded —— δ*∈(0,1)：左支 p7a_delta_star_pos；右支          *)
(*       δ*<1 独立三步（lt_mult_compat＋lt_id_l＋lt_trans）；                   *)
(*   uahl_omd_bounded —— κ∈(0,1) 基形（@p7a_omd_pos 与 @p7a_omd_lt_one          *)
(*       全参显式应用）；                                                     *)
(*   uahl_omd_bounded_one —— 实例形甲：温度:=1、利差:=1、                      *)
(*       invT:=inv_pos one one_pos；指数族保持抽象——全库无具体实数实例；        *)
(*   uahl_lo_lt_hi_one —— 夹逼实例：同上实例处 lo<hi（lt_trans 合成）；         *)
(*   uahl_omd_bounded_half —— 实例形乙：lo:=inv_pos (plus one one) two_pos；    *)
(*       左支独立链（half_twice、plus_positive 与恒等重排）推得 0<1−1/4，        *)
(*       右支 @p7a_omd_lt_one。                                               *)
(* 基础事实（S01_BaseRing）：two_pos、inv_pos_pos、half_twice、half_pos、        *)
(*   inv_pos_correct、lt_mult_compat、lt_id_l、lt_id_r、plus_positive、          *)
(*   mult_positive、one_pos。                                                 *)
(* 另注：柯西实数侧的 cauchy_real_exp_pos 属异接口（real_lt/cauchy_real_exp      *)
(*   世界），为未来具体 expf 实例预备，本件接口节不使用。                       *)
(*                                                                *)
(* 对标：mathlib 夹逼（squeeze）与 1−x<1 型界的构造性 Set 层对应；stdlib 无同形  *)
(*   （序与运算皆本库类字段）。                                               *)
(* 构造性注记：语句面全 Set 层（合取 S01 And=prod）；零承认；可提取。            *)
(* 编译配方：Rocq 9.1 直调 coqc，cpu_guard 包裹，-o 临时目录。                  *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import Paper7Ablation.
Require Import P7BoundedSoftmaxDeep.

(* ############ 段一：合取 lo<1∧1<hi、夹逼 lo<hi、δ*∈(0,1)（无序可判定参） ## *)
(* 节变量面与源模块 LoHiSqueeze.v 的 LhsPair 节一致（温度对＋利差对＋指数族四件）。 *)

Section UahlPair.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).

(* uahl_lo_lt_one_hi（源模块 lhs_lo_lt_one_hi 的独立重证）：左支经              *)
(*   p7a_lo_lt_one，右支经 p7d_hi_gt_one；invT 正性由 inv_pos_pos 提供。      *)
Theorem uahl_lo_lt_one_hi : And (lt lo one) (lt one hi).
Proof.
  split.
  - exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)).
  - exact (p7d_hi_gt_one temp temp_pos Delta Delta_pos expf expf_pos
             expf_zero expf_mono_lt).
Qed.

(* uahl_lo_lt_hi（源模块 lhs_lo_lt_hi 的独立重证）：lt_trans 两步，两支取自 uahl_lo_lt_one_hi 的两肢 *)
Theorem uahl_lo_lt_hi : lt lo hi.
Proof.
  exact (lt_trans lo one hi (fst uahl_lo_lt_one_hi) (snd uahl_lo_lt_one_hi)).
Qed.

(* uahl_delta_star_bounded（源模块 lhs_delta_star_bounded 的独立重证）：        *)
(*   左支 p7a_delta_star_pos；右支 δ*<1 独立三步：lt_mult_compat、             *)
(*   lt_id_l（经 mult_one）与 lt_trans。 *)
Theorem uahl_delta_star_bounded :
  And (lt zero (mult lo lo)) (lt (mult lo lo) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)). }
  split.
  - exact (p7a_delta_star_pos lo (expf_pos (mult invT (opp Delta)))).
  - exact (lt_trans (mult lo lo) (mult one lo) one
             (lt_mult_compat lo one lo
                (expf_pos (mult invT (opp Delta))) Hlo1)
             (lt_id_l (mult one lo) lo one
                (id_trans (mult_comm one lo) (mult_one lo)) Hlo1)).
Qed.

End UahlPair.

(* ############ 段二：uahl_omd_bounded —— κ:=1−δ*∈(0,1)（带可判定序参节） #### *)
(* 节变量面与源模块 LoHiSqueeze.v 的 LhsStar 节一致；p7a_omd_pos/p7a_omd_lt_one  *)
(* 的可判定序隐式参不可由结论反推，故以 @ 全参显式应用。                       *)

Section UahlStar.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).

(* uahl_omd_bounded（源模块 lhs_omd_bounded 的独立重证）：左支以 δ*<1 前提       *)
(*   应用 @p7a_omd_pos；右支以 0<lo 应用 @p7a_omd_lt_one——全参显式。 *)
Theorem uahl_omd_bounded :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)). }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp Delta))). }
  split.
  - exact (@p7a_omd_pos RI DO lo
             (lt_trans (mult lo lo) (mult one lo) one
                (lt_mult_compat lo one lo Hlopos Hlo1)
                (lt_id_l (mult one lo) lo one
                   (id_trans (mult_comm one lo) (mult_one lo)) Hlo1))).
  - exact (@p7a_omd_lt_one RI DO lo Hlopos).
Qed.

End UahlStar.

(* ########## 段三：实例形甲——uahl_omd_bounded/uahl_lo_lt_hi @ 温度:=1、利差:=1 ## *)
(* 温度与利差均取 one（one_pos 提供两处正性位），invT:=inv_pos one one_pos；    *)
(* 指数族保持抽象（全库无具体实数实例）。                                     *)

Section UahlSbInst.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos one one_pos.
Let lo := expf (mult invT (opp one)).

(* uahl_omd_bounded_one（uahl_omd_bounded 于温度:=1、利差:=1 的实例形）：      *)
(*   p7a_lo_lt_one @ one/one 供 lo<1，expf_pos 供 0<lo，δ*<1 三步内联，@ 全参显式。 *)
Theorem uahl_omd_bounded_one :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one one one_pos expf expf_zero expf_mono_lt invT
             (inv_pos_pos one one_pos)). }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp one))). }
  split.
  - exact (@p7a_omd_pos RI DO lo
             (lt_trans (mult lo lo) (mult one lo) one
                (lt_mult_compat lo one lo Hlopos Hlo1)
                (lt_id_l (mult one lo) lo one
                   (id_trans (mult_comm one lo) (mult_one lo)) Hlo1))).
  - exact (@p7a_omd_lt_one RI DO lo Hlopos).
Qed.

(* uahl_lo_lt_hi_one（uahl_lo_lt_hi 于同上实例的实例形）：p7a_lo_lt_one        *)
(*   @ one/one 供 lo<1，p7d_hi_gt_one @ one/one 供 1<hi，lt_trans 合成。 *)
Theorem uahl_lo_lt_hi_one :
  lt (expf (mult invT (opp one))) (expf (mult invT one)).
Proof.
  exact (lt_trans (expf (mult invT (opp one))) one (expf (mult invT one))           (p7a_lo_lt_one one one_pos expf expf_zero expf_mono_lt invT              (inv_pos_pos one one_pos))           (p7d_hi_gt_one one one_pos one one_pos expf expf_pos expf_zero              expf_mono_lt)).
Qed.

End UahlSbInst.

(* ############ 段四：实例形乙——uahl_omd_bounded @ lo:=二分之一抽象形 ######## *)
(* lo:=inv_pos (plus one one) two_pos（二分之一，two_pos/inv_pos_pos 提供正性）；*)
(* 左支不经 δ*<1 中转，走独立链：half_twice（半＋半=1，半方＋半方=半）与       *)
(* plus_positive（半方>0）及恒等重排，推得 0<1−1/4；                          *)
(* 右支 @p7a_omd_lt_one。                                                     *)

Section UahlHalf.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Let half := inv_pos (plus one one) two_pos.
Let half2 := mult half half.

(* uahl_omd_bounded_half（实例形乙） *)
Theorem uahl_omd_bounded_half :
  And (lt zero (minus one half2)) (lt (minus one half2) one).
Proof.
  assert (Hhp : lt zero half).
  { exact (inv_pos_pos (plus one one) two_pos). }
  assert (Hh2p : lt zero half2).
  { exact (mult_positive half half Hhp Hhp). }
  assert (Hh2p2 : lt zero (plus half2 half2)).
  { exact (plus_positive half2 half2 Hh2p Hh2p). }
  assert (Hq : Id (plus half2 half2) half).
  { exact (half_twice half). }
  assert (Hone : Id (plus half half) one).
  { exact (id_trans (id_cong (fun x => plus x x) (id_sym (mult_one half)))
                    (half_twice one)). }
  assert (Hone2 : Id one (plus (plus half2 half2) (plus half2 half2))).
  { exact (id_trans (id_sym Hone) (id_sym (id_cong (fun x => plus x x) Hq))). }
  assert (Gup : Id (plus (plus (plus half2 half2) (plus half2 half2))
                         (opp half2))
                   (plus half2 (plus half2 half2))).
  { exact (id_trans
             (id_sym (plus_assoc (plus half2 half2) (plus half2 half2)
                       (opp half2)))
             (id_trans
                (id_cong (fun x => plus (plus half2 half2) x)
                   (id_trans (id_sym (plus_assoc half2 half2 (opp half2)))
                      (id_trans
                         (id_cong (fun w => plus half2 w)
                            (plus_comm half2 (opp half2)))
                         (plus_assoc half2 (opp half2) half2))))
             (id_trans
                (id_cong (fun x => plus (plus half2 half2) x)
                   (id_cong (fun w => plus w half2) (plus_opp half2)))
                (id_trans
                   (id_cong (fun x => plus (plus half2 half2) x)
                      (id_trans (plus_comm zero half2) (plus_zero half2)))
                   (id_sym (plus_assoc half2 half2 half2)))))). }
  assert (Gtotal : Id (minus one half2) (plus half2 (plus half2 half2))).
  { exact (id_trans
             (id_sym (id_cong (fun w => plus w (opp half2)) (id_sym Hone2)))
             Gup). }
  split.
  - exact (lt_id_r zero (plus half2 (plus half2 half2)) (minus one half2)
             (id_sym Gtotal)
             (plus_positive half2 (plus half2 half2) Hh2p Hh2p2)).
  - exact (@p7a_omd_lt_one RI DO half Hhp).
Qed.

End UahlHalf.

(* ---- 收尾段：逐件 Print Assumptions 核验零承认 ---- *)
Print Assumptions uahl_lo_lt_one_hi.
Print Assumptions uahl_lo_lt_hi.
Print Assumptions uahl_delta_star_bounded.
Print Assumptions uahl_omd_bounded.
Print Assumptions uahl_omd_bounded_one.
Print Assumptions uahl_lo_lt_hi_one.
Print Assumptions uahl_omd_bounded_half.
