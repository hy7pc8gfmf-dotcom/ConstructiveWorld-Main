(* ============================================================ *)
(* UpReqHlogZD.v — 槽放电战役#4：HlogZ 槽构造性放电（KL 投影旗舰）    *)
(*                                                              *)
(* 目标旗舰：UpReqAlign.req_projected_distribution_minimizes_kl     *)
(*   （KL 投影 req 版，ReqKLProjection 节已闭；节后导出签名经        *)
(*     _hzlogd_probe.v Check 打表核实）。                           *)
(*                                                              *)
(* HlogZ 槽实测形（勘误要点）：                                     *)
(*   le (log (@Z_aud_req R RIS S sumf post_aud p) HZ) zero          *)
(*   ——是 log Z 的「上界形」（log Z ≤ 0），不是 lt zero (log Z)      *)
(*   下界形，也不是逐 eps 形。故放电路线勘定为：                     *)
(*   Z_aud ≤ sumf p（req_Z_aud_le_one，通过集质量 ≤ 总质量）          *)
(*     == one（Hp_norm 归一化）⟹ log Z_aud ≤ log one == 0            *)
(*     （log 单调 le 版直推；Id 侧总放电先例 = UpHlogZ.hlogz_*，      *)
(*       Real 层种子 = CW219 real_log_le_mono/real_log_le_zero_of_le_one）。 *)
(*   任务书草图「Z ≥ max p_i ⟹ log Z 下界」为下界槽路线，实测槽无     *)
(*   此形态：max 提取不入职；「逐点正性见证」在二态实例里由           *)
(*   hzlogd_HZ_bool 承接（HZ 槽一并放电），勘误详见交付报告。         *)
(*                                                              *)
(* 交付清单（前缀 hzlogd_ 独占，编前 grep 复验 0 撞名）：             *)
(*   [保底] hzlogd_log_le_zero_of_le_one —— Z 正性+Z ≤ 1 ⟹ log Z ≤ 0  *)
(*           抽象放电（log 单调 le 槽显式位，Set 层零 Prop）；         *)
(*   [T2②]  hzlogd_discharge_real —— 抽象单调槽由 CW219 种子          *)
(*           real_log_le_mono 直喂的 Real 具体放电（无条件闭合）；      *)
(*           hzlogd_discharge_real_direct —— real_log_le_zero_of_le_one *)
(*           直用双形（双形并存，殊途同归）；                          *)
(*   [主件1] hzlogd_proj_min_kl_hlogzfree —— 旗舰抽象 HlogZ-free      *)
(*           实例化：HlogZ 槽由保底件填充；诚实前提位移 = 新增          *)
(*           sum_le/Hp_norm（Z ≤ 1 路线的数学来源，旗舰原签名不含）；   *)
(*   [主件2] hzlogd_proj_min_kl_bool —— 旗舰 bool/Real 具体实例        *)
(*           （S := bool 二态审计，post_aud := id；HZ 槽由             *)
(*           hzlogd_HZ_bool 一并放电；仅余 p/q 分布前提，全 Set 层）。  *)
(*                                                              *)
(* 红线：零公理类禁词；全 Qed；Set 层语句（req/lt/le 全 Set 值；      *)
(* Hqz 的 post_aud s = false 槽与旗舰同位继承）；既有文件零改；        *)
(* 双形并存；零 git。                                                *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 保底件：抽象放电（log 单调 le 槽显式位；四关主链第 1 环）           *)
(*   论证：Z ≤ 1 ⟹ log Z ≤ log one（单调槽）⟹ log Z ≤ 0               *)
(*   （log_one 是接口字段：req (log one H) zero，经 le_id_r 换右端）。 *)
(* ============================================================ *)
Lemma hzlogd_log_le_zero_of_le_one :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R),
    (forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
       le x y -> le (log x Hx) (log y Hy)) ->
    forall (Z : R) (HZ : lt zero Z), le Z one -> le (log Z HZ) zero.
Proof.
  intros R RIS Hmono Z HZ HZ1.
  apply (@le_id_r R RIS (log Z HZ) (log one one_pos) zero).
  - exact (log_one one_pos).
  - exact (Hmono Z one HZ one_pos HZ1).
Qed.

(* ============================================================ *)
(* T2 模板 ②：Real 具体放电（抽象单调槽由 CW219 种子直喂）             *)
(*   real_log_le_mono（CW219 L112104 区，UpLogMono 镜像）喂单参槽；    *)
(*   语句层 lt/le/log 经 RealEnhancedReal 实例 delta 等同 real_*。     *)
(* ============================================================ *)
Lemma hzlogd_discharge_real :
  forall (Z : Real) (HZ : lt zero Z), le Z one -> le (log Z HZ) zero.
Proof.
  intros Z HZ HZ1.
  exact (hzlogd_log_le_zero_of_le_one Real RealEnhancedReal
           real_log_le_mono Z HZ HZ1).
Qed.

(* 双形并存：real_log_le_zero_of_le_one（UpLogMono 直用形态）直取，      *)
(* 与上行殊途同归（同型语句双路互证，UpHlogZ 双交付先例）。             *)
Lemma hzlogd_discharge_real_direct :
  forall (Z : Real) (HZ : lt zero Z), le Z one -> le (log Z HZ) zero.
Proof.
  intros Z HZ HZ1.
  exact (real_log_le_zero_of_le_one Z HZ HZ1).
Qed.

(* ============================================================ *)
(* 主件 1：旗舰抽象 HlogZ-free 实例化                                  *)
(*   旗舰节后签名（探针打表）= R RIS S sumf + sum_ext/add/linear +      *)
(*   log_req_compat + post_aud p Hp_pos HZ + q Hq Hqn Hqz + HlogZ。    *)
(*   本件：HlogZ 槽由保底件填充；新增 sum_le/Hp_norm 入口（Z ≤ 1        *)
(*   路线来源：req_Z_aud_le_one 要 sum_le，换右端要 Hp_norm）——         *)
(*   诚实前提位移，旗舰原签名不含此二者。                              *)
(* ============================================================ *)
Lemma hzlogd_proj_min_kl_hlogzfree :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set)
         (sumf : (S -> R) -> R)
         (sum_ext : forall f g : S -> R,
            (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (sum_add : forall f g : S -> R,
            req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)))
         (sum_linear : forall (a : R) (f : S -> R),
            req (sumf (fun s => mult a (f s))) (mult a (sumf f)))
         (sum_le : forall f g : S -> R,
            (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g))
         (log_req_compat : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
            req x y -> req (log x Hx) (log y Hy))
         (post_aud : S -> bool) (p : S -> R)
         (Hp_norm : req (sumf p) one)
         (Hp_pos : forall s : S, lt zero (p s))
         (HZ : lt zero (@Z_aud_req R RIS S sumf post_aud p))
         (Hmono : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
            le x y -> le (log x Hx) (log y Hy))
         (q : S -> R) (Hq : forall s : S, lt zero (q s))
         (Hqn : req (sumf q) one)
         (Hqz : forall s : S, post_aud s = false -> req (q s) zero),
    le (sumf (fun s =>
           @kl_proj_closed R RIS S sumf post_aud p Hp_pos HZ q Hq s))
       (sumf (fun s =>
           mult (q s)
                (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s))))).
Proof.
  intros R RIS S sumf sum_ext sum_add sum_linear sum_le log_req_compat
         post_aud p Hp_norm Hp_pos HZ Hmono q Hq Hqn Hqz.
  apply (@req_projected_distribution_minimizes_kl R RIS S sumf sum_ext sum_add
           sum_linear log_req_compat post_aud p Hp_pos HZ q Hq Hqn Hqz).
  (* HlogZ 槽放电：Z_aud ≤ one ⟹ log Z_aud ≤ 0（保底件直喂） *)
  apply (hzlogd_log_le_zero_of_le_one R RIS Hmono
           (@Z_aud_req R RIS S sumf post_aud p) HZ).
  (* Z_aud ≤ one：req_Z_aud_le_one（和单调）+ Hp_norm（le_id_r 换右端） *)
  exact (@le_id_r R RIS (@Z_aud_req R RIS S sumf post_aud p) (sumf p) one
           Hp_norm
           (@req_Z_aud_le_one R RIS S sumf sum_le post_aud p Hp_pos)).
Qed.

(* ============================================================ *)
(* 主件 2 地基：bool/Real 二态有限和（S := bool 二态审计实例）          *)
(*   sumf := plus (f true) (f false)；四条和前提 + log_req_compat      *)
(*   全部在本文件实证（Real 层闭合，零新假设）。                        *)
(* ============================================================ *)
Definition hzlogd_aud_sum (f : bool -> Real) : Real := plus (f true) (f false).

Lemma hzlogd_sum2_ext :
  forall f g : bool -> Real,
    (forall s : bool, req (f s) (g s)) ->
    req (hzlogd_aud_sum f) (hzlogd_aud_sum g).
Proof.
  intros f g H. unfold hzlogd_aud_sum.
  exact (req_plus_compat (f true) (g true) (f false) (g false)
           (H true) (H false)).
Qed.

Lemma hzlogd_sum2_add :
  forall f g : bool -> Real,
    req (hzlogd_aud_sum (fun s => plus (f s) (g s)))
        (plus (hzlogd_aud_sum f) (hzlogd_aud_sum g)).
Proof.
  intros f g. unfold hzlogd_aud_sum.
  apply (req_trans (plus (plus (f true) (g true)) (plus (f false) (g false)))
                   (plus (f true) (plus (g true) (plus (f false) (g false))))
                   (plus (plus (f true) (f false)) (plus (g true) (g false)))).
  - (* 步1：(a+b)+(c+d) → a+(b+(c+d))（assoc 反向） *)
    apply (req_sym (plus (f true) (plus (g true) (plus (f false) (g false))))
                   (plus (plus (f true) (g true)) (plus (f false) (g false)))
                   (plus_assoc (f true) (g true) (plus (f false) (g false)))).
  - apply (req_trans (plus (f true) (plus (g true) (plus (f false) (g false))))
                     (plus (f true) (plus (plus (g true) (f false)) (g false)))
                     (plus (plus (f true) (f false)) (plus (g true) (g false)))).
    + (* 步2：b+(c+d) → (b+c)+d（assoc 正向） *)
      apply (req_plus_compat (f true) (f true)
               (plus (g true) (plus (f false) (g false)))
               (plus (plus (g true) (f false)) (g false))).
      * apply req_refl.
      * apply plus_assoc.
    + apply (req_trans (plus (f true) (plus (plus (g true) (f false)) (g false)))
                       (plus (f true) (plus (plus (f false) (g true)) (g false)))
                       (plus (plus (f true) (f false)) (plus (g true) (g false)))).
      * (* 步3：(b+c)+d → (c+b)+d（comm 中段交换） *)
        apply (req_plus_compat (f true) (f true)
                 (plus (plus (g true) (f false)) (g false))
                 (plus (plus (f false) (g true)) (g false))).
        -- apply req_refl.
        -- apply (req_plus_compat (plus (g true) (f false))
                     (plus (f false) (g true)) (g false) (g false)).
           ++ apply plus_comm.
           ++ apply req_refl.
      * apply (req_trans (plus (f true) (plus (plus (f false) (g true)) (g false)))
                         (plus (f true) (plus (f false) (plus (g true) (g false))))
                         (plus (plus (f true) (f false)) (plus (g true) (g false)))).
        -- (* 步4：(c+b)+d → c+(b+d)（assoc 反向） *)
           apply (req_plus_compat (f true) (f true)
                    (plus (plus (f false) (g true)) (g false))
                    (plus (f false) (plus (g true) (g false)))).
           ++ apply req_refl.
           ++ apply (req_sym (plus (f false) (plus (g true) (g false)))
                             (plus (plus (f false) (g true)) (g false))
                             (plus_assoc (f false) (g true) (g false))).
        -- (* 步5：a+(c+(b+d)) → (a+c)+(b+d)（assoc 正向收口） *)
           apply plus_assoc.
Qed.

Lemma hzlogd_sum2_linear :
  forall (a : Real) (f : bool -> Real),
    req (hzlogd_aud_sum (fun s => mult a (f s))) (mult a (hzlogd_aud_sum f)).
Proof.
  intros a f. unfold hzlogd_aud_sum.
  apply (req_sym (mult a (plus (f true) (f false)))
                 (plus (mult a (f true)) (mult a (f false)))).
  apply distrib.
Qed.

Lemma hzlogd_sum2_le :
  forall f g : bool -> Real,
    (forall s : bool, le (f s) (g s)) ->
    le (hzlogd_aud_sum f) (hzlogd_aud_sum g).
Proof.
  intros f g H. unfold hzlogd_aud_sum.
  exact (le_plus_compat (f true) (g true) (f false) (g false)
           (H true) (H false)).
Qed.

(* log 兼容场实例（real_log_wd 直取；与 UpReqU2 T2 ② 同位闭合件） *)
Lemma hzlogd_log_req_compat_real :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (real_log_wd x y Hx Hy Hxy).
Qed.

(* ============================================================ *)
(* HZ 槽放电（二态「逐点见证」承接件）：通过点 true 处 p 正 ⟹           *)
(* Z_aud = plus (p true) zero > 0（iota 归约 + plus_zero 运输）。        *)
(* 二态空间里 max 项 = 通过点本身，无需 max 选择算子。                   *)
(* ============================================================ *)
Lemma hzlogd_HZ_bool :
  forall p : bool -> Real,
    lt zero (p true) ->
    lt zero (@Z_aud_req Real RealEnhancedReal bool hzlogd_aud_sum
               (fun b : bool => b) p).
Proof.
  intros p Hp.
  apply (@req_lt_compat Real RealEnhancedReal zero zero (p true)
           (@Z_aud_req Real RealEnhancedReal bool hzlogd_aud_sum
              (fun b : bool => b) p)).
  - apply req_refl.
  - exact (req_sym (@Z_aud_req Real RealEnhancedReal bool hzlogd_aud_sum
                      (fun b : bool => b) p)
                   (p true)
                   (req_trans (@Z_aud_req Real RealEnhancedReal bool
                                 hzlogd_aud_sum (fun b : bool => b) p)
                              (plus (p true) zero) (p true)
                              (req_refl (@Z_aud_req Real RealEnhancedReal bool
                                           hzlogd_aud_sum
                                           (fun b : bool => b) p))
                              (plus_zero (p true)))).
  - exact Hp.
Qed.

(* ============================================================ *)
(* 主件 2：旗舰 bool/Real 具体实例（HlogZ 槽由 T2 ② 放电件填充）        *)
(*   post_aud := fun b => b（审计集 = {true}）；和四前提全实证；        *)
(*   HZ 槽由 hzlogd_HZ_bool 放电（语句内联，免 assert 不透明墙）；       *)
(*   HlogZ 槽由 hzlogd_discharge_real 放电（Z_aud ≤ one 走               *)
(*   req_Z_aud_le_one + Hp_norm 同一路线）；                            *)
(*   余下前提仅 p/q 分布形态（Set 层：real_eq/real_lt 载体）。           *)
(* ============================================================ *)
Theorem hzlogd_proj_min_kl_bool :
  forall (p : bool -> Real)
         (Hp_norm : req (hzlogd_aud_sum p) one)
         (Hp_pos : forall s : bool, lt zero (p s))
         (q : bool -> Real) (Hq : forall s : bool, lt zero (q s))
         (Hqn : req (hzlogd_aud_sum q) one)
         (Hqz : forall s : bool,
            (fun b : bool => b) s = false -> req (q s) zero),
    le (hzlogd_aud_sum (fun s =>
          @kl_proj_closed Real RealEnhancedReal bool hzlogd_aud_sum
              (fun b : bool => b) p Hp_pos
              (hzlogd_HZ_bool p (Hp_pos true)) q Hq s))
       (hzlogd_aud_sum (fun s =>
          mult (q s)
               (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s))))).
Proof.
  intros p Hp_norm Hp_pos q Hq Hqn Hqz.
  apply (@req_projected_distribution_minimizes_kl Real RealEnhancedReal bool
           hzlogd_aud_sum hzlogd_sum2_ext hzlogd_sum2_add hzlogd_sum2_linear
           hzlogd_log_req_compat_real (fun b : bool => b) p Hp_pos
           (hzlogd_HZ_bool p (Hp_pos true)) q Hq Hqn Hqz).
  (* HlogZ 槽放电：T2 ② 具体件直喂 *)
  apply (hzlogd_discharge_real (@Z_aud_req Real RealEnhancedReal bool
                                  hzlogd_aud_sum (fun b : bool => b) p)
           (hzlogd_HZ_bool p (Hp_pos true))).
  exact (@le_id_r Real RealEnhancedReal
           (@Z_aud_req Real RealEnhancedReal bool hzlogd_aud_sum
              (fun b : bool => b) p)
           (hzlogd_aud_sum p) one Hp_norm
           (@req_Z_aud_le_one Real RealEnhancedReal bool hzlogd_aud_sum
              hzlogd_sum2_le (fun b : bool => b) p Hp_pos)).
Qed.

(* ============================================================ *)
(* G3 关：提取探针 + Print Assumptions（新件闭合性核验）                *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Warnings "-extraction-opaque-accessed".
Set Extraction Output Directory ".".
Extraction "upreqhlogzd_core.ml" hzlogd_log_le_zero_of_le_one
  hzlogd_proj_min_kl_hlogzfree.
Extraction "upreqhlogzd_real.ml" hzlogd_discharge_real
  hzlogd_discharge_real_direct hzlogd_HZ_bool hzlogd_proj_min_kl_bool.

Print Assumptions hzlogd_log_le_zero_of_le_one.
Print Assumptions hzlogd_discharge_real.
Print Assumptions hzlogd_discharge_real_direct.
Print Assumptions hzlogd_proj_min_kl_hlogzfree.
Print Assumptions hzlogd_HZ_bool.
Print Assumptions hzlogd_proj_min_kl_bool.

(* ============================================================ *)
(* 终验记录（编后核对回填）：                                          *)
(*   Qed 计数：11 = 保底1 + T2双形2 + 主件1 + 和地基4 + log兼容1 +      *)
(*   HZ放电1 + 主件2。                                                 *)
(*   G1 禁词 0；G2 EXIT=0；G3 提取双轨 core/real + PA 全 Closed；       *)
(*   G4 coqchk Modules were successfully checked。                     *)
(* ============================================================ *)
