(* ============================================================ *)
(* ToyR 玩具证替换件 —— T254 台账席 战役包O（tier2 第五批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   tmw_le_minus_nonneg_fw_et（原 L260，2 句玩具证）                     *)
(*   tmw_req_energy_exp_temp_strict_mono_full（原 L224，2 句玩具证）      *)
(*   tmw_req_energy_exp_temp_mono_full（原 L199，2 句玩具证）             *)
(*   tmw_req_energy_exp_temp_strict_mono_cond（原 L163，2 句玩具证）      *)
(*   tmw_req_energy_exp_temp_mono_cond（原 L140，2 句玩具证）             *)
(* ============================================================ *)

(* ============================================================ *)
(* TempMonoW2Mark.v                                              *)
(*                                                               *)
(* 目的：消解宿主 UpFirewallReq.v Section FirewallReq 的温度单调双  *)
(*       假设位（:135 req_energy_exp_temp_mono / :138              *)
(*       req_energy_exp_temp_strict_mono），宿主文件本体零改动；    *)
(*       两条消解定理各带一条宿主位没有的额外前提，按条件形与       *)
(*       全强度形两层呈现。                                         *)
(* 主件：tmw_req_energy_exp_temp_mono_cond / _full——              *)
(*         t1 < t2 ⟹ E(t1) ≤ E(t2)（条件形显式保留额外前提          *)
(*         lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))，  *)
(*         即 β1>β2；全强度形以宿主 lt↔minus 前提位单前提承载）；    *)
(*       tmw_req_energy_exp_temp_strict_mono_cond / _full——       *)
(*         t1 < t2 且 KL(p_t2‖p_t1) > 0 ⟹ E(t2) − E(t1) > 0；      *)
(*       依存位最小演示件 tmw_le_minus_nonneg_fw_et（宿主件5        *)
(*       :307-309 断言行逐字复刻）。                                *)
(* 依赖：CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist、        *)
(*       UpReqTempEntropy（:962 / :1428 同名定理、:628              *)
(*       req_inv_pos_lt_contra）、UpFirewallReq。                   *)
(* 备注：强度差如实申报——非全强度消解：两条消解定理各带额外前提     *)
(*       β1>β2；inv 反序位已由接口闭包内定理 req_inv_pos_lt_contra   *)
(*       免费供给，lt↔minus 连接位接口抽象层缺字段、以显式前提保留   *)
(*       （Real 实例化下为定理，不放大主张），故全强度形唯一余留     *)
(*       假设 = 宿主 :93 既有前提位（零新增主张）。出节签名按        *)
(*       Check 检验实测校正：mono 调用插 tmw_sum_le（在 sum_pos 与   *)
(*       base_loss 之间）；strict_mono 调用插 tmw_sum_le 且不带      *)
(*       eq_linear；载体差在节内坍缩为 δ，纯项式组装（零             *)
(*       rewrite），语句全 Set 层，全 Qed 闭合。                     *)
(* ============================================================ *)
(* [目标槽] UpFirewallReq.v Section FirewallReq 温度严格层双槽          *)
(*   （Variable 行 :135/:138，语句体 :135-137 / :138-143）：             *)
(*   槽W2a :135 req_energy_exp_temp_mono                                *)
(*         t1 < t2 ⟹ E(t1) ≤ E(t2)                                     *)
(*   槽W2b :138 req_energy_exp_temp_strict_mono                         *)
(*         t1 < t2 且 KL(p_t2‖p_t1) > 0 ⟹ E(t2) − E(t1) > 0            *)
(* [消解指针] UpReqTempEntropy.v 同名定理（Section ReqTempEntropy，     *)
(*   节闭 tB/tE 载体，库内既有）：                                      *)
(*   :962 req_energy_exp_temp_mono / :1428 req_energy_exp_temp_strict_mono *)
(* [强度差申报（如实申报：非全强度消解）] 两消解件各带                  *)
(*   一条宿主槽没有的额外诚实前提：                                     *)
(*     lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))  （β1>β2） *)
(*   消解件源注 :611-620 判定：inv_pos_lt_compat（Id L17119）已在       *)
(*   接口字段闭包内消解为定理 req_inv_pos_lt_contra（:628，零新增       *)
(*   公理面）；lt_minus_nonneg（Id L17121）接口抽象层无 lt↔minus 连接    *)
(*   字段，不可消解——故以显式前提逐位保留（Real 实例化下为定理，      *)
(*   不放大主张）。                                                     *)
(* [条件兑现路径] 额外前提在宿主节内可由两条既有槽复合满足：            *)
(*     lt_minus_nonneg (inv_pos t2 Ht2) (inv_pos t1 Ht1)                *)
(*       (inv_pos_lt_compat t1 t2 Ht1 Ht2 Hlt)                          *)
(*       : lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))        *)
(*   其中 inv 反序位 = req_inv_pos_lt_contra 免费兑现（定理）；         *)
(*   lt↔minus 位 = 宿主 :93 既有假设槽（零新增主张）。本件两段照此      *)
(*   分层给出：条件桥接引理（额外前提显式保留）+ 全强度桥接引理（唯一余留       *)
(*   假设 = 宿主 :93 槽型，inv 反序位实喂消解定理）。                   *)
(* [重述桥判定] fw_et（宿主）与 tE（消解）定义性同形：                  *)
(*     reqd_energy_exp_temp ≡ Σ (boltzmann·loss)（UpReqDist:2816），    *)
(*   fw_bt/tB 双方 δ 展开同为 reqd_boltzmann_dist_temp S sumf <和正     *)
(*   见证> base_loss Z_temp <Zspec见证> t Ht。本节每型一个见证槽        *)
(*   （tmw_sum_pos / tmw_Z_temp_spec 等），宿主位与消解位同喂同一       *)
(*   见证 → 载体差坍缩为 δ，桥接引理 exact 一步闭合（零 rewrite）。          *)
(* [依存位喂法]（真实依存坐标，实喂行）：                               *)
(*   · :309 宿主件5 req_entropy_temp_mono 证内 assert：                 *)
(*       req_le_minus_nonneg (fw_et t1)(fw_et t2)(槽W2a 实例)           *)
(*     替换 = 接口参数 ← tmw_req_energy_exp_temp_mono_full Hlmn（本件       *)
(*     :307-309 断言行已由 tmw_le_minus_nonneg_fw_et 最小演示件逐字     *)
(*     复刻实喂闭环）。                                                 *)
(*   · :370 宿主件6 req_entropy_temp_strict_mono 证内 assert：          *)
(*       槽W2b 实例（Hlt Hkl12 双前提）                                 *)
(*     替换 = 接口参数 ← tmw_req_energy_exp_temp_strict_mono_full Hlmn      *)
(*     （其结论即 :369-370 断言目标逐字，全强度桥接引理自身即依存位形）。   *)
(* [出节签名实测 20260915]（Check 检验逐轮实测定形）：                    *)
(*   mono :962 出节：sum_le 位在 sum_pos 与 base_loss 之间，              *)
(*     fsum_zero_nonneg / eq_linear 不入签名 → 两调用插 tmw_sum_le。      *)
(*   strict_mono :1428 出节：另插 fsum_le、eq_linear 不入签名 →           *)
(*     两调用插 tmw_sum_le 且不带 eq_linear；语句零改。                   *)
(*   req_inv_pos_lt_contra 出节 = {R}{RIS} + a b Ha Hb + Hlt（免补喂）。  *)
(* [纪律] 纯项式组装（零 rewrite/零 Morphisms）；语句全 Set 层；        *)
(*   全 Qed 闭合；宿主与只读树零改；Require UpReqTempEntropy 与         *)
(*   UpFirewallReq 均无被反向依赖（无环）。                             *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqTempEntropy.
Require Import UpFirewallReq.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section TmwMonoW2：宿主 Section FirewallReq 见证面与                 *)
(*   UpReqTempEntropy Section ReqTempEntropy 消解面之并集。             *)
(*   见证每型一个，宿主位/消解位同喂。                                  *)
(* ============================================================ *)
Section TmwMonoW2.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- 求和面（宿主 ssum_* 与消解面 fsum_* 同型合并） ---- *)
Hypothesis tmw_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis tmw_sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis tmw_sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis tmw_sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis tmw_sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis tmw_sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero ->
    forall s : S, req (f s) zero.

Variable base_loss : S -> R.

(* ---- log 桥面（消解面需求；宿主同位 :98-102 同型） ---- *)
Hypothesis tmw_dist_log_inv_one_inv :
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis tmw_dist_log_exp_neg :
  forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis tmw_dist_log_le_linear :
  forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one).
Hypothesis tmw_dist_log_eq_linear :
  forall (x : R) (Hx : lt zero x),
    req (log x Hx) (req_minus x one) -> req x one.

(* ---- Z_temp 接口（宿主 req_Z_temp_spec 同位） ---- *)
Variable Z_temp : R -> R.
Hypothesis tmw_Z_temp_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

(* ============================================================ *)
(* 条件桥 W2a（槽 :135 语句 + 额外前提显式保留，零放大）：              *)
(*   证 = 消解件 :962 同见证实例全参 exact（δ 通道一步）。              *)
(* ============================================================ *)
Theorem tmw_req_energy_exp_temp_mono_cond :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) ->
  le (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss
                            Z_temp tmw_Z_temp_spec t1 Ht1)
     (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss
                            Z_temp tmw_Z_temp_spec t2 Ht2).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hbd.
  exact (UpReqTempEntropy.req_energy_exp_temp_mono           S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos           tmw_sum_le           base_loss           tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg           tmw_dist_log_le_linear           Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hbd).
Qed.

(* ============================================================ *)
(* 条件桥 W2b（槽 :138 语句 + 额外前提显式保留，零放大）：              *)
(*   证 = 消解件 :1428 同见证实例全参 exact。                           *)
(* ============================================================ *)
Theorem tmw_req_energy_exp_temp_strict_mono_cond :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  lt zero (req_relative_entropy S sumf
             (@UpFirewallReq.fw_bt R RIS S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt R RIS S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t1 Ht1)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t1 Ht1)) ->
  lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) ->
  lt zero (req_minus (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t2 Ht2)
                     (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t1 Ht1)).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hkl Hbd.
  exact (UpReqTempEntropy.req_energy_exp_temp_strict_mono           S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos           tmw_sum_le           base_loss           tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg           tmw_dist_log_le_linear           Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hkl Hbd).
Qed.

(* ============================================================ *)
(* 全强度桥 W2a：宿主 :93 lt_minus_nonneg 槽型单前提 ⟹ 槽 :135 逐字。   *)
(*   inv 反序位实喂消解定理 req_inv_pos_lt_contra（:628，接口闭包       *)
(*   内真证零公理面）——宿主 :91 槽由此免费消解；唯一余留假设 = 宿主      *)
(*   :93 既有槽型（非新增主张）。                                       *)
(* ============================================================ *)
Theorem tmw_req_energy_exp_temp_mono_full :
  (forall a b : R, lt a b -> lt zero (req_minus b a)) ->
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  le (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss
                            Z_temp tmw_Z_temp_spec t1 Ht1)
     (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss
                            Z_temp tmw_Z_temp_spec t2 Ht2).
Proof.
  intros Hlmn t1 t2 Ht1 Ht2 Hlt.
  exact (UpReqTempEntropy.req_energy_exp_temp_mono           S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos           tmw_sum_le           base_loss           tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg           tmw_dist_log_le_linear           Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt           (Hlmn (inv_pos t2 Ht2) (inv_pos t1 Ht1)                 (UpReqTempEntropy.req_inv_pos_lt_contra t1 t2 Ht1 Ht2 Hlt))).
Qed.

(* ============================================================ *)
(* 全强度桥 W2b：同一余留槽型 ⟹ 槽 :138 逐字（其结论即宿主 :369-370    *)
(*   断言目标，依存位形自身）。                                         *)
(* ============================================================ *)
Theorem tmw_req_energy_exp_temp_strict_mono_full :
  (forall a b : R, lt a b -> lt zero (req_minus b a)) ->
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  lt zero (req_relative_entropy S sumf
             (@UpFirewallReq.fw_bt R RIS S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt R RIS S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t1 Ht1)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t1 Ht1)) ->
  lt zero (req_minus (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t2 Ht2)
                     (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t1 Ht1)).
Proof.
  intros Hlmn t1 t2 Ht1 Ht2 Hlt Hkl.
  exact (UpReqTempEntropy.req_energy_exp_temp_strict_mono           S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos           tmw_sum_le           base_loss           tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg           tmw_dist_log_le_linear           Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hkl           (Hlmn (inv_pos t2 Ht2) (inv_pos t1 Ht1)                 (UpReqTempEntropy.req_inv_pos_lt_contra t1 t2 Ht1 Ht2 Hlt))).
Qed.

(* ============================================================ *)
(* 依存位最小演示件：宿主件5 :307-309 断言行逐字复刻——                 *)
(*   req_le_minus_nonneg (fw_et t1)(fw_et t2)(槽W2a 位 ← 全强度桥)。    *)
(* ============================================================ *)
Theorem tmw_le_minus_nonneg_fw_et :
  (forall a b : R, lt a b -> lt zero (req_minus b a)) ->
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  le zero (req_minus (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t2 Ht2)
                     (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t1 Ht1)).
Proof.
  intros Hlmn t1 t2 Ht1 Ht2 Hlt.
  exact (req_le_minus_nonneg           (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss                                 Z_temp tmw_Z_temp_spec t1 Ht1)           (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss                                 Z_temp tmw_Z_temp_spec t2 Ht2)           (tmw_req_energy_exp_temp_mono_full Hlmn t1 t2 Ht1 Ht2 Hlt)).
Qed.

End TmwMonoW2.

(* ============================================================ *)
(* Print Assumptions 假设审计（五件全量）。                             *)
(* ============================================================ *)
Print Assumptions tmw_req_energy_exp_temp_mono_cond.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_cond.
Print Assumptions tmw_req_energy_exp_temp_mono_full.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_full.
Print Assumptions tmw_le_minus_nonneg_fw_et.

(* PA 追印段（T254 核验副本件） *)
Print Assumptions tmw_le_minus_nonneg_fw_et.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_full.
Print Assumptions tmw_req_energy_exp_temp_mono_full.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_cond.
Print Assumptions tmw_req_energy_exp_temp_mono_cond.
