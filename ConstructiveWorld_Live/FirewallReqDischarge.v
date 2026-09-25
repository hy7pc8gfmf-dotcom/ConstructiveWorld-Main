(* ==========================================================================)
   FirewallReqDischarge.v — 宿主 UpFirewallReq 温度三假设位的消解件
   使命: 三件逐字语句重申件（req_entropy_temp_explicit / req_relative_entropy_temp_decomp / req_temp_strict_ident2）+ 两条下游演示件，宿主文件本体零改动；清单所列五定理证明体经恒等核查与原件逐字同文。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist、UpReqTempEntropy（主路同名定理）、UpFirewallReq。
   对标: KL 分解恒等式 H(p_t) ≡ (1/t)·E(p_t) + log Z_t 等（温度-熵-相对熵关系的形式化）。
   构造性: 语句全 Set 层；纯项式组装（零 rewrite）、全 Qed 闭合；证明结尾记号与原件逐件守恒；Print Assumptions 审计在件尾。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树原地重编），cpu_guard 包裹限载。
   ========================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqTempEntropy.
Require Import UpFirewallReq.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section FrdTempDischarge：宿主 Section FirewallReq 见证面与          *)
(*   UpReqTempEntropy Section ReqTempEntropy 消解面之并集。见证每型     *)
(*   一个，宿主位/消解位同喂（重述桥判定见头注）。                      *)
(* ============================================================ *)
Section FrdTempDischarge.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- 求和面（宿主 ssum_* 与消解面 fsum_* 同型合并） ---- *)
Hypothesis frd_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis frd_sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis frd_sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis frd_sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis frd_sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis frd_sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero ->
    forall s : S, req (f s) zero.

Variable base_loss : S -> R.

(* ---- log 桥面（消解面需求；宿主同位 :98-102 同型） ---- *)
Hypothesis frd_dist_log_inv_one_inv :
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis frd_dist_log_exp_neg :
  forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis frd_dist_log_le_linear :
  forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one).
Hypothesis frd_dist_log_eq_linear :
  forall (x : R) (Hx : lt zero x),
    req (log x Hx) (req_minus x one) -> req x one.

(* ---- Z_temp 接口（宿主 req_Z_temp_spec 同位） ---- *)
Variable Z_temp : R -> R.
Hypothesis frd_Z_temp_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

(* ============================================================ *)
(* 重申件 A（槽A :122 逐字）：证 = 主路 :90 同名定理同见证实例。        *)
(* ============================================================ *)
Theorem frd_req_entropy_temp_explicit :
  forall (t : R) (Ht : lt zero t),
  req (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos base_loss Z_temp
                           frd_Z_temp_spec t Ht)
      (plus (mult (inv_pos t Ht)
                  (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos base_loss
                                        Z_temp frd_Z_temp_spec t Ht))
            (log (Z_temp t)
                 (req_Z_temp_pos S sumf frd_sum_pos base_loss Z_temp
                                 frd_Z_temp_spec t Ht))).
Proof.
  intros t Ht.
  exact (UpReqTempEntropy.req_entropy_temp_explicit           S sumf frd_sum_ext frd_sum_add frd_sum_linear frd_sum_pos           base_loss           frd_dist_log_inv_one_inv frd_dist_log_exp_neg           Z_temp frd_Z_temp_spec t Ht).
Qed.

(* ============================================================ *)
(* 重申件 B（槽B :128 逐字）：证 = 主路 :225，载体现身 fw_bt/fw_bt_pos， *)
(*   归一化证人 = fw_norm（fw_ 见证同喂）。                              *)
(* ============================================================ *)
Theorem frd_req_relative_entropy_temp_decomp :
  forall (t2 : R) (Ht2 : lt zero t2) (t1 : R) (Ht1 : lt zero t1),
  req (@UpFirewallReq.fw_kl R RIS S sumf frd_sum_pos base_loss Z_temp
                            frd_Z_temp_spec t1 t2 Ht1 Ht2)
      (plus (plus (opp (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos
                                            base_loss Z_temp
                                            frd_Z_temp_spec t1 Ht1))
                  (mult (inv_pos t2 Ht2)
                        (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos
                                              base_loss Z_temp
                                              frd_Z_temp_spec t1 Ht1)))
            (log (Z_temp t2)
                 (req_Z_temp_pos S sumf frd_sum_pos base_loss Z_temp
                                 frd_Z_temp_spec t2 Ht2))).
Proof.
  intros t2 Ht2 t1 Ht1.
  exact (UpReqTempEntropy.req_relative_entropy_temp_decomp           S sumf frd_sum_ext frd_sum_add frd_sum_linear frd_sum_pos           base_loss           frd_dist_log_inv_one_inv frd_dist_log_exp_neg           Z_temp frd_Z_temp_spec t2 Ht2           (@UpFirewallReq.fw_bt R RIS S sumf frd_sum_pos base_loss Z_temp                                 frd_Z_temp_spec t1 Ht1)           (@UpFirewallReq.fw_bt_pos R RIS S sumf frd_sum_pos base_loss                                    Z_temp frd_Z_temp_spec t1 Ht1)           (@UpFirewallReq.fw_norm R RIS S sumf frd_sum_linear frd_sum_pos                                   base_loss Z_temp frd_Z_temp_spec t1 Ht1)).
Qed.

(* ============================================================ *)
(* 重申件 C（槽C :144 逐字）：证 = 主路 :1208（其证内依存 :225 两例 +   *)
(*   A_chain2 交叉，装配链完备）。                                       *)
(* ============================================================ *)
Theorem frd_req_temp_strict_ident2 :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (plus (req_relative_entropy S sumf
             (@UpFirewallReq.fw_bt R RIS S sumf frd_sum_pos base_loss
                                   Z_temp frd_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt R RIS S sumf frd_sum_pos base_loss
                                   Z_temp frd_Z_temp_spec t1 Ht1)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t1 Ht1))
            (@UpFirewallReq.fw_kl R RIS S sumf frd_sum_pos base_loss
                                  Z_temp frd_Z_temp_spec t1 t2 Ht1 Ht2))
      (mult (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))
            (req_minus (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos
                                             base_loss Z_temp
                                             frd_Z_temp_spec t2 Ht2)
                       (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos
                                             base_loss Z_temp
                                             frd_Z_temp_spec t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  exact (UpReqTempEntropy.req_temp_strict_ident2           S sumf frd_sum_ext frd_sum_add frd_sum_linear frd_sum_pos           base_loss           frd_dist_log_inv_one_inv frd_dist_log_exp_neg           Z_temp frd_Z_temp_spec t1 t2 Ht1 Ht2).
Qed.

(* ============================================================ *)
(* 下游替换演示一：宿主件4（:187 依存位 :201/:203）零假设位可达——      *)
(*   槽A/槽B 参位实喂上面两重申件。                                     *)
(* ============================================================ *)
Theorem frd_recovery_entropy_gain :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (req_minus (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t2 Ht2)
                 (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t1 Ht1))
      (plus (mult (inv_pos t2 Ht2)
                  (req_minus (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos
                                                    base_loss Z_temp
                                                    frd_Z_temp_spec t2 Ht2)
                             (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos
                                                   base_loss Z_temp
                                                   frd_Z_temp_spec t1 Ht1)))
            (@UpFirewallReq.fw_kl R RIS S sumf frd_sum_pos base_loss
                                  Z_temp frd_Z_temp_spec t1 t2 Ht1 Ht2)).
Proof.
  intros t1 t2 Ht1 Ht2.
  exact (UpFirewallReq.req_recovery_entropy_gain           S sumf frd_sum_pos base_loss Z_temp frd_Z_temp_spec           frd_req_entropy_temp_explicit           frd_req_relative_entropy_temp_decomp           t1 t2 Ht1 Ht2).
Qed.

(* ============================================================ *)
(* 下游替换演示二：宿主件7 对偶形（:437 依存位 :458）——槽C 参位实喂     *)
(*   重申件 C（槽A/槽B 经件4 链式带入）。三槽替换至此全闭环。           *)
(* ============================================================ *)
Theorem frd_recovery_entropy_gain_alt :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (req_minus (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t2 Ht2)
                 (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t1 Ht1))
      (req_minus (mult (inv_pos t1 Ht1)
                       (req_minus (@UpFirewallReq.fw_et R RIS S sumf
                                                        frd_sum_pos
                                                        base_loss Z_temp
                                                        frd_Z_temp_spec
                                                        t2 Ht2)
                                  (@UpFirewallReq.fw_et R RIS S sumf
                                                        frd_sum_pos
                                                        base_loss Z_temp
                                                        frd_Z_temp_spec
                                                        t1 Ht1)))
                 (req_relative_entropy S sumf
                    (@UpFirewallReq.fw_bt R RIS S sumf frd_sum_pos base_loss
                                          Z_temp frd_Z_temp_spec t2 Ht2)
                    (@UpFirewallReq.fw_bt R RIS S sumf frd_sum_pos base_loss
                                          Z_temp frd_Z_temp_spec t1 Ht1)
                    (@UpFirewallReq.fw_bt_pos R RIS S sumf frd_sum_pos
                                             base_loss Z_temp
                                             frd_Z_temp_spec t2 Ht2)
                    (@UpFirewallReq.fw_bt_pos R RIS S sumf frd_sum_pos
                                             base_loss Z_temp
                                             frd_Z_temp_spec t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  exact (UpFirewallReq.req_recovery_entropy_gain_alt           S sumf frd_sum_pos base_loss Z_temp frd_Z_temp_spec           frd_req_entropy_temp_explicit           frd_req_relative_entropy_temp_decomp           frd_req_temp_strict_ident2           t1 t2 Ht1 Ht2).
Qed.

End FrdTempDischarge.

(* ============================================================ *)
(* Print Assumptions 假设审计（五件全量；与 bbd/enp 文末同款惯例），     *)
(* 语句面零改动、零新增假设位。                                          *)
(* ============================================================ *)
Print Assumptions frd_req_entropy_temp_explicit.
Print Assumptions frd_req_relative_entropy_temp_decomp.
Print Assumptions frd_req_temp_strict_ident2.
Print Assumptions frd_recovery_entropy_gain.
Print Assumptions frd_recovery_entropy_gain_alt.
