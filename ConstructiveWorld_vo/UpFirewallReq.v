(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpFirewallReq.v *)
(* *)
(* 目的： 防火墙机制的 req 抽象载体同构件。 *)
(* 主件： req_fw_energy_eta / req_entropy_temp_mono / req_entropy_temp_strict_mono 及 req_firewall_loop。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist。 *)
(* 备注： Id 层陈述经假设位承担；温度严格层的显式假设注记见正文。 *)
(* ============================================================ *)

(* ============================================================ *)
(*   （10 件）                                                    *)
(*   源定理：attn\UpFirewall.v（熵防火墙：退化检测与恢复的构造性闭环, *)
(*   伴件形态：req_* 独立伴 Section，与源定理同树（attn 目录）       *)
(* -------------------------------------------------------------- *)
(* 覆盖核对（req 件名 -> 源定理 Id 原件 @ 行号；件数规则：陈述含 Id  *)
(* 或证明核为 Id 迁移的声明，Variable 假设位计入；grep 实测 10，   *)
(* 规划书约 9，实测 10，全数结果零冻结；fw_double_pos @L130 零 Id  *)
(* 内容，按辅件结果不计件）：                                      *)
(*   件 1  req 假设位 req_Z_temp_spec           <- 源定理 L93        *)
(*   件 2  req_fw_energy_eta                    <- 源定理 L113（δ 件）*)
(*   件 3  req_fw_lt_double                     <- 源定理 L120        *)
(*   件 4  req_recovery_entropy_gain            <- 源定理 L139（主定理一）*)
(*   件 5  req_entropy_temp_mono                <- 源定理 L207        *)
(*   件 6  req_entropy_temp_strict_mono         <- 源定理 L261        *)
(*   件 7  req_recovery_entropy_gain_alt        <- 源定理 L318（主定理二）*)
(*   件 8  req_fw_verdict                       <- 源定理 L382（陈述迁移）*)
(*   件 9  req_fw_detect_warm                   <- 源定理 L388        *)
(*   件 10 req_firewall_loop                    <- 源定理 L412        *)
(* -------------------------------------------------------------- *)
(*   批 2 余件清单 a) 项（variational_temp_bound/energy_exp_temp_  *)
(*   mono/temp_strict_A_chain2/temp_strict_ident2/energy_exp_temp_ *)
(*   strict_mono/temp_energy_dual_closed）与 UpReqTempEntropy 件 1  *)

(*   位以 req Variable 槽承载（req_entropy_temp_explicit /          *)
(*   req_relative_entropy_temp_decomp / req_energy_exp_temp_mono /  *)
(*   req_energy_exp_temp_strict_mono / req_temp_strict_ident2），    *)
(*   假设位逐位保留不放大主张。                                     *)
(* 复用增量：Bt/归一/正性使用批 2 ReqTemp reqd_boltzmann_dist_temp  *)

(*   dist_log_inv_one_inv / dist_log_le_linear 同位声明）；减法/    *)
(*   旋转/分配使用批 1 UpReqAlgebra 引擎件。                        *)
(* 非平凡性分级：件 4/7 = A+（源定理最重 AC 链的 req 全链真证）；     *)
(*   件 5/6 = A（gibbs+恒等式迁移+加法保序 req 装配）；件 3 = A      *)
(*   （id_transport→lt_id_l 字段的传输真改）；件 9/10 = B（闭环     *)
(*   组装）；件 8 = 陈述迁移；件 2 = δ 平凡；件 1 = 假设位迁移。    *)
(* 诚实边界（源定理同款红线）：防火墙不主张 TV-熵传递；fw_verdict 的  *)
(*   Or 是证书和而非布尔判定器；全部接口假设有源定理同位先例。        *)
(* 纪律：纯 term-mode（零 rewrite/零 Morphisms）；语句全 Set 层；   *)
(*   全 Qed 完成；零禁词。                                          *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Import RealInterfaceEnhancedMod.

Section FirewallReq.

Context {R : Set}.
Context {RIS : RealInterfaceEnhancedSetoid R}.

Let zero := @zero R RIS.
Let one := @one R RIS.
Let plus := @plus R RIS.
Let mult := @mult R RIS.
Let opp := @opp R RIS.
Let lt := @lt R RIS.
Let le := @le R RIS.
Let log := @log R RIS.
Let inv_pos := @inv_pos R RIS.
Let exp_neg := @exp_neg R RIS.

(* ---- req 求和假设位（源定理 SumOver 使用字段逐位 req 化） ---- *)
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis ssum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis ssum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis ssum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis ssum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis ssum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).

Variable base_loss : S -> R.

(* 件 1：源定理 L93 Z_temp_spec 的 req 同形（假设位逐位保留） *)
Variable Z_temp : R -> R.
Hypothesis req_Z_temp_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

(* 源定理 L96-102 严格性/保序接口（同位假设槽，零放大） *)
Variable inv_pos_lt_compat : forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
  lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Variable lt_minus_nonneg : forall a b : R, lt a b -> lt zero (req_minus b a).
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).


Variable dist_log_inv_one_inv :
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Variable dist_log_le_linear :
  forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one).

(* ---- 温度参数化 Boltzmann 族（批 2 ReqTemp 直接使用） ---- *)
Definition fw_bt (t : R) (Ht : lt zero t) : S -> R :=
  reqd_boltzmann_dist_temp S sumf ssum_pos base_loss Z_temp req_Z_temp_spec t Ht.
Definition fw_bt_pos (t : R) (Ht : lt zero t) :
  forall s : S, lt zero (fw_bt t Ht s) :=
  reqd_boltzmann_dist_temp_pos S sumf ssum_pos base_loss Z_temp req_Z_temp_spec t Ht.
Definition fw_norm (t : R) (Ht : lt zero t) : req (sumf (fw_bt t Ht)) one :=
  reqd_boltzmann_dist_temp_normalized S sumf ssum_linear ssum_pos base_loss Z_temp
                                      req_Z_temp_spec t Ht.
Definition fw_h (t : R) (Ht : lt zero t) : R :=
  reqd_entropy_dist S sumf (fw_bt t Ht) (fw_bt_pos t Ht).
Definition fw_et (t : R) (Ht : lt zero t) : R :=
  sumf (fun s => mult (fw_bt t Ht s) (base_loss s)).
Definition fw_kl (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2) : R :=
  req_relative_entropy S sumf (fw_bt t1 Ht1) (fw_bt t2 Ht2)
                       (fw_bt_pos t1 Ht1) (fw_bt_pos t2 Ht2).

Variable req_entropy_temp_explicit : forall (t : R) (Ht : lt zero t),
  req (fw_h t Ht)
      (plus (mult (inv_pos t Ht) (fw_et t Ht))
            (log (Z_temp t)
                 (req_Z_temp_pos S sumf ssum_pos base_loss Z_temp
                                 req_Z_temp_spec t Ht))).
Variable req_relative_entropy_temp_decomp :
  forall (t2 : R) (Ht2 : lt zero t2) (t1 : R) (Ht1 : lt zero t1),
  req (fw_kl t1 t2 Ht1 Ht2)
      (plus (plus (opp (fw_h t1 Ht1)) (mult (inv_pos t2 Ht2) (fw_et t1 Ht1)))
            (log (Z_temp t2)
                 (req_Z_temp_pos S sumf ssum_pos base_loss Z_temp
                                 req_Z_temp_spec t2 Ht2))).
Variable req_energy_exp_temp_mono :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 -> le (fw_et t1 Ht1) (fw_et t2 Ht2).
Variable req_energy_exp_temp_strict_mono :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  lt zero (req_relative_entropy S sumf (fw_bt t2 Ht2) (fw_bt t1 Ht1)
                                 (fw_bt_pos t2 Ht2) (fw_bt_pos t1 Ht1)) ->
  lt zero (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)).
Variable req_temp_strict_ident2 :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (plus (req_relative_entropy S sumf (fw_bt t2 Ht2) (fw_bt t1 Ht1)
                                  (fw_bt_pos t2 Ht2) (fw_bt_pos t1 Ht1))
            (fw_kl t1 t2 Ht1 Ht2))
      (mult (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))
            (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1))).

(* ---- 基础引理 ---- *)

(* 件 2（δ 件）：能量期望的 η-形式桥（源定理 L113 id_refl 同位；req_minus
   /sumf 同形定义性展开） *)
Definition fw_energy_expectation (e p : S -> R) : R :=
  sumf (fun s => mult (p s) (e s)).
Lemma req_fw_energy_eta : forall (t : R) (Ht : lt zero t),
  req (fw_energy_expectation base_loss (fw_bt t Ht)) (fw_et t Ht).
Proof.
  intros t Ht. unfold fw_energy_expectation, fw_et.
  exact (req_refl (sumf (fun s => mult (fw_bt t Ht s) (base_loss s)))).
Qed.

(* 辅件（零 Id 内容，不计件）：倍温正性（源定理 L130 同位） *)
Lemma fw_double_pos : forall (t : R) (Ht : lt zero t), lt zero (plus t t).
Proof.
  intros t Ht. apply plus_positive; exact Ht.
Qed.

(* 件 3：倍温严格升（源定理 L120；req 差异真证：源定理 id_transport 换 req
   接口 lt_id_l 字段，zero+t ↦ t 的传输走 req_trans） *)
Lemma req_fw_lt_double : forall (t : R) (Ht : lt zero t), lt t (plus t t).
Proof.
  intros t Ht.
  apply (lt_id_l t (plus zero t) (plus t t)
                 (req_sym (plus zero t) t
                          (req_trans (plus zero t) (plus t zero) t
                                     (plus_comm zero t) (plus_zero t)))).
  apply (lt_plus_compat_lt_le zero t t t Ht (le_refl t)).
Qed.

(* ===== 件 4（主定理一）：恢复增益精确恒等式 =====
   源定理 L139：ΔH == β₂·(E₂ − E₁) + KL₁₂。req 全链真证：熵显式与
   KL 温度分解为显式假设假设位，余为源定理 AC 重排的扁平 req 跳链
   （u1/u2/v1-v3/u3/u4，每跳一个扁平项，零深嵌套）。 *)
Theorem req_recovery_entropy_gain :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))
      (plus (mult (inv_pos t2 Ht2) (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
            (fw_kl t1 t2 Ht1 Ht2)).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (b2 := inv_pos t2 Ht2).
  set (E1 := fw_et t1 Ht1).  set (E2 := fw_et t2 Ht2).
  set (H1 := fw_h t1 Ht1).   set (H2 := fw_h t2 Ht2).
  set (L2 := log (Z_temp t2)
                  (req_Z_temp_pos S sumf ssum_pos base_loss Z_temp
                                  req_Z_temp_spec t2 Ht2)).
  assert (Hex2 : req H2 (plus (mult b2 E2) L2))
    by exact (req_entropy_temp_explicit t2 Ht2).
  assert (Hkl : req (fw_kl t1 t2 Ht1 Ht2) (plus (plus (opp H1) (mult b2 E1)) L2))
    by exact (req_relative_entropy_temp_decomp t2 Ht2 t1 Ht1).
  assert (Hd : req (mult b2 (req_minus E2 E1)) (plus (mult b2 E2) (opp (mult b2 E1))))
    by exact (req_mult_minus_distr_l b2 E2 E1).
  (* v3 的零吸收子链 *)
  assert (Hv3 : req (plus (plus (mult b2 E2) (opp H1))
                          (plus (opp (mult b2 E1)) (mult b2 E1)))
                    (plus (mult b2 E2) (opp H1))).
  { apply (req_trans
              (plus (plus (mult b2 E2) (opp H1))
                    (plus (opp (mult b2 E1)) (mult b2 E1)))
              (plus (plus (mult b2 E2) (opp H1)) zero)
              (plus (mult b2 E2) (opp H1))).
    - exact (req_plus_compat (plus (mult b2 E2) (opp H1))
                             (plus (mult b2 E2) (opp H1))
                             (plus (opp (mult b2 E1)) (mult b2 E1)) zero
                             (req_refl (plus (mult b2 E2) (opp H1)))
                             (req_trans (plus (opp (mult b2 E1)) (mult b2 E1))
                                        (plus (mult b2 E1) (opp (mult b2 E1)))
                                        zero
                                        (plus_comm (opp (mult b2 E1)) (mult b2 E1))
                                        (plus_opp (mult b2 E1)))).
    - apply plus_zero. }
  (* u2 内核：b2(E2−E1) + (−H1 + b2E1) == b2E2 + −H1（Hd + swap_mid + 零吸收） *)
  assert (Hu2 : req (plus (mult b2 (req_minus E2 E1)) (plus (opp H1) (mult b2 E1)))
                    (plus (mult b2 E2) (opp H1))).
  { apply (req_trans
              (plus (mult b2 (req_minus E2 E1)) (plus (opp H1) (mult b2 E1)))
              (plus (plus (mult b2 E2) (opp (mult b2 E1))) (plus (opp H1) (mult b2 E1)))
              (plus (mult b2 E2) (opp H1))).
    - exact (req_plus_compat (mult b2 (req_minus E2 E1))
                             (plus (mult b2 E2) (opp (mult b2 E1)))
                             (plus (opp H1) (mult b2 E1)) (plus (opp H1) (mult b2 E1))
                             Hd (req_refl (plus (opp H1) (mult b2 E1)))).
    - apply (req_trans
                (plus (plus (mult b2 E2) (opp (mult b2 E1))) (plus (opp H1) (mult b2 E1)))
                (plus (plus (mult b2 E2) (opp H1)) (plus (opp (mult b2 E1)) (mult b2 E1)))
                (plus (mult b2 E2) (opp H1))).
      + exact (req_plus_swap_mid (mult b2 E2) (opp (mult b2 E1)) (opp H1) (mult b2 E1)).
      + exact Hv3. }
  (* u3：(b2E2 + −H1) + L2 == (b2E2 + L2) + −H1 *)
  assert (Hu3 : req (plus (plus (mult b2 E2) (opp H1)) L2)
                    (plus (plus (mult b2 E2) L2) (opp H1))).
  { apply (req_trans (plus (plus (mult b2 E2) (opp H1)) L2)
                     (plus (mult b2 E2) (plus (opp H1) L2))
                     (plus (plus (mult b2 E2) L2) (opp H1))).
    - exact (req_sym (plus (mult b2 E2) (plus (opp H1) L2))
                     (plus (plus (mult b2 E2) (opp H1)) L2)
                     (plus_assoc (mult b2 E2) (opp H1) L2)).
    - apply (req_trans (plus (mult b2 E2) (plus (opp H1) L2))
                       (plus (mult b2 E2) (plus L2 (opp H1)))
                       (plus (plus (mult b2 E2) L2) (opp H1))).
      + exact (req_plus_compat (mult b2 E2) (mult b2 E2)
                               (plus (opp H1) L2) (plus L2 (opp H1))
                               (req_refl (mult b2 E2)) (plus_comm (opp H1) L2)).
      + exact (plus_assoc (mult b2 E2) L2 (opp H1)). }
  (* 主体：G-RHS →[Hkl]→ X1 →[u1]→ … → H2 + −H1（= G-LHS，δ 透明） *)
  exact (req_sym
            (plus (mult b2 (req_minus E2 E1)) (fw_kl t1 t2 Ht1 Ht2))
            (plus H2 (opp H1))
            (req_trans
               (plus (mult b2 (req_minus E2 E1)) (fw_kl t1 t2 Ht1 Ht2))
               (plus (mult b2 (req_minus E2 E1))
                     (plus (plus (opp H1) (mult b2 E1)) L2))
               (plus H2 (opp H1))
               (req_plus_compat
                  (mult b2 (req_minus E2 E1)) (mult b2 (req_minus E2 E1))
                  (fw_kl t1 t2 Ht1 Ht2)
                  (plus (plus (opp H1) (mult b2 E1)) L2)
                  (req_refl (mult b2 (req_minus E2 E1))) Hkl)
               (req_trans
                  (plus (mult b2 (req_minus E2 E1))
                        (plus (plus (opp H1) (mult b2 E1)) L2))
                  (plus (plus (mult b2 E2) (opp H1)) L2)
                  (plus H2 (opp H1))
                  (req_trans
                     (plus (mult b2 (req_minus E2 E1))
                           (plus (plus (opp H1) (mult b2 E1)) L2))
                     (plus (plus (mult b2 (req_minus E2 E1)) (plus (opp H1) (mult b2 E1))) L2)
                     (plus (plus (mult b2 E2) (opp H1)) L2)
                     (plus_assoc (mult b2 (req_minus E2 E1))
                                 (plus (opp H1) (mult b2 E1)) L2)
                     (req_plus_compat
                        (plus (mult b2 (req_minus E2 E1)) (plus (opp H1) (mult b2 E1)))
                        (plus (mult b2 E2) (opp H1))
                        L2 L2 Hu2 (req_refl L2)))
                  (req_trans
                     (plus (plus (mult b2 E2) (opp H1)) L2)
                     (plus (plus (mult b2 E2) L2) (opp H1))
                     (plus H2 (opp H1))
                     Hu3
                     (req_plus_compat (plus (mult b2 E2) L2) H2
                                      (opp H1) (opp H1)
                                      (req_sym H2 (plus (mult b2 E2) L2) Hex2)
                                      (req_refl (opp H1))))))).
Qed.

(* ===== 件 5（主结果）：温度-熵单调 =====
   源定理 L207：t1 < t2 ⟹ H(p_{t1}) ≤ H(p_{t2})。路径：能量单调显式假设槽
   + 件 4 恒等式迁移 + 批 2 req_gibbs_inequality。 *)
Theorem req_entropy_temp_mono :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 -> le (fw_h t1 Ht1) (fw_h t2 Ht2).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt.
  assert (HdE : le zero (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
    by exact (req_le_minus_nonneg (fw_et t1 Ht1) (fw_et t2 Ht2)
                                  (req_energy_exp_temp_mono t1 t2 Ht1 Ht2 Hlt)).
  assert (Hkl : le zero (fw_kl t1 t2 Ht1 Ht2))
    by exact (@req_gibbs_inequality R RIS S sumf ssum_ext ssum_add ssum_linear
                                    ssum_le dist_log_inv_one_inv dist_log_le_linear
                                    (fw_bt t1 Ht1) (fw_bt t2 Ht2)
                                    (fw_bt_pos t1 Ht1) (fw_bt_pos t2 Ht2)
                                    (fw_norm t1 Ht1) (fw_norm t2 Ht2)).
  assert (Hb2 : le zero (inv_pos t2 Ht2))
    by exact (lt_le_iff zero (inv_pos t2 Ht2) (inl (inv_pos_pos t2 Ht2))).
  assert (Hterm : le zero (mult (inv_pos t2 Ht2)
                                (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))).
  { apply (le_id_l zero (mult (inv_pos t2 Ht2) zero)
                   (mult (inv_pos t2 Ht2) (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))).
    - exact (req_sym (mult (inv_pos t2 Ht2) zero) zero
                     (mult_zero (inv_pos t2 Ht2))).
    - exact (req_le_mult_compat_r (inv_pos t2 Ht2) zero
                                  (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1))
                                  Hb2 HdE). }
  assert (Hsum : le zero (plus (mult (inv_pos t2 Ht2)
                                      (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                               (fw_kl t1 t2 Ht1 Ht2))).
  { apply (le_trans zero
                    (mult (inv_pos t2 Ht2) (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                    (plus (mult (inv_pos t2 Ht2)
                                (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                          (fw_kl t1 t2 Ht1 Ht2))).
    - exact Hterm.
    - exact (req_le_plus_nonneg_r
                (mult (inv_pos t2 Ht2) (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                (fw_kl t1 t2 Ht1 Ht2) Hkl). }
  assert (Hfin : le zero (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))).
  { apply (le_id_r zero
                   (plus (mult (inv_pos t2 Ht2)
                               (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                         (fw_kl t1 t2 Ht1 Ht2))
                   (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))).
    - exact (req_sym (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))
                     (plus (mult (inv_pos t2 Ht2)
                                 (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                           (fw_kl t1 t2 Ht1 Ht2))
                     (req_recovery_entropy_gain t1 t2 Ht1 Ht2)).
    - exact Hsum. }
  apply (le_id_r (fw_h t1 Ht1)
                 (plus (fw_h t1 Ht1) (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1)))
                 (fw_h t2 Ht2)).
  - exact (req_minus_plus_cancel (fw_h t1 Ht1) (fw_h t2 Ht2)).
  - exact (req_le_plus_nonneg_r (fw_h t1 Ht1)
                                (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1)) Hfin).
Qed.

(* ===== 件 6（严格档）：升温 ⟹ 熵严格恢复 =====
   源定理 L261；诚实条件同款：KL(p_{t2}‖p_{t1}) > 0。 *)
Theorem req_entropy_temp_strict_mono :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  lt zero (req_relative_entropy S sumf (fw_bt t2 Ht2) (fw_bt t1 Ht1)
                                (fw_bt_pos t2 Ht2) (fw_bt_pos t1 Ht1)) ->
  lt (fw_h t1 Ht1) (fw_h t2 Ht2).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hkl12.
  assert (HdE : lt zero (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
    by exact (req_energy_exp_temp_strict_mono t1 t2 Ht1 Ht2 Hlt Hkl12).
  assert (Hterm : lt zero (mult (inv_pos t2 Ht2)
                                (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1))))
    by exact (mult_positive (inv_pos t2 Ht2)
                            (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1))
                            (inv_pos_pos t2 Ht2) HdE).
  assert (Hkl21 : le zero (fw_kl t1 t2 Ht1 Ht2))
    by exact (@req_gibbs_inequality R RIS S sumf ssum_ext ssum_add ssum_linear
                                    ssum_le dist_log_inv_one_inv dist_log_le_linear
                                    (fw_bt t1 Ht1) (fw_bt t2 Ht2)
                                    (fw_bt_pos t1 Ht1) (fw_bt_pos t2 Ht2)
                                    (fw_norm t1 Ht1) (fw_norm t2 Ht2)).
  assert (Hsum : lt zero (plus (mult (inv_pos t2 Ht2)
                                      (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                               (fw_kl t1 t2 Ht1 Ht2)))
    by exact (lt_le_trans zero
                          (mult (inv_pos t2 Ht2)
                                (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                          (plus (mult (inv_pos t2 Ht2)
                                      (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                                (fw_kl t1 t2 Ht1 Ht2))
                          Hterm
                          (req_le_plus_nonneg_r
                              (mult (inv_pos t2 Ht2) (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                              (fw_kl t1 t2 Ht1 Ht2) Hkl21)).
  assert (Hfin : lt zero (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))).
  { apply (lt_id_r zero
                   (plus (mult (inv_pos t2 Ht2)
                               (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                         (fw_kl t1 t2 Ht1 Ht2))
                   (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))).
    - exact (req_sym (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))
                     (plus (mult (inv_pos t2 Ht2)
                                 (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                           (fw_kl t1 t2 Ht1 Ht2))
                     (req_recovery_entropy_gain t1 t2 Ht1 Ht2)).
    - exact Hsum. }
  apply (lt_id_r (fw_h t1 Ht1)
                 (plus (fw_h t1 Ht1) (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1)))
                 (fw_h t2 Ht2)).
  - exact (req_minus_plus_cancel (fw_h t1 Ht1) (fw_h t2 Ht2)).
  - apply (lt_id_l (fw_h t1 Ht1) (plus zero (fw_h t1 Ht1))
                   (plus (fw_h t1 Ht1) (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1)))).
    + exact (req_sym (plus zero (fw_h t1 Ht1)) (fw_h t1 Ht1)
                              (req_trans (plus zero (fw_h t1 Ht1))
                                         (plus (fw_h t1 Ht1) zero)
                                         (fw_h t1 Ht1)
                                         (plus_comm zero (fw_h t1 Ht1))
                                         (plus_zero (fw_h t1 Ht1)))).
    + apply (lt_id_r (plus zero (fw_h t1 Ht1))
                              (plus (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1)) (fw_h t1 Ht1))
                              (plus (fw_h t1 Ht1) (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1)))).
      * exact (plus_comm (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1)) (fw_h t1 Ht1)).
      * exact (lt_plus_compat_lt_le zero
                                      (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))
                                      (fw_h t1 Ht1) (fw_h t1 Ht1)
                                      Hfin (le_refl (fw_h t1 Ht1))).
Qed.

(* ===== 件 7（主定理二，对偶形态）：对称 KL 联立 =====
   形态 = req_temp_strict_ident2 假设位条件形（出节成显式参，假设位零放大）。
   记 b1/b2、E1/E2、dE、H1/H2、K_A（假设位首和项）、K_B（fw_kl）：
     β1·dE == β2·dE + (β1−β2)·dE →[假设位之对称]→ β2·dE + (K_A + K_B)
            == (β2·dE + K_B) + K_A == ΔH + K_A（件 4 之对称），
   故 (β1·dE) − K_A == (ΔH + K_A) − K_A == ΔH（req_minus_plus_cancel_r
   经 plus_comm 两步完成），目标 req_sym 翻转。 *)
Theorem req_recovery_entropy_gain_alt :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (req_minus (fw_h t2 Ht2) (fw_h t1 Ht1))
      (req_minus (mult (inv_pos t1 Ht1) (req_minus (fw_et t2 Ht2) (fw_et t1 Ht1)))
                 (req_relative_entropy S sumf (fw_bt t2 Ht2) (fw_bt t1 Ht1)
                                        (fw_bt_pos t2 Ht2) (fw_bt_pos t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (b1 := inv_pos t1 Ht1).
  set (b2 := inv_pos t2 Ht2).
  set (E1 := fw_et t1 Ht1).
  set (E2 := fw_et t2 Ht2).
  set (H1 := fw_h t1 Ht1).
  set (H2 := fw_h t2 Ht2).
  set (dE := req_minus E2 E1).
  set (KA := req_relative_entropy S sumf (fw_bt t2 Ht2) (fw_bt t1 Ht1)
                               (fw_bt_pos t2 Ht2) (fw_bt_pos t1 Ht1)).
  set (KB := fw_kl t1 t2 Ht1 Ht2).
  assert (Hg4 : req (req_minus H2 H1) (plus (mult b2 dE) KB))
    by exact (req_recovery_entropy_gain t1 t2 Ht1 Ht2).
  assert (Hsym : req (plus KA KB) (mult (req_minus b1 b2) dE))
    by exact (req_temp_strict_ident2 t1 t2 Ht1 Ht2).
  assert (Hb1 : req b1 (plus b2 (req_minus b1 b2)))
    by exact (req_sym (plus b2 (req_minus b1 b2)) b1
                      (req_minus_plus_cancel b2 b1)).
  assert (Hsplit : req (mult b1 dE) (plus (mult b2 dE) (mult (req_minus b1 b2) dE))).
  { exact (req_trans (mult b1 dE)
                     (mult (plus b2 (req_minus b1 b2)) dE)
                     (plus (mult b2 dE) (mult (req_minus b1 b2) dE))
                     (req_mult_compat b1 (plus b2 (req_minus b1 b2)) dE dE
                                      Hb1 (req_refl dE))
                     (req_mult_plus_distr_r b2 (req_minus b1 b2) dE)). }
  assert (Hsym' : req (mult (req_minus b1 b2) dE) (plus KA KB))
    by exact (req_sym (plus KA KB) (mult (req_minus b1 b2) dE) Hsym).
  assert (Hb'' : req (mult b1 dE) (plus (req_minus H2 H1) KA)).
  { exact (req_trans (mult b1 dE)
                     (plus (mult b2 dE) (plus KA KB))
                     (plus (req_minus H2 H1) KA)
                     (req_trans (mult b1 dE)
                                (plus (mult b2 dE) (mult (req_minus b1 b2) dE))
                                (plus (mult b2 dE) (plus KA KB))
                                Hsplit
                                (req_plus_compat (mult b2 dE) (mult b2 dE)
                                                 (mult (req_minus b1 b2) dE)
                                                 (plus KA KB)
                                                 (req_refl (mult b2 dE))
                                                 Hsym'))
                     (req_trans (plus (mult b2 dE) (plus KA KB))
                                (plus (plus (mult b2 dE) KB) KA)
                                (plus (req_minus H2 H1) KA)
                                (req_trans (plus (mult b2 dE) (plus KA KB))
                                           (plus (mult b2 dE) (plus KB KA))
                                           (plus (plus (mult b2 dE) KB) KA)
                                           (req_plus_compat (mult b2 dE)
                                                            (mult b2 dE)
                                                            (plus KA KB)
                                                            (plus KB KA)
                                                            (req_refl (mult b2 dE))
                                                            (plus_comm KA KB))
                                           (plus_assoc (mult b2 dE) KB KA))
                                (req_plus_compat (plus (mult b2 dE) KB)
                                                 (req_minus H2 H1)
                                                 KA KA
                                                 (req_sym (req_minus H2 H1)
                                                          (plus (mult b2 dE) KB)
                                                          Hg4)
                                                 (req_refl KA)))). }
  exact (req_sym (req_minus (mult b1 dE) KA) (req_minus H2 H1)
                 (req_trans (req_minus (mult b1 dE) KA)
                            (req_minus (plus (req_minus H2 H1) KA) KA)
                            (req_minus H2 H1)
                            (reqd_minus_compat (mult b1 dE)
                                               (plus (req_minus H2 H1) KA)
                                               KA KA
                                               Hb'' (req_refl KA))
                            (req_trans (req_minus (plus (req_minus H2 H1) KA) KA)
                                       (req_minus (plus KA (req_minus H2 H1)) KA)
                                       (req_minus H2 H1)
                                       (reqd_minus_compat
                                          (plus (req_minus H2 H1) KA)
                                          (plus KA (req_minus H2 H1))
                                          KA KA
                                          (plus_comm (req_minus H2 H1) KA)
                                          (req_refl KA))
                                       (req_minus_plus_cancel_r KA
                                                                (req_minus H2 H1))))).
Qed.

(* ===== 件 8/9/10：闭环封装（证书形态状态机） =====
   （Set 层，非布尔判定器）；退化支重装判定仍为 inr。 *)

Definition req_fw_verdict (Hmin : R) (t : R) (Ht : lt zero t) : Set :=
  Or (le Hmin (fw_h t Ht))
     (sigT (fun gap : R => req gap (req_minus (fw_h t Ht) Hmin))).

Theorem req_fw_detect_warm :
  forall (Hmin : R) (t : R) (Ht : lt zero t)
         (Hdef : sigT (fun gap : R => req gap (req_minus (fw_h t Ht) Hmin))),
  sigT (fun t' => sigT (fun Ht' : lt zero t' =>
    And (lt t t')
        (And (le (fw_h t Ht) (fw_h t' Ht'))
             (req (req_minus (fw_h t' Ht') (fw_h t Ht))
                  (plus (mult (inv_pos t' Ht') (req_minus (fw_et t' Ht') (fw_et t Ht)))
                        (fw_kl t t' Ht Ht')))))).
Proof.
  intros Hmin t Ht Hdef.
  assert (Ht' : lt zero (plus t t)) by exact (fw_double_pos t Ht).
  assert (Hup : lt t (plus t t)) by exact (req_fw_lt_double t Ht).
  exists (plus t t). exists Ht'.
  split.
  - exact Hup.
  - split.
    + exact (req_entropy_temp_mono t (plus t t) Ht Ht' Hup).
    + exact (req_recovery_entropy_gain t (plus t t) Ht Ht').
Qed.

Theorem req_firewall_loop :
  forall (Hmin : R) (t : R) (Ht : lt zero t) (v : req_fw_verdict Hmin t Ht),
  sigT (fun t' => sigT (fun Ht' : lt zero t' =>
    And (le t t')
        (And (le (fw_h t Ht) (fw_h t' Ht'))
             (req_fw_verdict Hmin t' Ht')))).
Proof.
  intros Hmin t Ht v. destruct v as [Hok | Hdef].
  - exists t. exists Ht.
    split.
    + apply le_refl.
    + split.
      * apply le_refl.
      * left. exact Hok.
  - assert (Ht' : lt zero (plus t t)) by exact (fw_double_pos t Ht).
    assert (Hup : lt t (plus t t)) by exact (req_fw_lt_double t Ht).
    exists (plus t t). exists Ht'.
    split.
    + exact (lt_le_iff t (plus t t) (inl Hup)).
    + split.
      * exact (req_entropy_temp_mono t (plus t t) Ht Ht' Hup).
      * right. exists (req_minus (fw_h (plus t t) Ht') Hmin).
        exact (req_refl (req_minus (fw_h (plus t t) Ht') Hmin)).
Qed.

End FirewallReq.
