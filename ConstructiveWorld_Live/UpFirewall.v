(* ============================================================ *)
(* 【同名替换稿说明】本件为玩具级定理同名替换件：原件全文逐字保留， *)
(* 仅将清单所列玩具位中真刀位之证明体替换为显式见证微刀（裸          *)
(* reflexivity 换 Qeq_refl 显式项；apply 反射位换全参显式见证项），   *)
(* 非刀位玩具体与其余全部文本逐字保留，声明面与引用面零改动，零新增  *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留原件   *)
(* Print Assumptions 追印面。                                        *)
(* 清单：                                                          *)
(*   fw_energy_eta（原 L119，显式见证微刀 1 处）                             *)
(* ============================================================ *)

(* ============================================================ *)
(* UpFirewall.v *)
(* *)
(* 目的： 防火墙机制：能量-温度界、熵温度单调与防火墙循环（Real 层）。 *)
(* 主件： fw_energy_eta / fw_lt_double 能量界；entropy_temp_mono / entropy_temp_strict_mono；firewall_loop。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： 基损失非负、求和正性等以显式 Variable 前提给出；判定面 fw_verdict 为 Set 层编码。 *)
(* 编译配方：SW2 全字面环境（COQLIB/ROCQLIB/OCAMLLIB/COQPATH 置空）， *)
(*   Rocq 9.1 coqc -q -native-compiler no，-Q 单根。 *)
(* ============================================================ *)

(* ============================================================
   UpFirewall.v —— 熵防火墙：退化检测与恢复的构造性闭环
   （上游三段：UpEntropyGain 增量核算 + UpBudgetReal 预算击穿）

   纸笔推导（先于动手，完整链）：
     连续对偶：H(T) = log Z(T) + E(T)/T，∂H/∂T = Var_T(E)/T² ≥ 0。
     构造性离散版不走导数，走**代数恒等式**（本件件 2）：
       对任意两正温度 t1 t2（无需任何序前提）：
         ΔH := H(p_{t2}) − H(p_{t1})
            == β₂·(E₂ − E₁) + KL(p_{t1} ‖ p_{t2})      （β₂ := 1/t₂）
       三行证明：
                relative_entropy_temp_decomp]
             = H₂ − H₁                                 [熵显式
                entropy_temp_explicit]
       KL 项承担了连续版 Var_T(E) 的角色——"离散方差"。
     单调（件 1）是恒等式的推论：
       t1 < t2 ⟹ E₁ ≤ E₂（根 energy_exp_temp_mono，L17521）
              ⟹ β₂·(E₂−E₁) ≥ 0（β₂ > 0，le_mult_compat_r）
       KL ≥ 0（根 gibbs_inequality，L16629）
       ⟹ ΔH ≥ 0 ⟹ H(p_{t1}) ≤ H(p_{t2})。
     对称 KL 恒等（根 temp_strict_ident2，L17879）：
       (β₁−β₂)·(E₂−E₁) == KL(p_{t2}‖p_{t1}) + KL(p_{t1}‖p_{t2})
     与件 2 联立消 ΔE 得第二恢复形态（件 2 alt）：
       ΔH == β₁·(E₂−E₁) − KL(p_{t2}‖p_{t1})
     （除法式 ΔH == β₂(K₁₂+K₂₁)/(β₁−β₂) + K₂₁ 需 inv_pos 链，
       无增量信息，显式弃用。）

   结果件：
     件 1  entropy_temp_mono：t1 < t2 ⟹ H(p_{t1}) ≤ H(p_{t2})
           （严格前提版；接口层 le 序不可判定，非严格版以件 2
             恒等式为精确内容——恒等式对一切正温度对成立）
     件 2  recovery_entropy_gain：恢复增益精确恒等式（主形态）
           + recovery_entropy_gain_alt：对称 KL 联立形态
           + entropy_temp_strict_mono：严格单调档
            （显式条件 同款：KL(p_{t2}‖p_{t1}) > 0）
     件 3  fw_verdict（Or 编码健康/退化判定）+ fw_detect_warm
           （退化 ⟹ sigT 升温目标 t' := t+t 与恢复证书）
           + firewall_loop（闭环：温度不降 + 熵不降 + 判定重装）

   显式边界（写进头的红线）：
     1) 熵防火墙不主张 TV-熵传递（Pinsker 型在册构造性红线）——
        闭环只证"升温 ⟹ 熵不降（且增量有精确分解）"，
        不证"熵恢复 ⟹ 分布距离收缩"。
     2) 闭环为证书形态非可判定检测：Real 层序不可判定（接口 le
        无三分律；root L139-141 已移除 le_lt_dec 并注明其经典性），
        fw_verdict 的 Or 是**证书和**（A+B），不是布尔判定器。
     3) 显式接口假设（全部有根内同名先例，非经典公理）：
          base_loss / sum_over_S_pos / Z_temp / Z_temp_spec
            —— 根 FreeEnergyMinimization 区同名 Variable 复刻；
          inv_pos_lt_compat / lt_minus_nonneg
            —— 根 区同名 Variable（L17119-17121）复刻，
               Real 层可实例化；
          lt_plus_compat_lt_le
            —— 根 ConvergenceCauchy 区同名 Variable 先例
               （UpEntropyGain.v 同名复用），仅用于升温目标
               t' := t+t 的严格性 lt t (t+t)。

   纪律：纯构造性 / Set 层 / 语句零 Prop（Id/le/lt/And:=A*B/
        Or:=A+b/sigT）/ 全程零未证缺口、零经典公理 / 可提取
        OCaml（提取产物经验收关卡核验）。
   ============================================================ *)
Require Import CW_ConstructiveWorld_219.

Section FirewallLoop.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* 解包接口字段（同根 FreeEnergyMinimization 区先例） *)
Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let le := @le RI.
Let lt := @lt RI.
Let log := @log RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.
(* minus 保持根全局 Definition（minus a b := plus a (opp b)） *)

Variable base_loss : S -> R.
Variable sum_over_S_pos : forall f : S -> R,
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).
Variable Z_temp : R -> R.
Variable Z_temp_spec : forall (t : R) (Ht : lt zero t),
  Id (Z_temp t) (sum_over_S (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).
(* 严格性接口（根 区同名 Variable 复刻） *)
Variable inv_pos_lt_compat : forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
  lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Variable lt_minus_nonneg : forall a b : R, lt a b -> lt zero (minus b a).
(* 混合 lt+le 加法保序（根 ConvergenceCauchy 区同名 Variable 先例；
   仅用于升温目标 t' := t+t 的严格性） *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* 温度参数化 Boltzmann 族速记（全参显式） *)
Let Bt (t : R) (Ht : lt zero t) : S -> R :=
  boltzmann_dist_temp base_loss sum_over_S_pos Z_temp Z_temp_spec t Ht.
Let Et (t : R) (Ht : lt zero t) : R :=
  energy_exp_temp base_loss sum_over_S_pos Z_temp Z_temp_spec t Ht.

(* ===== 基础引理 ===== *)

(* 能量期望的 η-形式桥：energy_expectation (Bt t) 定义性 == Et t *)
Lemma fw_energy_eta : forall (t : R) (Ht : lt zero t),
  Id (energy_expectation base_loss (Bt t Ht)) (Et t Ht).
Proof. intros t Ht. exact (@id_refl _ (energy_expectation base_loss (Bt t Ht))). Qed.

(* 倍温严格升：t > 0 ⟹ t < t + t（升温目标的构造性证书）
   （接口 plus 抽象：plus zero t 与 t 非转换可互换，
     须走 id_transport——抽象层 Id 假设禁 rewrite 的标准通路） *)
Lemma fw_lt_double : forall t : R, forall Ht : lt zero t,
  lt t (plus t t).
Proof.
  intros t Ht.
  apply (id_transport (fun w => lt w (plus t t))
                      (id_trans (plus_comm zero t) (plus_zero t))).
  apply (lt_plus_compat_lt_le zero t t t Ht (le_refl t)).
Qed.

(* 倍温正性：t > 0 ⟹ t + t > 0 *)
Lemma fw_double_pos : forall t : R, forall Ht : lt zero t,
  lt zero (plus t t).
Proof.
  intros t Ht. apply plus_positive; exact Ht.
Qed.

(* ===== 件 2（主结果）：恢复增益精确恒等式 =====
   ΔH := H(p_{t2}) − H(p_{t1}) == β₂·(E₂ − E₁) + KL(p_{t1} ‖ p_{t2})
   三行证明：KL 温度分解 + 熵显式 + 纯 AC 重排。 *)
Theorem recovery_entropy_gain : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  Id (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
     (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
           (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))).
Proof.
  intros t1 t2 Ht1 Ht2.
  unfold minus.
  set (b2 := inv_pos t2 Ht2).
  set (E1 := Et t1 Ht1). set (E2 := Et t2 Ht2).
  set (H1 := entropy_dist (Bt t1 Ht1)). set (H2 := entropy_dist (Bt t2 Ht2)).
  set (K := relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)).
  set (L2 := log (Z_temp t2)).
  (* 熵显式：H2 == b2·E2 + L2 *)
  assert (Hex2 : Id H2 (plus (mult b2 E2) L2))
    by exact (entropy_temp_explicit base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2).
  (* KL 温度分解：K == (−H1 + b2·E1) + L2
     （energy_expectation (Bt t1) 定义性 == E1，fw_energy_eta 同 id_refl） *)
  assert (Hkl : Id K (plus (plus (opp H1) (mult b2 E1)) L2)).
  { apply (id_trans (relative_entropy_temp_decomp base_loss sum_over_S_pos Z_temp Z_temp_spec
                                  t2 Ht2 (Bt t1 Ht1)
                                  (boltzmann_dist_temp_normalized base_loss sum_over_S_pos
                                     Z_temp Z_temp_spec t1 Ht1))).
    apply (id_cong (fun x => plus (plus (opp H1) (mult b2 x)) L2)).
    apply fw_energy_eta. }
  (* 差的左分配：b2·(E2−E1) == b2·E2 + −(b2·E1) *)
  assert (Hd : Id (mult b2 (minus E2 E1)) (plus (mult b2 E2) (opp (mult b2 E1)))).
  { apply (id_trans (mult_minus_distr_l b2 E2 E1)).
    unfold minus. apply id_refl. }
  (* 主代数链（纯 AC）：
     b2(E2−E1) + ((−H1+b2E1)+L2) == (b2E2 + −(b2E1)) + ((−H1+b2E1)+L2)
       == b2E2 + ((−(b2E1)) + ((−H1+b2E1)+L2))
       == b2E2 + ((−(b2E1)) + (b2E1 + (−H1+L2)))
       == b2E2 + ((−(b2E1) + b2E1) + (−H1+L2))
       == b2E2 + (−H1+L2)
       == (b2E2 + L2) + −H1 == H2 + −H1 *)
  assert (Hrot : forall aX : R,
    Id (plus (plus (opp H1) aX) L2) (plus aX (plus (opp H1) L2))).
  { intros aX.
    apply (id_trans (id_sym (plus_assoc (opp H1) aX L2))).
    apply (id_trans (id_cong (fun w => plus (opp H1) w) (plus_comm aX L2))).
    apply (id_trans (plus_assoc (opp H1) L2 aX)).
    apply (plus_comm (plus (opp H1) L2) aX). }
  assert (Hchain : Id (plus (mult b2 (minus E2 E1)) (plus (plus (opp H1) (mult b2 E1)) L2))
                      (plus H2 (opp H1))).
  { apply (id_trans (id_cong (fun x => plus x (plus (plus (opp H1) (mult b2 E1)) L2)) Hd)).
    apply (id_trans (id_sym (plus_assoc (mult b2 E2) (opp (mult b2 E1))
                                        (plus (plus (opp H1) (mult b2 E1)) L2)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) (plus (opp (mult b2 E1)) w))
                             (Hrot (mult b2 E1)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) w)
                             (plus_assoc (opp (mult b2 E1)) (mult b2 E1)
                                         (plus (opp H1) L2)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) (plus w (plus (opp H1) L2)))
                             (id_trans (plus_comm (opp (mult b2 E1)) (mult b2 E1))
                                       (plus_opp (mult b2 E1))))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) w)
                             (plus_comm zero (plus (opp H1) L2)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) w)
                             (plus_zero (plus (opp H1) L2)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) w) (plus_comm (opp H1) L2))).
    apply (id_trans (plus_assoc (mult b2 E2) L2 (opp H1))).
    apply (id_cong (fun w => plus w (opp H1)) (id_sym Hex2)). }
  apply (id_sym (id_trans (id_cong (fun x => plus (mult b2 (minus E2 E1)) x) Hkl) Hchain)).
Qed.

(* ===== 件 1（主结果）：温度-熵单调 =====
   t1 < t2 ⟹ H(p_{t1}) ≤ H(p_{t2})。
   路径：能量单调（根）+ 件 2 恒等式 + KL ≥ 0（根 Gibbs）。 *)
Theorem entropy_temp_mono : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  lt t1 t2 -> le (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t2 Ht2)).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt.
  (* E1 ≤ E2（根 主定理 energy_exp_temp_mono） *)
  assert (HdE : le zero (minus (Et t2 Ht2) (Et t1 Ht1))).
  { apply le_minus_nonneg.
    exact (energy_exp_temp_mono base_loss sum_over_S_pos inv_pos_lt_compat
             lt_minus_nonneg Z_temp Z_temp_spec t1 t2 Ht1 Ht2 Hlt). }
  (* KL(p_{t1} ‖ p_{t2}) ≥ 0（根 Gibbs 不等式） *)
  assert (Hkl : le zero (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))).
  { apply (gibbs_inequality (Bt t1 Ht1) (Bt t2 Ht2)).
    - exact (boltzmann_dist_temp_normalized base_loss sum_over_S_pos Z_temp Z_temp_spec t1 Ht1).
    - intros s. exact (boltzmann_dist_temp_pos base_loss sum_over_S_pos Z_temp Z_temp_spec t1 Ht1 s).
    - exact (boltzmann_dist_temp_normalized base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2).
    - intros s. exact (boltzmann_dist_temp_pos base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2 s). }
  (* β₂ > 0 ⟹ β₂·ΔE ≥ 0 *)
  assert (Hb2 : le zero (inv_pos t2 Ht2)).
  { apply (lt_le_iff _ _). left. exact (inv_pos_pos t2 Ht2). }
  assert (Hterm : le zero (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))).
  { apply (le_id_l zero (mult (inv_pos t2 Ht2) zero)
                     (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))).
    - exact (id_sym (mult_zero (inv_pos t2 Ht2))).
    - exact (le_mult_compat_r (inv_pos t2 Ht2) zero (minus (Et t2 Ht2) (Et t1 Ht1)) Hb2 HdE). }
  (* 两非负项相加 ≥ 0 *)
  assert (Hsum : le zero (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                               (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))))
    by exact (le_trans zero (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                        (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                              (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)))
                        Hterm
                        (le_plus_nonneg_r (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                                          (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)) Hkl)).
  (* 件 2 恒等式迁移：ΔH ≥ 0 *)
  assert (Hfin : le zero (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))).
  { apply (le_id_r zero (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                              (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)))).
    - exact (id_sym (recovery_entropy_gain t1 t2 Ht1 Ht2)).
    - exact Hsum. }
  (* H1 + ΔH == H2（minus_plus_cancel）⟹ H1 ≤ H2 *)
  apply (le_id_r (entropy_dist (Bt t1 Ht1))
                 (plus (entropy_dist (Bt t1 Ht1))
                       (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1))))
                 (entropy_dist (Bt t2 Ht2))).
  - exact (minus_plus_cancel (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t2 Ht2))).
  - exact (le_plus_nonneg_r (entropy_dist (Bt t1 Ht1))
                            (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1))) Hfin).
Qed.

(* ===== 件 2 严格档：升温 ⟹ 熵严格恢复 =====
   显式条件（根 同款）：KL(p_{t2} ‖ p_{t1}) > 0
   （分布非平凡时满足；KL 退化为零仅当两温度分布逐点相同）。
   路径：根 energy_exp_temp_strict_mono 给 ΔE > 0 ⟹ β₂ΔE > 0，
   加 KL ≥ 0 后由件 2 恒等式迁移。 *)
Theorem entropy_temp_strict_mono : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  lt t1 t2 ->
  lt zero (relative_entropy (Bt t2 Ht2) (Bt t1 Ht1)) ->
  lt (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t2 Ht2)).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hkl12.
  assert (HdE : lt zero (minus (Et t2 Ht2) (Et t1 Ht1)))
    by exact (energy_exp_temp_strict_mono base_loss sum_over_S_pos inv_pos_lt_compat
                lt_minus_nonneg Z_temp Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hkl12).
  assert (Hterm : lt zero (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1))))
    by exact (mult_positive (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1))
                            (inv_pos_pos t2 Ht2) HdE).
  assert (Hkl21 : le zero (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))).
  { apply (gibbs_inequality (Bt t1 Ht1) (Bt t2 Ht2)).
    - exact (boltzmann_dist_temp_normalized base_loss sum_over_S_pos Z_temp Z_temp_spec t1 Ht1).
    - intros s. exact (boltzmann_dist_temp_pos base_loss sum_over_S_pos Z_temp Z_temp_spec t1 Ht1 s).
    - exact (boltzmann_dist_temp_normalized base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2).
    - intros s. exact (boltzmann_dist_temp_pos base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2 s). }
  assert (Hsum : lt zero (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                               (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))))
    by exact (lt_le_trans zero (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                          (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                                (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)))
                          Hterm
                          (le_plus_nonneg_r (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                                            (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)) Hkl21)).
  assert (Hfin : lt zero (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1))))
    by exact (lt_id_r zero (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                                  (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)))
                       (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
                       (id_sym (recovery_entropy_gain t1 t2 Ht1 Ht2)) Hsum).
  apply (lt_id_r (entropy_dist (Bt t1 Ht1))
                 (plus (entropy_dist (Bt t1 Ht1))
                       (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1))))
                 (entropy_dist (Bt t2 Ht2))).
  - exact (minus_plus_cancel (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t2 Ht2))).
  - (* lt H1 (H1 + ΔH)：两侧各走一次 id_transport
       （zero + H1 ↦ H1；ΔH + H1 ↦ H1 + ΔH；接口 plus 抽象不可换形） *)
    apply (id_transport
             (fun w => lt w (plus (entropy_dist (Bt t1 Ht1))
                                  (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))))
             (id_trans (plus_comm zero (entropy_dist (Bt t1 Ht1)))
                       (plus_zero (entropy_dist (Bt t1 Ht1))))).
    apply (id_transport
             (fun w => lt (plus zero (entropy_dist (Bt t1 Ht1))) w)
             (plus_comm (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
                        (entropy_dist (Bt t1 Ht1)))).
    exact (lt_plus_compat_lt_le zero
                                (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
                                (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t1 Ht1))
                                Hfin (le_refl (entropy_dist (Bt t1 Ht1)))).
Qed.

(* ===== 件 2 对偶形态：对称 KL 联立 =====
   与根 temp_strict_ident2（(β₁−β₂)ΔE == K12 + K21）联立消 (β₁−β₂)ΔE：
   ΔH == β₁·ΔE − K12（K12 := KL(p_{t2} ‖ p_{t1})）。
   三个恢复量（ΔH, ΔE, KL 组合）的完整系数表到此闭合。 *)
Theorem recovery_entropy_gain_alt : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  Id (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
     (minus (mult (inv_pos t1 Ht1) (minus (Et t2 Ht2) (Et t1 Ht1)))
            (relative_entropy (Bt t2 Ht2) (Bt t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (dE := minus (Et t2 Ht2) (Et t1 Ht1)).
  set (K12 := relative_entropy (Bt t2 Ht2) (Bt t1 Ht1)).
  set (K21 := relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)).
  (* 对称 KL 恒等（根 temp_strict_ident2） *)
  assert (Hsym : Id (plus K12 K21) (mult (minus b1 b2) dE))
    by exact (temp_strict_ident2 base_loss sum_over_S_pos Z_temp Z_temp_spec t1 t2 Ht1 Ht2).
  (* b1 == b2 + (b1 − b2) *)
  assert (Hb1 : Id b1 (plus b2 (minus b1 b2))).
  { apply id_sym.
    apply (id_trans (plus_assoc b2 b1 (opp b2))).
    apply (id_trans (id_cong (fun w => plus w (opp b2)) (plus_comm b2 b1))).
    apply (id_trans (id_sym (plus_assoc b1 b2 (opp b2)))).
    apply (id_trans (id_cong (fun w => plus b1 w) (plus_opp b2))).
    apply (plus_zero b1). }
  (* 分配：b1·ΔE == b2·ΔE + (b1−b2)·ΔE *)
  assert (Hdistr : Id (mult b1 dE) (plus (mult b2 dE) (mult (minus b1 b2) dE))).
  { apply (id_trans (id_cong (fun w => mult w dE) Hb1)).
    apply (mult_plus_distr_r b2 (minus b1 b2) dE). }
  (* (b1−b2)·ΔE == K21 + K12（Hsym 对换） *)
  assert (Hsym' : Id (mult (minus b1 b2) dE) (plus K21 K12))
    by exact (id_trans (id_sym Hsym) (plus_comm K12 K21)).
  (* 减法消去：(K21 + K12) − K12 == K21 *)
  assert (Hcancel : Id (minus (plus K21 K12) K12) K21).
  { unfold minus.
    apply (id_trans (id_sym (plus_assoc K21 K12 (opp K12)))).
    apply (id_trans (id_cong (fun w => plus K21 w) (plus_opp K12))).
    apply (plus_zero K21). }
  (* 组装：ΔH == b2ΔE + K21（件 2）
       == (b2ΔE + (K21+K12)) − K12 == (b2ΔE + (b1−b2)ΔE) − K12 == b1ΔE − K12 *)
  assert (Hstep1 : Id (plus (mult b2 dE) K21)
                      (minus (plus (mult b2 dE) (plus K21 K12)) K12)).
  { apply (id_trans (id_cong (fun w => plus (mult b2 dE) w) (id_sym Hcancel))).
    apply (plus_assoc (mult b2 dE) (plus K21 K12) (opp K12)). }
  assert (Hstep2 : Id (minus (plus (mult b2 dE) (plus K21 K12)) K12)
                      (minus (mult b1 dE) K12)).
  { apply (id_cong (fun w => minus w K12)
                   (id_sym (id_trans Hdistr
                     (id_cong (fun w => plus (mult b2 dE) w) Hsym')))). }
  apply (id_trans (recovery_entropy_gain t1 t2 Ht1 Ht2)).
  exact (id_trans Hstep1 Hstep2).
Qed.

(* ===== 件 3：闭环封装（证书形态状态机） =====

   fw_verdict：健康判定 = Or 证书和（Set 层，非布尔判定器）
     - inl：健康证书 —— 熵过阈值 H_min 的 le 证书；
     - inr：退化报告 —— 量化缺口的 sigT 单元素类型（gap 恒等于
       当前熵 − H_min 的差值，携带"还差多少"的可提取实数）。
       （注意层级：Or 的分支是类型不是项——实数本身不能作分支，
         须经 sigT 单元素类型承载。）
   firewall_loop：闭环转移 —— 任一判定 ⟹ sigT 见证后继温度
     （健康：驻留 t' := t；退化：倍温 t' := t + t），
     携带转移证书（温度不降 + 熵不降 + 判定重装）。
   显式边界：单轮迭代不宣称"恢复健康"——退化支的重装判定
     仍是 inr（新一轮缺口报告）；健康与否由下一轮 fw_verdict
     证书回答。循环不变量 = 温度不降 ∧ 熵不降（件 1/2 供给）。 *)

Definition fw_verdict (Hmin : R) (t : R) (Ht : lt zero t) : Set :=
  Or (le Hmin (entropy_dist (Bt t Ht)))
     (sigT (fun gap : R => Id gap (minus (entropy_dist (Bt t Ht)) Hmin))).

(* 检测-升温响应：退化报告 ⟹ sigT 见证升温目标 t' := t + t
   与恢复证书（熵不降 + 增量精确分解 = 件 2 恒等式） *)
Theorem fw_detect_warm : forall (Hmin : R) (t : R) (Ht : lt zero t)
                                (Hdef : sigT (fun gap : R =>
                                          Id gap (minus (entropy_dist (Bt t Ht)) Hmin))),
  sigT (fun t' => sigT (fun Ht' : lt zero t' =>
    And (lt t t')
        (And (le (entropy_dist (Bt t Ht)) (entropy_dist (Bt t' Ht')))
             (Id (minus (entropy_dist (Bt t' Ht')) (entropy_dist (Bt t Ht)))
                 (plus (mult (inv_pos t' Ht') (minus (Et t' Ht') (Et t Ht)))
                       (relative_entropy (Bt t Ht) (Bt t' Ht'))))))).
Proof.
  intros Hmin t Ht Hdef.
  assert (Ht' : lt zero (plus t t)) by exact (fw_double_pos t Ht).
  assert (Hup : lt t (plus t t)) by exact (fw_lt_double t Ht).
  exists (plus t t). exists Ht'.
  split.
  - exact Hup.
  - split.
    + exact (entropy_temp_mono t (plus t t) Ht Ht' Hup).
    + exact (recovery_entropy_gain t (plus t t) Ht Ht').
Qed.

(* 闭环主定理：任一判定 ⟹ sigT 后继状态
   （温度不降 ∧ 熵不降 ∧ 判定重装）——逐轮可重复应用的
   证书状态机转移；健康支驻留、退化支倍温。 *)
Theorem firewall_loop : forall (Hmin : R) (t : R) (Ht : lt zero t)
                              (v : fw_verdict Hmin t Ht),
  sigT (fun t' => sigT (fun Ht' : lt zero t' =>
    And (le t t')
        (And (le (entropy_dist (Bt t Ht)) (entropy_dist (Bt t' Ht')))
             (fw_verdict Hmin t' Ht')))).
Proof.
  intros Hmin t Ht v. destruct v as [Hok | Hdef].
  - (* 健康支：驻留 *)
    exists t. exists Ht.
    split.
    + apply le_refl.
    + split.
      * apply le_refl.
      * left. exact Hok.
  - (* 退化支：倍温 t' := t + t，熵恢复（件 1），判定重装（显式：仍 inr） *)
    assert (Ht' : lt zero (plus t t)) by exact (fw_double_pos t Ht).
    assert (Hup : lt t (plus t t)) by exact (fw_lt_double t Ht).
    exists (plus t t). exists Ht'.
    split.
    + apply (lt_le_iff _ _). left. exact Hup.
    + split.
      * exact (entropy_temp_mono t (plus t t) Ht Ht' Hup).
      * right. exact (existT _ (minus (entropy_dist (Bt (plus t t) Ht')) Hmin) id_refl).
Qed.

End FirewallLoop.

(* ============ 提取检验（可执行 OCaml，验收关卡） ============ *)
Set Warnings "-extraction-opaque-accessed".
