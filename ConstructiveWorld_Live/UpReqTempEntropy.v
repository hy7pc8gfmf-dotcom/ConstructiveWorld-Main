(* UpReqTempEntropy.v — 温度熵层 5 件 req 化（批 2 余件收口，任务批 3 前置）
   母本：签名迁移规划书-20260908.md 批 2 余件 (a)；基座 Id 原件：
     entropy_temp_explicit        <- CW219 L17271（熵显式 H(p_β)==β·E+logZ）
     relative_entropy_temp_decomp <- CW219 L17356（KL(q‖p_β)==−H(q)+β·E(q)+logZ）
     entropy_deficit_kl_temp      <- CW219 L17691（同能量 ⟹ S[p_β]−S[p]==KL）
     max_entropy_is_boltzmann_temp<- CW219 L17726（同能量 ⟹ S[p]≤S[p_β]）
     entropy_max_unique_temp      <- CW219 L17763（同能量同熵 ⟹ p==p_β 逐点）
   依赖件（全部 UpReqDist.v ReqTemp/ReqFEP 节闭合形，-Q . "" 直接消费）：
     req_Z_temp_pos / reqd_boltzmann_dist_temp / reqd_energy_exp_temp /
     reqd_boltzmann_dist_temp_normalized / reqd_boltzmann_dist_temp_pos(Defined) /
     reqd_boltzmann_log_temp_decomp + FEP 求和面 fsum_ext/add/linear/pos/le/
     zero_nonneg + 接口桥 dist_log_inv_one_inv / dist_log_exp_neg /
     dist_log_le_linear / dist_log_eq_linear + req_entropy_neg_sum +
     req_gibbs_inequality / req_gibbs_equality。
   方法（批 2 卡坑 5）：预平衡原子项程序化拼接——两侧各拆为逐项命名的
     预平衡原子项（逐项 exact），再 req_trans 按序闭合；零 rewrite。
   纪律：纯构造性；Set 层语句（req/lt/le 均 Set 值，零 Prop 泄露）；
     纯 term-mode（req_trans 链 + compat 桥）；log 前提逐位携带正性证明
     （正性证明 proof-relevant，批 2 卡坑 7——一律用 Defined 正性件
     tBpos/tZpos（δ 透明别名）保证与 decomp 的前提字面一致）。
   命名对齐注记：req_entropy_deficit_temp（本文件/任务名）＝批 2 台账
     req_entropy_deficit_kl_temp＝Id entropy_deficit_kl_temp（L17691）。 *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section ReqTempEntropy：温度熵层消费面                        *)
(*   节参数 = ReqFEP 求和面/接口桥 + ReqTemp 的 Z_temp 接口      *)
(*   （不含固定温度 D/Z/partition——温度层只依赖 Z_temp）。       *)
(* ============================================================ *)
Section ReqTempEntropy.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis fsum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis fsum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis fsum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis fsum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis fsum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis fsum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero ->
    forall s : S, req (f s) zero.
Variable base_loss : S -> R.
Hypothesis dist_log_inv_one_inv :
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis dist_log_exp_neg :
  forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis dist_log_le_linear :
  forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one).
Hypothesis dist_log_eq_linear :
  forall (x : R) (Hx : lt zero x),
    req (log x Hx) (req_minus x one) -> req x one.
Variable Z_temp : R -> R.
Hypothesis Z_temp_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

(* ---- 温度族透明别名（δ 可达；正性/归一化一律取 Defined 正件，   ---- *)
(* ---- 与 reqd_boltzmann_log_temp_decomp 的 log 前提字面一致）    ---- *)
Definition tB (t : R) (Ht : lt zero t) : S -> R :=
  reqd_boltzmann_dist_temp S sumf fsum_pos base_loss Z_temp Z_temp_spec t Ht.
Definition tE (t : R) (Ht : lt zero t) : R :=
  reqd_energy_exp_temp S sumf fsum_pos base_loss Z_temp Z_temp_spec t Ht.
Definition tBpos (t : R) (Ht : lt zero t) : reqd_positive_dist S (tB t Ht) :=
  reqd_boltzmann_dist_temp_pos S sumf fsum_pos base_loss Z_temp Z_temp_spec t Ht.
Definition tBnorm (t : R) (Ht : lt zero t) : reqd_normalized S sumf (tB t Ht) :=
  reqd_boltzmann_dist_temp_normalized S sumf fsum_linear fsum_pos
    base_loss Z_temp Z_temp_spec t Ht.
Definition tZpos (t : R) (Ht : lt zero t) : lt zero (Z_temp t) :=
  req_Z_temp_pos S sumf fsum_pos base_loss Z_temp Z_temp_spec t Ht.

(* ============================================================ *)
(* 件 1/5：温度熵显式（Id entropy_temp_explicit @17271）         *)
(*   H(p_β) == β·E(p_β) + log Z_t。逐点 p·(−log p) == p·(βe)+p·logZ *)
(*   （decomp 换形 + opp_plus/双否定 + distrib + 交换），Σ 层     *)
(*   fsum_ext + fsum_add + β 提取（逐点交换/结合 + fsum_linear）  *)
(*   + logZ 常数提取（交换 + fsum_linear + 归一化 + mult_one）。  *)
(* ============================================================ *)
Theorem req_entropy_temp_explicit :
  forall (t : R) (Ht : lt zero t),
    req (reqd_entropy_dist S sumf (tB t Ht) (tBpos t Ht))
        (plus (mult (inv_pos t Ht) (tE t Ht))
              (log (Z_temp t) (tZpos t Ht))).
Proof.
  intros t Ht.
  set (bta := inv_pos t Ht).
  set (LZ := log (Z_temp t) (tZpos t Ht)).
  set (p := tB t Ht).
  set (Hp := tBpos t Ht).
  unfold reqd_entropy_dist.
  (* 主链：Σ p·(−log p) == Σ (p·βe + p·logZ) == β·Σ p·e + logZ *)
  apply (req_trans
    (sumf (fun s : S => mult (p s) (opp (log (p s) (Hp s)))))
    (sumf (fun s : S => plus (mult (p s) (mult bta (base_loss s)))
                             (mult (p s) LZ)))
    (plus (mult bta (tE t Ht)) LZ)).
  - (* 逐点换形 Σ 层入口 *)
    apply (fsum_ext
      (fun s : S => mult (p s) (opp (log (p s) (Hp s))))
      (fun s : S => plus (mult (p s) (mult bta (base_loss s))) (mult (p s) LZ))).
    intro s.
    apply (req_trans
      (mult (p s) (opp (log (p s) (Hp s))))
      (mult (p s) (plus LZ (mult bta (base_loss s))))
      (plus (mult (p s) (mult bta (base_loss s))) (mult (p s) LZ))).
    + (* 步 A：−log p == logZ + βe（decomp + opp_plus + 双否定×2） *)
      apply (req_trans
        (mult (p s) (opp (log (p s) (Hp s))))
        (mult (p s) (opp (plus (opp LZ) (opp (mult bta (base_loss s))))))
        (mult (p s) (plus LZ (mult bta (base_loss s))))).
      * exact (req_mult_compat (p s) (p s)
                 (opp (log (p s) (Hp s)))
                 (opp (plus (opp LZ) (opp (mult bta (base_loss s)))))
                 (req_refl (p s))
                 (req_opp_compat (log (p s) (Hp s))
                                 (plus (opp LZ) (opp (mult bta (base_loss s))))
                                 (reqd_boltzmann_log_temp_decomp S sumf fsum_pos
                                    base_loss dist_log_inv_one_inv dist_log_exp_neg
                                    Z_temp Z_temp_spec t Ht s))).
      * apply (req_trans
          (mult (p s) (opp (plus (opp LZ) (opp (mult bta (base_loss s))))))
          (mult (p s) (plus (opp (opp LZ)) (opp (opp (mult bta (base_loss s))))))
          (mult (p s) (plus LZ (mult bta (base_loss s))))).
        -- exact (req_mult_compat (p s) (p s)
                     (opp (plus (opp LZ) (opp (mult bta (base_loss s)))))
                     (plus (opp (opp LZ)) (opp (opp (mult bta (base_loss s)))))
                     (req_refl (p s))
                     (req_opp_plus (opp LZ) (opp (mult bta (base_loss s))))).
        -- exact (req_mult_compat (p s) (p s)
                     (plus (opp (opp LZ)) (opp (opp (mult bta (base_loss s)))))
                     (plus LZ (mult bta (base_loss s)))
                     (req_refl (p s))
                     (req_plus_compat (opp (opp LZ)) LZ
                                      (opp (opp (mult bta (base_loss s))))
                                      (mult bta (base_loss s))
                                      (req_double_neg LZ)
                                      (req_double_neg (mult bta (base_loss s))))).
    + (* 步 B：p·(logZ+βe) == p·βe + p·logZ（distrib + plus_comm） *)
      apply (req_trans
        (mult (p s) (plus LZ (mult bta (base_loss s))))
        (plus (mult (p s) LZ) (mult (p s) (mult bta (base_loss s))))
        (plus (mult (p s) (mult bta (base_loss s))) (mult (p s) LZ))).
      * exact (distrib (p s) LZ (mult bta (base_loss s))).
      * exact (plus_comm (mult (p s) LZ) (mult (p s) (mult bta (base_loss s)))).
  - (* Σ 层：fsum_add + β 提取 + logZ 常数提取 *)
    apply (req_trans
      (sumf (fun s : S => plus (mult (p s) (mult bta (base_loss s)))
                               (mult (p s) LZ)))
      (plus (sumf (fun s : S => mult (p s) (mult bta (base_loss s))))
            (sumf (fun s : S => mult (p s) LZ)))
      (plus (mult bta (tE t Ht)) LZ)).
    + exact (fsum_add
               (fun s : S => mult (p s) (mult bta (base_loss s)))
               (fun s : S => mult (p s) LZ)).
    + apply (req_plus_compat
               (sumf (fun s : S => mult (p s) (mult bta (base_loss s))))
               (mult bta (tE t Ht))
               (sumf (fun s : S => mult (p s) LZ))
               LZ).
      * (* β 提取：Σ p·(βe) == β·Σ p·e（逐点交换/结合 + fsum_linear） *)
        apply (req_trans
          (sumf (fun s : S => mult (p s) (mult bta (base_loss s))))
          (sumf (fun s : S => mult bta (mult (p s) (base_loss s))))
          (mult bta (tE t Ht))).
        -- apply (fsum_ext
              (fun s : S => mult (p s) (mult bta (base_loss s)))
              (fun s : S => mult bta (mult (p s) (base_loss s)))).
           intro s.
           apply (req_trans
             (mult (p s) (mult bta (base_loss s)))
             (mult (mult bta (base_loss s)) (p s))
             (mult bta (mult (p s) (base_loss s)))).
           ++ exact (mult_comm (p s) (mult bta (base_loss s))).
           ++ apply (req_trans
                (mult (mult bta (base_loss s)) (p s))
                (mult bta (mult (base_loss s) (p s)))
                (mult bta (mult (p s) (base_loss s)))).
              ** exact (req_sym (mult bta (mult (base_loss s) (p s)))
                                (mult (mult bta (base_loss s)) (p s))
                                (mult_assoc bta (base_loss s) (p s))).
              ** exact (req_mult_compat bta bta
                          (mult (base_loss s) (p s))
                          (mult (p s) (base_loss s))
                          (req_refl bta) (mult_comm (base_loss s) (p s))).
        -- exact (fsum_linear bta (fun s : S => mult (p s) (base_loss s))).
      * (* logZ 常数提取：Σ p·logZ == logZ·Σ p == logZ *)
        apply (req_trans
          (sumf (fun s : S => mult (p s) LZ))
          (sumf (fun s : S => mult LZ (p s)))
          LZ).
        -- apply (fsum_ext (fun s : S => mult (p s) LZ)
                           (fun s : S => mult LZ (p s))).
           intro s. exact (mult_comm (p s) LZ).
        -- apply (req_trans
              (sumf (fun s : S => mult LZ (p s)))
              (mult LZ (sumf p))
              LZ).
           ++ exact (fsum_linear LZ p).
           ++ apply (req_trans (mult LZ (sumf p)) (mult LZ one) LZ).
              ** exact (req_mult_compat LZ LZ (sumf p) one
                          (req_refl LZ) (tBnorm t Ht)).
              ** exact (mult_one LZ).
Qed.

(* ============================================================ *)
(* 件 2/5：相对熵温度分解（Id relative_entropy_temp_decomp @17356） *)
(*   KL(q‖p_β) == −H(q) + β·E(q) + log Z_t（q 归一化）。          *)
(*   req_minus 展开 + 逐点 distrib；Σ q·log q == −H(q)           *)
(*   （req_entropy_neg_sum 运输）；Σ q·log p_β == −β·E(q) − logZ  *)
(*   （decomp 逐点 + 交换 + distrib + opp_mult_l + β 提取 +       *)
(*   logZ 常数提取）；组装 fsum_add/fsum_opp + opp_plus/双否定 +  *)
(*   plus_assoc。                                                *)
(* ============================================================ *)
Theorem req_relative_entropy_temp_decomp :
  forall (t : R) (Ht : lt zero t) (q : S -> R) (Hq : reqd_positive_dist S q),
    reqd_normalized S sumf q ->
    req (req_relative_entropy S sumf q (tB t Ht) Hq (tBpos t Ht))
        (plus (plus (opp (reqd_entropy_dist S sumf q Hq))
                    (mult (inv_pos t Ht)
                          (reqd_energy_expectation S sumf base_loss q)))
              (log (Z_temp t) (tZpos t Ht))).
Proof.
  intros t Ht q Hq Hnq.
  set (bta := inv_pos t Ht).
  set (LZ := log (Z_temp t) (tZpos t Ht)).
  set (pB := tB t Ht).
  set (HpB := tBpos t Ht).
  set (Hq0 := reqd_entropy_dist S sumf q Hq).
  set (Eq := reqd_energy_expectation S sumf base_loss q).
  unfold req_relative_entropy, req_minus.
  (* 预平衡原子项 P2：q·(βe) == β·(q·e)（交换/结合重排） *)
  assert (P2 : forall s : S,
    req (mult (q s) (mult bta (base_loss s))) (mult bta (mult (q s) (base_loss s)))).
  { intro s.
    apply (req_trans
      (mult (q s) (mult bta (base_loss s)))
      (mult (mult bta (base_loss s)) (q s))
      (mult bta (mult (q s) (base_loss s)))).
    - exact (mult_comm (q s) (mult bta (base_loss s))).
    - apply (req_trans
        (mult (mult bta (base_loss s)) (q s))
        (mult bta (mult (base_loss s) (q s)))
        (mult bta (mult (q s) (base_loss s)))).
      + exact (req_sym (mult bta (mult (base_loss s) (q s)))
                       (mult (mult bta (base_loss s)) (q s))
                       (mult_assoc bta (base_loss s) (q s))).
      + exact (req_mult_compat bta bta
                 (mult (base_loss s) (q s)) (mult (q s) (base_loss s))
                 (req_refl bta) (mult_comm (base_loss s) (q s))). }
  (* 预平衡原子项 Hcz：Σ q·logZ == logZ（常数提取 + 归一化） *)
  assert (Hcz : req (sumf (fun s : S => mult (q s) LZ)) LZ).
  { apply (req_trans
      (sumf (fun s : S => mult (q s) LZ))
      (sumf (fun s : S => mult LZ (q s)))
      LZ).
    - apply (fsum_ext (fun s : S => mult (q s) LZ) (fun s : S => mult LZ (q s))).
      intro s. exact (mult_comm (q s) LZ).
    - apply (req_trans
        (sumf (fun s : S => mult LZ (q s)))
        (mult LZ (sumf q))
        LZ).
      + exact (fsum_linear LZ q).
      + apply (req_trans (mult LZ (sumf q)) (mult LZ one) LZ).
        * exact (req_mult_compat LZ LZ (sumf q) one (req_refl LZ) Hnq).
        * exact (mult_one LZ). }
  (* 预平衡原子项 HlogH：Σ q·log p_β == opp(β·E(q)) + opp(logZ) *)
  assert (HlogH : req (sumf (fun s : S => mult (q s) (log (pB s) (HpB s))))
                      (plus (opp (mult bta Eq)) (opp LZ))).
  { apply (req_trans
      (sumf (fun s : S => mult (q s) (log (pB s) (HpB s))))
      (sumf (fun s : S => plus (opp (mult (q s) (mult bta (base_loss s))))
                               (opp (mult (q s) LZ))))
      (plus (opp (mult bta Eq)) (opp LZ))).
    - (* 逐点：q·log p_β == opp(q·βe) + opp(q·logZ) *)
      apply (fsum_ext
        (fun s : S => mult (q s) (log (pB s) (HpB s)))
        (fun s : S => plus (opp (mult (q s) (mult bta (base_loss s))))
                           (opp (mult (q s) LZ)))).
      intro s.
      apply (req_trans
        (mult (q s) (log (pB s) (HpB s)))
        (mult (q s) (plus (opp LZ) (opp (mult bta (base_loss s)))))
        (plus (opp (mult (q s) (mult bta (base_loss s)))) (opp (mult (q s) LZ)))).
      + (* decomp 换形 *)
        exact (req_mult_compat (q s) (q s)
                 (log (pB s) (HpB s))
                 (plus (opp LZ) (opp (mult bta (base_loss s))))
                 (req_refl (q s))
                 (reqd_boltzmann_log_temp_decomp S sumf fsum_pos base_loss
                    dist_log_inv_one_inv dist_log_exp_neg
                    Z_temp Z_temp_spec t Ht s)).
      + (* 剩余四步：交换 + distrib + opp_mult_l ×2 *)
        apply (req_trans
          (mult (q s) (plus (opp LZ) (opp (mult bta (base_loss s)))))
          (mult (q s) (plus (opp (mult bta (base_loss s))) (opp LZ)))
          (plus (opp (mult (q s) (mult bta (base_loss s)))) (opp (mult (q s) LZ)))).
        * exact (req_mult_compat (q s) (q s)
                   (plus (opp LZ) (opp (mult bta (base_loss s))))
                   (plus (opp (mult bta (base_loss s))) (opp LZ))
                   (req_refl (q s))
                   (plus_comm (opp LZ) (opp (mult bta (base_loss s))))).
        * apply (req_trans
            (mult (q s) (plus (opp (mult bta (base_loss s))) (opp LZ)))
            (plus (mult (q s) (opp (mult bta (base_loss s))))
                  (mult (q s) (opp LZ)))
            (plus (opp (mult (q s) (mult bta (base_loss s)))) (opp (mult (q s) LZ)))).
          -- exact (distrib (q s) (opp (mult bta (base_loss s))) (opp LZ)).
          -- apply (req_trans
               (plus (mult (q s) (opp (mult bta (base_loss s)))) (mult (q s) (opp LZ)))
               (plus (opp (mult (q s) (mult bta (base_loss s)))) (mult (q s) (opp LZ)))
               (plus (opp (mult (q s) (mult bta (base_loss s)))) (opp (mult (q s) LZ)))).
             ++ exact (req_plus_compat
                         (mult (q s) (opp (mult bta (base_loss s))))
                         (opp (mult (q s) (mult bta (base_loss s))))
                         (mult (q s) (opp LZ))
                         (mult (q s) (opp LZ))
                         (req_opp_mult_l (q s) (mult bta (base_loss s)))
                         (req_refl (mult (q s) (opp LZ)))).
             ++ exact (req_plus_compat
                         (opp (mult (q s) (mult bta (base_loss s))))
                         (opp (mult (q s) (mult bta (base_loss s))))
                         (mult (q s) (opp LZ))
                         (opp (mult (q s) LZ))
                         (req_refl (opp (mult (q s) (mult bta (base_loss s)))))
                         (req_opp_mult_l (q s) LZ)).
    - (* Σ 层：fsum_add + 两支各归位 *)
      apply (req_trans
        (sumf (fun s : S => plus (opp (mult (q s) (mult bta (base_loss s))))
                                 (opp (mult (q s) LZ))))
        (plus (sumf (fun s : S => opp (mult (q s) (mult bta (base_loss s)))))
              (sumf (fun s : S => opp (mult (q s) LZ))))
        (plus (opp (mult bta Eq)) (opp LZ))).
      + exact (fsum_add
                 (fun s : S => opp (mult (q s) (mult bta (base_loss s))))
                 (fun s : S => opp (mult (q s) LZ))).
      + apply (req_plus_compat
                 (sumf (fun s : S => opp (mult (q s) (mult bta (base_loss s)))))
                 (opp (mult bta Eq))
                 (sumf (fun s : S => opp (mult (q s) LZ)))
                 (opp LZ)).
        * exact (req_trans
                   (sumf (fun s : S => opp (mult (q s) (mult bta (base_loss s)))))
                   (sumf (fun s : S => opp (mult bta (mult (q s) (base_loss s)))))
                   (opp (mult bta Eq))
                   (fsum_ext
                      (fun s : S => opp (mult (q s) (mult bta (base_loss s))))
                      (fun s : S => opp (mult bta (mult (q s) (base_loss s))))
                      (fun s : S => req_opp_compat
                                      (mult (q s) (mult bta (base_loss s)))
                                      (mult bta (mult (q s) (base_loss s)))
                                      (P2 s)))
                   (req_trans
                      (sumf (fun s : S => opp (mult bta (mult (q s) (base_loss s)))))
                      (opp (sumf (fun s : S => mult bta (mult (q s) (base_loss s)))))
                      (opp (mult bta Eq))
                      (fsum_opp S sumf fsum_ext fsum_linear
                         (fun s : S => mult bta (mult (q s) (base_loss s))))
                      (req_opp_compat
                         (sumf (fun s : S => mult bta (mult (q s) (base_loss s))))
                         (mult bta Eq)
                         (fsum_linear bta (fun s : S => mult (q s) (base_loss s)))))).
        * exact (req_trans
                   (sumf (fun s : S => opp (mult (q s) LZ)))
                   (opp (sumf (fun s : S => mult (q s) LZ)))
                   (opp LZ)
                   (fsum_opp S sumf fsum_ext fsum_linear (fun s : S => mult (q s) LZ))
                   (req_opp_compat (sumf (fun s : S => mult (q s) LZ)) LZ Hcz)). }
  (* 预平衡原子项 Hopp：opp(opp X + opp Y) == X + Y *)
  assert (Hopp : req (opp (plus (opp (mult bta Eq)) (opp LZ))) (plus (mult bta Eq) LZ)).
  { exact (req_trans
             (opp (plus (opp (mult bta Eq)) (opp LZ)))
             (plus (opp (opp (mult bta Eq))) (opp (opp LZ)))
             (plus (mult bta Eq) LZ)
             (req_opp_plus (opp (mult bta Eq)) (opp LZ))
             (req_plus_compat (opp (opp (mult bta Eq))) (mult bta Eq)
                              (opp (opp LZ)) LZ
                              (req_double_neg (mult bta Eq))
                              (req_double_neg LZ))). }
  (* 主链组装 *)
  apply (req_trans
    (sumf (fun s : S => mult (q s)
                              (plus (log (q s) (Hq s)) (opp (log (pB s) (HpB s))))))
    (sumf (fun s : S => plus (mult (q s) (log (q s) (Hq s)))
                             (mult (q s) (opp (log (pB s) (HpB s))))))
    (plus (plus (opp Hq0) (mult bta Eq)) LZ)).
  - apply (fsum_ext
      (fun s : S => mult (q s)
                         (plus (log (q s) (Hq s)) (opp (log (pB s) (HpB s)))))
      (fun s : S => plus (mult (q s) (log (q s) (Hq s)))
                         (mult (q s) (opp (log (pB s) (HpB s)))))).
    intro s.
    exact (distrib (q s) (log (q s) (Hq s)) (opp (log (pB s) (HpB s)))).
  - apply (req_trans
      (sumf (fun s : S => plus (mult (q s) (log (q s) (Hq s)))
                               (mult (q s) (opp (log (pB s) (HpB s))))))
      (plus (sumf (fun s : S => mult (q s) (log (q s) (Hq s))))
            (opp (sumf (fun s : S => mult (q s) (log (pB s) (HpB s))))))
      (plus (plus (opp Hq0) (mult bta Eq)) LZ)).
    + exact (req_trans
               (sumf (fun s : S => plus (mult (q s) (log (q s) (Hq s)))
                                        (mult (q s) (opp (log (pB s) (HpB s))))))
               (plus (sumf (fun s : S => mult (q s) (log (q s) (Hq s))))
                     (sumf (fun s : S => mult (q s) (opp (log (pB s) (HpB s))))))
               (plus (sumf (fun s : S => mult (q s) (log (q s) (Hq s))))
                     (opp (sumf (fun s : S => mult (q s) (log (pB s) (HpB s))))))
               (fsum_add (fun s : S => mult (q s) (log (q s) (Hq s)))
                         (fun s : S => mult (q s) (opp (log (pB s) (HpB s)))))
               (req_plus_compat
                  (sumf (fun s : S => mult (q s) (log (q s) (Hq s))))
                  (sumf (fun s : S => mult (q s) (log (q s) (Hq s))))
                  (sumf (fun s : S => mult (q s) (opp (log (pB s) (HpB s)))))
                  (opp (sumf (fun s : S => mult (q s) (log (pB s) (HpB s)))))
                  (req_refl (sumf (fun s : S => mult (q s) (log (q s) (Hq s)))))
                  (req_trans
                     (sumf (fun s : S => mult (q s) (opp (log (pB s) (HpB s)))))
                     (sumf (fun s : S => opp (mult (q s) (log (pB s) (HpB s)))))
                     (opp (sumf (fun s : S => mult (q s) (log (pB s) (HpB s)))))
                     (fsum_ext
                        (fun s : S => mult (q s) (opp (log (pB s) (HpB s))))
                        (fun s : S => opp (mult (q s) (log (pB s) (HpB s))))
                        (fun s : S => req_opp_mult_l (q s) (log (pB s) (HpB s))))
                     (fsum_opp S sumf fsum_ext fsum_linear
                        (fun s : S => mult (q s) (log (pB s) (HpB s))))))).
    + apply (req_trans
        (plus (sumf (fun s : S => mult (q s) (log (q s) (Hq s))))
              (opp (sumf (fun s : S => mult (q s) (log (pB s) (HpB s))))))
        (plus (opp Hq0) (opp (plus (opp (mult bta Eq)) (opp LZ))))
        (plus (plus (opp Hq0) (mult bta Eq)) LZ)).
      * apply (req_plus_compat
                 (sumf (fun s : S => mult (q s) (log (q s) (Hq s))))
                 (opp Hq0)
                 (opp (sumf (fun s : S => mult (q s) (log (pB s) (HpB s)))))
                 (opp (plus (opp (mult bta Eq)) (opp LZ)))).
        -- exact (req_entropy_neg_sum S sumf fsum_ext fsum_linear q Hq).
        -- exact (req_opp_compat
                    (sumf (fun s : S => mult (q s) (log (pB s) (HpB s))))
                    (plus (opp (mult bta Eq)) (opp LZ))
                    HlogH).
      * exact (req_trans
                 (plus (opp Hq0) (opp (plus (opp (mult bta Eq)) (opp LZ))))
                 (plus (opp Hq0) (plus (mult bta Eq) LZ))
                 (plus (plus (opp Hq0) (mult bta Eq)) LZ)
                 (req_plus_compat (opp Hq0) (opp Hq0)
                                  (opp (plus (opp (mult bta Eq)) (opp LZ)))
                                  (plus (mult bta Eq) LZ)
                                  (req_refl (opp Hq0)) Hopp)
                 (plus_assoc (opp Hq0) (mult bta Eq) LZ)).
Qed.

(* ============================================================ *)
(* 件 3/5：熵亏损温度版（Id entropy_deficit_kl_temp @17691；      *)
(*   批 2 台账名 req_entropy_deficit_kl_temp）。                  *)
(*   同约束能量 E(p) == E(p_β) ⟹ S[p_β] − S[p] == KL(p‖p_β)。    *)
(*   链：KL 分解（件 2）+ 熵显式（件 1）+ 结合/交换重排 +         *)
(*   同能量替换（β·E(p) ↦ β·E(p_β)，req_mult_compat）+            *)
(*   req_minus 展开后 Hse 正向 / Hsub 反向闭合。                  *)
(* ============================================================ *)
Theorem req_entropy_deficit_temp :
  forall (t : R) (Ht : lt zero t) (p : S -> R) (Hp : reqd_positive_dist S p),
    reqd_normalized S sumf p ->
    req (reqd_energy_expectation S sumf base_loss p) (tE t Ht) ->
    req (req_minus (reqd_entropy_dist S sumf (tB t Ht) (tBpos t Ht))
                   (reqd_entropy_dist S sumf p Hp))
        (req_relative_entropy S sumf p (tB t Ht) Hp (tBpos t Ht)).
Proof.
  intros t Ht p Hp Hnp Henergy.
  set (bta := inv_pos t Ht).
  set (LZ := log (Z_temp t) (tZpos t Ht)).
  set (Sp := reqd_entropy_dist S sumf p Hp).
  set (Spt := reqd_entropy_dist S sumf (tB t Ht) (tBpos t Ht)).
  set (K := req_relative_entropy S sumf p (tB t Ht) Hp (tBpos t Ht)).
  set (Ep := reqd_energy_expectation S sumf base_loss p).
  (* KL(p‖p_β) == −S[p] + β·E(p) + logZ（件 2） *)
  assert (Hkl : req K (plus (plus (opp Sp) (mult bta Ep)) LZ))
    by exact (req_relative_entropy_temp_decomp t Ht p Hp Hnp).
  (* S[p_β] == β·E(p_β) + logZ（件 1） *)
  assert (Hse : req Spt (plus (mult bta (tE t Ht)) LZ))
    by exact (req_entropy_temp_explicit t Ht).
  (* 重排：K == (β·E(p) + logZ) + (−S[p]) *)
  assert (Hkl' : req K (plus (plus (mult bta Ep) LZ) (opp Sp))).
  { exact (req_trans K
             (plus (opp Sp) (plus (mult bta Ep) LZ))
             (plus (plus (mult bta Ep) LZ) (opp Sp))
             (req_trans K
                (plus (plus (opp Sp) (mult bta Ep)) LZ)
                (plus (opp Sp) (plus (mult bta Ep) LZ))
                Hkl
                (req_sym (plus (opp Sp) (plus (mult bta Ep) LZ))
                         (plus (plus (opp Sp) (mult bta Ep)) LZ)
                         (plus_assoc (opp Sp) (mult bta Ep) LZ)))
             (plus_comm (opp Sp) (plus (mult bta Ep) LZ))). }
  (* 同能量替换：β·E(p) ↦ β·E(p_β) *)
  assert (Hsub : req K (plus (plus (mult bta (tE t Ht)) LZ) (opp Sp))).
  { exact (req_trans K
             (plus (plus (mult bta Ep) LZ) (opp Sp))
             (plus (plus (mult bta (tE t Ht)) LZ) (opp Sp))
             Hkl'
             (req_plus_compat (plus (mult bta Ep) LZ)
                              (plus (mult bta (tE t Ht)) LZ)
                              (opp Sp) (opp Sp)
                              (req_plus_compat (mult bta Ep)
                                               (mult bta (tE t Ht))
                                               LZ LZ
                                               (req_mult_compat bta bta Ep (tE t Ht)
                                                                (req_refl bta) Henergy)
                                               (req_refl LZ))
                              (req_refl (opp Sp)))). }
  (* 目标：S[p_β] − S[p] == K（req_minus 展开 + Hse 正向 / Hsub 反向） *)
  unfold req_minus.
  apply (req_trans (plus Spt (opp Sp))
                   (plus (plus (mult bta (tE t Ht)) LZ) (opp Sp))
                   K).
  - exact (req_plus_compat Spt (plus (mult bta (tE t Ht)) LZ)
                           (opp Sp) (opp Sp)
                           Hse (req_refl (opp Sp))).
  - exact (req_sym K (plus (plus (mult bta (tE t Ht)) LZ) (opp Sp)) Hsub).
Qed.

(* ============================================================ *)
(* 件 4/5：最大熵=Boltzmann 温度版                                *)
(*   （Id max_entropy_is_boltzmann_temp @17726）。                *)
(*   同约束能量 ⟹ S[p] ≤ S[p_β]。组装：熵亏（件 3）+              *)
(*   req_gibbs_inequality（p 与 p_β 均归一化）+ le 移项链          *)
(*   （le_id_r + req_minus_plus_cancel + req_le_plus_nonneg_r）。 *)
(* ============================================================ *)
Theorem req_max_entropy_is_boltzmann_temp :
  forall (t : R) (Ht : lt zero t) (p : S -> R) (Hp : reqd_positive_dist S p),
    reqd_normalized S sumf p ->
    req (reqd_energy_expectation S sumf base_loss p) (tE t Ht) ->
    le (reqd_entropy_dist S sumf p Hp)
       (reqd_entropy_dist S sumf (tB t Ht) (tBpos t Ht)).
Proof.
  intros t Ht p Hp Hnp Henergy.
  set (Sp := reqd_entropy_dist S sumf p Hp).
  set (Spt := reqd_entropy_dist S sumf (tB t Ht) (tBpos t Ht)).
  set (K := req_relative_entropy S sumf p (tB t Ht) Hp (tBpos t Ht)).
  (* 1. S[p_β] − S[p] == KL（件 3） *)
  assert (Hdef : req (req_minus Spt Sp) K)
    by exact (req_entropy_deficit_temp t Ht p Hp Hnp Henergy).
  (* 2. KL ≥ 0（req_gibbs_inequality；p_β 归一化 = reqd_boltzmann_dist_temp_normalized） *)
  assert (Hkl : le zero K).
  { exact (req_gibbs_inequality S sumf fsum_ext fsum_add fsum_linear fsum_le
                                dist_log_inv_one_inv dist_log_le_linear
                                p (tB t Ht) Hp (tBpos t Ht) Hnp (tBnorm t Ht)). }
  (* 3. 0 ≤ S[p_β] − S[p] ⟹ S[p] ≤ S[p_β] *)
  assert (Hnonneg : le zero (req_minus Spt Sp))
    by exact (le_id_r zero K (req_minus Spt Sp) (req_sym _ _ Hdef) Hkl).
  apply (le_id_r Sp (plus Sp (req_minus Spt Sp)) Spt).
  - exact (req_minus_plus_cancel Sp Spt).
  - exact (req_le_plus_nonneg_r Sp (req_minus Spt Sp) Hnonneg).
Qed.

(* ============================================================ *)
(* 件 5/5：唯一性温度版（Id entropy_max_unique_temp @17763）。     *)
(*   同约束能量 + 同熵 ⟹ p == p_β 逐点。组装：熵亏（件 3）+        *)
(*   同熵 ⟹ KL == 0（req_minus_self_zero）+                      *)
(*   req_gibbs_equality（KL == 0 ⟹ 逐点相等）。                   *)
(* ============================================================ *)
Theorem req_entropy_max_unique_temp :
  forall (t : R) (Ht : lt zero t) (p : S -> R) (Hp : reqd_positive_dist S p),
    reqd_normalized S sumf p ->
    req (reqd_energy_expectation S sumf base_loss p) (tE t Ht) ->
    req (reqd_entropy_dist S sumf p Hp)
        (reqd_entropy_dist S sumf (tB t Ht) (tBpos t Ht)) ->
    forall s : S, req (p s) (tB t Ht s).
Proof.
  intros t Ht p Hp Hnp Henergy Hent s.
  set (Sp := reqd_entropy_dist S sumf p Hp).
  set (Spt := reqd_entropy_dist S sumf (tB t Ht) (tBpos t Ht)).
  set (K := req_relative_entropy S sumf p (tB t Ht) Hp (tBpos t Ht)).
  (* 1. S[p_β] − S[p] == KL（件 3） *)
  assert (Hdef : req (req_minus Spt Sp) K)
    by exact (req_entropy_deficit_temp t Ht p Hp Hnp Henergy).
  (* 2. 等熵 ⟹ KL == 0 *)
  assert (Hkl0 : req K zero).
  { exact (req_trans K (req_minus Spt Sp) zero
             (req_sym _ _ Hdef)
             (req_minus_self_zero Spt Sp (req_sym _ _ Hent))). }
  (* 3. gibbs_equality：KL == 0 ⟹ p == p_β 逐点 *)
  exact (req_gibbs_equality S sumf fsum_ext fsum_add fsum_linear fsum_zero_nonneg
                            dist_log_inv_one_inv dist_log_le_linear
                            dist_log_eq_linear
                            p (tB t Ht) Hp (tBpos t Ht) Hnp (tBnorm t Ht) Hkl0 s).
Qed.

(* ============================================================ *)
(* 温度严格层增量节（批 2 挂账 5+1 件，第三席续建 2026-09-09）    *)
(*   基座坐标（Id 原件，CW219 ConstructiveWorld_Live 主副本）：   *)
(*     variational_temp_bound         @L17468                    *)
(*     energy_exp_temp_mono           @L17521                    *)
(*     temp_energy_dual_closed        @L17788（sigT 形）         *)
(*     temp_strict_A_chain2           @L17825                    *)
(*     temp_strict_ident2             @L17879                    *)
(*     energy_exp_temp_strict_mono    @L18019                    *)
(*   组装路线（照 UpReqDist.v 尾注判词）：消费件 1（熵显式）+     *)
(*   件 2（KL 温度分解）+ UpReqDist.ReqAlgBridge2 移项链           *)
(*   （req_le_plus_cancel_l 系/req_le_mult_pos_cancel/            *)
(*   req_le_minus_nonneg_rev/req_mult_minus_distr_r/              *)
(*   reqd_lt_mult_pos_cancel/reqd_minus_compat）。                *)
(*   诚实假设位（Id 同位，逐位保留）：                            *)
(*     a) Id L17119 inv_pos_lt_compat（Variable）——req 接口字段   *)
(*       闭包检查通过（inv_pos_pos/inv_pos_correct/lt_mult_compat），*)
(*       按 RestA 先例「放电」为定理 req_inv_pos_lt_contra，       *)
(*       不新增公理；                                             *)
(*     b) Id L17121 lt_minus_nonneg（Variable）——接口抽象层无     *)
(*       lt↔minus 连接字段（Real 层逐 eps 直构），不可放电；       *)
(*       在 mono/strict_mono 两件以显式前提                       *)
(*         lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))   *)
(*       逐位保留（Real 实例化下为定理，不放大主张）。            *)
(* ============================================================ *)

(* ---- 放电件：inv 反单调（Id L21013/L17119 同位 Variable 真证）---- *)
(*   链：inv b == (inv a·a)·inv b < (inv a·b)·inv b == inv a       *)
(*   （两端 inv_pos_correct/mult_one 吸收，中段 lt_mult_compat      *)
(*   两次 + req_lt_compat 交换运输）——RestA ralt_inv_pos_lt_contra  *)
(*   同款复刻，接口字段闭包内真证。                                *)
Lemma req_inv_pos_lt_contra :
  forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
    lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  set (ia := inv_pos a Ha).
  set (ib := inv_pos b Hb).
  assert (Hia1 : req (mult ia a) one).
  { exact (req_trans (mult ia a) (mult a ia) one
             (mult_comm ia a) (inv_pos_correct a Ha)). }
  assert (Hib1 : req (mult b ib) one).
  { exact (inv_pos_correct b Hb). }
  assert (Hmid : req (mult (mult ia a) ib) ib).
  { apply (req_trans (mult (mult ia a) ib) (mult one ib) ib).
    - exact (req_mult_compat (mult ia a) one ib ib Hia1 (req_refl ib)).
    - exact (req_trans (mult one ib) (mult ib one) ib
               (mult_comm one ib) (mult_one ib)). }
  assert (Hlt1 : lt (mult ia a) (mult ia b)).
  { apply (req_lt_compat (mult a ia) (mult ia a) (mult b ia) (mult ia b)
                         (mult_comm a ia) (mult_comm b ia)).
    exact (lt_mult_compat a b ia (inv_pos_pos a Ha) Hab). }
  assert (Hltmid : lt (mult (mult ia a) ib) (mult (mult ia b) ib)).
  { exact (lt_mult_compat (mult ia a) (mult ia b) ib
             (inv_pos_pos b Hb) Hlt1). }
  assert (Hright : req (mult (mult ia b) ib) ia).
  { apply (req_trans (mult (mult ia b) ib) (mult ia (mult b ib)) ia).
    - exact (req_sym (mult ia (mult b ib)) (mult (mult ia b) ib)
                     (mult_assoc ia b ib)).
    - apply (req_trans (mult ia (mult b ib)) (mult ia one) ia).
      + exact (req_mult_compat ia ia (mult b ib) one
                 (req_refl ia) Hib1).
      + exact (mult_one ia). }
  apply (lt_id_r ib (mult (mult ia b) ib) ia Hright).
  exact (lt_id_l ib (mult (mult ia a) ib) (mult (mult ia b) ib)
                   (req_sym (mult (mult ia a) ib) ib Hmid) Hltmid).
Qed.

(* ---- 代数助手：减法对 (x−y)+(y−x) == 0（纯接口代数真证） ---- *)
Lemma reqd_minus_pair_cancel :
  forall a b : R, req (plus (req_minus a b) (req_minus b a)) zero.
Proof.
  intros a b.
  apply (req_trans (plus (req_minus a b) (req_minus b a))
                   (plus a (plus (opp b) (plus b (opp a))))
                   zero).
  - exact (req_sym (plus a (plus (opp b) (plus b (opp a))))
                   (plus (plus a (opp b)) (plus b (opp a)))
                   (plus_assoc a (opp b) (plus b (opp a)))).
  - apply (req_trans (plus a (plus (opp b) (plus b (opp a))))
                     (plus a (plus (plus (opp b) b) (opp a)))
                     zero).
    + exact (req_plus_compat a a
               (plus (opp b) (plus b (opp a)))
               (plus (plus (opp b) b) (opp a))
               (req_refl a) (plus_assoc (opp b) b (opp a))).
    + apply (req_trans (plus a (plus (plus (opp b) b) (opp a)))
                       (plus a (plus zero (opp a)))
                       zero).
      * exact (req_plus_compat a a
                  (plus (plus (opp b) b) (opp a))
                  (plus zero (opp a))
                  (req_refl a)
                  (req_plus_compat (plus (opp b) b) zero (opp a) (opp a)
                     (req_trans (plus (opp b) b) (plus b (opp b)) zero
                        (plus_comm (opp b) b) (plus_opp b))
                     (req_refl (opp a)))).
      * apply (req_trans (plus a (plus zero (opp a)))
                         (plus a (opp a))
                         zero).
        -- exact (req_plus_compat a a (plus zero (opp a)) (opp a)
                    (req_refl a)
                    (req_trans (plus zero (opp a)) (plus (opp a) zero) (opp a)
                       (plus_comm zero (opp a)) (plus_zero (opp a)))).
        -- exact (plus_opp a).
Qed.

(* ---- 代数助手：减反 flip (b−a) == −(a−b)（纯接口代数真证） ---- *)
Lemma reqd_minus_opp_flip :
  forall a b : R, req (req_minus b a) (opp (req_minus a b)).
Proof.
  intros a b.
  apply (req_trans (plus b (opp a)) (plus (opp a) b)
                   (opp (plus a (opp b)))).
  - exact (plus_comm b (opp a)).
  - apply (req_trans (plus (opp a) b)
                     (plus (opp a) (opp (opp b)))
                     (opp (plus a (opp b)))).
    + exact (req_plus_compat (opp a) (opp a) b (opp (opp b))
               (req_refl (opp a)) (req_sym (opp (opp b)) b (req_double_neg b))).
    + exact (req_sym (opp (plus a (opp b))) (plus (opp a) (opp (opp b)))
                     (req_opp_plus a (opp b))).
Qed.

(* ============================================================ *)
(* 严格层件 1/6：KL 分解换形（Id temp_strict_A_chain2 @17825）    *)
(*   −S2 + b1·E2 + log Z1 == (b1−b2)·E2 + (log Z1 − log Z2)。     *)
(*   非平凡性：组装（件 1 熵显式）+ 真证代数链（opp_plus/双否定/  *)
(*   distrib/req_mult_minus_distr_r req 链，零 rewrite）。        *)
(* ============================================================ *)
Theorem req_temp_strict_A_chain2 :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
    req (plus (plus (opp (reqd_entropy_dist S sumf (tB t2 Ht2) (tBpos t2 Ht2)))
                    (mult (inv_pos t1 Ht1) (tE t2 Ht2)))
              (log (Z_temp t1) (tZpos t1 Ht1)))
        (plus (mult (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))
                    (tE t2 Ht2))
              (req_minus (log (Z_temp t1) (tZpos t1 Ht1))
                         (log (Z_temp t2) (tZpos t2 Ht2)))).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (b1 := inv_pos t1 Ht1).
  set (b2 := inv_pos t2 Ht2).
  set (E2 := tE t2 Ht2).
  set (S2 := reqd_entropy_dist S sumf (tB t2 Ht2) (tBpos t2 Ht2)).
  set (LZ1 := log (Z_temp t1) (tZpos t1 Ht1)).
  set (LZ2 := log (Z_temp t2) (tZpos t2 Ht2)).
  (* 熵显式（件 1）：S2 == b2·E2 + LZ2 *)
  assert (Hse : req S2 (plus (mult b2 E2) LZ2))
    by exact (req_entropy_temp_explicit t2 Ht2).
  (* 主链五段（Id H1/H2/H3/H4/H5 同构；id_cong → req compat 桥） *)
  assert (H1 : req (plus (plus (opp S2) (mult b1 E2)) LZ1)
                   (plus (plus (opp (plus (mult b2 E2) LZ2)) (mult b1 E2)) LZ1)).
  { exact (req_plus_compat
             (plus (opp S2) (mult b1 E2))
             (plus (opp (plus (mult b2 E2) LZ2)) (mult b1 E2))
             LZ1 LZ1
             (req_plus_compat (opp S2) (opp (plus (mult b2 E2) LZ2))
                              (mult b1 E2) (mult b1 E2)
                              (req_opp_compat S2 (plus (mult b2 E2) LZ2) Hse)
                              (req_refl (mult b1 E2)))
             (req_refl LZ1)). }
  assert (H2 : req (plus (plus (opp (plus (mult b2 E2) LZ2)) (mult b1 E2)) LZ1)
                   (plus (plus (plus (opp (mult b2 E2)) (opp LZ2)) (mult b1 E2)) LZ1)).
  { exact (req_plus_compat
             (plus (opp (plus (mult b2 E2) LZ2)) (mult b1 E2))
             (plus (plus (opp (mult b2 E2)) (opp LZ2)) (mult b1 E2))
             LZ1 LZ1
             (req_plus_compat (opp (plus (mult b2 E2) LZ2))
                              (plus (opp (mult b2 E2)) (opp LZ2))
                              (mult b1 E2) (mult b1 E2)
                              (req_opp_plus (mult b2 E2) LZ2)
                              (req_refl (mult b1 E2)))
             (req_refl LZ1)). }
  assert (H3 : req (plus (plus (plus (opp (mult b2 E2)) (opp LZ2)) (mult b1 E2)) LZ1)
                   (plus (plus (opp (mult b2 E2)) (mult b1 E2))
                         (plus (opp LZ2) LZ1))).
  { apply (req_trans
             (plus (plus (plus (opp (mult b2 E2)) (opp LZ2)) (mult b1 E2)) LZ1)
             (plus (plus (opp (mult b2 E2)) (plus (opp LZ2) (mult b1 E2))) LZ1)
             (plus (plus (opp (mult b2 E2)) (mult b1 E2))
                   (plus (opp LZ2) LZ1))).
    - exact (req_plus_compat
               (plus (plus (opp (mult b2 E2)) (opp LZ2)) (mult b1 E2))
               (plus (opp (mult b2 E2)) (plus (opp LZ2) (mult b1 E2)))
               LZ1 LZ1
               (req_sym (plus (opp (mult b2 E2)) (plus (opp LZ2) (mult b1 E2)))
                        (plus (plus (opp (mult b2 E2)) (opp LZ2)) (mult b1 E2))
                        (plus_assoc (opp (mult b2 E2)) (opp LZ2) (mult b1 E2)))
               (req_refl LZ1)).
    - apply (req_trans
               (plus (plus (opp (mult b2 E2)) (plus (opp LZ2) (mult b1 E2))) LZ1)
               (plus (plus (opp (mult b2 E2)) (plus (mult b1 E2) (opp LZ2))) LZ1)
               (plus (plus (opp (mult b2 E2)) (mult b1 E2))
                     (plus (opp LZ2) LZ1))).
      + exact (req_plus_compat
                 (plus (opp (mult b2 E2)) (plus (opp LZ2) (mult b1 E2)))
                 (plus (opp (mult b2 E2)) (plus (mult b1 E2) (opp LZ2)))
                 LZ1 LZ1
                 (req_plus_compat (opp (mult b2 E2)) (opp (mult b2 E2))
                    (plus (opp LZ2) (mult b1 E2)) (plus (mult b1 E2) (opp LZ2))
                    (req_refl (opp (mult b2 E2)))
                    (plus_comm (opp LZ2) (mult b1 E2)))
                 (req_refl LZ1)).
      + apply (req_trans
                 (plus (plus (opp (mult b2 E2)) (plus (mult b1 E2) (opp LZ2))) LZ1)
                 (plus (plus (plus (opp (mult b2 E2)) (mult b1 E2)) (opp LZ2)) LZ1)
                 (plus (plus (opp (mult b2 E2)) (mult b1 E2))
                       (plus (opp LZ2) LZ1))).
        * exact (req_plus_compat
                   (plus (opp (mult b2 E2)) (plus (mult b1 E2) (opp LZ2)))
                   (plus (plus (opp (mult b2 E2)) (mult b1 E2)) (opp LZ2))
                   LZ1 LZ1
                   (plus_assoc (opp (mult b2 E2)) (mult b1 E2) (opp LZ2))
                   (req_refl LZ1)).
        * exact (req_sym
                   (plus (plus (opp (mult b2 E2)) (mult b1 E2))
                         (plus (opp LZ2) LZ1))
                   (plus (plus (plus (opp (mult b2 E2)) (mult b1 E2)) (opp LZ2))
                         LZ1)
                   (plus_assoc (plus (opp (mult b2 E2)) (mult b1 E2))
                               (opp LZ2) LZ1)). }
  assert (H4 : req (plus (plus (opp (mult b2 E2)) (mult b1 E2))
                         (plus (opp LZ2) LZ1))
                   (plus (mult (req_minus b1 b2) E2) (plus (opp LZ2) LZ1))).
  { exact (req_plus_compat
             (plus (opp (mult b2 E2)) (mult b1 E2))
             (mult (req_minus b1 b2) E2)
             (plus (opp LZ2) LZ1) (plus (opp LZ2) LZ1)
             (req_trans (plus (opp (mult b2 E2)) (mult b1 E2))
                        (plus (mult b1 E2) (opp (mult b2 E2)))
                        (mult (req_minus b1 b2) E2)
                        (plus_comm (opp (mult b2 E2)) (mult b1 E2))
                        (req_sym (mult (req_minus b1 b2) E2)
                                 (req_minus (mult b1 E2) (mult b2 E2))
                                 (req_mult_minus_distr_r b1 b2 E2)))
             (req_refl (plus (opp LZ2) LZ1))). }
  assert (H5 : req (plus (mult (req_minus b1 b2) E2) (plus (opp LZ2) LZ1))
                   (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))).
  { exact (req_plus_compat
             (mult (req_minus b1 b2) E2) (mult (req_minus b1 b2) E2)
             (plus (opp LZ2) LZ1) (req_minus LZ1 LZ2)
             (req_refl (mult (req_minus b1 b2) E2))
             (plus_comm (opp LZ2) LZ1)). }
  exact (req_trans
           (plus (plus (opp S2) (mult b1 E2)) LZ1)
           (plus (plus (opp (plus (mult b2 E2) LZ2)) (mult b1 E2)) LZ1)
           (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))
           H1
           (req_trans
              (plus (plus (opp (plus (mult b2 E2) LZ2)) (mult b1 E2)) LZ1)
              (plus (plus (plus (opp (mult b2 E2)) (opp LZ2)) (mult b1 E2)) LZ1)
              (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))
              H2
              (req_trans
                 (plus (plus (plus (opp (mult b2 E2)) (opp LZ2)) (mult b1 E2)) LZ1)
                 (plus (plus (opp (mult b2 E2)) (mult b1 E2))
                       (plus (opp LZ2) LZ1))
                 (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))
                 H3
                 (req_trans
                    (plus (plus (opp (mult b2 E2)) (mult b1 E2))
                          (plus (opp LZ2) LZ1))
                    (plus (mult (req_minus b1 b2) E2) (plus (opp LZ2) LZ1))
                    (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))
                    H4
                    H5)))).
Qed.

(* ============================================================ *)
(* 严格层件 2/6：变分界（Id variational_temp_bound @17468）       *)
(*   归一化正分布 q：H(q) − β·E(q) ≤ log Z_t。                    *)
(*   非平凡性：组装（件 2 KL 分解 + req_gibbs_inequality）+       *)
(*   真证移项链（le_id_l/le_id_r + le_plus_compat + 4 步代数链）。*)
(* ============================================================ *)
Theorem req_variational_temp_bound :
  forall (t : R) (Ht : lt zero t) (q : S -> R) (Hq : reqd_positive_dist S q),
    reqd_normalized S sumf q ->
    le (req_minus (reqd_entropy_dist S sumf q Hq)
                  (mult (inv_pos t Ht) (reqd_energy_expectation S sumf base_loss q)))
       (log (Z_temp t) (tZpos t Ht)).
Proof.
  intros t Ht q Hq Hnq.
  set (Sq := reqd_entropy_dist S sumf q Hq).
  set (bE := mult (inv_pos t Ht) (reqd_energy_expectation S sumf base_loss q)).
  set (LZ := log (Z_temp t) (tZpos t Ht)).
  (* KL(q‖p_t) ≥ 0（req_gibbs_inequality） *)
  assert (Hkl : le zero (req_relative_entropy S sumf q (tB t Ht) Hq (tBpos t Ht))).
  { exact (req_gibbs_inequality S sumf fsum_ext fsum_add fsum_linear fsum_le
             dist_log_inv_one_inv dist_log_le_linear
             q (tB t Ht) Hq (tBpos t Ht) Hnq (tBnorm t Ht)). }
  (* KL == (−H + βE) + logZ（件 2）并运输 *)
  assert (Hkl0 : le zero (plus (plus (opp Sq) bE) LZ)).
  { exact (le_id_r zero
             (req_relative_entropy S sumf q (tB t Ht) Hq (tBpos t Ht))
             (plus (plus (opp Sq) bE) LZ)
             (req_relative_entropy_temp_decomp t Ht q Hq Hnq)
             Hkl). }
  (* 移项 1：H ≤ βE + logZ *)
  assert (Hstep1 : le Sq (plus bE LZ)).
  { apply (le_id_l Sq (plus Sq zero)).
    - exact (req_sym (plus Sq zero) Sq (plus_zero Sq)).
    - apply (le_id_r (plus Sq zero)
               (plus Sq (plus (plus (opp Sq) bE) LZ)) (plus bE LZ)).
      + (* Sq + ((−Sq + βE) + LZ) == βE + LZ：4 步代数链 *)
        apply (req_trans (plus Sq (plus (plus (opp Sq) bE) LZ))
                         (plus (plus Sq (plus (opp Sq) bE)) LZ)
                         (plus bE LZ)).
        * exact (plus_assoc Sq (plus (opp Sq) bE) LZ).
        * apply (req_trans (plus (plus Sq (plus (opp Sq) bE)) LZ)
                           (plus (plus (plus Sq (opp Sq)) bE) LZ)
                           (plus bE LZ)).
          -- exact (req_plus_compat (plus Sq (plus (opp Sq) bE))
                       (plus (plus Sq (opp Sq)) bE) LZ LZ
                       (plus_assoc Sq (opp Sq) bE) (req_refl LZ)).
          -- apply (req_trans (plus (plus (plus Sq (opp Sq)) bE) LZ)
                              (plus (plus zero bE) LZ)
                              (plus bE LZ)).
             ++ exact (req_plus_compat (plus (plus Sq (opp Sq)) bE)
                         (plus zero bE) LZ LZ
                         (req_plus_compat (plus Sq (opp Sq)) zero bE bE
                            (plus_opp Sq) (req_refl bE))
                         (req_refl LZ)).
             ++ exact (req_plus_compat (plus zero bE) bE LZ LZ
                          (req_trans (plus zero bE) (plus bE zero) bE
                             (plus_comm zero bE) (plus_zero bE))
                          (req_refl LZ)).
      + exact (le_plus_compat Sq Sq zero (plus (plus (opp Sq) bE) LZ)
                 (le_refl Sq) Hkl0). }
  (* 移项 2：H − βE ≤ logZ *)
  apply (le_id_r (plus Sq (opp bE))
                 (plus (plus bE LZ) (opp bE)) LZ).
  - (* (βE + LZ) − βE == LZ：5 步代数链 *)
    apply (req_trans (plus (plus bE LZ) (opp bE))
                     (plus bE (plus LZ (opp bE)))
                     LZ).
    + exact (req_sym (plus bE (plus LZ (opp bE)))
                     (plus (plus bE LZ) (opp bE))
                     (plus_assoc bE LZ (opp bE))).
    + apply (req_trans (plus bE (plus LZ (opp bE)))
                       (plus bE (plus (opp bE) LZ))
                       LZ).
      * exact (req_plus_compat bE bE (plus LZ (opp bE)) (plus (opp bE) LZ)
                 (req_refl bE) (plus_comm LZ (opp bE))).
      * apply (req_trans (plus bE (plus (opp bE) LZ))
                         (plus (plus bE (opp bE)) LZ)
                         LZ).
        -- exact (plus_assoc bE (opp bE) LZ).
        -- apply (req_trans (plus (plus bE (opp bE)) LZ) (plus zero LZ) LZ).
           ++ exact (req_plus_compat (plus bE (opp bE)) zero LZ LZ
                       (plus_opp bE) (req_refl LZ)).
           ++ exact (req_trans (plus zero LZ) (plus LZ zero) LZ
                   (plus_comm zero LZ) (plus_zero LZ)).
  - exact (le_plus_compat Sq (plus bE LZ) (opp bE) (opp bE)
             Hstep1 (le_refl (opp bE))).
Qed.

(* ============================================================ *)
(* 严格层件 3/6：温度-期望能量单调（Id energy_exp_temp_mono @17521）*)
(*   t1 < t2 ⟹ E(t1) ≤ E(t2)。非平凡性：真证组装（放电件 Hb +    *)
(*   变分界 ×2 + 件 1 熵显式 + Id Hm/Hshift/Hsum/Hlhs 全链 req 复刻 *)
(*   + req_le_mult_pos_cancel/req_le_minus_nonneg_rev 移项链）。   *)
(*   诚实前提：lt zero (b1 − b2)（Id L17121 lt_minus_nonneg 同位， *)
(*   接口抽象层不可放电，Real 实例化下为定理）。                   *)
(* ============================================================ *)
Theorem req_energy_exp_temp_mono :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
    lt t1 t2 ->
    lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) ->
    le (tE t1 Ht1) (tE t2 Ht2).
Proof.
  intros t1 t2 Ht1 Ht2 Ht12 Hbd.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (E1 := tE t1 Ht1). set (E2 := tE t2 Ht2).
  set (S1 := reqd_entropy_dist S sumf (tB t1 Ht1) (tBpos t1 Ht1)).
  set (S2 := reqd_entropy_dist S sumf (tB t2 Ht2) (tBpos t2 Ht2)).
  set (LZ1 := log (Z_temp t1) (tZpos t1 Ht1)).
  set (LZ2 := log (Z_temp t2) (tZpos t2 Ht2)).
  (* β2 < β1（放电件） *)
  assert (Hb : lt b2 b1)
    by exact (req_inv_pos_lt_contra t1 t2 Ht1 Ht2 Ht12).
  (* 变分界 ×2（q := p_{t2} / p_{t1} 交叉） *)
  assert (Hv1 : le (req_minus S2 (mult b1 E2)) LZ1).
  { exact (req_variational_temp_bound t1 Ht1 (tB t2 Ht2) (tBpos t2 Ht2)
             (tBnorm t2 Ht2)). }
  assert (Hv2 : le (req_minus S1 (mult b2 E1)) LZ2).
  { exact (req_variational_temp_bound t2 Ht2 (tB t1 Ht1) (tBpos t1 Ht1)
             (tBnorm t1 Ht1)). }
  (* 熵显式（件 1）×2 *)
  assert (Hex1 : req S1 (plus (mult b1 E1) LZ1))
    by exact (req_entropy_temp_explicit t1 Ht1).
  assert (Hex2 : req S2 (plus (mult b2 E2) LZ2))
    by exact (req_entropy_temp_explicit t2 Ht2).
  (* 熵显式代入变分界（reqd_minus_compat 运输） *)
  assert (Hv1' : le (req_minus (plus (mult b2 E2) LZ2) (mult b1 E2)) LZ1).
  { apply (le_id_l (req_minus (plus (mult b2 E2) LZ2) (mult b1 E2))
                   (req_minus S2 (mult b1 E2)) LZ1).
    - exact (reqd_minus_compat (plus (mult b2 E2) LZ2) S2
               (mult b1 E2) (mult b1 E2)
               (req_sym S2 (plus (mult b2 E2) LZ2) Hex2)
               (req_refl (mult b1 E2))).
    - exact Hv1. }
  assert (Hv2' : le (req_minus (plus (mult b1 E1) LZ1) (mult b2 E1)) LZ2).
  { apply (le_id_l (req_minus (plus (mult b1 E1) LZ1) (mult b2 E1))
                   (req_minus S1 (mult b2 E1)) LZ2).
    - exact (reqd_minus_compat (plus (mult b1 E1) LZ1) S1
               (mult b2 E1) (mult b2 E1)
               (req_sym S1 (plus (mult b1 E1) LZ1) Hex1)
               (req_refl (mult b2 E1))).
    - exact Hv2. }
  (* minus 内化简（Id Hm1：X−Y == (b2−b1)·E2 + LZ2，5 步） *)
  assert (Hm1 : req (req_minus (plus (mult b2 E2) LZ2) (mult b1 E2))
                    (plus (mult (req_minus b2 b1) E2) LZ2)).
  { apply (req_trans (req_minus (plus (mult b2 E2) LZ2) (mult b1 E2))
                     (plus (mult b2 E2) (plus LZ2 (opp (mult b1 E2))))
                     (plus (mult (req_minus b2 b1) E2) LZ2)).
    - exact (req_sym (plus (mult b2 E2) (plus LZ2 (opp (mult b1 E2))))
                     (plus (plus (mult b2 E2) LZ2) (opp (mult b1 E2)))
                     (plus_assoc (mult b2 E2) LZ2 (opp (mult b1 E2)))).
    - apply (req_trans (plus (mult b2 E2) (plus LZ2 (opp (mult b1 E2))))
                       (plus (mult b2 E2) (plus (opp (mult b1 E2)) LZ2))
                       (plus (mult (req_minus b2 b1) E2) LZ2)).
      + exact (req_plus_compat (mult b2 E2) (mult b2 E2)
                 (plus LZ2 (opp (mult b1 E2))) (plus (opp (mult b1 E2)) LZ2)
                 (req_refl (mult b2 E2)) (plus_comm LZ2 (opp (mult b1 E2)))).
      + apply (req_trans (plus (mult b2 E2) (plus (opp (mult b1 E2)) LZ2))
                         (plus (plus (mult b2 E2) (opp (mult b1 E2))) LZ2)
                         (plus (mult (req_minus b2 b1) E2) LZ2)).
        * exact (plus_assoc (mult b2 E2) (opp (mult b1 E2)) LZ2).
        * exact (req_plus_compat
                   (plus (mult b2 E2) (opp (mult b1 E2)))
                   (mult (req_minus b2 b1) E2) LZ2 LZ2
                   (req_sym (mult (req_minus b2 b1) E2)
                            (req_minus (mult b2 E2) (mult b1 E2))
                            (req_mult_minus_distr_r b2 b1 E2))
                   (req_refl LZ2)). }
  assert (Hm2 : req (req_minus (plus (mult b1 E1) LZ1) (mult b2 E1))
                    (plus (mult (req_minus b1 b2) E1) LZ1)).
  { apply (req_trans (req_minus (plus (mult b1 E1) LZ1) (mult b2 E1))
                     (plus (mult b1 E1) (plus LZ1 (opp (mult b2 E1))))
                     (plus (mult (req_minus b1 b2) E1) LZ1)).
    - exact (req_sym (plus (mult b1 E1) (plus LZ1 (opp (mult b2 E1))))
                     (plus (plus (mult b1 E1) LZ1) (opp (mult b2 E1)))
                     (plus_assoc (mult b1 E1) LZ1 (opp (mult b2 E1)))).
    - apply (req_trans (plus (mult b1 E1) (plus LZ1 (opp (mult b2 E1))))
                       (plus (mult b1 E1) (plus (opp (mult b2 E1)) LZ1))
                       (plus (mult (req_minus b1 b2) E1) LZ1)).
      + exact (req_plus_compat (mult b1 E1) (mult b1 E1)
                 (plus LZ1 (opp (mult b2 E1))) (plus (opp (mult b2 E1)) LZ1)
                 (req_refl (mult b1 E1)) (plus_comm LZ1 (opp (mult b2 E1)))).
      + apply (req_trans (plus (mult b1 E1) (plus (opp (mult b2 E1)) LZ1))
                         (plus (plus (mult b1 E1) (opp (mult b2 E1))) LZ1)
                         (plus (mult (req_minus b1 b2) E1) LZ1)).
        * exact (plus_assoc (mult b1 E1) (opp (mult b2 E1)) LZ1).
        * exact (req_plus_compat
                   (plus (mult b1 E1) (opp (mult b2 E1)))
                   (mult (req_minus b1 b2) E1) LZ1 LZ1
                   (req_sym (mult (req_minus b1 b2) E1)
                            (req_minus (mult b1 E1) (mult b2 E1))
                            (req_mult_minus_distr_r b1 b2 E1))
                   (req_refl LZ1)). }
  (* 收口变分界（Id Hv1''/Hv2''） *)
  assert (Hv1'' : le (plus (mult (req_minus b2 b1) E2) LZ2) LZ1).
  { apply (le_id_l (plus (mult (req_minus b2 b1) E2) LZ2)
                   (req_minus (plus (mult b2 E2) LZ2) (mult b1 E2)) LZ1).
    - exact (req_sym (req_minus (plus (mult b2 E2) LZ2) (mult b1 E2))
                     (plus (mult (req_minus b2 b1) E2) LZ2) Hm1).
    - exact Hv1'. }
  assert (Hv2'' : le (plus (mult (req_minus b1 b2) E1) LZ1) LZ2).
  { apply (le_id_l (plus (mult (req_minus b1 b2) E1) LZ1)
                   (req_minus (plus (mult b1 E1) LZ1) (mult b2 E1)) LZ2).
    - exact (req_sym (req_minus (plus (mult b1 E1) LZ1) (mult b2 E1))
                     (plus (mult (req_minus b1 b2) E1) LZ1) Hm2).
    - exact Hv2'. }
  (* 移项（Id Hshift1/Hshift2：le X (LZ1−LZ2)） *)
  assert (Hshift1 : le (mult (req_minus b2 b1) E2) (req_minus LZ1 LZ2)).
  { apply (le_id_l (mult (req_minus b2 b1) E2)
                   (plus (plus (mult (req_minus b2 b1) E2) LZ2) (opp LZ2))
                   (req_minus LZ1 LZ2)).
    - apply (req_trans (mult (req_minus b2 b1) E2)
                       (plus (mult (req_minus b2 b1) E2) zero)
                       (plus (plus (mult (req_minus b2 b1) E2) LZ2) (opp LZ2))).
      + exact (req_sym (plus (mult (req_minus b2 b1) E2) zero)
                       (mult (req_minus b2 b1) E2)
                       (plus_zero (mult (req_minus b2 b1) E2))).
      + apply (req_trans (plus (mult (req_minus b2 b1) E2) zero)
                         (plus (mult (req_minus b2 b1) E2)
                               (plus LZ2 (opp LZ2)))
                         (plus (plus (mult (req_minus b2 b1) E2) LZ2)
                               (opp LZ2))).
        * exact (req_plus_compat (mult (req_minus b2 b1) E2)
                    (mult (req_minus b2 b1) E2) zero (plus LZ2 (opp LZ2))
                    (req_refl (mult (req_minus b2 b1) E2))
                    (req_sym (plus LZ2 (opp LZ2)) zero (plus_opp LZ2))).
        * exact (plus_assoc (mult (req_minus b2 b1) E2) LZ2 (opp LZ2)).
    - apply (le_id_r (plus (plus (mult (req_minus b2 b1) E2) LZ2) (opp LZ2))
                     (plus LZ1 (opp LZ2)) (req_minus LZ1 LZ2)).
      + exact (req_refl (plus LZ1 (opp LZ2))).
      + exact (le_plus_compat (plus (mult (req_minus b2 b1) E2) LZ2) LZ1
                 (opp LZ2) (opp LZ2) Hv1'' (le_refl (opp LZ2))). }
  assert (Hshift2 : le (mult (req_minus b1 b2) E1) (req_minus LZ2 LZ1)).
  { apply (le_id_l (mult (req_minus b1 b2) E1)
                   (plus (plus (mult (req_minus b1 b2) E1) LZ1) (opp LZ1))
                   (req_minus LZ2 LZ1)).
    - apply (req_trans (mult (req_minus b1 b2) E1)
                       (plus (mult (req_minus b1 b2) E1) zero)
                       (plus (plus (mult (req_minus b1 b2) E1) LZ1) (opp LZ1))).
      + exact (req_sym (plus (mult (req_minus b1 b2) E1) zero)
                       (mult (req_minus b1 b2) E1)
                       (plus_zero (mult (req_minus b1 b2) E1))).
      + apply (req_trans (plus (mult (req_minus b1 b2) E1) zero)
                         (plus (mult (req_minus b1 b2) E1)
                               (plus LZ1 (opp LZ1)))
                         (plus (plus (mult (req_minus b1 b2) E1) LZ1)
                               (opp LZ1))).
        * exact (req_plus_compat (mult (req_minus b1 b2) E1)
                    (mult (req_minus b1 b2) E1) zero (plus LZ1 (opp LZ1))
                    (req_refl (mult (req_minus b1 b2) E1))
                    (req_sym (plus LZ1 (opp LZ1)) zero (plus_opp LZ1))).
        * exact (plus_assoc (mult (req_minus b1 b2) E1) LZ1 (opp LZ1)).
    - apply (le_id_r (plus (plus (mult (req_minus b1 b2) E1) LZ1) (opp LZ1))
                     (plus LZ2 (opp LZ1)) (req_minus LZ2 LZ1)).
      + exact (req_refl (plus LZ2 (opp LZ1))).
      + exact (le_plus_compat (plus (mult (req_minus b1 b2) E1) LZ1) LZ2
                 (opp LZ1) (opp LZ1) Hv2'' (le_refl (opp LZ1))). }
  (* 相加 + 对消（reqd_minus_pair_cancel） *)
  assert (Hsum : le (plus (mult (req_minus b2 b1) E2) (mult (req_minus b1 b2) E1))
                   (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1))).
  { exact (le_plus_compat (mult (req_minus b2 b1) E2) (req_minus LZ1 LZ2)
             (mult (req_minus b1 b2) E1) (req_minus LZ2 LZ1)
             Hshift1 Hshift2). }
  assert (Hz : req (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1)) zero)
    by exact (reqd_minus_pair_cancel LZ1 LZ2).
  assert (Hoppm : req (req_minus b2 b1) (opp (req_minus b1 b2)))
    by exact (reqd_minus_opp_flip b1 b2).
  (* LHS 换形：d'·E2 + d·E1 == d·(E1 − E2)（Id Hlhs 五步） *)
  assert (Hlhs : req (plus (mult (req_minus b2 b1) E2) (mult (req_minus b1 b2) E1))
                     (mult (req_minus b1 b2) (req_minus E1 E2))).
  { apply (req_trans
             (plus (mult (req_minus b2 b1) E2) (mult (req_minus b1 b2) E1))
             (plus (mult (opp (req_minus b1 b2)) E2) (mult (req_minus b1 b2) E1))
             (mult (req_minus b1 b2) (req_minus E1 E2))).
    - exact (req_plus_compat (mult (req_minus b2 b1) E2)
               (mult (opp (req_minus b1 b2)) E2)
               (mult (req_minus b1 b2) E1) (mult (req_minus b1 b2) E1)
               (req_mult_compat (req_minus b2 b1) (opp (req_minus b1 b2))
                  E2 E2 Hoppm (req_refl E2))
               (req_refl (mult (req_minus b1 b2) E1))).
    - apply (req_trans
               (plus (mult (opp (req_minus b1 b2)) E2) (mult (req_minus b1 b2) E1))
               (plus (opp (mult (req_minus b1 b2) E2)) (mult (req_minus b1 b2) E1))
               (mult (req_minus b1 b2) (req_minus E1 E2))).
      + exact (req_plus_compat (mult (opp (req_minus b1 b2)) E2)
                 (opp (mult (req_minus b1 b2) E2))
                 (mult (req_minus b1 b2) E1) (mult (req_minus b1 b2) E1)
                 (req_opp_mult_r (req_minus b1 b2) E2)
                 (req_refl (mult (req_minus b1 b2) E1))).
      + apply (req_trans
                 (plus (opp (mult (req_minus b1 b2) E2)) (mult (req_minus b1 b2) E1))
                 (plus (mult (req_minus b1 b2) (opp E2)) (mult (req_minus b1 b2) E1))
                 (mult (req_minus b1 b2) (req_minus E1 E2))).
        * exact (req_plus_compat (opp (mult (req_minus b1 b2) E2))
                   (mult (req_minus b1 b2) (opp E2))
                   (mult (req_minus b1 b2) E1) (mult (req_minus b1 b2) E1)
                   (req_sym (mult (req_minus b1 b2) (opp E2))
                            (opp (mult (req_minus b1 b2) E2))
                            (req_opp_mult_l (req_minus b1 b2) E2))
                   (req_refl (mult (req_minus b1 b2) E1))).
        * apply (req_trans
                   (plus (mult (req_minus b1 b2) (opp E2))
                         (mult (req_minus b1 b2) E1))
                   (mult (req_minus b1 b2) (plus (opp E2) E1))
                   (mult (req_minus b1 b2) (req_minus E1 E2))).
          -- exact (req_sym
                      (mult (req_minus b1 b2) (plus (opp E2) E1))
                      (plus (mult (req_minus b1 b2) (opp E2))
                            (mult (req_minus b1 b2) E1))
                      (distrib (req_minus b1 b2) (opp E2) E1)).
          -- exact (req_mult_compat (req_minus b1 b2) (req_minus b1 b2)
                       (plus (opp E2) E1) (req_minus E1 E2)
                       (req_refl (req_minus b1 b2))
                       (plus_comm (opp E2) E1)). }
  (* 组装：d·(E1 − E2) ≤ 0（Id Hmain） *)
  assert (Hmain : le (mult (req_minus b1 b2) (req_minus E1 E2)) zero).
  { apply (le_id_l (mult (req_minus b1 b2) (req_minus E1 E2))
                   (plus (mult (req_minus b2 b1) E2)
                         (mult (req_minus b1 b2) E1)) zero).
    - exact (req_sym (plus (mult (req_minus b2 b1) E2)
                           (mult (req_minus b1 b2) E1))
                     (mult (req_minus b1 b2) (req_minus E1 E2)) Hlhs).
    - exact (le_id_r (plus (mult (req_minus b2 b1) E2)
                           (mult (req_minus b1 b2) E1))
                     (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1))
                     zero Hz Hsum). }
  (* 乘正消去 + 减法逆（ReqAlgBridge2 移项链） *)
  assert (Hcancel : le (req_minus E1 E2) zero).
  { apply (req_le_mult_pos_cancel (req_minus E1 E2) (req_minus b1 b2) Hbd).
    apply (le_id_l (mult (req_minus E1 E2) (req_minus b1 b2))
                   (mult (req_minus b1 b2) (req_minus E1 E2)) zero).
    - exact (mult_comm (req_minus E1 E2) (req_minus b1 b2)).
    - exact Hmain. }
  exact (req_le_minus_nonneg_rev E1 E2 Hcancel).
Qed.

(* ============================================================ *)
(* 严格层件 4/6：KL 分解相减恒等（Id temp_strict_ident2 @17879）  *)
(*   KL(p_{t2}‖p_{t1}) + KL(p_{t1}‖p_{t2}) == (b1−b2)·(E2 − E1)。 *)
(*   非平凡性：组装（件 2 + 严格层件 1 A_chain2 交叉）+ 真证代数链 *)
(*   （reqd_minus_pair_cancel/reqd_minus_opp_flip 助手 + Hmain2    *)
(*   五步 req 链 + 逐步 trans 重排），幂等 δ 段 req_refl 闭合。    *)
(* ============================================================ *)
Theorem req_temp_strict_ident2 :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
    req (plus (req_relative_entropy S sumf (tB t2 Ht2) (tB t1 Ht1)
                 (tBpos t2 Ht2) (tBpos t1 Ht1))
              (req_relative_entropy S sumf (tB t1 Ht1) (tB t2 Ht2)
                 (tBpos t1 Ht1) (tBpos t2 Ht2)))
        (mult (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))
              (req_minus (tE t2 Ht2) (tE t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (E1 := tE t1 Ht1). set (E2 := tE t2 Ht2).
  set (LZ1 := log (Z_temp t1) (tZpos t1 Ht1)).
  set (LZ2 := log (Z_temp t2) (tZpos t2 Ht2)).
  set (K1 := req_relative_entropy S sumf (tB t2 Ht2) (tB t1 Ht1)
               (tBpos t2 Ht2) (tBpos t1 Ht1)).
  set (K2 := req_relative_entropy S sumf (tB t1 Ht1) (tB t2 Ht2)
               (tBpos t1 Ht1) (tBpos t2 Ht2)).
  assert (HK1 : req K1 (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))).
  { exact (req_trans K1
             (plus (plus (opp (reqd_entropy_dist S sumf (tB t2 Ht2) (tBpos t2 Ht2)))
                         (mult (inv_pos t1 Ht1) (tE t2 Ht2)))
                   LZ1)
             (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))
             (req_relative_entropy_temp_decomp t1 Ht1 (tB t2 Ht2)
                (tBpos t2 Ht2) (tBnorm t2 Ht2))
             (req_temp_strict_A_chain2 t1 t2 Ht1 Ht2)). }
  assert (HK2 : req K2 (plus (mult (req_minus b2 b1) E1) (req_minus LZ2 LZ1))).
  { exact (req_trans K2
             (plus (plus (opp (reqd_entropy_dist S sumf (tB t1 Ht1) (tBpos t1 Ht1)))
                         (mult (inv_pos t2 Ht2) (tE t1 Ht1)))
                   LZ2)
             (plus (mult (req_minus b2 b1) E1) (req_minus LZ2 LZ1))
             (req_relative_entropy_temp_decomp t2 Ht2 (tB t1 Ht1)
                (tBpos t1 Ht1) (tBnorm t1 Ht1))
             (req_temp_strict_A_chain2 t2 t1 Ht2 Ht1)). }
  assert (Hsum : req (plus K1 K2)
                     (plus (plus (mult (req_minus b1 b2) E2)
                                 (req_minus LZ1 LZ2))
                           (plus (mult (req_minus b2 b1) E1)
                                 (req_minus LZ2 LZ1)))).
  { exact (req_plus_compat K1
             (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))
             K2
             (plus (mult (req_minus b2 b1) E1) (req_minus LZ2 LZ1))
             HK1 HK2). }
  assert (Hz : req (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1)) zero)
    by exact (reqd_minus_pair_cancel LZ1 LZ2).
  assert (Hoppm : req (req_minus b2 b1) (opp (req_minus b1 b2)))
    by exact (reqd_minus_opp_flip b1 b2).
  (* Hmain2：d·E2 + d'·E1 == d·(E2 − E1)（五步） *)
  assert (Hmain2 : req (plus (mult (req_minus b1 b2) E2)
                             (mult (req_minus b2 b1) E1))
                       (mult (req_minus b1 b2) (req_minus E2 E1))).
  { apply (req_trans
             (plus (mult (req_minus b1 b2) E2) (mult (req_minus b2 b1) E1))
             (plus (mult (req_minus b1 b2) E2) (mult (opp (req_minus b1 b2)) E1))
             (mult (req_minus b1 b2) (req_minus E2 E1))).
    - exact (req_plus_compat (mult (req_minus b1 b2) E2)
               (mult (req_minus b1 b2) E2)
               (mult (req_minus b2 b1) E1) (mult (opp (req_minus b1 b2)) E1)
               (req_refl (mult (req_minus b1 b2) E2))
               (req_mult_compat (req_minus b2 b1) (opp (req_minus b1 b2))
                  E1 E1 Hoppm (req_refl E1))).
    - apply (req_trans
               (plus (mult (req_minus b1 b2) E2) (mult (opp (req_minus b1 b2)) E1))
               (plus (mult (req_minus b1 b2) E2) (opp (mult (req_minus b1 b2) E1)))
               (mult (req_minus b1 b2) (req_minus E2 E1))).
      + exact (req_plus_compat (mult (req_minus b1 b2) E2)
                 (mult (req_minus b1 b2) E2)
                 (mult (opp (req_minus b1 b2)) E1)
                 (opp (mult (req_minus b1 b2) E1))
                 (req_refl (mult (req_minus b1 b2) E2))
                 (req_opp_mult_r (req_minus b1 b2) E1)).
      + apply (req_trans
                 (plus (mult (req_minus b1 b2) E2)
                       (opp (mult (req_minus b1 b2) E1)))
                 (plus (mult (req_minus b1 b2) E2)
                       (mult (req_minus b1 b2) (opp E1)))
                 (mult (req_minus b1 b2) (req_minus E2 E1))).
        * exact (req_plus_compat (mult (req_minus b1 b2) E2)
                   (mult (req_minus b1 b2) E2)
                   (opp (mult (req_minus b1 b2) E1))
                   (mult (req_minus b1 b2) (opp E1))
                   (req_refl (mult (req_minus b1 b2) E2))
                   (req_sym (mult (req_minus b1 b2) (opp E1))
                            (opp (mult (req_minus b1 b2) E1))
                            (req_opp_mult_l (req_minus b1 b2) E1))).
        * apply (req_trans
                   (plus (mult (req_minus b1 b2) E2)
                         (mult (req_minus b1 b2) (opp E1)))
                   (mult (req_minus b1 b2) (plus E2 (opp E1)))
                   (mult (req_minus b1 b2) (req_minus E2 E1))).
          -- exact (req_sym
                      (mult (req_minus b1 b2) (plus E2 (opp E1)))
                      (plus (mult (req_minus b1 b2) E2)
                            (mult (req_minus b1 b2) (opp E1)))
                      (distrib (req_minus b1 b2) E2 (opp E1))).
          -- exact (req_mult_compat (req_minus b1 b2) (req_minus b1 b2)
                       (plus E2 (opp E1)) (req_minus E2 E1)
                       (req_refl (req_minus b1 b2))
                       (req_refl (plus E2 (opp E1)))). }
  assert (H1 : req (plus (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))
                         (plus (mult (req_minus b2 b1) E1) (req_minus LZ2 LZ1)))
                   (plus (mult (req_minus b1 b2) E2)
                         (plus (req_minus LZ1 LZ2)
                               (plus (mult (req_minus b2 b1) E1)
                                     (req_minus LZ2 LZ1))))).
  { exact (req_sym
             (plus (mult (req_minus b1 b2) E2)
                   (plus (req_minus LZ1 LZ2)
                         (plus (mult (req_minus b2 b1) E1)
                               (req_minus LZ2 LZ1))))
             (plus (plus (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2))
                   (plus (mult (req_minus b2 b1) E1) (req_minus LZ2 LZ1)))
             (plus_assoc (mult (req_minus b1 b2) E2) (req_minus LZ1 LZ2)
                         (plus (mult (req_minus b2 b1) E1)
                               (req_minus LZ2 LZ1)))). }
  assert (H2 : req (plus (mult (req_minus b1 b2) E2)
                         (plus (req_minus LZ1 LZ2)
                               (plus (mult (req_minus b2 b1) E1)
                                     (req_minus LZ2 LZ1))))
                   (plus (mult (req_minus b1 b2) E2)
                         (plus (mult (req_minus b2 b1) E1)
                               (plus (req_minus LZ1 LZ2)
                                     (req_minus LZ2 LZ1))))).
  { apply (req_trans
             (plus (mult (req_minus b1 b2) E2)
                   (plus (req_minus LZ1 LZ2)
                         (plus (mult (req_minus b2 b1) E1)
                               (req_minus LZ2 LZ1))))
             (plus (mult (req_minus b1 b2) E2)
                   (plus (plus (req_minus LZ1 LZ2) (mult (req_minus b2 b1) E1))
                         (req_minus LZ2 LZ1)))
             (plus (mult (req_minus b1 b2) E2)
                   (plus (mult (req_minus b2 b1) E1)
                         (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1))))).
    - exact (req_plus_compat (mult (req_minus b1 b2) E2)
               (mult (req_minus b1 b2) E2)
               (plus (req_minus LZ1 LZ2)
                     (plus (mult (req_minus b2 b1) E1) (req_minus LZ2 LZ1)))
               (plus (plus (req_minus LZ1 LZ2) (mult (req_minus b2 b1) E1))
                     (req_minus LZ2 LZ1))
               (req_refl (mult (req_minus b1 b2) E2))
               (plus_assoc (req_minus LZ1 LZ2) (mult (req_minus b2 b1) E1)
                           (req_minus LZ2 LZ1))).
    - apply (req_trans
               (plus (mult (req_minus b1 b2) E2)
                     (plus (plus (req_minus LZ1 LZ2) (mult (req_minus b2 b1) E1))
                           (req_minus LZ2 LZ1)))
               (plus (mult (req_minus b1 b2) E2)
                     (plus (plus (mult (req_minus b2 b1) E1) (req_minus LZ1 LZ2))
                           (req_minus LZ2 LZ1)))
               (plus (mult (req_minus b1 b2) E2)
                     (plus (mult (req_minus b2 b1) E1)
                           (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1))))).
      + exact (req_plus_compat (mult (req_minus b1 b2) E2)
                 (mult (req_minus b1 b2) E2)
                 (plus (plus (req_minus LZ1 LZ2) (mult (req_minus b2 b1) E1))
                       (req_minus LZ2 LZ1))
                 (plus (plus (mult (req_minus b2 b1) E1) (req_minus LZ1 LZ2))
                       (req_minus LZ2 LZ1))
                 (req_refl (mult (req_minus b1 b2) E2))
                 (req_plus_compat
                    (plus (req_minus LZ1 LZ2) (mult (req_minus b2 b1) E1))
                    (plus (mult (req_minus b2 b1) E1) (req_minus LZ1 LZ2))
                    (req_minus LZ2 LZ1) (req_minus LZ2 LZ1)
                    (plus_comm (req_minus LZ1 LZ2) (mult (req_minus b2 b1) E1))
                    (req_refl (req_minus LZ2 LZ1)))).
      + exact (req_plus_compat (mult (req_minus b1 b2) E2)
                 (mult (req_minus b1 b2) E2)
                 (plus (plus (mult (req_minus b2 b1) E1) (req_minus LZ1 LZ2))
                       (req_minus LZ2 LZ1))
                 (plus (mult (req_minus b2 b1) E1)
                       (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1)))
                 (req_refl (mult (req_minus b1 b2) E2))
                 (req_sym (plus (mult (req_minus b2 b1) E1)
                                (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1)))
                          (plus (plus (mult (req_minus b2 b1) E1)
                                      (req_minus LZ1 LZ2))
                                (req_minus LZ2 LZ1))
                          (plus_assoc (mult (req_minus b2 b1) E1)
                                      (req_minus LZ1 LZ2)
                                      (req_minus LZ2 LZ1)))). }
  assert (Hza : req (plus (mult (req_minus b1 b2) E2)
                          (plus (mult (req_minus b2 b1) E1)
                                (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1))))
                    (plus (mult (req_minus b1 b2) E2)
                          (plus (mult (req_minus b2 b1) E1) zero))).
  { exact (req_plus_compat (mult (req_minus b1 b2) E2)
             (mult (req_minus b1 b2) E2)
             (plus (mult (req_minus b2 b1) E1)
                   (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1)))
             (plus (mult (req_minus b2 b1) E1) zero)
             (req_refl (mult (req_minus b1 b2) E2))
             (req_plus_compat (mult (req_minus b2 b1) E1)
                (mult (req_minus b2 b1) E1)
                (plus (req_minus LZ1 LZ2) (req_minus LZ2 LZ1)) zero
                (req_refl (mult (req_minus b2 b1) E1)) Hz)). }
  assert (H3 : req (plus (mult (req_minus b1 b2) E2)
                         (plus (mult (req_minus b2 b1) E1) zero))
                   (plus (mult (req_minus b1 b2) E2) (mult (req_minus b2 b1) E1))).
  { exact (req_plus_compat (mult (req_minus b1 b2) E2)
             (mult (req_minus b1 b2) E2)
             (plus (mult (req_minus b2 b1) E1) zero) (mult (req_minus b2 b1) E1)
             (req_refl (mult (req_minus b1 b2) E2))
             (plus_zero (mult (req_minus b2 b1) E1))). }
  exact (req_trans _ _ _ Hsum
           (req_trans _ _ _ H1
              (req_trans _ _ _ H2
                 (req_trans _ _ _ Hza (req_trans _ _ _ H3 Hmain2))))).
Qed.

(* ============================================================ *)
(* 严格层件 5/6：温度-能量严格单调（Id @18019 差正形态）          *)
(*   t1 < t2 且 KL(p_{t2}‖p_{t1}) > 0 ⟹ 0 < E(t2) − E(t1)。       *)
(*   非平凡性：组装（ident2 + req_gibbs_inequality +              *)
(*   lt_le_trans/req_le_plus_nonneg_r + reqd_lt_mult_pos_cancel   *)
(*   严格消去）。诚实前提同 mono 件（lt_minus_nonneg 同位）。      *)
(* ============================================================ *)
Theorem req_energy_exp_temp_strict_mono :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
    lt t1 t2 ->
    lt zero (req_relative_entropy S sumf (tB t2 Ht2) (tB t1 Ht1)
               (tBpos t2 Ht2) (tBpos t1 Ht1)) ->
    lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) ->
    lt zero (req_minus (tE t2 Ht2) (tE t1 Ht1)).
Proof.
  intros t1 t2 Ht1 Ht2 Ht12 Hkl1 Hbd.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (E1 := tE t1 Ht1). set (E2 := tE t2 Ht2).
  set (K1 := req_relative_entropy S sumf (tB t2 Ht2) (tB t1 Ht1)
               (tBpos t2 Ht2) (tBpos t1 Ht1)).
  set (K2 := req_relative_entropy S sumf (tB t1 Ht1) (tB t2 Ht2)
               (tBpos t1 Ht1) (tBpos t2 Ht2)).
  (* K2 ≥ 0（req_gibbs_inequality） *)
  assert (Hkl2 : le zero K2).
  { exact (req_gibbs_inequality S sumf fsum_ext fsum_add fsum_linear fsum_le
             dist_log_inv_one_inv dist_log_le_linear
             (tB t1 Ht1) (tB t2 Ht2) (tBpos t1 Ht1) (tBpos t2 Ht2)
             (tBnorm t1 Ht1) (tBnorm t2 Ht2)). }
  (* K1 + K2 > 0（lt_le_trans + req_le_plus_nonneg_r） *)
  assert (Hklsum : lt zero (plus K1 K2)).
  { exact (lt_le_trans zero K1 (plus K1 K2) Hkl1
             (req_le_plus_nonneg_r K1 K2 Hkl2)). }
  (* 恒等（件 ident2）+ lt_id_r 替换 *)
  assert (Hprod : lt zero (mult (req_minus b1 b2) (req_minus E2 E1))).
  { exact (lt_id_r zero (plus K1 K2)
             (mult (req_minus b1 b2) (req_minus E2 E1))
             (req_temp_strict_ident2 t1 t2 Ht1 Ht2) Hklsum). }
  (* 正乘严格消去（先 comm 换序） *)
  apply (reqd_lt_mult_pos_cancel (req_minus E2 E1) (req_minus b1 b2) Hbd).
  apply (lt_id_r zero (mult (req_minus b1 b2) (req_minus E2 E1))
                  (mult (req_minus E2 E1) (req_minus b1 b2))).
  - exact (mult_comm (req_minus b1 b2) (req_minus E2 E1)).
  - exact Hprod.
Qed.

(* ============================================================ *)
(* 严格层件 6/6：对偶闭环 sigT 形（Id temp_energy_dual_closed      *)
(*   @17788）。非平凡性：纯组装（幂等 δ 对偶逐件标注）——见证 =    *)
(*   tB/tBnorm/tBpos（Defined 正件），能量口 req_refl（tE δ 透明），*)
(*   最优口 = 件 4，唯一口 = 件 5。零新增主张。                    *)
(* ============================================================ *)
Theorem req_temp_energy_dual_closed :
  forall (t : R) (Ht : lt zero t),
    sigT (fun pb : S -> R =>
      sigT (fun Hpb : reqd_positive_dist S pb =>
        And (reqd_normalized S sumf pb)
            (And (req (reqd_energy_expectation S sumf base_loss pb) (tE t Ht))
                 (And (forall (p : S -> R) (Hp : reqd_positive_dist S p),
                        reqd_normalized S sumf p ->
                        req (reqd_energy_expectation S sumf base_loss p) (tE t Ht) ->
                        le (reqd_entropy_dist S sumf p Hp)
                           (reqd_entropy_dist S sumf pb Hpb))
                      (forall (p : S -> R) (Hp : reqd_positive_dist S p),
                        reqd_normalized S sumf p ->
                        req (reqd_energy_expectation S sumf base_loss p) (tE t Ht) ->
                        req (reqd_entropy_dist S sumf p Hp)
                            (reqd_entropy_dist S sumf pb Hpb) ->
                        forall s : S, req (p s) (pb s)))))).
Proof.
  intros t Ht.
  exists (tB t Ht).
  exists (tBpos t Ht).
  split.
  - exact (tBnorm t Ht).
  - split.
    + exact (req_refl (tE t Ht)).
    + split.
      * intros p Hp Hnp Henergy.
        exact (req_max_entropy_is_boltzmann_temp t Ht p Hp Hnp Henergy).
      * intros p Hp Hnp Henergy Hent.
        exact (req_entropy_max_unique_temp t Ht p Hp Hnp Henergy Hent).
Qed.

End ReqTempEntropy.

(* ============================================================ *)
(* 批 2 余件 (a) 温度熵层 5 件逐条核销（对照 UpReqDist.v 文件尾）：*)
(*   req_entropy_temp_explicit        <- Id entropy_temp_explicit *)
(*     @CW219 L17271                                          [1] *)
(*   req_relative_entropy_temp_decomp <- Id @L17356           [2] *)
(*   req_entropy_deficit_temp         <- Id entropy_deficit_    *)
(*     kl_temp @L17691（台账名 req_entropy_deficit_kl_temp）  [3] *)
(*   req_max_entropy_is_boltzmann_temp<- Id @L17726           [4] *)
(*   req_entropy_max_unique_temp      <- Id @L17763           [5] *)
(* -------------------------------------------------------------- *)
(* 本文件合计：5 Qed（全部纯构造性；节参数 = FEP 求和面/接口桥    *)
(*   + Z_temp 接口，不含固定温度 D/Z——温度层只依赖 Z_temp）。     *)
(* Id → req 非平凡差异（逐件真证，非抄写）：                      *)
(*   a) log 前提逐位携带正性证明（tBpos/tZpos 透明别名，与        *)
(*     reqd_boltzmann_log_temp_decomp 的前提字面一致——批 2 卡坑7）；*)
(*   b) minus → req_minus（δ 透明），Id mult_minus_distr_l /      *)
(*     sum_over_S_minus → distrib / fsum_opp 桥（opp_mult_l 换形）；*)
(*   c) Id rewrite 链 → req_trans + compat 桥（零 rewrite）；     *)
(*   d) 接口 mult_assoc 方向反向（req (a·(b·c)) ((a·b)·c)），     *)
(*     结合步以 req_sym 对齐；                                    *)
(*   e) 件 3 的 Hpp（reqd_positive_dist p）与 Id 同为诚实现位（未用）。 *)
(* 消费入口：Require Import UpReqTempEntropy.（依赖 CW219 +        *)
(*   UpReqAlgebra + UpReqDist 三 .vo 已编译可载）。                *)
(* -------------------------------------------------------------- *)

(* ============================================================ *)
(* 温度严格层增量节 6 件逐条核销（第三席 2026-09-09，批 2 挂账    *)
(*   5+1 件收口；基座坐标 = CW219 ConstructiveWorld_Live 主副本）：*)
(*   req_variational_temp_bound       <- Id variational_temp_    *)
(*     bound @L17468（件 2 + req_gibbs_inequality + 移项链真证） [6] *)
(*   req_energy_exp_temp_mono         <- Id @L17521（放电件 +    *)
(*     变分界×2 + Id Hm/Hshift/Hsum/Hlhs 全链 req 复刻）       [7] *)
(*   req_temp_energy_dual_closed      <- Id @L17788 sigT 形      *)
(*     （纯组装：tB/tBpos/tBnorm + 能量口 req_refl + 件 4/件 5）[8] *)
(*   req_temp_strict_A_chain2         <- Id @L17825（件 1 +      *)
(*     opp_plus/distrib/req_mult_minus_distr_r 五段 req 链）   [9] *)
(*   req_temp_strict_ident2           <- Id @L17879（件 2 + [9]  *)
(*     交叉 + Hmain2 五步 + H1/H2/Hza/H3 逐步 trans 重排）    [10] *)
(*   req_energy_exp_temp_strict_mono  <- Id @L18019（[10] +      *)
(*     req_gibbs_inequality + reqd_lt_mult_pos_cancel 严格消去）[11] *)
(*   助手 3：req_inv_pos_lt_contra（**放电**：Id L17119/L21013      *)
(*     Variable 位接口字段闭包真证关闭，RestA ralt_inv_pos_lt_     *)
(*     contra 同款复刻——零新增公理）+ reqd_minus_pair_cancel /     *)
(*     reqd_minus_opp_flip（纯接口代数，Hsum/Hoppm 段公用）。      *)
(* -------------------------------------------------------------- *)
(* 诚实签名变化台账（对照 Id 原件）：                              *)
(*   1. mono / strict_mono 增显式前提 lt zero (req_minus b1 b2)：  *)
(*     Id L17121 lt_minus_nonneg 系接口抽象层 Variable（Real 层逐  *)
(*     eps 直构），req 接口无 lt↔minus 连接字段，不可放电——逐位    *)
(*     保留（Real 实例化下为定理，不放大主张）。                    *)
(*   2. dual_closed 的 reqd_positive_dist pb 合取支升入 sigT 见证位     *)
(*     （Hpb）：req 系 reqd_entropy_dist 的正性位 proof-relevant，抽象   *)
(*     pb 无见证不可类型化——信息与 Id 逐位等价（正性即数据）。     *)
(*   3. dual_closed 各约束口结论改 req/le 形（Id 系 Id→req 常规）。 *)
(* 本文件合计：14 Qed = 批 2 五件 [1]-[5] + 本批 3 助手 + 6 件      *)
(*   [6]-[11]（全部纯构造性；Set 层语句零 Prop 泄露；纯 term-mode，  *)
(*   零 Morphisms）。节参数不变（温度层只依赖 Z_temp 接口）。        *)
(* 消费入口不变：Require Import UpReqTempEntropy.（CW219 +          *)
(*   UpReqAlgebra + UpReqDist 三 .vo 已编译可载）。                 *)
(* -------------------------------------------------------------- *)
