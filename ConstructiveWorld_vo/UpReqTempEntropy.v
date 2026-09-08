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
Definition tBpos (t : R) (Ht : lt zero t) : positive_dist S (tB t Ht) :=
  reqd_boltzmann_dist_temp_pos S sumf fsum_pos base_loss Z_temp Z_temp_spec t Ht.
Definition tBnorm (t : R) (Ht : lt zero t) : normalized S sumf (tB t Ht) :=
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
    req (entropy_dist S sumf (tB t Ht) (tBpos t Ht))
        (plus (mult (inv_pos t Ht) (tE t Ht))
              (log (Z_temp t) (tZpos t Ht))).
Proof.
  intros t Ht.
  set (bta := inv_pos t Ht).
  set (LZ := log (Z_temp t) (tZpos t Ht)).
  set (p := tB t Ht).
  set (Hp := tBpos t Ht).
  unfold entropy_dist.
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
  forall (t : R) (Ht : lt zero t) (q : S -> R) (Hq : positive_dist S q),
    normalized S sumf q ->
    req (req_relative_entropy S sumf q (tB t Ht) Hq (tBpos t Ht))
        (plus (plus (opp (entropy_dist S sumf q Hq))
                    (mult (inv_pos t Ht)
                          (energy_expectation S sumf base_loss q)))
              (log (Z_temp t) (tZpos t Ht))).
Proof.
  intros t Ht q Hq Hnq.
  set (bta := inv_pos t Ht).
  set (LZ := log (Z_temp t) (tZpos t Ht)).
  set (pB := tB t Ht).
  set (HpB := tBpos t Ht).
  set (Hq0 := entropy_dist S sumf q Hq).
  set (Eq := energy_expectation S sumf base_loss q).
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
  forall (t : R) (Ht : lt zero t) (p : S -> R) (Hp : positive_dist S p),
    normalized S sumf p ->
    req (energy_expectation S sumf base_loss p) (tE t Ht) ->
    req (req_minus (entropy_dist S sumf (tB t Ht) (tBpos t Ht))
                   (entropy_dist S sumf p Hp))
        (req_relative_entropy S sumf p (tB t Ht) Hp (tBpos t Ht)).
Proof.
  intros t Ht p Hp Hnp Henergy.
  set (bta := inv_pos t Ht).
  set (LZ := log (Z_temp t) (tZpos t Ht)).
  set (Sp := entropy_dist S sumf p Hp).
  set (Spt := entropy_dist S sumf (tB t Ht) (tBpos t Ht)).
  set (K := req_relative_entropy S sumf p (tB t Ht) Hp (tBpos t Ht)).
  set (Ep := energy_expectation S sumf base_loss p).
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
  forall (t : R) (Ht : lt zero t) (p : S -> R) (Hp : positive_dist S p),
    normalized S sumf p ->
    req (energy_expectation S sumf base_loss p) (tE t Ht) ->
    le (entropy_dist S sumf p Hp)
       (entropy_dist S sumf (tB t Ht) (tBpos t Ht)).
Proof.
  intros t Ht p Hp Hnp Henergy.
  set (Sp := entropy_dist S sumf p Hp).
  set (Spt := entropy_dist S sumf (tB t Ht) (tBpos t Ht)).
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
  forall (t : R) (Ht : lt zero t) (p : S -> R) (Hp : positive_dist S p),
    normalized S sumf p ->
    req (energy_expectation S sumf base_loss p) (tE t Ht) ->
    req (entropy_dist S sumf p Hp)
        (entropy_dist S sumf (tB t Ht) (tBpos t Ht)) ->
    forall s : S, req (p s) (tB t Ht s).
Proof.
  intros t Ht p Hp Hnp Henergy Hent s.
  set (Sp := entropy_dist S sumf p Hp).
  set (Spt := entropy_dist S sumf (tB t Ht) (tBpos t Ht)).
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
(*   e) 件 3 的 Hpp（positive_dist p）与 Id 同为诚实现位（未用）。 *)
(* 消费入口：Require Import UpReqTempEntropy.（依赖 CW219 +        *)
(*   UpReqAlgebra + UpReqDist 三 .vo 已编译可载）。                *)
(* -------------------------------------------------------------- *)
