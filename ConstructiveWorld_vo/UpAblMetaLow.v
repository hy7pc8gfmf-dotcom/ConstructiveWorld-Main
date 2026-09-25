(* ============================================================ *)
(*                                                              *)
(*   甲 mtl_tv_lower       : forall n, le (omd^n·TV0) (TV(n))                   *)
(*   乙 mtl_no_mixing_below: lt B (omd^n·TV0) -> lt B (TV(n))                   *)
(* 精读步分解族实形后定谳：两件在现 cf2 载体上为【可反驳假命题】，本件交付            *)
(* 全链机器反驳（零新假设，四关绿）：                                            *)
(*   根因：cf2_z 只依赖当前态（z s s' = if s then one else opp one），            *)
(*   softmax 核行内 logit 恒定，归一化后每行恰为均匀分布——核行全同：              *)
(*     mtl_kernel_val_t/f : cf2_kernel true/false s' == cf2_inv_two（全 s'）     *)
(*   于是单步把点质量对拍平：cf2_titer 1 cf2_mu0 与 cf2_titer 1 cf2_nu0 逐点        *)
(*   同值，TV(1) == zero（mtl_tv_one_zero），而 omd·TV0 == omd > 0 严格。         *)
(*   甲在 n:=1 处被 mtl_refute_lower 反驳（le 分裂 inl/inr 双支皆导               *)
(*   lt zero zero）；乙被 mtl_no_mixing_refuted 反驳（取 n:=1、                  *)
(*   B:=delta_star·(omd·TV0)，前件 lt B W 由 lt_mult_compat+delta_star<one        *)
(*   真构造，后件运输后与 B>0 相撞）。                                            *)
(* 结论：现载体真实混合时间为 1 步（核每行=均匀），「混合窗 Θ(omd^{-n}) 两侧」      *)
(*   叙事对现 Fin2 世界数据不成立；上界件（cf2_tv_iter_eps 等）不受影响。          *)
(* 升级方向（挂账 M2/主会话）：世界数据需核行真异——z 须同依赖两态（如对角 ±1 形）；  *)
(*   或残核取置换形（K = delta·U + omd·Id），此时 TV(n) == omd^n·TV0 精确成立，    *)
(*   甲乙两件按原语句即为真，本件帮件一~六全部直接复用。                           *)
(* 红线自审：全件语句 Set 值（req/le/lt/Not 均基座 Set 层别名）；零新假设；          *)
(*   零承认件；零经典逻辑；前提位全显式证书参数；本件只读上游零改母本。              *)
(* 编译配方：9.1 直调轨，unset COQLIB/ROCQLIB，全量 coqc -Q . ""（cpu_guard 包裹）。 *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSampling.
Require Import UpReqConcFin2.
Import RealInterfaceEnhancedMod.

(* ---- 帮件〇：左零乘（mult_zero 字段只有右零形；零在左经 comm 桥） ---- *)

Lemma mtl_mult_zero_l : forall a : Real, req (mult zero a) zero.
Proof.
  intro a.
  apply (req_trans _ (mult a zero) zero).
  - exact (mult_comm zero a).
  - exact (mult_zero a).
Defined.

(* ---- 帮件一：二枚举求和形状（cf2_sumf 折叠定义级展开） ---- *)

Lemma mtl_sum2 : forall g : bool -> Real,
  req (cf2_sumf g) (plus (g true) (g false)).
Proof.
  intro g.
  apply (req_trans _ (plus (g true) (plus (g false) zero)) _).
  - exact (req_refl (plus (g true) (plus (g false) zero))).
  - exact (req_plus_compat (g true) (g true) (plus (g false) zero) (g false)
             (req_refl (g true)) (plus_zero (g false))).
Defined.

(* ---- 帮件二：行值代数——正 f 的 f·inv(f+f) 恒等于 inv_two ---- *)

Lemma mtl_row_alg : forall (f : Real) (Hf : lt zero f),
  req (mult f (inv_pos (plus f f) (plus_positive f f Hf Hf))) cf2_inv_two.
Proof.
  intros f Hf.
  apply (req_trans _
           (mult f (mult (inv_pos f Hf) (inv_pos (plus one one) req_two_pos)))
           cf2_inv_two).
  - apply (req_mult_compat f f _ _ (req_refl f)).
    apply (req_trans _
             (inv_pos (mult f (plus one one))
                      (mult_positive f (plus one one) Hf req_two_pos)) _).
    + apply (inv_pos_ext (plus f f) (mult f (plus one one))
               (plus_positive f f Hf Hf)
               (mult_positive f (plus one one) Hf req_two_pos)).
      apply (req_sym _ _).
      apply (req_trans _ (mult (plus one one) f) _).
      * exact (mult_comm f (plus one one)).
      * exact (req_two_mult f).
    + exact (req_inv_pos_mult_distr f (plus one one) Hf req_two_pos).
  - apply (req_trans _
             (mult (mult f (inv_pos f Hf))
                   (inv_pos (plus one one) req_two_pos)) _).
    + exact (mult_assoc f (inv_pos f Hf) (inv_pos (plus one one) req_two_pos)).
    + apply (req_trans _
               (mult one (inv_pos (plus one one) req_two_pos)) cf2_inv_two).
      * apply (req_mult_compat _ _ _ _).
        -- exact (inv_pos_correct f Hf).
        -- exact (req_refl (inv_pos (plus one one) req_two_pos)).
      * exact (req_mult_one_l (inv_pos (plus one one) req_two_pos)).
Defined.

(* ---- 帮件三：核行值——cf2 核每行恒等于 inv_two（行内 logit 恒定的代数后果） ---- *)

Definition mtl_fac_t : Real :=
  rsq_exp_pos_fn (mult (inv_pos cf2_temp cf2_temp_pos) one).

Definition mtl_fac_f : Real :=
  rsq_exp_pos_fn (mult (inv_pos cf2_temp cf2_temp_pos) (opp one)).

Lemma mtl_fac_t_pos : lt zero mtl_fac_t.
Proof. exact (epp_pos (mult (inv_pos cf2_temp cf2_temp_pos) one)). Defined.

Lemma mtl_fac_f_pos : lt zero mtl_fac_f.
Proof. exact (epp_pos (mult (inv_pos cf2_temp cf2_temp_pos) (opp one))). Defined.

Lemma mtl_kernel_val_t : forall s' : bool, req (cf2_kernel true s') cf2_inv_two.
Proof.
  intro s'.
  apply (req_trans _
           (mult mtl_fac_t
              (inv_pos (plus mtl_fac_t mtl_fac_t)
                 (plus_positive mtl_fac_t mtl_fac_t
                    mtl_fac_t_pos mtl_fac_t_pos)))
           cf2_inv_two).
  - apply (req_mult_compat _ _ _ _ (req_refl _)).
    apply (inv_pos_ext (cf2_Zrow true) (plus mtl_fac_t mtl_fac_t)
             (cf2_Zrow_pos true)
             (plus_positive mtl_fac_t mtl_fac_t
                mtl_fac_t_pos mtl_fac_t_pos)).
    apply (req_trans _
             (plus (rsq_exp_pos_fn (mult (inv_pos cf2_temp cf2_temp_pos)
                                      (cf2_z true true)))
                   (rsq_exp_pos_fn (mult (inv_pos cf2_temp cf2_temp_pos)
                                      (cf2_z true false)))) _).
    + exact (mtl_sum2 (fun s0 : bool =>
                rsq_exp_pos_fn (mult (inv_pos cf2_temp cf2_temp_pos)
                                   (cf2_z true s0)))).
    + exact (req_plus_compat _ _ _ _ (req_refl _) (req_refl _)).
  - exact (mtl_row_alg mtl_fac_t mtl_fac_t_pos).
Defined.

Lemma mtl_kernel_val_f : forall s' : bool, req (cf2_kernel false s') cf2_inv_two.
Proof.
  intro s'.
  apply (req_trans _
           (mult mtl_fac_f
              (inv_pos (plus mtl_fac_f mtl_fac_f)
                 (plus_positive mtl_fac_f mtl_fac_f
                    mtl_fac_f_pos mtl_fac_f_pos)))
           cf2_inv_two).
  - apply (req_mult_compat _ _ _ _ (req_refl _)).
    apply (inv_pos_ext (cf2_Zrow false) (plus mtl_fac_f mtl_fac_f)
             (cf2_Zrow_pos false)
             (plus_positive mtl_fac_f mtl_fac_f
                mtl_fac_f_pos mtl_fac_f_pos)).
    apply (req_trans _
             (plus (rsq_exp_pos_fn (mult (inv_pos cf2_temp cf2_temp_pos)
                                      (cf2_z false true)))
                   (rsq_exp_pos_fn (mult (inv_pos cf2_temp cf2_temp_pos)
                                      (cf2_z false false)))) _).
    + exact (mtl_sum2 (fun s0 : bool =>
                rsq_exp_pos_fn (mult (inv_pos cf2_temp cf2_temp_pos)
                                   (cf2_z false s0)))).
    + exact (req_plus_compat _ _ _ _ (req_refl _) (req_refl _)).
  - exact (mtl_row_alg mtl_fac_f mtl_fac_f_pos).
Defined.

(* ---- 帮件四：单步拍平——点质量对一步后逐点同值 == inv_two ---- *)

Lemma mtl_pt_t : forall s' : bool, req (cf2_k_step cf2_mu0 s') cf2_inv_two.
Proof.
  intro s'.
  apply (req_trans _
           (plus (mult (cf2_mu0 true) (cf2_kernel true s'))
                 (plus (mult (cf2_mu0 false) (cf2_kernel false s')) zero))
           cf2_inv_two).
  - exact (req_refl _).
  - apply (req_trans _
             (plus (cf2_kernel true s') (plus zero zero)) _).
    + exact (req_plus_compat _ _ _ _
               (req_mult_one_l (cf2_kernel true s'))
               (req_plus_compat _ _ _ _
                  (mtl_mult_zero_l (cf2_kernel false s')) (req_refl zero))).
    + apply (req_trans _ (plus (cf2_kernel true s') zero) _).
      * exact (req_plus_compat _ _ _ _ (req_refl _) (plus_zero zero)).
      * apply (req_trans _ (cf2_kernel true s') cf2_inv_two).
        -- exact (plus_zero (cf2_kernel true s')).
        -- exact (mtl_kernel_val_t s').
Defined.

Lemma mtl_pt_n : forall s' : bool, req (cf2_k_step cf2_nu0 s') cf2_inv_two.
Proof.
  intro s'.
  apply (req_trans _
           (plus (mult (cf2_nu0 true) (cf2_kernel true s'))
                 (plus (mult (cf2_nu0 false) (cf2_kernel false s')) zero))
           cf2_inv_two).
  - exact (req_refl _).
  - apply (req_trans _
             (plus zero (plus (cf2_kernel false s') zero)) _).
    + exact (req_plus_compat _ _ _ _
               (mtl_mult_zero_l (cf2_kernel true s'))
               (req_plus_compat _ _ _ _
                  (req_mult_one_l (cf2_kernel false s'))
                  (req_refl zero))).
    + apply (req_trans _ (plus (cf2_kernel false s') zero) _).
      * exact (req_plus_zero_l (plus (cf2_kernel false s') zero)).
      * apply (req_trans _ (cf2_kernel false s') cf2_inv_two).
        -- exact (plus_zero (cf2_kernel false s')).
        -- exact (mtl_kernel_val_f s').
Defined.

(* titer 1 与 k_step 的定义级同体换形 *)
Lemma mtl_t1_t : forall s' : bool, req (cf2_titer 1%nat cf2_mu0 s') cf2_inv_two.
Proof. intro s'. exact (mtl_pt_t s'). Defined.

Lemma mtl_t1_n : forall s' : bool, req (cf2_titer 1%nat cf2_nu0 s') cf2_inv_two.
Proof. intro s'. exact (mtl_pt_n s'). Defined.

(* ---- 帮件五：n=1 处 TV == zero ---- *)

Lemma mtl_pt_abs : forall s : bool,
  req (abs (req_minus (cf2_titer 1%nat cf2_mu0 s) (cf2_titer 1%nat cf2_nu0 s)))
      zero.
Proof.
  intro s.
  assert (Hd : req (req_minus (cf2_titer 1%nat cf2_mu0 s)
                              (cf2_titer 1%nat cf2_nu0 s)) zero).
  { apply (req_trans _ (req_minus cf2_inv_two cf2_inv_two) zero).
    - exact (reqd_minus_compat _ _ _ _ (mtl_t1_t s) (mtl_t1_n s)).
    - exact (plus_opp cf2_inv_two). }
  apply (req_trans _
             (req_minus (cf2_titer 1%nat cf2_mu0 s)
                        (cf2_titer 1%nat cf2_nu0 s)) zero).
  - exact (cf2_bs_abs _ (lt_le_iff _ _ (inr (req_sym _ _ Hd)))).
  - exact Hd.
Defined.

Lemma mtl_tv_one_zero :
  req (cf2_tv (cf2_titer 1%nat cf2_mu0) (cf2_titer 1%nat cf2_nu0)) zero.
Proof.
  apply (req_trans _
           (mult cf2_inv_two
              (cf2_sumf (fun s : bool =>
                   abs (req_minus (cf2_titer 1%nat cf2_mu0 s)
                                  (cf2_titer 1%nat cf2_nu0 s)))))
           zero).
  - exact (req_refl (mult cf2_inv_two
                (cf2_sumf (fun s : bool =>
                     abs (req_minus (cf2_titer 1%nat cf2_mu0 s)
                                    (cf2_titer 1%nat cf2_nu0 s)))))).
  - exact (req_trans _ _ _
             (req_mult_compat cf2_inv_two cf2_inv_two
                (cf2_sumf (fun s : bool =>
                     abs (req_minus (cf2_titer 1%nat cf2_mu0 s)
                                    (cf2_titer 1%nat cf2_nu0 s))))
                (cf2_sumf (fun _ : bool => zero))
                (req_refl cf2_inv_two)
                (req_trans _ _ _
                   (mtl_sum2 (fun s : bool =>
                        abs (req_minus (cf2_titer 1%nat cf2_mu0 s)
                                       (cf2_titer 1%nat cf2_nu0 s))))
                   (req_trans _ _ _
                      (req_plus_compat
                         (abs (req_minus (cf2_titer 1%nat cf2_mu0 true)
                                     (cf2_titer 1%nat cf2_nu0 true)))
                         zero
                         (abs (req_minus (cf2_titer 1%nat cf2_mu0 false)
                                     (cf2_titer 1%nat cf2_nu0 false)))
                         zero
                         (mtl_pt_abs true) (mtl_pt_abs false))
                      (req_plus_zero_l zero))))
             (req_trans _ _ _
                (req_mult_compat cf2_inv_two cf2_inv_two
                   (cf2_sumf (fun _ : bool => zero)) zero
                   (req_refl cf2_inv_two)
                   (req_trans _ _ _
                      (mtl_sum2 (fun _ : bool => zero))
                      (req_plus_zero_l zero)))
                (mult_zero cf2_inv_two))).
Defined.

(* ---- 帮件六：TV0 == one；omd^1 == omd；W := omd·TV0 的同值与正性 ---- *)

Lemma mtl_tv0_one : req (cf2_tv cf2_mu0 cf2_nu0) one.
Proof.
  apply (req_trans _ (mult cf2_inv_two (plus one one)) one).
  - exact (req_mult_compat cf2_inv_two cf2_inv_two
             (cf2_sumf (fun s : bool =>
                  abs (req_minus (cf2_mu0 s) (cf2_nu0 s))))
             (plus one one) (req_refl cf2_inv_two) cf2_tv_sum_one).
  - apply (req_trans _ (mult (plus one one) cf2_inv_two) one).
    + exact (mult_comm cf2_inv_two (plus one one)).
    + exact (inv_pos_correct (plus one one) req_two_pos).
Defined.

Lemma mtl_rpow1_omd : req (req_r_pow cf2_omd 1%nat) cf2_omd.
Proof.
  apply (req_trans _ (mult cf2_omd (req_r_pow cf2_omd 0%nat)) cf2_omd).
  - exact (req_refl _).
  - exact (req_mult_one_r cf2_omd).
Defined.

Definition mtl_W : Real :=
  mult (req_r_pow cf2_omd 1%nat) (cf2_tv cf2_mu0 cf2_nu0).

Lemma mtl_W_omd : req mtl_W cf2_omd.
Proof.
  apply (req_trans _ (mult cf2_omd one) cf2_omd).
  - exact (req_mult_compat _ _ _ _ mtl_rpow1_omd mtl_tv0_one).
  - exact (req_mult_one_r cf2_omd).
Defined.

Lemma mtl_W_pos : lt zero mtl_W.
Proof.
  exact (mult_positive _ _
           (lt_id_r zero cf2_omd (req_r_pow cf2_omd 1%nat)
              (req_sym _ _ mtl_rpow1_omd) cf2_omd_pos)
           cf2_tv_pos).
Defined.

(* ---- 帮件七：预算 B := delta_star·W 严格落在 (0, W) 内 ---- *)

Lemma mtl_B_lt_W : lt (mult cf2_delta_star mtl_W) mtl_W.
Proof.
  exact (lt_id_r (mult cf2_delta_star mtl_W) (mult one mtl_W) mtl_W
           (req_mult_one_l mtl_W)
           (lt_mult_compat cf2_delta_star one mtl_W mtl_W_pos cf2_ds_lt_one)).
Defined.

Lemma mtl_B_pos : lt zero (mult cf2_delta_star mtl_W).
Proof.
  exact (mult_positive cf2_delta_star mtl_W cf2_ds_pos mtl_W_pos).
Defined.

(* ============ 主件甲：下界步引理在 n:=1 处的机器反驳 ============ *)

Theorem mtl_refute_lower :
  Not (le (mult (req_r_pow cf2_omd 1%nat) (cf2_tv cf2_mu0 cf2_nu0))
          (cf2_tv (cf2_titer 1%nat cf2_mu0) (cf2_titer 1%nat cf2_nu0))).
Proof.
  intro H.
  assert (Hle0 : le mtl_W zero).
  { apply (le_trans mtl_W
              (cf2_tv (cf2_titer 1%nat cf2_mu0) (cf2_titer 1%nat cf2_nu0)) zero).
    - exact (le_id_l mtl_W
               (mult (req_r_pow cf2_omd 1%nat) (cf2_tv cf2_mu0 cf2_nu0))
               (cf2_tv (cf2_titer 1%nat cf2_mu0) (cf2_titer 1%nat cf2_nu0))
               (req_refl (mult (req_r_pow cf2_omd 1%nat)
                               (cf2_tv cf2_mu0 cf2_nu0))) H).
    - exact (le_id_r
               (cf2_tv (cf2_titer 1%nat cf2_mu0) (cf2_titer 1%nat cf2_nu0))
               zero zero (req_refl zero)
               (le_id_r
                  (cf2_tv (cf2_titer 1%nat cf2_mu0) (cf2_titer 1%nat cf2_nu0))
                  (cf2_tv (cf2_titer 1%nat cf2_mu0) (cf2_titer 1%nat cf2_nu0))
                  zero mtl_tv_one_zero
                  (le_refl
                     (cf2_tv (cf2_titer 1%nat cf2_mu0)
                             (cf2_titer 1%nat cf2_nu0))))).
  }
  apply (lt_irrefl zero).
  exact (lt_id_r zero cf2_omd zero
           (le_antisym cf2_omd zero
              (le_trans cf2_omd mtl_W zero
                 (le_id_l cf2_omd mtl_W mtl_W
                    (req_sym _ _ mtl_W_omd) (le_refl mtl_W))
                 Hle0)
              (lt_le_iff zero cf2_omd (inl cf2_omd_pos)))
           cf2_omd_pos).
Defined.

(* ============ 主件乙：未混合下界推论的机器反驳 ============ *)
(*   乙语句：forall n B, lt B (omd^n·TV0) -> lt B (TV(n))。                      *)
(*   取 n:=1、B:=delta_star·W：前件真（mtl_B_lt_W），后件导 lt B zero，           *)
(*   与 mtl_B_pos 相撞。                                                        *)

Theorem mtl_no_mixing_refuted :
  Not (forall (n : nat) (B : Real),
    lt B (mult (req_r_pow cf2_omd n) (cf2_tv cf2_mu0 cf2_nu0)) ->
    lt B (cf2_tv (cf2_titer n cf2_mu0) (cf2_titer n cf2_nu0))).
Proof.
  intro H.
  assert (Hc : lt (mult cf2_delta_star mtl_W)
                  (cf2_tv (cf2_titer 1%nat cf2_mu0)
                          (cf2_titer 1%nat cf2_nu0))).
  { exact (H 1%nat (mult cf2_delta_star mtl_W) mtl_B_lt_W). }
  apply (lt_irrefl zero).
  exact (lt_trans zero (mult cf2_delta_star mtl_W) zero
           mtl_B_pos (lt_id_r _ _ zero mtl_tv_one_zero Hc)).
Defined.

(* ============ 四关自检：全件 Closed（零新假设） ============ *)

Print Assumptions mtl_sum2.
Print Assumptions mtl_row_alg.
Print Assumptions mtl_kernel_val_t.
Print Assumptions mtl_kernel_val_f.
Print Assumptions mtl_pt_t.
Print Assumptions mtl_pt_n.
Print Assumptions mtl_tv_one_zero.
Print Assumptions mtl_tv0_one.
Print Assumptions mtl_W_omd.
Print Assumptions mtl_B_lt_W.
Print Assumptions mtl_refute_lower.
Print Assumptions mtl_no_mixing_refuted.
