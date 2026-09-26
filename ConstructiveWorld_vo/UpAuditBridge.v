(* ============================================================ *)
(* UpAuditBridge.v *)
(* *)
(* 目的： 审计温度配分 Z 的对数桥与审计质量构造（Real 层 list 离散世界）。 *)
(* 主件： uab_Z_aud_log_bridge：Z 的对数分解桥；配 uab_minp_pos_cert / uab_full_pos_cert 正性证书链。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： 不主张 KL(full 与 minp) 方向：通过集外 minp 取零点，正性前提不成立，为显式排除的语义边界；词表可判定性与温度和正性以 Variable 前提声明。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAuditBridge：Min-P 截断采样 = 到通过集的 KL 投影（P8 全量）   *)
(* 桥引理 + list-KL 分解恒等式 + 精确代价 + eps 最优性 + hlogz     *)
(* ============================================================ *)
(* 诚实边界（方向纪律）：                                        *)
(*   1) 全部从截断侧度量：KL(q‖full)、KL(q‖minp)、KL(minp‖full)。 *)
(*      不主张 KL(full‖minp)——通过集外 minp 取零点，正性前提不在  *)
(*      手，诚实拒绝该方向。                                     *)
(*   2) Z_aud 语义：= 保留集上【完整核】的质量                    *)
(*      Z_aud = Σ_keep markov_kernel = temp_sum · inv(Z_full)。   *)
(*      这是 KL 投影语义的正确定标（投影基 = 归一化完整核），      *)

(*      即「通过集质量亏损的对数」（kept'=Z_aud, dropped'=1−Z_aud, *)
(*      均以完整核为参照；root 无 real_minp_dropped_mass，故以     *)
(*      kept-mass 形态陈述，见 real_Z_aud_is_kept_mass）。         *)
(*      注意：任务书字面形态「minp == markov_kernel·inv(Σ_keep     *)
(*      temp_factor)」缺 Z_full 定标、代数不闭合；本件按投影语义   *)
(*      修正为「minp == markov_kernel·inv(Z_aud)」，Z_aud 为完整   *)
(*      核的保留质量。                                            *)
(*   3) 根内既有资产直接消费不重证：real_minp_*（RealMinPMain）、  *)
(*      real_list_sum 骨架、real_gibbs/real_kl_term、real_inv_inv、*)
(*      real_log_* 单调族。本文件为 list 世界对接层（根内无此内容）。*)
(*   4) 219 基座（2026-09-09 回并）：树内 219.vo 已重建为 9.0 同轨   *)
(*      （幻数 90001；旧 9.1 盘留档 .vo.bak-90100），本机 9.0 编译器 *)
(*      直读通过，回退条款解除：Require CW_ConstructiveWorld_219。   *)
(*      消费名 48 项探针核对逐位在位（含 RealSetoid 七字段与        *)
(*      MinP 三机器），声明与定理陈述零数学改动。回退版备份   *)
(*      于 UpAuditBridge-基线备份-20260909.v。                  *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

Section UpAuditBridge.

(* ---------- Min-P 机器接口（镜像 root RealMinPMain） ---------- *)
Variable Token : Type.
Variable vocab : list Token.
Variable real_temp_factor : Token -> Real.
Variable real_minp_keep : list Token -> Token -> Set.
Variable real_minp_keep_dec : forall (prefix : list Token) (w : Token),
  Or (real_minp_keep prefix w) (Not (real_minp_keep prefix w)).

(* 保留分支项：keep ⟹ temp_factor，drop ⟹ 0
   （定义性 == root real_minp_temp_sum 的求和项） *)
Definition uab_branch (prefix : list Token) (w : Token) : Real :=
  match real_minp_keep_dec prefix w with
  | inl _ => real_temp_factor w
  | inr _ => real_zero
  end.

(* 截断质量 temp_sum := Σ_keep temp_factor（root 机器） *)
Definition uab_temp_sum (prefix : list Token) : Real :=
  real_minp_temp_sum Token vocab real_temp_factor real_minp_keep real_minp_keep_dec prefix.

(* 正性接口（root 诚实接口形态） *)
Variable uab_temp_sum_pos : forall prefix : list Token,
  real_lt real_zero (uab_temp_sum prefix).

(* 诚实接口：温度因子逐 token 正（abstract 层由 exp_neg_pos 提供， *)
(* root RealMinPMain 未假设，KL 项需之，故显式补） *)
Variable uab_temp_factor_pos : forall w : Token, real_lt real_zero (real_temp_factor w).

(* 完整配分（root Real 层无 real_partition_temp——本次补齐） *)
Definition Z_full : Real := real_list_sum Token real_temp_factor vocab.
Variable uab_Z_full_pos : real_lt real_zero Z_full.

(* 完整核（温度化 Boltzmann，root abstract markov_kernel 的 Real 形态） *)
Definition real_markov_kernel (prefix : list Token) (w : Token) : Real :=
  real_mult (real_temp_factor w) (real_inv_pos Z_full uab_Z_full_pos).

(* 审计质量 Z_aud := 完整核的保留质量 == temp_sum · inv(Z_full) *)
Definition uab_Z_aud (prefix : list Token) : Real :=
  real_mult (uab_temp_sum prefix) (real_inv_pos Z_full uab_Z_full_pos).


(*   必须透明以保 delta/iota 转换一致，禁 Qed 封死） ---------- *)
Definition uab_minp_pos_cert (prefix : list Token) (w : Token) :
  real_lt real_zero (real_mult (real_temp_factor w)
                               (real_inv_pos (uab_temp_sum prefix) (uab_temp_sum_pos prefix))) :=
  real_mult_positive (real_temp_factor w)
                     (real_inv_pos (uab_temp_sum prefix) (uab_temp_sum_pos prefix))
                     (uab_temp_factor_pos w) (real_inv_pos_pos (uab_temp_sum prefix) (uab_temp_sum_pos prefix)).

Definition uab_full_pos_cert (prefix : list Token) (w : Token) :
  real_lt real_zero (real_markov_kernel prefix w) :=
  real_mult_positive (real_temp_factor w) (real_inv_pos Z_full uab_Z_full_pos)
                     (uab_temp_factor_pos w) (real_inv_pos_pos Z_full uab_Z_full_pos).

Definition uab_Z_aud_pos_cert (prefix : list Token) :
  real_lt real_zero (uab_Z_aud prefix) :=
  real_mult_positive (uab_temp_sum prefix) (real_inv_pos Z_full uab_Z_full_pos)
                     (uab_temp_sum_pos prefix) (real_inv_pos_pos Z_full uab_Z_full_pos).

(* min-p 核（root real_minp_markov_kernel 的本地摘要） *)
Definition uab_minp_kernel (prefix : list Token) (w : Token) : Real :=
  real_minp_markov_kernel Token vocab real_temp_factor real_minp_keep real_minp_keep_dec
                          uab_temp_sum_pos prefix w.

(* min-p 核 keep 支正性（透明 Defined：keep 支即 uab_minp_pos_cert，
   delta+iota 后与证书项转换一致——不得 Qed 封死） *)
Definition uab_minp_keep_pos (prefix : list Token) (w : Token)
  (Hk : real_minp_keep prefix w) : real_lt real_zero (uab_minp_kernel prefix w).
Proof.
  unfold uab_minp_kernel, real_minp_markov_kernel.
  destruct (real_minp_keep_dec prefix w) as [Hk' | Hd].
  - exact (uab_minp_pos_cert prefix w).
  - destruct (Hd Hk).
Defined.


Lemma uab_minp_fail_zero : forall (prefix : list Token) (w : Token),
  Not (real_minp_keep prefix w) -> real_eq (uab_minp_kernel prefix w) real_zero.
Proof.
  intros prefix w Hd. unfold uab_minp_kernel, real_minp_markov_kernel.
  destruct (real_minp_keep_dec prefix w) as [Hk | Hd'].
  - destruct (Hd Hk).
  - apply real_eq_refl.
Qed.

(* ---------- 基础代数（real_eq 层小工具） ---------- *)

Lemma uab_one_mult : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x. apply (real_eq_trans _ (real_mult x real_one) _).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

Lemma uab_plus_zero_l : forall x : Real, real_eq (real_plus real_zero x) x.
Proof.
  intro x. apply (real_eq_trans _ (real_plus x real_zero) _).
  - apply real_plus_comm.
  - apply real_plus_zero.
Qed.

Lemma uab_plus_zero_opp : forall a : Real, real_eq (real_plus (real_opp a) a) real_zero.
Proof.
  intro a. apply (real_eq_trans _ (real_plus a (real_opp a)) _).
  - apply real_plus_comm.
  - apply real_plus_opp.
Qed.

Lemma uab_list_sum_zero : forall (X : Type) (l : list X),
  real_eq (real_list_sum X (fun _ : X => real_zero) l) real_zero.
Proof.
  intros X l. induction l as [| w rest IH]; simpl.
  - apply real_eq_refl.
  - apply (real_eq_trans _ (real_list_sum X (fun _ : X => real_zero) rest) _).
    + apply uab_plus_zero_l.
    + exact IH.
Qed.

(* 逆的唯一性：x·y == 1 ⟹ y == inv(x)（由 inv_pos_correct + 环代数） *)
Lemma uab_inv_unique : forall (x y : Real) (Hx : real_lt real_zero x),
  real_eq (real_mult x y) real_one -> real_eq y (real_inv_pos x Hx).
Proof.
  intros x y Hx Hxy.
  apply (real_eq_trans _ (real_mult real_one y) _).
  - apply (real_eq_sym _ _ (uab_one_mult y)).
  - apply (real_eq_trans _ (real_mult (real_mult (real_inv_pos x Hx) x) y) _).
    + apply (RealSetoid.real_eq_mult_compat real_one y
               (real_mult (real_inv_pos x Hx) x) y
               (real_eq_sym (real_mult (real_inv_pos x Hx) x) real_one
                 (real_eq_trans (real_mult (real_inv_pos x Hx) x)
                                (real_mult x (real_inv_pos x Hx)) real_one
                                (real_mult_comm (real_inv_pos x Hx) x)
                                (real_inv_pos_correct x Hx)))
               (real_eq_refl y)).
    + apply (real_eq_trans _ (real_mult (real_inv_pos x Hx) (real_mult x y)) _).
      * apply (real_eq_sym _ _ (real_mult_assoc (real_inv_pos x Hx) x y)).
      * apply (real_eq_trans _ (real_mult (real_inv_pos x Hx) real_one) _).
        -- apply (RealSetoid.real_eq_mult_compat (real_inv_pos x Hx) (real_mult x y)
                    (real_inv_pos x Hx) real_one (real_eq_refl _) Hxy).
        -- apply real_mult_one.
Qed.

(* 逆元对乘法的分配：inv(a·b) == inv(a)·inv(b)（root L95695 abstract 版 *)
(* 的 Real 层本地复刻；root 该引理在 217 基线快照之外） *)
Lemma uab_inv_mult_distr : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_eq (real_inv_pos (real_mult a b) (real_mult_positive a b Ha Hb))
          (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb)).
Proof.
  intros a b Ha Hb.
  apply (real_eq_sym (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb))
                     (real_inv_pos (real_mult a b) (real_mult_positive a b Ha Hb))).
  apply (uab_inv_unique (real_mult a b) (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb))
                        (real_mult_positive a b Ha Hb)).
  (* 目标：(a·b)·(Ja·Jb) == one *)
  assert (K1 : real_eq (real_mult (real_inv_pos b Hb) (real_mult a b))
                       (real_mult a real_one)).
  { apply (real_eq_trans _ (real_mult (real_mult (real_inv_pos b Hb) a) b) _).
    - apply real_mult_assoc.
    - apply (real_eq_trans _ (real_mult (real_mult a (real_inv_pos b Hb)) b) _).
      + apply (RealSetoid.real_eq_mult_compat (real_mult (real_inv_pos b Hb) a)
                 b (real_mult a (real_inv_pos b Hb)) b
                 (real_mult_comm (real_inv_pos b Hb) a) (real_eq_refl b)).
      + apply (real_eq_trans _ (real_mult a (real_mult (real_inv_pos b Hb) b)) _).
        * apply (real_eq_sym _ _ (real_mult_assoc a (real_inv_pos b Hb) b)).
        * apply (RealSetoid.real_eq_mult_compat a (real_mult (real_inv_pos b Hb) b)
                   a real_one (real_eq_refl a)
                   (real_eq_trans (real_mult (real_inv_pos b Hb) b)
                                  (real_mult b (real_inv_pos b Hb)) real_one
                                  (real_mult_comm (real_inv_pos b Hb) b)
                                  (real_inv_pos_correct b Hb))). }
  apply (real_eq_trans _ (real_mult (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb))
                                    (real_mult a b)) _).
  - apply real_mult_comm.
  - apply (real_eq_trans _ (real_mult (real_inv_pos a Ha)
                                      (real_mult (real_inv_pos b Hb) (real_mult a b))) _).
    + apply (real_eq_sym _ _ (real_mult_assoc (real_inv_pos a Ha) (real_inv_pos b Hb)
                                 (real_mult a b))).
    + apply (real_eq_trans _ (real_mult (real_inv_pos a Ha) (real_mult a real_one)) _).
      * apply (RealSetoid.real_eq_mult_compat (real_inv_pos a Ha)
                 (real_mult (real_inv_pos b Hb) (real_mult a b))
                 (real_inv_pos a Ha) (real_mult a real_one)
                 (real_eq_refl _) K1).
      * apply (real_eq_trans _ (real_mult (real_inv_pos a Ha) a) _).
        -- apply (RealSetoid.real_eq_mult_compat (real_inv_pos a Ha)
                     (real_mult a real_one) (real_inv_pos a Ha) a
                     (real_eq_refl _) (real_mult_one a)).
        -- apply (real_eq_trans _ (real_mult a (real_inv_pos a Ha)) _).
           ++ apply real_mult_comm.
           ++ apply (real_inv_pos_correct a Ha).
Qed.




Lemma uab_log_inv_neg : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
          (real_opp (real_log x Hx)).
Proof.
  intros x Hx.
  assert (Hsum : real_eq (real_plus (real_log x Hx)
                                    (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                         real_zero).
  { apply (real_eq_trans _ (real_log (real_mult x (real_inv_pos x Hx))
                                     (real_mult_positive x (real_inv_pos x Hx) Hx
                                       (real_inv_pos_pos x Hx))) _).
    - apply (real_eq_sym _ _ (real_log_mult x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx))).
    - apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
      + apply (real_log_wd (real_mult x (real_inv_pos x Hx)) real_one
                 (real_mult_positive x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx))
                 real_lt_zero_one (real_inv_pos_correct x Hx)).
      + apply (real_log_one real_lt_zero_one). }
  assert (Hdir : real_eq (real_opp (real_log x Hx))
                         (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))).
  { apply (real_eq_trans _ (real_plus (real_opp (real_log x Hx)) real_zero) _).
    - apply (real_eq_sym _ _ (real_plus_zero (real_opp (real_log x Hx)))).
    - apply (real_eq_trans _ (real_plus (real_opp (real_log x Hx))
                                        (real_plus (real_log x Hx)
                                                   (real_log (real_inv_pos x Hx)
                                                             (real_inv_pos_pos x Hx)))) _).
      + apply (RealSetoid.real_eq_plus_compat (real_opp (real_log x Hx)) real_zero
                 (real_opp (real_log x Hx))
                 (real_plus (real_log x Hx)
                            (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                 (real_eq_refl _)
                 (real_eq_sym (real_plus (real_log x Hx)
                                         (real_log (real_inv_pos x Hx)
                                                   (real_inv_pos_pos x Hx)))
                              real_zero Hsum)).
      + apply (real_eq_trans _
                 (real_plus (real_plus (real_opp (real_log x Hx)) (real_log x Hx))
                            (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))) _).
        * apply (real_plus_assoc (real_opp (real_log x Hx)) (real_log x Hx)
                    (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))).
        * apply (real_eq_trans _ (real_plus real_zero
                                   (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))) _).
          -- apply (RealSetoid.real_eq_plus_compat
                       (real_plus (real_opp (real_log x Hx)) (real_log x Hx))
                       (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
                       real_zero (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
                       (uab_plus_zero_opp (real_log x Hx)) (real_eq_refl _)).
          -- apply uab_plus_zero_l. }
  apply (real_eq_sym _ _ Hdir).
Qed.

(* 加法尺度拆分：(L + −p) + −(L + −q) == −(p + −q)（A1） *)
Lemma uab_add_scale_split : forall (L p q : Real),
  real_eq (real_plus (real_plus L (real_opp p)) (real_opp (real_plus L (real_opp q))))
          (real_opp (real_plus p (real_opp q))).
Proof.
  intros L p q.
  (* S1 : −(L + −q) == −L + q *)
  assert (S1 : real_eq (real_opp (real_plus L (real_opp q)))
                       (real_plus (real_opp L) q)).
  { apply (real_eq_trans _ (real_plus (real_opp L) (real_opp (real_opp q))) _).
    - apply (real_opp_plus L (real_opp q)).
    - apply (RealSetoid.real_eq_plus_compat (real_opp L) (real_opp (real_opp q))
               (real_opp L) q (real_eq_refl _) (real_opp_opp q)). }
  (* S2 : (−p + (−L + q)) == ((−L + −p) + q) *)
  assert (S2 : real_eq (real_plus (real_opp p) (real_plus (real_opp L) q))
                       (real_plus (real_plus (real_opp L) (real_opp p)) q)).
  { apply (real_eq_trans _ (real_plus (real_plus (real_opp p) (real_opp L)) q) _).
    - apply (real_plus_assoc (real_opp p) (real_opp L) q).
    - apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp p) (real_opp L))
               q (real_plus (real_opp L) (real_opp p)) q
               (real_plus_comm (real_opp p) (real_opp L)) (real_eq_refl q)). }
  (* S3 : L + (−L + −p) == (L + −L) + −p *)
  assert (S3 : real_eq (real_plus L (real_plus (real_opp L) (real_opp p)))
                       (real_plus (real_plus L (real_opp L)) (real_opp p))).
  { apply (real_plus_assoc L (real_opp L) (real_opp p)). }
  (* S4 : (L + −L) + −p == zero + −p == −p *)
  assert (S4 : real_eq (real_plus (real_plus L (real_opp L)) (real_opp p))
                       (real_opp p)).
  { apply (real_eq_trans _ (real_plus real_zero (real_opp p)) _).
    - apply (RealSetoid.real_eq_plus_compat (real_plus L (real_opp L)) (real_opp p)
               real_zero (real_opp p) (real_plus_opp L) (real_eq_refl _)).
    - apply uab_plus_zero_l. }
  (* S5 : −p + q == −(p + −q) *)
  assert (S5 : real_eq (real_plus (real_opp p) q)
                       (real_opp (real_plus p (real_opp q)))).
  { apply (real_eq_trans _ (real_plus (real_opp p) (real_opp (real_opp q))) _).
    - apply (RealSetoid.real_eq_plus_compat (real_opp p) q (real_opp p)
               (real_opp (real_opp q)) (real_eq_refl _)
               (real_eq_sym _ _ (real_opp_opp q))).
    - apply (real_eq_sym _ _ (real_opp_plus p (real_opp q))). }
  apply (real_eq_trans _ (real_plus (real_plus L (real_opp p))
                                    (real_plus (real_opp L) q)) _).
  - apply (RealSetoid.real_eq_plus_compat (real_plus L (real_opp p))
             (real_opp (real_plus L (real_opp q)))
             (real_plus L (real_opp p)) (real_plus (real_opp L) q)
             (real_eq_refl _) S1).
  - apply (real_eq_trans _ (real_plus L (real_plus (real_opp p) (real_plus (real_opp L) q))) _).
    + apply (real_eq_sym _ _ (real_plus_assoc L (real_opp p) (real_plus (real_opp L) q))).
    + apply (real_eq_trans _ (real_plus L (real_plus (real_plus (real_opp L) (real_opp p)) q)) _).
      * apply (RealSetoid.real_eq_plus_compat L
                 (real_plus (real_opp p) (real_plus (real_opp L) q))
                 L (real_plus (real_plus (real_opp L) (real_opp p)) q)
                 (real_eq_refl _) S2).
      * apply (real_eq_trans _
                 (real_plus (real_plus L (real_plus (real_opp L) (real_opp p))) q) _).
        -- apply (real_plus_assoc L (real_plus (real_opp L) (real_opp p)) q).
        -- apply (real_eq_trans _
                    (real_plus (real_plus (real_plus L (real_opp L)) (real_opp p)) q) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus L (real_plus (real_opp L) (real_opp p)))
                       q (real_plus (real_plus L (real_opp L)) (real_opp p)) q
                       S3 (real_eq_refl q)).
           ++ apply (real_eq_trans _ (real_plus (real_plus real_zero (real_opp p)) q) _).
              ** apply (RealSetoid.real_eq_plus_compat
                          (real_plus (real_plus L (real_opp L)) (real_opp p))
                          q (real_plus real_zero (real_opp p)) q
                          (RealSetoid.real_eq_plus_compat (real_plus L (real_opp L))
                             (real_opp p) real_zero (real_opp p)
                             (real_plus_opp L) (real_eq_refl _))
                          (real_eq_refl q)).
              ** apply (real_eq_trans _ (real_plus (real_opp p) q) _).
                 --- apply (RealSetoid.real_eq_plus_compat (real_plus real_zero (real_opp p))
                              q (real_opp p) q (uab_plus_zero_l (real_opp p))
                              (real_eq_refl q)).
                 --- apply S5.
Qed.

(* 逐点核心（P3）：log(minp形态) − log(full形态) == −log uab_Z_aud
   （无分支形态：对 inline 乘积陈述，证书全透明一致） *)
(* uab_Z_aud 与其展开形的 log 转换桥（apply 统一器不展开 Section 内定义，
   以 exact 的完整转换检查显式过桥） *)
Lemma uab_Z_aud_log_bridge : forall prefix : list Token,
  real_eq (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix))
          (real_log (real_mult (uab_temp_sum prefix) (real_inv_pos Z_full uab_Z_full_pos))
                    (uab_Z_aud_pos_cert prefix)).
Proof.
  intro prefix. exact (real_eq_refl _).
Qed.

Lemma uab_log_minp_minus_full : forall (prefix : list Token) (w : Token),
  real_eq (real_plus (real_log (real_mult (real_temp_factor w)
                                          (real_inv_pos (uab_temp_sum prefix) (uab_temp_sum_pos prefix)))
                               (uab_minp_pos_cert prefix w))
                     (real_opp (real_log (real_mult (real_temp_factor w)
                                                    (real_inv_pos Z_full uab_Z_full_pos))
                                         (uab_full_pos_cert prefix w))))
          (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix))).
Proof.
  intros prefix w.
  assert (Hm : real_eq (real_log (real_mult (real_temp_factor w)
                                            (real_inv_pos (uab_temp_sum prefix)
                                                          (uab_temp_sum_pos prefix)))
                                 (uab_minp_pos_cert prefix w))
                       (real_plus (real_log (real_temp_factor w) (uab_temp_factor_pos w))
                                  (real_opp (real_log (uab_temp_sum prefix)
                                                      (uab_temp_sum_pos prefix))))).
  { apply (real_eq_trans _
             (real_plus (real_log (real_temp_factor w) (uab_temp_factor_pos w))
                        (real_log (real_inv_pos (uab_temp_sum prefix)
                                                (uab_temp_sum_pos prefix))
                                  (real_inv_pos_pos (uab_temp_sum prefix)
                                                    (uab_temp_sum_pos prefix)))) _).
    - apply (real_log_mult (real_temp_factor w)
                           (real_inv_pos (uab_temp_sum prefix) (uab_temp_sum_pos prefix))
                           (uab_temp_factor_pos w)
                           (real_inv_pos_pos (uab_temp_sum prefix) (uab_temp_sum_pos prefix))).
    - apply (RealSetoid.real_eq_plus_compat
               (real_log (real_temp_factor w) (uab_temp_factor_pos w))
               (real_log (real_inv_pos (uab_temp_sum prefix) (uab_temp_sum_pos prefix))
                         (real_inv_pos_pos (uab_temp_sum prefix) (uab_temp_sum_pos prefix)))
               (real_log (real_temp_factor w) (uab_temp_factor_pos w))
               (real_opp (real_log (uab_temp_sum prefix) (uab_temp_sum_pos prefix)))
               (real_eq_refl _)
               (uab_log_inv_neg (uab_temp_sum prefix) (uab_temp_sum_pos prefix))). }
  assert (Hf : real_eq (real_log (real_mult (real_temp_factor w)
                                            (real_inv_pos Z_full uab_Z_full_pos))
                                 (uab_full_pos_cert prefix w))
                       (real_plus (real_log (real_temp_factor w) (uab_temp_factor_pos w))
                                  (real_opp (real_log Z_full uab_Z_full_pos)))).
  { apply (real_eq_trans _
             (real_plus (real_log (real_temp_factor w) (uab_temp_factor_pos w))
                        (real_log (real_inv_pos Z_full uab_Z_full_pos)
                                  (real_inv_pos_pos Z_full uab_Z_full_pos))) _).
    - apply (real_log_mult (real_temp_factor w) (real_inv_pos Z_full uab_Z_full_pos)
                           (uab_temp_factor_pos w) (real_inv_pos_pos Z_full uab_Z_full_pos)).
    - apply (RealSetoid.real_eq_plus_compat
               (real_log (real_temp_factor w) (uab_temp_factor_pos w))
               (real_log (real_inv_pos Z_full uab_Z_full_pos)
                         (real_inv_pos_pos Z_full uab_Z_full_pos))
               (real_log (real_temp_factor w) (uab_temp_factor_pos w))
               (real_opp (real_log Z_full uab_Z_full_pos))
               (real_eq_refl _) (uab_log_inv_neg Z_full uab_Z_full_pos)). }
  assert (Hz : real_eq (real_log (real_mult (uab_temp_sum prefix)
                                            (real_inv_pos Z_full uab_Z_full_pos))
                                 (uab_Z_aud_pos_cert prefix))
                       (real_plus (real_log (uab_temp_sum prefix) (uab_temp_sum_pos prefix))
                                  (real_opp (real_log Z_full uab_Z_full_pos)))).
  { apply (real_eq_trans _
             (real_log (real_mult (uab_temp_sum prefix) (real_inv_pos Z_full uab_Z_full_pos))
                       (real_mult_positive (uab_temp_sum prefix)
                                           (real_inv_pos Z_full uab_Z_full_pos)
                                           (uab_temp_sum_pos prefix)
                                           (real_inv_pos_pos Z_full uab_Z_full_pos))) _).
    - apply (real_log_wd
               (real_mult (uab_temp_sum prefix) (real_inv_pos Z_full uab_Z_full_pos))
               (real_mult (uab_temp_sum prefix) (real_inv_pos Z_full uab_Z_full_pos))
               (uab_Z_aud_pos_cert prefix)
               (real_mult_positive (uab_temp_sum prefix)
                                   (real_inv_pos Z_full uab_Z_full_pos)
                                   (uab_temp_sum_pos prefix)
                                   (real_inv_pos_pos Z_full uab_Z_full_pos))
               (real_eq_refl _)).
    - apply (real_eq_trans _
               (real_plus (real_log (uab_temp_sum prefix) (uab_temp_sum_pos prefix))
                          (real_log (real_inv_pos Z_full uab_Z_full_pos)
                                    (real_inv_pos_pos Z_full uab_Z_full_pos))) _).
      + apply (real_log_mult (uab_temp_sum prefix)
                             (real_inv_pos Z_full uab_Z_full_pos)
                             (uab_temp_sum_pos prefix)
                             (real_inv_pos_pos Z_full uab_Z_full_pos)).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_log (uab_temp_sum prefix) (uab_temp_sum_pos prefix))
                 (real_log (real_inv_pos Z_full uab_Z_full_pos)
                           (real_inv_pos_pos Z_full uab_Z_full_pos))
                 (real_log (uab_temp_sum prefix) (uab_temp_sum_pos prefix))
                 (real_opp (real_log Z_full uab_Z_full_pos))
                 (real_eq_refl _)
                 (uab_log_inv_neg Z_full uab_Z_full_pos)). }
  apply (real_eq_trans _
           (real_plus (real_plus (real_log (real_temp_factor w) (uab_temp_factor_pos w))
                                 (real_opp (real_log (uab_temp_sum prefix)
                                                     (uab_temp_sum_pos prefix))))
                      (real_opp (real_plus (real_log (real_temp_factor w)
                                                           (uab_temp_factor_pos w))
                                           (real_opp (real_log Z_full uab_Z_full_pos))))) _).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _ Hm
             (RealSetoid.real_eq_opp_compat _ _ Hf)).
  - apply (real_eq_trans _
             (real_opp (real_plus (real_log (uab_temp_sum prefix) (uab_temp_sum_pos prefix))
                                  (real_opp (real_log Z_full uab_Z_full_pos)))) _).
    + apply uab_add_scale_split.
    + apply (RealSetoid.real_eq_opp_compat _ _).
      * apply (real_eq_sym _ _ Hz).
Qed.

(* 尺度恒等式（件 1 keep 支核心代数，单引理封装）：
   x·inv(a) == (x·inv(b))·inv(a·inv(b))
   经 inv_pos_mult_distr + real_inv_inv + real_inv_pos_correct + 环代数 *)
Lemma uab_scale_identity : forall (x a b : Real)
  (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_eq (real_mult x (real_inv_pos a Ha))
          (real_mult (real_mult x (real_inv_pos b Hb))
                     (real_inv_pos (real_mult a (real_inv_pos b Hb))
                                   (real_mult_positive a (real_inv_pos b Hb) Ha
                                     (real_inv_pos_pos b Hb)))).
Proof.
  intros x a b Ha Hb.
  assert (S1 : real_eq (real_inv_pos (real_mult a (real_inv_pos b Hb))
                                     (real_mult_positive a (real_inv_pos b Hb) Ha
                                       (real_inv_pos_pos b Hb)))
                       (real_mult (real_inv_pos a Ha) b)).
  { apply (real_eq_trans _
             (real_mult (real_inv_pos a Ha)
                        (real_inv_pos (real_inv_pos b Hb) (real_inv_pos_pos b Hb))) _).
    - apply (uab_inv_mult_distr a (real_inv_pos b Hb) Ha (real_inv_pos_pos b Hb)).
    - apply (RealSetoid.real_eq_mult_compat (real_inv_pos a Ha)
               (real_inv_pos (real_inv_pos b Hb) (real_inv_pos_pos b Hb))
               (real_inv_pos a Ha) b (real_eq_refl _)
               (real_inv_inv b Hb (real_inv_pos_pos b Hb))). }
  (* 正向链：x·Ja == x·(Ja·one) == x·(Ja·(Jb·b)) == ... == (x·Jb)·inv(a·Jb) *)
  apply (real_eq_trans _ (real_mult x (real_mult (real_inv_pos a Ha) real_one)) _).
  - apply (RealSetoid.real_eq_mult_compat x (real_inv_pos a Ha)
             x (real_mult (real_inv_pos a Ha) real_one)
             (real_eq_refl x) (real_eq_sym _ _ (real_mult_one (real_inv_pos a Ha)))).
  - apply (real_eq_trans _
             (real_mult x (real_mult (real_inv_pos a Ha) (real_mult (real_inv_pos b Hb) b))) _).
    + apply (RealSetoid.real_eq_mult_compat x (real_mult (real_inv_pos a Ha) real_one)
               x (real_mult (real_inv_pos a Ha) (real_mult (real_inv_pos b Hb) b))
               (real_eq_refl x)
               (RealSetoid.real_eq_mult_compat (real_inv_pos a Ha) real_one
                  (real_inv_pos a Ha) (real_mult (real_inv_pos b Hb) b)
                  (real_eq_refl _)
                  (real_eq_sym _ _
                    (real_eq_trans (real_mult (real_inv_pos b Hb) b)
                                   (real_mult b (real_inv_pos b Hb)) real_one
                                   (real_mult_comm (real_inv_pos b Hb) b)
                                   (real_inv_pos_correct b Hb))))).
    + apply (real_eq_trans _
               (real_mult x (real_mult (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb)) b)) _).
      * apply (RealSetoid.real_eq_mult_compat x
                 (real_mult (real_inv_pos a Ha) (real_mult (real_inv_pos b Hb) b))
                 x (real_mult (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb)) b)
                 (real_eq_refl x) (real_mult_assoc (real_inv_pos a Ha) (real_inv_pos b Hb) b)).
      * apply (real_eq_trans _
                 (real_mult x (real_mult (real_mult (real_inv_pos b Hb) (real_inv_pos a Ha)) b)) _).
        -- apply (RealSetoid.real_eq_mult_compat x
                    (real_mult (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb)) b)
                    x (real_mult (real_mult (real_inv_pos b Hb) (real_inv_pos a Ha)) b)
                    (real_eq_refl x)
                    (RealSetoid.real_eq_mult_compat (real_mult (real_inv_pos a Ha)
                                                        (real_inv_pos b Hb))
                       b (real_mult (real_inv_pos b Hb) (real_inv_pos a Ha)) b
                       (real_mult_comm (real_inv_pos a Ha) (real_inv_pos b Hb))
                       (real_eq_refl b))).
        -- apply (real_eq_trans _
                     (real_mult x (real_mult (real_inv_pos b Hb) (real_mult (real_inv_pos a Ha) b))) _).
           ++ apply (RealSetoid.real_eq_mult_compat x
                       (real_mult (real_mult (real_inv_pos b Hb) (real_inv_pos a Ha)) b)
                       x (real_mult (real_inv_pos b Hb) (real_mult (real_inv_pos a Ha) b))
                       (real_eq_refl x)
                       (real_eq_sym _ _ (real_mult_assoc (real_inv_pos b Hb)
                                                          (real_inv_pos a Ha) b))).
           ++ apply (real_eq_trans _
                       (real_mult (real_mult x (real_inv_pos b Hb)) (real_mult (real_inv_pos a Ha) b)) _).
              ** apply (real_mult_assoc x (real_inv_pos b Hb) (real_mult (real_inv_pos a Ha) b)).
              ** apply (RealSetoid.real_eq_mult_compat
                          (real_mult x (real_inv_pos b Hb)) (real_mult (real_inv_pos a Ha) b)
                          (real_mult x (real_inv_pos b Hb))
                          (real_inv_pos (real_mult a (real_inv_pos b Hb))
                                        (real_mult_positive a (real_inv_pos b Hb) Ha
                                          (real_inv_pos_pos b Hb)))
                          (real_eq_refl _) (real_eq_sym _ _ S1)).
Qed.

(* ============================================================ *)
(* 件 1（桥引理）：min-p 核 == 投影形态                          *)
(*   keep 支：minp w == markov_kernel w · inv(uab_Z_aud)             *)
(*   drop 支：两侧皆零                                           *)
(* ============================================================ *)

Definition uab_proj_kernel (prefix : list Token) (w : Token) : Real :=
  match real_minp_keep_dec prefix w with
  | inl _ => real_mult (real_markov_kernel prefix w)
                       (real_inv_pos (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix))
  | inr _ => real_zero
  end.

Theorem real_minp_kernel_is_projection : forall (prefix : list Token) (w : Token),
  real_eq (uab_minp_kernel prefix w) (uab_proj_kernel prefix w).
Proof.
  intros prefix w.
  unfold uab_minp_kernel, real_minp_markov_kernel, uab_proj_kernel.
  destruct (real_minp_keep_dec prefix w) as [Hk | Hd].
  - (* keep 支：尺度恒等式（uab_Z_aud delta 展开 == S·inv(Z_full)） *)
    apply (uab_scale_identity (real_temp_factor w) (uab_temp_sum prefix) Z_full
             (uab_temp_sum_pos prefix) uab_Z_full_pos).
  - (* drop 支：两侧皆零 *)
    apply real_eq_refl.
Qed.

(* temp_sum 与其 list 展开形的转换桥（exact 全转换，绕 apply 统一器限制） *)
Lemma uab_temp_sum_list_bridge : forall prefix : list Token,
  real_eq (real_list_sum Token (uab_branch prefix) vocab) (uab_temp_sum prefix).
Proof. intro prefix. exact (real_eq_refl _). Qed.

(* ============================================================ *)
(* 件 1b：uab_Z_aud == 保留集上完整核质量；投影形态核归一化           *)
(* ============================================================ *)

Theorem real_Z_aud_is_kept_mass : forall prefix : list Token,
  real_eq (uab_Z_aud prefix)
          (real_list_sum Token
             (fun w : Token =>
                match real_minp_keep_dec prefix w with
                | inl _ => real_markov_kernel prefix w
                | inr _ => real_zero
                end) vocab).
Proof.
  intro prefix. unfold uab_Z_aud.
  assert (Hfwd : real_eq (real_list_sum Token
                            (fun w : Token =>
                               match real_minp_keep_dec prefix w with
                               | inl _ => real_markov_kernel prefix w
                               | inr _ => real_zero
                               end) vocab)
                         (real_mult (uab_temp_sum prefix)
                                    (real_inv_pos Z_full uab_Z_full_pos))).
  { apply (real_eq_trans _
             (real_list_sum Token
                (fun w : Token => real_mult (uab_branch prefix w)
                                            (real_inv_pos Z_full uab_Z_full_pos))
                vocab) _).
    - apply (real_list_sum_ext Token
                (fun w : Token =>
                   match real_minp_keep_dec prefix w with
                   | inl _ => real_markov_kernel prefix w
                   | inr _ => real_zero
                   end)
                (fun w : Token => real_mult (uab_branch prefix w)
                                            (real_inv_pos Z_full uab_Z_full_pos))
                vocab).
      intro w. destruct (real_minp_keep_dec prefix w) as [Hk | Hd].
      + unfold real_markov_kernel, uab_branch.
        destruct (real_minp_keep_dec prefix w) as [Hk2 | Hd2].
        * apply real_eq_refl.
        * destruct (Hd2 Hk).
      + unfold uab_branch.
        destruct (real_minp_keep_dec prefix w) as [Hk2 | Hd2].
        * destruct (Hd Hk2).
        * apply (real_eq_sym _ _
                   (real_eq_trans (real_mult real_zero (real_inv_pos Z_full uab_Z_full_pos))
                                  (real_mult (real_inv_pos Z_full uab_Z_full_pos) real_zero)
                                  real_zero
                                  (real_mult_comm real_zero (real_inv_pos Z_full uab_Z_full_pos))
                                  (real_mult_zero (real_inv_pos Z_full uab_Z_full_pos)))).
    - apply (real_eq_trans _
                (real_mult (real_inv_pos Z_full uab_Z_full_pos)
                           (real_list_sum Token (uab_branch prefix) vocab)) _).
      + apply (real_list_sum_linear_r Token (real_inv_pos Z_full uab_Z_full_pos)
                    (uab_branch prefix) vocab).
      + apply (real_eq_trans _
                  (real_mult (real_inv_pos Z_full uab_Z_full_pos) (uab_temp_sum prefix)) _).
        * apply (RealSetoid.real_eq_mult_compat (real_inv_pos Z_full uab_Z_full_pos)
                    (real_list_sum Token (uab_branch prefix) vocab)
                    (real_inv_pos Z_full uab_Z_full_pos) (uab_temp_sum prefix)
                    (real_eq_refl _) (uab_temp_sum_list_bridge prefix)).
        * apply real_mult_comm. }
  exact (real_eq_sym _ _ Hfwd).
Qed.

Theorem real_proj_normalized_list : forall prefix : list Token,
  real_eq (real_list_sum Token (uab_proj_kernel prefix) vocab) real_one.
Proof.
  intro prefix.
  apply (real_eq_trans _ (real_list_sum Token (uab_minp_kernel prefix) vocab) _).
  - apply (real_list_sum_ext Token (uab_proj_kernel prefix) (uab_minp_kernel prefix) vocab).
    intro w. apply (real_eq_sym _ _ (real_minp_kernel_is_projection prefix w)).
  - exact (real_minp_markov_kernel_normalized Token vocab real_temp_factor
             real_minp_keep real_minp_keep_dec uab_temp_sum_pos prefix).
Qed.

(* ============================================================ *)
(* 件 5（hlogz 接入）：uab_Z_aud ≤ 1 ⟹ log uab_Z_aud ≤ 0 ⟹ 代价项非负    *)
(* ============================================================ *)

Theorem real_Z_aud_le_one : forall prefix : list Token,
  real_le (uab_Z_aud prefix) real_one.
Proof.
  intro prefix.
  assert (Hpt : forall w : Token,
             real_le (match real_minp_keep_dec prefix w with
                      | inl _ => real_temp_factor w
                      | inr _ => real_zero
                      end) (real_temp_factor w)).
  { intro w. destruct (real_minp_keep_dec prefix w) as [Hk | Hd].
    - apply real_le_refl.
    - apply (RealSetoid.real_lt_le_iff_req real_zero (real_temp_factor w)).
      exact (inl (uab_temp_factor_pos w)). }
  assert (Hsum : real_le (uab_temp_sum prefix) Z_full).
  { unfold uab_temp_sum, real_minp_temp_sum, Z_full.
    apply (real_list_sum_le Token
             (fun w : Token =>
                match real_minp_keep_dec prefix w with
                | inl _ => real_temp_factor w
                | inr _ => real_zero
                end) real_temp_factor vocab Hpt). }
  unfold uab_Z_aud.
  apply (RealSetoid.real_le_id_r
           (real_mult (uab_temp_sum prefix) (real_inv_pos Z_full uab_Z_full_pos))
           (real_mult Z_full (real_inv_pos Z_full uab_Z_full_pos)) real_one
           (real_inv_pos_correct Z_full uab_Z_full_pos)).
  apply (real_le_mult_compat (uab_temp_sum prefix) Z_full
           (real_inv_pos Z_full uab_Z_full_pos)
           (real_inv_pos_pos Z_full uab_Z_full_pos) Hsum).
Qed.

Theorem real_log_Z_aud_le_zero : forall prefix : list Token,
  real_le (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)) real_zero.
Proof.
  intro prefix.
  pose proof (real_Z_aud_le_one prefix) as HZ1.
  unfold real_le in HZ1. destruct HZ1 as [Hlt | Heq].
  - apply (RealSetoid.real_le_id_r (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix))
             (real_log real_one real_lt_zero_one) real_zero (real_log_one real_lt_zero_one)).
    apply (RealSetoid.real_lt_le_iff_req (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix))
             (real_log real_one real_lt_zero_one)).
    exact (inl (real_log_lt_mono (uab_Z_aud prefix) real_one
                  (uab_Z_aud_pos_cert prefix) real_lt_zero_one Hlt)).
  - apply (RealSetoid.real_eq_le (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)) real_zero).
    apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
    + apply (real_log_wd (uab_Z_aud prefix) real_one
               (uab_Z_aud_pos_cert prefix) real_lt_zero_one Heq).
    + apply (real_log_one real_lt_zero_one).
Qed.

Theorem real_opp_log_Z_aud_nonneg : forall prefix : list Token,
  real_le real_zero (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix))).
Proof.
  intro prefix.
  apply (RealSetoid.real_le_id_l real_zero (real_opp real_zero)
           (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
           (real_eq_sym real_zero (real_opp real_zero) real_opp_zero)).
  apply (real_opp_le_compat (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)) real_zero).
  exact (real_log_Z_aud_le_zero prefix).
Qed.

(* ============================================================ *)
(* 件 2：list-KL 分解恒等式（kl_sum_split / kl_tail_eval 骨架的   *)
(*       list Token 世界复刻）                                   *)
(*   求和项按 keep_dec 分支；drop 支两侧归零；证书全透明          *)
(* ============================================================ *)

(* KL 求和项（q 对完整核） *)
Definition uab_kl_q_full (prefix : list Token) (q : Token -> Real)
  (Hq : forall w : Token, real_minp_keep prefix w -> real_lt real_zero (q w))
  (w : Token) : Real :=
  match real_minp_keep_dec prefix w with
  | inl Hk =>
      real_mult (q w)
        (real_plus (real_log (q w) (Hq w Hk))
                   (real_opp (real_log (real_mult (real_temp_factor w)
                                                  (real_inv_pos Z_full uab_Z_full_pos))
                                       (uab_full_pos_cert prefix w))))
  | inr _ => real_zero
  end.

(* KL 求和项（q 对 min-p 核 keep 支形态） *)
Definition uab_kl_q_minp (prefix : list Token) (q : Token -> Real)
  (Hq : forall w : Token, real_minp_keep prefix w -> real_lt real_zero (q w))
  (w : Token) : Real :=
  match real_minp_keep_dec prefix w with
  | inl Hk =>
      real_mult (q w)
        (real_plus (real_log (q w) (Hq w Hk))
                   (real_opp (real_log (real_mult (real_temp_factor w)
                                                  (real_inv_pos (uab_temp_sum prefix)
                                                                (uab_temp_sum_pos prefix)))
                                       (uab_minp_pos_cert prefix w))))
  | inr _ => real_zero
  end.


Definition uab_kl_tail (prefix : list Token) (q : Token -> Real)
  (Hq : forall w : Token, real_minp_keep prefix w -> real_lt real_zero (q w))
  (w : Token) : Real :=
  match real_minp_keep_dec prefix w with
  | inl _ =>
      real_mult (q w)
        (real_plus (real_log (real_mult (real_temp_factor w)
                                        (real_inv_pos (uab_temp_sum prefix)
                                                      (uab_temp_sum_pos prefix)))
                             (uab_minp_pos_cert prefix w))
                   (real_opp (real_log (real_mult (real_temp_factor w)
                                                  (real_inv_pos Z_full uab_Z_full_pos))
                                       (uab_full_pos_cert prefix w))))
  | inr _ => real_zero
  end.

(* a − c == (a − b) + (b − c)（real_eq 形态，root kl_minus_split 的 list 版） *)
Lemma uab_minus_split : forall a b c : Real,
  real_eq (real_plus a (real_opp c))
          (real_plus (real_plus a (real_opp b)) (real_plus b (real_opp c))).
Proof.
  intros a b c.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp b) (real_plus b (real_opp c)))) _).
  - apply (RealSetoid.real_eq_plus_compat a (real_opp c) a
             (real_plus (real_opp b) (real_plus b (real_opp c)))
             (real_eq_refl a)
             (real_eq_sym _ _
               (real_eq_trans (real_plus (real_opp b) (real_plus b (real_opp c)))
                              (real_plus (real_plus (real_opp b) b) (real_opp c))
                              (real_opp c)
                              (real_plus_assoc (real_opp b) b (real_opp c))
                              (real_eq_trans
                                 (real_plus (real_plus (real_opp b) b) (real_opp c))
                                 (real_plus real_zero (real_opp c))
                                 (real_opp c)
                                 (RealSetoid.real_eq_plus_compat
                                    (real_plus (real_opp b) b) (real_opp c)
                                    real_zero (real_opp c)
                                    (uab_plus_zero_opp b) (real_eq_refl _))
                                 (uab_plus_zero_l (real_opp c)))))).
  - apply (real_plus_assoc a (real_opp b) (real_plus b (real_opp c))).
Qed.


Lemma uab_kl_pointwise_split : forall (prefix : list Token) (q : Token -> Real)
  (Hq : forall w : Token, real_minp_keep prefix w -> real_lt real_zero (q w)) (w : Token),
  real_eq (uab_kl_q_full prefix q Hq w)
          (real_plus (uab_kl_q_minp prefix q Hq w) (uab_kl_tail prefix q Hq w)).
Proof.
  intros prefix q Hq w.
  unfold uab_kl_q_full, uab_kl_q_minp, uab_kl_tail.
  destruct (real_minp_keep_dec prefix w) as [Hk | Hd].
  - (* q·(L − F) == q·((L − M) + (M − F)) == q·(L − M) + q·(M − F) *)
    apply (real_eq_trans _
             (real_mult (q w)
                (real_plus (real_plus (real_log (q w) (Hq w Hk))
                                      (real_opp (real_log (real_mult (real_temp_factor w)
                                                                      (real_inv_pos (uab_temp_sum prefix)
                                                                                       (uab_temp_sum_pos prefix)))
                                                          (uab_minp_pos_cert prefix w))))
                           (real_plus (real_log (real_mult (real_temp_factor w)
                                                           (real_inv_pos (uab_temp_sum prefix)
                                                                         (uab_temp_sum_pos prefix)))
                                                (uab_minp_pos_cert prefix w))
                                      (real_opp (real_log (real_mult (real_temp_factor w)
                                                                      (real_inv_pos Z_full
                                                                                       uab_Z_full_pos))
                                                           (uab_full_pos_cert prefix w)))))) _).
    + apply (RealSetoid.real_eq_mult_compat (q w)
               (real_plus (real_log (q w) (Hq w Hk))
                          (real_opp (real_log (real_mult (real_temp_factor w)
                                                          (real_inv_pos Z_full uab_Z_full_pos))
                                       (uab_full_pos_cert prefix w))))
               (q w)
               (real_plus (real_plus (real_log (q w) (Hq w Hk))
                                     (real_opp (real_log (real_mult (real_temp_factor w)
                                                                     (real_inv_pos (uab_temp_sum prefix)
                                                                                   (uab_temp_sum_pos prefix)))
                                                         (uab_minp_pos_cert prefix w))))
                          (real_plus (real_log (real_mult (real_temp_factor w)
                                                          (real_inv_pos (uab_temp_sum prefix)
                                                                        (uab_temp_sum_pos prefix)))
                                                       (uab_minp_pos_cert prefix w))
                                     (real_opp (real_log (real_mult (real_temp_factor w)
                                                                     (real_inv_pos Z_full
                                                                                      uab_Z_full_pos))
                                                          (uab_full_pos_cert prefix w)))))
               (real_eq_refl _)
               (uab_minus_split (real_log (q w) (Hq w Hk))
                  (real_log (real_mult (real_temp_factor w)
                                       (real_inv_pos (uab_temp_sum prefix)
                                                     (uab_temp_sum_pos prefix)))
                            (uab_minp_pos_cert prefix w))
                  (real_log (real_mult (real_temp_factor w)
                                       (real_inv_pos Z_full uab_Z_full_pos))
                            (uab_full_pos_cert prefix w)))).
    + apply (real_distrib (q w)
                  (real_plus (real_log (q w) (Hq w Hk))
                             (real_opp (real_log (real_mult (real_temp_factor w)
                                                             (real_inv_pos (uab_temp_sum prefix)
                                                                           (uab_temp_sum_pos prefix)))
                                                 (uab_minp_pos_cert prefix w))))
                  (real_plus (real_log (real_mult (real_temp_factor w)
                                                  (real_inv_pos (uab_temp_sum prefix)
                                                                (uab_temp_sum_pos prefix)))
                                               (uab_minp_pos_cert prefix w))
                             (real_opp (real_log (real_mult (real_temp_factor w)
                                                             (real_inv_pos Z_full uab_Z_full_pos))
                                                  (uab_full_pos_cert prefix w))))).
  - apply (real_eq_sym _ _ (real_plus_zero real_zero)).
Qed.

(* 和级分解（尾项未求值形态）：Σ q‖full == Σ q‖minp + Σ tail *)
Lemma uab_kl_sum_split : forall (prefix : list Token) (q : Token -> Real)
  (Hq_norm : real_eq (real_list_sum Token q vocab) real_one)
  (Hq_pos : forall w : Token, real_minp_keep prefix w -> real_lt real_zero (q w))
  (Hq_fail : forall w : Token, Not (real_minp_keep prefix w) -> real_eq (q w) real_zero),
  real_eq (real_list_sum Token (uab_kl_q_full prefix q Hq_pos) vocab)
          (real_plus (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                     (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab)).
Proof.
  intros prefix q Hq_norm Hq_pos Hq_fail.
  apply (real_eq_trans _
           (real_list_sum Token
              (fun w : Token => real_plus (uab_kl_q_minp prefix q Hq_pos w)
                                          (uab_kl_tail prefix q Hq_pos w)) vocab) _).
  - apply (real_list_sum_ext Token (uab_kl_q_full prefix q Hq_pos)
              (fun w : Token => real_plus (uab_kl_q_minp prefix q Hq_pos w)
                                          (uab_kl_tail prefix q Hq_pos w)) vocab).
    exact (uab_kl_pointwise_split prefix q Hq_pos).
  - apply (real_list_sum_add Token (uab_kl_q_minp prefix q Hq_pos)
              (uab_kl_tail prefix q Hq_pos) vocab).
Qed.


Lemma uab_kl_tail_eval : forall (prefix : list Token) (q : Token -> Real)
  (Hq_norm : real_eq (real_list_sum Token q vocab) real_one)
  (Hq_pos : forall w : Token, real_minp_keep prefix w -> real_lt real_zero (q w))
  (Hq_fail : forall w : Token, Not (real_minp_keep prefix w) -> real_eq (q w) real_zero),
  real_eq (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab)
          (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix))).
Proof.
  intros prefix q Hq_norm Hq_pos Hq_fail.
  assert (Hpt : forall w : Token,
             real_eq (uab_kl_tail prefix q Hq_pos w)
                     (real_mult (real_opp (real_log (uab_Z_aud prefix)
                                                     (uab_Z_aud_pos_cert prefix))) (q w))).
  { intro w. unfold uab_kl_tail.
    destruct (real_minp_keep_dec prefix w) as [Hk | Hd].
    - apply (real_eq_trans _
                (real_mult (q w)
                   (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))) _).
      + apply (RealSetoid.real_eq_mult_compat (q w)
                   (real_plus (real_log (real_mult (real_temp_factor w)
                                                   (real_inv_pos (uab_temp_sum prefix)
                                                                 (uab_temp_sum_pos prefix)))
                                        (uab_minp_pos_cert prefix w))
                              (real_opp (real_log (real_mult (real_temp_factor w)
                                                              (real_inv_pos Z_full
                                                                             uab_Z_full_pos))
                                                   (uab_full_pos_cert prefix w))))
                   (q w)
                   (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                   (real_eq_refl _)
                   (uab_log_minp_minus_full prefix w)).
      + apply real_mult_comm.
    - pose proof (Hq_fail w Hd) as Hq0.
      apply (real_eq_trans real_zero
                (real_mult (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                           real_zero)
                (real_mult (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                           (q w))
                (real_eq_sym _ _
                   (real_mult_zero
                      (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))))
                (RealSetoid.real_eq_mult_compat
                   (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                   real_zero
                   (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                   (q w) (real_eq_refl _) (real_eq_sym (q w) real_zero Hq0))). }
  apply (real_eq_trans _
           (real_list_sum Token
              (fun w : Token =>
                 real_mult (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                           (q w)) vocab) _).
  - apply (real_list_sum_ext Token (uab_kl_tail prefix q Hq_pos)
              (fun w : Token =>
                 real_mult (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                           (q w)) vocab Hpt).
  - apply (real_eq_trans _
              (real_mult (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                         (real_list_sum Token q vocab)) _).
    + apply (real_list_sum_linear Token
                (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix))) q vocab).
    + apply (real_eq_trans _
                (real_mult (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                           real_one) _).
      * apply (RealSetoid.real_eq_mult_compat
                  (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                  (real_list_sum Token q vocab)
                  (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix))) real_one
                  (real_eq_refl _) Hq_norm).
      * apply real_mult_one.
Qed.

(* 件 2 主恒等式（尾项已求值——任务书陈述形态） *)
Theorem real_kl_sum_split_list : forall (prefix : list Token) (q : Token -> Real)
  (Hq_norm : real_eq (real_list_sum Token q vocab) real_one)
  (Hq_pos : forall w : Token, real_minp_keep prefix w -> real_lt real_zero (q w))
  (Hq_fail : forall w : Token, Not (real_minp_keep prefix w) -> real_eq (q w) real_zero),
  real_eq (real_list_sum Token (uab_kl_q_full prefix q Hq_pos) vocab)
          (real_plus (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                     (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))).
Proof.
  intros prefix q Hq_norm Hq_pos Hq_fail.
  apply (real_eq_trans _
           (real_plus (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                      (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab)) _).
  - exact (uab_kl_sum_split prefix q Hq_norm Hq_pos Hq_fail).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _
             (real_eq_refl _) (uab_kl_tail_eval prefix q Hq_norm Hq_pos Hq_fail)).
Qed.

(* ============================================================ *)

(*   即截断代价 = 通过集质量亏损的对数（kept'==uab_Z_aud，参照完整核） *)
(* ============================================================ *)

(* KL(dist‖dist) == 0（自 KL 归零） *)
Lemma uab_kl_self_zero : forall prefix : list Token,
  real_eq (real_list_sum Token
             (uab_kl_q_minp prefix (uab_minp_kernel prefix) (uab_minp_keep_pos prefix)) vocab)
          real_zero.
Proof.
  intro prefix.
  apply (real_eq_trans _ (real_list_sum Token (fun _ : Token => real_zero) vocab) _).
  - apply (real_list_sum_ext Token
              (uab_kl_q_minp prefix (uab_minp_kernel prefix) (uab_minp_keep_pos prefix))
              (fun _ : Token => real_zero) vocab).
    intro w. unfold uab_kl_q_minp.
    (* 全部展开暴露 match，再统一 case 分析（避免 delta 隐藏的 o 阻断抽象） *)
    unfold uab_minp_kernel, real_minp_markov_kernel, uab_minp_keep_pos.
    destruct (real_minp_keep_dec prefix w) as [Hk | Hd].
    + apply (real_eq_trans _
                  (real_mult (real_mult (real_temp_factor w)
                                        (real_inv_pos (uab_temp_sum prefix)
                                                      (uab_temp_sum_pos prefix)))
                             real_zero) _).
      * apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _)
                  (real_plus_opp (real_log (real_mult (real_temp_factor w)
                                                      (real_inv_pos (uab_temp_sum prefix)
                                                                    (uab_temp_sum_pos prefix)))
                                           (uab_minp_pos_cert prefix w)))).
      * apply real_mult_zero.
    + apply real_eq_refl.
  - apply uab_list_sum_zero.
Qed.

Theorem real_minp_kl_cost : forall prefix : list Token,
  real_eq (real_list_sum Token
             (uab_kl_q_full prefix (uab_minp_kernel prefix) (uab_minp_keep_pos prefix)) vocab)
          (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix))).
Proof.
  intro prefix.
  pose proof (uab_kl_sum_split prefix (uab_minp_kernel prefix)
                (real_minp_markov_kernel_normalized Token vocab real_temp_factor
                   real_minp_keep real_minp_keep_dec uab_temp_sum_pos prefix)
                (uab_minp_keep_pos prefix) (uab_minp_fail_zero prefix)) as Hsplit.
  pose proof (uab_kl_tail_eval prefix (uab_minp_kernel prefix)
                (real_minp_markov_kernel_normalized Token vocab real_temp_factor
                   real_minp_keep real_minp_keep_dec uab_temp_sum_pos prefix)
                (uab_minp_keep_pos prefix) (uab_minp_fail_zero prefix)) as Htail.
  pose proof (uab_kl_self_zero prefix) as Hself.
  apply (real_eq_trans _
           (real_plus (real_list_sum Token
                         (uab_kl_q_minp prefix (uab_minp_kernel prefix)
                                       (uab_minp_keep_pos prefix)) vocab)
                      (real_list_sum Token
                         (uab_kl_tail prefix (uab_minp_kernel prefix)
                                       (uab_minp_keep_pos prefix)) vocab)) _).
  - exact Hsplit.
  - apply (real_eq_trans _
              (real_plus (real_list_sum Token
                            (uab_kl_q_minp prefix (uab_minp_kernel prefix)
                                          (uab_minp_keep_pos prefix)) vocab)
                         (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))) _).
    + apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _) Htail).
    + apply (real_eq_trans _
                (real_plus real_zero
                           (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))) _).
      * apply (RealSetoid.real_eq_plus_compat _ _ _ _ Hself (real_eq_refl _)).
      * apply uab_plus_zero_l.
Qed.

(* ============================================================ *)
(* 件 4（eps 最优性）：KL_list(q ‖ minp) ≤ KL_list(q ‖ full) + eps *)
(*   由件 2 分解 + 尾项 = −log uab_Z_aud ≥ 0（件 5）+ eps 余量；        *)
(*   方向纪律：仅截断侧度量，不主张 KL(full‖minp)。               *)
(* ============================================================ *)

Lemma uab_le_plus_nonneg_r : forall a c : Real,
  real_le real_zero c -> real_le a (real_plus a c).
Proof.
  intros a c H0c.
  apply (RealSetoid.real_le_id_l a (real_plus a real_zero) (real_plus a c)
           (real_eq_sym (real_plus a real_zero) a (real_plus_zero a))).
  apply (real_le_plus_compat a a real_zero c (real_le_refl a) H0c).
Qed.

Theorem real_minp_projection_eps : forall (prefix : list Token) (q : Token -> Real)
  (Hq_norm : real_eq (real_list_sum Token q vocab) real_one)
  (Hq_pos : forall w : Token, real_minp_keep prefix w -> real_lt real_zero (q w))
  (Hq_fail : forall w : Token, Not (real_minp_keep prefix w) -> real_eq (q w) real_zero)
  (eps : Real) (Heps : real_lt real_zero eps),
  real_le (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
          (real_plus (real_list_sum Token (uab_kl_q_full prefix q Hq_pos) vocab) eps).
Proof.
  intros prefix q Hq_norm Hq_pos Hq_fail eps Heps.
  pose proof (uab_kl_sum_split prefix q Hq_norm Hq_pos Hq_fail) as Hsplit.
  pose proof (uab_kl_tail_eval prefix q Hq_norm Hq_pos Hq_fail) as Htail.
  pose proof (real_opp_log_Z_aud_nonneg prefix) as Hnonneg.
  assert (HT : real_le real_zero
                 (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab)).
  { apply (RealSetoid.real_le_id_r real_zero
             (real_opp (real_log (uab_Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
             (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab)
             (real_eq_sym _ _ Htail) Hnonneg). }
  assert (HT2 : real_le real_zero
                  (real_plus (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab) eps)).
  { apply (real_le_plus_compat real_zero
             (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab)
             real_zero eps HT
             (RealSetoid.real_lt_le_iff_req real_zero eps (inl Heps))). }
  assert (H1 : real_le (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                       (real_plus (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                                  (real_plus (real_list_sum Token (uab_kl_tail prefix q Hq_pos)
                                                              vocab)
                                             eps))).
  { apply uab_le_plus_nonneg_r. exact HT2. }
  assert (H2 : real_eq (real_plus (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                                  (real_plus (real_list_sum Token (uab_kl_tail prefix q Hq_pos)
                                                              vocab)
                                             eps))
                       (real_plus (real_list_sum Token (uab_kl_q_full prefix q Hq_pos) vocab)
                                  eps)).
  { apply (real_eq_trans _
              (real_plus (real_plus (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                                    (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab))
                         eps) _).
    - apply (real_plus_assoc (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab) eps).
    - apply (RealSetoid.real_eq_plus_compat _ _ _ _
                (real_eq_sym _ _ Hsplit) (real_eq_refl eps)). }
  apply (RealSetoid.real_le_id_r
           (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
           (real_plus (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                      (real_plus (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab) eps))
           (real_plus (real_list_sum Token (uab_kl_q_full prefix q Hq_pos) vocab) eps)
           H2 H1).
Qed.

End UpAuditBridge.
