(* ============================================================ *)
(* UpReqSampling.v *)
(* *)
(* 目的： 采样核的 req 层镜像：Doeblin 收缩与迭代预算面。 *)
(* 主件： rsq_u_titer / rsq_bs_kernel 迭代核与 rsq_u_tr_decomp 分解。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist。 *)
(* 备注： 参考分布归一化与正性为 Variable 前提；一步分解为构造核。 *)
(* ============================================================ *)

(* UpReqSampling.v — 签名迁移批 4 保底件：UContraction + BoundedSoftmax 的 req 系重述
   母本：签名迁移规划书-20260908.md 批 4 清单（BoundedSoftmax 23 + UContraction 11 = 保底 34 件）；
   Id 原件：CW_ConstructiveWorld_219.v
     Section UContraction     L95737-96039（11 件：Lemma/Theorem 计数，定义件另计）；
     Section BoundedSoftmax   L96043-96356（23 件：21 Lemma + 2 Theorem，定义件另计）。
     UpReqAlgebra（批 1 地基）：req_minus / req_minus_plus_congr_l / req_minus_factor /
       req_minus_factor_pt / req_le_minus_nonneg / req_mult_cancel_l /
       req_lt_id_r_loc / req_two_pos / req_le_mult_compat_r；
     UpReqDist（批 2）：reqd_sum_minus / reqd_nat_to_R / reqd_nat_to_R_pos /
       reqd_minus_compat / reqd_opp_zero / reqd_softmax_scaled / reqd_softmax_temp_param
       （ReqSoftmaxDual 节 = 本文件 BoundedSoftmax 前置锚，规划书明示直接消费）；
     基座：exp_neg_req_compat_setoid（L66223，规划书明示直接消费不再自建桥）。
   ----------------------------------------------------------------
   纪律：纯构造性；Set 层语句（req/lt/le 均 Set 值）；纯 term-mode
   （req_trans 链 + compat 桥，零 Morphisms / 零 rewrite）；诚实接口假设位
   ----------------------------------------------------------------
   诚实签名变化登记表（Id -> req，逐件差异真证非抄写）：
   1. minus：接口无字段，全文件用 UpReqAlgebra req_minus（δ 透明，req_minus a b
     定义性 = plus a (opp b)）——Id 语句中 minus 一处不落。
   2. u_norm / transition_row / 行归一：Id (sum ...) one -> req (sumf ...) one。
   3. abs_ge_zero_id_cc（Id Variable，Id (abs a) a）-> abs_ge_zero_req
     （le zero a -> req (abs a) a）：假设位保留，出口 Id 换 req。
   4. lt_plus_compat_lt_le_h / sum_swap_cc：语句无 Id，逐字同位迁移。
   5. attn_nat_to_R（绑定 Id 接口 plus/one）-> reqd_nat_to_R（绑定 setoid
     运算，UpReqDist 真证件）：nat 到 R 换轨非抄写（UpReqDist 有 plus_hom/
     mult_hom 真证）。
   6. r_pow（Id L14071，绑定 Id 接口 mult/one）-> req_r_pow（本文件头，
     setoid mult/one 同构 Fixpoint 重绑）。
   7. sum_eq_list（req 化）+ enum_nonempty：Not (Id enum nil) -> Not (enum = nil)
     ——req 仅定义在 R 上，list 层恒等走 Stdlib eq（构造性，Prop 位与 Id 原件
     同阶）。
   8. expf 迷你接口（Id 5 假设：pos/zero/plus/mono_lt/mono_le，Part C 消解其
     可满足性）-> 本文件以 setoid exp_neg 具体化 exp_pos_fn := exp_neg (opp x)，
     5 性质全部由接口字段 + exp_neg_req_compat_setoid 真证导出（epp_* 辅件）——
     抽象假设位闭合为接口实例，零新假设（与基内 softmax_setoid 同锚）。
   9. u_titer / u_r_kernel / Zrow / bs_kernel / Unif / delta_star / factor：
     定义件 δ 同构迁移（minus -> req_minus，attn_nat_to_R -> reqd_nat_to_R）。
   ----------------------------------------------------------------
   覆盖核对（req 件名 -> Id 原件 @ 行号）：
   【ReqUContraction 11】u_omd_pos_next<-95773 u_r_nonneg<-95787
     u_r_norm<-95796 u_tr_decomp<-95813 delta_absorb_u<-95833
     u_step_decomp<-95852 u_step_norm<-95991 u_abs_row<-96018
     u_tv_contraction<-96034 u_titer_norm<-96014 u_tv_iter<-96022
   【ReqBoundedSoftmax 23】bs_list_const_sum<-96085 bs_list_le_const<-96104
     bs_list_ge_const<-96121 bs_nR_pos<-96140 bs_lo_pos<-96153 bs_hi_pos<-96156
     bs_opp_lt<-96160 bs_lo_lt_hi<-96168 bs_lo_hi_eq<-96178
     bs_delta_star_lt_one<-96187 bs_inv_hi_lo<-96194 bs_factor_ge_lo<-96202
     bs_factor_le_hi<-96211 bs_Zrow_ge<-96221 bs_Zrow_le<-96229
     bs_Zrow_pos<-96236 bs_kernel_pos<-96247 bs_kernel_nonneg<-96255
     bs_kernel_row<-96260 bs_Unif_norm<-96274 bs_minorization<-96283
     bounded_softmax_tv_contraction<-96328 bounded_softmax_tv_iter<-96341
   【非平凡性分级】真证：u_tv_contraction / u_tv_iter / bs_minorization /
     bs_lo_hi_eq / bs_lo_lt_hi / epp_* 家 / aux_le_mult_nonneg_t12 /
     aux_delta_plus_omd / bs_kernel_eq_reqd_scaled（见证位桥）；
     组装（Id 链 req_trans 逐段重放）：u_r_norm / u_tr_decomp / delta_absorb_u /
     u_step_decomp / u_step_norm / u_abs_row / u_titer_norm / bs_list_* 家 /
     bs_Zrow_* / bs_kernel_row / bs_Unif_norm / bs_factor_* / bs_opp_lt /
     bs_inv_hi_lo / bs_delta_star_lt_one / bs_Zrow_pos / bs_kernel_pos /
     bs_kernel_nonneg / bs_nR_pos；
     幂等δ对偶：u_omd_pos_next 首段（omd δ 展开 req_refl 支路）；
     对位验证（旗舰消费）：bounded_softmax_tv_contraction / bounded_softmax_tv_iter
     （req_u_tv_contraction / req_u_tv_iter 全参对位投喂）。
   【冻结清单】本两节 34 件零冻结（Id 原件全部可 req 重述，无深链缺口）。
     结论留档：Id expf 抽象接口不迁移（由 8 项具体化替代，Part C 消解位
     随之退役，非冻结）。
   ---------------------------------------------------------------- *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* req_r_pow：Id r_pow（L14071）的 setoid 重绑（签名变化 6） *)
Fixpoint req_r_pow {R : Set} {RIS : RealInterfaceEnhancedSetoid R}
         (x : R) (n : nat) : R :=
  match n with
  | 0%nat => one
  | Datatypes.S m => mult x (req_r_pow x m)
  end.

(* ============================================================ *)
(* Section ReqUContraction：UContraction 节 req 迁移（11 件）      *)
(*   Id 原件 L95737-96039。求和诚实接口 = Id SumOver 类字段      *)
(*   （L1400-1441）req 镜像，节内自持（跨席 Hypothesis 不可消费  *)

(* ============================================================ *)
Section ReqUContraction.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- 求和诚实接口（Id SumOver 字段 req 镜像，逐位） ---- *)
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
(* 求和三角：|Σ f| ≤ Σ |f|（Id SumOver abs_sum_le 字段 req 镜像） *)
Hypothesis abs_sum_le_h :
  forall f : S -> R, le (abs (sumf f)) (sumf (fun s : S => abs (f s))).

(* Σ(f−g) == Σf − Σg：消费 UpReqDist reqd_sum_minus（零新假设；签名变化 1） *)
Let sum_minus :=
  reqd_sum_minus S sumf sum_ext sum_add sum_linear.

Variable u : S -> R.
Variable u_norm : req (sumf u) one.
Variable delta : R.
Variable delta_lt_one : lt delta one.
Variable transition : S -> S -> R.
Variable transition_nonneg : forall s s' : S, le zero (transition s s').
Variable transition_row :
  forall s : S, req (sumf (fun s' : S => transition s s')) one.
Variable minorization : forall s s' : S, le (mult delta (u s')) (transition s s').
Variable sum_swap_cc : forall f : S -> S -> R,
  req (sumf (fun s : S => sumf (fun s' : S => f s s')))
      (sumf (fun s' : S => sumf (fun s : S => f s s'))).
Variable abs_ge_zero_req : forall a : R, le zero a -> req (abs a) a.
Variable lt_plus_compat_lt_le_h : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

Let omd := req_minus one delta.

(* 1−δ > 0（Id @95773；幂等δ对偶首段：omd δ 展开 req_refl 支路） *)
Lemma rsq_u_omd_pos_next : lt zero omd.
Proof.
  apply (lt_id_l zero (plus delta (opp delta)) omd
                 (req_sym _ _ (plus_opp delta))
                 (lt_plus_compat_lt_le_h delta one (opp delta) (opp delta)
                                         delta_lt_one (le_refl (opp delta)))).
Qed.

Let inv_omd := inv_pos omd rsq_u_omd_pos_next.

(* aux_delta_plus_omd：δ + (1−δ) == 1（delta_absorb_u / u_step_norm 共用尾链） *)
Lemma aux_delta_plus_omd : req (plus delta omd) one.
Proof.
  apply (req_trans _ (plus (plus delta one) (opp delta)) _).
  - exact (plus_assoc delta one (opp delta)).
  - apply (req_trans (plus (plus delta one) (opp delta))
                     (plus (plus one delta) (opp delta)) _).
    + exact (req_plus_compat (plus delta one) (plus one delta)
                (opp delta) (opp delta)
                (plus_comm delta one) (req_refl (opp delta))).
    + apply (req_trans (plus (plus one delta) (opp delta))
                       (plus one (plus delta (opp delta))) _).
      * exact (req_sym _ _ (plus_assoc one delta (opp delta))).
      * apply (req_trans (plus one (plus delta (opp delta)))
                         (plus one zero) one).
        -- exact (req_plus_compat one one (plus delta (opp delta)) zero
                     (req_refl one) (plus_opp delta)).
        -- exact (plus_zero one).
Qed.

(* 辅件（真证）：lt·le 双非负乘法（Id 接口件 le_mult_nonneg_t12 的 req
   重建；UpReqAlgebra 无现成件——le_mult_compat_weak 右乘位 + 双 req 换元） *)
Lemma aux_le_mult_nonneg_t12 :
  forall a b : R, lt zero a -> le zero b -> le zero (mult a b).
Proof.
  intros a b Ha Hb.
  apply (le_id_r zero (mult b a) (mult a b) (mult_comm b a)).
  apply (le_id_l zero (mult zero a) (mult b a)).
  - exact (req_sym (mult zero a) zero
             (req_trans (mult zero a) (mult a zero) zero
                        (mult_comm zero a) (mult_zero a))).
  - exact (le_mult_compat_weak zero b a (lt_le_iff zero a (inl Ha)) Hb).
Qed.

Definition rsq_u_r_kernel (s s' : S) : R :=
  mult inv_omd (req_minus (transition s s') (mult delta (u s'))).

(* R 核逐点非负（Id @95787） *)
Lemma rsq_u_r_nonneg : forall s s' : S, le zero (rsq_u_r_kernel s s').
Proof.
  intros s s'. unfold rsq_u_r_kernel.
  apply (aux_le_mult_nonneg_t12 inv_omd
                                (req_minus (transition s s') (mult delta (u s')))).
  - exact (inv_pos_pos omd rsq_u_omd_pos_next).
  - exact (req_le_minus_nonneg (mult delta (u s')) (transition s s')
                               (minorization s s')).
Qed.

(* R 核行归一（Id @95796；组装：Id 链 req_trans 逐段重放） *)
Lemma rsq_u_r_norm : forall s : S, req (sumf (fun s' : S => rsq_u_r_kernel s s')) one.
Proof.
  intro s. unfold rsq_u_r_kernel.
  apply (req_trans _ (mult inv_omd
         (sumf (fun s' : S => req_minus (transition s s') (mult delta (u s'))))) _).
  - exact (sum_linear inv_omd
            (fun s' : S => req_minus (transition s s') (mult delta (u s')))).
  - apply (req_trans _ (mult inv_omd
           (req_minus (sumf (fun s' : S => transition s s'))
                      (sumf (fun s' : S => mult delta (u s'))))) _).
    + exact (req_mult_compat inv_omd inv_omd
               (sumf (fun s' : S => req_minus (transition s s') (mult delta (u s'))))
               (req_minus (sumf (fun s' : S => transition s s'))
                          (sumf (fun s' : S => mult delta (u s'))))
               (req_refl inv_omd)
               (sum_minus (fun s' : S => transition s s')
                          (fun s' : S => mult delta (u s')))).
    + apply (req_trans _ (mult inv_omd (req_minus one (mult delta one))) _).
      * exact (req_mult_compat inv_omd inv_omd
                 (req_minus (sumf (fun s' : S => transition s s'))
                            (sumf (fun s' : S => mult delta (u s'))))
                 (req_minus one (mult delta one))
                 (req_refl inv_omd)
                 (reqd_minus_compat (sumf (fun s' : S => transition s s')) one
                                    (sumf (fun s' : S => mult delta (u s')))
                                    (mult delta one)
                                    (transition_row s)
                                    (req_trans (sumf (fun s' : S => mult delta (u s')))
                                               (mult delta (sumf u)) (mult delta one)
                                               (sum_linear delta u)
                                               (req_mult_compat delta delta (sumf u) one
                                                                (req_refl delta) u_norm)))).
      * apply (req_trans _ (mult inv_omd omd) _).
        -- exact (req_mult_compat inv_omd inv_omd
                    (req_minus one (mult delta one)) omd
                    (req_refl inv_omd)
                    (reqd_minus_compat one one (mult delta one) delta
                                       (req_refl one) (mult_one delta))).
        -- exact (req_trans (mult inv_omd omd) (mult omd inv_omd) one
                   (mult_comm inv_omd omd)
                   (inv_pos_correct omd rsq_u_omd_pos_next)).
Qed.

(* T == δ·u + (1−δ)·R（Id @95813） *)
Lemma rsq_u_tr_decomp : forall s s' : S,
  req (transition s s')
      (plus (mult delta (u s')) (mult omd (rsq_u_r_kernel s s'))).
Proof.
  intros s s'. unfold rsq_u_r_kernel.
  assert (Habs : req (mult omd (mult inv_omd
                          (req_minus (transition s s') (mult delta (u s')))))
                     (req_minus (transition s s') (mult delta (u s')))).
  { apply (req_trans _ (mult (mult omd inv_omd)
           (req_minus (transition s s') (mult delta (u s')))) _).
    - exact (mult_assoc omd inv_omd
               (req_minus (transition s s') (mult delta (u s')))).
    - apply (req_trans _ (mult one
             (req_minus (transition s s') (mult delta (u s')))) _).
      + exact (req_mult_compat (mult omd inv_omd) one
                  (req_minus (transition s s') (mult delta (u s')))
                  (req_minus (transition s s') (mult delta (u s')))
                  (inv_pos_correct omd rsq_u_omd_pos_next) (req_refl _)).
      + exact (req_mult_one_l (req_minus (transition s s') (mult delta (u s')))). }
  assert (H1 : req (transition s s')
                   (plus (mult delta (u s'))
                         (req_minus (transition s s') (mult delta (u s'))))).
  { exact (req_sym _ _ (req_minus_plus_cancel (mult delta (u s')) (transition s s'))). }
  assert (H2 : req (plus (mult delta (u s'))
                         (req_minus (transition s s') (mult delta (u s'))))
                  (plus (mult delta (u s'))
                        (mult omd (mult inv_omd
                           (req_minus (transition s s') (mult delta (u s'))))))).
  { apply (req_plus_compat (mult delta (u s')) (mult delta (u s'))).
    - exact (req_refl _).
    - exact (req_sym _ _ Habs). }
  exact (req_trans _ _ _ H1 H2).
Qed.

(* δ·a + (1−δ)·a == a（Id @95833；消费 aux_delta_plus_omd） *)
Lemma rsq_delta_absorb_u : forall a : R,
  req (plus (mult delta a) (mult omd a)) a.
Proof.
  intro a.
  apply (req_trans _ (plus (mult a delta) (mult a omd)) _).
  - exact (req_plus_compat (mult delta a) (mult a delta)
              (mult omd a) (mult a omd)
              (mult_comm delta a) (mult_comm omd a)).
  - apply (req_trans _ (mult a (plus delta omd)) _).
    + exact (req_sym _ _ (distrib a delta omd)).
    + apply (req_trans _ (mult a one) _).
      * exact (req_mult_compat a a (plus delta omd) one (req_refl a)
                 aux_delta_plus_omd).
      * exact (mult_one a).
Qed.

Let u_step (mu : S -> R) (s' : S) : R :=
  sumf (fun s : S => mult (mu s) (transition s s')).

(* 单步分解：Tμ == δ·u + (1−δ)·Rμ（Id @95852） *)
Lemma rsq_u_step_decomp : forall (mu : S -> R) (s' : S),
  req (sumf mu) one ->
  req (u_step mu s')
      (plus (mult delta (u s'))
            (mult omd (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))).
Proof.
  intros mu s' Hmu. unfold u_step.
  apply (req_trans _ (sumf (fun s : S => mult (mu s)
         (plus (mult delta (u s')) (mult omd (rsq_u_r_kernel s s'))))) _).
  - exact (sum_ext (fun s : S => mult (mu s) (transition s s'))
                   (fun s : S => mult (mu s)
                      (plus (mult delta (u s')) (mult omd (rsq_u_r_kernel s s'))))
                   (fun s : S => req_mult_compat (mu s) (mu s) (transition s s')
                      (plus (mult delta (u s')) (mult omd (rsq_u_r_kernel s s')))
                      (req_refl (mu s)) (rsq_u_tr_decomp s s'))).
  - apply (req_trans _ (sumf (fun s : S =>
           plus (mult (mu s) (mult delta (u s')))
                (mult (mu s) (mult omd (rsq_u_r_kernel s s'))))) _).
    + exact (sum_ext (fun s : S => mult (mu s)
                        (plus (mult delta (u s')) (mult omd (rsq_u_r_kernel s s'))))
                     (fun s : S => plus (mult (mu s) (mult delta (u s')))
                                        (mult (mu s) (mult omd (rsq_u_r_kernel s s'))))
                     (fun s : S => distrib (mu s) (mult delta (u s'))
                                           (mult omd (rsq_u_r_kernel s s')))).
    + apply (req_trans _ (plus (sumf (fun s : S => mult (mu s) (mult delta (u s'))))
                               (sumf (fun s : S => mult (mu s) (mult omd (rsq_u_r_kernel s s'))))) _).
      * exact (sum_add (fun s : S => mult (mu s) (mult delta (u s')))
                       (fun s : S => mult (mu s) (mult omd (rsq_u_r_kernel s s')))).
      * assert (Hfirst : req (sumf (fun s : S => mult (mu s) (mult delta (u s'))))
                             (mult delta (u s'))).
        { apply (req_trans _ (sumf (fun s : S => mult (mult (mu s) delta) (u s'))) _).
          - exact (sum_ext (fun s : S => mult (mu s) (mult delta (u s')))
                           (fun s : S => mult (mult (mu s) delta) (u s'))
                           (fun s : S => mult_assoc (mu s) delta (u s'))).
          - apply (req_trans _ (sumf (fun s : S => mult (mult delta (mu s)) (u s'))) _).
            + exact (sum_ext (fun s : S => mult (mult (mu s) delta) (u s'))
                             (fun s : S => mult (mult delta (mu s)) (u s'))
                             (fun s : S => req_mult_compat (mult (mu s) delta)
                                (mult delta (mu s)) (u s') (u s')
                                (mult_comm (mu s) delta) (req_refl _))).
            + apply (req_trans _ (sumf (fun s : S => mult delta (mult (mu s) (u s')))) _).
              * exact (sum_ext (fun s : S => mult (mult delta (mu s)) (u s'))
                               (fun s : S => mult delta (mult (mu s) (u s')))
                               (fun s : S => req_sym _ _ (mult_assoc delta (mu s) (u s')))).
              * apply (req_trans _ (mult delta (sumf (fun s : S => mult (mu s) (u s')))) _).
                -- exact (sum_linear delta (fun s : S => mult (mu s) (u s'))).
                -- apply (req_mult_compat delta delta
                             (sumf (fun s : S => mult (mu s) (u s'))) (u s')
                             (req_refl delta)).
                   apply (req_trans (sumf (fun s : S => mult (mu s) (u s')))
                                    (mult (u s') (sumf mu)) _).
                   ++ apply (req_trans (sumf (fun s : S => mult (mu s) (u s')))
                                       (sumf (fun s : S => mult (u s') (mu s))) _).
                      ** exact (sum_ext (fun s : S => mult (mu s) (u s'))
                                        (fun s : S => mult (u s') (mu s))
                                        (fun s : S => mult_comm (mu s) (u s'))).
                      ** exact (sum_linear (u s') mu).
                   ++ apply (req_trans _ (mult one (u s')) _).
                      ** exact (req_trans (mult (u s') (sumf mu))
                                 (mult (sumf mu) (u s')) (mult one (u s'))
                                 (mult_comm (u s') (sumf mu))
                                 (req_mult_compat (sumf mu) one (u s') (u s')
                                                  Hmu (req_refl _))).
                      ** exact (req_trans (mult one (u s')) (mult (u s') one) (u s')
                                 (mult_comm one (u s')) (mult_one (u s'))). }
        exact (req_plus_compat (sumf (fun s : S => mult (mu s) (mult delta (u s'))))
                               (mult delta (u s'))
                               (sumf (fun s : S => mult (mu s) (mult omd (rsq_u_r_kernel s s'))))
                               (mult omd (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))
                               Hfirst
                               (req_trans
                                  (sumf (fun s : S =>
                                     mult (mu s) (mult omd (rsq_u_r_kernel s s'))))
                                  (sumf (fun s : S =>
                                     mult omd (mult (mu s) (rsq_u_r_kernel s s'))))
                                  (mult omd
                                     (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))
                                  (sum_ext
                                     (fun s : S => mult (mu s) (mult omd (rsq_u_r_kernel s s')))
                                     (fun s : S => mult omd (mult (mu s) (rsq_u_r_kernel s s')))
                                     (fun s : S =>
                                        req_trans
                                          (mult (mu s) (mult omd (rsq_u_r_kernel s s')))
                                          (mult (mult (mu s) omd) (rsq_u_r_kernel s s'))
                                          (mult omd (mult (mu s) (rsq_u_r_kernel s s')))
                                          (mult_assoc (mu s) omd (rsq_u_r_kernel s s'))
                                          (req_trans
                                             (mult (mult (mu s) omd) (rsq_u_r_kernel s s'))
                                             (mult (mult omd (mu s)) (rsq_u_r_kernel s s'))
                                             (mult omd (mult (mu s) (rsq_u_r_kernel s s')))
                                             (req_mult_compat (mult (mu s) omd)
                                                (mult omd (mu s)) (rsq_u_r_kernel s s')
                                                (rsq_u_r_kernel s s')
                                                (mult_comm (mu s) omd) (req_refl _))
                                             (req_sym _ _
                                                (mult_assoc omd (mu s) (rsq_u_r_kernel s s'))))))
                                  (sum_linear omd
                                     (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))).
Qed.

(* 单步保持归一化（Id @95991） *)
Lemma rsq_u_step_norm : forall mu : S -> R,
  req (sumf mu) one -> req (sumf (fun s' : S => u_step mu s')) one.
Proof.
  intros mu Hmu.
  apply (req_trans _ (sumf (fun s' : S =>
        plus (mult delta (u s'))
             (mult omd (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))))) _).
  - exact (sum_ext (fun s' : S => u_step mu s') (fun s' : S =>
        plus (mult delta (u s'))
             (mult omd (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))))
        (fun s' : S => rsq_u_step_decomp mu s' Hmu)).
  - apply (req_trans _ (plus (sumf (fun s' : S => mult delta (u s')))
        (sumf (fun s' : S => mult omd
                 (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))))) _).
    + exact (sum_add (fun s' : S => mult delta (u s'))
                     (fun s' : S => mult omd
                        (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))).
    + assert (HL : req (sumf (fun s' : S => mult delta (u s'))) (mult delta one)).
      { exact (req_trans (sumf (fun s' : S => mult delta (u s')))
                         (mult delta (sumf u)) (mult delta one)
                         (sum_linear delta u)
                         (req_mult_compat delta delta (sumf u) one
                                          (req_refl delta) u_norm)). }
      assert (HR : req (sumf (fun s' : S => mult omd
                          (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))))
                     (mult omd (sumf mu))).
      { apply (req_trans _ (mult omd
               (sumf (fun s' : S => sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))) _).
        - exact (sum_linear omd
                   (fun s' : S => sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))).
        - apply (req_mult_compat omd omd
                    (sumf (fun s' : S => sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))
                    (sumf mu) (req_refl omd)).
          apply (req_trans (sumf (fun s2 : S => sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s2))))
                           (sumf (fun s : S => sumf (fun s2 : S => mult (mu s) (rsq_u_r_kernel s s2)))) _).
          * exact (req_sym _ _
                      (sum_swap_cc (fun s s2 : S => mult (mu s) (rsq_u_r_kernel s s2)))).
          * apply (req_trans _ (sumf (fun s : S =>
                mult (mu s) (sumf (fun s2 : S => rsq_u_r_kernel s s2)))) _).
            + exact (sum_ext (fun s : S => sumf (fun s2 : S => mult (mu s) (rsq_u_r_kernel s s2)))
                             (fun s : S => mult (mu s) (sumf (fun s2 : S => rsq_u_r_kernel s s2)))
                             (fun s : S => sum_linear (mu s) (fun s2 : S => rsq_u_r_kernel s s2))).
            + apply (req_trans _ (sumf (fun s : S => mult (mu s) one)) _).
              -- exact (sum_ext (fun s : S => mult (mu s) (sumf (fun s2 : S => rsq_u_r_kernel s s2)))
                               (fun s : S => mult (mu s) one)
                               (fun s : S => req_mult_compat (mu s) (mu s)
                                  (sumf (fun s2 : S => rsq_u_r_kernel s s2)) one
                                  (req_refl (mu s)) (rsq_u_r_norm s))).
              -- exact (sum_ext (fun s : S => mult (mu s) one) (fun s : S => mu s)
                               (fun s : S => mult_one (mu s))). }
      apply (req_trans _ (plus (mult delta one) (mult omd (sumf mu))) _).
      * exact (req_plus_compat _ _ _ _ HL HR).
      * apply (req_trans _ (plus delta (mult omd (sumf mu))) _).
        -- exact (req_plus_compat (mult delta one) delta
                      (mult omd (sumf mu)) (mult omd (sumf mu))
                      (mult_one delta) (req_refl _)).
        -- apply (req_trans _ (plus delta omd) _).
           ++ exact (req_plus_compat delta delta
                        (mult omd (sumf mu)) omd (req_refl delta)
                        (req_trans (mult omd (sumf mu)) (mult omd one) omd
                                   (req_mult_compat omd omd (sumf mu) one
                                                    (req_refl omd) Hmu)
                                   (mult_one omd))).
           ++ exact (aux_delta_plus_omd).
Qed.

(* |Σ f·R| ≤ Σ |f|·R（Id @96018） *)
Lemma rsq_u_abs_row : forall (f : S -> R) (s' : S),
  le (abs (sumf (fun s : S => mult (f s) (rsq_u_r_kernel s s'))))
     (sumf (fun s : S => mult (abs (f s)) (rsq_u_r_kernel s s'))).
Proof.
  intros f s'.
  apply (le_id_r (abs (sumf (fun s : S => mult (f s) (rsq_u_r_kernel s s'))))
                 (sumf (fun s : S => abs (mult (f s) (rsq_u_r_kernel s s'))))
                 (sumf (fun s : S => mult (abs (f s)) (rsq_u_r_kernel s s')))).
  - exact (sum_ext (fun s : S => abs (mult (f s) (rsq_u_r_kernel s s')))
                   (fun s : S => mult (abs (f s)) (rsq_u_r_kernel s s'))
                   (fun s : S =>
                      req_trans (abs (mult (f s) (rsq_u_r_kernel s s')))
                                (mult (abs (f s)) (abs (rsq_u_r_kernel s s')))
                                (mult (abs (f s)) (rsq_u_r_kernel s s'))
                                (abs_mult (f s) (rsq_u_r_kernel s s'))
                                (req_mult_compat (abs (f s)) (abs (f s))
                                   (abs (rsq_u_r_kernel s s')) (rsq_u_r_kernel s s')
                                   (req_refl (abs (f s)))
                                   (abs_ge_zero_req (rsq_u_r_kernel s s')
                                                    (rsq_u_r_nonneg s s'))))).
  - exact (abs_sum_le_h (fun s : S => mult (f s) (rsq_u_r_kernel s s'))).
Qed.

Let inv_two := inv_pos (plus one one) req_two_pos.
Let tv_req (mu nu : S -> R) : R :=
  mult inv_two (sumf (fun s : S => abs (req_minus (mu s) (nu s)))).

(* ========== 主定理 A：双点 TV 收缩（无需平稳性）【旗舰 1】==========
   Id @96034。真证：Hpt 逐点链（reqd_minus_compat 换 id_cong2 minus、
   req_minus_plus_congr_l / req_minus_factor / req_minus_factor_pt 换
   Id minus 系）+ abs 见证位（abs_mult + abs_ge_zero_req）+ Hsum 交换链。 *)
Lemma rsq_u_tv_contraction : forall (mu nu : S -> R),
  req (sumf mu) one -> req (sumf nu) one ->
  le (tv_req (u_step mu) (u_step nu)) (mult omd (tv_req mu nu)).
Proof.
  intros mu nu Hmu Hnu.
  assert (Hge : le zero omd).
  { exact (req_le_minus_nonneg delta one (lt_le_iff _ _ (inl delta_lt_one))). }
  assert (Hpt : forall s' : S,
    le (abs (req_minus (u_step mu s') (u_step nu s')))
       (mult omd (sumf (fun s : S =>
          mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s'))))).
  { intro s'.
    assert (Hd : req (req_minus (u_step mu s') (u_step nu s'))
                     (mult omd (sumf (fun s : S =>
                        mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s'))))).
    { apply (req_trans (req_minus (u_step mu s') (u_step nu s'))
             (req_minus (plus (mult delta (u s'))
                              (mult omd (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))))
                        (plus (mult delta (u s'))
                              (mult omd (sumf (fun s : S => mult (nu s) (rsq_u_r_kernel s s')))))) _).
      - exact (reqd_minus_compat (u_step mu s')
                  (plus (mult delta (u s'))
                        (mult omd (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))))
                  (u_step nu s')
                  (plus (mult delta (u s'))
                        (mult omd (sumf (fun s : S => mult (nu s) (rsq_u_r_kernel s s')))))
                  (rsq_u_step_decomp mu s' Hmu) (rsq_u_step_decomp nu s' Hnu)).
      - apply (req_trans _ (req_minus (mult omd
                  (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))
                  (mult omd (sumf (fun s : S => mult (nu s) (rsq_u_r_kernel s s'))))) _).
        + exact (req_minus_plus_congr_l (mult delta (u s'))
                    (mult omd (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))))
                    (mult omd (sumf (fun s : S => mult (nu s) (rsq_u_r_kernel s s'))))).
        + apply (req_trans _ (mult omd (req_minus
                    (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))
                    (sumf (fun s : S => mult (nu s) (rsq_u_r_kernel s s'))))) _).
          * exact (req_minus_factor omd
                      (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))
                      (sumf (fun s : S => mult (nu s) (rsq_u_r_kernel s s')))).
          * apply (req_mult_compat omd omd
                       (req_minus (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))
                                  (sumf (fun s : S => mult (nu s) (rsq_u_r_kernel s s'))))
                       (sumf (fun s : S =>
                          mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s')))
                       (req_refl omd)).
            apply (req_trans (req_minus (sumf (fun s : S => mult (mu s) (rsq_u_r_kernel s s')))
                                        (sumf (fun s : S => mult (nu s) (rsq_u_r_kernel s s'))))
                             (sumf (fun s : S =>
                                req_minus (mult (mu s) (rsq_u_r_kernel s s'))
                                          (mult (nu s) (rsq_u_r_kernel s s')))) _).
            -- exact (req_sym _ _ (sum_minus (fun s : S => mult (mu s) (rsq_u_r_kernel s s'))
                                            (fun s : S => mult (nu s) (rsq_u_r_kernel s s')))).
            -- exact (sum_ext (fun s : S =>
                     req_minus (mult (mu s) (rsq_u_r_kernel s s')) (mult (nu s) (rsq_u_r_kernel s s')))
                              (fun s : S => mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s'))
                              (fun s : S => req_minus_factor_pt (mu s) (nu s) (rsq_u_r_kernel s s'))).
    }
    apply (le_id_l (abs (req_minus (u_step mu s') (u_step nu s')))
                   (mult omd (abs (sumf (fun s : S =>
                      mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s')))))
                   (mult omd (sumf (fun s : S =>
                      mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s'))))).
    - apply (req_trans (abs (req_minus (u_step mu s') (u_step nu s')))
                       (abs (mult omd (sumf (fun s : S =>
                          mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s'))))) _).
      + exact (req_abs_compat (req_minus (u_step mu s') (u_step nu s'))
                  (mult omd (sumf (fun s : S =>
                     mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s')))) Hd).
      + exact (req_trans (abs (mult omd (sumf (fun s : S =>
                   mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s')))))
              (mult (abs omd) (abs (sumf (fun s : S =>
                 mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s'))))) _
              (abs_mult omd (sumf (fun s : S =>
                 mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s'))))
              (req_mult_compat (abs omd) omd
                 (abs (sumf (fun s : S => mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s'))))
                 (abs (sumf (fun s : S => mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s'))))
                 (abs_ge_zero_req omd Hge) (req_refl _))).
    - exact (req_le_mult_compat_r omd
               (abs (sumf (fun s : S => mult (req_minus (mu s) (nu s)) (rsq_u_r_kernel s s'))))
               (sumf (fun s : S => mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s')))
               Hge (rsq_u_abs_row (fun s : S => req_minus (mu s) (nu s)) s')). }
  assert (Hsum : le (sumf (fun s' : S => abs (req_minus (u_step mu s') (u_step nu s'))))
                   (mult omd (sumf (fun s : S => abs (req_minus (mu s) (nu s)))))).
  { apply (le_id_r (sumf (fun s' : S => abs (req_minus (u_step mu s') (u_step nu s'))))
                   (sumf (fun s' : S => mult omd
                            (sumf (fun s : S =>
                               mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s')))))
                   (mult omd (sumf (fun s : S => abs (req_minus (mu s) (nu s)))))).
    - apply (req_trans _ (mult omd (sumf (fun s' : S =>
           sumf (fun s : S => mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s'))))) _).
      + exact (sum_linear omd (fun s' : S =>
            sumf (fun s : S => mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s')))).
      + apply (req_mult_compat omd omd
                  (sumf (fun s' : S =>
                     sumf (fun s : S => mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s'))))
                  (sumf (fun s : S => abs (req_minus (mu s) (nu s))))
                  (req_refl omd)).
        apply (req_trans (sumf (fun s' : S =>
                   sumf (fun s : S => mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s'))))
                         (sumf (fun s : S =>
                   sumf (fun s' : S => mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s')))) _).
        * exact (req_sym _ _
                    (sum_swap_cc (fun s s' : S =>
                       mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s')))).
        * apply (req_trans _ (sumf (fun s : S =>
              mult (abs (req_minus (mu s) (nu s)))
                   (sumf (fun s' : S => rsq_u_r_kernel s s')))) _).
          -- exact (sum_ext (fun s : S =>
                   sumf (fun s' : S => mult (abs (req_minus (mu s) (nu s))) (rsq_u_r_kernel s s')))
                            (fun s : S =>
                   mult (abs (req_minus (mu s) (nu s))) (sumf (fun s' : S => rsq_u_r_kernel s s')))
                            (fun s : S => sum_linear (abs (req_minus (mu s) (nu s)))
                                          (fun s' : S => rsq_u_r_kernel s s'))).
          -- apply (req_trans _ (sumf (fun s : S =>
                   mult (abs (req_minus (mu s) (nu s))) one)) _).
             ++ exact (sum_ext (fun s : S =>
                    mult (abs (req_minus (mu s) (nu s))) (sumf (fun s' : S => rsq_u_r_kernel s s')))
                               (fun s : S => mult (abs (req_minus (mu s) (nu s))) one)
                               (fun s : S => req_mult_compat (abs (req_minus (mu s) (nu s)))
                                  (abs (req_minus (mu s) (nu s)))
                                  (sumf (fun s' : S => rsq_u_r_kernel s s')) one
                                  (req_refl (abs (req_minus (mu s) (nu s)))) (rsq_u_r_norm s))).
             ++ exact (sum_ext (fun s : S => mult (abs (req_minus (mu s) (nu s))) one)
                               (fun s : S => abs (req_minus (mu s) (nu s)))
                               (fun s : S => mult_one (abs (req_minus (mu s) (nu s))))).
    - exact (sum_le _ _ Hpt). }
  apply (le_trans _ (mult inv_two
             (mult omd (sumf (fun s : S => abs (req_minus (mu s) (nu s))))))).
  - exact (req_le_mult_compat_r inv_two
             (sumf (fun s' : S => abs (req_minus (u_step mu s') (u_step nu s'))))
             (mult omd (sumf (fun s : S => abs (req_minus (mu s) (nu s)))))
             (lt_le_iff _ _ (inl (inv_pos_pos (plus one one) req_two_pos))) Hsum).
  - assert (Hswap : req (mult inv_two
                          (mult omd (sumf (fun s : S => abs (req_minus (mu s) (nu s))))))
                        (mult omd (mult inv_two
                          (sumf (fun s : S => abs (req_minus (mu s) (nu s))))))).
    { apply (req_trans _ (mult (mult inv_two omd)
             (sumf (fun s : S => abs (req_minus (mu s) (nu s))))) _).
      + exact (mult_assoc inv_two omd
                 (sumf (fun s : S => abs (req_minus (mu s) (nu s))))).
      + apply (req_trans _ (mult (mult omd inv_two)
               (sumf (fun s : S => abs (req_minus (mu s) (nu s))))) _).
        * exact (req_mult_compat (mult inv_two omd) (mult omd inv_two)
                    (sumf (fun s : S => abs (req_minus (mu s) (nu s))))
                    (sumf (fun s : S => abs (req_minus (mu s) (nu s))))
                    (mult_comm inv_two omd) (req_refl _)).
        * exact (req_sym _ _ (mult_assoc omd inv_two
                    (sumf (fun s : S => abs (req_minus (mu s) (nu s)))))). }
    apply (le_id_l _ _ _ Hswap).
    exact (le_refl _).
Qed.

(* ========== 迭代收缩：几何率 (1−δ)ⁿ ========== *)
Fixpoint rsq_u_titer (n : nat) (mu : S -> R) : S -> R :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => u_step (rsq_u_titer m mu)
  end.

Lemma rsq_u_titer_norm : forall (n : nat) (mu : S -> R),
  req (sumf mu) one -> req (sumf (rsq_u_titer n mu)) one.
Proof.
  intro n. induction n as [| n IH]; intros mu H.
  - exact H.
  - exact (rsq_u_step_norm (rsq_u_titer n mu) (IH mu H)).
Qed.

(* ========== 迭代 TV 收缩【旗舰 2】（Id @96022；真证：
   底 case req 数乘单位换轨 + 递归步 req_le_mult_compat_r 对位） ========== *)
Theorem rsq_u_tv_iter : forall (n : nat) (mu nu : S -> R),
  req (sumf mu) one -> req (sumf nu) one ->
  le (tv_req (rsq_u_titer n mu) (rsq_u_titer n nu))
     (mult (req_r_pow omd n) (tv_req mu nu)).
Proof.
  intro n. induction n as [| n IH]; intros mu nu Hmu Hnu.
  - exact (le_id_l _ _ _
             (req_trans (tv_req mu nu) (mult (tv_req mu nu) one)
                        (mult one (tv_req mu nu))
                        (req_sym _ _ (mult_one (tv_req mu nu)))
                        (mult_comm (tv_req mu nu) one))
             (le_refl (mult one (tv_req mu nu)))).
  - apply (le_trans _ (mult omd (tv_req (rsq_u_titer n mu) (rsq_u_titer n nu)))).
    + exact (rsq_u_tv_contraction (rsq_u_titer n mu) (rsq_u_titer n nu)
              (rsq_u_titer_norm n mu Hmu) (rsq_u_titer_norm n nu Hnu)).
    + exact (le_id_r _ _ _
              (mult_assoc omd (req_r_pow omd n) (tv_req mu nu))
              (req_le_mult_compat_r omd (tv_req (rsq_u_titer n mu) (rsq_u_titer n nu))
                (mult (req_r_pow omd n) (tv_req mu nu))
                (req_le_minus_nonneg delta one (lt_le_iff _ _ (inl delta_lt_one)))
                (IH mu nu Hmu Hnu))).
Qed.

End ReqUContraction.

(* ============================================================ *)
(* Section ReqBoundedSoftmax：BoundedSoftmax 节 req 迁移（23 件）  *)
(*   Id 原件 L96043-96356。expf 迷你接口具体化为 exp_pos_fn       *)
(*   （= exp_neg (opp x)，接口实例即消解）；list 求和机器换轨      *)
(*   reqd_nat_to_R；前置锚 = UpReqDist ReqSoftmaxDual reqd_softmax_*。 *)
(* ============================================================ *)
Section ReqBoundedSoftmax.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- 求和诚实接口（本节所需最小集） ---- *)
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis abs_sum_le_h :
  forall f : S -> R, le (abs (sumf f)) (sumf (fun s : S => abs (f s))).

(* ---- 有限世界数据（Id Variables req 化） ---- *)
Variable enum : list S.
Variable enum_nonempty : Not (enum = nil).
Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable z : S -> S -> R.
Variable z_lb : forall s s' : S, le (opp Delta) (z s s').
Variable z_ub : forall s s' : S, le (z s s') Delta.

(* 诚实接口三件（Id bs_swap/bs_abs/bs_lpc 同位） *)
Variable bs_swap : forall f : S -> S -> R,
  req (sumf (fun s : S => sumf (fun s' : S => f s s')))
      (sumf (fun s' : S => sumf (fun s : S => f s s'))).
Variable bs_abs : forall a : R, le zero a -> req (abs a) a.
Variable bs_lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).

Fixpoint rsq_bs_list_sum (f : S -> R) (l : list S) : R :=
  match l with
  | nil => zero
  | x :: t => plus (f x) (rsq_bs_list_sum f t)
  end.

(* 枚举求和规范化（Id Variable sum_eq_list req 化：签名变化 7） *)
Variable sum_eq_list : forall g : S -> R, req (sumf g) (rsq_bs_list_sum g enum).

(* ---- 构造性指数：exp_neg 具体化（签名变化 8；epp_* 辅件家真证） ---- *)
Definition rsq_exp_pos_fn (x : R) : R := exp_neg (opp x).

Lemma epp_pos : forall x : R, lt zero (rsq_exp_pos_fn x).
Proof. intro x. exact (exp_neg_pos (opp x)). Qed.

Lemma epp_ext : forall x y : R, req x y -> req (rsq_exp_pos_fn x) (rsq_exp_pos_fn y).
Proof.
  intros x y H.
  exact (exp_neg_req_compat_setoid (opp x) (opp y) (req_opp_compat x y H)).
Qed.

Lemma epp_zero : req (rsq_exp_pos_fn zero) one.
Proof.
  exact (req_trans _ _ _
           (exp_neg_req_compat_setoid (opp zero) zero reqd_opp_zero)
           (exp_neg_zero)).
Qed.

Lemma epp_plus : forall a b : R,
  req (rsq_exp_pos_fn (plus a b)) (mult (rsq_exp_pos_fn a) (rsq_exp_pos_fn b)).
Proof.
  intros a b.
  apply (req_trans _ (exp_neg (plus (opp a) (opp b))) _).
  - exact (exp_neg_req_compat_setoid (opp (plus a b)) (plus (opp a) (opp b))
                                      (req_opp_plus a b)).
  - exact (exp_neg_plus (opp a) (opp b)).
Qed.

Lemma epp_mono_lt : forall a b : R, lt a b -> lt (rsq_exp_pos_fn a) (rsq_exp_pos_fn b).
Proof.
  intros a b H. exact (exp_neg_decr (opp b) (opp a) (opp_lt_compat a b H)).
Qed.

Lemma epp_mono_le : forall a b : R, le a b -> le (rsq_exp_pos_fn a) (rsq_exp_pos_fn b).
Proof.
  intros a b H. exact (exp_neg_le_decr (opp b) (opp a) (opp_le_compat a b H)).
Qed.

(* ---- list 求和机器（Id @96085/96104/96121；组装） ---- *)

Lemma rsq_bs_list_const_sum : forall (c : R) (l : list S),
  req (rsq_bs_list_sum (fun _ : S => c) l) (mult (reqd_nat_to_R (length l)) c).
Proof.
  intros c l. induction l as [| x t IH].
  - exact (req_sym _ _ (req_trans (mult zero c) (mult c zero) zero
             (mult_comm zero c) (mult_zero c))).
  - assert (Hstep : req (plus c (rsq_bs_list_sum (fun _ : S => c) t))
                        (plus (mult c one) (mult c (reqd_nat_to_R (length t))))).
    { exact (req_plus_compat c (mult c one) (rsq_bs_list_sum (fun _ : S => c) t)
                             (mult c (reqd_nat_to_R (length t)))
                             (req_sym _ _ (mult_one c))
                             (req_trans _ _ _ IH
                                (mult_comm (reqd_nat_to_R (length t)) c))). }
    apply (req_trans _ (plus (mult c one) (mult c (reqd_nat_to_R (length t)))) _).
    + exact Hstep.
    + apply (req_trans _ (mult c (plus one (reqd_nat_to_R (length t)))) _).
      * exact (req_sym _ _ (distrib c one (reqd_nat_to_R (length t)))).
      * exact (mult_comm c (plus one (reqd_nat_to_R (length t)))).
Qed.

Lemma rsq_bs_list_le_const : forall (f : S -> R) (c : R) (l : list S),
  (forall x : S, le (f x) c) ->
  le (rsq_bs_list_sum f l) (mult (reqd_nat_to_R (length l)) c).
Proof.
  intros f c l H. induction l as [| x t IH].
  - exact (le_id_r zero zero (mult zero c)
             (req_sym _ _ (req_trans (mult zero c) (mult c zero) zero
                        (mult_comm zero c) (mult_zero c)))
             (le_refl zero)).
  - apply (le_id_r (plus (f x) (rsq_bs_list_sum f t))
                   (plus c (mult c (reqd_nat_to_R (length t))))
                   (mult (plus one (reqd_nat_to_R (length t))) c)).
    + exact (req_sym _ _ (req_trans
              (mult (plus one (reqd_nat_to_R (length t))) c)
              (mult c (plus one (reqd_nat_to_R (length t))))
              (plus c (mult c (reqd_nat_to_R (length t))))
              (mult_comm (plus one (reqd_nat_to_R (length t))) c)
              (req_trans (mult c (plus one (reqd_nat_to_R (length t))))
                         (plus (mult c one) (mult c (reqd_nat_to_R (length t))))
                         (plus c (mult c (reqd_nat_to_R (length t))))
                         (distrib c one (reqd_nat_to_R (length t)))
                         (req_plus_compat (mult c one) c
                            (mult c (reqd_nat_to_R (length t)))
                            (mult c (reqd_nat_to_R (length t)))
                            (mult_one c) (req_refl _))))).
    + exact (le_plus_compat (f x) c (rsq_bs_list_sum f t)
                            (mult c (reqd_nat_to_R (length t)))
                            (H x)
                            (le_id_r _ _ _ (mult_comm (reqd_nat_to_R (length t)) c)
                                       IH)).
Qed.

Lemma rsq_bs_list_ge_const : forall (f : S -> R) (c : R) (l : list S),
  (forall x : S, le c (f x)) ->
  le (mult (reqd_nat_to_R (length l)) c) (rsq_bs_list_sum f l).
Proof.
  intros f c l H. induction l as [| x t IH].
  - exact (le_id_l (mult zero c) zero zero
             (req_trans (mult zero c) (mult c zero) zero
                        (mult_comm zero c) (mult_zero c))
             (le_refl zero)).
  - apply (le_id_l (mult (plus one (reqd_nat_to_R (length t))) c)
                   (plus c (mult c (reqd_nat_to_R (length t))))
                   (plus (f x) (rsq_bs_list_sum f t))).
    + exact (req_trans
              (mult (plus one (reqd_nat_to_R (length t))) c)
              (mult c (plus one (reqd_nat_to_R (length t))))
              (plus c (mult c (reqd_nat_to_R (length t))))
              (mult_comm (plus one (reqd_nat_to_R (length t))) c)
              (req_trans (mult c (plus one (reqd_nat_to_R (length t))))
                         (plus (mult c one) (mult c (reqd_nat_to_R (length t))))
                         (plus c (mult c (reqd_nat_to_R (length t))))
                         (distrib c one (reqd_nat_to_R (length t)))
                         (req_plus_compat (mult c one) c
                            (mult c (reqd_nat_to_R (length t)))
                            (mult c (reqd_nat_to_R (length t)))
                            (mult_one c) (req_refl _)))).
    + exact (le_plus_compat c (f x) (mult c (reqd_nat_to_R (length t)))
                            (rsq_bs_list_sum f t)
                            (H x)
                            (le_id_l _ _ _ (req_sym _ _
                               (mult_comm (reqd_nat_to_R (length t)) c)) IH)).
Qed.

Let nR := reqd_nat_to_R (length enum).

Lemma rsq_bs_nR_pos : lt zero nR.
Proof.
  destruct enum as [| x t].
  - destruct (enum_nonempty eq_refl).
  - exact (reqd_nat_to_R_pos (length t)).
Qed.

Let invT := inv_pos temp temp_pos.
Let factor (s s' : S) : R := rsq_exp_pos_fn (mult invT (z s s')).
Let lo := rsq_exp_pos_fn (mult invT (opp Delta)).
Let hi := rsq_exp_pos_fn (mult invT Delta).
Let delta_star := mult lo lo.

Lemma rsq_bs_lo_pos : lt zero lo.
Proof. exact (epp_pos (mult invT (opp Delta))). Qed.

Lemma rsq_bs_hi_pos : lt zero hi.
Proof. exact (epp_pos (mult invT Delta)). Qed.

(* opp Delta < Delta（由 Delta > 0；Id @96160） *)
Lemma rsq_bs_opp_lt : lt (opp Delta) Delta.
Proof.
  apply (le_lt_trans (opp Delta) zero Delta).
  - exact (le_id_r (opp Delta) (opp zero) zero reqd_opp_zero
             (opp_le_compat zero Delta (lt_le_iff _ _ (inl Delta_pos)))).
  - exact Delta_pos.
Qed.

Lemma rsq_bs_lo_lt_hi : lt lo hi.
Proof.
  apply (epp_mono_lt (mult invT (opp Delta)) (mult invT Delta)).
  apply (lt_id_l _ (mult (opp Delta) invT) _ (mult_comm invT (opp Delta))).
  apply (req_lt_id_r_loc _ _ _ (mult_comm Delta invT)).
  exact (lt_mult_compat (opp Delta) Delta invT
                        (inv_pos_pos temp temp_pos) rsq_bs_opp_lt).
Qed.

(* lo·hi == one（exp 同态性；Id @96178；真证） *)
Lemma rsq_bs_lo_hi_eq : req (mult lo hi) one.
Proof.
  apply (req_trans (mult lo hi)
                   (rsq_exp_pos_fn (plus (mult invT (opp Delta)) (mult invT Delta))) _).
  - exact (req_sym _ _ (epp_plus (mult invT (opp Delta)) (mult invT Delta))).
  - apply (req_trans _ (rsq_exp_pos_fn (mult invT (plus (opp Delta) Delta))) _).
    + exact (epp_ext _ _ (req_sym _ _ (distrib invT (opp Delta) Delta))).
    + apply (req_trans _ (rsq_exp_pos_fn (mult invT zero)) _).
      * exact (epp_ext _ _ (req_mult_compat invT invT (plus (opp Delta) Delta)
                               zero (req_refl invT)
                               (req_trans (plus (opp Delta) Delta)
                                          (plus Delta (opp Delta)) zero
                                          (plus_comm (opp Delta) Delta)
                                          (plus_opp Delta)))).
      * apply (req_trans _ (rsq_exp_pos_fn zero) _).
        -- exact (epp_ext _ _ (mult_zero invT)).
        -- exact (req_trans (rsq_exp_pos_fn zero) (exp_neg zero) one
                   (exp_neg_req_compat_setoid (opp zero) zero reqd_opp_zero)
                   (exp_neg_zero)).
Qed.

Lemma rsq_bs_delta_star_lt_one : lt delta_star one.
Proof.
  apply (req_lt_id_r_loc _ _ _ (rsq_bs_lo_hi_eq)).
  apply (req_lt_id_r_loc _ _ _ (mult_comm hi lo)).
  exact (lt_mult_compat lo hi lo rsq_bs_lo_pos rsq_bs_lo_lt_hi).
Qed.

Lemma rsq_bs_inv_hi_lo : req (inv_pos hi rsq_bs_hi_pos) lo.
Proof.
  apply (req_mult_cancel_l hi _ _ rsq_bs_hi_pos).
  exact (req_trans (mult hi (inv_pos hi rsq_bs_hi_pos)) one (mult hi lo)
                   (inv_pos_correct hi rsq_bs_hi_pos)
                   (req_sym _ _ (req_trans (mult hi lo) (mult lo hi) one
                              (mult_comm hi lo) rsq_bs_lo_hi_eq))).
Qed.

(* 因子上下界（Id @96202/96211） *)
Lemma rsq_bs_factor_ge_lo : forall s s' : S, le lo (factor s s').
Proof.
  intros s s'.
  apply (epp_mono_le (mult invT (opp Delta)) (mult invT (z s s'))).
  exact (req_le_mult_compat_r invT (opp Delta) (z s s')
           (lt_le_iff _ _ (inl (inv_pos_pos temp temp_pos))) (z_lb s s')).
Qed.

Lemma rsq_bs_factor_le_hi : forall s s' : S, le (factor s s') hi.
Proof.
  intros s s'.
  apply (epp_mono_le (mult invT (z s s')) (mult invT Delta)).
  exact (req_le_mult_compat_r invT (z s s') Delta
           (lt_le_iff _ _ (inl (inv_pos_pos temp temp_pos))) (z_ub s s')).
Qed.

Definition rsq_Zrow (s : S) : R := sumf (fun s' : S => factor s s').

Lemma rsq_bs_Zrow_ge : forall s : S, le (mult nR lo) (rsq_Zrow s).
Proof.
  intro s.
  apply (le_id_r (mult nR lo) (rsq_bs_list_sum (fun s' : S => factor s s') enum)
                 (rsq_Zrow s)
                 (req_sym _ _ (sum_eq_list (fun s' : S => factor s s')))).
  exact (rsq_bs_list_ge_const (fun s' : S => factor s s') lo enum
                          (fun x : S => rsq_bs_factor_ge_lo s x)).
Qed.

Lemma rsq_bs_Zrow_le : forall s : S, le (rsq_Zrow s) (mult nR hi).
Proof.
  intro s.
  apply (le_id_l (rsq_Zrow s) (rsq_bs_list_sum (fun s' : S => factor s s') enum)
                 (mult nR hi)).
  - exact (sum_eq_list (fun s' : S => factor s s')).
  - exact (rsq_bs_list_le_const (fun s' : S => factor s s') hi enum
                            (fun x : S => rsq_bs_factor_le_hi s x)).
Qed.

Lemma rsq_bs_Zrow_pos : forall s : S, lt zero (rsq_Zrow s).
Proof.
  intro s.
  exact (lt_le_trans zero (mult nR lo) (rsq_Zrow s)
                     (mult_positive nR lo rsq_bs_nR_pos rsq_bs_lo_pos) (rsq_bs_Zrow_ge s)).
Qed.

(* softmax 核（温度 T；Id @96044 定义 req 形） *)
Definition rsq_bs_kernel (s s' : S) : R :=
  mult (factor s s') (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)).

Lemma rsq_bs_kernel_pos : forall s s' : S, lt zero (rsq_bs_kernel s s').
Proof.
  intros s s'. exact (mult_positive (factor s s')
                        (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s))
                        (epp_pos (mult invT (z s s')))
                        (inv_pos_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s))).
Qed.

Lemma rsq_bs_kernel_nonneg : forall s s' : S, le zero (rsq_bs_kernel s s').
Proof.
  intros s s'. exact (lt_le_iff _ _ (inl (rsq_bs_kernel_pos s s'))).
Qed.

Lemma rsq_bs_kernel_row : forall s : S, req (sumf (fun s' : S => rsq_bs_kernel s s')) one.
Proof.
  intro s. unfold rsq_bs_kernel.
  apply (req_trans _ (sumf (fun s' : S =>
        mult (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)) (factor s s'))) _).
  - exact (sum_ext
             (fun s' : S => mult (factor s s') (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)))
             (fun s' : S => mult (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)) (factor s s'))
             (fun s' : S => mult_comm (factor s s')
                                      (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)))).
  - apply (req_trans _
             (mult (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s))
                   (sumf (fun s' : S => factor s s'))) _).
    + exact (sum_linear (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s))
                        (fun s' : S => factor s s')).
    + exact (req_trans _ _ _
               (mult_comm (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)) (rsq_Zrow s))
               (inv_pos_correct (rsq_Zrow s) (rsq_bs_Zrow_pos s))).
Qed.

(* 均匀分布 U = 1/enum 模 *)
Let Unif : S -> R := fun _ : S => inv_pos nR rsq_bs_nR_pos.

Lemma rsq_bs_Unif_norm : req (sumf Unif) one.
Proof.
  apply (req_trans _ (rsq_bs_list_sum Unif enum) _).
  - exact (sum_eq_list Unif).
  - apply (req_trans _
             (mult (reqd_nat_to_R (length enum)) (inv_pos nR rsq_bs_nR_pos)) _).
    + exact (rsq_bs_list_const_sum (inv_pos nR rsq_bs_nR_pos) enum).
    + exact (inv_pos_correct nR rsq_bs_nR_pos).
Qed.

(* ---- 前置锚：消费 UpReqDist ReqSoftmaxDual reqd_softmax_scaled ----
   （幂等δ对偶 + 见证位桥；e^(z/T) = e^(-((-z)/T)) 换位为真证链） *)
Lemma bs_kernel_eq_reqd_scaled :
  forall s s' : S,
    req (rsq_bs_kernel s s')
        (reqd_softmax_scaled S sumf sum_pos invT (fun s0 : S => opp (z s s0)) s').
Proof.
  intros s s'.
  apply (req_trans _ (mult (exp_neg (opp (mult invT (z s s'))))
                           (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s))) _).
  - exact (req_refl (mult (exp_neg (opp (mult invT (z s s'))))
                          (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)))).
  - apply (req_mult_compat _ _ _ _).
    + apply (exp_neg_req_compat_setoid _ _).
      exact (req_sym _ _ (req_opp_mult_l invT (z s s'))).
    + apply (inv_pos_ext (rsq_Zrow s)
                         (sumf (fun s0 : S => exp_neg (mult invT (opp (z s s0)))))
                         (rsq_bs_Zrow_pos s)
                         (sum_pos (fun s0 : S => exp_neg (mult invT (opp (z s s0))))
                                  (fun s0 : S => exp_neg_pos (mult invT (opp (z s s0)))))).
      apply (sum_ext (fun s'0 : S => factor s s'0)
                     (fun s0 : S => exp_neg (mult invT (opp (z s s0))))).
      intro s0.
      exact (req_trans (rsq_exp_pos_fn (mult invT (z s s0)))
                       (exp_neg (opp (mult invT (z s s0))))
                       (exp_neg (mult invT (opp (z s s0))))
                       (req_refl _)
                       (exp_neg_req_compat_setoid (opp (mult invT (z s s0)))
                          (mult invT (opp (z s s0)))
                          (req_sym _ _ (req_opp_mult_l invT (z s s0))))).
Qed.

(* ===== 旗舰核心：显式 Doeblin 下界 =====
   P(s,s') >= del星·U(s')，del星 := lo·lo = e^(-2D/T)（精确，无损耗；Id @96283 真证） *)
Lemma rsq_bs_minorization : forall s s' : S,
  le (mult delta_star (Unif s')) (rsq_bs_kernel s s').
Proof.
  intros s s'.
  assert (Hchain : le (mult lo (inv_pos (mult nR hi)
                              (mult_positive nR hi rsq_bs_nR_pos rsq_bs_hi_pos)))
                      (rsq_bs_kernel s s')).
  { apply (le_trans _ (mult lo (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)))).
    - exact (req_le_mult_compat_r lo
                (inv_pos (mult nR hi) (mult_positive nR hi rsq_bs_nR_pos rsq_bs_hi_pos))
                (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s))
                (lt_le_iff _ _ (inl rsq_bs_lo_pos))
                (inv_pos_le_compat (rsq_Zrow s) (mult nR hi) (rsq_bs_Zrow_pos s)
                                   (mult_positive nR hi rsq_bs_nR_pos rsq_bs_hi_pos)
                                   (rsq_bs_Zrow_le s))).
    - unfold rsq_bs_kernel.
      exact (le_id_l _ _ _ (mult_comm lo (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)))
               (le_id_r _ _ _
                 (req_sym _ _ (mult_comm (factor s s')
                                         (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s))))
                 (req_le_mult_compat_r (inv_pos (rsq_Zrow s) (rsq_bs_Zrow_pos s)) lo
                                   (factor s s')
                                   (lt_le_iff _ _ (inl (inv_pos_pos (rsq_Zrow s)
                                                        (rsq_bs_Zrow_pos s))))
                                   (rsq_bs_factor_ge_lo s s')))). }
  assert (Heq : req (mult delta_star (Unif s'))
                   (mult lo (inv_pos (mult nR hi)
                              (mult_positive nR hi rsq_bs_nR_pos rsq_bs_hi_pos)))).
  { assert (Hd1 : req (mult lo (inv_pos (mult nR hi)
                                   (mult_positive nR hi rsq_bs_nR_pos rsq_bs_hi_pos)))
                      (mult lo (mult (inv_pos nR rsq_bs_nR_pos)
                                     (inv_pos hi rsq_bs_hi_pos)))).
    { exact (req_mult_compat lo lo _ _
               (req_refl lo) (req_inv_pos_mult_distr nR hi rsq_bs_nR_pos rsq_bs_hi_pos)). }
    assert (Hd2 : req (mult lo (mult (inv_pos nR rsq_bs_nR_pos) (inv_pos hi rsq_bs_hi_pos)))
                      (mult (mult lo lo) (inv_pos nR rsq_bs_nR_pos))).
    { apply (req_trans
                (mult lo (mult (inv_pos nR rsq_bs_nR_pos) (inv_pos hi rsq_bs_hi_pos)))
                (mult lo (mult (inv_pos nR rsq_bs_nR_pos) lo)) _).
      - exact (req_mult_compat lo lo _ _ (req_refl lo)
                 (req_mult_compat (inv_pos nR rsq_bs_nR_pos) (inv_pos nR rsq_bs_nR_pos)
                    (inv_pos hi rsq_bs_hi_pos) lo (req_refl _) rsq_bs_inv_hi_lo)).
      - apply (req_trans
                  (mult lo (mult (inv_pos nR rsq_bs_nR_pos) lo))
                  (mult lo (mult lo (inv_pos nR rsq_bs_nR_pos)))
                  (mult (mult lo lo) (inv_pos nR rsq_bs_nR_pos))
                  (req_mult_compat lo lo _ _
                     (req_refl lo) (mult_comm (inv_pos nR rsq_bs_nR_pos) lo))
                  (mult_assoc lo lo (inv_pos nR rsq_bs_nR_pos))). }
    exact (req_sym _ _ (req_trans _ _ _ Hd1 Hd2)). }
  exact (le_id_l _ _ _ Heq Hchain).
Qed.

Let inv_two := inv_pos (plus one one) req_two_pos.
Let tv_req (mu nu : S -> R) : R :=
  mult inv_two (sumf (fun s : S => abs (req_minus (mu s) (nu s)))).
Let k_step (mu : S -> R) (s' : S) : R :=
  sumf (fun s : S => mult (mu s) (rsq_bs_kernel s s')).
Fixpoint k_titer (n : nat) (mu : S -> R) : S -> R :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => k_step (k_titer m mu)
  end.

(* ===== 旗舰定理 1：有界 softmax 核的双点 TV 收缩 =====
   收缩率显式：1 - e^(-2D/T)（Id @96328；对位验证：全参投喂） *)
Theorem rsq_bounded_softmax_tv_contraction : forall (mu nu : S -> R),
  req (sumf mu) one -> req (sumf nu) one ->
  le (tv_req (k_step mu) (k_step nu))
     (mult (req_minus one delta_star) (tv_req mu nu)).
Proof.
  intros mu nu Hmu Hnu.
  exact (rsq_u_tv_contraction S sumf sum_ext sum_linear sum_add sum_le abs_sum_le_h
           Unif rsq_bs_Unif_norm delta_star rsq_bs_delta_star_lt_one
           rsq_bs_kernel rsq_bs_kernel_row rsq_bs_minorization
           bs_swap bs_abs bs_lpc mu nu Hmu Hnu).
Qed.

(* ===== 旗舰定理 2：迭代收缩，显式几何率 (1 - e^(-2D/T))^n ===== *)
Theorem rsq_bounded_softmax_tv_iter : forall (n : nat) (mu nu : S -> R),
  req (sumf mu) one -> req (sumf nu) one ->
  le (tv_req (k_titer n mu) (k_titer n nu))
     (mult (req_r_pow (req_minus one delta_star) n) (tv_req mu nu)).
Proof.
  intros n mu nu Hmu Hnu.
  exact (rsq_u_tv_iter S sumf sum_ext sum_linear sum_add sum_le abs_sum_le_h
           Unif rsq_bs_Unif_norm delta_star rsq_bs_delta_star_lt_one
           rsq_bs_kernel rsq_bs_kernel_row rsq_bs_minorization
           bs_swap bs_abs bs_lpc n mu nu Hmu Hnu).
Qed.

End ReqBoundedSoftmax.
