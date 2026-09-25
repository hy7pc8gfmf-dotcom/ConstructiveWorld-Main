(* ============================================================ *)
(* UpReqFEPAttn.v *)
(* *)
(* 目的： 注意力自由能原理（FEP）的 req 层四件与行视图一件。 *)
(* 主件： req_attention_minimizes_free_energy_unique 与 req_bs_kernel_row_is_softmax_temp 行视图。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist。 *)
(* 备注： 配分正性与 softmax 归一化为接口前提；签名变化以登记表申报（δ 记账）。 *)
(* ============================================================ *)

(* ============================================================ *)

(*                                                              *)
(* Id 原件定位（grep 实证）：                                     *)
(*   Section FEPAttention：L112164-112252 ≡ G01_CoreMicro.v Part1   *)
(*     （fep_partition_condition L112193 / fep_align L112201 /    *)
(*      fep_F_ext L112211 / 旗舰 attention_minimizes_free_energy_ *)
(*      unique L112225）；                                        *)
(*   Section RowView：L112256-112304 ≡ G01_CoreMicro.v Part2        *)
(*     （bs_kernel_row_is_softmax_temp L112281）；                *)
(*   Section FEPLogZ：Module UpExtras219 内 L114023-114099  *)
(*     （fep_partition_condition L114054 / fep_align L114063 /    *)
(*      fep_F_ext L114073 / 旗舰 free_energy_softmax_eq_neg_T_    *)
(*      logZ L114089）——D.3 交接提到的「G01_CoreMicro.v 对位」经核验：    *)
(*      FEPAttention/RowView 与 G01_CoreMicro.v 逐字同构，FEPLogZ 不在     *)
(*      G01_CoreMicro.v，在基座 UpExtras219（fep_F_ext 较弱：无归一前提）。*)
(*                                                              *)

(*     req_min_free_energy_is_boltzmann（无条件形态，探针签名      *)



(*     req_boltzmann_positive / req_boltzmann_normalized；        *)
(*   基座 Setoid 节 exp_neg_req_compat_setoid（L66223）为证明件，  *)

(*                                                              *)
(* 诚实签名变化登记表（δ 记账）：                                   *)
(*   1. log 前提化：req 侧 log 带 lt zero 前提，自由能 F_attn 对    *)
(*      逐点正性位 (forall s, lt zero (p s)) 显式收参（Id 系       *)
(*      reqd_normalized 前提在 req_fep_F_ext 保留为 raw req 形          *)
(*      req (sumf p) one 位，旗舰按 Id 证明路径真实消费面收参）。   *)
(*   2. RowView 参数位剪除：Id bs_kernel 的 enum/enum_nonempty/    *)
(*      Delta/z_lb/expf_mono_le/sum_eq_list 六位为其他引理服务，   *)
(*      行等式证明路径仅消费 expf/expf_pos/expf_agree 三位；其中   *)

(*      冲突，req 侧按真实消费面收参（expf_agree 换 req 签名）。    *)


(*      位——Real 实例由 real_log_wd（L42277）可满足，        *)

(*   4. 命名核对：req 件名 = Id 原件名加 req_ 前缀；FEPLogZ 4 件    *)
(*      加 _logz 后缀（节内定义 lz_ 前缀防跨节遮蔽）；Id 层同名     *)
(*      原件在 /G01_CoreMicro 顶层并存不覆盖。                        *)
(*                                                              *)
(* 红线：零公理、零弃证、零参数化声明、零经典律；Set 层语句        *)
(*   （req/lt/le 均 Set 值；合取用 Set 层 And:=A*B）；纯 term-mode  *)
(*   （req_trans 链 + 兼容桥，零态射改写依赖）；全 Qed 闭合；       *)

(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Import RealInterfaceEnhancedMod.

(* ################ Section ReqFEPAttn：FEPAttention 4 件 ################ *)
(*   Id 原件 L112164-112252 逐位 req 镜像；和接口 = 六性质位   *)

Section ReqFEPAttn.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable sumf : (S -> R) -> R.

Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero ->
    forall s : S, req (f s) zero.
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).


Hypothesis log_inv_one_inv :
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis log_exp_neg :
  forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis log_le_linear :
  forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one).
Hypothesis log_eq_linear :
  forall (x : R) (Hx : lt zero x),
    req (log x Hx) (req_minus x one) -> req x one.

(*      Real 实例 real_log_wd 可满足，实例化留接口扩展批） ---- *)
Hypothesis log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).

(* ---- 温度 softmax 实例位（Id 节 Variables z/T/T_pos 逐位） ---- *)
Variable z : S -> R.
Variable T : R.
Variable T_pos : lt zero T.

(* ---- 节内定义（Id 节 Let base/invT/Zf/Zf_pos/F_attn 逐位镜像） ---- *)
Definition base : S -> R := fun s : S => opp (z s).
Definition invT : R := inv_pos T T_pos.
Definition Zf : R :=
  sumf (fun s : S => exp_pos_fn_setoid (mult invT (z s))).

Lemma Zf_pos : lt zero Zf.
Proof.
  unfold Zf, exp_pos_fn_setoid. apply sum_pos.
  intro s. apply exp_neg_pos.
Qed.

Definition softmax_z (s : S) : R :=
  mult (exp_pos_fn_setoid (mult invT (z s))) (inv_pos Zf Zf_pos).
Definition boltz_z (s : S) : R :=
  mult (inv_pos Zf Zf_pos) (exp_neg (mult invT (base s))).
Definition F_attn (p : S -> R) (Hp : forall s : S, lt zero (p s)) : R :=
  plus (sumf (fun s : S => mult (p s) (base s)))
       (mult T (sumf (fun s : S => mult (p s) (log (p s) (Hp s))))).

(* ---- 件 1/9：配分条件（Id fep_partition_condition L112193） ---- *)
(*   Z == Σ_s e^{-(1/T)·(-z s)}：逐点 opp_mult_l 换形 + exp 兼容桥。 *)
Theorem req_fep_partition_condition :
  req Zf (sumf (fun s : S => exp_neg (mult invT (base s)))).
Proof.
  unfold Zf, base, exp_pos_fn_setoid.
  apply (sum_ext _ _ (fun s : S =>
    exp_neg_req_compat_setoid _ _ (req_sym _ _ (req_opp_mult_l invT (z s))))).
Qed.

(* ---- 件 2/9：对齐引理（Id fep_align L112201） ---- *)
(*   Boltzmann（能量 −z、温度 T）逐点 = 温度 softmax：乘积换序 +     *)
(*   分子 exp 兼容换形（Id 证明链 req_trans 重放）。                 *)
Theorem req_fep_align : forall s : S, req (boltz_z s) (softmax_z s).
Proof.
  intro s. unfold boltz_z, softmax_z, base, exp_pos_fn_setoid.
  apply (req_trans
    (mult (inv_pos Zf Zf_pos) (exp_neg (mult invT (opp (z s)))))
    (mult (exp_neg (mult invT (opp (z s)))) (inv_pos Zf Zf_pos))
    (mult (exp_neg (opp (mult invT (z s)))) (inv_pos Zf Zf_pos))).
  - exact (mult_comm _ _).
  - apply (req_mult_compat _ _ _ _
      (exp_neg_req_compat_setoid _ _ (req_opp_mult_l invT (z s)))
      (req_refl (inv_pos Zf Zf_pos))).
Qed.

(* ---- 辅件：softmax 归一化（Id softmax_temp_normalized 消费位镜像；*)
(*      旗舰 Hnorms 前提供给；线性提因子 + 配分折返 + 逆元完成） ---- *)
Lemma req_softmax_z_normalized : req (sumf softmax_z) one.
Proof.
  unfold softmax_z.
  apply (req_trans
    (sumf (fun s : S => mult (exp_pos_fn_setoid (mult invT (z s)))
                             (inv_pos Zf Zf_pos)))
    (mult (inv_pos Zf Zf_pos) Zf) one).
  - apply (req_trans
      (sumf (fun s : S => mult (exp_pos_fn_setoid (mult invT (z s)))
                               (inv_pos Zf Zf_pos)))
      (sumf (fun s : S => mult (inv_pos Zf Zf_pos)
                               (exp_pos_fn_setoid (mult invT (z s)))))
      (mult (inv_pos Zf Zf_pos)
            (sumf (fun s : S => exp_pos_fn_setoid (mult invT (z s)))))).
    + apply (sum_ext _ _ (fun s : S => mult_comm _ _)).
    + exact (sum_linear (inv_pos Zf Zf_pos)
               (fun s : S => exp_pos_fn_setoid (mult invT (z s)))).
  - apply (req_trans (mult (inv_pos Zf Zf_pos) Zf)
                     (mult Zf (inv_pos Zf Zf_pos)) one).
    + exact (mult_comm _ _).
    + exact (inv_pos_correct Zf Zf_pos).
Qed.

(* ---- 件 3/9：F 外延（Id fep_F_ext L112211） ---- *)
(*   逐点相等的分布给出相等自由能；log 前提化收逐点正性位（登记表 1），  *)
(*   Id 归一前提保留为 raw req 形；逐点 log 换形走 log_req_compat。   *)
Theorem req_fep_F_ext :
  forall (p q : S -> R)
         (Hp : forall s : S, lt zero (p s))
         (Hq : forall s : S, lt zero (q s)),
    req (sumf p) one -> req (sumf q) one ->
    (forall s : S, req (p s) (q s)) ->
    req (F_attn p Hp) (F_attn q Hq).
Proof.
  intros p q Hp Hq Hnp1 Hnp2 Hpt. unfold F_attn.
  apply (req_plus_compat _ _ _ _).
  - apply (sum_ext _ _ (fun s : S =>
      req_mult_compat _ _ _ _ (Hpt s) (req_refl (base s)))).
  - apply (req_mult_compat _ _ _ _ (req_refl T)
      (sum_ext _ _ (fun s : S =>
        req_mult_compat _ _ _ _ (Hpt s)
          (log_req_compat (p s) (q s) (Hp s) (Hq s) (Hpt s))))).
Qed.

(* ---- 辅件：softmax 逐点正性（旗舰语句位直引） ---- *)
Lemma softmax_z_pos : forall s : S, lt zero (softmax_z s).
Proof.
  intro s. unfold softmax_z, exp_pos_fn_setoid. apply mult_positive.
  - apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

(* ---- 件 4/9 旗舰：attention = 变分自由能的唯一最小点                *)
(*   （Id attention_minimizes_free_energy_unique L112225）。          *)
(*   消费链：req_fep_F_ext（softmax↔boltzmann 换形，Id HFsb 步）       *)
(*   → UpReqDist req_min_free_energy_is_boltzmann（≤ 腿）/            *)
(*   req_free_energy_min_unique（唯一性腿）+ req_fep_align 完成。      *)
Theorem req_attention_minimizes_free_energy_unique :
  forall (p : S -> R) (Hp : forall s : S, lt zero (p s)),
    req (sumf p) one ->
    And (le (F_attn softmax_z softmax_z_pos) (F_attn p Hp))
        (req (F_attn p Hp) (F_attn softmax_z softmax_z_pos) ->
          forall s : S, req (p s) (softmax_z s)).
Proof.
  intros p Hp Hnp.
  assert (Hpinv : req (inv_pos Zf Zf_pos)
                    (inv_pos Zf (@Z_pos R RIS S sumf sum_pos
                                   base T T_pos Zf req_fep_partition_condition))).
  { apply (req_mult_cancel_l Zf _ _ Zf_pos).
    apply (req_trans _ _ _ (inv_pos_correct Zf Zf_pos)
             (req_sym _ _ (inv_pos_correct Zf
                (@Z_pos R RIS S sumf sum_pos base T T_pos Zf
                   req_fep_partition_condition)))). }
  assert (Hpt : forall s : S,
            req (boltz_z s)
                (@reqd_boltzmann_dist R RIS S sumf sum_pos base T T_pos Zf
                   req_fep_partition_condition s)).
  { intro s. apply (req_mult_compat _ _ _ _ Hpinv
             (req_refl (exp_neg (mult invT (base s))))). }
  assert (Hnboltz : req (sumf boltz_z) one).
  { assert (Hn : reqd_normalized S sumf
                   (@reqd_boltzmann_dist R RIS S sumf sum_pos base T T_pos Zf
                      req_fep_partition_condition))
      by exact (@req_boltzmann_normalized R RIS S sumf sum_linear sum_pos
                  base T T_pos Zf req_fep_partition_condition).
    unfold reqd_normalized in Hn.
    apply (req_trans _ _ _ (sum_ext _ _ Hpt) Hn). }
  assert (Hposbz : forall s : S, lt zero (boltz_z s)).
  { intro s. apply (lt_id_r zero _ _ (req_sym _ _ (Hpt s))).
    exact (@req_boltzmann_positive R RIS S sumf sum_pos
             base T T_pos Zf req_fep_partition_condition s). }
  assert (HFsb : req (F_attn softmax_z softmax_z_pos)
                     (F_attn boltz_z Hposbz))
    by exact (req_fep_F_ext softmax_z boltz_z softmax_z_pos
               Hposbz
               req_softmax_z_normalized Hnboltz
               (fun s : S => req_sym _ _ (req_fep_align s))).
  assert (Hmin : le (F_attn (@reqd_boltzmann_dist R RIS S sumf sum_pos
                               base T T_pos Zf req_fep_partition_condition)
                            (@req_boltzmann_positive R RIS S sumf sum_pos
                               base T T_pos Zf req_fep_partition_condition))
                   (F_attn p Hp))
    by exact (@req_min_free_energy_is_boltzmann R RIS S sumf sum_ext sum_add sum_linear
                sum_pos sum_le base T T_pos Zf req_fep_partition_condition
                log_inv_one_inv log_exp_neg log_le_linear p Hp Hnp).
  assert (HFcong : forall (d1 d2 : S -> R) (Hd1 : forall s : S, lt zero (d1 s))
                     (Hd2 : forall s : S, lt zero (d2 s)),
             (forall s : S, req (d1 s) (d2 s)) ->
             req (F_attn d1 Hd1) (F_attn d2 Hd2)).
  { intros d1 d2 Hd1 Hd2 H. unfold F_attn. apply req_plus_compat.
    - apply (sum_ext _ _). intro s. apply req_mult_compat.
      + apply H.
      + apply req_refl.
    - apply (req_mult_compat _ _ _ _ (req_refl T) (sum_ext _ _ (fun s =>
        req_mult_compat _ _ _ _ (H s)
          (log_req_compat (d1 s) (d2 s) (Hd1 s) (Hd2 s) (H s))))). }
  assert (Hle : le (F_attn boltz_z Hposbz) (F_attn p Hp)).
  { apply (le_id_l _ _ _
             (req_sym _ _ (HFcong
                (@reqd_boltzmann_dist R RIS S sumf sum_pos base T T_pos Zf
                   req_fep_partition_condition)
                boltz_z
                (@req_boltzmann_positive R RIS S sumf sum_pos base T T_pos Zf
                   req_fep_partition_condition) Hposbz
                (fun s0 : S => req_sym _ _ (Hpt s0))))
             Hmin). }
  split.
  - exact (le_id_l _ _ _ HFsb Hle).
  - intros Heq s.
    apply (req_trans _ _ _
      (@req_free_energy_min_unique R RIS S sumf sum_ext sum_add sum_linear
        sum_pos sum_zero_nonneg base T T_pos Zf req_fep_partition_condition
        log_inv_one_inv log_exp_neg log_le_linear log_eq_linear
        p Hp Hnp
        (req_trans _ _ _ Heq
           (HFcong softmax_z
              (@reqd_boltzmann_dist R RIS S sumf sum_pos base T T_pos Zf
                 req_fep_partition_condition)
              softmax_z_pos
              (@req_boltzmann_positive R RIS S sumf sum_pos base T T_pos Zf
                 req_fep_partition_condition)
              (fun s0 : S =>
                 req_trans _ _ _ (req_sym _ _ (req_fep_align s0)) (Hpt s0))))
        s)
      (req_trans _ _ _ (req_sym _ _ (Hpt s)) (req_fep_align s))).
Qed.

End ReqFEPAttn.

(* ################ Section ReqRowView：RowView 1 件 ################ *)
(*   Id 原件 L112256-112304（bs_kernel_row_is_softmax_temp     *)
(*   L112281）req 镜像。参数位剪除登记表见文件头注 2；expf 迷你接口     *)
(*   一致性前提换 req 签名（expf_agree）。                           *)
Section ReqRowView.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable sumf : (S -> R) -> R.

Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable z2 : S -> S -> R.
Variable expf : R -> R.
Hypothesis expf_pos : forall x : R, lt zero (expf x).
Hypothesis expf_agree : forall x : R, req (expf x) (exp_pos_fn_setoid x).

(* ---- 行配分函数（Id Zrow 镜像：Σ_s0 expf((1/T)·z2 s s0)） ---- *)
Definition req_Zrow (s : S) : R :=
  sumf (fun s0 : S => expf (mult (inv_pos temp temp_pos) (z2 s s0))).

Lemma req_Zrow_pos : forall s : S, lt zero (req_Zrow s).
Proof.
  intro s. unfold req_Zrow. apply sum_pos. intro s0. apply expf_pos.
Qed.

(* ---- 单查询行 softmax 侧（Id partition_function_temp/softmax_temp  *)
(*      对 (fun s0 => z2 s s0) 实例的镜像） ---- *)
Definition req_row_partition (s : S) : R :=
  sumf (fun s0 : S => exp_pos_fn_setoid (mult (inv_pos temp temp_pos) (z2 s s0))).

Lemma req_row_partition_pos : forall s : S, lt zero (req_row_partition s).
Proof.
  intro s. unfold req_row_partition, exp_pos_fn_setoid.
  apply sum_pos. intro s0. apply exp_neg_pos.
Qed.

Definition req_row_softmax (s s' : S) : R :=
  mult (exp_pos_fn_setoid (mult (inv_pos temp temp_pos) (z2 s s')))
       (inv_pos (req_row_partition s) (req_row_partition_pos s)).

(* ---- 行核（Id bs_kernel 消费面镜像：分子 expf 行元 + 逆行配分） ---- *)
Definition req_bs_kernel (s s' : S) : R :=
  mult (expf (mult (inv_pos temp temp_pos) (z2 s s')))
       (inv_pos (req_Zrow s) (req_Zrow_pos s)).

(* ---- 件 5/9：行视图（Id bs_kernel_row_is_softmax_temp L112281） ---- *)
(*   行核每行 = 单查询温度 softmax：HZ 步（行配分折返，sum_ext +      *)
(*   expf_agree 逐点）+ 分子 expf_agree + 逆元 inv_pos_ext 归一。      *)
Theorem req_bs_kernel_row_is_softmax_temp : forall s s' : S,
  req (req_bs_kernel s s') (req_row_softmax s s').
Proof.
  intros s s'.
  assert (HZ : req (req_Zrow s) (req_row_partition s)).
  { unfold req_Zrow, req_row_partition.
    apply (sum_ext _ _ (fun s0 : S =>
      expf_agree (mult (inv_pos temp temp_pos) (z2 s s0)))). }
  unfold req_bs_kernel, req_row_softmax.
  exact (req_mult_compat _ _ _ _
    (expf_agree (mult (inv_pos temp temp_pos) (z2 s s')))
    (inv_pos_ext (req_Zrow s) (req_row_partition s)
                 (req_Zrow_pos s) (req_row_partition_pos s) HZ)).
Qed.

End ReqRowView.

(* ################ Section ReqFEPLogZ：FEPLogZ 4 件 ################ *)
(*   Id 原件 Module UpExtras219 Section FEPLogZ L114023-114099  *)
(*   req 镜像（与 ReqFEPAttn 节同构；fep_F_ext 较弱：无归一前提位，    *)
(*   旗舰 free_energy_softmax_eq_neg_T_logZ 消费 req_free_energy_     *)
(*   boltzmann 完成）。节内定义 lz_ 前缀防跨节顶层遮蔽（登记表 4）。     *)
Section ReqFEPLogZ.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable sumf : (S -> R) -> R.

Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).


Hypothesis log_inv_one_inv :
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis log_exp_neg :
  forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).

Variable z : S -> R.
Variable T : R.
Variable T_pos : lt zero T.

Definition lz_base : S -> R := fun s : S => opp (z s).
Definition lz_invT : R := inv_pos T T_pos.
Definition lz_Zf : R :=
  sumf (fun s : S => exp_pos_fn_setoid (mult lz_invT (z s))).

Lemma lz_Zf_pos : lt zero lz_Zf.
Proof.
  unfold lz_Zf, exp_pos_fn_setoid. apply sum_pos.
  intro s. apply exp_neg_pos.
Qed.

Definition lz_softmax_z (s : S) : R :=
  mult (exp_pos_fn_setoid (mult lz_invT (z s))) (inv_pos lz_Zf lz_Zf_pos).
Definition lz_boltz_z (s : S) : R :=
  mult (inv_pos lz_Zf lz_Zf_pos) (exp_neg (mult lz_invT (lz_base s))).
Definition lz_F_attn (p : S -> R) (Hp : forall s : S, lt zero (p s)) : R :=
  plus (sumf (fun s : S => mult (p s) (lz_base s)))
       (mult T (sumf (fun s : S => mult (p s) (log (p s) (Hp s))))).

(* ---- 件 6/9：配分条件@FEPLogZ（Id L114054） ---- *)
Theorem req_fep_partition_condition_logz :
  req lz_Zf (sumf (fun s : S => exp_neg (mult lz_invT (lz_base s)))).
Proof.
  unfold lz_Zf, lz_base, exp_pos_fn_setoid.
  apply (sum_ext _ _ (fun s : S =>
    exp_neg_req_compat_setoid _ _ (req_sym _ _ (req_opp_mult_l lz_invT (z s))))).
Qed.

(* ---- 件 7/9：对齐引理@FEPLogZ（Id L114063） ---- *)
Theorem req_fep_align_logz : forall s : S, req (lz_boltz_z s) (lz_softmax_z s).
Proof.
  intro s. unfold lz_boltz_z, lz_softmax_z, lz_base, exp_pos_fn_setoid.
  apply (req_trans
    (mult (inv_pos lz_Zf lz_Zf_pos) (exp_neg (mult lz_invT (opp (z s)))))
    (mult (exp_neg (mult lz_invT (opp (z s)))) (inv_pos lz_Zf lz_Zf_pos))
    (mult (exp_neg (opp (mult lz_invT (z s)))) (inv_pos lz_Zf lz_Zf_pos))).
  - exact (mult_comm _ _).
  - apply (req_mult_compat _ _ _ _
      (exp_neg_req_compat_setoid _ _ (req_opp_mult_l lz_invT (z s)))
      (req_refl (inv_pos lz_Zf lz_Zf_pos))).
Qed.

(* ---- 件 8/9：F 外延@FEPLogZ（Id L114073；无归一前提位的较弱形） ---- *)
Theorem req_fep_F_ext_logz :
  forall (p q : S -> R)
         (Hp : forall s : S, lt zero (p s))
         (Hq : forall s : S, lt zero (q s)),
    (forall s : S, req (p s) (q s)) ->
    req (lz_F_attn p Hp) (lz_F_attn q Hq).
Proof.
  intros p q Hp Hq Hpt. unfold lz_F_attn.
  apply (req_plus_compat _ _ _ _).
  - apply (sum_ext _ _ (fun s : S =>
      req_mult_compat _ _ _ _ (Hpt s) (req_refl (lz_base s)))).
  - apply (req_mult_compat _ _ _ _ (req_refl T)
      (sum_ext _ _ (fun s : S =>
        req_mult_compat _ _ _ _ (Hpt s)
          (log_req_compat (p s) (q s) (Hp s) (Hq s) (Hpt s))))).
Qed.

(* ---- 辅件：softmax 逐点正性（旗舰语句位直引） ---- *)
Lemma lz_softmax_z_pos : forall s : S, lt zero (lz_softmax_z s).
Proof.
  intro s. unfold lz_softmax_z, exp_pos_fn_setoid. apply mult_positive.
  - apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.


(*   （Id free_energy_softmax_eq_neg_T_logZ L114089）。               *)
(*   链：F 外延（softmax↔boltzmann 逐点换形）→ UpReqDist              *)

Theorem req_free_energy_softmax_eq_neg_T_logZ :
  req (lz_F_attn lz_softmax_z lz_softmax_z_pos)
      (mult (opp T) (log lz_Zf lz_Zf_pos)).
Proof.
  assert (Hpinv : req (inv_pos lz_Zf lz_Zf_pos)
                      (inv_pos lz_Zf (@Z_pos R RIS S sumf sum_pos
                                       lz_base T T_pos lz_Zf
                                       req_fep_partition_condition_logz))).
  { apply (req_mult_cancel_l lz_Zf _ _ lz_Zf_pos).
    apply (req_trans _ _ _ (inv_pos_correct lz_Zf lz_Zf_pos)
             (req_sym _ _ (inv_pos_correct lz_Zf
                (@Z_pos R RIS S sumf sum_pos lz_base T T_pos lz_Zf
                   req_fep_partition_condition_logz)))). }
  assert (Hpt : forall s : S,
            req (lz_boltz_z s)
                (@reqd_boltzmann_dist R RIS S sumf sum_pos lz_base T T_pos lz_Zf
                   req_fep_partition_condition_logz s)).
  { intro s. apply (req_mult_compat _ _ _ _ Hpinv
             (req_refl (exp_neg (mult lz_invT (lz_base s))))). }
  assert (Hpos : forall s : S, lt zero (lz_boltz_z s)).
  { intro s. apply (lt_id_r zero _ _ (req_sym _ _ (Hpt s))).
    exact (@req_boltzmann_positive R RIS S sumf sum_pos
             lz_base T T_pos lz_Zf req_fep_partition_condition_logz s). }
  exact (req_trans _ _ _
    (req_trans _ _ _
      (req_trans _ _ _
        (req_fep_F_ext_logz lz_softmax_z lz_boltz_z lz_softmax_z_pos Hpos
           (fun s : S => req_sym _ _ (req_fep_align_logz s)))
        (req_fep_F_ext_logz lz_boltz_z
           (@reqd_boltzmann_dist R RIS S sumf sum_pos lz_base T T_pos lz_Zf
              req_fep_partition_condition_logz)
           Hpos
           (@req_boltzmann_positive R RIS S sumf sum_pos lz_base T T_pos lz_Zf
              req_fep_partition_condition_logz)
           Hpt))
      (@req_free_energy_boltzmann R RIS S sumf sum_ext sum_add sum_linear
        sum_pos lz_base T T_pos lz_Zf req_fep_partition_condition_logz
        log_inv_one_inv log_exp_neg))
    (req_mult_compat _ _ _ _ (req_refl (opp T))
       (log_req_compat lz_Zf lz_Zf
          (@Z_pos R RIS S sumf sum_pos lz_base T T_pos lz_Zf
             req_fep_partition_condition_logz)
          lz_Zf_pos (req_refl lz_Zf)))).
Qed.

End ReqFEPLogZ.

(*
   【FEPAttention】req_fep_partition_condition<-112193
     req_fep_align<-112201 req_fep_F_ext<-112211
     req_attention_minimizes_free_energy_unique<-112225【旗舰】
   【RowView】req_bs_kernel_row_is_softmax_temp<-112281
   【FEPLogZ】req_fep_partition_condition_logz<-114054
     req_fep_align_logz<-114063 req_fep_F_ext_logz<-114073
     req_free_energy_softmax_eq_neg_T_logZ<-114089【旗舰】
   辅件（非显式假设，证明位供给）：Zf_pos softmax_z_pos
     req_softmax_z_normalized req_Zrow_pos req_row_partition_pos
     lz_Zf_pos lz_softmax_z_pos。 *)
