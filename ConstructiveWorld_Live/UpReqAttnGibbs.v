(* UpReqAttnGibbs.v — 签名迁移批 4 主件：AttentionGibbsBridge 簇首段连贯子链 req 化
   母本：签名迁移规划书-20260908.md 批 4 清单；
   Id 原件：CW_ConstructiveWorld_219.v Section AttentionGibbsBridge L27929-30669
     （首段 = softmax 家 L27950-28600）。
   前置锚（规划书明示直接消费，零重建）：
     基座 Setoid 节已迁 7 件（L66137-66414）：exp_pos_fn_setoid /
       partition_function_setoid / partition_function_pos_setoid / softmax_setoid /
       softmax_pos_setoid / softmax_normalized_setoid / exp_neg_req_compat_setoid；
     UpReqDist ReqSoftmaxDual req softmax 族：reqd_softmax_scaled /
       reqd_softmax_temp_param / reqd_scale_temp_duality / reqd_sqrt_witness。
   ----------------------------------------------------------------
   纪律：纯构造性；Set 层语句；纯 term-mode（req_trans 链 + compat 桥，
   零 Morphisms）；诚实接口假设位逐位保留；全部 coqc/coqchk 经 cpu_guard。
   ----------------------------------------------------------------
   覆盖对账（req 件名 -> Id 原件 @ CW219 行号）：
   【首段 14】ag_softmax_mix_normalized<-28023 ag_softmax_is_prob<-28073
     ag_partition_function_temp_pos<-28094 ag_softmax_temp_pos<-28109
     ag_softmax_temp_normalized<-28119 ag_softmax_temp_mix_normalized<-28147
     ag_softmax_temp_relative<-28196（Boltzmann 约定对位，因子换 exp_neg） ag_partition_function_scaled_pos<-28444
     ag_softmax_scaled_pos<-28460 ag_softmax_scaled_normalized<-28471
     ag_temp_is_scale_duality<-28537 ag_sq_witness_4<-28555
     ag_scale_sqrt_witness_dual<-28565 ag_half_scale_is_temp_two<-28577
   【已迁 7（基座 Setoid 节，直接消费不重迁）】
     partition_function_pos<-27962 softmax_pos<-27980 softmax_normalized<-27991
     attention_is_gibbs<-28606 steady_state_boltzmann_attn<-28722
     boltzmann_normalized_attn<-28802 exp_neg_req_compat_setoid<-66223。
   【冻结清单（规划书 (d) 关卡逐件理由回写）】
     1. softmax_gap_concentration<-28282：集中不等式需逐 eps 有界和机器
        （min/r_max 家 req 场未建）；密度低，留批 5。
     2. temperature_zero_limit<-28337：T→0 极限语义需 lim/metric 因果链
        （接口字段在而链长 >30 步）；留批 5。
     3. list 机器 13 件：规划书 (d) 明示冻结复用（evicted/list 段，L29360 起）。
     4. boltzmann 块余件（attention_is_gibbs_temp<-28634 /
        scale_inv_T_eq_softmax_temp<-28679 / scaled_attention_is_gibbs_temp<-28694 /
        eviction 簇<-29360 起）：首段子链之外，留余量席接力；其依赖的核心件
        已在"已迁 7"内。
   【非平凡性分级】真证：ag_softmax_temp_relative（exp 加法同态 + 换位链）/
     aux_alpha_plus_omda / ag_softmax_temp_pos 家 / ag_softmax_scaled_pos 家 /
     ag_partition_function_*_pos；组装（Id 链 req_trans 重放）：
     ag_softmax_mix_normalized / ag_softmax_temp_normalized /
     ag_softmax_scaled_normalized / ag_softmax_temp_mix_normalized /
     ag_softmax_is_prob；幂等δ对偶：ag_temp_is_scale_duality /
     ag_half_scale_is_temp_two（req_refl 级，消费 reqd_scale_temp_duality）；
     对位验证（见证记账）：ag_scale_sqrt_witness_dual（Hw 仅语句记账，
     证明路径 = reqd_scale_temp_duality，与 Id @28565 同构）。
   ---------------------------------------------------------------- *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section ReqAttnGibbs：AttentionGibbsBridge 首段 req 迁移       *)
(*   求和诚实接口 = Id SumOver/基座 Setoid 节同款三性质 + add，    *)
(*   节内自持（跨席 Hypothesis 不可消费纪律）。                   *)
(* ============================================================ *)
Section ReqAttnGibbs.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable sumf : (S -> R) -> R.

Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).

(* 温度（Id Variables T/T_pos req 位逐位） *)
Variable T : R.
Variable T_pos : lt zero T.

(* ---- 辅件：a + (1−a) == one（mix 家共用尾链；真证） ---- *)
Lemma aux_alpha_plus_omda : forall a : R, req (plus a (req_minus one a)) one.
Proof.
  intro a.
  apply (req_trans _ (plus (plus a one) (opp a)) _).
  - exact (plus_assoc a one (opp a)).
  - apply (req_trans (plus (plus a one) (opp a))
                     (plus (plus one a) (opp a)) _).
    + exact (req_plus_compat (plus a one) (plus one a) (opp a) (opp a)
                (plus_comm a one) (req_refl _)).
    + apply (req_trans (plus (plus one a) (opp a))
                       (plus one (plus a (opp a))) _).
      * exact (req_sym _ _ (plus_assoc one a (opp a))).
      * apply (req_trans (plus one (plus a (opp a))) (plus one zero) one).
        -- exact (req_plus_compat one one (plus a (opp a)) zero
                      (req_refl one) (plus_opp a)).
        -- exact (plus_zero one).
Qed.

(* ---- 单位温度 softmax 家（消费基座 softmax_setoid 系） ---- *)

(* 凸组合归一化守恒（Id @28023；组装） *)
Theorem ag_softmax_mix_normalized :
  forall (z z' : S -> R) (alpha : R) (Halpha : lt zero alpha)
         (Halpha1 : lt zero (req_minus one alpha)),
    req (sumf (fun s : S =>
            plus (mult alpha (softmax_setoid S sumf sum_pos z s))
                 (mult (req_minus one alpha)
                       (softmax_setoid S sumf sum_pos z' s))))
        one.
Proof.
  intros z z' alpha Halpha Halpha1.
  assert (Hp : req (sumf (fun s : S => softmax_setoid S sumf sum_pos z s)) one)
    by exact (softmax_normalized_setoid S sumf sum_ext sum_linear sum_pos z).
  assert (Hq : req (sumf (fun s : S => softmax_setoid S sumf sum_pos z' s)) one)
    by exact (softmax_normalized_setoid S sumf sum_ext sum_linear sum_pos z').
  apply (req_trans _ (plus
        (sumf (fun s : S => mult alpha (softmax_setoid S sumf sum_pos z s)))
        (sumf (fun s : S => mult (req_minus one alpha)
                                 (softmax_setoid S sumf sum_pos z' s)))) _).
  - exact (sum_add (fun s : S => mult alpha (softmax_setoid S sumf sum_pos z s))
                   (fun s : S => mult (req_minus one alpha)
                                      (softmax_setoid S sumf sum_pos z' s))).
  - apply (req_trans _ (plus
        (mult alpha (sumf (fun s : S => softmax_setoid S sumf sum_pos z s)))
        (mult (req_minus one alpha)
              (sumf (fun s : S => softmax_setoid S sumf sum_pos z' s)))) _).
    + exact (req_plus_compat _ _ _ _
               (sum_linear alpha (fun s : S => softmax_setoid S sumf sum_pos z s))
               (sum_linear (req_minus one alpha)
                           (fun s : S => softmax_setoid S sumf sum_pos z' s))).
    + apply (req_trans _ (plus (mult alpha one)
                               (mult (req_minus one alpha) one)) _).
      * exact (req_plus_compat _ _ _ _
                   (req_mult_compat alpha alpha
                      (sumf (fun s : S => softmax_setoid S sumf sum_pos z s)) one
                      (req_refl alpha) Hp)
                   (req_mult_compat (req_minus one alpha) (req_minus one alpha)
                      (sumf (fun s : S => softmax_setoid S sumf sum_pos z' s)) one
                      (req_refl (req_minus one alpha)) Hq)).
      * apply (req_trans _ (plus alpha (req_minus one alpha)) _).
        -- exact (req_plus_compat (mult alpha one) alpha
                       (mult (req_minus one alpha) one) (req_minus one alpha)
                       (mult_one alpha) (mult_one (req_minus one alpha))).
        -- exact (aux_alpha_plus_omda alpha).
Qed.

(* softmax 是概率分布（正性 + 归一化；Id @28073；组装） *)
Theorem ag_softmax_is_prob :
  forall z : S -> R,
    And (forall s : S, le zero (softmax_setoid S sumf sum_pos z s))
        (req (sumf (fun s : S => softmax_setoid S sumf sum_pos z s)) one).
Proof.
  intro z. split.
  - intro s. exact (lt_le_iff _ _ (inl (softmax_pos_setoid S sumf sum_pos z s))).
  - exact (softmax_normalized_setoid S sumf sum_ext sum_linear sum_pos z).
Qed.

(* ---- 温度退火家族（Id @28091-28195；消费 reqd_softmax_temp_param） ---- *)

Definition partition_function_temp_r (z : S -> R) : R :=
  sumf (fun s : S => exp_pos_fn_setoid (mult (inv_pos T T_pos) (z s))).

Lemma ag_partition_function_temp_pos :
  forall z : S -> R, lt zero (partition_function_temp_r z).
Proof.
  intro z. unfold partition_function_temp_r.
  apply sum_pos.
  intro s. exact (exp_neg_pos (opp (mult (inv_pos T T_pos) (z s)))).
Qed.

Lemma ag_softmax_temp_pos :
  forall (z : S -> R) (s : S),
    lt zero (reqd_softmax_temp_param S sumf sum_pos T T_pos z s).
Proof.
  intros z s.
  unfold reqd_softmax_temp_param.
  pose (Pw := (fun s0 : S => exp_neg (mult (inv_pos T T_pos) (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult (inv_pos T T_pos) (z s0))))).
  exact (mult_positive (exp_neg (mult (inv_pos T T_pos) (z s)))
                       (inv_pos (sumf Pw) Wp)
                       (exp_neg_pos (mult (inv_pos T T_pos) (z s)))
                       (inv_pos_pos (sumf Pw) Wp)).
Qed.

Lemma ag_softmax_temp_normalized :
  forall z : S -> R,
    req (sumf (fun s : S =>
           reqd_softmax_temp_param S sumf sum_pos T T_pos z s)) one.
Proof.
  intro z.
  unfold reqd_softmax_temp_param.
  pose (Pw := (fun s0 : S => exp_neg (mult (inv_pos T T_pos) (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult (inv_pos T T_pos) (z s0))))).
  pose (IV := (inv_pos (sumf Pw) Wp)).
  apply (req_trans _ (sumf (fun s : S => mult IV (exp_neg (mult (inv_pos T T_pos) (z s))))) _).
  - apply (sum_ext (fun s : S => mult (exp_neg (mult (inv_pos T T_pos) (z s))) IV)
                   (fun s : S => mult IV (exp_neg (mult (inv_pos T T_pos) (z s))))).
    intro s. exact (mult_comm (exp_neg (mult (inv_pos T T_pos) (z s))) IV).
  - apply (req_trans _ (mult IV (sumf Pw)) _).
    + exact (sum_linear IV Pw).
    + exact (req_trans _ _ _ (mult_comm IV (sumf Pw)) (inv_pos_correct (sumf Pw) Wp)).
Qed.

(* 温度化 softmax 的凸组合归一化守恒（Id @28147；组装） *)
Theorem ag_softmax_temp_mix_normalized :
  forall (z z' : S -> R) (alpha : R) (Halpha : lt zero alpha)
         (Halpha1 : lt zero (req_minus one alpha)),
    req (sumf (fun s : S =>
            plus (mult alpha
                       (reqd_softmax_temp_param S sumf sum_pos T T_pos z s))
                 (mult (req_minus one alpha)
                       (reqd_softmax_temp_param S sumf sum_pos T T_pos z' s))))
        one.
Proof.
  intros z z' alpha Halpha Halpha1.
  assert (Hp : req (sumf (fun s : S =>
                   reqd_softmax_temp_param S sumf sum_pos T T_pos z s)) one)
    by exact (ag_softmax_temp_normalized z).
  assert (Hq : req (sumf (fun s : S =>
                   reqd_softmax_temp_param S sumf sum_pos T T_pos z' s)) one)
    by exact (ag_softmax_temp_normalized z').
  apply (req_trans _ (plus
        (sumf (fun s : S =>
           mult alpha (reqd_softmax_temp_param S sumf sum_pos T T_pos z s)))
        (sumf (fun s : S =>
           mult (req_minus one alpha)
                (reqd_softmax_temp_param S sumf sum_pos T T_pos z' s)))) _).
  - exact (sum_add
             (fun s : S => mult alpha (reqd_softmax_temp_param S sumf sum_pos T T_pos z s))
             (fun s : S => mult (req_minus one alpha)
                                (reqd_softmax_temp_param S sumf sum_pos T T_pos z' s))).
  - apply (req_trans _ (plus
        (mult alpha (sumf (fun s : S =>
                    reqd_softmax_temp_param S sumf sum_pos T T_pos z s)))
        (mult (req_minus one alpha)
              (sumf (fun s : S =>
                    reqd_softmax_temp_param S sumf sum_pos T T_pos z' s)))) _).
    + exact (req_plus_compat _ _ _ _
               (sum_linear alpha
                  (fun s : S => reqd_softmax_temp_param S sumf sum_pos T T_pos z s))
               (sum_linear (req_minus one alpha)
                  (fun s : S => reqd_softmax_temp_param S sumf sum_pos T T_pos z' s))).
    + apply (req_trans _ (plus (mult alpha one)
                               (mult (req_minus one alpha) one)) _).
      * exact (req_plus_compat _ _ _ _
                   (req_mult_compat alpha alpha
                      (sumf (fun s : S => reqd_softmax_temp_param S sumf sum_pos T T_pos z s)) one
                      (req_refl alpha) Hp)
                   (req_mult_compat (req_minus one alpha) (req_minus one alpha)
                      (sumf (fun s : S => reqd_softmax_temp_param S sumf sum_pos T T_pos z' s)) one
                      (req_refl (req_minus one alpha)) Hq)).
      * apply (req_trans _ (plus alpha (req_minus one alpha)) _).
        -- exact (req_plus_compat (mult alpha one) alpha
                       (mult (req_minus one alpha) one) (req_minus one alpha)
                       (mult_one alpha) (mult_one (req_minus one alpha))).
        -- exact (aux_alpha_plus_omda alpha).
Qed.

(* 相对形：softmax_temp z s == softmax_temp z s'·e^(−(z s − z s')/T)
   （Id @28196 对位；诚实签名变化：Id softmax_temp 家用 exp_pos 约定
   e^(+z/T)，reqd_softmax_temp_param 用 Boltzmann 约定 e^(−z/T)——
   相对形因子随之从 exp_pos_fn (invT·Δz) 换为 exp_neg (invT·Δz)，
   正负号对位记录于本台账；真证：exp 加法同态 + req_minus 换位链） *)
Theorem ag_softmax_temp_relative :
  forall (z : S -> R) (s s' : S),
    req (reqd_softmax_temp_param S sumf sum_pos T T_pos z s)
        (mult (reqd_softmax_temp_param S sumf sum_pos T T_pos z s')
              (exp_neg (mult (inv_pos T T_pos) (req_minus (z s) (z s'))))).
Proof.
  intros z s s'.
  assert (Hzs : req (z s) (plus (z s') (req_minus (z s) (z s')))).
  { exact (req_sym _ _ (req_minus_plus_cancel (z s') (z s))). }
  assert (Hf : req (exp_neg (mult (inv_pos T T_pos) (z s)))
                   (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                         (exp_neg (mult (inv_pos T T_pos)
                                       (req_minus (z s) (z s')))))).
  { exact (req_trans
             (exp_neg (mult (inv_pos T T_pos) (z s)))
             (exp_neg (plus (mult (inv_pos T T_pos) (z s'))
                            (mult (inv_pos T T_pos)
                                  (req_minus (z s) (z s')))))
             (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                   (exp_neg (mult (inv_pos T T_pos)
                                  (req_minus (z s) (z s')))))
             (exp_neg_req_compat_setoid
                (mult (inv_pos T T_pos) (z s))
                (plus (mult (inv_pos T T_pos) (z s'))
                      (mult (inv_pos T T_pos) (req_minus (z s) (z s'))))
                (req_trans (mult (inv_pos T T_pos) (z s))
                           (mult (inv_pos T T_pos)
                                 (plus (z s') (req_minus (z s) (z s'))))
                           (plus (mult (inv_pos T T_pos) (z s'))
                                 (mult (inv_pos T T_pos)
                                       (req_minus (z s) (z s'))))
                           (req_mult_compat (inv_pos T T_pos)
                              (inv_pos T T_pos) (z s)
                              (plus (z s') (req_minus (z s) (z s')))
                              (req_refl _) Hzs)
                           (distrib (inv_pos T T_pos) (z s')
                                    (req_minus (z s) (z s')))))
             (exp_neg_plus (mult (inv_pos T T_pos) (z s'))
                           (mult (inv_pos T T_pos)
                                 (req_minus (z s) (z s'))))). }
  unfold reqd_softmax_temp_param.
  pose (Pw := (fun s0 : S => exp_neg (mult (inv_pos T T_pos) (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult (inv_pos T T_pos) (z s0))))).
  pose (IV := (inv_pos (sumf Pw) Wp)).
  assert (Has : req (mult (exp_neg (mult (inv_pos T T_pos) (z s))) IV)
                   (mult IV
                      (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                            (exp_neg (mult (inv_pos T T_pos)
                                           (req_minus (z s) (z s'))))))).
  { apply (req_trans _ (mult IV (exp_neg (mult (inv_pos T T_pos) (z s)))) _).
    - exact (mult_comm (exp_neg (mult (inv_pos T T_pos) (z s))) IV).
    - exact (req_mult_compat IV IV (exp_neg (mult (inv_pos T T_pos) (z s)))
                (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                      (exp_neg (mult (inv_pos T T_pos)
                                     (req_minus (z s) (z s')))))
                (req_refl _) Hf). }
  assert (Har : req (mult IV
                       (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                             (exp_neg (mult (inv_pos T T_pos)
                                            (req_minus (z s) (z s'))))))
                   (mult (mult (exp_neg (mult (inv_pos T T_pos) (z s'))) IV)
                         (exp_neg (mult (inv_pos T T_pos)
                                        (req_minus (z s) (z s')))))).
  { exact (req_trans
             (mult IV
                (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                      (exp_neg (mult (inv_pos T T_pos)
                                     (req_minus (z s) (z s'))))))
             (mult (mult IV (exp_neg (mult (inv_pos T T_pos) (z s'))))
                   (exp_neg (mult (inv_pos T T_pos)
                                  (req_minus (z s) (z s')))))
             (mult (mult (exp_neg (mult (inv_pos T T_pos) (z s'))) IV)
                   (exp_neg (mult (inv_pos T T_pos)
                                  (req_minus (z s) (z s')))))
             (mult_assoc IV (exp_neg (mult (inv_pos T T_pos) (z s')))
                (exp_neg (mult (inv_pos T T_pos)
                               (req_minus (z s) (z s')))))
             (req_mult_compat (mult IV (exp_neg (mult (inv_pos T T_pos) (z s'))))
                (mult (exp_neg (mult (inv_pos T T_pos) (z s'))) IV)
                (exp_neg (mult (inv_pos T T_pos) (req_minus (z s) (z s'))))
                (exp_neg (mult (inv_pos T T_pos) (req_minus (z s) (z s'))))
                (mult_comm IV (exp_neg (mult (inv_pos T T_pos) (z s'))))
                (req_refl _))). }
  apply (req_trans _ (mult IV
         (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
               (exp_neg (mult (inv_pos T T_pos)
                              (req_minus (z s) (z s')))))) _).
  - exact Has.
  - exact Har.
Qed.

(* ---- 缩放家族（Id @28440-28535；消费 reqd_softmax_scaled） ---- *)

Lemma ag_partition_function_scaled_pos :
  forall (c : R) (z : S -> R),
    lt zero (sumf (fun s : S => exp_pos_fn_setoid (mult c (z s)))).
Proof.
  intros c z. apply sum_pos.
  intro s. exact (exp_neg_pos (opp (mult c (z s)))).
Qed.

Lemma ag_softmax_scaled_pos :
  forall (c : R) (z : S -> R) (s : S),
    lt zero (reqd_softmax_scaled S sumf sum_pos c z s).
Proof.
  intros c z s.
  unfold reqd_softmax_scaled.
  pose (Pw := (fun s0 : S => exp_neg (mult c (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult c (z s0))))).
  exact (mult_positive (exp_neg (mult c (z s)))
                       (inv_pos (sumf Pw) Wp)
                       (exp_neg_pos (mult c (z s)))
                       (inv_pos_pos (sumf Pw) Wp)).
Qed.

Lemma ag_softmax_scaled_normalized :
  forall (c : R) (z : S -> R),
    req (sumf (fun s : S => reqd_softmax_scaled S sumf sum_pos c z s)) one.
Proof.
  intros c z.
  unfold reqd_softmax_scaled.
  pose (Pw := (fun s0 : S => exp_neg (mult c (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult c (z s0))))).
  pose (IV := (inv_pos (sumf Pw) Wp)).
  apply (req_trans _ (sumf (fun s : S => mult IV (exp_neg (mult c (z s))))) _).
  - apply (sum_ext (fun s : S => mult (exp_neg (mult c (z s))) IV)
                   (fun s : S => mult IV (exp_neg (mult c (z s))))).
    intro s. exact (mult_comm (exp_neg (mult c (z s))) IV).
  - apply (req_trans _ (mult IV (sumf Pw)) _).
    + exact (sum_linear IV Pw).
    + exact (req_trans _ _ _ (mult_comm IV (sumf Pw)) (inv_pos_correct (sumf Pw) Wp)).
Qed.

(* ---- 缩放-温度对偶与平方维数实例（Id @28537-28600） ---- *)

(* 反向对称（Id @28537；幂等δ对偶：消费 reqd_scale_temp_duality） *)
Lemma ag_temp_is_scale_duality :
  forall (c : R) (Hc : lt zero c) (z : S -> R) (s : S),
    req (reqd_softmax_temp_param S sumf sum_pos c Hc z s)
        (reqd_softmax_scaled S sumf sum_pos (inv_pos c Hc) z s).
Proof.
  intros c Hc z s.
  exact (req_sym _ _ (reqd_scale_temp_duality S sumf sum_pos c Hc z s)).
Qed.

(* d = 4 = 2² 见证（Id @28555；消费 req_two_mult 真证） *)
Lemma ag_sq_witness_4 :
  reqd_sqrt_witness (plus (plus one one) (plus one one)) (plus one one).
Proof.
  exact (req_two_mult (plus one one)).
Qed.

(* 通用平方维数对偶：凡 d = r²（见证式）则 1/r 缩放 == 温度 r
   （Id @28565；对位验证：Hw 仅语句记账，与 Id 原件同构） *)
Theorem ag_scale_sqrt_witness_dual :
  forall (d r : R) (Hr : lt zero r), reqd_sqrt_witness d r ->
  forall (z : S -> R) (s : S),
    req (reqd_softmax_scaled S sumf sum_pos (inv_pos r Hr) z s)
        (reqd_softmax_temp_param S sumf sum_pos r Hr z s).
Proof.
  intros d r Hr Hw z s.
  exact (reqd_scale_temp_duality S sumf sum_pos r Hr z s).
Qed.

(* d = 4（r = 2）实例：softmax(z/2) == 温度 2 的 softmax（Id @28577） *)
Lemma ag_half_scale_is_temp_two :
  forall (z : S -> R) (s : S),
    req (reqd_softmax_scaled S sumf sum_pos
              (inv_pos (plus one one) req_two_pos) z s)
        (reqd_softmax_temp_param S sumf sum_pos (plus one one) req_two_pos z s).
Proof.
  intros z s.
  exact (reqd_scale_temp_duality S sumf sum_pos (plus one one) req_two_pos z s).
Qed.

End ReqAttnGibbs.
