(* ============================================================ *)
(* UpReqLogCompD.v —— 广义旗舰链 G5-S 复合族放电席（重启）：S 阻塞 7 槽    *)
(*   复合清偿（G5 G05_LogSmall 18 件 + G6 G05_LogSmall 10 件 引擎试装）      *)
(*   2026-09-10                                                            *)
(* ------------------------------------------------------------------ *)
(* 席 71 判词表 7 槽逐槽判定（本席复合重建）：                              *)
(*  [槽1] energy_in_log_boltzmann_bridge@UpSigMigrate:65 —— 放电           *)
(*    logc_energy_in_log_boltzmann（LogcFEP 节，F1-F5 链）：req 复合重建，  *)
(*    供给链 = sum 代数三槽 + partition_condition(N 参显式位) +            *)
(*    B1(sup_compat)/B2(sup_log_exp_neg) 供给槽（Real 层闭合件 =           *)
(*    logd_log_compat_real / logd_log_exp_neg_real，G5）+ log_mult/        *)
(*    log_inv_one_inv 接口分解。Id 原件 energy_in_log_boltzmann@CW219:     *)
(*    16116 的 req 签名独立组装（E387 双名异型：Id rewrite 链不可直连）。   *)
(*  [槽2] free_energy_boltzmann_bridge@UpSigMigrate:70 —— 放电             *)
(*    logc_free_energy_boltzmann（F6-F8 链）：F[p_b] ≡ -D·log Z。链 =      *)
(*    槽1 逐点恒等 → 逐点 p·e 两项分解（F6）→ sum_ext/sum_opp/sum_add/     *)
(*    sum_linear 四桥（F7）→ 归一化（F4：partition+inv_pos_correct）→     *)
(*    环代数坍缩（F8）。Id 原件 free_energy_boltzmann@CW219:15945 同位。    *)
(*  [槽3] rdf_log_diff@UpReqRDF:1704 —— S 阻塞（精确缺件分类）             *)
(*    缺件 A：req 层 log eps-delta 根件（log 导数 req 化）。Real 层根在盘   *)
(*    （real_log_differentiable@CW219:46386，df:=1/x，Bishop 逐 eps；      *)
(*    real_log_plus_diff@44464），但其形 = RealDifferentiable 域前提记录    *)
(*    （f : forall x, 0<x -> Real）+ 尾 slack（|D| ≤ eps|h|+eps'）；        *)
(*    reqRDF 形 = 纯函数 f : R -> R + 精确形 |D| ≤ eps|h|。换装 + 收口      *)
(*    两件均超本席时间盒。缺件 B：req_rdf_compose 外层喂入类型位——log 带    *)
(*    正性见证不满足 F : R -> R，需专用 log-composite 引擎（不能通用       *)
(*    compose 直喂）。阻塞分类留档接力（尾注对账节）。                      *)
(*  [槽4] real_kl_decomp_full@UpRealLeB:218 —— 放电（双层双形）             *)
(*    logc_fe_kl_decomp（F9，req 层 minus 形，泛型 RIS）+                  *)
(*    logc_real_kl_decomp_full（Part 3，Real 层 real_kl_term 形，           *)
(*    real_list_sum 实例化 + G6 logd_kl_term_minus_form 桥）。FEP 分解     *)
(*    F[p] ≡ F[p_b] + D·Σ kl。链 = 槽1 逐点 → Σ p·e 两项分解 → 归一化     *)
(*    坍缩 logZ 项 → KL 字面形重组。供给 = partition 显式位（Hpart）+      *)
(*    B1/B2 + sum 代数（G6 Part E 诚实条件放电同型）。                     *)
(*  [槽5] req_entropy_temp_explicit@UpFirewallReq:122 —— 放电               *)
(*    logc_entropy_temp_explicit（LogcTemp 节 T5）：H(t) ≡ E(t)/T +        *)
(*    log Z(T)。链 = 逐点 log p_b 分解（D:=t, Z:=Z_temp t，T3）→           *)
(*    Σ p·log p 显式（T4）→ sum_opp 取负。                                 *)
(*  [槽6] req_relative_entropy_temp_decomp@UpFirewallReq:128 —— 放电        *)
(*    logc_relative_entropy_temp_decomp（T6）：KL(t1‖t2) ≡ -H(t1) +        *)
(*    E(t1)/t2 + log Z(t2)。链 = T4 中间件 + T3 换形取负 + sum_add 合并。   *)
(*  [槽7] req_temp_strict_ident2@UpFirewallReq:144 —— S 阻塞（本席降级，    *)
(*    链已明示待组装）：KL(t2‖t1)+KL(t1‖t2) ≡ (1/t1-1/t2)(E2-E1)。        *)
(*    复合链实读完备 = T6 两例 + T5 换形（-H ≡ -E/T - log Z）→ 8 项 req    *)
(*    置换坍缩（logZ 双双抵消 + X:=1/t1-1/t2 数缩，Part 0 logc_cancel_     *)
(*    left/logc_plus_assoc_cancel 消去核已备）→ distrib 收口。供给链零     *)
(*    缺件，仅余纯 req 代数置换组装工时超本席时间盒——下一席直接装配。      *)
(* 供给槽说明（诚实条件放电，G5 logd_pos_of_agree / G6 Part E 同型）：       *)
(*    B1/B2 在泛型 RIS 层非接口字段，以节 Hypothesis 显式位承接；Real 层    *)
(*    闭合实例 = G5 logd_log_compat_real / logd_log_exp_neg_real（Part 3   *)
(*    即以此二件闭合，零新增 log 假设）。zt_pos 槽 = UpReqTempEntropy      *)
(*    req_Z_temp_pos 产物位（批 2 席领地，未 Require，以槽位承接）。        *)
(* 防撞：logc_ 前缀 + 全部新名 26 个，全库 attn/001 grep 零命中（建前       *)
(*    2026-09-10 逐名实查；UpReqLogCompD 文件名零命中）。                   *)
(* 双形并存：槽4 双层（req minus 形 / Real kl_term 形）；槽1/2 与           *)
(*    UpSigMigrate 节 Hypothesis 同位（本件独立重建，既有文件零改）；       *)
(*    槽5/6/7 与 UpFirewallReq 挂账槽同位（logc_t_* 定义族 =               *)
(*    entropy_dist/req_relative_entropy@UpReqDist:1043-1046 同体重建）。    *)
(* 红线：Set 层零 Prop（结论全 req/lt/le 接口 Set 值）；全 Qed 闭合；零公理； *)
(*    既有文件零改；零 git；温控 guard 错峰（复用 _sqp_guard.ps1 参数化，    *)
(*    零改既有脚本）。                                                     *)
(* 编译配方：_sqp_guard.ps1 温控包装（CoreN 绑核）                          *)
(*   coqc -Q . "" -Q "..\001" "" UpReqLogCompD.v（单核绑核，零裸调）        *)
(* G4：coqchk -Q . "" -Q "..\001" "" UpReqLogCompD（长窗，禁 -o）           *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import G05_LogSmall.
Require Import G05_LogSmall.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Part 0：req 代数公共机（泛型 RIS；全节共享）                              *)
(* ============================================================ *)

Section LogcAlg.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* A1：mult one 左形（mult_one 右形字段 + comm） *)
Lemma logc_mult_one_l : forall a : R, req (mult one a) a.
Proof.
  intro a.
  exact (req_trans (mult one a) (mult a one) a (mult_comm one a) (mult_one a)).
Qed.

(* A2：mult a (opp b) ≡ opp (mult a b)（distrib + mult_zero + 零消去） *)
Lemma logc_mult_opp_l : forall a b : R, req (mult a (opp b)) (opp (mult a b)).
Proof.
  intros a b.
  apply (logd_req_plus_zero_r R RIS (mult a b) (mult a (opp b))).
  apply (req_trans (plus (mult a b) (mult a (opp b)))
                   (mult a (plus b (opp b))) zero).
  - apply req_sym. exact (distrib a b (opp b)).
  - apply (req_trans (mult a (plus b (opp b))) (mult a zero) zero).
    + apply (req_mult_compat a a (plus b (opp b)) zero (req_refl a) (plus_opp b)).
    + exact (mult_zero a).
Qed.

(* A3：mult (opp a) b ≡ opp (mult a b)（A2 对偶 + comm） *)
Lemma logc_mult_opp_r : forall a b : R, req (mult (opp a) b) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_trans (mult (opp a) b) (mult b (opp a)) (opp (mult a b))).
  - exact (mult_comm (opp a) b).
  - apply (req_trans (mult b (opp a)) (opp (mult b a)) (opp (mult a b))).
    + exact (logc_mult_opp_l b a).
    + apply req_opp_compat. exact (mult_comm b a).
Qed.

(* A4：opp(a+b) ≡ opp a + opp b（分配取负；零消去构造） *)
Lemma logc_opp_plus : forall a b : R, req (opp (plus a b)) (plus (opp a) (opp b)).
Proof.
  intros a b.
  apply req_sym.
  apply (logd_req_plus_zero_r R RIS (plus a b) (plus (opp a) (opp b))).
  apply (req_trans (plus (plus a b) (plus (opp a) (opp b)))
                   (plus a (plus b (plus (opp a) (opp b)))) zero).
  - apply req_sym. exact (plus_assoc a b (plus (opp a) (opp b))).
  - apply (req_trans (plus a (plus b (plus (opp a) (opp b))))
                     (plus a (plus (plus b (opp a)) (opp b))) zero).
    + apply (req_plus_compat a a (plus b (plus (opp a) (opp b)))
                              (plus (plus b (opp a)) (opp b))).
      * apply req_refl.
      * exact (plus_assoc b (opp a) (opp b)).
    + apply (req_trans (plus a (plus (plus b (opp a)) (opp b)))
                       (plus (plus a (plus b (opp a))) (opp b)) zero).
      * exact (plus_assoc a (plus b (opp a)) (opp b)).
      * apply (req_trans (plus (plus a (plus b (opp a))) (opp b))
                         (plus (plus a (plus (opp a) b)) (opp b)) zero).
        -- apply (req_plus_compat (plus a (plus b (opp a)))
                     (plus a (plus (opp a) b)) (opp b) (opp b)).
           ++ apply (req_plus_compat a a (plus b (opp a)) (plus (opp a) b)).
              ** apply req_refl.
              ** exact (plus_comm b (opp a)).
           ++ apply req_refl.
        -- apply (req_trans (plus (plus a (plus (opp a) b)) (opp b))
                            (plus (plus (plus a (opp a)) b) (opp b)) zero).
           ++ apply (req_plus_compat (plus a (plus (opp a) b))
                        (plus (plus a (opp a)) b) (opp b) (opp b)).
              ** exact (plus_assoc a (opp a) b).
              ** apply req_refl.
           ++ apply (req_trans (plus (plus (plus a (opp a)) b) (opp b))
                               (plus (plus a (opp a)) (plus b (opp b))) zero).
              ** apply req_sym. exact (plus_assoc (plus a (opp a)) b (opp b)).
              ** apply (req_trans (plus (plus a (opp a)) (plus b (opp b)))
                                  (plus zero zero) zero).
                 --- apply (req_plus_compat (plus a (opp a)) zero
                               (plus b (opp b)) zero (plus_opp a) (plus_opp b)).
                 --- exact (plus_zero zero).
Qed.

(* A5：u + (w + opp u) ≡ w（加法交换结合消去） *)
Lemma logc_plus_assoc_cancel : forall u w : R, req (plus u (plus w (opp u))) w.
Proof.
  intros u w.
  apply (req_trans (plus u (plus w (opp u))) (plus (plus u w) (opp u)) w).
  - exact (plus_assoc u w (opp u)).
  - apply (req_trans (plus (plus u w) (opp u)) (plus (plus w u) (opp u)) w).
    + apply (req_plus_compat (plus u w) (plus w u) (opp u) (opp u)
                (plus_comm u w) (req_refl (opp u))).
    + apply (req_trans (plus (plus w u) (opp u)) (plus w (plus u (opp u))) w).
      * apply req_sym. exact (plus_assoc w u (opp u)).
      * apply (req_trans (plus w (plus u (opp u))) (plus w zero) w).
        -- apply (req_plus_compat w w (plus u (opp u)) zero
                     (req_refl w) (plus_opp u)).
        -- exact (plus_zero w).
Qed.

(* A6：v ≡ u + w ⟹ opp u + v ≡ w（被减项消去；槽 7 数缩核） *)
Lemma logc_cancel_left : forall u v w : R,
  req v (plus u w) -> req (plus (opp u) v) w.
Proof.
  intros u v w H.
  apply (req_trans (plus (opp u) v)
                   (plus (opp u) (plus w (opp (opp u)))) w).
  - apply (req_plus_compat (opp u) (opp u) v (plus w (opp (opp u)))
              (req_refl (opp u))).
    apply (req_trans v (plus u w) (plus w (opp (opp u)))).
    + exact H.
    + apply (req_trans (plus u w) (plus w u) (plus w (opp (opp u)))).
      * exact (plus_comm u w).
      * apply (req_plus_compat w w u (opp (opp u)) (req_refl w)).
        apply req_sym. exact (logd_req_opp_opp R RIS u).
  - exact (logc_plus_assoc_cancel (opp u) w).
Qed.

End LogcAlg.

(* ============================================================ *)
(* Part 1：FEP 复合节（槽 1/2/4；UpSigMigrate 节供给形同位）                  *)
(* ============================================================ *)

Section LogcFEP.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Type.

(* sum 代数三槽（UpSigMigrate SumOver setoid 对接面同位） *)
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).

Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.
Variable Z : R.
Variable Z_pos : lt zero Z.
(* partition_condition（N 参显式供给位；G5 判词表原文） *)
Hypothesis fep_partition :
  req Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).

(* B1/B2 供给槽（G5 判词表；Real 层闭合 = logd_log_compat_real /           *)
(*   logd_log_exp_neg_real） *)
Hypothesis sup_compat : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Hypothesis sup_log_exp_neg : forall u : R,
  req (log (exp_neg u) (exp_neg_pos u)) (opp u).

(* 节内定义（UpSigMigrate 惯例形态同位） *)
Definition logc_posd (p : S -> R) : Type := forall s : S, lt zero (p s).
Definition logc_boltz (s : S) : R :=
  mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))).
Lemma logc_boltz_pos : logc_posd logc_boltz.
Proof.
  intro s.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Defined.
Definition logc_fe (p : S -> R) (Hp : logc_posd p) : R :=
  plus (sumf (fun s => mult (p s) (base_loss s)))
       (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s))))).

(* F1：sum 右线性（sum_linear 的 mult (f s) a 形对偶） *)
Lemma logc_sum_linear_r : forall (a : R) (f : S -> R),
  req (sumf (fun s => mult (f s) a)) (mult (sumf f) a).
Proof.
  intros a f.
  apply (req_trans (sumf (fun s => mult (f s) a))
                   (sumf (fun s => mult a (f s))) (mult (sumf f) a)).
  - apply sum_ext. intro s. exact (mult_comm (f s) a).
  - apply (req_trans (sumf (fun s => mult a (f s)))
                     (mult a (sumf f)) (mult (sumf f) a)).
    + exact (sum_linear a f).
    + exact (mult_comm a (sumf f)).
Qed.

(* F2：sum 取负：Σ opp f ≡ opp Σ f（opp one 数缩路线） *)
Lemma logc_sum_opp : forall f : S -> R,
  req (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s))) (opp (sumf f))).
  - apply sum_ext. intro s.
    apply (req_trans (opp (f s)) (opp (mult one (f s))) (mult (opp one) (f s))).
    + apply req_opp_compat.
      exact (req_sym (mult one (f s)) (f s) (logc_mult_one_l (f s))).
    + apply req_sym. exact (logc_mult_opp_r one (f s)).
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f)) (opp (sumf f))).
    + exact (sum_linear (opp one) f).
    + apply (req_trans (mult (opp one) (sumf f))
                       (opp (mult one (sumf f))) (opp (sumf f))).
      * exact (logc_mult_opp_r one (sumf f)).
      * apply req_opp_compat. exact (logc_mult_one_l (sumf f)).
Qed.

(* F3：逐点 log 分解（槽 1 之根）：log p_b(s) ≡ -log Z - e(s)/D *)
Lemma logc_boltz_log_decomp : forall s : S,
  req (log (logc_boltz s) (logc_boltz_pos s))
      (plus (opp (log Z Z_pos))
            (opp (mult (inv_pos D D_pos) (base_loss s)))).
Proof.
  intro s.
  apply (req_trans (log (logc_boltz s) (logc_boltz_pos s))
                   (plus (log (inv_pos Z Z_pos) (inv_pos_pos Z Z_pos))
                         (log (exp_neg (mult (inv_pos D D_pos) (base_loss s)))
                              (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))))
                   (plus (opp (log Z Z_pos))
                         (opp (mult (inv_pos D D_pos) (base_loss s))))).
  - exact (log_mult (inv_pos Z Z_pos)
                    (exp_neg (mult (inv_pos D D_pos) (base_loss s)))
                    (inv_pos_pos Z Z_pos)
                    (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))).
  - apply req_plus_compat.
    + exact (logd_log_inv_one_inv_of_compat R RIS sup_compat Z Z_pos
               (inv_pos_pos Z Z_pos)).
    + exact (sup_log_exp_neg (mult (inv_pos D D_pos) (base_loss s))).
Qed.

(* F4：Boltzmann 归一化：Σ p_b ≡ 1（partition + sum_linear + inv_pos_correct） *)
Lemma logc_boltzmann_normalized : req (sumf logc_boltz) one.
Proof.
  apply (req_trans (sumf logc_boltz)
                   (mult (inv_pos Z Z_pos)
                         (sumf (fun s => exp_neg
                                   (mult (inv_pos D D_pos) (base_loss s)))))
                   one).
  - exact (sum_linear (inv_pos Z Z_pos)
             (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
  - apply (req_trans (mult (inv_pos Z Z_pos)
                           (sumf (fun s => exp_neg
                                      (mult (inv_pos D D_pos) (base_loss s)))))
                     (mult (inv_pos Z Z_pos) Z) one).
    + apply (req_mult_compat (inv_pos Z Z_pos) (inv_pos Z Z_pos)
               (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z
               (req_refl (inv_pos Z Z_pos))).
      apply req_sym. exact fep_partition.
    + apply (req_trans (mult (inv_pos Z Z_pos) Z)
                       (mult Z (inv_pos Z Z_pos)) one).
      * exact (mult_comm (inv_pos Z Z_pos) Z).
      * exact (inv_pos_correct Z Z_pos).
Qed.

(* F5【槽 1 放电件】：e(s) ≡ -D·(log p_b(s) + log Z)                        *)
(*   （Id 原件 energy_in_log_boltzmann@CW219:16116 的 req 签名独立组装）    *)
Lemma logc_energy_in_log_boltzmann : forall s : S,
  req (base_loss s)
      (opp (mult D (plus (log (logc_boltz s) (logc_boltz_pos s))
                         (log Z Z_pos)))).
Proof.
  intro s.
  assert (Hsum : req (plus (log (logc_boltz s) (logc_boltz_pos s)) (log Z Z_pos))
                     (opp (mult (inv_pos D D_pos) (base_loss s)))).
  { apply (req_trans (plus (log (logc_boltz s) (logc_boltz_pos s)) (log Z Z_pos))
                     (plus (plus (opp (log Z Z_pos))
                                 (opp (mult (inv_pos D D_pos) (base_loss s))))
                           (log Z Z_pos))
                     (opp (mult (inv_pos D D_pos) (base_loss s)))).
    - apply (req_plus_compat (log (logc_boltz s) (logc_boltz_pos s))
               (plus (opp (log Z Z_pos))
                     (opp (mult (inv_pos D D_pos) (base_loss s))))
               (log Z Z_pos) (log Z Z_pos)).
      + exact (logc_boltz_log_decomp s).
      + apply req_refl.
    - apply (req_trans (plus (plus (opp (log Z Z_pos))
                                   (opp (mult (inv_pos D D_pos) (base_loss s))))
                             (log Z Z_pos))
                       (plus (opp (log Z Z_pos))
                             (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                                   (log Z Z_pos)))
                       (opp (mult (inv_pos D D_pos) (base_loss s)))).
      + apply req_sym.
        exact (plus_assoc (opp (log Z Z_pos))
               (opp (mult (inv_pos D D_pos) (base_loss s))) (log Z Z_pos)).
      + apply (req_trans (plus (opp (log Z Z_pos))
                               (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                                     (log Z Z_pos)))
                         (plus (opp (log Z Z_pos))
                               (plus (log Z Z_pos)
                                     (opp (mult (inv_pos D D_pos) (base_loss s)))))
                         (opp (mult (inv_pos D D_pos) (base_loss s)))).
        * apply (req_plus_compat (opp (log Z Z_pos)) (opp (log Z Z_pos))
                   (plus (opp (mult (inv_pos D D_pos) (base_loss s))) (log Z Z_pos))
                   (plus (log Z Z_pos) (opp (mult (inv_pos D D_pos) (base_loss s))))).
          -- apply req_refl.
          -- exact (plus_comm (opp (mult (inv_pos D D_pos) (base_loss s)))
                              (log Z Z_pos)).
        * apply (req_trans (plus (opp (log Z Z_pos))
                                 (plus (log Z Z_pos)
                                       (opp (mult (inv_pos D D_pos) (base_loss s)))))
                           (plus zero (opp (mult (inv_pos D D_pos) (base_loss s))))
                           (opp (mult (inv_pos D D_pos) (base_loss s)))).
          -- apply (req_trans (plus (opp (log Z Z_pos))
                                    (plus (log Z Z_pos)
                                          (opp (mult (inv_pos D D_pos)
                                                     (base_loss s)))))
                              (plus (plus (opp (log Z Z_pos)) (log Z Z_pos))
                                    (opp (mult (inv_pos D D_pos) (base_loss s))))
                              (plus zero (opp (mult (inv_pos D D_pos)
                                                   (base_loss s))))).
             ++ exact (plus_assoc (opp (log Z Z_pos)) (log Z Z_pos)
                       (opp (mult (inv_pos D D_pos) (base_loss s)))).
             ++ apply (req_plus_compat (plus (opp (log Z Z_pos)) (log Z Z_pos))
                        zero
                        (opp (mult (inv_pos D D_pos) (base_loss s)))
                        (opp (mult (inv_pos D D_pos) (base_loss s)))).
                ** exact (req_trans (plus (opp (log Z Z_pos)) (log Z Z_pos))
                                    (plus (log Z Z_pos) (opp (log Z Z_pos)))
                                    zero
                                    (plus_comm (opp (log Z Z_pos))
                                               (log Z Z_pos))
                                    (plus_opp (log Z Z_pos))).
                ** apply req_refl.
          -- exact (logd_req_plus_zero_l R RIS
                      (opp (mult (inv_pos D D_pos) (base_loss s)))). }
  apply (req_sym (opp (mult D (plus (log (logc_boltz s) (logc_boltz_pos s))
                                     (log Z Z_pos))))
                 (base_loss s)).
  apply (req_trans (opp (mult D (plus (log (logc_boltz s) (logc_boltz_pos s))
                                      (log Z Z_pos))))
                   (opp (opp (base_loss s))) (base_loss s)).
  - apply req_opp_compat.
    apply (req_trans (mult D (plus (log (logc_boltz s) (logc_boltz_pos s))
                                   (log Z Z_pos)))
                     (mult D (opp (mult (inv_pos D D_pos) (base_loss s))))
                     (opp (base_loss s))).
    + apply (req_mult_compat D D
               (plus (log (logc_boltz s) (logc_boltz_pos s)) (log Z Z_pos))
               (opp (mult (inv_pos D D_pos) (base_loss s)))
               (req_refl D) Hsum).
    + apply (req_trans (mult D (opp (mult (inv_pos D D_pos) (base_loss s))))
                       (opp (mult D (mult (inv_pos D D_pos) (base_loss s))))
                       (opp (base_loss s))).
      * exact (logc_mult_opp_l D (mult (inv_pos D D_pos) (base_loss s))).
      * apply req_opp_compat.
        apply (req_trans (mult D (mult (inv_pos D D_pos) (base_loss s)))
                         (mult (mult D (inv_pos D D_pos)) (base_loss s))
                         (base_loss s)).
        -- exact (mult_assoc D (inv_pos D D_pos) (base_loss s)).
        -- apply (req_trans (mult (mult D (inv_pos D D_pos)) (base_loss s))
                            (mult one (base_loss s)) (base_loss s)).
           ++ apply (req_mult_compat (mult D (inv_pos D D_pos)) one
                        (base_loss s) (base_loss s)
                        (inv_pos_correct D D_pos) (req_refl (base_loss s))).
           ++ exact (logc_mult_one_l (base_loss s)).
  - exact (logd_req_opp_opp R RIS (base_loss s)).
Qed.

(* F6：逐点 p·e 两项分解（对任意正性分布 q 成立；D 全程保形） *)
Lemma logc_pt_energy_point : forall (q : S -> R) (Hq : logc_posd q) (s : S),
  req (mult (q s) (base_loss s))
      (opp (plus (mult D (mult (q s) (log (logc_boltz s) (logc_boltz_pos s))))
                 (mult D (mult (q s) (log Z Z_pos))))).
Proof.
  intros q Hq s.
  apply (req_trans (mult (q s) (base_loss s))
                   (mult (q s) (opp (mult D (plus (log (logc_boltz s)
                                                    (logc_boltz_pos s))
                                                   (log Z Z_pos)))))
                   (opp (plus (mult D (mult (q s)
                                             (log (logc_boltz s)
                                                  (logc_boltz_pos s))))
                              (mult D (mult (q s) (log Z Z_pos)))))).
  - apply (req_mult_compat (q s) (q s) (base_loss s)
             (opp (mult D (plus (log (logc_boltz s) (logc_boltz_pos s))
                                (log Z Z_pos))))
             (req_refl (q s))).
    exact (logc_energy_in_log_boltzmann s).
  - apply (req_trans (mult (q s) (opp (mult D (plus (log (logc_boltz s)
                                                      (logc_boltz_pos s))
                                                     (log Z Z_pos)))))
                     (opp (mult (q s) (mult D (plus (log (logc_boltz s)
                                                      (logc_boltz_pos s))
                                                     (log Z Z_pos)))))
                     (opp (plus (mult D (mult (q s)
                                               (log (logc_boltz s)
                                                    (logc_boltz_pos s))))
                                (mult D (mult (q s) (log Z Z_pos)))))).
    + exact (logc_mult_opp_l (q s)
               (mult D (plus (log (logc_boltz s) (logc_boltz_pos s))
                             (log Z Z_pos)))).
    + apply (req_trans (opp (mult (q s) (mult D (plus (log (logc_boltz s)
                                                        (logc_boltz_pos s))
                                                       (log Z Z_pos)))))
                       (opp (mult D (mult (q s)
                                           (plus (log (logc_boltz s)
                                                  (logc_boltz_pos s))
                                                 (log Z Z_pos)))))
                       (opp (plus (mult D (mult (q s)
                                                 (log (logc_boltz s)
                                                      (logc_boltz_pos s))))
                                  (mult D (mult (q s) (log Z Z_pos)))))).
      * apply req_opp_compat.
        apply (req_trans (mult (q s) (mult D (plus (log (logc_boltz s)
                                                     (logc_boltz_pos s))
                                                    (log Z Z_pos))))
                         (mult (mult (q s) D)
                               (plus (log (logc_boltz s) (logc_boltz_pos s))
                                     (log Z Z_pos)))
                         (mult D (mult (q s)
                                       (plus (log (logc_boltz s)
                                                  (logc_boltz_pos s))
                                                 (log Z Z_pos))))).
        -- exact (mult_assoc (q s) D
                       (plus (log (logc_boltz s) (logc_boltz_pos s))
                             (log Z Z_pos))).
        -- apply (req_trans (mult (mult (q s) D)
                                  (plus (log (logc_boltz s)
                                             (logc_boltz_pos s))
                                        (log Z Z_pos)))
                            (mult (mult D (q s))
                                  (plus (log (logc_boltz s)
                                             (logc_boltz_pos s))
                                        (log Z Z_pos)))
                            (mult D (mult (q s)
                                          (plus (log (logc_boltz s)
                                                     (logc_boltz_pos s))
                                                (log Z Z_pos))))).
           ++ apply (req_mult_compat (mult (q s) D) (mult D (q s))
                        (plus (log (logc_boltz s) (logc_boltz_pos s))
                              (log Z Z_pos))
                        (plus (log (logc_boltz s) (logc_boltz_pos s))
                              (log Z Z_pos))
                        (mult_comm (q s) D)
                        (req_refl (plus (log (logc_boltz s)
                                          (logc_boltz_pos s))
                                        (log Z Z_pos)))).
           ++ apply req_sym. exact (mult_assoc D (q s)
                        (plus (log (logc_boltz s) (logc_boltz_pos s))
                              (log Z Z_pos))).
      * apply req_opp_compat.
        apply (req_trans (mult D (mult (q s)
                                        (plus (log (logc_boltz s)
                                                   (logc_boltz_pos s))
                                                  (log Z Z_pos))))
                         (mult D (plus (mult (q s)
                                             (log (logc_boltz s)
                                                  (logc_boltz_pos s)))
                                       (mult (q s) (log Z Z_pos))))
                         (plus (mult D (mult (q s)
                                             (log (logc_boltz s)
                                                  (logc_boltz_pos s))))
                               (mult D (mult (q s) (log Z Z_pos))))).
        -- apply (req_mult_compat D D
                       (mult (q s) (plus (log (logc_boltz s)
                                                  (logc_boltz_pos s))
                                                (log Z Z_pos)))
                       (plus (mult (q s) (log (logc_boltz s)
                                                (logc_boltz_pos s)))
                             (mult (q s) (log Z Z_pos)))
                       (req_refl D)
                       (distrib (q s) (log (logc_boltz s) (logc_boltz_pos s))
                          (log Z Z_pos))).
        -- exact (distrib D (mult (q s) (log (logc_boltz s) (logc_boltz_pos s)))
                    (mult (q s) (log Z Z_pos))).
Qed.

(* F7：Σ p_b·e ≡ opp(D·Σ p_b·log p_b) + opp(D·log Z)（归一化入槽） *)
Lemma logc_boltz_energy_sum :
  req (sumf (fun s => mult (logc_boltz s) (base_loss s)))
      (plus (opp (mult D (sumf (fun s => mult (logc_boltz s)
                                (log (logc_boltz s) (logc_boltz_pos s))))))
            (opp (mult D (log Z Z_pos)))).
Proof.
  set (LB := fun s : S => log (logc_boltz s) (logc_boltz_pos s)).
  set (A := fun s : S => mult D (mult (logc_boltz s) (LB s))).
  set (Bs := fun s : S => mult D (mult (logc_boltz s) (log Z Z_pos))).
  apply (req_trans (sumf (fun s => mult (logc_boltz s) (base_loss s)))
                   (opp (sumf (fun s : S => plus (A s) (Bs s))))
                   (plus (opp (mult D (sumf (fun s => mult (logc_boltz s)
                                             (LB s)))))
                         (opp (mult D (log Z Z_pos))))).
  - apply (req_trans (sumf (fun s => mult (logc_boltz s) (base_loss s)))
                     (sumf (fun s : S => opp (plus (A s) (Bs s))))
                     (opp (sumf (fun s : S => plus (A s) (Bs s))))).
    + apply sum_ext. intro s.
      exact (logc_pt_energy_point logc_boltz logc_boltz_pos s).
    + exact (logc_sum_opp (fun s : S => plus (A s) (Bs s))).
  - apply (req_trans (opp (sumf (fun s : S => plus (A s) (Bs s))))
                     (opp (plus (sumf A) (sumf Bs)))
                     (plus (opp (mult D (sumf (fun s => mult (logc_boltz s)
                                               (LB s)))))
                           (opp (mult D (log Z Z_pos))))).
    + apply req_opp_compat. exact (sum_add A Bs).
    + apply (req_trans (opp (plus (sumf A) (sumf Bs)))
                       (plus (opp (sumf A)) (opp (sumf Bs)))
                       (plus (opp (mult D (sumf (fun s => mult (logc_boltz s)
                                                 (LB s)))))
                             (opp (mult D (log Z Z_pos))))).
        * exact (logc_opp_plus (sumf A) (sumf Bs)).
        * apply req_plus_compat.
          -- apply req_opp_compat.
             exact (sum_linear D (fun s : S => mult (logc_boltz s) (LB s))).
          -- apply req_opp_compat.
             apply (req_trans (sumf Bs)
                              (mult D (sumf (fun s : S => mult (logc_boltz s)
                                                (log Z Z_pos))))
                              (mult D (log Z Z_pos))).
             ++ exact (sum_linear D
                          (fun s : S => mult (logc_boltz s) (log Z Z_pos))).
             ++ apply (req_mult_compat D D
                          (sumf (fun s => mult (logc_boltz s) (log Z Z_pos)))
                          (log Z Z_pos) (req_refl D)).
                ** apply (req_trans (sumf (fun s => mult (logc_boltz s)
                                            (log Z Z_pos)))
                                    (mult (sumf logc_boltz) (log Z Z_pos))
                                    (log Z Z_pos)).
                   --- exact (logc_sum_linear_r (log Z Z_pos) logc_boltz).
                   --- apply (req_trans (mult (sumf logc_boltz) (log Z Z_pos))
                                        (mult one (log Z Z_pos))
                                        (log Z Z_pos)).
                      +++ apply (req_mult_compat (sumf logc_boltz) one
                                    (log Z Z_pos) (log Z Z_pos)
                                    logc_boltzmann_normalized
                                    (req_refl (log Z Z_pos))).
                      +++ exact (logc_mult_one_l (log Z Z_pos)).
Qed.

(* F8【槽 2 放电件】：F[p_b] ≡ -D·log Z                                     *)
(*   （Id 原件 free_energy_boltzmann@CW219:15945 的 req 签名独立组装）      *)
Lemma logc_free_energy_boltzmann :
  req (logc_fe logc_boltz logc_boltz_pos) (mult (opp D) (log Z Z_pos)).
Proof.
  set (LB := fun s : S => log (logc_boltz s) (logc_boltz_pos s)).
  set (S1 := mult D (sumf (fun s : S => mult (logc_boltz s) (LB s)))).
  assert (HoppS1 : req (plus (opp S1) S1) zero).
  { apply (req_trans (plus (opp S1) S1) (plus S1 (opp S1)) zero).
    - exact (plus_comm (opp S1) S1).
    - exact (plus_opp S1). }
  assert (HFE : req (logc_fe logc_boltz logc_boltz_pos)
                    (plus (opp (plus S1 (mult D (log Z Z_pos)))) S1)).
  { apply (req_trans (logc_fe logc_boltz logc_boltz_pos)
                     (plus (sumf (fun s => mult (logc_boltz s) (base_loss s)))
                           S1)
                     (plus (opp (plus S1 (mult D (log Z Z_pos)))) S1)).
    - apply req_refl.
    - apply (req_plus_compat (sumf (fun s => mult (logc_boltz s) (base_loss s)))
                (opp (plus S1 (mult D (log Z Z_pos)))) S1 S1).
      + apply (req_trans (sumf (fun s => mult (logc_boltz s) (base_loss s)))
                         (plus (opp S1) (opp (mult D (log Z Z_pos))))
                         (opp (plus S1 (mult D (log Z Z_pos))))).
        * exact logc_boltz_energy_sum.
        * apply req_sym. exact (logc_opp_plus S1 (mult D (log Z Z_pos))).
      + apply req_refl. }
  apply (req_trans (logc_fe logc_boltz logc_boltz_pos)
                   (plus (opp (plus S1 (mult D (log Z Z_pos)))) S1)
                   (mult (opp D) (log Z Z_pos))).
  - exact HFE.
  - apply (req_trans (plus (opp (plus S1 (mult D (log Z Z_pos)))) S1)
                     (plus (plus (opp S1) (opp (mult D (log Z Z_pos)))) S1)
                     (mult (opp D) (log Z Z_pos))).
    + apply (req_plus_compat (opp (plus S1 (mult D (log Z Z_pos))))
                (plus (opp S1) (opp (mult D (log Z Z_pos)))) S1 S1).
      * exact (logc_opp_plus S1 (mult D (log Z Z_pos))).
      * apply req_refl.
    + apply (req_trans (plus (plus (opp S1) (opp (mult D (log Z Z_pos)))) S1)
                       (plus (opp (mult D (log Z Z_pos))) zero)
                       (mult (opp D) (log Z Z_pos))).
      * apply (req_trans (plus (plus (opp S1) (opp (mult D (log Z Z_pos)))) S1)
                         (plus (opp S1) (plus (opp (mult D (log Z Z_pos))) S1))
                         (plus (opp (mult D (log Z Z_pos))) zero)).
        -- apply req_sym.
           exact (plus_assoc (opp S1) (opp (mult D (log Z Z_pos))) S1).
        -- apply (req_trans (plus (opp S1)
                                  (plus (opp (mult D (log Z Z_pos))) S1))
                            (plus (opp S1)
                                  (plus S1 (opp (mult D (log Z Z_pos)))))
                            (plus (opp (mult D (log Z Z_pos))) zero)).
           ++ apply (req_plus_compat (opp S1) (opp S1)
                        (plus (opp (mult D (log Z Z_pos))) S1)
                        (plus S1 (opp (mult D (log Z Z_pos))))
                        (req_refl (opp S1))
                        (plus_comm (opp (mult D (log Z Z_pos))) S1)).
           ++ apply (req_trans (plus (opp S1)
                                     (plus S1 (opp (mult D (log Z Z_pos)))))
                               (plus (plus (opp S1) S1)
                                     (opp (mult D (log Z Z_pos))))
                               (plus (opp (mult D (log Z Z_pos))) zero)).
              ** exact (plus_assoc (opp S1) S1 (opp (mult D (log Z Z_pos)))).
              ** apply (req_trans (plus (plus (opp S1) S1)
                                          (opp (mult D (log Z Z_pos))))
                                  (plus zero (opp (mult D (log Z Z_pos))))
                                  (plus (opp (mult D (log Z Z_pos))) zero)).
                 --- apply (req_plus_compat (plus (opp S1) S1) zero
                           (opp (mult D (log Z Z_pos)))
                           (opp (mult D (log Z Z_pos)))
                           HoppS1 (req_refl (opp (mult D (log Z Z_pos))))).
                 --- exact (plus_comm zero (opp (mult D (log Z Z_pos)))).
      * apply (req_trans (plus (opp (mult D (log Z Z_pos))) zero)
                         (opp (mult D (log Z Z_pos)))
                         (mult (opp D) (log Z Z_pos))).
        -- exact (plus_zero (opp (mult D (log Z Z_pos)))).
        -- apply req_sym. exact (logc_mult_opp_r D (log Z Z_pos)).
Qed.



(* F9【槽 4 放电件·req 层】：FEP 分解 F[p] ≡ F[p_b] + D·Σ kl(minus 形)       *)
Lemma logc_fe_kl_decomp : forall (p : S -> R) (Hp : logc_posd p)
    (Hnormp : req (sumf p) one),
  req (logc_fe p Hp)
      (plus (logc_fe logc_boltz logc_boltz_pos)
            (mult D (sumf (fun s => mult (p s)
                             (plus (log (p s) (Hp s))
                                   (opp (log (logc_boltz s)
                                             (logc_boltz_pos s)))))))).
Proof.
  intros p Hp Hnormp.
  set (Lb := fun s : S => log (logc_boltz s) (logc_boltz_pos s)).
  set (Lp := fun s : S => log (p s) (Hp s)).
  set (U := mult D (sumf (fun s => mult (p s) (Lp s)))).
  set (V := mult D (sumf (fun s => mult (p s) (Lb s)))).
  set (W := mult D (log Z Z_pos)).
  (* Hpe：Σ p·e ≡ opp(V + W)（逐点 F6 + sum 三桥 + Hnormp 入槽） *)
  assert (Hpe : req (sumf (fun s => mult (p s) (base_loss s)))
                    (plus (opp V) (opp W))).
  { apply (req_trans (sumf (fun s => mult (p s) (base_loss s)))
                     (opp (sumf (fun s => plus (mult D (mult (p s) (Lb s)))
                                                (mult D (mult (p s)
                                                           (log Z Z_pos))))))
                     (plus (opp V) (opp W))).
    - apply (req_trans (sumf (fun s => mult (p s) (base_loss s)))
                       (sumf (fun s => opp (plus (mult D (mult (p s) (Lb s)))
                                                 (mult D (mult (p s)
                                                            (log Z Z_pos))))))
                       (opp (sumf (fun s => plus (mult D (mult (p s) (Lb s)))
                                                  (mult D (mult (p s)
                                                             (log Z Z_pos))))))).
      + apply sum_ext. intro s. exact (logc_pt_energy_point p Hp s).
      + exact (logc_sum_opp (fun s => plus (mult D (mult (p s) (Lb s)))
                                (mult D (mult (p s) (log Z Z_pos))))).
    - apply (req_trans (opp (sumf (fun s => plus (mult D (mult (p s) (Lb s)))
                                  (mult D (mult (p s) (log Z Z_pos))))))
                       (opp (plus (sumf (fun s => mult D (mult (p s) (Lb s))))
                                  (sumf (fun s => mult D (mult (p s)
                                                             (log Z Z_pos))))))
                       (plus (opp V) (opp W))).
      + apply req_opp_compat.
        exact (sum_add (fun s => mult D (mult (p s) (Lb s)))
                       (fun s => mult D (mult (p s) (log Z Z_pos)))).
      + apply (req_trans (opp (plus (sumf (fun s => mult D (mult (p s) (Lb s))))
                                    (sumf (fun s => mult D (mult (p s)
                                                           (log Z Z_pos))))))
                         (plus (opp (sumf (fun s => mult D (mult (p s) (Lb s)))))
                               (opp (sumf (fun s => mult D (mult (p s)
                                                          (log Z Z_pos))))))
                         (plus (opp V) (opp W))).
        * exact (logc_opp_plus (sumf (fun s => mult D (mult (p s) (Lb s))))
                    (sumf (fun s => mult D (mult (p s) (log Z Z_pos))))).
        * apply req_plus_compat.
          -- apply req_opp_compat.
             exact (sum_linear D (fun s => mult (p s) (Lb s))).
          -- apply req_opp_compat.
             apply (req_trans (sumf (fun s => mult D (mult (p s) (log Z Z_pos))))
                              (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))
                              (mult D (log Z Z_pos))).
             ++ exact (sum_linear D (fun s => mult (p s) (log Z Z_pos))).
             ++ apply (req_mult_compat D D
                          (sumf (fun s => mult (p s) (log Z Z_pos)))
                          (log Z Z_pos) (req_refl D)).
                ** apply (req_trans (sumf (fun s => mult (p s) (log Z Z_pos)))
                                    (mult (sumf p) (log Z Z_pos)) (log Z Z_pos)).
                   --- exact (logc_sum_linear_r (log Z Z_pos) p).
                   --- apply (req_trans (mult (sumf p) (log Z Z_pos))
                                        (mult one (log Z Z_pos))
                                        (log Z Z_pos)).
                      +++ apply (req_mult_compat (sumf p) one
                                    (log Z Z_pos) (log Z Z_pos)
                                    Hnormp (req_refl (log Z Z_pos))).
                      +++ exact (logc_mult_one_l (log Z Z_pos)). }
  (* F[p] ≡ (opp V + opp W) + U *)
  assert (HFEp : req (logc_fe p Hp) (plus (plus (opp V) (opp W)) U)).
  { apply (req_trans (logc_fe p Hp)
                     (plus (sumf (fun s => mult (p s) (base_loss s)))
                           (mult D (sumf (fun s => mult (p s) (Lp s)))))
                     (plus (plus (opp V) (opp W)) U)).
    - apply req_refl.
    - apply (req_trans (plus (sumf (fun s => mult (p s) (base_loss s)))
                             (mult D (sumf (fun s => mult (p s) (Lp s)))))
                       (plus (plus (opp V) (opp W))
                             (mult D (sumf (fun s => mult (p s) (Lp s)))))
                       (plus (plus (opp V) (opp W)) U)).
      + apply (req_plus_compat (sumf (fun s => mult (p s) (base_loss s)))
                  (plus (opp V) (opp W))
                  (mult D (sumf (fun s => mult (p s) (Lp s))))
                  (mult D (sumf (fun s => mult (p s) (Lp s))))).
        * exact Hpe.
        * apply req_refl.
      + apply req_refl. }
  (* KL 桥：D·Σ p·(log p - log b) ≡ U + opp V *)
  assert (Hkl : req (mult D (sumf (fun s => mult (p s) (plus (Lp s) (opp (Lb s))))))
                    (plus U (opp V))).
  { set (K := fun s : S => mult (p s) (plus (Lp s) (opp (Lb s)))).
    set (K2 := fun s : S => plus (mult (p s) (Lp s))
                                 (opp (mult (p s) (Lb s)))).
    assert (Hper : forall s : S, req (K s) (K2 s)).
    { intro s.
      apply (req_trans (K s)
                       (plus (mult (p s) (Lp s)) (mult (p s) (opp (Lb s))))
                       (K2 s)).
      - exact (distrib (p s) (Lp s) (opp (Lb s))).
      - apply (req_plus_compat (mult (p s) (Lp s)) (mult (p s) (Lp s))
                  (mult (p s) (opp (Lb s))) (opp (mult (p s) (Lb s)))
                  (req_refl (mult (p s) (Lp s)))).
        exact (logc_mult_opp_l (p s) (Lb s)). }
    apply (req_trans (mult D (sumf K)) (mult D (sumf K2)) (plus U (opp V))).
    - apply (req_mult_compat D D (sumf K) (sumf K2) (req_refl D)).
      apply sum_ext. intro s. exact (Hper s).
    - apply (req_trans (mult D (sumf K2))
                       (plus (mult D (sumf (fun s => mult (p s) (Lp s))))
                             (mult D (sumf (fun s => opp (mult (p s) (Lb s))))))
                       (plus U (opp V))).
      + apply (req_trans (mult D (sumf K2))
                         (mult D (plus (sumf (fun s => mult (p s) (Lp s)))
                                       (sumf (fun s => opp (mult (p s) (Lb s))))))
                         (plus (mult D (sumf (fun s => mult (p s) (Lp s))))
                               (mult D (sumf (fun s => opp (mult (p s) (Lb s))))))).
        * apply (req_mult_compat D D (sumf K2)
                    (plus (sumf (fun s => mult (p s) (Lp s)))
                          (sumf (fun s => opp (mult (p s) (Lb s)))))
                    (req_refl D)).
          exact (sum_add (fun s => mult (p s) (Lp s))
                         (fun s => opp (mult (p s) (Lb s)))).
        * exact (distrib D (sumf (fun s => mult (p s) (Lp s)))
                    (sumf (fun s => opp (mult (p s) (Lb s))))).
      + apply (req_plus_compat (mult D (sumf (fun s => mult (p s) (Lp s))))
                  U
                  (mult D (sumf (fun s => opp (mult (p s) (Lb s)))))
                  (opp (mult D (sumf (fun s => mult (p s) (Lb s)))))).
        * apply req_refl.
        * apply (req_trans (mult D (sumf (fun s => opp (mult (p s) (Lb s)))))
                           (mult D (opp (sumf (fun s => mult (p s) (Lb s)))))
                           (opp (mult D (sumf (fun s => mult (p s) (Lb s)))))).
          -- apply (req_mult_compat D D
                        (sumf (fun s => opp (mult (p s) (Lb s))))
                        (opp (sumf (fun s => mult (p s) (Lb s))))
                        (req_refl D)).
             exact (logc_sum_opp (fun s => mult (p s) (Lb s))).
          -- exact (logc_mult_opp_l D (sumf (fun s => mult (p s) (Lb s)))).
}
  (* 汇总：F[p] ≡ (oppV + oppW) + U ≡ oppW + (U + oppV) ≡ F[b] + D·KL *)
  apply (req_trans (logc_fe p Hp) (plus (plus (opp V) (opp W)) U)
                   (plus (logc_fe logc_boltz logc_boltz_pos)
                         (mult D (sumf (fun s => mult (p s)
                                          (plus (Lp s) (opp (Lb s)))))))).
  - exact HFEp.
  - apply (req_trans (plus (plus (opp V) (opp W)) U)
                     (plus (opp W) (plus U (opp V)))
                     (plus (logc_fe logc_boltz logc_boltz_pos)
                           (mult D (sumf (fun s => mult (p s)
                                            (plus (Lp s) (opp (Lb s)))))))).
    + (* (oppV + oppW) + U ≡ oppW + (U + oppV)：五步置换 *)
      apply (req_trans (plus (plus (opp V) (opp W)) U)
                       (plus (opp V) (plus (opp W) U))
                       (plus (opp W) (plus U (opp V)))).
      * apply req_sym. exact (plus_assoc (opp V) (opp W) U).
      * apply (req_trans (plus (opp V) (plus (opp W) U))
                         (plus (opp V) (plus U (opp W)))
                         (plus (opp W) (plus U (opp V)))).
        -- apply (req_plus_compat (opp V) (opp V) (plus (opp W) U)
                     (plus U (opp W)) (req_refl (opp V))
                     (plus_comm (opp W) U)).
        -- apply (req_trans (plus (opp V) (plus U (opp W)))
                            (plus (plus (opp V) U) (opp W))
                            (plus (opp W) (plus U (opp V)))).
           ++ exact (plus_assoc (opp V) U (opp W)).
           ++ apply (req_trans (plus (plus (opp V) U) (opp W))
                               (plus (opp W) (plus (opp V) U))
                               (plus (opp W) (plus U (opp V)))).
              ** exact (plus_comm (plus (opp V) U) (opp W)).
              ** apply (req_trans (plus (opp W) (plus (opp V) U))
                                  (plus (opp W) (plus U (opp V)))
                                  (plus (opp W) (plus U (opp V)))).
                 --- apply (req_plus_compat (opp W) (opp W) (plus (opp V) U)
                              (plus U (opp V)) (req_refl (opp W))
                              (plus_comm (opp V) U)).
                 --- apply req_refl.
    + apply (req_plus_compat (opp (mult D (log Z Z_pos)))
               (logc_fe logc_boltz logc_boltz_pos)
               (plus U (opp V))
               (mult D (sumf (fun s => mult (p s)
                                (plus (Lp s) (opp (Lb s))))))).
      * (* F[b] ≡ opp W（槽 2 内形） *)
        apply (req_trans (opp (mult D (log Z Z_pos)))
                         (mult (opp D) (log Z Z_pos))
                         (logc_fe logc_boltz logc_boltz_pos)).
        -- apply req_sym. exact (logc_mult_opp_r D (log Z Z_pos)).
        -- apply req_sym. exact logc_free_energy_boltzmann.
      * apply req_sym. exact Hkl.
Qed.

End LogcFEP.

(* ============================================================ *)
(* Part 2：【槽 4 放电件·Real 层】real_kl_term 形（real_list_sum 实例化；     *)
(*   供给 = Hpart 显式位 + G5 B1/B2 闭合件 + G6 D1 字面形桥）                 *)
(* ============================================================ *)

Lemma logc_real_kl_decomp_full :
  forall (X : Type) (l : list X) (e : X -> Real) (D : Real)
    (D_pos : real_lt real_zero D) (Z : Real) (Z_pos : real_lt real_zero Z)
    (Hpart : real_eq Z (real_list_sum X
                        (fun s => real_exp_neg
                                   (real_mult (real_inv_pos D D_pos) (e s))) l))
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
    (Hnormp : real_eq (real_list_sum X p l) real_one),
  real_eq
    (real_free_energy X (fun f => real_list_sum X f l) e D p Hp)
    (real_plus
       (real_free_energy X (fun f => real_list_sum X f l) e D
          (fun s => real_mult (real_inv_pos Z Z_pos)
                              (real_exp_neg
                                 (real_mult (real_inv_pos D D_pos) (e s))))
          (fun s => real_mult_positive (real_inv_pos Z Z_pos)
                       (real_exp_neg (real_mult (real_inv_pos D D_pos) (e s)))
                       (real_inv_pos_pos Z Z_pos)
                       (real_exp_neg_pos
                          (real_mult (real_inv_pos D D_pos) (e s)))))
       (real_mult D
          (real_list_sum X
             (fun s => real_kl_term (p s)
                         (real_mult (real_inv_pos Z Z_pos)
                                    (real_exp_neg
                                       (real_mult (real_inv_pos D D_pos)
                                                  (e s))))
                         (Hp s)
                         (real_mult_positive (real_inv_pos Z Z_pos)
                            (real_exp_neg
                               (real_mult (real_inv_pos D D_pos) (e s)))
                            (real_inv_pos_pos Z Z_pos)
                            (real_exp_neg_pos
                               (real_mult (real_inv_pos D D_pos) (e s))))) l))).
Proof.
  intros X l e D D_pos Z Z_pos Hpart p Hp Hnormp.
  set (B := fun s : X => real_mult (real_inv_pos Z Z_pos)
                       (real_exp_neg (real_mult (real_inv_pos D D_pos) (e s)))).
  set (Bpos := fun s : X => real_mult_positive (real_inv_pos Z Z_pos)
                  (real_exp_neg (real_mult (real_inv_pos D D_pos) (e s)))
                  (real_inv_pos_pos Z Z_pos)
                  (real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (e s)))).
  pose proof (@logc_fe_kl_decomp Real RealEnhancedReal X
                (fun f => real_list_sum X f l)
                (fun f g H => real_list_sum_ext X f g l H)
                (fun f g => real_list_sum_add X f g l)
                (fun a f => real_list_sum_linear X a f l)
                e D D_pos Z Z_pos Hpart
                logd_log_compat_real logd_log_exp_neg_real p Hp Hnormp) as Hd.
  apply (real_eq_trans
           (real_free_energy X (fun f => real_list_sum X f l) e D p Hp)
           (real_plus
              (real_free_energy X (fun f => real_list_sum X f l) e D B Bpos)
              (real_mult D
                 (real_list_sum X
                    (fun s => real_mult (p s)
                                (real_plus (real_log (p s) (Hp s))
                                           (real_opp (real_log (B s)
                                                       (Bpos s))))) l)))
           (real_plus
              (real_free_energy X (fun f => real_list_sum X f l) e D B Bpos)
              (real_mult D
                 (real_list_sum X
                    (fun s => real_kl_term (p s) (B s) (Hp s) (Bpos s)) l)))).
  - exact Hd.
  - apply (RealSetoid.real_eq_plus_compat
             (real_free_energy X (fun f => real_list_sum X f l) e D B Bpos)
             (real_mult D
                (real_list_sum X
                   (fun s => real_mult (p s)
                              (real_plus (real_log (p s) (Hp s))
                                         (real_opp (real_log (B s)
                                                     (Bpos s))))) l))
             (real_free_energy X (fun f => real_list_sum X f l) e D B Bpos)
             (real_mult D
                (real_list_sum X
                   (fun s => real_kl_term (p s) (B s) (Hp s) (Bpos s)) l))).
    + apply real_eq_refl.
    + apply (RealSetoid.real_eq_mult_compat D
               (real_list_sum X
                  (fun s => real_mult (p s)
                             (real_plus (real_log (p s) (Hp s))
                                        (real_opp (real_log (B s)
                                                    (Bpos s))))) l)
               D
               (real_list_sum X
                  (fun s => real_kl_term (p s) (B s) (Hp s) (Bpos s)) l)).
      * apply real_eq_refl.
      * apply (real_eq_sym
                 (real_list_sum X
                    (fun s => real_kl_term (p s) (B s) (Hp s) (Bpos s)) l)
                 (real_list_sum X
                    (fun s => real_mult (p s)
                               (real_plus (real_log (p s) (Hp s))
                                          (real_opp (real_log (B s)
                                                      (Bpos s))))) l)).
         exact (real_list_sum_ext X
                  (fun s => real_kl_term (p s) (B s) (Hp s) (Bpos s))
                  (fun s => real_mult (p s)
                             (real_plus (real_log (p s) (Hp s))
                                        (real_opp (real_log (B s)
                                                    (Bpos s))))) l
                  (fun s => logd_kl_term_minus_form (p s) (B s) (Hp s)
                              (Bpos s))).
Qed.

(* ============================================================ *)
(* Part 3：温度复合节（槽 5/6/7；UpFirewallReq 节供给形同位）                  *)
(* ============================================================ *)

Section LogcTemp.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.

Variable sumf : (S -> R) -> R.
Hypothesis tsum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis tsum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis tsum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).

Variable energy : S -> R.
Variable Z_temp : R -> R.
(* req_Z_temp_spec（母件 L93 同位假设槽） *)
Hypothesis zt_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (energy s)))).
(* zt_pos 槽 = UpReqTempEntropy req_Z_temp_pos 产物位（批 2 席领地） *)
Hypothesis zt_pos : forall (t : R) (Ht : lt zero t), lt zero (Z_temp t).
(* B1/B2 供给槽（同 LogcFEP） *)
Hypothesis tsup_compat : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Hypothesis tsup_log_exp_neg : forall u : R,
  req (log (exp_neg u) (exp_neg_pos u)) (opp u).

(* 温度参数化定义族（UpFirewallReq fw_* 同位；entropy_dist/               *)
(*   req_relative_entropy@UpReqDist:1043-1046 同体重建） *)
Definition logc_t_bt (t : R) (Ht : lt zero t) (s : S) : R :=
  mult (inv_pos (Z_temp t) (zt_pos t Ht))
       (exp_neg (mult (inv_pos t Ht) (energy s))).
Definition logc_t_bt_pos (t : R) (Ht : lt zero t) :
  forall s : S, lt zero (logc_t_bt t Ht s).
Proof.
  intros s.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Defined.
Definition logc_t_et (t : R) (Ht : lt zero t) : R :=
  sumf (fun s => mult (logc_t_bt t Ht s) (energy s)).
Definition logc_t_h (t : R) (Ht : lt zero t) : R :=
  sumf (fun s => mult (logc_t_bt t Ht s)
                      (opp (log (logc_t_bt t Ht s) (logc_t_bt_pos t Ht s)))).
Definition logc_t_kl (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2) : R :=
  sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                      (plus (log (logc_t_bt t1 Ht1 s) (logc_t_bt_pos t1 Ht1 s))
                            (opp (log (logc_t_bt t2 Ht2 s)
                                      (logc_t_bt_pos t2 Ht2 s))))).

(* T1：sum 取负/右线性（LogcFEP 同款，节字段换喂） *)
Lemma logc_t_sum_opp : forall f : S -> R,
  req (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s))) (opp (sumf f))).
  - apply tsum_ext. intro s.
    apply (req_trans (opp (f s)) (opp (mult one (f s))) (mult (opp one) (f s))).
    + apply req_opp_compat.
      exact (req_sym (mult one (f s)) (f s) (logc_mult_one_l (f s))).
    + apply req_sym. exact (logc_mult_opp_r one (f s)).
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f)) (opp (sumf f))).
    + exact (tsum_linear (opp one) f).
    + apply (req_trans (mult (opp one) (sumf f))
                       (opp (mult one (sumf f))) (opp (sumf f))).
      * exact (logc_mult_opp_r one (sumf f)).
      * apply req_opp_compat. exact (logc_mult_one_l (sumf f)).
Qed.

Lemma logc_t_sum_linear_r : forall (a : R) (f : S -> R),
  req (sumf (fun s => mult (f s) a)) (mult (sumf f) a).
Proof.
  intros a f.
  apply (req_trans (sumf (fun s => mult (f s) a))
                   (sumf (fun s => mult a (f s))) (mult (sumf f) a)).
  - apply tsum_ext. intro s. exact (mult_comm (f s) a).
  - apply (req_trans (sumf (fun s => mult a (f s)))
                     (mult a (sumf f)) (mult (sumf f) a)).
    + exact (tsum_linear a f).
    + exact (mult_comm a (sumf f)).
Qed.

(* T2：归一化 Σ p_b(t) ≡ 1（zt_spec + tsum_linear + inv_pos_correct） *)
Lemma logc_t_normalized : forall (t : R) (Ht : lt zero t),
  req (sumf (logc_t_bt t Ht)) one.
Proof.
  intros t Ht.
  apply (req_trans (sumf (logc_t_bt t Ht))
                   (mult (inv_pos (Z_temp t) (zt_pos t Ht))
                         (sumf (fun s => exp_neg
                                   (mult (inv_pos t Ht) (energy s)))))
                   one).
  - exact (tsum_linear (inv_pos (Z_temp t) (zt_pos t Ht))
             (fun s => exp_neg (mult (inv_pos t Ht) (energy s)))).
  - apply (req_trans (mult (inv_pos (Z_temp t) (zt_pos t Ht))
                           (sumf (fun s => exp_neg
                                      (mult (inv_pos t Ht) (energy s)))))
                     (mult (inv_pos (Z_temp t) (zt_pos t Ht)) (Z_temp t)) one).
    + apply (req_mult_compat (inv_pos (Z_temp t) (zt_pos t Ht))
               (inv_pos (Z_temp t) (zt_pos t Ht))
               (sumf (fun s => exp_neg (mult (inv_pos t Ht) (energy s))))
               (Z_temp t)
               (req_refl (inv_pos (Z_temp t) (zt_pos t Ht)))).
      apply req_sym. exact (zt_spec t Ht).
    + apply (req_trans (mult (inv_pos (Z_temp t) (zt_pos t Ht)) (Z_temp t))
                       (mult (Z_temp t) (inv_pos (Z_temp t) (zt_pos t Ht)))
                       one).
      * exact (mult_comm (inv_pos (Z_temp t) (zt_pos t Ht)) (Z_temp t)).
      * exact (inv_pos_correct (Z_temp t) (zt_pos t Ht)).
Qed.

(* T3：逐点 log 分解：log p_b(t,s) ≡ -log Z(t) - e(s)/t *)
Lemma logc_t_log_decomp : forall (t : R) (Ht : lt zero t) (s : S),
  req (log (logc_t_bt t Ht s) (logc_t_bt_pos t Ht s))
      (plus (opp (log (Z_temp t) (zt_pos t Ht)))
            (opp (mult (inv_pos t Ht) (energy s)))).
Proof.
  intros t Ht s.
  apply (req_trans (log (logc_t_bt t Ht s) (logc_t_bt_pos t Ht s))
                   (plus (log (inv_pos (Z_temp t) (zt_pos t Ht))
                              (inv_pos_pos (Z_temp t) (zt_pos t Ht)))
                         (log (exp_neg (mult (inv_pos t Ht) (energy s)))
                              (exp_neg_pos (mult (inv_pos t Ht) (energy s)))))
                   (plus (opp (log (Z_temp t) (zt_pos t Ht)))
                         (opp (mult (inv_pos t Ht) (energy s))))).
  - exact (log_mult (inv_pos (Z_temp t) (zt_pos t Ht))
                    (exp_neg (mult (inv_pos t Ht) (energy s)))
                    (inv_pos_pos (Z_temp t) (zt_pos t Ht))
                    (exp_neg_pos (mult (inv_pos t Ht) (energy s)))).
  - apply req_plus_compat.
    + exact (logd_log_inv_one_inv_of_compat R RIS tsup_compat (Z_temp t)
               (zt_pos t Ht) (inv_pos_pos (Z_temp t) (zt_pos t Ht))).
    + exact (tsup_log_exp_neg (mult (inv_pos t Ht) (energy s))).
Qed.

(* T4：Σ p_b·log p_b ≡ -log Z(t) - E(t)/t（槽 5/6 的中间件） *)
Lemma logc_t_sum_plogp : forall (t : R) (Ht : lt zero t),
  req (sumf (fun s => mult (logc_t_bt t Ht s)
                           (log (logc_t_bt t Ht s) (logc_t_bt_pos t Ht s))))
      (plus (opp (log (Z_temp t) (zt_pos t Ht)))
            (opp (mult (inv_pos t Ht) (logc_t_et t Ht)))).
Proof.
  intros t Ht.
  apply (req_trans (sumf (fun s => mult (logc_t_bt t Ht s)
                            (log (logc_t_bt t Ht s) (logc_t_bt_pos t Ht s))))
                   (sumf (fun s => plus
                               (opp (mult (logc_t_bt t Ht s)
                                          (log (Z_temp t) (zt_pos t Ht))))
                               (opp (mult (logc_t_bt t Ht s)
                                          (mult (inv_pos t Ht) (energy s))))))
                   (plus (opp (log (Z_temp t) (zt_pos t Ht)))
                         (opp (mult (inv_pos t Ht) (logc_t_et t Ht))))).
  - apply tsum_ext. intro s.
    (* bt·log bt ≡ bt·(-logZt - e/t) ≡ opp(bt·logZt) + opp(bt·(e/t)) *)
    apply (req_trans (mult (logc_t_bt t Ht s)
                           (log (logc_t_bt t Ht s) (logc_t_bt_pos t Ht s)))
                     (mult (logc_t_bt t Ht s)
                           (plus (opp (log (Z_temp t) (zt_pos t Ht)))
                                 (opp (mult (inv_pos t Ht) (energy s)))))
                     (plus (opp (mult (logc_t_bt t Ht s)
                                      (log (Z_temp t) (zt_pos t Ht))))
                           (opp (mult (logc_t_bt t Ht s)
                                      (mult (inv_pos t Ht) (energy s)))))).
    + apply (req_mult_compat (logc_t_bt t Ht s) (logc_t_bt t Ht s)
               (log (logc_t_bt t Ht s) (logc_t_bt_pos t Ht s))
               (plus (opp (log (Z_temp t) (zt_pos t Ht)))
                     (opp (mult (inv_pos t Ht) (energy s))))
               (req_refl (logc_t_bt t Ht s))).
      exact (logc_t_log_decomp t Ht s).
    + apply (req_trans (mult (logc_t_bt t Ht s)
                             (plus (opp (log (Z_temp t) (zt_pos t Ht)))
                                   (opp (mult (inv_pos t Ht) (energy s)))))
                       (plus (mult (logc_t_bt t Ht s)
                                   (opp (log (Z_temp t) (zt_pos t Ht))))
                             (mult (logc_t_bt t Ht s)
                                   (opp (mult (inv_pos t Ht) (energy s)))))
                       (plus (opp (mult (logc_t_bt t Ht s)
                                        (log (Z_temp t) (zt_pos t Ht))))
                             (opp (mult (logc_t_bt t Ht s)
                                        (mult (inv_pos t Ht) (energy s)))))).
      * exact (distrib (logc_t_bt t Ht s) (opp (log (Z_temp t) (zt_pos t Ht)))
                  (opp (mult (inv_pos t Ht) (energy s)))).
      * apply (req_plus_compat (mult (logc_t_bt t Ht s)
                                   (opp (log (Z_temp t) (zt_pos t Ht))))
                  (opp (mult (logc_t_bt t Ht s) (log (Z_temp t) (zt_pos t Ht))))
                  (mult (logc_t_bt t Ht s)
                        (opp (mult (inv_pos t Ht) (energy s))))
                  (opp (mult (logc_t_bt t Ht s)
                             (mult (inv_pos t Ht) (energy s))))).
        -- exact (logc_mult_opp_l (logc_t_bt t Ht s)
                    (log (Z_temp t) (zt_pos t Ht))).
        -- exact (logc_mult_opp_l (logc_t_bt t Ht s)
                    (mult (inv_pos t Ht) (energy s))).
  - apply (req_trans (sumf (fun s => plus
                               (opp (mult (logc_t_bt t Ht s)
                                          (log (Z_temp t) (zt_pos t Ht))))
                               (opp (mult (logc_t_bt t Ht s)
                                          (mult (inv_pos t Ht) (energy s))))))
                     (plus (sumf (fun s => opp (mult (logc_t_bt t Ht s)
                                                 (log (Z_temp t)
                                                      (zt_pos t Ht)))))
                           (sumf (fun s => opp (mult (logc_t_bt t Ht s)
                                                 (mult (inv_pos t Ht)
                                                       (energy s))))))
                     (plus (opp (log (Z_temp t) (zt_pos t Ht)))
                           (opp (mult (inv_pos t Ht) (logc_t_et t Ht))))).
    + exact (tsum_add (fun s => opp (mult (logc_t_bt t Ht s)
                             (log (Z_temp t) (zt_pos t Ht))))
                      (fun s => opp (mult (logc_t_bt t Ht s)
                                (mult (inv_pos t Ht) (energy s))))).
    + apply (req_plus_compat
               (sumf (fun s => opp (mult (logc_t_bt t Ht s)
                                   (log (Z_temp t) (zt_pos t Ht)))))
               (opp (log (Z_temp t) (zt_pos t Ht)))
               (sumf (fun s => opp (mult (logc_t_bt t Ht s)
                                   (mult (inv_pos t Ht) (energy s)))))
               (opp (mult (inv_pos t Ht) (logc_t_et t Ht)))).
      * apply (req_trans (sumf (fun s => opp (mult (logc_t_bt t Ht s)
                                   (log (Z_temp t) (zt_pos t Ht)))))
                         (opp (sumf (fun s => mult (logc_t_bt t Ht s)
                                     (log (Z_temp t) (zt_pos t Ht)))))
                         (opp (log (Z_temp t) (zt_pos t Ht)))).
        -- exact (logc_t_sum_opp (fun s => mult (logc_t_bt t Ht s)
                                    (log (Z_temp t) (zt_pos t Ht)))).
        -- apply (req_trans (opp (sumf (fun s => mult (logc_t_bt t Ht s)
                                         (log (Z_temp t) (zt_pos t Ht)))))
                            (opp (mult (log (Z_temp t) (zt_pos t Ht))
                                       (sumf (logc_t_bt t Ht))))
                            (opp (log (Z_temp t) (zt_pos t Ht)))).
           ++ apply req_opp_compat.
              apply (req_trans (sumf (fun s : S => mult (logc_t_bt t Ht s)
                                         (log (Z_temp t) (zt_pos t Ht))))
                               (mult (sumf (logc_t_bt t Ht))
                                     (log (Z_temp t) (zt_pos t Ht)))
                               (mult (log (Z_temp t) (zt_pos t Ht))
                                     (sumf (logc_t_bt t Ht)))).
              ** exact (logc_t_sum_linear_r (log (Z_temp t) (zt_pos t Ht))
                            (logc_t_bt t Ht)).
              ** exact (mult_comm (sumf (logc_t_bt t Ht))
                            (log (Z_temp t) (zt_pos t Ht))).
           ++ apply req_opp_compat.
              apply (req_trans (mult (log (Z_temp t) (zt_pos t Ht))
                                     (sumf (logc_t_bt t Ht)))
                               (mult (log (Z_temp t) (zt_pos t Ht)) one)
                               (log (Z_temp t) (zt_pos t Ht))).
              ** apply (req_mult_compat (log (Z_temp t) (zt_pos t Ht))
                            (log (Z_temp t) (zt_pos t Ht))
                            (sumf (logc_t_bt t Ht)) one
                            (req_refl (log (Z_temp t) (zt_pos t Ht)))
                            (logc_t_normalized t Ht)).
              ** exact (mult_one (log (Z_temp t) (zt_pos t Ht))).
      * apply (req_trans (sumf (fun s => opp (mult (logc_t_bt t Ht s)
                                   (mult (inv_pos t Ht) (energy s)))))
                         (opp (sumf (fun s => mult (logc_t_bt t Ht s)
                                     (mult (inv_pos t Ht) (energy s)))))
                         (opp (mult (inv_pos t Ht) (logc_t_et t Ht)))).
        -- exact (logc_t_sum_opp (fun s => mult (logc_t_bt t Ht s)
                                    (mult (inv_pos t Ht) (energy s)))).
        -- apply (req_trans (opp (sumf (fun s => mult (logc_t_bt t Ht s)
                                         (mult (inv_pos t Ht) (energy s)))))
                            (opp (mult (inv_pos t Ht)
                                       (sumf (fun s => mult (logc_t_bt t Ht s)
                                                (energy s)))))
                            (opp (mult (inv_pos t Ht) (logc_t_et t Ht)))).
           ++ apply req_opp_compat.
              apply (req_trans (sumf (fun s => mult (logc_t_bt t Ht s)
                                        (mult (inv_pos t Ht) (energy s))))
                               (sumf (fun s => mult (inv_pos t Ht)
                                        (mult (logc_t_bt t Ht s) (energy s))))
                               (mult (inv_pos t Ht)
                                 (sumf (fun s => mult (logc_t_bt t Ht s)
                                           (energy s))))).
              ** apply tsum_ext. intro s.
                 apply (req_trans (mult (logc_t_bt t Ht s)
                                    (mult (inv_pos t Ht) (energy s)))
                                  (mult (mult (logc_t_bt t Ht s)
                                          (inv_pos t Ht))
                                    (energy s))
                                  (mult (inv_pos t Ht)
                                    (mult (logc_t_bt t Ht s) (energy s)))).
                 --- exact (mult_assoc (logc_t_bt t Ht s) (inv_pos t Ht)
                              (energy s)).
                 --- apply (req_trans (mult (mult (logc_t_bt t Ht s)
                                          (inv_pos t Ht))
                                    (energy s))
                                      (mult (mult (inv_pos t Ht)
                                              (logc_t_bt t Ht s))
                                        (energy s))
                                      (mult (inv_pos t Ht)
                                        (mult (logc_t_bt t Ht s)
                                          (energy s)))).
                     +++ apply (req_mult_compat
                                  (mult (logc_t_bt t Ht s) (inv_pos t Ht))
                                  (mult (inv_pos t Ht) (logc_t_bt t Ht s))
                                  (energy s) (energy s)
                                  (mult_comm (logc_t_bt t Ht s)
                                             (inv_pos t Ht))
                                  (req_refl (energy s))).
                     +++ apply req_sym.
                         exact (mult_assoc (inv_pos t Ht)
                                  (logc_t_bt t Ht s) (energy s)).
              ** exact (tsum_linear (inv_pos t Ht)
                          (fun s => mult (logc_t_bt t Ht s) (energy s))).
           ++ apply req_opp_compat. apply req_refl.
Qed.

(* T5【槽 5 放电件】：H(t) ≡ E(t)/t + log Z(t) *)
Lemma logc_entropy_temp_explicit : forall (t : R) (Ht : lt zero t),
  req (logc_t_h t Ht)
      (plus (mult (inv_pos t Ht) (logc_t_et t Ht))
            (log (Z_temp t) (zt_pos t Ht))).
Proof.
  intros t Ht.
  apply (req_trans (logc_t_h t Ht)
                   (opp (sumf (fun s => mult (logc_t_bt t Ht s)
                                   (log (logc_t_bt t Ht s)
                                        (logc_t_bt_pos t Ht s)))))
                   (plus (mult (inv_pos t Ht) (logc_t_et t Ht))
                         (log (Z_temp t) (zt_pos t Ht)))).
  - apply (req_trans (logc_t_h t Ht)
                     (sumf (fun s => opp (mult (logc_t_bt t Ht s)
                                 (log (logc_t_bt t Ht s)
                                      (logc_t_bt_pos t Ht s)))))
                     (opp (sumf (fun s => mult (logc_t_bt t Ht s)
                                     (log (logc_t_bt t Ht s)
                                          (logc_t_bt_pos t Ht s)))))).
    + apply tsum_ext. intro s.
      exact (logc_mult_opp_l (logc_t_bt t Ht s)
                (log (logc_t_bt t Ht s) (logc_t_bt_pos t Ht s))).
    + exact (logc_t_sum_opp (fun s => mult (logc_t_bt t Ht s)
                                (log (logc_t_bt t Ht s)
                                     (logc_t_bt_pos t Ht s)))).
  - apply (req_trans (opp (sumf (fun s => mult (logc_t_bt t Ht s)
                                 (log (logc_t_bt t Ht s)
                                      (logc_t_bt_pos t Ht s)))))
                     (opp (plus (opp (log (Z_temp t) (zt_pos t Ht)))
                                (opp (mult (inv_pos t Ht)
                                           (logc_t_et t Ht)))))
                     (plus (mult (inv_pos t Ht) (logc_t_et t Ht))
                           (log (Z_temp t) (zt_pos t Ht)))).
    + apply req_opp_compat.
      exact (logc_t_sum_plogp t Ht).
    + apply (req_trans (opp (plus (opp (log (Z_temp t) (zt_pos t Ht)))
                                  (opp (mult (inv_pos t Ht)
                                             (logc_t_et t Ht)))))
                       (plus (opp (opp (log (Z_temp t) (zt_pos t Ht))))
                             (opp (opp (mult (inv_pos t Ht)
                                             (logc_t_et t Ht)))))
                       (plus (mult (inv_pos t Ht) (logc_t_et t Ht))
                             (log (Z_temp t) (zt_pos t Ht)))).
      * exact (logc_opp_plus (opp (log (Z_temp t) (zt_pos t Ht)))
                 (opp (mult (inv_pos t Ht) (logc_t_et t Ht)))).
      * apply (req_trans (plus (opp (opp (log (Z_temp t) (zt_pos t Ht))))
                               (opp (opp (mult (inv_pos t Ht)
                                           (logc_t_et t Ht)))))
                         (plus (log (Z_temp t) (zt_pos t Ht))
                               (mult (inv_pos t Ht) (logc_t_et t Ht)))
                         (plus (mult (inv_pos t Ht) (logc_t_et t Ht))
                               (log (Z_temp t) (zt_pos t Ht)))).
        -- apply (req_plus_compat (opp (opp (log (Z_temp t) (zt_pos t Ht))))
                      (log (Z_temp t) (zt_pos t Ht))
                      (opp (opp (mult (inv_pos t Ht) (logc_t_et t Ht))))
                      (mult (inv_pos t Ht) (logc_t_et t Ht))).
           ++ exact (logd_req_opp_opp R RIS (log (Z_temp t) (zt_pos t Ht))).
           ++ exact (logd_req_opp_opp R RIS
                      (mult (inv_pos t Ht) (logc_t_et t Ht))).
        -- exact (plus_comm (log (Z_temp t) (zt_pos t Ht))
                  (mult (inv_pos t Ht) (logc_t_et t Ht))).
Qed.

(* T6【槽 6 放电件】：KL(t1‖t2) ≡ -H(t1) + E(t1)/t2 + log Z(t2) *)
Lemma logc_relative_entropy_temp_decomp :
  forall (t2 : R) (Ht2 : lt zero t2) (t1 : R) (Ht1 : lt zero t1),
  req (logc_t_kl t1 t2 Ht1 Ht2)
      (plus (plus (opp (logc_t_h t1 Ht1))
                  (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))
            (log (Z_temp t2) (zt_pos t2 Ht2))).
Proof.
  intros t2 Ht2 t1 Ht1.
  (* Σ p1·log p1 与 Σ p1·(-log p2) 各自显式，sum_add 合并 *)
  assert (Hleft : req (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                (log (logc_t_bt t1 Ht1 s)
                                     (logc_t_bt_pos t1 Ht1 s))))
                     (plus (opp (log (Z_temp t1) (zt_pos t1 Ht1)))
                           (opp (mult (inv_pos t1 Ht1)
                                      (logc_t_et t1 Ht1))))).
  { exact (logc_t_sum_plogp t1 Ht1). }
  assert (Hright : req (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                 (opp (log (logc_t_bt t2 Ht2 s)
                                           (logc_t_bt_pos t2 Ht2 s)))))
                     (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                           (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))).
  { apply (req_trans (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                              (opp (log (logc_t_bt t2 Ht2 s)
                                        (logc_t_bt_pos t2 Ht2 s)))))
                     (sumf (fun s => plus (mult (logc_t_bt t1 Ht1 s)
                                            (log (Z_temp t2) (zt_pos t2 Ht2)))
                                          (mult (logc_t_bt t1 Ht1 s)
                                            (mult (inv_pos t2 Ht2)
                                                  (energy s)))))
                     (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                           (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))).
    - apply tsum_ext. intro s.
      (* p1·(-log p2) ≡ p1·(logZt2 + e/t2) ≡ p1·logZt2 + p1·(e/t2) *)
      apply (req_trans (mult (logc_t_bt t1 Ht1 s)
                             (opp (log (logc_t_bt t2 Ht2 s)
                                       (logc_t_bt_pos t2 Ht2 s))))
                       (mult (logc_t_bt t1 Ht1 s)
                             (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                                   (mult (inv_pos t2 Ht2) (energy s))))
                       (plus (mult (logc_t_bt t1 Ht1 s)
                                   (log (Z_temp t2) (zt_pos t2 Ht2)))
                             (mult (logc_t_bt t1 Ht1 s)
                                   (mult (inv_pos t2 Ht2) (energy s))))).
      + apply (req_mult_compat (logc_t_bt t1 Ht1 s) (logc_t_bt t1 Ht1 s)
                  (opp (log (logc_t_bt t2 Ht2 s) (logc_t_bt_pos t2 Ht2 s)))
                  (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                        (mult (inv_pos t2 Ht2) (energy s)))
                  (req_refl (logc_t_bt t1 Ht1 s))).
        (* -log p2(s) ≡ logZt2 + e/t2（T3 取负换形） *)
        apply (req_trans (opp (log (logc_t_bt t2 Ht2 s)
                                   (logc_t_bt_pos t2 Ht2 s)))
                         (opp (plus (opp (log (Z_temp t2) (zt_pos t2 Ht2)))
                                    (opp (mult (inv_pos t2 Ht2)
                                               (energy s)))))
                         (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                               (mult (inv_pos t2 Ht2) (energy s)))).
        -- apply req_opp_compat.
           exact (logc_t_log_decomp t2 Ht2 s).
        -- apply (req_trans (opp (plus (opp (log (Z_temp t2) (zt_pos t2 Ht2)))
                                       (opp (mult (inv_pos t2 Ht2)
                                                  (energy s)))))
                            (plus (opp (opp (log (Z_temp t2)
                                                 (zt_pos t2 Ht2))))
                                  (opp (opp (mult (inv_pos t2 Ht2)
                                                  (energy s)))))
                            (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                                  (mult (inv_pos t2 Ht2) (energy s)))).
           ++ exact (logc_opp_plus (opp (log (Z_temp t2) (zt_pos t2 Ht2)))
                       (opp (mult (inv_pos t2 Ht2) (energy s)))).
           ++ apply (req_plus_compat
                        (opp (opp (log (Z_temp t2) (zt_pos t2 Ht2))))
                        (log (Z_temp t2) (zt_pos t2 Ht2))
                        (opp (opp (mult (inv_pos t2 Ht2) (energy s))))
                        (mult (inv_pos t2 Ht2) (energy s))).
              ** exact (logd_req_opp_opp R RIS
                          (log (Z_temp t2) (zt_pos t2 Ht2))).
              ** exact (logd_req_opp_opp R RIS
                          (mult (inv_pos t2 Ht2) (energy s))).
      + exact (distrib (logc_t_bt t1 Ht1 s)
                  (log (Z_temp t2) (zt_pos t2 Ht2))
                  (mult (inv_pos t2 Ht2) (energy s))).
    - apply (req_trans (sumf (fun s => plus (mult (logc_t_bt t1 Ht1 s)
                                              (log (Z_temp t2)
                                                   (zt_pos t2 Ht2)))
                                            (mult (logc_t_bt t1 Ht1 s)
                                              (mult (inv_pos t2 Ht2)
                                                    (energy s)))))
                       (plus (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                             (log (Z_temp t2)
                                                  (zt_pos t2 Ht2))))
                             (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                               (mult (inv_pos t2 Ht2)
                                                     (energy s)))))
                       (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                             (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))).
      + exact (tsum_add (fun s => mult (logc_t_bt t1 Ht1 s)
                                  (log (Z_temp t2) (zt_pos t2 Ht2)))
                        (fun s => mult (logc_t_bt t1 Ht1 s)
                                  (mult (inv_pos t2 Ht2) (energy s)))).
      + apply (req_plus_compat (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                         (log (Z_temp t2) (zt_pos t2 Ht2))))
                  (log (Z_temp t2) (zt_pos t2 Ht2))
                  (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                    (mult (inv_pos t2 Ht2) (energy s))))
                  (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1))).
        * apply (req_trans (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                     (log (Z_temp t2) (zt_pos t2 Ht2))))
                           (mult (sumf (logc_t_bt t1 Ht1))
                                  (log (Z_temp t2) (zt_pos t2 Ht2)))
                           (log (Z_temp t2) (zt_pos t2 Ht2))).
          -- exact (logc_t_sum_linear_r (log (Z_temp t2) (zt_pos t2 Ht2))
                       (logc_t_bt t1 Ht1)).
          -- apply (req_trans (mult (sumf (logc_t_bt t1 Ht1))
                                    (log (Z_temp t2) (zt_pos t2 Ht2)))
                              (mult one (log (Z_temp t2) (zt_pos t2 Ht2)))
                              (log (Z_temp t2) (zt_pos t2 Ht2))).
             ++ apply (req_mult_compat (sumf (logc_t_bt t1 Ht1)) one
                          (log (Z_temp t2) (zt_pos t2 Ht2))
                          (log (Z_temp t2) (zt_pos t2 Ht2))
                          (logc_t_normalized t1 Ht1)
                          (req_refl (log (Z_temp t2) (zt_pos t2 Ht2)))).
             ++ exact (logc_mult_one_l (log (Z_temp t2) (zt_pos t2 Ht2))).
        * apply (req_trans (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                     (mult (inv_pos t2 Ht2) (energy s))))
                           (mult (inv_pos t2 Ht2)
                                  (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                                    (energy s))))
                           (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1))).
          -- apply (req_trans (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                        (mult (inv_pos t2 Ht2) (energy s))))
                              (sumf (fun s => mult (inv_pos t2 Ht2)
                                        (mult (logc_t_bt t1 Ht1 s) (energy s))))
                              (mult (inv_pos t2 Ht2)
                                (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                                  (energy s))))).
             ++ apply tsum_ext. intro s.
                 apply (req_trans (mult (logc_t_bt t1 Ht1 s)
                                    (mult (inv_pos t2 Ht2) (energy s)))
                                  (mult (mult (logc_t_bt t1 Ht1 s)
                                          (inv_pos t2 Ht2))
                                    (energy s))
                                  (mult (inv_pos t2 Ht2)
                                    (mult (logc_t_bt t1 Ht1 s) (energy s)))).
                 --- exact (mult_assoc (logc_t_bt t1 Ht1 s) (inv_pos t2 Ht2)
                              (energy s)).
                 --- apply (req_trans (mult (mult (logc_t_bt t1 Ht1 s)
                                          (inv_pos t2 Ht2))
                                    (energy s))
                                      (mult (mult (inv_pos t2 Ht2)
                                              (logc_t_bt t1 Ht1 s))
                                        (energy s))
                                      (mult (inv_pos t2 Ht2)
                                        (mult (logc_t_bt t1 Ht1 s)
                                          (energy s)))).
                     +++ apply (req_mult_compat
                                  (mult (logc_t_bt t1 Ht1 s) (inv_pos t2 Ht2))
                                  (mult (inv_pos t2 Ht2) (logc_t_bt t1 Ht1 s))
                                  (energy s) (energy s)
                                  (mult_comm (logc_t_bt t1 Ht1 s)
                                             (inv_pos t2 Ht2))
                                  (req_refl (energy s))).
                     +++ apply req_sym.
                         exact (mult_assoc (inv_pos t2 Ht2)
                                  (logc_t_bt t1 Ht1 s) (energy s)).
             ++ exact (tsum_linear (inv_pos t2 Ht2)
                         (fun s => mult (logc_t_bt t1 Ht1 s) (energy s))).
          -- apply req_refl. }
  (* KL ≡ Σ p1·log p1 + Σ p1·(-log p2)；目标 = T5 换形后的 -H1 项 + 右项 *)
  apply (req_trans (logc_t_kl t1 t2 Ht1 Ht2)
                   (plus (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                   (log (logc_t_bt t1 Ht1 s)
                                        (logc_t_bt_pos t1 Ht1 s))))
                         (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                   (opp (log (logc_t_bt t2 Ht2 s)
                                             (logc_t_bt_pos t2 Ht2 s))))))
                   (plus (plus (opp (logc_t_h t1 Ht1))
                               (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))
                         (log (Z_temp t2) (zt_pos t2 Ht2)))).
  - apply (req_trans (logc_t_kl t1 t2 Ht1 Ht2)
                     (sumf (fun s => plus (mult (logc_t_bt t1 Ht1 s)
                                            (log (logc_t_bt t1 Ht1 s)
                                                 (logc_t_bt_pos t1 Ht1 s)))
                                          (mult (logc_t_bt t1 Ht1 s)
                                            (opp (log (logc_t_bt t2 Ht2 s)
                                                      (logc_t_bt_pos t2 Ht2 s))))))
                     (plus (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                   (log (logc_t_bt t1 Ht1 s)
                                        (logc_t_bt_pos t1 Ht1 s))))
                           (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                     (opp (log (logc_t_bt t2 Ht2 s)
                                               (logc_t_bt_pos t2 Ht2 s))))))).
    + apply tsum_ext. intro s.
      exact (distrib (logc_t_bt t1 Ht1 s)
                (log (logc_t_bt t1 Ht1 s) (logc_t_bt_pos t1 Ht1 s))
                (opp (log (logc_t_bt t2 Ht2 s) (logc_t_bt_pos t2 Ht2 s)))).
    + exact (tsum_add (fun s => mult (logc_t_bt t1 Ht1 s)
                        (log (logc_t_bt t1 Ht1 s) (logc_t_bt_pos t1 Ht1 s)))
                      (fun s => mult (logc_t_bt t1 Ht1 s)
                        (opp (log (logc_t_bt t2 Ht2 s)
                                  (logc_t_bt_pos t2 Ht2 s))))).
  - apply (req_trans (plus (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                  (log (logc_t_bt t1 Ht1 s)
                                       (logc_t_bt_pos t1 Ht1 s))))
                           (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                                     (opp (log (logc_t_bt t2 Ht2 s)
                                               (logc_t_bt_pos t2 Ht2 s))))))
                     (plus (plus (opp (log (Z_temp t1) (zt_pos t1 Ht1)))
                                 (opp (mult (inv_pos t1 Ht1)
                                            (logc_t_et t1 Ht1))))
                           (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                                 (mult (inv_pos t2 Ht2)
                                       (logc_t_et t1 Ht1))))
                     (plus (plus (opp (logc_t_h t1 Ht1))
                                 (mult (inv_pos t2 Ht2)
                                       (logc_t_et t1 Ht1)))
                           (log (Z_temp t2) (zt_pos t2 Ht2)))).
    + apply (req_plus_compat
                (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                          (log (logc_t_bt t1 Ht1 s) (logc_t_bt_pos t1 Ht1 s))))
                (plus (opp (log (Z_temp t1) (zt_pos t1 Ht1)))
                      (opp (mult (inv_pos t1 Ht1) (logc_t_et t1 Ht1))))
                (sumf (fun s => mult (logc_t_bt t1 Ht1 s)
                          (opp (log (logc_t_bt t2 Ht2 s)
                                    (logc_t_bt_pos t2 Ht2 s)))))
                (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                      (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))).
      * exact Hleft.
      * exact Hright.
    + (* 置换收口：(-logZ1 - E1/t1) + (logZ2 + E1/t2) ≡ (-H1 + E1/t2) + logZ2 *)
      assert (HoppH1 : req (opp (logc_t_h t1 Ht1))
                           (plus (opp (mult (inv_pos t1 Ht1)
                                           (logc_t_et t1 Ht1)))
                                 (opp (log (Z_temp t1) (zt_pos t1 Ht1))))).
      { apply (req_trans (opp (logc_t_h t1 Ht1))
                         (opp (plus (mult (inv_pos t1 Ht1)
                                          (logc_t_et t1 Ht1))
                                    (log (Z_temp t1) (zt_pos t1 Ht1))))
                         (plus (opp (mult (inv_pos t1 Ht1)
                                          (logc_t_et t1 Ht1)))
                               (opp (log (Z_temp t1) (zt_pos t1 Ht1))))).
        - apply req_opp_compat.
          exact (logc_entropy_temp_explicit t1 Ht1).
        - exact (logc_opp_plus (mult (inv_pos t1 Ht1) (logc_t_et t1 Ht1))
                  (log (Z_temp t1) (zt_pos t1 Ht1))). }
      apply (req_trans (plus (plus (opp (log (Z_temp t1) (zt_pos t1 Ht1)))
                                   (opp (mult (inv_pos t1 Ht1)
                                              (logc_t_et t1 Ht1))))
                             (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                                   (mult (inv_pos t2 Ht2)
                                         (logc_t_et t1 Ht1))))
                       (plus (plus (opp (mult (inv_pos t1 Ht1)
                                              (logc_t_et t1 Ht1)))
                                   (opp (log (Z_temp t1)
                                             (zt_pos t1 Ht1))))
                             (plus (mult (inv_pos t2 Ht2)
                                         (logc_t_et t1 Ht1))
                                   (log (Z_temp t2) (zt_pos t2 Ht2))))
                       (plus (plus (opp (logc_t_h t1 Ht1))
                                   (mult (inv_pos t2 Ht2)
                                         (logc_t_et t1 Ht1)))
                             (log (Z_temp t2) (zt_pos t2 Ht2)))).
      * apply (req_plus_compat
                  (plus (opp (log (Z_temp t1) (zt_pos t1 Ht1)))
                    (opp (mult (inv_pos t1 Ht1) (logc_t_et t1 Ht1))))
                  (plus (opp (mult (inv_pos t1 Ht1) (logc_t_et t1 Ht1)))
                    (opp (log (Z_temp t1) (zt_pos t1 Ht1))))
                  (plus (log (Z_temp t2) (zt_pos t2 Ht2))
                    (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))
                  (plus (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1))
                    (log (Z_temp t2) (zt_pos t2 Ht2)))).
        -- exact (plus_comm (opp (log (Z_temp t1) (zt_pos t1 Ht1)))
                               (opp (mult (inv_pos t1 Ht1)
                                          (logc_t_et t1 Ht1)))).
        -- exact (plus_comm (log (Z_temp t2) (zt_pos t2 Ht2))
                               (mult (inv_pos t2 Ht2)
                                         (logc_t_et t1 Ht1))).
      * apply (req_trans (plus (plus (opp (mult (inv_pos t1 Ht1)
                                                 (logc_t_et t1 Ht1)))
                                       (opp (log (Z_temp t1)
                                                 (zt_pos t1 Ht1))))
                                  (plus (mult (inv_pos t2 Ht2)
                                              (logc_t_et t1 Ht1))
                                    (log (Z_temp t2) (zt_pos t2 Ht2))))
                         (plus (plus (plus (opp (mult (inv_pos t1 Ht1)
                                                        (logc_t_et t1 Ht1)))
                                              (opp (log (Z_temp t1)
                                                        (zt_pos t1 Ht1))))
                                        (mult (inv_pos t2 Ht2)
                                              (logc_t_et t1 Ht1)))
                                  (log (Z_temp t2) (zt_pos t2 Ht2)))
                         (plus (plus (opp (logc_t_h t1 Ht1))
                                     (mult (inv_pos t2 Ht2)
                                           (logc_t_et t1 Ht1)))
                               (log (Z_temp t2) (zt_pos t2 Ht2)))).
        -- exact (plus_assoc (plus (opp (mult (inv_pos t1 Ht1)
                                                  (logc_t_et t1 Ht1)))
                                   (opp (log (Z_temp t1) (zt_pos t1 Ht1))))
                             (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1))
                             (log (Z_temp t2) (zt_pos t2 Ht2))).
        -- apply (req_plus_compat
                    (plus (plus (opp (mult (inv_pos t1 Ht1)
                                                (logc_t_et t1 Ht1)))
                                  (opp (log (Z_temp t1)
                                            (zt_pos t1 Ht1))))
                            (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))
                    (plus (opp (logc_t_h t1 Ht1))
                      (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1)))
                    (log (Z_temp t2) (zt_pos t2 Ht2))
                    (log (Z_temp t2) (zt_pos t2 Ht2))).
           ++ apply (req_plus_compat
                        (plus (opp (mult (inv_pos t1 Ht1) (logc_t_et t1 Ht1)))
                          (opp (log (Z_temp t1) (zt_pos t1 Ht1))))
                        (opp (logc_t_h t1 Ht1))
                        (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1))
                        (mult (inv_pos t2 Ht2) (logc_t_et t1 Ht1))).
              ** exact (req_sym
                          (opp (logc_t_h t1 Ht1))
                          (plus (opp (mult (inv_pos t1 Ht1)
                                           (logc_t_et t1 Ht1)))
                                (opp (log (Z_temp t1) (zt_pos t1 Ht1))))
                          HoppH1).
              ** apply req_refl.
           ++ apply req_refl.
Qed.

End LogcTemp.

(* ============================================================ *)
(* 闭合性审计（G3 关：主放电件 Print Assumptions）                          *)
(* ============================================================ *)
Print Assumptions logc_energy_in_log_boltzmann.
Print Assumptions logc_free_energy_boltzmann.
Print Assumptions logc_fe_kl_decomp.
Print Assumptions logc_real_kl_decomp_full.
Print Assumptions logc_entropy_temp_explicit.
Print Assumptions logc_relative_entropy_temp_decomp.
Print Assumptions logc_boltzmann_normalized.
Print Assumptions logc_boltz_log_decomp.
Print Assumptions logc_t_log_decomp.
Print Assumptions logc_t_sum_plogp.
