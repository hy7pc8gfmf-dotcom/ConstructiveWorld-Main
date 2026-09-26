(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(* ToyR 玩具证替换件 ——   工程包AC（tier2 末段第一批）      *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   uac_npx_cross（原 L182，2 句强证）	*)
(* ============================================================ *)

(* UpReqAlignClose.v — 位CYC6（组 E-STAGING-CYC6）-C1 桥首步施工件
   ====================================================================
   两个深链假设位（req_backward_kl_identity :434 / req_policy_improvement_mono
   :630）以同位定理形态装载；log-mult 全字段桥（Align2:877 配方）req 世界移植。
   引擎供给（零新引擎）：
     - UpReqAlign2.v:877 req2_pi_next_log_decomp（配方源文件，:884-959 逐字移植）
     - UpReqAlign3.v:3162 req2_backward_kl_step（主定理三点恒等式，无条件五段）
   施工纪律：纯 term-mode req_trans 链；log_mult 见证位逐字 mult_positive 形；
   既有文件零改（G07:652 阻塞注记不回改，另出对账声明——见文件尾）。
   ==================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlign3.
Require UpReqU2.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* UacClose：同位装载节（节参数与 ReqAlignCore/Req2AlignCore 逐位对齐）  *)
(*   证人面：posd/nrm1/KLR/PSTRR/NPXR/... 全部为上游闭名 δ 透明包装      *)
(*   （E346/E370 定型三步： δ 透明包装一次喂定，语句层逐位同位）。    *)
(* ============================================================ *)
Section UacClose.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.

(* ---- 求和对接面（批 3/闭合节同位四槽） ---- *)
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).

(* ---- 接口缺口桥两槽（ReqAlignCore 原生 log_req_compat +
        Align2 增槽 log_inv_exp_neg_req；Real 层无条件实例化消解留
        log_req_compat_real@UpReqU2 模板先例） ---- *)
Hypothesis log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Hypothesis log_inv_exp_neg_req :
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.

(* ---- 节参数（ReqAlignCore/Req2AlignCore 同位；eta 三件为
        r2_policy_improvement_mono 参面喂定所需） ---- *)
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable eta : R.
Variable eta_pos : lt zero eta.
Variable eta_le_one : le eta one.
(* T4R 注记（既有节签调整后）：本 Variable 在 :89/:91 canonical 化后已无传参位（闲置保留，防下游语句面引用断裂）； pi_star_req/req_pi_star_pos 现由 UpReqAlign.Z_align_pos 依赖模块内部供正性。 *)
Variable Z_align_pos : lt zero (@Z_align_req R RIS S sumf reward beta beta_pos pi_ref).

(* ---- B 类桥槽同位运输（Align3:1451 req2_gibbs_inequality 的 req 语句位；
        KL≥0 plain-le 形=序无消去墙，诚实保留，与 Align3 同因同位） ---- *)
Hypothesis uac_gibbs_le_zero :
  forall (p q : S -> R) (Hp : @pos_dist R RIS S p) (Hq : @pos_dist R RIS S q),
    le zero (@relative_entropy_req R RIS S sumf p q Hp Hq).

(* ---- δ 透明包装（req 世界闭名；unfold 后即上游定义体，零转换摩擦） ---- *)
Definition uac_posd (p : S -> R) : Set := @pos_dist R RIS S p.
Definition uac_nrm1 (p : S -> R) : Set := @norm_one R RIS S sumf p.
Definition uac_KLR (p q : S -> R) :
    @pos_dist R RIS S p -> @pos_dist R RIS S q -> R :=
  @relative_entropy_req R RIS S sumf p q.
Definition uac_PSTRR (s : S) : R :=
  @pi_star_req R RIS S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos s.
Definition uac_PSTRR_pos : @pos_dist R RIS S uac_PSTRR :=
  @req_pi_star_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos.

(* T4R 桥（既有节签调整后）：PSTR（自绑 Z_align_pos 槽）与 canonical uac_PSTRR
   的逐点 req——两者仅差 inv_pos 的正性证明参（Z_align_pos 变量 vs
   UpReqAlign.Z_align_pos 内部依赖模块实例）；req_mult_cancel_l + inv_pos_correct
   双折运输。kl_move 证人槽由 req_refl 改喂本桥。 *)
Lemma uac_pstr_cross : forall s : S,
  req (@PSTR R RIS S sumf reward beta beta_pos pi_ref Z_align_pos s) (uac_PSTRR s).
Proof.
  intro s.
  apply (req_mult_compat _ _ _ _
    (req_mult_cancel_l (Z_align_req S sumf reward beta beta_pos pi_ref) _ _
       Z_align_pos
       (req_trans _ _ _
          (inv_pos_correct (Z_align_req S sumf reward beta beta_pos pi_ref)
             Z_align_pos)
          (req_sym _ _
             (inv_pos_correct (Z_align_req S sumf reward beta beta_pos pi_ref)
                (@UpReqAlign.Z_align_pos R RIS S sumf sum_pos reward beta beta_pos
                   pi_ref pi_ref_pos)))))
    (req_refl (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))).
Qed.
Definition uac_ADR (pi_t : S -> R) (Hpi_t : @pos_dist R RIS S pi_t) (s : S) : R :=
  @advantage_aug_req R RIS S reward beta pi_ref pi_ref_pos pi_t Hpi_t s.
Definition uac_ZRR (pi_t : S -> R) (Hpi_t : @pos_dist R RIS S pi_t) : R :=
  @Z_rel_req R RIS S sumf reward beta beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t.
Definition uac_ZRR_pos (pi_t : S -> R) (Hpi_t : @pos_dist R RIS S pi_t) :
    lt zero (uac_ZRR pi_t Hpi_t) :=
  @req_Z_rel_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
                 eta pi_t Hpi_t.
Definition uac_NPXR (pi_t : S -> R) (Hpi_t : @pos_dist R RIS S pi_t) (s : S) : R :=
  @pi_next_req R RIS S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
               eta pi_t Hpi_t s.
Definition uac_NPXR_pos (pi_t : S -> R) (Hpi_t : @pos_dist R RIS S pi_t) :
    @pos_dist R RIS S (uac_NPXR pi_t Hpi_t) :=
  fun s => @req_pi_next_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                            pi_ref_pos eta pi_t Hpi_t s.
Definition uac_AOR (p : S -> R) (Hp : @pos_dist R RIS S p) : R :=
  @align_objective_req R RIS S sumf reward beta pi_ref pi_ref_pos p Hp.
Definition uac_AER (s : S) : R :=
  @align_energy_req R RIS S reward beta pi_ref pi_ref_pos s.

(* ============================================================ *)
(* 第一件：log-mult 全字段桥（Align2:877 req2_pi_next_log_decomp 配方
   逐字移植 req 世界）——log(pi_next(s)) 三段展开在嵌套积
   mult ivZ (mult (pi_t s) expm) 上按接口字段见证位逐层取 log_mult
   乘法律；G07:659「接口字段缺口」所指引擎，本件落盘。                *)
(* ============================================================ *)
Lemma uac_pi_next_log_decomp :
  forall (pi_t : S -> R) (Hpi_t : @pos_dist R RIS S pi_t) (s : S),
    req (log (uac_NPXR pi_t Hpi_t s) (uac_NPXR_pos pi_t Hpi_t s))
        (plus (log (pi_t s) (Hpi_t s))
              (plus (mult (mult eta (inv_pos beta beta_pos))
                          (uac_ADR pi_t Hpi_t s))
                    (opp (log (uac_ZRR pi_t Hpi_t)
                              (uac_ZRR_pos pi_t Hpi_t))))).
Proof.
  intros pi_t Hpi_t s.
  set (iv := inv_pos beta beta_pos).
  set (lg := log (pi_t s) (Hpi_t s)).
  set (lgZ := log (uac_ZRR pi_t Hpi_t) (uac_ZRR_pos pi_t Hpi_t)).
  set (X := mult (mult eta iv) (uac_ADR pi_t Hpi_t s)).
  set (expm := exp_neg (opp X)).
  set (ivZ := inv_pos (uac_ZRR pi_t Hpi_t) (uac_ZRR_pos pi_t Hpi_t)).
  (* 证人显式（Qed 件不可 delta；先经 log_req_compat 开门，其后全透明） *)
  set (Hp1 := inv_pos_pos (uac_ZRR pi_t Hpi_t) (uac_ZRR_pos pi_t Hpi_t)).
  set (Hp2 := mult_positive (pi_t s) expm (Hpi_t s) (exp_neg_pos (opp X))).
  set (HpI := mult_positive ivZ (mult (pi_t s) expm) Hp1 Hp2).
  set (Wit := uac_NPXR_pos pi_t Hpi_t s).
  assert (Hstep12 : req (log (mult ivZ (mult (pi_t s) expm)) HpI)
                        (plus (opp lgZ) (plus lg X))).
  { exact (req_trans (log (mult ivZ (mult (pi_t s) expm)) HpI)
           (plus (opp lgZ) (log (mult (pi_t s) expm) Hp2))
           (plus (opp lgZ) (plus lg X))
           (req_trans (log (mult ivZ (mult (pi_t s) expm)) HpI)
                      (plus (log ivZ Hp1) (log (mult (pi_t s) expm) Hp2))
                      (plus (opp lgZ) (log (mult (pi_t s) expm) Hp2))
                      (log_mult ivZ (mult (pi_t s) expm) Hp1 Hp2)
                      (req_plus_compat (log ivZ Hp1) (opp lgZ)
                                       (log (mult (pi_t s) expm) Hp2)
                                       (log (mult (pi_t s) expm) Hp2)
                                       (@req_log_inv_one_inv R RIS log_req_compat
                                                            (uac_ZRR pi_t Hpi_t)
                                                            (uac_ZRR_pos pi_t Hpi_t))
                                       (req_refl (log (mult (pi_t s) expm) Hp2))))
           (req_plus_compat (opp lgZ) (opp lgZ)
                            (log (mult (pi_t s) expm) Hp2) (plus lg X)
                            (req_refl (opp lgZ))
                            (req_trans (log (mult (pi_t s) expm) Hp2)
                                       (plus lg (log expm (exp_neg_pos (opp X))))
                                       (plus lg X)
                                       (log_mult (pi_t s) expm (Hpi_t s)
                                                 (exp_neg_pos (opp X)))
                                       (req_plus_compat lg lg
                                                        (log expm (exp_neg_pos (opp X))) X
                                                        (req_refl lg)
                                                        (req_trans
                                                           (log expm (exp_neg_pos (opp X)))
                                                           (opp (opp X)) X
                                                           (@req_log_exp_neg R RIS log_inv_exp_neg_req (opp X))
                                                           (req_double_neg X)))))). }
  exact (req_trans (log (uac_NPXR pi_t Hpi_t s) Wit)
                   (log (mult ivZ (mult (pi_t s) expm)) HpI)
                   (plus lg (plus X (opp lgZ)))
                   (log_req_compat (uac_NPXR pi_t Hpi_t s)
                                   (mult ivZ (mult (pi_t s) expm))
                                   Wit HpI (req_refl (uac_NPXR pi_t Hpi_t s)))
                   (req_trans (log (mult ivZ (mult (pi_t s) expm)) HpI)
                              (plus (opp lgZ) (plus lg X))
                              (plus lg (plus X (opp lgZ)))
                              Hstep12
                              (req_trans (plus (opp lgZ) (plus lg X))
                              (plus (plus (opp lgZ) lg) X)
                              (plus lg (plus X (opp lgZ)))
                              (plus_assoc (opp lgZ) lg X)
                              (req_trans (plus (plus (opp lgZ) lg) X)
                                         (plus (plus lg (opp lgZ)) X)
                                         (plus lg (plus X (opp lgZ)))
                                         (req_plus_compat (plus (opp lgZ) lg)
                                                          (plus lg (opp lgZ)) X X
                                                          (plus_comm (opp lgZ) lg)
                                                          (req_refl X))
                                         (req_trans (plus (plus lg (opp lgZ)) X)
                                                    (plus lg (plus (opp lgZ) X))
                                                    (plus lg (plus X (opp lgZ)))
                                                    (req_sym (plus lg (plus (opp lgZ) X))
                                                             (plus (plus lg (opp lgZ)) X)
                                                             (plus_assoc lg (opp lgZ) X))
                                                    (req_plus_compat lg lg
                                                                     (plus (opp lgZ) X)
                                                                     (plus X (opp lgZ))
                                                                     (req_refl lg)
                                                                     (plus_comm (opp lgZ) X))))))).
Qed.

(* ============================================================ *)
(* 重述底货（E-卡 U2Machine：正性见证是数据，跨世界一跳过渡件）          *)
(* ============================================================ *)

(* req2/req 双世界 pi_next 项桥（inv_pos 证人位重述：req2_Z_rel_pos →
   req_Z_rel_pos；inv_pos_ext 接口字段开门，乘法律闭合） *)
Lemma uac_npx_cross :
  forall (pi_t : S -> R) (Hpi_t : @pos_dist R RIS S pi_t) (s : S),
    req (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
              eta pi_t Hpi_t s)
        (uac_NPXR pi_t Hpi_t s).
Proof.
  intros pi_t Hpi_t s.
  apply (req_mult_compat
           (inv_pos (@req2_Z_rel R RIS S sumf reward beta beta_pos pi_ref
                                  pi_ref_pos eta pi_t Hpi_t)
                    (@req2_Z_rel_pos R RIS S sumf sum_pos reward beta beta_pos
                                     pi_ref pi_ref_pos eta pi_t Hpi_t))
           (inv_pos (uac_ZRR pi_t Hpi_t) (uac_ZRR_pos pi_t Hpi_t))
           (mult (pi_t s)
                 (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                     (@req2_adv R RIS S reward beta pi_ref
                                                pi_ref_pos pi_t Hpi_t s)))))
           (mult (pi_t s)
                 (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                     (uac_ADR pi_t Hpi_t s)))))
           (inv_pos_ext (@req2_Z_rel R RIS S sumf reward beta beta_pos pi_ref
                                      pi_ref_pos eta pi_t Hpi_t)
                        (uac_ZRR pi_t Hpi_t)
                        (@req2_Z_rel_pos R RIS S sumf sum_pos reward beta beta_pos
                                         pi_ref pi_ref_pos eta pi_t Hpi_t)
                        (uac_ZRR_pos pi_t Hpi_t)
                        (req_refl (uac_ZRR pi_t Hpi_t)))
           (req_refl (mult (pi_t s)
                           (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                               (uac_ADR pi_t Hpi_t s))))))).
Qed.

(* KL 双参数移动桥（底点逐点 req + 双侧证人自由重述；
   sum_ext + log_req_compat x↔y 组装，E-卡 U2Machine 同型） *)
Lemma uac_kl_move :
  forall (p1 p2 q1 q2 : S -> R)
         (Hp1 : @pos_dist R RIS S p1) (Hp2 : @pos_dist R RIS S p2)
         (Hq1 : @pos_dist R RIS S q1) (Hq2 : @pos_dist R RIS S q2),
    (forall s : S, req (p1 s) (p2 s)) ->
    (forall s : S, req (q1 s) (q2 s)) ->
    req (uac_KLR p1 q1 Hp1 Hq1) (uac_KLR p2 q2 Hp2 Hq2).
Proof.
  intros p1 p2 q1 q2 Hp1 Hp2 Hq1 Hq2 H12 H34.
  unfold uac_KLR, relative_entropy_req.
  apply (sum_ext
           (fun s => mult (p1 s)
                          (req_minus (log (p1 s) (Hp1 s)) (log (q1 s) (Hq1 s))))
           (fun s => mult (p2 s)
                          (req_minus (log (p2 s) (Hp2 s)) (log (q2 s) (Hq2 s))))).
  intro s.
  apply (req_mult_compat (p1 s) (p2 s)
           (req_minus (log (p1 s) (Hp1 s)) (log (q1 s) (Hq1 s)))
           (req_minus (log (p2 s) (Hp2 s)) (log (q2 s) (Hq2 s)))
           (H12 s)).
  unfold req_minus.
  apply (req_plus_compat (log (p1 s) (Hp1 s)) (log (p2 s) (Hp2 s))
                         (opp (log (q1 s) (Hq1 s))) (opp (log (q2 s) (Hq2 s)))
                         (log_req_compat (p1 s) (p2 s) (Hp1 s) (Hp2 s) (H12 s))
                         (req_opp_compat (log (q1 s) (Hq1 s)) (log (q2 s) (Hq2 s))
                                         (log_req_compat (q1 s) (q2 s) (Hq1 s)
                                                         (Hq2 s) (H34 s)))).
Qed.

(* 对齐自由能移动桥（uac_AOR 重述底货） *)
Lemma uac_F_move :
  forall (p1 p2 : S -> R)
         (Hp1 : @pos_dist R RIS S p1) (Hp2 : @pos_dist R RIS S p2),
    (forall s : S, req (p1 s) (p2 s)) ->
    req (@F_align_req R RIS S sumf reward beta pi_ref pi_ref_pos p1 Hp1)
        (@F_align_req R RIS S sumf reward beta pi_ref pi_ref_pos p2 Hp2).
Proof.
  intros p1 p2 Hp1 Hp2 H12.
  unfold F_align_req.
  apply (req_plus_compat
           (sumf (fun s => mult (p1 s) (uac_AER s)))
           (sumf (fun s => mult (p2 s) (uac_AER s)))
           (mult beta (sumf (fun s => mult (p1 s) (log (p1 s) (Hp1 s)))))
           (mult beta (sumf (fun s => mult (p2 s) (log (p2 s) (Hp2 s)))))).
  - apply (sum_ext (fun s => mult (p1 s) (uac_AER s))
                   (fun s => mult (p2 s) (uac_AER s))).
    intro s.
    apply (req_mult_compat (p1 s) (p2 s) (uac_AER s) (uac_AER s) (H12 s)
                           (req_refl (uac_AER s))).
  - apply (req_mult_compat beta beta
           (sumf (fun s => mult (p1 s) (log (p1 s) (Hp1 s))))
           (sumf (fun s => mult (p2 s) (log (p2 s) (Hp2 s))))
           (req_refl beta)).
    apply (sum_ext (fun s => mult (p1 s) (log (p1 s) (Hp1 s)))
                   (fun s => mult (p2 s) (log (p2 s) (Hp2 s)))).
    intro s.
    apply (req_mult_compat (p1 s) (p2 s) (log (p1 s) (Hp1 s)) (log (p2 s) (Hp2 s))
                           (H12 s)
                           (log_req_compat (p1 s) (p2 s) (Hp1 s) (Hp2 s) (H12 s))).
Qed.

(* ============================================================ *)
(* 第二件（槽一）：req_backward_kl_identity 假设位语句同位装载
   （UpReqAlign.v:434-442 逐位同形；依赖模块 = Align3:3162
   req2_backward_kl_step 无条件五段主定理，经 uac_kl_move 证人重述
   一跳过渡；G07:652 阻塞裁决就此翻案——见文件尾声明）。              *)
(* ============================================================ *)
Lemma uac_req_backward_kl_identity :
  forall (pi_t : S -> R) (Hpi_t : @pos_dist R RIS S pi_t)
         (Hnorm : @norm_one R RIS S sumf pi_t),
    req (uac_KLR uac_PSTRR (uac_NPXR pi_t Hpi_t) uac_PSTRR_pos
             (uac_NPXR_pos pi_t Hpi_t))
        (plus (mult (req_minus one eta)
                    (uac_KLR uac_PSTRR pi_t uac_PSTRR_pos Hpi_t))
              (plus (opp (mult eta (uac_KLR pi_t uac_PSTRR Hpi_t uac_PSTRR_pos)))
                    (uac_KLR pi_t (uac_NPXR pi_t Hpi_t) Hpi_t
                                 (uac_NPXR_pos pi_t Hpi_t)))).
Proof.
  intros pi_t Hpi_t Hnorm.
  apply (req_trans
           (uac_KLR uac_PSTRR (uac_NPXR pi_t Hpi_t) uac_PSTRR_pos
                    (uac_NPXR_pos pi_t Hpi_t))
           (uac_KLR (@PSTR R RIS S sumf reward beta beta_pos pi_ref Z_align_pos)
                    (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref
                          pi_ref_pos eta pi_t Hpi_t)
                    (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref
                               pi_ref_pos Z_align_pos)
                    (@npx_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                              pi_ref_pos eta pi_t Hpi_t))
           (plus (mult (req_minus one eta)
                       (uac_KLR uac_PSTRR pi_t uac_PSTRR_pos Hpi_t))
                 (plus (opp (mult eta (uac_KLR pi_t uac_PSTRR Hpi_t uac_PSTRR_pos)))
                       (uac_KLR pi_t (uac_NPXR pi_t Hpi_t) Hpi_t
                                (uac_NPXR_pos pi_t Hpi_t))))).
  - exact (req_sym
             (uac_KLR (@PSTR R RIS S sumf reward beta beta_pos pi_ref Z_align_pos)
                      (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref
                            pi_ref_pos eta pi_t Hpi_t)
                      (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref
                                 pi_ref_pos Z_align_pos)
                      (@npx_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                                pi_ref_pos eta pi_t Hpi_t))
             (uac_KLR uac_PSTRR (uac_NPXR pi_t Hpi_t) uac_PSTRR_pos
                      (uac_NPXR_pos pi_t Hpi_t))
             (uac_kl_move
             (@PSTR R RIS S sumf reward beta beta_pos pi_ref Z_align_pos)
             uac_PSTRR
             (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
                   eta pi_t Hpi_t)
             (uac_NPXR pi_t Hpi_t)
             (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref pi_ref_pos
                        Z_align_pos)
             uac_PSTRR_pos
             (@npx_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                       pi_ref_pos eta pi_t Hpi_t)
             (uac_NPXR_pos pi_t Hpi_t)
             (fun s => uac_pstr_cross s)
             (fun s => uac_npx_cross pi_t Hpi_t s))).
  - apply (req_trans
             (uac_KLR (@PSTR R RIS S sumf reward beta beta_pos pi_ref Z_align_pos)
                      (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref
                            pi_ref_pos eta pi_t Hpi_t)
                      (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref
                                 pi_ref_pos Z_align_pos)
                      (@npx_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                                pi_ref_pos eta pi_t Hpi_t))
             (plus (mult (req_minus one eta)
                         (uac_KLR (@PSTR R RIS S sumf reward beta beta_pos pi_ref
                                        Z_align_pos)
                                  pi_t
                                  (@PSTR_pos R RIS S sumf reward beta beta_pos
                                             pi_ref pi_ref_pos Z_align_pos)
                                  Hpi_t))
                   (plus (opp (mult eta
                                    (uac_KLR pi_t
                                             (@PSTR R RIS S sumf reward beta
                                                    beta_pos pi_ref Z_align_pos)
                                             Hpi_t
                                             (@PSTR_pos R RIS S sumf reward beta
                                                        beta_pos pi_ref pi_ref_pos
                                                        Z_align_pos))))
                         (uac_KLR pi_t
                                  (@NPX R RIS S sumf sum_pos reward beta beta_pos
                                        pi_ref pi_ref_pos eta pi_t Hpi_t)
                                  Hpi_t
                                  (@npx_pos R RIS S sumf sum_pos reward beta
                                            beta_pos pi_ref pi_ref_pos eta pi_t
                                            Hpi_t))))
             (plus (mult (req_minus one eta)
                         (uac_KLR uac_PSTRR pi_t uac_PSTRR_pos Hpi_t))
                   (plus (opp (mult eta (uac_KLR pi_t uac_PSTRR Hpi_t uac_PSTRR_pos)))
                         (uac_KLR pi_t (uac_NPXR pi_t Hpi_t) Hpi_t
                                  (uac_NPXR_pos pi_t Hpi_t))))).
    + exact (@req2_backward_kl_step R RIS S sumf sum_ext sum_add sum_linear
                  sum_pos log_req_compat log_inv_exp_neg_req reward beta beta_pos
                  pi_ref pi_ref_pos eta Z_align_pos pi_t Hpi_t Hnorm).
    + apply (req_plus_compat
                (mult (req_minus one eta)
                      (uac_KLR (@PSTR R RIS S sumf reward beta beta_pos pi_ref
                                       Z_align_pos)
                               pi_t
                               (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref
                                          pi_ref_pos Z_align_pos)
                               Hpi_t))
                (mult (req_minus one eta)
                      (uac_KLR uac_PSTRR pi_t uac_PSTRR_pos Hpi_t))
                (plus (opp (mult eta
                                 (uac_KLR pi_t
                                          (@PSTR R RIS S sumf reward beta beta_pos
                                                 pi_ref Z_align_pos)
                                          Hpi_t
                                          (@PSTR_pos R RIS S sumf reward beta
                                                     beta_pos pi_ref pi_ref_pos
                                                     Z_align_pos))))
                      (uac_KLR pi_t
                               (@NPX R RIS S sumf sum_pos reward beta beta_pos
                                     pi_ref pi_ref_pos eta pi_t Hpi_t)
                               Hpi_t
                               (@npx_pos R RIS S sumf sum_pos reward beta beta_pos
                                         pi_ref pi_ref_pos eta pi_t Hpi_t)))
                (plus (opp (mult eta (uac_KLR pi_t uac_PSTRR Hpi_t uac_PSTRR_pos)))
                      (uac_KLR pi_t (uac_NPXR pi_t Hpi_t) Hpi_t
                               (uac_NPXR_pos pi_t Hpi_t)))).
      * apply (req_mult_compat (req_minus one eta) (req_minus one eta)
                  (uac_KLR (@PSTR R RIS S sumf reward beta beta_pos pi_ref
                                 Z_align_pos)
                           pi_t
                           (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref
                                      pi_ref_pos Z_align_pos)
                           Hpi_t)
                  (uac_KLR uac_PSTRR pi_t uac_PSTRR_pos Hpi_t)
                  (req_refl (req_minus one eta))
                  (uac_kl_move
                     (@PSTR R RIS S sumf reward beta beta_pos pi_ref Z_align_pos)
                     uac_PSTRR pi_t pi_t
                     (@PSTR_pos R RIS S sumf reward beta beta_pos pi_ref
                                pi_ref_pos Z_align_pos)
                     uac_PSTRR_pos Hpi_t Hpi_t
                     (fun s => uac_pstr_cross s)
                     (fun s => req_refl (pi_t s)))).
      * apply (req_plus_compat
                  (opp (mult eta
                            (uac_KLR pi_t
                                     (@PSTR R RIS S sumf reward beta beta_pos
                                            pi_ref Z_align_pos)
                                     Hpi_t
                                     (@PSTR_pos R RIS S sumf reward beta beta_pos
                                                pi_ref pi_ref_pos Z_align_pos))))
                  (opp (mult eta (uac_KLR pi_t uac_PSTRR Hpi_t uac_PSTRR_pos)))
                  (uac_KLR pi_t
                           (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref
                                 pi_ref_pos eta pi_t Hpi_t)
                           Hpi_t
                           (@npx_pos R RIS S sumf sum_pos reward beta beta_pos
                                     pi_ref pi_ref_pos eta pi_t Hpi_t))
                  (uac_KLR pi_t (uac_NPXR pi_t Hpi_t) Hpi_t
                           (uac_NPXR_pos pi_t Hpi_t))
                  (req_opp_compat
                     (mult eta
                           (uac_KLR pi_t
                                    (@PSTR R RIS S sumf reward beta beta_pos
                                           pi_ref Z_align_pos)
                                    Hpi_t
                                    (@PSTR_pos R RIS S sumf reward beta beta_pos
                                               pi_ref pi_ref_pos Z_align_pos)))
                     (mult eta (uac_KLR pi_t uac_PSTRR Hpi_t uac_PSTRR_pos))
                     (req_mult_compat eta eta
                        (uac_KLR pi_t
                                 (@PSTR R RIS S sumf reward beta beta_pos pi_ref
                                        Z_align_pos)
                                 Hpi_t
                                 (@PSTR_pos R RIS S sumf reward beta beta_pos
                                            pi_ref pi_ref_pos Z_align_pos))
                        (uac_KLR pi_t uac_PSTRR Hpi_t uac_PSTRR_pos)
                        (req_refl eta)
                        (uac_kl_move pi_t
                                     pi_t
                                     (@PSTR R RIS S sumf reward beta beta_pos
                                            pi_ref Z_align_pos)
                                     uac_PSTRR Hpi_t Hpi_t
                                     (@PSTR_pos R RIS S sumf reward beta beta_pos
                                                pi_ref pi_ref_pos Z_align_pos)
                                     uac_PSTRR_pos
                                     (fun s => req_refl (pi_t s))
                                     (fun s => uac_pstr_cross s))))
                  (uac_kl_move pi_t
                               pi_t
                               (@NPX R RIS S sumf sum_pos reward beta beta_pos
                                     pi_ref pi_ref_pos eta pi_t Hpi_t)
                               (uac_NPXR pi_t Hpi_t) Hpi_t Hpi_t
                               (@npx_pos R RIS S sumf sum_pos reward beta beta_pos
                                         pi_ref pi_ref_pos eta pi_t Hpi_t)
                               (uac_NPXR_pos pi_t Hpi_t)
                               (fun s => req_refl (pi_t s))
                               (fun s => uac_npx_cross pi_t Hpi_t s))).
Qed.

(* ============================================================ *)
(* 第二件（槽二）：req_policy_improvement_mono 假设位语句同位装载
   （UpReqAlign.v:630-633 逐位同形；依赖模块 = Align3:1456
   r2_policy_improvement_mono，经 uac_F_move 证人重述一跳过渡；
   uac_gibbs_le_zero 槽同位直接代入）。                                   *)
(* ============================================================ *)
Lemma uac_req_policy_improvement_mono :
  forall (pi_t : S -> R) (Hpi_t : @pos_dist R RIS S pi_t)
         (Hnorm : @norm_one R RIS S sumf pi_t),
    le (uac_AOR pi_t Hpi_t)
       (uac_AOR (uac_NPXR pi_t Hpi_t) (uac_NPXR_pos pi_t Hpi_t)).
Proof.
  intros pi_t Hpi_t Hnorm.
  assert (Hmid : req (uac_AOR (@NPX R RIS S sumf sum_pos reward beta beta_pos
                                    pi_ref pi_ref_pos eta pi_t Hpi_t)
                              (@npx_pos R RIS S sumf sum_pos reward beta beta_pos
                                        pi_ref pi_ref_pos eta pi_t Hpi_t))
                     (uac_AOR (uac_NPXR pi_t Hpi_t) (uac_NPXR_pos pi_t Hpi_t))).
  { unfold uac_AOR, align_objective_req.
    apply (req_opp_compat
             (@F_align_req R RIS S sumf reward beta pi_ref pi_ref_pos
                           (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref
                                 pi_ref_pos eta pi_t Hpi_t)
                           (@npx_pos R RIS S sumf sum_pos reward beta beta_pos
                                     pi_ref pi_ref_pos eta pi_t Hpi_t))
             (@F_align_req R RIS S sumf reward beta pi_ref pi_ref_pos
                           (uac_NPXR pi_t Hpi_t)
                           (uac_NPXR_pos pi_t Hpi_t))).
    apply (uac_F_move
             (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
                   eta pi_t Hpi_t)
             (uac_NPXR pi_t Hpi_t)
             (@npx_pos R RIS S sumf sum_pos reward beta beta_pos pi_ref
                       pi_ref_pos eta pi_t Hpi_t)
             (uac_NPXR_pos pi_t Hpi_t)
             (fun s => uac_npx_cross pi_t Hpi_t s)). }
  exact (le_id_r (uac_AOR pi_t Hpi_t)
                 (uac_AOR (@NPX R RIS S sumf sum_pos reward beta beta_pos pi_ref
                                pi_ref_pos eta pi_t Hpi_t)
                          (@npx_pos R RIS S sumf sum_pos reward beta beta_pos
                                    pi_ref pi_ref_pos eta pi_t Hpi_t))
                 (uac_AOR (uac_NPXR pi_t Hpi_t) (uac_NPXR_pos pi_t Hpi_t))
                 Hmid
                 (@r2_policy_improvement_mono R RIS S sumf sum_ext sum_add
                    sum_linear sum_pos log_req_compat log_inv_exp_neg_req reward
                    beta beta_pos pi_ref pi_ref_pos eta eta_pos eta_le_one
                    uac_gibbs_le_zero pi_t Hpi_t Hnorm)).
Qed.

End UacClose.

(* ============================================================ *)
(* 对账声明段（两桥放行）——G07:655/UpReqAlign 尾清单对账注记              *)
(* ============================================================ *)
(* 一、G07_KLWall.v:652-659 [阻塞裁决] 翻案（结论过时，引 -C1桥判定.md
   组 E-STAGING-CYC6 实测）：
   G07:658-659 结论「构造性引擎不在盘……precise 阻塞词：softmax-KL 深链
   log-mult 接口字段缺口」已过时。引擎三件实测在盘（grep 全库实证）：
     1. log-mult 全字段桥 = UpReqAlign2.v:877 req2_pi_next_log_decomp
        （:893-896 证人显式 Hp1/Hp2/HpI，log_req_compat 开门 + log_mult
        全字段双吃）——本件 uac_pi_next_log_decomp 照 :884-959 配方逐字
        移植 req 世界，缺口引擎落盘；
     2. 深链主定理 = UpReqAlign3.v:3162 req2_backward_kl_step（无条件 Qed
        五段组装：HA β·KSN=FE差 / HB t13_hexp / HC·HK split /
        HD 坍缩 / HE iv 成形 + β 逆吸收闭合）；
     3. 对偶槽 = UpReqAlign3.v:1456 r2_policy_improvement_mono。
   失准点复述：G07 引证 GeomD 头部③「接口字段无 log-mult 全字段故不在其
   scope」系 GeomD 节内接口局限外推为全库结论；同波 G05_LogSmall.v:1267
   自记「log_mult / exp_neg_plus 在案」。                                        *)
(* 二、UpReqAlign.v 尾清单对账（深链挂起清单第 1/2/3 条）：
   第 1 条 req_backward_kl_identity（本文件 :434 假设位）→ 本件
   uac_req_backward_kl_identity 同位装载（槽语句逐位同形，δ 透明包装
   E370 语句层转换判据）；
   第 2 条 req_policy_improvement_mono（本文件 :630 假设位）→ 本件
   uac_req_policy_improvement_mono 同位装载；
   第 3 条主定理链（req_policy_iter_kl_geom_step / _iter /
   req_dpo_loss_iter_mono）两桥放行后全链闭合路径：以本件两 uac 定理
   同位替换 UpReqAlign:484/:645 的假设位使用点即得无条件 req 定理
   （链上其余 req 侧运输与序代数内容批 3 已真证，尾清单自记）。               *)
(* 三、诚实前提面（装载件签名，供兑现批对账）：
   uac_pi_next_log_decomp —— sum 四槽 + log_req_compat +
     log_inv_exp_neg_req（前五槽为 ReqAlignCore 原生节参，第六槽为
     Align2 增槽；Real 层无条件实例化消解沿 log_req_compat_real@UpReqU2 模板）；
   uac_req_backward_kl_identity —— 同上（主定理参面 ZAL_pos 证人位由本节
     Z_align_pos 直接代入，pi_ref_norm/eta_pos/eta_le_one 参面剪除不出现）；
   uac_req_policy_improvement_mono —— 同上 + uac_gibbs_le_zero
     （B 类 KL≥0 plain-le 槽，Align3:1451 req2_gibbs_inequality 同位运输；
     序无消去=LPO 家族墙，与 UpReqAlign 冻结清单第 1 条同因，诚实保留）。
   四关状态：本件 G1/G2 自验；G3 提取检验与 G4 rocqchk 留待四关组。        *)
(* 四、界外件声明：G07:648-654 [跳过] req_step_kl_eta_bound 不在本件 scope
   （GeomD eps 形已实例化消解，plain-le 闭合属 Or 形=X 红线，防重复不重建）；
   既有文件零改（本件为纯新建 shim，V-F2/CWD6/CWE5 领地未触碰）。            *)
(* ============================================================ *)

Print Assumptions uac_pi_next_log_decomp.
Print Assumptions uac_req_backward_kl_identity.
Print Assumptions uac_req_policy_improvement_mono.

(* ---- ToyR 追印：清单件假设面逐件打印，判读全闭 ---- *)
Print Assumptions uac_npx_cross.
