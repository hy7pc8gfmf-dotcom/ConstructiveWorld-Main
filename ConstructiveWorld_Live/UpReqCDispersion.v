(* ============================================================ *)
(* UpReqCDispersion.v —— C 档余槽批量放电席 T26（log_req_compat 9 实例打头） *)
(*   2026-09-11；承席N2 Top3 判词：「G5 logd_ 闭合实例与 LogCompD 六槽收口  *)
(*   已把『需新基元』降维成『Require+实例化』纯组装；9 实例同形一喂即收」  *)
(* ------------------------------------------------------------------ *)
(* 槽位名单（普查 attn/T2①槽位普查与放电分级-20260910.md C 档区段）：      *)
(*   s1 UpReqAlgebra:1492   ReqLogBridge   （下游 3 件）                  *)
(*   s2 UpReqAlign:75       ReqAlignCore   （下游 1 件）                  *)
(*   s3 UpReqAlign:698      ReqKLProjection（下游 4 件）                  *)
(*   s4 UpReqAlign2:81      Req2AlignCore  （下游 7 件）                  *)
(*   s5 UpReqAlign3:72      Req3AlignCore  （下游 21 件）                 *)
(*   s6 UpReqU2:307         ReqU2FixedPoint（下游 12 件）                 *)
(*   s7 UpReqFEPAttn:97     ReqFEPAttn     （下游 2 件）                  *)
(*   s8 UpReqFEPAttn:344    ReqFEPLogZ     （下游 2 件）                  *)
(*   s9 UpAlignIdReq:134    AlignGapReq    （下游 6 件）                  *)
(* 供给（G5 G05_LogSmall UpReqLogPrimD Real 层闭合件，上游已建成）：        *)
(*   B1 logd_log_compat_real        ——9 槽 log_req_compat 同形一喂        *)
(*   B4 logd_log_inv_exp_neg_real   ——伴生槽 log_inv_exp_neg_req（s5/s9） *)
(* 放电形态（纯组装，两层）：                                             *)
(*   Part A：9 槽语句 Real 层闭合证书（载体重命名 R:=Real、喂 B1）         *)
(*   Part C：9 槽普查点名下游件的 Real 实例化——compat 槽喂 B1、            *)
(*     log_inv_exp_neg_req 槽喂 B4（每件=槽真插入位类型化证据）；          *)
(*     sum 面槽保持接口型参数位（t22_bool_sumf 两点载体为其 Real 满足证，  *)
(*     上游在盘；其 raw real_eq/real_lt →接口 req/lt 换装会在提取层生成    *)
(*     Obj.bridge 残留——实测 15 处，本席如实不 ship，留接口扩展批。       *)
(* 诚实边界：s6 w2_gibbs_eq / req_u2_fixed_point_unique 等还吃 log_le_    *)
(*   linear / log_eq_linear 等号槽（普查 S 档 G6 属，构造性逆向桥不可证    *)
(*   判词在 G5 头注与 UpRealLeB 尾注台账）——本席不触，只放 compat 单槽。  *)
(* 红线：Set 层零 Prop 泄露（结论全 req/lt 接口 Set 值）；全 Qed 闭合；     *)
(*   既有文件零改；零 git；新名 t26_ 前缀（2026-09-11 全库 grep 零命中）。 *)
(* 编译配方：_t26_run.ps1 温控包装（cpu_guard CoreN 3 绑核）               *)
(*   coqc -q [-vos] -Q voTree "" -Q Live_X "" <件>.v                      *)
(*   G4：coqchk -Q voTree "" -Q Live_X "" UpReqCDispersion                *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import G05_LogSmall.
Require Import UpReqEntropyUniqueTemp.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlign3.
Require Import UpReqU2.
Require Import UpReqFEPAttn.
Require Import UpAlignIdReq.

Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Part A：9 槽 log_req_compat 语句 Real 层闭合证书（同形批，B1 直喂）      *)
(*   槽形（普查原文）：forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),  *)
(*   req x y -> req (log x Hx) (log y Hy)；载体重命名 R := Real，          *)
(*   RIS := RealEnhancedReal（S07 Instance，CW219 Export 链入域）。        *)
(* ============================================================ *)

(* 槽 s1：UpReqAlgebra:1492（ReqLogBridge） *)
Theorem t26_s1_algebra_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* 槽 s2：UpReqAlign:75（ReqAlignCore） *)
Theorem t26_s2_align_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* 槽 s3：UpReqAlign:698（ReqKLProjection） *)
Theorem t26_s3_alignklp_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* 槽 s4：UpReqAlign2:81（Req2AlignCore） *)
Theorem t26_s4_align2_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* 槽 s5：UpReqAlign3:72（Req3AlignCore） *)
Theorem t26_s5_align3_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* 槽 s6：UpReqU2:307（ReqU2FixedPoint） *)
Theorem t26_s6_u2_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* 槽 s7：UpReqFEPAttn:97（ReqFEPAttn） *)
Theorem t26_s7_fepattn_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* 槽 s8：UpReqFEPAttn:344（ReqFEPLogZ） *)
Theorem t26_s8_feplogz_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* 槽 s9：UpAlignIdReq:134（AlignGapReq） *)
Theorem t26_s9_alignid_log_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Qed.

(* ============================================================ *)
(* Part B：bool 两点求和载面（下游实例化的 sumf 供给位）                    *)
(*   载体复用 t22_bool_sumf（= real_list_sum bool f [true;false]，         *)
(*   UpReqEntropyUniqueTemp L73；raw real_eq/real_lt 满足证四件同在盘）。   *)
(* ============================================================ *)

Definition t26_bsum (f : bool -> Real) : Real := t22_bool_sumf f.

(* ============================================================ *)
(* Part C：普查点名下游件 Real 实例化（compat 槽喂 B1、log_inv_exp_neg_req  *)
(*   槽喂 B4；sum 面槽为接口型参数位——见头注诚实边界）                     *)
(* ============================================================ *)

(* ---- s1 UpReqAlgebra ReqLogBridge（普查点名 req_log_inv_one_inv@1519、  *)
(*      req_log_div@1536；本节无节参，compat 单槽直喂，全 Concrete） ---- *)

Theorem t26_s1_req_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x),
    req (log (inv_pos x Hx) (inv_pos_pos x Hx)) (opp (log x Hx)).
Proof.
  intros x Hx.
  exact (@UpReqAlgebra.req_log_inv_one_inv Real RealEnhancedReal
           logd_log_compat_real x Hx).
Qed.

Theorem t26_s1_req_log_div :
  forall (a b : Real) (Ha : lt zero a) (Hb : lt zero b),
    req (log (mult a (inv_pos b Hb))
             (mult_positive a (inv_pos b Hb) Ha (inv_pos_pos b Hb)))
        (req_minus (log a Ha) (log b Hb)).
Proof.
  intros a b Ha Hb.
  exact (@UpReqAlgebra.req_log_div Real RealEnhancedReal
           logd_log_compat_real a b Ha Hb).
Qed.

(* ---- s2 UpReqAlign ReqAlignCore（普查点名 req_free_energy_align_ext@251； *)
(*      载体 S:=bool、sumf:=t26_bsum；sum_ext 槽接口型参数位） ---- *)

Theorem t26_s2_req_free_energy_align_ext :
  forall (sum_ext : forall f g : bool -> Real,
            (forall s : bool, req (f s) (g s)) ->
            req (t26_bsum f) (t26_bsum g))
    (reward : bool -> Real) (beta : Real)
    (pi_ref : bool -> Real)
    (pi_ref_pos : forall s : bool, lt zero (pi_ref s))
    (f g : bool -> Real)
    (Hf : UpReqAlign.pos_dist bool f) (Hg : UpReqAlign.pos_dist bool g),
    (forall s : bool, req (f s) (g s)) ->
    req (UpReqAlign.F_align_req bool t26_bsum reward beta pi_ref pi_ref_pos f Hf)
        (UpReqAlign.F_align_req bool t26_bsum reward beta pi_ref pi_ref_pos g Hg).
Proof.
  intros sum_ext reward beta pi_ref pi_ref_pos f g Hf Hg Hfg.
  exact (@UpReqAlign.req_free_energy_align_ext Real RealEnhancedReal
           bool t26_bsum sum_ext logd_log_compat_real
           reward beta pi_ref pi_ref_pos f g Hf Hg Hfg).
Qed.

(* ---- s3 UpReqAlign ReqKLProjection（普查点名 rkl_log_inv_one_inv@871、  *)
(*      req_log_proj_pass@910；后者零 sum 槽，全 Concrete） ---- *)

Theorem t26_s3_rkl_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x),
    req (log (inv_pos x Hx) (inv_pos_pos x Hx)) (opp (log x Hx)).
Proof.
  intros x Hx.
  exact (@UpReqAlign.rkl_log_inv_one_inv Real RealEnhancedReal
           logd_log_compat_real x Hx).
Qed.

Theorem t26_s3_req_log_proj_pass :
  forall (post_aud : bool -> bool) (p : bool -> Real)
    (Hp_pos : forall s : bool, lt zero (p s))
    (HZ : lt zero (UpReqAlign.Z_aud_req bool t26_bsum post_aud p))
    (s : bool) (E : post_aud s = true),
    req (log (UpReqAlign.projected_distribution_req bool t26_bsum post_aud p HZ s)
             (UpReqAlign.req_projected_pass_pos bool t26_bsum post_aud p Hp_pos HZ s E))
        (plus (log (p s) (Hp_pos s))
              (log (inv_pos (UpReqAlign.Z_aud_req bool t26_bsum post_aud p) HZ)
                   (inv_pos_pos (UpReqAlign.Z_aud_req bool t26_bsum post_aud p) HZ))).
Proof.
  intros post_aud p Hp_pos HZ s E.
  exact (@UpReqAlign.req_log_proj_pass Real RealEnhancedReal
           bool t26_bsum logd_log_compat_real
           post_aud p Hp_pos HZ s E).
Qed.

(* ---- s4 UpReqAlign2 Req2AlignCore（普查点名 req2_log_inv_one_inv@335）-- *)

Theorem t26_s4_req2_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x),
    req (log (inv_pos x Hx) (inv_pos_pos x Hx)) (opp (log x Hx)).
Proof.
  intros x Hx.
  exact (@UpReqAlign2.req2_log_inv_one_inv Real RealEnhancedReal
           logd_log_compat_real x Hx).
Qed.

(* ---- s5 UpReqAlign3 Req3AlignCore（普查点名 r2_log_inv_opp@1511、        *)
(*      w_F_t_rel_decomp@163；后者四 sum 槽接口型参数位 + B4 直喂）       ---- *)

Theorem t26_s5_r2_log_inv_opp :
  forall (x : Real) (Hx : lt zero x),
    req (log (inv_pos x Hx) (inv_pos_pos x Hx)) (opp (log x Hx)).
Proof.
  intros x Hx.
  exact (@UpReqAlign3.r2_log_inv_opp Real RealEnhancedReal
           logd_log_compat_real x Hx).
Qed.

Theorem t26_s5_w_F_t_rel_decomp :
  forall (sum_ext : forall f g : bool -> Real,
            (forall s : bool, req (f s) (g s)) ->
            req (t26_bsum f) (t26_bsum g))
    (sum_add : forall f g : bool -> Real,
            req (t26_bsum (fun s => plus (f s) (g s)))
                (plus (t26_bsum f) (t26_bsum g)))
    (sum_linear : forall (a : Real) (f : bool -> Real),
            req (t26_bsum (fun s => mult a (f s))) (mult a (t26_bsum f)))
    (sum_pos : forall f : bool -> Real,
            (forall s : bool, lt zero (f s)) -> lt zero (t26_bsum f))
    (reward : bool -> Real) (beta : Real)
    (beta_pos : lt zero beta)
    (pi_ref : bool -> Real)
    (pi_ref_pos : forall s : bool, lt zero (pi_ref s))
    (eta : Real)
    (pi_t : bool -> Real) (Hpi_t : UpReqAlign3.pos3 bool pi_t),
    UpReqAlign3.nrm bool t26_bsum pi_t ->
    req (UpReqAlign3.FE bool t26_bsum
           (UpReqAlign3.ET bool reward beta pi_ref pi_ref_pos eta pi_t Hpi_t)
           beta pi_t Hpi_t)
        (plus (UpReqAlign3.FE bool t26_bsum
                 (UpReqAlign3.ET bool reward beta pi_ref pi_ref_pos eta pi_t Hpi_t)
                 beta
                 (UpReqAlign3.NPX bool t26_bsum sum_pos reward beta beta_pos
                    pi_ref pi_ref_pos eta pi_t Hpi_t)
                 (UpReqAlign3.npx_pos bool t26_bsum sum_pos reward beta beta_pos
                    pi_ref pi_ref_pos eta pi_t Hpi_t))
              (mult beta
                 (UpReqAlign3.KLE bool t26_bsum pi_t
                    (UpReqAlign3.NPX bool t26_bsum sum_pos reward beta beta_pos
                       pi_ref pi_ref_pos eta pi_t Hpi_t)
                    Hpi_t
                    (UpReqAlign3.npx_pos bool t26_bsum sum_pos reward beta beta_pos
                       pi_ref pi_ref_pos eta pi_t Hpi_t)))).
Proof.
  intros sum_ext sum_add sum_linear sum_pos
         reward beta beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t Hnrm.
  exact (@UpReqAlign3.w_F_t_rel_decomp Real RealEnhancedReal
           bool t26_bsum sum_ext sum_add sum_linear sum_pos
           logd_log_compat_real logd_log_inv_exp_neg_real
           reward beta beta_pos pi_ref pi_ref_pos eta pi_t Hpi_t Hnrm).
Qed.

(* ---- s6 UpReqU2 ReqU2FixedPoint（普查点名 r2u_FA_witness_ext@392；       *)
(*      w2_gibbs_eq/req_u2_fixed_point_unique 另吃 S 档等号槽，本席不触） ---- *)

Theorem t26_s6_r2u_FA_witness_ext :
  forall (sum_ext : forall f g : bool -> Real,
            (forall s : bool, req (f s) (g s)) ->
            req (t26_bsum f) (t26_bsum g))
    (reward : bool -> Real) (beta : Real)
    (pi_ref : bool -> Real)
    (pi_ref_pos : forall s : bool, lt zero (pi_ref s))
    (p : bool -> Real) (Hp Hq : UpReqU2.pos3 bool p),
    req (UpReqU2.FA bool t26_bsum reward beta pi_ref pi_ref_pos p Hp)
        (UpReqU2.FA bool t26_bsum reward beta pi_ref pi_ref_pos p Hq).
Proof.
  intros sum_ext reward beta pi_ref pi_ref_pos p Hp Hq.
  exact (@UpReqU2.r2u_FA_witness_ext Real RealEnhancedReal
           bool t26_bsum sum_ext logd_log_compat_real
           reward beta pi_ref pi_ref_pos p Hp Hq).
Qed.

(* ---- s7 UpReqFEPAttn ReqFEPAttn（普查点名 req_fep_F_ext@180） -------- *)

Theorem t26_s7_req_fep_F_ext :
  forall (sum_ext : forall f g : bool -> Real,
            (forall s : bool, req (f s) (g s)) ->
            req (t26_bsum f) (t26_bsum g))
    (z : bool -> Real) (T : Real) (p q : bool -> Real)
    (Hp : forall s : bool, lt zero (p s))
    (Hq : forall s : bool, lt zero (q s)),
    req (t26_bsum p) one ->
    req (t26_bsum q) one ->
    (forall s : bool, req (p s) (q s)) ->
    req (UpReqFEPAttn.F_attn bool t26_bsum z T p Hp)
        (UpReqFEPAttn.F_attn bool t26_bsum z T q Hq).
Proof.
  intros sum_ext z T p q Hp Hq Hnp Hnq Hpq.
  exact (@UpReqFEPAttn.req_fep_F_ext Real RealEnhancedReal
           bool t26_bsum sum_ext logd_log_compat_real
           z T p q Hp Hq Hnp Hnq Hpq).
Qed.

(* ---- s8 UpReqFEPAttn ReqFEPLogZ（普查点名 req_fep_F_ext_logz@395） ---- *)

Theorem t26_s8_req_fep_F_ext_logz :
  forall (sum_ext : forall f g : bool -> Real,
            (forall s : bool, req (f s) (g s)) ->
            req (t26_bsum f) (t26_bsum g))
    (z : bool -> Real) (T : Real) (p q : bool -> Real)
    (Hp : forall s : bool, lt zero (p s))
    (Hq : forall s : bool, lt zero (q s)),
    (forall s : bool, req (p s) (q s)) ->
    req (UpReqFEPAttn.lz_F_attn bool t26_bsum z T p Hp)
        (UpReqFEPAttn.lz_F_attn bool t26_bsum z T q Hq).
Proof.
  intros sum_ext z T p q Hp Hq Hpq.
  exact (@UpReqFEPAttn.req_fep_F_ext_logz Real RealEnhancedReal
           bool t26_bsum sum_ext logd_log_compat_real
           z T p q Hp Hq Hpq).
Qed.

(* ---- s9 UpAlignIdReq AlignGapReq（普查点名 w_gap_base@172、              *)
(*      w_subgap_base@187；四 sum 槽接口型参数位 + B4 直喂）             ---- *)

Theorem t26_s9_w_gap_base :
  forall (sum_ext : forall f g : bool -> Real,
            (forall s : bool, req (f s) (g s)) ->
            req (t26_bsum f) (t26_bsum g))
    (sum_add : forall f g : bool -> Real,
            req (t26_bsum (fun s => plus (f s) (g s)))
                (plus (t26_bsum f) (t26_bsum g)))
    (sum_linear : forall (a : Real) (f : bool -> Real),
            req (t26_bsum (fun s => mult a (f s))) (mult a (t26_bsum f)))
    (sum_pos : forall f : bool -> Real,
            (forall s : bool, lt zero (f s)) -> lt zero (t26_bsum f))
    (reward : bool -> Real) (beta : Real)
    (beta_pos : lt zero beta)
    (pi_ref : bool -> Real)
    (pi_ref_pos : forall s : bool, lt zero (pi_ref s))
    (eta : Real) (eta_pos : lt zero eta)
    (pi_t : bool -> Real) (Hpi_t : UpAlignIdReq.pos3 bool pi_t),
    UpAlignIdReq.nrm bool t26_bsum pi_t ->
    req (req_minus
           (UpAlignIdReq.JJ bool t26_bsum reward beta pi_ref pi_ref_pos
              (UpAlignIdReq.NPX bool t26_bsum sum_pos reward beta beta_pos
                 pi_ref pi_ref_pos eta pi_t Hpi_t)
              (UpAlignIdReq.npx_pos bool t26_bsum sum_pos reward beta beta_pos
                 pi_ref pi_ref_pos eta pi_t Hpi_t))
           (UpAlignIdReq.JJ bool t26_bsum reward beta pi_ref pi_ref_pos pi_t Hpi_t))
        (mult beta
           (plus (mult (req_minus (inv_pos eta eta_pos) one)
                    (UpAlignIdReq.KLE bool t26_bsum
                       (UpAlignIdReq.NPX bool t26_bsum sum_pos reward beta beta_pos
                          pi_ref pi_ref_pos eta pi_t Hpi_t)
                       pi_t
                       (UpAlignIdReq.npx_pos bool t26_bsum sum_pos reward beta beta_pos
                          pi_ref pi_ref_pos eta pi_t Hpi_t)
                       Hpi_t))
                 (mult (inv_pos eta eta_pos)
                    (UpAlignIdReq.KLE bool t26_bsum pi_t
                       (UpAlignIdReq.NPX bool t26_bsum sum_pos reward beta beta_pos
                          pi_ref pi_ref_pos eta pi_t Hpi_t)
                       Hpi_t
                       (UpAlignIdReq.npx_pos bool t26_bsum sum_pos reward beta beta_pos
                          pi_ref pi_ref_pos eta pi_t Hpi_t))))).
Proof.
  intros sum_ext sum_add sum_linear sum_pos
         reward beta beta_pos pi_ref pi_ref_pos eta eta_pos pi_t Hpi_t Hnrm.
  exact (@UpAlignIdReq.w_gap_base Real RealEnhancedReal
           bool t26_bsum sum_ext sum_add sum_linear sum_pos
           logd_log_compat_real logd_log_inv_exp_neg_real
           reward beta beta_pos pi_ref pi_ref_pos eta eta_pos pi_t Hpi_t Hnrm).
Qed.

Theorem t26_s9_w_subgap_base :
  forall (sum_ext : forall f g : bool -> Real,
            (forall s : bool, req (f s) (g s)) ->
            req (t26_bsum f) (t26_bsum g))
    (sum_add : forall f g : bool -> Real,
            req (t26_bsum (fun s => plus (f s) (g s)))
                (plus (t26_bsum f) (t26_bsum g)))
    (sum_linear : forall (a : Real) (f : bool -> Real),
            req (t26_bsum (fun s => mult a (f s))) (mult a (t26_bsum f)))
    (reward : bool -> Real) (beta : Real)
    (beta_pos : lt zero beta)
    (pi_ref : bool -> Real)
    (pi_ref_pos : forall s : bool, lt zero (pi_ref s))
    (ZAL_pos : lt zero
                 (UpAlignIdReq.ZAL bool t26_bsum reward beta beta_pos pi_ref))
    (p : bool -> Real) (Hp : UpAlignIdReq.pos3 bool p),
    UpAlignIdReq.nrm bool t26_bsum p ->
    req (req_minus
           (UpAlignIdReq.JJ bool t26_bsum reward beta pi_ref pi_ref_pos
              (UpAlignIdReq.PSTR bool t26_bsum reward beta beta_pos pi_ref ZAL_pos)
              (UpAlignIdReq.PSTR_pos bool t26_bsum reward beta beta_pos pi_ref
                 pi_ref_pos ZAL_pos))
           (UpAlignIdReq.JJ bool t26_bsum reward beta pi_ref pi_ref_pos p Hp))
        (mult beta
           (UpAlignIdReq.KLE bool t26_bsum p
              (UpAlignIdReq.PSTR bool t26_bsum reward beta beta_pos pi_ref ZAL_pos)
              Hp
              (UpAlignIdReq.PSTR_pos bool t26_bsum reward beta beta_pos pi_ref
                 pi_ref_pos ZAL_pos))).
Proof.
  intros sum_ext sum_add sum_linear
         reward beta beta_pos pi_ref pi_ref_pos ZAL_pos p Hp Hnrm.
  exact (@UpAlignIdReq.w_subgap_base Real RealEnhancedReal
           bool t26_bsum sum_ext sum_add sum_linear
           logd_log_compat_real logd_log_inv_exp_neg_real
           reward beta beta_pos pi_ref pi_ref_pos ZAL_pos p Hp Hnrm).
Qed.

(* ============================================================ *)
(* 闭合性审计（G3 关：全件 Print Assumptions）                             *)
(* ============================================================ *)
Print Assumptions t26_s1_algebra_log_compat.
Print Assumptions t26_s2_align_log_compat.
Print Assumptions t26_s3_alignklp_log_compat.
Print Assumptions t26_s4_align2_log_compat.
Print Assumptions t26_s5_align3_log_compat.
Print Assumptions t26_s6_u2_log_compat.
Print Assumptions t26_s7_fepattn_log_compat.
Print Assumptions t26_s8_feplogz_log_compat.
Print Assumptions t26_s9_alignid_log_compat.
Print Assumptions t26_s1_req_log_inv_one_inv.
Print Assumptions t26_s1_req_log_div.
Print Assumptions t26_s2_req_free_energy_align_ext.
Print Assumptions t26_s3_rkl_log_inv_one_inv.
Print Assumptions t26_s3_req_log_proj_pass.
Print Assumptions t26_s4_req2_log_inv_one_inv.
Print Assumptions t26_s5_r2_log_inv_opp.
Print Assumptions t26_s5_w_F_t_rel_decomp.
Print Assumptions t26_s6_r2u_FA_witness_ext.
Print Assumptions t26_s7_req_fep_F_ext.
Print Assumptions t26_s8_req_fep_F_ext_logz.
Print Assumptions t26_s9_w_gap_base.
Print Assumptions t26_s9_w_subgap_base.
