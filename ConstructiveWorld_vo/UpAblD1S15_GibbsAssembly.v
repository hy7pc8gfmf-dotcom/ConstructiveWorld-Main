(* ============================================================ *)
(* UpAblD1S15_GibbsAssembly.v —— FA-D1S15 论文域消融施工席 双包件②    *)
(* 席位：FA-D1S15（D1-⑦ 后续·Align3 16 位＋GibbsAssembly 18 位      *)
(* ≤34 位双包）｜独立伴生件·原树零改·零 git·零注册面增量              *)
(*                                                              *)
(* 本件辖区：GibbsAssembly.v 装配底座（454 行）——S2 地基件之上        *)
(*   扩槽＋增量立件，合计 18 位＝A 接口 8＋B 导出链 7＋C 扩槽参 3：    *)
(*  A 组·普查接口槽 8 位直配（S2 底座骨架，扩槽不重立）：              *)
(*     L39(R,RIS)｜L40(S)｜L46(sumf)｜L47(ga2_sum_ext)｜            *)
(*     L49(ga2_sum_add)｜L52(ga2_sum_linear)｜L55(ga2_sum_le)｜      *)
(*     L57(ga2_log_req_compat＝S2 槽定理已立，本件打包面直配其定理，  *)
(*     零重立——槽主件仍为 uabd1s2_ga2_log_req_compat）。             *)
(*  B 组·节内导出链 7 位逐位立件（母本坐标→本件定理）：                *)
(*     L62(ga2_rt)→uabd1s15_ga2_rt｜L64(ga2_le_id_l)→…_le_id_l｜    *)
(*     L66(ga2_le_id_r)→…_le_id_r｜L70(ga2_mopp_one)→…_mopp_one｜   *)
(*     L80(ga2_ptw_le)→…_ptw_le（log 兼容槽＝LOGC 显式接口条件       *)
(*     供给——S8 坑卡⑧接口条件供给级条款）｜                          *)
(*     L301(ga2_gibbs_eps)→…_gibbs_eps｜L411(ga2_gibbs_eps_opps)→   *)
(*     …_gibbs_eps_opps（后两位典范 Real 载体实例化，sumf↦           *)
(*     sumd_sumf S0 en——S2 底座同源，四腿 UpReqSumD:112/135/161/203）。*)
(*  C 组·扩槽参 3 位（母本 L298-306 头注自述「norm 槽面＋eps 见证形   *)
(*     出口」；普查未单列的节参面——禁注水如实登记为显式参承接位，      *)
(*     非无条件供给）：Hnp(norm p)｜Hnq(norm q)｜Heps(lt zero eps)。  *)
(* 排除登记（扩槽不重立，零触碰）：L57 槽定理＝S2 已立（本件 A 组      *)
(*   直配引用）；L44 剪除账（log_inv_exp_neg_req 零消费）＝底座件     *)
(*   自持剪除，本件尊重不虚立（S2 同口径）。                          *)
(* 母本代际核验（AA4）：Live_X 副本与 ConstructiveWorld-Main 两副本    *)
(*   md5 同代 73d1d7e01e018aa7d6abc05d1c6c9c06（开工实测，收工复核）。 *)
(*                                                              *)
(* 形态：A 组＝S13 打包记录型（槽语句逐字入包）；B 组＝母本证明体       *)
(*   逐字搬运＋槽换腿机械移植（零新数学，诚实标 T·导出链级）；C 组＝   *)
(*   显式参承接（S13 GIBBS 参数先例同族）。零 W 墙新登记。             *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219／UpReqAlgebra／ *)
(*   UpReqAlign2／G05_LogSmall／UpReqSumD／UpAblD1S2_reqlog_Gibbs-    *)
(*   Assembly（S2 地基件——本件扩槽不重立的骨架来源）。零 Require 槽位  *)
(*   母本 GibbsAssembly.v 本体（防 P3S1 坑1 混代际 .vo 地雷）。         *)
(* 纪律：零 git、零注册面增量、attn 论文域源档/论文目录零触碰；        *)
(*   fail-loud。                                                    *)
(* 四关留痕：Live_X/attn/logs/g{0..4}-UpAblD1S15_*.{log,exit}        *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqAlign2.
Require Import G05_LogSmall.
Require Import UpReqSumD.
Require Import UpAblD1S2_reqlog_GibbsAssembly.
Import RealInterfaceEnhancedMod.

Definition uabd1s15_ren : RealInterfaceEnhancedSetoid Real :=
  RealInterfaceEnhancedMod.RealEnhancedReal.

(* ================================================================
   A 组·普查接口槽 8 位：打包记录型（对照母本 L39-57 槽语句逐字入包）
   ================================================================ *)

Inductive uabd1s15_ga2_pack8 : Type :=
| uabd1s15_ga2_pack8_intro :
    forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R),
      forall (S : Set) (sumf : (S -> R) -> R),
        forall (ga2_sum_ext : forall f g : S -> R,
                   (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)),
          forall (ga2_sum_add : forall f g : S -> R,
                     req (sumf (fun s : S => plus (f s) (g s)))
                         (plus (sumf f) (sumf g))),
            forall (ga2_sum_linear : forall (a : R) (f : S -> R),
                       req (sumf (fun s : S => mult a (f s)))
                           (mult a (sumf f))),
              forall (ga2_sum_le : forall f g : S -> R,
                         (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g)),
                forall (ga2_log_req_compat : forall (x y : R) (Hx : lt zero x)
                                                      (Hy : lt zero y),
                                          req x y -> req (log x Hx) (log y Hy)),
                  uabd1s15_ga2_pack8.

(* 供给件：S2 底座骨架实例（sumd_sumf 有限和，典范 Real 载体）——
   求和四腿＝UpReqSumD 直喂（与 S2 底座包同源同腿），log 腿＝S2 槽定理
   直配（扩槽不重立）。 *)
Theorem uabd1s15_ga2_pack8_supplied : uabd1s15_ga2_pack8.
Proof.
  exact (uabd1s15_ga2_pack8_intro
           Real uabd1s15_ren
           unit (sumd_sumf unit (tt :: nil))
           (sumd_sum_ext unit (tt :: nil))
           (sumd_sum_add unit (tt :: nil))
           (sumd_sum_linear unit (tt :: nil))
           (sumd_sum_le unit (tt :: nil))
           uabd1s2_ga2_log_req_compat).
Qed.

(* ================================================================
   B 组·导出链前 4 位：R 泛型导出（母本 L62-76 逐字搬运）
   ================================================================ *)

Section UpAblD1S15GAAlg.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* ---- L62-63：req 传递组合器 ---- *)
Definition uabd1s15_ga2_rt {x y z : R} (H1 : req x y) (H2 : req y z) : req x z :=
  req_trans x y z H1 H2.

(* ---- L64-65 / L66-67：le 承接组合器对 ---- *)
Definition uabd1s15_ga2_le_id_l {a b c : R} (H1 : req a b) (H2 : le b c) : le a c :=
  le_id_l a b c H1 H2.
Definition uabd1s15_ga2_le_id_r {a b c : R} (H1 : req b c) (H2 : le a b) : le a c :=
  le_id_r a b c H1 H2.

(* ---- L70-76：opp one 乘法归一（req_opp_mult_r + mult_one 两步） ---- *)
Lemma uabd1s15_ga2_mopp_one : forall x : R, req (mult (opp one) x) (opp x).
Proof.
  intro x.
  exact (req_trans (mult (opp one) x) (opp (mult one x)) (opp x)
                   (req_opp_mult_r one x)
                   (req_opp_compat (mult one x) x (req_mult_one_l x))).
Qed.

End UpAblD1S15GAAlg.

(* ================================================================
   B 组·导出链第 5 位：点态切线核（母本 L80-296 逐字搬运；
   log 兼容槽＝LOGC 显式接口条件供给——S8 坑卡⑧条款，
   母本该位即节槽 ga2_log_req_compat 的消费点 L108）
   ================================================================ *)

Section UpAblD1S15GAPtw.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable LOGC : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Variable S0 : Set.

Lemma uabd1s15_ga2_ptw_le :
  forall (p q : S0 -> R) (eps : R) (s : S0)
         (Hps : lt zero (p s)) (Hqs : lt zero (q s)),
    lt zero eps ->
    le (plus (p s) (opp (plus (q s) (mult (p s) eps))))
       (mult (p s) (req_minus (log (p s) Hps) (log (q s) Hqs))).
Proof.
  intros p q eps s Hps Hqs Heps.
  assert (Htan : le (log (mult (q s) (inv_pos (p s) Hps))
                          (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)))
                    (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
    by exact (log_le_linear_eps (mult (q s) (inv_pos (p s) Hps))
                 (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps))
                 eps Heps).
  assert (Hlm : req (log (mult (q s) (inv_pos (p s) Hps))
                         (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)))
                    (plus (log (q s) Hqs) (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))))
    by exact (log_mult (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)).
  (* log(1/p) ≡ −log p（inv_pos_correct 归一 + log 论证换底 + 取消件） *)
  assert (Hlip : req (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))
                     (opp (log (p s) Hps))).
  { assert (Ha : req (log (mult (p s) (inv_pos (p s) Hps))
                          (mult_positive (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps)))
                     (plus (log (p s) Hps) (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))))
      by exact (log_mult (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps)).
    assert (Hb : req (log (mult (p s) (inv_pos (p s) Hps))
                          (mult_positive (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps)))
                     (log one one_pos))
      by exact (LOGC (mult (p s) (inv_pos (p s) Hps)) one
                 (mult_positive (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps))
                 one_pos (inv_pos_correct (p s) Hps)).
    assert (Hc : req (log one one_pos) zero) by exact (log_one one_pos).
    assert (Hd : req (plus (log (p s) Hps)
                           (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))) zero)
      by exact (uabd1s15_ga2_rt
                  (req_sym (log (mult (p s) (inv_pos (p s) Hps))
                              (mult_positive (p s) (inv_pos (p s) Hps) Hps
                                (inv_pos_pos (p s) Hps)))
                           (plus (log (p s) Hps)
                                 (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps)))
                           Ha)
                  (uabd1s15_ga2_rt Hb Hc)).
    exact (req_plus_inv_unique (log (p s) Hps)
             (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))
             (opp (log (p s) Hps)) Hd (plus_opp (log (p s) Hps))). }
  assert (Hstep3 : req (log (mult (q s) (inv_pos (p s) Hps))
                            (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)))
                       (plus (log (q s) Hqs) (opp (log (p s) Hps))))
    by exact (uabd1s15_ga2_rt Hlm
              (req_plus_compat (log (q s) Hqs) (log (q s) Hqs)
                (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps)) (opp (log (p s) Hps))
                (req_refl (log (q s) Hqs)) Hlip)).
  assert (H4 : le (plus (log (q s) Hqs) (opp (log (p s) Hps)))
                  (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
    by exact (uabd1s15_ga2_le_id_l
                (req_sym (log (mult (q s) (inv_pos (p s) Hps))
                            (mult_positive (q s) (inv_pos (p s) Hps) Hqs
                              (inv_pos_pos (p s) Hps)))
                         (plus (log (q s) Hqs) (opp (log (p s) Hps)))
                         Hstep3)
                Htan).
  assert (H5 : le (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                  (opp (plus (log (q s) Hqs) (opp (log (p s) Hps)))))
    by exact (opp_le_compat (plus (log (q s) Hqs) (opp (log (p s) Hps)))
                            (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                            H4).
  (* 右腿形归一：opp (plus (log q) (opp (log p))) ≡ req_minus (log p) (log q) *)
  assert (H6 : req (opp (plus (log (q s) Hqs) (opp (log (p s) Hps))))
                   (req_minus (log (p s) Hps) (log (q s) Hqs))).
  { assert (r1 : req (opp (plus (log (q s) Hqs) (opp (log (p s) Hps))))
                     (plus (opp (log (q s) Hqs)) (opp (opp (log (p s) Hps)))))
      by exact (req_opp_plus (log (q s) Hqs) (opp (log (p s) Hps))).
    assert (r2 : req (plus (opp (log (q s) Hqs)) (opp (opp (log (p s) Hps))))
                     (plus (opp (log (q s) Hqs)) (log (p s) Hps)))
      by exact (req_plus_compat (opp (log (q s) Hqs)) (opp (log (q s) Hqs))
                (opp (opp (log (p s) Hps))) (log (p s) Hps)
                (req_refl (opp (log (q s) Hqs))) (req_double_neg (log (p s) Hps))).
    assert (r3 : req (plus (opp (log (q s) Hqs)) (log (p s) Hps))
                     (plus (log (p s) Hps) (opp (log (q s) Hqs))))
      by exact (plus_comm (opp (log (q s) Hqs)) (log (p s) Hps)).
    exact (uabd1s15_ga2_rt (uabd1s15_ga2_rt r1 r2) r3). }
  assert (H7 : le (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                  (req_minus (log (p s) Hps) (log (q s) Hqs)))
    by exact (uabd1s15_ga2_le_id_r H6 H5).
  assert (Hle0 : le zero (p s)) by exact (lt_le_iff zero (p s) (inl Hps)).
  assert (H8 : le (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                  (mult (p s) (req_minus (log (p s) Hps) (log (q s) Hqs))))
    by exact (req_le_mult_compat_r (p s) _ _ Hle0 H7).
  (* 左腿值归一：p·opp(1 − q/p + eps) ≡ plus p (opp (plus q (p·eps)))
     （inv_pos_correct 约分 q/p·p = q + distrib/opp 分配律，req 代数链） *)
  assert (H9 : req (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                   (plus (p s) (opp (plus (q s) (mult (p s) eps))))).
  { assert (d1 : req (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                     (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps)))
      by exact (req_sym (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))
                        (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                        (plus_assoc (mult (q s) (inv_pos (p s) Hps)) (opp one) eps)).
    assert (c1 : req (mult (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                     (plus (mult (p s) (mult (q s) (inv_pos (p s) Hps)))
                           (mult (p s) (plus (opp one) eps))))
      by exact (uabd1s15_ga2_rt
                (req_mult_compat (p s) (p s)
                  (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                  (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))
                  (req_refl (p s)) d1)
                (distrib (p s) (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))).
    assert (c2 : req (mult (p s) (mult (q s) (inv_pos (p s) Hps))) (q s)).
    { exact (uabd1s15_ga2_rt (mult_assoc (p s) (q s) (inv_pos (p s) Hps))
              (uabd1s15_ga2_rt (req_mult_compat (mult (p s) (q s)) (mult (q s) (p s))
                         (inv_pos (p s) Hps) (inv_pos (p s) Hps)
                         (req_mult_comm_rewrite (p s) (q s))
                         (req_refl (inv_pos (p s) Hps)))
                (uabd1s15_ga2_rt (req_sym (mult (q s) (mult (p s) (inv_pos (p s) Hps)))
                                 (mult (mult (q s) (p s)) (inv_pos (p s) Hps))
                                 (mult_assoc (q s) (p s) (inv_pos (p s) Hps)))
                  (uabd1s15_ga2_rt (req_mult_compat (q s) (q s)
                             (mult (p s) (inv_pos (p s) Hps)) one
                             (req_refl (q s)) (inv_pos_correct (p s) Hps))
                    (mult_one (q s)))))). }
    assert (c3 : req (mult (p s) (plus (opp one) eps)) (plus (opp (p s)) (mult (p s) eps))).
    { assert (m1 : req (mult (p s) (opp one)) (opp (p s)))
        by exact (uabd1s15_ga2_rt (req_opp_mult_l (p s) one)
                  (req_opp_compat (mult (p s) one) (p s) (mult_one (p s)))).
      exact (uabd1s15_ga2_rt (distrib (p s) (opp one) eps)
              (req_plus_compat (mult (p s) (opp one)) (opp (p s))
                (mult (p s) eps) (mult (p s) eps) m1 (req_refl (mult (p s) eps)))). }
    assert (t2 : req (mult (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                     (plus (q s) (plus (opp (p s)) (mult (p s) eps))))
      by exact (uabd1s15_ga2_rt c1
                (uabd1s15_ga2_rt
                  (req_plus_compat (mult (p s) (mult (q s) (inv_pos (p s) Hps))) (q s)
                    (mult (p s) (plus (opp one) eps)) (mult (p s) (plus (opp one) eps))
                    c2 (req_refl (mult (p s) (plus (opp one) eps))))
                  (req_plus_compat (q s) (q s)
                    (mult (p s) (plus (opp one) eps)) (plus (opp (p s)) (mult (p s) eps))
                    (req_refl (q s)) c3))).
    assert (c5 : req (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                     (opp (mult (p s) (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps)))))
      by exact (uabd1s15_ga2_rt
                (req_opp_mult_l (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                (req_opp_compat (mult (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                  (mult (p s) (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps)))
                  (req_mult_compat (p s) (p s)
                    (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                    (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))
                    (req_refl (p s)) d1))).
    assert (c6 : req (opp (plus (q s) (plus (opp (p s)) (mult (p s) eps))))
                     (plus (p s) (opp (plus (q s) (mult (p s) eps))))).
    { assert (v1 : req (opp (plus (q s) (plus (opp (p s)) (mult (p s) eps))))
                       (plus (opp (q s)) (opp (plus (opp (p s)) (mult (p s) eps)))))
        by exact (req_opp_plus (q s) (plus (opp (p s)) (mult (p s) eps))).
      assert (v2 : req (opp (plus (opp (p s)) (mult (p s) eps)))
                       (plus (opp (opp (p s))) (opp (mult (p s) eps))))
        by exact (req_opp_plus (opp (p s)) (mult (p s) eps)).
      assert (v3 : req (plus (opp (q s)) (opp (plus (opp (p s)) (mult (p s) eps))))
                       (plus (opp (q s)) (plus (opp (opp (p s))) (opp (mult (p s) eps)))))
        by exact (req_plus_compat (opp (q s)) (opp (q s))
                  (opp (plus (opp (p s)) (mult (p s) eps)))
                  (plus (opp (opp (p s))) (opp (mult (p s) eps)))
                  (req_refl (opp (q s))) v2).
      assert (v4 : req (plus (opp (q s)) (opp (opp (p s)))) (plus (opp (q s)) (p s)))
        by exact (req_plus_compat (opp (q s)) (opp (q s)) (opp (opp (p s))) (p s)
                  (req_refl (opp (q s))) (req_double_neg (p s))).
      assert (v5 : req (plus (opp (q s)) (plus (opp (opp (p s))) (opp (mult (p s) eps))))
                       (plus (plus (opp (q s)) (opp (opp (p s)))) (opp (mult (p s) eps))))
        by exact (plus_assoc (opp (q s)) (opp (opp (p s))) (opp (mult (p s) eps))).
      assert (v6 : req (plus (plus (opp (q s)) (opp (opp (p s)))) (opp (mult (p s) eps)))
                       (plus (plus (opp (q s)) (p s)) (opp (mult (p s) eps))))
        by exact (req_plus_compat (plus (opp (q s)) (opp (opp (p s)))) (plus (opp (q s)) (p s))
                  (opp (mult (p s) eps)) (opp (mult (p s) eps)) v4 (req_refl (opp (mult (p s) eps)))).
      assert (v7 : req (plus (plus (opp (q s)) (p s)) (opp (mult (p s) eps)))
                       (plus (plus (p s) (opp (q s))) (opp (mult (p s) eps))))
        by exact (req_plus_compat (plus (opp (q s)) (p s)) (plus (p s) (opp (q s)))
                  (opp (mult (p s) eps)) (opp (mult (p s) eps))
                  (plus_comm (opp (q s)) (p s)) (req_refl (opp (mult (p s) eps)))).
      assert (v8 : req (plus (plus (p s) (opp (q s))) (opp (mult (p s) eps)))
                       (plus (p s) (plus (opp (q s)) (opp (mult (p s) eps)))))
        by exact (req_sym (plus (p s) (plus (opp (q s)) (opp (mult (p s) eps))))
                          (plus (plus (p s) (opp (q s))) (opp (mult (p s) eps)))
                          (plus_assoc (p s) (opp (q s)) (opp (mult (p s) eps)))).
      assert (v9 : req (plus (p s) (plus (opp (q s)) (opp (mult (p s) eps))))
                       (plus (p s) (opp (plus (q s) (mult (p s) eps)))))
        by exact (req_plus_compat (p s) (p s)
                  (plus (opp (q s)) (opp (mult (p s) eps)))
                  (opp (plus (q s) (mult (p s) eps)))
                  (req_refl (p s))
                  (req_sym (opp (plus (q s) (mult (p s) eps)))
                           (plus (opp (q s)) (opp (mult (p s) eps)))
                           (req_opp_plus (q s) (mult (p s) eps)))).
      exact (uabd1s15_ga2_rt v1
              (uabd1s15_ga2_rt v3
                (uabd1s15_ga2_rt v5
                  (uabd1s15_ga2_rt v6 (uabd1s15_ga2_rt v7 (uabd1s15_ga2_rt v8 v9)))))). }
    exact (uabd1s15_ga2_rt c5
              (uabd1s15_ga2_rt (req_opp_compat
                        (mult (p s) (plus (mult (q s) (inv_pos (p s) Hps))
                                            (plus (opp one) eps)))
                        (plus (q s) (plus (opp (p s)) (mult (p s) eps)))
                        (uabd1s15_ga2_rt (req_sym (mult (p s)
                                           (plus (plus (mult (q s) (inv_pos (p s) Hps))
                                                   (opp one)) eps))
                                         (mult (p s)
                                           (plus (mult (q s) (inv_pos (p s) Hps))
                                                   (plus (opp one) eps)))
                                         (req_mult_compat (p s) (p s)
                                           (plus (plus (mult (q s) (inv_pos (p s) Hps))
                                                   (opp one)) eps)
                                           (plus (mult (q s) (inv_pos (p s) Hps))
                                                   (plus (opp one) eps))
                                           (req_refl (p s)) d1))
                                  t2))
                c6)). }
  exact (uabd1s15_ga2_le_id_l
          (req_sym (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                   (plus (p s) (opp (plus (q s) (mult (p s) eps)))) H9)
          H8).
Qed.

End UpAblD1S15GAPtw.

(* ================================================================
   B 组·导出链第 6-7 位＋C 组·扩槽参 3 位：主件与出口孪生
   （母本 L301-449 典范 Real 载体实例化；sumf ↦ sumd_sumf S0 en
   ——S2 底座同源；Hnp/Hnq/Heps＝显式参承接位，诚实保留）
   ================================================================ *)

Theorem uabd1s15_ga2_gibbs_eps :
  forall (S0 : Set) (en : list S0)
         (p q : S0 -> Real)
         (Hp : @req2_pos_dist Real uabd1s15_ren S0 p)
         (Hq : @req2_pos_dist Real uabd1s15_ren S0 q)
         (Hnp : req (sumd_sumf S0 en p) one)
         (Hnq : req (sumd_sumf S0 en q) one)
         (eps : Real),
    lt zero eps ->
    le zero (plus (@req2_rel_ent Real uabd1s15_ren S0 (sumd_sumf S0 en) p q Hp Hq) eps).
Proof.
  intros S0 en p q Hp Hq Hnp Hnq eps Heps.
  assert (Hptw : forall s : S0,
            le (plus (p s) (opp (plus (q s) (mult (p s) eps))))
               (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
    by (intro s;
        exact (uabd1s15_ga2_ptw_le uabd1s2_ga2_log_req_compat S0 p q eps s
                 (Hp s) (Hq s) Heps)).
  assert (Hsum : le (sumd_sumf S0 en (fun s : S0 => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                    (sumd_sumf S0 en (fun s : S0 => mult (p s)
                              (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))))
    by exact (sumd_sum_le S0 en _ _ Hptw).
  (* 求和代数：ΣG ≡ opp eps（norm 零和 + 线性 + opp one 缩放） *)
  assert (Tr : req (sumd_sumf S0 en (fun s : S0 => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                   (opp eps)).
  { assert (T1 : req (sumd_sumf S0 en (fun s : S0 => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                     (plus (sumd_sumf S0 en p)
                           (sumd_sumf S0 en (fun s : S0 => opp (plus (q s) (mult (p s) eps))))))
      by exact (sumd_sum_add S0 en p (fun s : S0 => opp (plus (q s) (mult (p s) eps)))).
    assert (T3e : req (sumd_sumf S0 en (fun s : S0 => opp (plus (q s) (mult (p s) eps))))
                      (plus (opp one) (opp eps))).
    { assert (T3a : req (sumd_sumf S0 en (fun s : S0 => opp (plus (q s) (mult (p s) eps))))
                        (sumd_sumf S0 en (fun s : S0 => plus (opp (q s)) (opp (mult (p s) eps)))))
        by exact (sumd_sum_ext S0 en (fun s : S0 => opp (plus (q s) (mult (p s) eps)))
                  (fun s : S0 => plus (opp (q s)) (opp (mult (p s) eps)))
                  (fun s : S0 => req_opp_plus (q s) (mult (p s) eps))).
      assert (T3b : req (sumd_sumf S0 en (fun s : S0 => plus (opp (q s)) (opp (mult (p s) eps))))
                        (plus (sumd_sumf S0 en (fun s : S0 => opp (q s)))
                              (sumd_sumf S0 en (fun s : S0 => opp (mult (p s) eps)))))
        by exact (sumd_sum_add S0 en (fun s : S0 => opp (q s))
                    (fun s : S0 => opp (mult (p s) eps))).
      assert (A : req (sumd_sumf S0 en (fun s : S0 => opp (q s))) (opp one)).
      { assert (A1 : req (sumd_sumf S0 en (fun s : S0 => opp (q s)))
                          (sumd_sumf S0 en (fun s : S0 => mult (opp one) (q s))))
          by exact (sumd_sum_ext S0 en (fun s : S0 => opp (q s))
                    (fun s : S0 => mult (opp one) (q s))
                    (fun s : S0 => req_sym (mult (opp one) (q s)) (opp (q s))
                                (uabd1s15_ga2_mopp_one (q s)))).
        assert (A2 : req (sumd_sumf S0 en (fun s : S0 => mult (opp one) (q s)))
                          (mult (opp one) (sumd_sumf S0 en q)))
          by exact (sumd_sum_linear S0 en (opp one) q).
        assert (A3 : req (mult (opp one) (sumd_sumf S0 en q)) (mult (opp one) one))
          by exact (req_mult_compat (opp one) (opp one) (sumd_sumf S0 en q) one
                      (req_refl (opp one)) Hnq).
        assert (A4 : req (mult (opp one) one) (opp one)) by exact (mult_one (opp one)).
        exact (uabd1s15_ga2_rt A1 (uabd1s15_ga2_rt A2 (uabd1s15_ga2_rt A3 A4))). }
      assert (B : req (sumd_sumf S0 en (fun s : S0 => opp (mult (p s) eps))) (opp eps)).
      { assert (B1 : req (sumd_sumf S0 en (fun s : S0 => opp (mult (p s) eps)))
                          (sumd_sumf S0 en (fun s : S0 => mult (opp one) (mult (p s) eps))))
          by exact (sumd_sum_ext S0 en (fun s : S0 => opp (mult (p s) eps))
                    (fun s : S0 => mult (opp one) (mult (p s) eps))
                    (fun s : S0 => req_sym (mult (opp one) (mult (p s) eps))
                                (opp (mult (p s) eps))
                                (uabd1s15_ga2_mopp_one (mult (p s) eps)))).
        assert (B2 : req (sumd_sumf S0 en (fun s : S0 => mult (opp one) (mult (p s) eps)))
                          (mult (opp one) (sumd_sumf S0 en (fun s : S0 => mult (p s) eps))))
          by exact (sumd_sum_linear S0 en (opp one) (fun s : S0 => mult (p s) eps)).
        assert (B3 : req (sumd_sumf S0 en (fun s : S0 => mult (p s) eps)) eps).
        { assert (B3a : req (sumd_sumf S0 en (fun s : S0 => mult (p s) eps))
                            (sumd_sumf S0 en (fun s : S0 => mult eps (p s))))
            by exact (sumd_sum_ext S0 en (fun s : S0 => mult (p s) eps)
                      (fun s : S0 => mult eps (p s))
                      (fun s : S0 => req_mult_comm_rewrite (p s) eps)).
          assert (B3b : req (sumd_sumf S0 en (fun s : S0 => mult eps (p s)))
                            (mult eps (sumd_sumf S0 en p)))
            by exact (sumd_sum_linear S0 en eps p).
          assert (B3c : req (mult eps (sumd_sumf S0 en p)) (mult eps one))
            by exact (req_mult_compat eps eps (sumd_sumf S0 en p) one (req_refl eps) Hnp).
          assert (B3d : req (mult eps one) eps) by exact (mult_one eps).
          exact (uabd1s15_ga2_rt B3a (uabd1s15_ga2_rt B3b (uabd1s15_ga2_rt B3c B3d))). }
        assert (B4 : req (mult (opp one) (sumd_sumf S0 en (fun s : S0 => mult (p s) eps)))
                          (mult (opp one) eps))
          by exact (req_mult_compat (opp one) (opp one)
                    (sumd_sumf S0 en (fun s : S0 => mult (p s) eps)) eps
                    (req_refl (opp one)) B3).
        exact (uabd1s15_ga2_rt B1
                (uabd1s15_ga2_rt B2 (uabd1s15_ga2_rt B4 (uabd1s15_ga2_mopp_one eps)))). }
      exact (uabd1s15_ga2_rt T3a (uabd1s15_ga2_rt T3b
              (req_plus_compat (sumd_sumf S0 en (fun s : S0 => opp (q s))) (opp one)
                (sumd_sumf S0 en (fun s : S0 => opp (mult (p s) eps))) (opp eps) A B))). }
    assert (T4 : req (plus one (plus (opp one) (opp eps))) (opp eps)).
    { assert (e1 : req (plus one (plus (opp one) (opp eps)))
                       (plus (plus one (opp one)) (opp eps)))
        by exact (plus_assoc one (opp one) (opp eps)).
      assert (e2 : req (plus (plus one (opp one)) (opp eps)) (plus zero (opp eps)))
        by exact (req_plus_compat (plus one (opp one)) zero (opp eps) (opp eps)
                  (plus_opp one) (req_refl (opp eps))).
      exact (uabd1s15_ga2_rt e1 (uabd1s15_ga2_rt e2 (req_plus_zero_l (opp eps)))). }
    exact (uabd1s15_ga2_rt T1
            (uabd1s15_ga2_rt
              (req_plus_compat (sumd_sumf S0 en p) one
                (sumd_sumf S0 en (fun s : S0 => opp (plus (q s) (mult (p s) eps))))
                (plus (opp one) (opp eps)) Hnp T3e)
              T4)). }
  assert (HD : le (opp eps)
                  (sumd_sumf S0 en (fun s : S0 => mult (p s)
                            (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))))
    by exact (uabd1s15_ga2_le_id_l
                (req_sym (sumd_sumf S0 en (fun s : S0 => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                         (opp eps) Tr)
                Hsum).
  apply (le_id_l zero (plus (opp eps) eps)
          (plus (sumd_sumf S0 en (fun s : S0 => mult (p s)
                        (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))) eps)).
  - exact (uabd1s15_ga2_rt (req_sym (plus eps (opp eps)) zero (plus_opp eps))
                  (plus_comm eps (opp eps))).
  - exact (le_plus_compat (opp eps)
            (sumd_sumf S0 en (fun s : S0 => mult (p s)
                      (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
            eps eps HD (le_refl eps)).
Qed.

(* ---- 出口孪生：le (opp eps) KL 形（消费侧夹逼常用向；req 群归一） ---- *)
Corollary uabd1s15_ga2_gibbs_eps_opps :
  forall (S0 : Set) (en : list S0)
         (p q : S0 -> Real)
         (Hp : @req2_pos_dist Real uabd1s15_ren S0 p)
         (Hq : @req2_pos_dist Real uabd1s15_ren S0 q)
         (Hnp : req (sumd_sumf S0 en p) one)
         (Hnq : req (sumd_sumf S0 en q) one)
         (eps : Real),
    lt zero eps ->
    le (opp eps) (@req2_rel_ent Real uabd1s15_ren S0 (sumd_sumf S0 en) p q Hp Hq).
Proof.
  intros S0 en p q Hp Hq Hnp Hnq eps Heps.
  assert (Step1 : le (plus zero (opp eps))
                     (plus (plus (@req2_rel_ent Real uabd1s15_ren S0 (sumd_sumf S0 en) p q Hp Hq) eps)
                           (opp eps)))
    by exact (le_plus_compat zero
                             (plus (@req2_rel_ent Real uabd1s15_ren S0 (sumd_sumf S0 en) p q Hp Hq) eps)
                             (opp eps) (opp eps)
                             (uabd1s15_ga2_gibbs_eps S0 en p q Hp Hq Hnp Hnq eps Heps)
                             (le_refl (opp eps))).
  assert (Step3 : req (plus (plus (@req2_rel_ent Real uabd1s15_ren S0 (sumd_sumf S0 en) p q Hp Hq) eps)
                            (opp eps))
                     (@req2_rel_ent Real uabd1s15_ren S0 (sumd_sumf S0 en) p q Hp Hq)).
  { exact (uabd1s15_ga2_rt
            (req_sym (plus (@req2_rel_ent Real uabd1s15_ren S0 (sumd_sumf S0 en) p q Hp Hq)
                           (plus eps (opp eps)))
                     (plus (plus (@req2_rel_ent Real uabd1s15_ren S0 (sumd_sumf S0 en) p q Hp Hq) eps)
                           (opp eps))
                     (plus_assoc (@req2_rel_ent Real uabd1s15_ren S0 (sumd_sumf S0 en) p q Hp Hq)
                                 eps (opp eps)))
            (uabd1s15_ga2_rt
              (req_plus_compat (@req2_rel_ent Real uabd1s15_ren S0 (sumd_sumf S0 en) p q Hp Hq)
                (@req2_rel_ent Real uabd1s15_ren S0 (sumd_sumf S0 en) p q Hp Hq)
                (plus eps (opp eps)) zero
                (req_refl (@req2_rel_ent Real uabd1s15_ren S0 (sumd_sumf S0 en) p q Hp Hq))
                (plus_opp eps))
              (plus_zero (@req2_rel_ent Real uabd1s15_ren S0 (sumd_sumf S0 en) p q Hp Hq)))). }
  exact (le_id_l (opp eps) (plus zero (opp eps))
                 (@req2_rel_ent Real uabd1s15_ren S0 (sumd_sumf S0 en) p q Hp Hq)
                 (req_sym (plus zero (opp eps)) (opp eps)
                          (req_plus_zero_l (opp eps)))
                 (le_id_r (plus zero (opp eps))
                          (plus (plus (@req2_rel_ent Real uabd1s15_ren S0 (sumd_sumf S0 en) p q Hp Hq) eps)
                                (opp eps))
                          (@req2_rel_ent Real uabd1s15_ren S0 (sumd_sumf S0 en) p q Hp Hq)
                          Step3 Step1)).
Qed.

(* ============ 假设面收口申报 ============ *)

Print Assumptions uabd1s15_ga2_pack8_supplied.
Print Assumptions uabd1s15_ga2_ptw_le.
Print Assumptions uabd1s15_ga2_gibbs_eps.
Print Assumptions uabd1s15_ga2_gibbs_eps_opps.
