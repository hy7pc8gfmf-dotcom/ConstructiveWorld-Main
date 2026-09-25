(* ============================================================
   使命：本件数学使命叙述见下方原头注首段（既有件注记型头注整编候后波）。
   依赖：见原头注 Require 面与依赖段。
   对标：见原头注来源/对标行。
   构造性：纯构造性、零承认件（详见原头注红线自审段）。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)
(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   ga2_mopp_one（原 L70，8 句刀体）                                    *)
(* ============================================================ *)

(* ===================================================================== *)
(* req2_gibbs_inequality 组装件（norm 槽面 + eps 见证形出口）                 *)
(*                                                                       *)
(* 槽/供体坐标：                                                          *)
(*   · 槽：UpReqU2.v:359 req2_gibbs_inequality : forall p q (Hp pos3 p)    *)
(*     (Hq pos3 q), le zero (KLE p q Hp Hq)，KLE p q Hp Hq :=              *)
(*     @req2_rel_ent R RIS S sumf p q Hp Hq（δ 透明，同 UpReqAlign3:1460）  *)
(*     ——Id 同位 gibbs_inequality@CW219 L16629（拆分件 S04:2841）。         *)
(*   差 1（norm 位）：槽语句无归一化前提，而无 norm 的 KL≥0 数学为假         *)
(*     （反例 p = q/2：KL = Σ (q/2)·log(1/2) < 0）；S04 Id 供体证明实质       *)
(*     使用 normalized（零和步 Σ(p−q) = 1−1 = 0）。故任何真实例化消解必须           *)
(*     带 norm 供给位——本件以显式节参承担（T2① 假设位非公理）。              *)
(*   差 2（序无消去）：req 层接口切线引擎 log_le_linear_eps 为逐 eps 形，    *)
(*     plain-le 不可由接口逐 eps 字段导出（UpReqAlign3 裁定结论同因）——故        *)
(*     出口取项目教义 eps 见证形（plain 墙三绕之一，交接文档 §4.2-11）：      *)
(*     le zero (plus KL eps)。                                              *)
(* 数学路线（S04 骨架的 req2 面重演，非平凡真证）：                           *)
(*   逐点：对 x := q/p 施切线 log x ≤ x−1+eps ⟹ log p − log q ≥ 1 − q/p −   *)
(*   eps ⟹ p·(log p − log q) ≥ p − q − p·eps（inv_pos_correct 约分）；      *)
(*   求和：Σ ≥ Σp − Σq − eps·Σp = −eps（norm 零和 + sum 线性）⟹             *)
(*   KL + eps ≥ 0。                                                        *)
(* 实例化消解路线登记：下游使用链（UpReqU2/UpReqAlign3/4 各槽使用点）其结论面       *)
(*   本身携带 norm 前提者，可喂本件并同步升级结论至 eps 形；plain 形待        *)
(*   Real 层实例供给（UpReqAlign4「sup_gibbs 的 Real 供给属批 2」同路标）。   *)
(* 纪律：纯构造性；Set 层语句零 Prop 泄露（req/lt/le 均 Set 值）；纯项模式    *)
(*   （组合器逐段直引，零 Ltac 重写层）；假设位 = T2① 显式参非公理；          *)
(*   全链可提取。                                                          *)
(* ===================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqAlign2.
Import RealInterfaceEnhancedMod.

Section GibbsAssembly.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.

(* ---- 求和对接面（UpReqAlign2 Req2AlignCore 同位；本件使用 ext/add/linear    *)
(*   + le 单调槽 ga2_sum_le（UpReqPPOPlain rpl_sum_le 同形）。sum_pos 与       *)
(*   log_inv_exp_neg_req 零使用，诚实剪除（出节参面登记）。                    *)
(*   注意：UpReqAlign2 原节无 le 单调槽——本件增补位，喂定时由实例侧供给）。      *)
Variable sumf : (S -> R) -> R.
Hypothesis ga2_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis ga2_sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis ga2_sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis ga2_sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis ga2_log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).

(* ---- 节内组合器（隐式参版，避 elaborator 占位序坑） ---- *)
Definition ga2_rt {x y z : R} (H1 : req x y) (H2 : req y z) : req x z :=
  req_trans x y z H1 H2.
Definition ga2_le_id_l {a b c : R} (H1 : req a b) (H2 : le b c) : le a c :=
  le_id_l a b c H1 H2.
Definition ga2_le_id_r {a b c : R} (H1 : req b c) (H2 : le a b) : le a c :=
  le_id_r a b c H1 H2.

(* ---- 节内辅件 1：opp one 乘法归一（req_opp_mult_r + mult_one 两步） ---- *)
Lemma ga2_mopp_one : forall x : R, req (mult (opp one) x) (opp x).
Proof.
  intro x.
  assert (H1 : req (mult (opp one) x) (opp (mult one x))).
  { exact (req_opp_mult_r one x). }
  assert (H2 : req (mult one x) x).
  { exact (req_mult_one_l x). }
  assert (H3 : req (opp (mult one x)) (opp x)).
  { exact (req_opp_compat (mult one x) x H2). }
  exact (req_trans (mult (opp one) x) (opp (mult one x)) (opp x) H1 H3).
Qed.

(* ---- 节内辅件 2（点态核，S04 gibbs_pointwise 的 req2 面重演）：             *)
(*   p·(1 − q/p − eps) ≤ p·(log p − log q)，逐点 s。                          *)
Lemma ga2_ptw_le :
  forall (p q : S -> R) (eps : R) (s : S)
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
      by exact (ga2_log_req_compat (mult (p s) (inv_pos (p s) Hps)) one
                 (mult_positive (p s) (inv_pos (p s) Hps) Hps (inv_pos_pos (p s) Hps))
                 one_pos (inv_pos_correct (p s) Hps)).
    assert (Hc : req (log one one_pos) zero) by exact (log_one one_pos).
    assert (Hd : req (plus (log (p s) Hps)
                           (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))) zero)
      by exact (ga2_rt
                  (req_sym (log (mult (p s) (inv_pos (p s) Hps))
                              (mult_positive (p s) (inv_pos (p s) Hps) Hps
                                (inv_pos_pos (p s) Hps)))
                           (plus (log (p s) Hps)
                                 (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps)))
                           Ha)
                  (ga2_rt Hb Hc)).
    exact (req_plus_inv_unique (log (p s) Hps)
             (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps))
             (opp (log (p s) Hps)) Hd (plus_opp (log (p s) Hps))). }
  assert (Hstep3 : req (log (mult (q s) (inv_pos (p s) Hps))
                            (mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)))
                       (plus (log (q s) Hqs) (opp (log (p s) Hps))))
    by exact (ga2_rt Hlm
              (req_plus_compat (log (q s) Hqs) (log (q s) Hqs)
                (log (inv_pos (p s) Hps) (inv_pos_pos (p s) Hps)) (opp (log (p s) Hps))
                (req_refl (log (q s) Hqs)) Hlip)).
  assert (H4 : le (plus (log (q s) Hqs) (opp (log (p s) Hps)))
                  (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
    by exact (ga2_le_id_l
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
    exact (ga2_rt (ga2_rt r1 r2) r3). }
  assert (H7 : le (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                  (req_minus (log (p s) Hps) (log (q s) Hqs)))
    by exact (ga2_le_id_r H6 H5).
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
      by exact (ga2_rt
                (req_mult_compat (p s) (p s)
                  (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)
                  (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))
                  (req_refl (p s)) d1)
                (distrib (p s) (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps))).
    assert (c2 : req (mult (p s) (mult (q s) (inv_pos (p s) Hps))) (q s)).
    { exact (ga2_rt (mult_assoc (p s) (q s) (inv_pos (p s) Hps))
              (ga2_rt (req_mult_compat (mult (p s) (q s)) (mult (q s) (p s))
                         (inv_pos (p s) Hps) (inv_pos (p s) Hps)
                         (req_mult_comm_rewrite (p s) (q s))
                         (req_refl (inv_pos (p s) Hps)))
                (ga2_rt (req_sym (mult (q s) (mult (p s) (inv_pos (p s) Hps)))
                                 (mult (mult (q s) (p s)) (inv_pos (p s) Hps))
                                 (mult_assoc (q s) (p s) (inv_pos (p s) Hps)))
                  (ga2_rt (req_mult_compat (q s) (q s)
                             (mult (p s) (inv_pos (p s) Hps)) one
                             (req_refl (q s)) (inv_pos_correct (p s) Hps))
                    (mult_one (q s)))))). }
    assert (c3 : req (mult (p s) (plus (opp one) eps)) (plus (opp (p s)) (mult (p s) eps))).
    { assert (m1 : req (mult (p s) (opp one)) (opp (p s)))
        by exact (ga2_rt (req_opp_mult_l (p s) one)
                  (req_opp_compat (mult (p s) one) (p s) (mult_one (p s)))).
      exact (ga2_rt (distrib (p s) (opp one) eps)
              (req_plus_compat (mult (p s) (opp one)) (opp (p s))
                (mult (p s) eps) (mult (p s) eps) m1 (req_refl (mult (p s) eps)))). }
    assert (t2 : req (mult (p s) (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps))
                     (plus (q s) (plus (opp (p s)) (mult (p s) eps))))
      by exact (ga2_rt c1
                (ga2_rt
                  (req_plus_compat (mult (p s) (mult (q s) (inv_pos (p s) Hps))) (q s)
                    (mult (p s) (plus (opp one) eps)) (mult (p s) (plus (opp one) eps))
                    c2 (req_refl (mult (p s) (plus (opp one) eps))))
                  (req_plus_compat (q s) (q s)
                    (mult (p s) (plus (opp one) eps)) (plus (opp (p s)) (mult (p s) eps))
                    (req_refl (q s)) c3))).
    assert (c5 : req (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                     (opp (mult (p s) (plus (mult (q s) (inv_pos (p s) Hps)) (plus (opp one) eps)))))
      by exact (ga2_rt
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
      exact (ga2_rt v1
              (ga2_rt v3
                (ga2_rt v5
                  (ga2_rt v6 (ga2_rt v7 (ga2_rt v8 v9)))))). }
    exact (ga2_rt c5
              (ga2_rt (req_opp_compat
                        (mult (p s) (plus (mult (q s) (inv_pos (p s) Hps))
                                            (plus (opp one) eps)))
                        (plus (q s) (plus (opp (p s)) (mult (p s) eps)))
                        (ga2_rt (req_sym (mult (p s)
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
  exact (ga2_le_id_l
          (req_sym (mult (p s) (opp (plus (plus (mult (q s) (inv_pos (p s) Hps)) (opp one)) eps)))
                   (plus (p s) (opp (plus (q s) (mult (p s) eps)))) H9)
          H8).
Qed.

(* ---- 主件：req2_gibbs_inequality 组装（norm 槽面 + eps 见证形出口） ----
   出口结论 le zero (plus KL eps)：KL 项 = @req2_rel_ent R RIS S sumf p q Hp Hq
   （与 UpReqU2.v:359 槽语句的 KLE 项 δ 透明逐字同体）。 *)
Lemma ga2_gibbs_eps :
  forall (p q : S -> R)
         (Hp : @req2_pos_dist R RIS S p) (Hq : @req2_pos_dist R RIS S q)
         (Hnp : req (sumf p) one) (Hnq : req (sumf q) one) (eps : R),
    lt zero eps ->
    le zero (plus (@req2_rel_ent R RIS S sumf p q Hp Hq) eps).
Proof.
  intros p q Hp Hq Hnp Hnq eps Heps.
  assert (Hptw : forall s : S,
            le (plus (p s) (opp (plus (q s) (mult (p s) eps))))
               (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
    by (intro s; exact (ga2_ptw_le p q eps s (Hp s) (Hq s) Heps)).
  assert (Hsum : le (sumf (fun s => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                    (sumf (fun s => mult (p s)
                              (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))))
    by exact (ga2_sum_le _ _ Hptw).
  (* 求和代数：ΣG ≡ opp eps（norm 零和 + 线性 + opp one 缩放） *)
  assert (Tr : req (sumf (fun s => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                   (opp eps)).
  { assert (T1 : req (sumf (fun s => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                     (plus (sumf p)
                           (sumf (fun s => opp (plus (q s) (mult (p s) eps))))))
      by exact (ga2_sum_add p (fun s => opp (plus (q s) (mult (p s) eps)))).
    assert (T3e : req (sumf (fun s => opp (plus (q s) (mult (p s) eps))))
                      (plus (opp one) (opp eps))).
    { assert (T3a : req (sumf (fun s => opp (plus (q s) (mult (p s) eps))))
                        (sumf (fun s => plus (opp (q s)) (opp (mult (p s) eps)))))
        by exact (ga2_sum_ext (fun s => opp (plus (q s) (mult (p s) eps)))
                  (fun s => plus (opp (q s)) (opp (mult (p s) eps)))
                  (fun s => req_opp_plus (q s) (mult (p s) eps))).
      assert (T3b : req (sumf (fun s => plus (opp (q s)) (opp (mult (p s) eps))))
                        (plus (sumf (fun s => opp (q s)))
                              (sumf (fun s => opp (mult (p s) eps)))))
        by exact (ga2_sum_add (fun s => opp (q s)) (fun s => opp (mult (p s) eps))).
      assert (A : req (sumf (fun s => opp (q s))) (opp one)).
      { assert (A1 : req (sumf (fun s => opp (q s))) (sumf (fun s => mult (opp one) (q s))))
          by exact (ga2_sum_ext (fun s => opp (q s)) (fun s => mult (opp one) (q s))
                    (fun s => req_sym (mult (opp one) (q s)) (opp (q s))
                                (ga2_mopp_one (q s)))).
        assert (A2 : req (sumf (fun s => mult (opp one) (q s))) (mult (opp one) (sumf q)))
          by exact (ga2_sum_linear (opp one) q).
        assert (A3 : req (mult (opp one) (sumf q)) (mult (opp one) one))
          by exact (req_mult_compat (opp one) (opp one) (sumf q) one
                      (req_refl (opp one)) Hnq).
        assert (A4 : req (mult (opp one) one) (opp one)) by exact (mult_one (opp one)).
        exact (ga2_rt A1 (ga2_rt A2 (ga2_rt A3 A4))). }
      assert (B : req (sumf (fun s => opp (mult (p s) eps))) (opp eps)).
      { assert (B1 : req (sumf (fun s => opp (mult (p s) eps)))
                          (sumf (fun s => mult (opp one) (mult (p s) eps))))
          by exact (ga2_sum_ext (fun s => opp (mult (p s) eps))
                    (fun s => mult (opp one) (mult (p s) eps))
                    (fun s => req_sym (mult (opp one) (mult (p s) eps))
                                (opp (mult (p s) eps))
                                (ga2_mopp_one (mult (p s) eps)))).
        assert (B2 : req (sumf (fun s => mult (opp one) (mult (p s) eps)))
                          (mult (opp one) (sumf (fun s => mult (p s) eps))))
          by exact (ga2_sum_linear (opp one) (fun s => mult (p s) eps)).
        assert (B3 : req (sumf (fun s => mult (p s) eps)) eps).
        { assert (B3a : req (sumf (fun s => mult (p s) eps))
                            (sumf (fun s => mult eps (p s))))
            by exact (ga2_sum_ext (fun s => mult (p s) eps) (fun s => mult eps (p s))
                      (fun s => req_mult_comm_rewrite (p s) eps)).
          assert (B3b : req (sumf (fun s => mult eps (p s))) (mult eps (sumf p)))
            by exact (ga2_sum_linear eps p).
          assert (B3c : req (mult eps (sumf p)) (mult eps one))
            by exact (req_mult_compat eps eps (sumf p) one (req_refl eps) Hnp).
          assert (B3d : req (mult eps one) eps) by exact (mult_one eps).
          exact (ga2_rt B3a (ga2_rt B3b (ga2_rt B3c B3d))). }
        assert (B4 : req (mult (opp one) (sumf (fun s => mult (p s) eps)))
                          (mult (opp one) eps))
          by exact (req_mult_compat (opp one) (opp one)
                    (sumf (fun s => mult (p s) eps)) eps (req_refl (opp one)) B3).
        exact (ga2_rt B1
                (ga2_rt B2 (ga2_rt B4 (ga2_mopp_one eps)))). }
      exact (ga2_rt T3a (ga2_rt T3b
              (req_plus_compat (sumf (fun s => opp (q s))) (opp one)
                (sumf (fun s => opp (mult (p s) eps))) (opp eps) A B))). }
    assert (T4 : req (plus one (plus (opp one) (opp eps))) (opp eps)).
    { assert (e1 : req (plus one (plus (opp one) (opp eps)))
                       (plus (plus one (opp one)) (opp eps)))
        by exact (plus_assoc one (opp one) (opp eps)).
      assert (e2 : req (plus (plus one (opp one)) (opp eps)) (plus zero (opp eps)))
        by exact (req_plus_compat (plus one (opp one)) zero (opp eps) (opp eps)
                  (plus_opp one) (req_refl (opp eps))).
      exact (ga2_rt e1 (ga2_rt e2 (req_plus_zero_l (opp eps)))). }
    exact (ga2_rt T1
            (ga2_rt
              (req_plus_compat (sumf p) one
                (sumf (fun s => opp (plus (q s) (mult (p s) eps))))
                (plus (opp one) (opp eps)) Hnp T3e)
              T4)). }
  assert (HD : le (opp eps)
                  (sumf (fun s => mult (p s)
                            (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))))
    by exact (ga2_le_id_l
                (req_sym (sumf (fun s => plus (p s) (opp (plus (q s) (mult (p s) eps)))))
                         (opp eps) Tr)
                Hsum).
  apply (le_id_l zero (plus (opp eps) eps)
          (plus (sumf (fun s => mult (p s)
                        (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))) eps)).
  - exact (ga2_rt (req_sym (plus eps (opp eps)) zero (plus_opp eps))
                  (plus_comm eps (opp eps))).
  - exact (le_plus_compat (opp eps)
            (sumf (fun s => mult (p s)
                      (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
            eps eps HD (le_refl eps)).
Qed.

(* ---- 出口孪生：le (opp eps) KL 形（使用侧夹逼常用向；req 群归一） ---- *)
Corollary ga2_gibbs_eps_opps :
  forall (p q : S -> R)
         (Hp : @req2_pos_dist R RIS S p) (Hq : @req2_pos_dist R RIS S q)
         (Hnp : req (sumf p) one) (Hnq : req (sumf q) one) (eps : R),
    lt zero eps ->
    le (opp eps) (@req2_rel_ent R RIS S sumf p q Hp Hq).
Proof.
  intros p q Hp Hq Hnp Hnq eps Heps.
  assert (Step1 : le (plus zero (opp eps))
                     (plus (plus (@req2_rel_ent R RIS S sumf p q Hp Hq) eps)
                           (opp eps)))
    by exact (le_plus_compat zero
                             (plus (@req2_rel_ent R RIS S sumf p q Hp Hq) eps)
                             (opp eps) (opp eps)
                             (ga2_gibbs_eps p q Hp Hq Hnp Hnq eps Heps)
                             (le_refl (opp eps))).
  assert (Step3 : req (plus (plus (@req2_rel_ent R RIS S sumf p q Hp Hq) eps)
                            (opp eps))
                     (@req2_rel_ent R RIS S sumf p q Hp Hq)).
  { exact (ga2_rt
            (req_sym (plus (@req2_rel_ent R RIS S sumf p q Hp Hq)
                           (plus eps (opp eps)))
                     (plus (plus (@req2_rel_ent R RIS S sumf p q Hp Hq) eps)
                           (opp eps))
                     (plus_assoc (@req2_rel_ent R RIS S sumf p q Hp Hq) eps (opp eps)))
            (ga2_rt
              (req_plus_compat (@req2_rel_ent R RIS S sumf p q Hp Hq)
                (@req2_rel_ent R RIS S sumf p q Hp Hq) (plus eps (opp eps)) zero
                (req_refl (@req2_rel_ent R RIS S sumf p q Hp Hq)) (plus_opp eps))
              (plus_zero (@req2_rel_ent R RIS S sumf p q Hp Hq)))). }
  exact (le_id_l (opp eps) (plus zero (opp eps))
                 (@req2_rel_ent R RIS S sumf p q Hp Hq)
                 (req_sym (plus zero (opp eps)) (opp eps)
                          (req_plus_zero_l (opp eps)))
                 (le_id_r (plus zero (opp eps))
                          (plus (plus (@req2_rel_ent R RIS S sumf p q Hp Hq) eps)
                                (opp eps))
                          (@req2_rel_ent R RIS S sumf p q Hp Hq) Step3 Step1)).
Qed.

End GibbsAssembly.

Print Assumptions ga2_gibbs_eps.
Print Assumptions ga2_gibbs_eps_opps.
