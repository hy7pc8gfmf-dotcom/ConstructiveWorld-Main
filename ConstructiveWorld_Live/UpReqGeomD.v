(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   geod_policy_iter_kl_geom_step_eps（原 L460，3 句玩具证）             *)
(*   geod_step_kl_eta_bound_eps（原 L431，3 句玩具证）                    *)
(*   geod_kappa_pos（原 L393，2 句玩具证）                                *)
(*   geod_lsum_linear（原 L247，3 句玩具证）                              *)
(*   geod_lsum_add（原 L239，3 句玩具证）                                 *)
(*   geod_lsum_le（原 L231，3 句玩具证）                                  *)
(*   geod_amgm_pointwise_iface（原 L210，1 句玩具证）                     *)
(*   geod_amgm_pointwise_eps（原 L178，2 句玩具证）                       *)
(*   geod_le_to_le_b（原 L84，2 句玩具证）                                *)
(* ============================================================ *)
(* ============================================================ *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 为恒等守恒——清单所列 9 参数位证明体与 Main 现版原件逐字同文（刀体                                *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqGeomD.v *)
(* *)
(* 目的： step_kl_eta_bound 参数位的单步几何不等式消解。 *)
(* 主件： geod_amgm_pointwise_eps / geod_lsum_le 几何-算术平均与求和界族。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： 普查核对经实读裁决，错位三处如实登记于正文；sum_le 接口为显式前提。 *)
(* ============================================================ *)

(* ============================================================ *)
(*   主定理：UpReqAlign.req_policy_iter_kl_geom_step（评审 4.2 点名件） *)
(*   假设位：req_step_kl_eta_bound（T2① 单步几何不等式假设位）        *)
(* ---------------------------------------------------------------- *)
(* 数学核：单步不等式归约为插值配分 Z = Σ pit^{1-eta}·pis^eta ≤ 1   *)

(* ---------------------------------------------------------------- *)
(*   在盘引擎 real_step_kl_eta_bound_eps（根 L113142）与       *)
(*   real_step_kl_eta_bound_B（UpRealLeB.v L437）与 req 参数位语句       *)
(*   不是同形：①载体 nat-list(seq 0 n) vs 抽象 S+sumf；②序谓词      *)
(*   eps 形/eps-le 语言 vs 接口 Or 形 le（real_le_to_le_b 单向桥，   *)

(*   ③下一策略 real_step_next（几何插值）vs pi_next_req（softmax/    *)


(*   裁决：按普查 ② 指令转「实例化消解件」路线——在盘引擎为理论核，   *)

(*   （req 求和实例批的正内容）+ 引擎的接口形实例化消解。             *)
(* ---------------------------------------------------------------- *)
(* 本文件结果（前缀 geod_，grep 全库零撞名实测）：                    *)
(*   [保底] geod_pow_pos / geod_pow_pos_correct / geod_amgm_pointwise_eps *)
(*     逐点凸性（a^{1-e}b^e ≤ (1-e)a+e·b+eps），接口 req 语言换形；    *)
(*     geod_amgm_pointwise_iface 为逐字接口投影语形版。               *)
(*   [主件] geod_le_b（接口层 eps-le 非严格序语言，Set 值）+          *)
(*     geod_sum_collapse（抽象求和塌缩机：逐点 eps 配权 + 双归一化    *)
(*     吸收，任意增强接口+sumf 机器可依存）+                          *)
(*     geod_interp_Z_le_one_eps（插值 Z ≤ 1+eps 接口形实例——         *)
(*     数学核的 req/eps 形落盘）。                                    *)
(*   [主] geod_step_kl_eta_bound_eps（参数位语句的接口形消解件）+       *)
(*     geod_policy_iter_kl_geom_step_eps（主结论件：换向实例        *)
(*     KL(pis‖next) ≤ (1-eta)·KL(pis‖pit)+eps，假设位被 M2 引擎         *)
(*     一次喂定——「参数位被消解件填充的具体形态」，无条件无假设位）。       *)
(* ---------------------------------------------------------------- *)
(* 诚实边界（阻塞裁决见合规自查报告）：req 参数位的 plain-le（Or 形）结论     *)
(*   不可由 eps/eps-le 引擎消解——序无消去，逆向完成需强序闭包原理，   *)

(*   与红线「不等式走逐 eps/eps-le 语言」一致。                       *)
(* 红线：Set 层语句（real_lt/real_le/real_eq 均 Set 值，零泄露）；    *)
(*   零未闭合证明（全 Qed）；既有文件零改；纯 term-mode 组装。        *)

(*   （cpu_guard 包装，错峰单发）。                                   *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* G-A 抽象层：接口 eps-le 非严格序语言（任意增强接口可依存）        *)
(*   投影全 @ 显式（RIS 显式参，免实例消解歧义）                     *)
(* ============================================================ *)
Section GeodLeB.
Context {R : Set} (RIS : RealInterfaceEnhancedSetoid R).

(* eps-le 语言：x ≤_ge y := 对全部正 eps，x ≤ y+eps（Set 值 forall 形；
   与 UpRealLeB.real_le_b（lt 形）同族，取 le 支以适配 sum_le 直接塌缩） *)
Definition geod_le_b (x y : R) : Set :=
  forall eps : R, @lt R RIS zero eps -> @le R RIS x (@plus R RIS y eps).

(* 正移位：0 < eps 则 y ≤ y+eps（le 链：le_plus_compat + lt_le_iff） *)
Lemma geod_shift_le : forall (y eps : R),
  @lt R RIS zero eps -> @le R RIS y (@plus R RIS y eps).
Proof.
  intros y eps Heps.
  apply (@le_id_l R RIS y (@plus R RIS y zero) (@plus R RIS y eps)).
  - apply (@req_sym R RIS (@plus R RIS y zero) y). apply (@plus_zero R RIS y).
  - apply (@le_plus_compat R RIS y y zero eps).
    + apply (@le_refl R RIS y).
    + exact (@lt_le_iff R RIS zero eps (inl Heps)).
Qed.

(* 单向桥：接口 le ⟹ eps-le（le_trans 一步，零分支） *)
Lemma geod_le_to_le_b : forall x y : R,
  @le R RIS x y -> geod_le_b x y.
Proof.
  intros x y Hle eps Heps.
  exact (@le_trans R RIS x y (@plus R RIS y eps) Hle (geod_shift_le y eps Heps)).
Qed.

End GeodLeB.

(* ============================================================ *)

(*   逐点 eps 配权（权 = u，归一化 sumf u == 1）⟹ 总误差恰为 eps。   *)
(*   零除法、零折半，纯 sum_le + sum_add + sum_linear + 归一化吸收。  *)
(* ============================================================ *)
Section GeodSum.
Context {R : Set} (RIS : RealInterfaceEnhancedSetoid R).
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_le : forall f g : S -> R,
  (forall s : S, @le R RIS (f s) (g s)) -> @le R RIS (sumf f) (sumf g).
Hypothesis sum_add : forall f g : S -> R,
  @req R RIS (sumf (fun s => @plus R RIS (f s) (g s)))
       (@plus R RIS (sumf f) (sumf g)).
Hypothesis sum_linear : forall (a : R) (f : S -> R),
  @req R RIS (sumf (fun s => @mult R RIS a (f s))) (@mult R RIS a (sumf f)).

Lemma geod_sum_collapse : forall (u f g : S -> R),
  @req R RIS (sumf u) one ->
  (forall (eps : R), @lt R RIS zero eps -> forall s : S,
     @le R RIS (f s) (@plus R RIS (g s) (@mult R RIS eps (u s)))) ->
  geod_le_b RIS (sumf f) (sumf g).
Proof.
  intros u f g Hnorm Hpt eps Heps.
  apply (@le_id_r R RIS (sumf f)
                 (sumf (fun s => @plus R RIS (g s) (@mult R RIS eps (u s))))
                 (@plus R RIS (sumf g) eps)).
  - (* 求和端换形：Σ(g+eps·u) == Σg + eps·Σu == Σg + eps·1 == Σg+eps *)
    apply (@req_trans R RIS
             (sumf (fun s => @plus R RIS (g s) (@mult R RIS eps (u s))))
             (@plus R RIS (sumf g) (sumf (fun s => @mult R RIS eps (u s))))
             (@plus R RIS (sumf g) eps)).
    + exact (sum_add g (fun s => @mult R RIS eps (u s))).
    + apply (@req_plus_compat R RIS (sumf g) (sumf g)
                               (sumf (fun s => @mult R RIS eps (u s))) eps
                               (@req_refl R RIS (sumf g))).
      apply (@req_trans R RIS (sumf (fun s => @mult R RIS eps (u s)))
                         (@mult R RIS eps (sumf u))
                         eps).
      * exact (sum_linear eps u).
      * apply (@req_trans R RIS (@mult R RIS eps (sumf u))
                             (@mult R RIS eps one)
                             eps).
        -- apply (@req_mult_compat R RIS eps eps (sumf u) one
                    (@req_refl R RIS eps) Hnorm).
        -- exact (@mult_one R RIS eps).
  - (* 逐点 eps 配权提升 *)
    apply (sum_le f (fun s => @plus R RIS (g s) (@mult R RIS eps (u s)))).
    exact (Hpt eps Heps).
Qed.

End GeodSum.

(* ============================================================ *)
(* G-C Real 实例：幂载体与保底逐点凸性（接口 req 语言换形）          *)

(*   均为 RealEnhancedReal 实例投影，与 real_* 逐字段 delta 透明）。  *)
(* ============================================================ *)
Definition geod_pow_pos (a alpha : Real) (Ha : real_lt real_zero a) : Real :=
  real_exp_neg (real_opp (real_mult alpha (real_log a Ha))).

(* 环辅件：负负消去（逐点 ring，零名依赖） *)
Lemma geod_opp_opp : forall x : Real,
  real_eq (real_opp (real_opp x)) x.
Proof.
  intros x. destruct x as [u Hu]. apply real_eq_of_zero_diff.
  intro n. simpl. ring.
Qed.

(* 载体换形：接口形幂 == 根内 real_pow_pos（cw_log 层 delta + 负负消去）
   （real_exp_neg/real_log 与实例投影逐字段 delta 透明——载体即接口形） *)
Lemma geod_pow_pos_correct : forall (a alpha : Real) (Ha : real_lt real_zero a),
  real_eq (geod_pow_pos a alpha Ha) (real_pow_pos a alpha Ha).
Proof.
  intros a alpha Ha.
  apply (real_eq_trans (geod_pow_pos a alpha Ha)
                       (cauchy_real_exp (real_opp (real_opp (real_mult alpha (cw_log a Ha)))))
                       (real_pow_pos a alpha Ha)).
  - exact (real_eq_refl _).
  - apply (cauchy_real_exp_wd _ _). apply geod_opp_opp.
Qed.

(* 保底：逐点凸性/加权 AM-GM（a^{1-e}·b^e ≤ (1-e)a + e·b + eps）
   证书供给链：real_le_compat 换形 + 根内 real_amgm_pointwise_eps 直连
   （Varberg 锥引擎，L112817 在盘，零重建理论） *)
Theorem geod_amgm_pointwise_eps : forall (a b eta : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_mult (geod_pow_pos a (real_plus real_one (real_opp eta)) Ha)
                     (geod_pow_pos b eta Hb))
          (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) a)
                                (real_mult eta b)) eps).
Proof.
  intros a b eta Ha Hb Heta Hetale eps Heps.
  exact (RealSetoid.real_le_compat           (real_mult (real_pow_pos a (real_plus real_one (real_opp eta)) Ha)                      (real_pow_pos b eta Hb))           (real_mult (geod_pow_pos a (real_plus real_one (real_opp eta)) Ha)                      (geod_pow_pos b eta Hb))           (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) a)                                 (real_mult eta b)) eps)           (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) a)                                 (real_mult eta b)) eps)           (RealSetoid.real_eq_mult_compat              (real_pow_pos a (real_plus real_one (real_opp eta)) Ha)              (real_pow_pos b eta Hb)              (geod_pow_pos a (real_plus real_one (real_opp eta)) Ha)              (geod_pow_pos b eta Hb)              (real_eq_sym _ _ (geod_pow_pos_correct a (real_plus real_one (real_opp eta)) Ha))              (real_eq_sym _ _ (geod_pow_pos_correct b eta Hb)))           (real_eq_refl _)           (real_amgm_pointwise_eps a b eta Ha Hb Heta Hetale eps Heps)).
Qed.

(* 保底接口语形版：结论谓词与前提谓词逐字取接口投影（与保底件
   delta 同体，登记接口形出口面） *)
Theorem geod_amgm_pointwise_iface : forall (a b eta : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  @lt Real RealEnhancedReal real_zero eta ->
  @le Real RealEnhancedReal eta real_one ->
  forall eps : Real, @lt Real RealEnhancedReal real_zero eps ->
  @le Real RealEnhancedReal
     (real_mult (geod_pow_pos a (real_plus real_one (real_opp eta)) Ha)
                (geod_pow_pos b eta Hb))
     (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) a)
                           (real_mult eta b)) eps).
Proof.
  exact (fun a b eta Ha Hb => geod_amgm_pointwise_eps a b eta Ha Hb).
Qed.

(* ============================================================ *)
(* G-D Real 实例：list 求和机器 + 插值 Z ≤ 1+eps（主件落盘）         *)
(* ============================================================ *)
Definition geod_lsum (n : nat) (f : nat -> Real) : Real :=
  real_list_sum nat f (List.seq 0 n).

(* list 求和三参数位（real_list_sum_* 显式应用，X := nat 显式） *)
Lemma geod_lsum_le : forall (n : nat) (f g : nat -> Real),
  (forall i : nat, real_le (f i) (g i)) ->
  real_le (geod_lsum n f) (geod_lsum n g).
Proof.
  intros n f g H.
  unfold geod_lsum.
  exact (real_list_sum_le nat f g (List.seq 0 n) H).
Qed.

Lemma geod_lsum_add : forall (n : nat) (f g : nat -> Real),
  real_eq (geod_lsum n (fun i => real_plus (f i) (g i)))
          (real_plus (geod_lsum n f) (geod_lsum n g)).
Proof.
  intros n f g.
  unfold geod_lsum.
  exact (real_list_sum_add nat f g (List.seq 0 n)).
Qed.

Lemma geod_lsum_linear : forall (n : nat) (a : Real) (f : nat -> Real),
  real_eq (geod_lsum n (fun i => real_mult a (f i)))
          (real_mult a (geod_lsum n f)).
Proof.
  intros n a f.
  unfold geod_lsum.
  exact (real_list_sum_linear nat a f (List.seq 0 n)).
Qed.

(* 环辅件：eta + (1-eta) == 1 *)
Lemma geod_eta_plus_kappa : forall eta : Real,
  real_eq (real_plus eta (real_plus real_one (real_opp eta))) real_one.
Proof.
  intros eta. destruct eta as [v Hv]. apply real_eq_of_zero_diff.
  intro n. simpl. ring.
Qed.

(* 环辅件：0 + x == x *)
Lemma geod_plus_zero_l : forall x : Real,
  real_eq (real_plus real_zero x) x.
Proof.
  intros x. destruct x as [u Hu]. apply real_eq_of_zero_diff.
  intro n. simpl. ring.
Qed.

(* 加权和归一化：Σ(m·pit + eta·pis) == (1-eta)·Σpit + eta·Σpis == 1
   （M1 同款吸收，list 件直连） *)
Lemma geod_lsum_pair_norm : forall (n : nat) (pit pist : nat -> Real) (eta : Real)
    (Hnormp : real_eq (geod_lsum n pit) real_one)
    (Hnormr : real_eq (geod_lsum n pist) real_one),
  real_eq (geod_lsum n (fun i => real_plus
                          (real_mult (real_plus real_one (real_opp eta)) (pit i))
                          (real_mult eta (pist i))))
          real_one.
Proof.
  intros n pit pist eta Hnormp Hnormr.
  apply (real_eq_trans _
           (real_plus (real_mult (real_plus real_one (real_opp eta)) (geod_lsum n pit))
                      (real_mult eta (geod_lsum n pist)))).
  - (* Σ(f+g) == Σf + Σg + 线性律 *)
    apply (real_eq_trans _
             (real_plus (geod_lsum n (fun i => real_mult (real_plus real_one (real_opp eta)) (pit i)))
                        (geod_lsum n (fun i => real_mult eta (pist i))))).
    + exact (geod_lsum_add n _ _).
    + apply (RealSetoid.real_eq_plus_compat _ _ _ _
               (geod_lsum_linear n (real_plus real_one (real_opp eta)) pit)
               (geod_lsum_linear n eta pist)).
  - (* 归一化吸收 + (1-eta)+eta == 1 *)
    apply (real_eq_trans _
             (real_plus (real_mult (real_plus real_one (real_opp eta)) real_one)
                        (real_mult eta real_one))).
    + apply (RealSetoid.real_eq_plus_compat _ _ _ _
               (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _) Hnormp)
               (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _) Hnormr)).
    + apply (real_eq_trans _
               (real_plus (real_plus real_one (real_opp eta)) eta)).
      * apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_mult_one _) (real_mult_one _)).
      * (* (1-eta)+eta == 1：换序 + eta+(1-eta)==1 *)
        apply (real_eq_trans _
                 (real_plus eta (real_plus real_one (real_opp eta)))).
        -- apply real_plus_comm.
        -- exact (geod_eta_plus_kappa eta).
Qed.

(* list 版求和塌缩（real 面——G3 提取闭包零实例记录；与抽象机
   geod_sum_collapse 同构，sumf := geod_lsum n 实例化） *)
Lemma geod_lsum_collapse_real : forall (n : nat) (u f g : nat -> Real),
  real_eq (geod_lsum n u) real_one ->
  (forall (eps : Real), real_lt real_zero eps -> forall i : nat,
     real_le (f i) (real_plus (g i) (real_mult eps (u i)))) ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (geod_lsum n f) (real_plus (geod_lsum n g) eps).
Proof.
  intros n u f g Hnorm Hpt eps Heps.
  apply (RealSetoid.real_le_id_r (geod_lsum n f)
         (geod_lsum n (fun i => real_plus (g i) (real_mult eps (u i))))
         (real_plus (geod_lsum n g) eps)).
  - apply (real_eq_trans
             (geod_lsum n (fun i => real_plus (g i) (real_mult eps (u i))))
             (real_plus (geod_lsum n g) (geod_lsum n (fun i => real_mult eps (u i))))
             (real_plus (geod_lsum n g) eps)).
    + exact (geod_lsum_add n g (fun i => real_mult eps (u i))).
    + apply (RealSetoid.real_eq_plus_compat (geod_lsum n g)
               (geod_lsum n (fun i => real_mult eps (u i)))
               (geod_lsum n g) eps).
      * apply real_eq_refl.
      * apply (real_eq_trans (geod_lsum n (fun i => real_mult eps (u i)))
                             (real_mult eps (geod_lsum n u)) eps).
        -- exact (geod_lsum_linear n eps u).
        -- exact (real_eq_trans (real_mult eps (geod_lsum n u))
                   (real_mult eps real_one) eps
                   (RealSetoid.real_eq_mult_compat eps (geod_lsum n u) eps real_one
                      (real_eq_refl _) Hnorm)
                   (real_mult_one eps)).
  - apply (geod_lsum_le n f (fun i => real_plus (g i) (real_mult eps (u i)))).
    exact (Hpt eps Heps).
Qed.

(* 主件：插值配分 Z ≤ 1 + eps（接口形，数学核落盘）
   Z := Σ pit^{1-eta}·pis^eta ≤ 1+eps——逐点 AM-GM（保底件）配权
   eps·pit(i)，geod_sum_collapse 求和塌缩吸收（归一化双前提）。 *)
Theorem geod_interp_Z_le_one_eps : forall (n : nat) (pit pist : nat -> Real) (eta : Real)
    (Hpit : forall i : nat, real_lt real_zero (pit i))
    (Hpist : forall i : nat, real_lt real_zero (pist i))
    (Hnormp : real_eq (geod_lsum n pit) real_one)
    (Hnormr : real_eq (geod_lsum n pist) real_one),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (geod_lsum n (fun i => real_mult
                            (geod_pow_pos (pit i) (real_plus real_one (real_opp eta)) (Hpit i))
                            (geod_pow_pos (pist i) eta (Hpist i))))
          (real_plus real_one eps).
Proof.
  intros n pit pist eta Hpit Hpist Hnormp Hnormr Heta Hetale eps Heps.
  pose proof (geod_lsum_collapse_real n pit
                (fun i => real_mult
                            (geod_pow_pos (pit i) (real_plus real_one (real_opp eta)) (Hpit i))
                            (geod_pow_pos (pist i) eta (Hpist i)))
                (fun i => real_plus (real_mult (real_plus real_one (real_opp eta)) (pit i))
                                    (real_mult eta (pist i)))
                Hnormp
                (fun e He i => geod_amgm_pointwise_eps (pit i) (pist i) eta (Hpit i) (Hpist i)
                                 Heta Hetale (real_mult e (pit i))
                                 (real_mult_positive e (pit i) He (Hpit i)))
                eps Heps) as Hm.
  apply (RealSetoid.real_le_id_r
           (geod_lsum n (fun i => real_mult
                            (geod_pow_pos (pit i) (real_plus real_one (real_opp eta)) (Hpit i))
                            (geod_pow_pos (pist i) eta (Hpist i))))
           (real_plus (geod_lsum n (fun i => real_plus
                            (real_mult (real_plus real_one (real_opp eta)) (pit i))
                            (real_mult eta (pist i)))) eps)
           (real_plus real_one eps)).
  - apply (RealSetoid.real_eq_plus_compat
              (geod_lsum n (fun i => real_plus
                              (real_mult (real_plus real_one (real_opp eta)) (pit i))
                              (real_mult eta (pist i))))
              eps real_one eps
              (geod_lsum_pair_norm n pit pist eta Hnormp Hnormr) (real_eq_refl _)).
  - exact Hm.
Qed.

(* ============================================================ *)
(* G-E 主定理：参数位语句消解件 + 换向结论件（参数位被引擎一次喂定的具体形态）  *)
(* ============================================================ *)
(* eta 缩放辅件：0 < eta 则 1-eta > 0（m3_kappa_pos 同款直连，
   本地零依赖复刻：ring 恒等 + lt 平移） *)
Lemma geod_kappa_pos : forall eta : Real,
  real_lt eta real_one ->
  real_lt real_zero (real_plus real_one (real_opp eta)).
Proof.
  intros eta Hlt.
  exact (real_eq_lt_lt real_zero (real_plus eta (real_opp eta))           (real_plus real_one (real_opp eta))           (real_eq_sym (real_plus eta (real_opp eta)) real_zero              (real_plus_opp eta))           (real_lt_plus_compat_lt_le eta real_one (real_opp eta)              (real_opp eta) Hlt (real_le_refl (real_opp eta)))).
Qed.

(* 0 < eta 则 1-eta ≤ 1（lt 支经 Or 左支入 le） *)
Lemma geod_kappa_le_one : forall eta : Real,
  real_lt real_zero eta ->
  real_le (real_plus real_one (real_opp eta)) real_one.
Proof.
  intros eta Hpos.
  assert (Hlt : real_lt (real_plus real_one (real_opp eta)) real_one).
  { apply (real_lt_eq_lt (real_plus real_one (real_opp eta))
             (real_plus eta (real_plus real_one (real_opp eta))) real_one).
    - exact (real_eq_lt_lt (real_plus real_one (real_opp eta))
               (real_plus real_zero (real_plus real_one (real_opp eta)))
               (real_plus eta (real_plus real_one (real_opp eta)))
               (real_eq_sym _ _ (geod_plus_zero_l (real_plus real_one (real_opp eta))))
               (real_lt_plus_compat_lt_le real_zero eta
                  (real_plus real_one (real_opp eta))
                  (real_plus real_one (real_opp eta))
                  Hpos (real_le_refl (real_plus real_one (real_opp eta))))).
    - exact (geod_eta_plus_kappa eta). }
  exact (inl Hlt).
Qed.

(* 主假设位消解件：单步 KL 收缩的接口形 eps 版
   KL(pit‖next) ≤ eta·KL(pit‖pis) + eps，next := 几何插值策略
   （req 参数位语句 req_step_kl_eta_bound 的 eps-le 语言对应物；
   证书链 = 根内 M2 引擎 real_step_kl_eta_bound_eps 一次喂定） *)
Theorem geod_step_kl_eta_bound_eps :
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr))
    (Hqv : forall i : nat,
             real_lt real_zero (real_step_next n p r eta Hp Hr HZ i)),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (geod_lsum n
             (fun i : nat => real_kl_term (p i)
                             (real_step_next n p r eta Hp Hr HZ i) (Hp i) (Hqv i)))
          (real_plus (real_mult eta
                        (geod_lsum n
                           (fun i : nat => real_kl_term (p i) (r i) (Hp i) (Hr i))))
                     eps).
Proof.
  intros n p r eta Hp Hr Hnormp Hnormr HZ Hqv Heta Hetale eps Heps.
  unfold geod_lsum.
  exact (real_step_kl_eta_bound_eps n p r eta Hp Hr Hnormp Hnormr HZ Hqv           Heta Hetale eps Heps).
Qed.

(* 主结论件：单步真几何收缩（policy_iter_kl_geom_step 的接口形
   eps 对应物）——M2 换向实例（p-参数位 := pis、r-参数位 := pit、eta-参数位 :=
   1-eta），假设位被引擎一次喂定，无条件无假设位：
   KL(pis‖next) ≤ (1-eta)·KL(pis‖pit) + eps *)
Theorem geod_policy_iter_kl_geom_step_eps :
  forall (n : nat) (r p : nat -> Real) (eta : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (HZ : real_lt real_zero (real_interp_Z n r p (real_plus real_one (real_opp eta)) Hr Hp))
    (Hqv : forall i : nat,
             real_lt real_zero (real_step_next n r p (real_plus real_one (real_opp eta)) Hr Hp HZ i)),
  real_lt real_zero eta -> real_lt eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (geod_lsum n
             (fun i : nat => real_kl_term (r i)
                             (real_step_next n r p (real_plus real_one (real_opp eta)) Hr Hp HZ i)
                             (Hr i) (Hqv i)))
          (real_plus (real_mult (real_plus real_one (real_opp eta))
                        (geod_lsum n
                           (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                     eps).
Proof.
  intros n r p eta Hr Hp Hnormr Hnormp HZ Hqv Heta Hlt1 eps Heps.
  unfold geod_lsum.
  exact (real_step_kl_eta_bound_eps n r p (real_plus real_one (real_opp eta))           Hr Hp Hnormr Hnormp HZ Hqv           (geod_kappa_pos eta Hlt1) (geod_kappa_le_one eta Heta) eps Heps).
Qed.
