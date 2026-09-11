(* ============================================================ *)
(* UpReqGeomIter.v —— 第二轮非平凡补强 ①：策略迭代族 Real 层迭代镜像席  *)
(*   任务书源＝第二轮非平凡补强-前十分析-20260910.md R2-1（L9/L96）：    *)
(*   定理 4.8 的抽象层迭代收缩 KL(π*‖π_t) 以 (1−η)^t 几何收缩，        *)
(*   在 Real 层按「单步放电件＋幂载体」归纳合龙（eps 形）。             *)
(* ---------------------------------------------------------------- *)
(* 先例件（全部只消费 .vo，零改已绿文件）：                              *)
(*   UpReqGeomD：旗舰单步 geod_policy_iter_kl_geom_step_eps（L451）      *)
(*     KL(r‖next) ≤ (1−η)·KL(r‖p)+eps ＋ geod_lsum/geod_kappa_pos；      *)
(*   UpReqPowB：幂载体 powb_pow（(1−η)^t）；                             *)
(*   UpRealLeB：real_le_b/real_le_to_le_b（B 伴件语言）；                *)
(*   UpGeomB：geod_b_half_double（半量机，KL Bishop 非负伴件消费）。      *)
(* ---------------------------------------------------------------- *)
(* 数学核（归纳合龙，单点 eps 引入→常数加权→末端收口）：                 *)
(*   迭代轨道 π_0 := p，π_{t+1} := step_next(π*, π_t; κ:=1−η)。          *)
(*   不变式：KL(π*‖π_t) ≤ κ^t·KL(π*‖π_0) + eps（同一 eps 全程不漂移）。  *)
(*   归纳步：单步件喂余量 η·eps（0<η·eps 引擎件喂定），                  *)
(*     κ·(κ^t·KL0 + eps) + η·eps = κ^{t+1}·KL0 + (κ+η)·eps              *)
(*     = κ^{t+1}·KL0 + 1·eps = κ^{t+1}·KL0 + eps——κ+η==1 环账一次收口，  *)
(*   余量链零中途翻倍（单误差源单点引入，C.2 模板要点）。                *)
(* ---------------------------------------------------------------- *)
(* 分层保底（分件 Qed）：单步（消费 GeomD 旗舰）→ 一步件 → 两步件 →      *)
(*   t 步归纳主件。各层形态同构，无余量漂移，无负结果。                  *)
(* ---------------------------------------------------------------- *)
(* 诚实边界与判词：                                                      *)
(*   【判词 I1｜η 开区间】主件前提 0<η<1。闭端 η=1 时 κ=1−η 的严格正    *)
(*   证书构造性不可分（PowB 判词 P4 在案），且单步引擎                    *)
(*   real_step_kl_eta_bound_eps 本身要求 0<κ——与任务书「η∈(0,1]」        *)
(*   口径的出入见交付报告勘误 E-1。                                      *)
(*   【判词 I2｜n 非平凡】n≥1 显式前提：Z:=Σ r^{1−κ}q^κ 的正性在 n=0     *)
(*   时不可证（空和=0），沿 real_list_sum_pos 非空前提同格。             *)
(*   【判词 I3｜证书依赖】real_pow_pos/real_log 值依赖正性见证参数位，    *)
(*   迭代轨道以 sigT（Set 值）打包逐站证书线程（UpGeomB geod_b_iterate    *)
(*   同构先例）；语句面全 Set 值零 Prop 泄露。                           *)
(*   【判词 I4｜PowB 幂单调衔接差距】主件只消费 powb_pow 幂载体；         *)
(*   powb_one_minus_eta_mono_dec（κ^{t1} ≤_B κ^t）与主件合成为           *)
(*   「t ≤ t1 ⟹ KL_{t1} ≤ κ^t·KL_0」需 κ^{t1}·KL_0 ≤ κ^t·KL_0+δ 的      *)
(*   le_b 乘法保序闭包（非负右因子版），其证需 KL_0 上界材料或专门的     *)
(*   幂单调-KL 合成器——库内两件皆无，挂账未建（精确差距见交付报告）。    *)
(*   可用侧标记：KL_0 的 Bishop 非负 0 ≤_B KL_0 本席已伴件落盘           *)
(*   （geodi_kl_nonneg_B，gibbs+半量机），缺口纯在乘法保序闭包一侧。      *)
(* 红线：零未闭合证明（全 Qed）；零新公理；语句面全 Set 值（real_le/      *)
(*   real_lt/real_eq/real_le_b 均 Set 值，Or:=A+B 库内定义）；既有文件    *)
(*   零改；纯 term-mode 组装（real_eq 非 Id，禁 rewrite 主链，全链       *)
(*   real_eq_trans/compat）。                                            *)
(* 编译配方：C:\Rocq-Platform~9.0~2025.08\bin\coqc.exe                    *)
(*   -Q . "" -Q "..\001" "" UpReqGeomIter.v（cpu_guard 包装，禁裸调）。   *)
(* ============================================================ *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Export G07_KLWall.
Require Import UpReqGeomD.
Require Import UpGeomB.

(* ============================================================ *)
(* A. 环辅件：κ + η == 1（κ := 1−η 字面承载；GeomD η+(1−η)==1 换序）    *)
(* ============================================================ *)
Lemma geodi_kappa_plus_eta : forall eta : Real,
  real_eq (real_plus (real_plus real_one (real_opp eta)) eta) real_one.
Proof.
  intros eta.
  apply (real_eq_trans _ (real_plus eta (real_plus real_one (real_opp eta)))).
  - apply real_plus_comm.
  - exact (geod_eta_plus_kappa eta).
Qed.

(* 左单位元：1·x == x（CW_219 仅右单位元件 real_mult_one；comm 换位直给） *)
Lemma geodi_mult_one_l : forall x : Real,
  real_eq (real_mult real_one x) x.
Proof.
  intro x.
  exact (real_eq_trans (real_mult real_one x) (real_mult x real_one) x
           (real_mult_comm real_one x) (real_mult_one x)).
Qed.

(* ============================================================ *)
(* B. 正性三件：幂正 / 插值配分 Z 正 / 下一策略逐点正                    *)
(* ============================================================ *)
Lemma geodi_pow_pos_lt : forall (a alpha : Real) (Ha : real_lt real_zero a),
  real_lt real_zero (real_pow_pos a alpha Ha).
Proof.
  intros a alpha Ha. unfold real_pow_pos.
  exact (cauchy_real_exp_pos (real_mult alpha (cw_log a Ha))).
Qed.

(* Z 正（n≥1 非平凡前提；逐项=正幂×正幂，real_list_sum_pos 非空和正） *)
(*   n≥1 界走 CW_219 Set 层编码 NatLt := Id (ltb) true（UpMinP/UpReqPowB   *)
(*   先例同款；Prop 层 Datatypes.lt 构造性红线禁用，n=0 支路经              *)
(*   id_false_true（CW_219：Id false true -> Empty_set）destruct 爆破）   *)
Lemma geodi_zpos : forall (n : nat) (r q : nat -> Real) (kappa : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hq : forall i : nat, real_lt real_zero (q i))
    (Hn : NatLt 0 n),
  real_lt real_zero (real_interp_Z n r q kappa Hr Hq).
Proof.
  intros n r q kappa Hr Hq Hn. unfold real_interp_Z.
  apply (real_list_sum_pos nat).
  - intro i.
    apply (real_mult_positive
             (real_pow_pos (r i) (real_plus real_one (real_opp kappa)) (Hr i))
             (real_pow_pos (q i) kappa (Hq i))).
    + exact (geodi_pow_pos_lt (r i) (real_plus real_one (real_opp kappa)) (Hr i)).
    + exact (geodi_pow_pos_lt (q i) kappa (Hq i)).
  - destruct n as [| m].
    + (* NatLt 0 0 ≡ Id false true：Empty_set 零构造子爆破（UpReqPowB 先例） *)
      destruct (id_false_true Hn).
    + intro Hc. simpl in Hc. discriminate Hc.
Qed.

(* 下一策略逐点正：正幂×正幂×正倒数的乘法正性链 *)
Lemma geodi_next_pos : forall (n : nat) (r q : nat -> Real) (kappa : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hq : forall i : nat, real_lt real_zero (q i))
    (Hn : NatLt 0 n) (i : nat),
  real_lt real_zero
    (real_step_next n r q kappa Hr Hq (geodi_zpos n r q kappa Hr Hq Hn) i).
Proof.
  intros n r q kappa Hr Hq Hn i. unfold real_step_next.
  apply (real_mult_positive
           (real_mult
              (real_pow_pos (r i) (real_plus real_one (real_opp kappa)) (Hr i))
              (real_pow_pos (q i) kappa (Hq i)))
           (real_inv_pos (real_interp_Z n r q kappa Hr Hq)
                         (geodi_zpos n r q kappa Hr Hq Hn))).
  - apply (real_mult_positive
             (real_pow_pos (r i) (real_plus real_one (real_opp kappa)) (Hr i))
             (real_pow_pos (q i) kappa (Hq i))).
    + exact (geodi_pow_pos_lt (r i) (real_plus real_one (real_opp kappa)) (Hr i)).
    + exact (geodi_pow_pos_lt (q i) kappa (Hq i)).
  - exact (real_inv_pos_pos (real_interp_Z n r q kappa Hr Hq)
              (geodi_zpos n r q kappa Hr Hq Hn)).
Qed.

(* ============================================================ *)
(* C. 迭代轨道载体：sigT 打包逐站证书的依赖递归（全 Set 值）              *)
(*   π_0 := p；π_{S m} := step_next(π*, π_m; κ)，Z 正/逐点正自足供给。   *)
(* ============================================================ *)
Fixpoint geodi_seq (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) (kappa : Real)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hn : NatLt 0 n) (t : nat)
  : sigT (fun q : nat -> Real => forall i : nat, real_lt real_zero (q i)) :=
  match t with
  | O => existT _ p Hp
  | Datatypes.S m =>
      match geodi_seq n r Hr kappa p Hp Hn m with
      | existT _ q Hq =>
          existT _
            (real_step_next n r q kappa Hr Hq
               (geodi_zpos n r q kappa Hr Hq Hn))
            (geodi_next_pos n r q kappa Hr Hq Hn)
      end
  end.

Definition geodi_iterate (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) (eta : Real)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hn : NatLt 0 n) (t : nat) : nat -> Real :=
  projT1 (geodi_seq n r Hr (real_plus real_one (real_opp eta)) p Hp Hn t).

Definition geodi_iterate_pos (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) (eta : Real)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hn : NatLt 0 n) (t : nat) :
  forall i : nat, real_lt real_zero (geodi_iterate n r Hr eta p Hp Hn t i) :=
  projT2 (geodi_seq n r Hr (real_plus real_one (real_opp eta)) p Hp Hn t).

(* 还原引理：S 站轨道 == 引擎下一策略（匹配消解在证内完成） *)
Lemma geodi_iterate_S : forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) (eta : Real)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hn : NatLt 0 n) (m : nat),
  geodi_iterate n r Hr eta p Hp Hn (Datatypes.S m) =
  real_step_next n r (geodi_iterate n r Hr eta p Hp Hn m)
    (real_plus real_one (real_opp eta))
    Hr (geodi_iterate_pos n r Hr eta p Hp Hn m)
    (geodi_zpos n r (geodi_iterate n r Hr eta p Hp Hn m)
       (real_plus real_one (real_opp eta)) Hr
       (geodi_iterate_pos n r Hr eta p Hp Hn m) Hn).
Proof.
  intros n r Hr eta p Hp Hn m.
  unfold geodi_iterate, geodi_iterate_pos.
  (* 先单步 ι 展开 (S m) 支露出 match（变量 m 上 fix 不动、内层保持折叠），  *)
  (* 再 destruct 内层轨道 existT 换形——顺序颠倒则 match 永远卡死。          *)
  cbn [geodi_seq].
  destruct (geodi_seq n r Hr (real_plus real_one (real_opp eta)) p Hp Hn m)
    as [q Hq].
  reflexivity.
Qed.

(* 轨道 sigT 对子方程：S 站整对 == existT 打包(step(q), next证书(q))。        *)
(*   依赖证书换型的合法 rewrite 目标：对 geodi_seq (S m) 整体抽象是依赖      *)
(*   良定的（证书的类型随对子整体换型），对裸值 geodi_iterate (S m) 抽象     *)
(*   则不适定（real_kl_term 第4参类型依赖第2参值）。                         *)
Lemma geodi_seq_pair_S : forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) (kappa : Real)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hn : NatLt 0 n) (m : nat),
  geodi_seq n r Hr kappa p Hp Hn (Datatypes.S m) =
  existT (fun q : nat -> Real => forall i : nat, real_lt real_zero (q i))
    (real_step_next n r (projT1 (geodi_seq n r Hr kappa p Hp Hn m))
       kappa Hr (projT2 (geodi_seq n r Hr kappa p Hp Hn m))
       (geodi_zpos n r (projT1 (geodi_seq n r Hr kappa p Hp Hn m)) kappa Hr
          (projT2 (geodi_seq n r Hr kappa p Hp Hn m)) Hn))
    (geodi_next_pos n r (projT1 (geodi_seq n r Hr kappa p Hp Hn m)) kappa Hr
       (projT2 (geodi_seq n r Hr kappa p Hp Hn m)) Hn).
Proof.
  intros n r Hr kappa p Hp Hn m.
  cbn [geodi_seq].
  destruct (geodi_seq n r Hr kappa p Hp Hn m) as [q Hq].
  reflexivity.
Qed.

(* ============================================================ *)
(* D. 归一化沿轨不变：Σ π_{t+1} == Σ(term)·inv Z == Z·inv Z == 1          *)
(* ============================================================ *)
Lemma geodi_step_norm : forall (n : nat) (r q : nat -> Real) (kappa : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hq : forall i : nat, real_lt real_zero (q i))
    (HZ : real_lt real_zero (real_interp_Z n r q kappa Hr Hq)),
  real_eq (geod_lsum n (real_step_next n r q kappa Hr Hq HZ)) real_one.
Proof.
  intros n r q kappa Hr Hq HZ.
  unfold geod_lsum, real_step_next.
  apply (real_eq_trans _
           (real_mult (real_inv_pos (real_interp_Z n r q kappa Hr Hq) HZ)
                      (real_interp_Z n r q kappa Hr Hq))).
  - (* Σ(term·invZ) == invZ·Σterm == invZ·Z（Σterm≡Z 定义透明） *)
    apply (real_eq_trans _
             (real_mult (real_inv_pos (real_interp_Z n r q kappa Hr Hq) HZ)
                        (real_list_sum nat
                           (fun i : nat =>
                              real_mult (real_pow_pos (r i) (real_plus real_one (real_opp kappa)) (Hr i))
                              (real_pow_pos (q i) kappa (Hq i)))
                           (seq 0 n)))).
    + exact (real_list_sum_linear_r nat
               (real_inv_pos (real_interp_Z n r q kappa Hr Hq) HZ)
               (fun i : nat =>
                  real_mult (real_pow_pos (r i) (real_plus real_one (real_opp kappa)) (Hr i))
                              (real_pow_pos (q i) kappa (Hq i)))
               (seq 0 n)).
    + apply (RealSetoid.real_eq_mult_compat
               (real_inv_pos (real_interp_Z n r q kappa Hr Hq) HZ)
               (real_list_sum nat
                  (fun i : nat =>
                     real_mult (real_pow_pos (r i) (real_plus real_one (real_opp kappa)) (Hr i))
                              (real_pow_pos (q i) kappa (Hq i)))
                  (seq 0 n))
               (real_inv_pos (real_interp_Z n r q kappa Hr Hq) HZ)
               (real_interp_Z n r q kappa Hr Hq)).
      * apply real_eq_refl.
      * apply real_eq_refl.
  - (* invZ·Z == Z·invZ == 1 *)
    apply (real_eq_trans _
             (real_mult (real_interp_Z n r q kappa Hr Hq)
                        (real_inv_pos (real_interp_Z n r q kappa Hr Hq) HZ))).
    + apply real_mult_comm.
    + exact (real_inv_pos_correct (real_interp_Z n r q kappa Hr Hq) HZ).
Qed.

Lemma geodi_seq_norm : forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) (eta : Real)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hn : NatLt 0 n)
    (Hnormp : real_eq (geod_lsum n p) real_one) (t : nat),
  real_eq (geod_lsum n (geodi_iterate n r Hr eta p Hp Hn t)) real_one.
Proof.
  intros n r Hr eta p Hp Hn Hnormp t. induction t as [| m IH].
  - exact Hnormp.
  - rewrite geodi_iterate_S.
    exact (geodi_step_norm n r (geodi_iterate n r Hr eta p Hp Hn m)
             (real_plus real_one (real_opp eta)) Hr
             (geodi_iterate_pos n r Hr eta p Hp Hn m)
             (geodi_zpos n r (geodi_iterate n r Hr eta p Hp Hn m)
                (real_plus real_one (real_opp eta)) Hr
                (geodi_iterate_pos n r Hr eta p Hp Hn m) Hn)).
Qed.

(* 成对泛化范数：m 站轨道分量 q 的归一化（destruct 换形后的 Hp-槽直供件）。 *)
(*   fold 包装 geodi_iterate … m 与消解后 q 不可转换（变量 m 上 fix 卡死），  *)
(*   故沿轨证书族须以「轨道 = existT q Hq」方程为载体成对泛化。              *)
Lemma geodi_seq_norm_pair : forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) (eta : Real)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hn : NatLt 0 n)
    (Hnormp : real_eq (geod_lsum n p) real_one) (m : nat)
    (q : nat -> Real) (Hq : forall i : nat, real_lt real_zero (q i)),
  geodi_seq n r Hr eta p Hp Hn m = existT _ q Hq ->
  real_eq (geod_lsum n q) real_one.
Proof.
  intros n r Hr eta p Hp Hn Hnormp m.
  induction m as [| m IH]; intros q Hq E.
  - cbn [geodi_seq] in E.
    (* 基例：分量方程给 p = q（projT1 投影，避开依赖 inversion） *)
    assert (Epq : p = q).
    { exact (f_equal (@projT1 (nat -> Real)
                        (fun q0 : nat -> Real => forall i : nat,
                            real_lt real_zero (q0 i))) E). }
    rewrite <- Epq. exact Hnormp.
  - cbn [geodi_seq] in E.
    destruct (geodi_seq n r Hr eta p Hp Hn m) as [q' Hq'] eqn:E'.
    cbn [projT1 projT2] in E.
    (* S 站分量 q == step(q')（projT1 投影），范数沿 geodi_step_norm 供给 *)
    assert (Eq1 : real_step_next n r q' eta Hr Hq'
                    (geodi_zpos n r q' eta Hr Hq' Hn) = q).
    { exact (f_equal (@projT1 (nat -> Real)
                        (fun q0 : nat -> Real => forall i : nat,
                            real_lt real_zero (q0 i))) E). }
    rewrite <- Eq1.
    exact (geodi_step_norm n r q' eta Hr Hq'
             (geodi_zpos n r q' eta Hr Hq' Hn)).
Qed.

(* ============================================================ *)
(* E. 正因子左乘保序（Or 两支：lt 支引擎件喂定；eq 支换形）               *)
(* ============================================================ *)
Lemma geodi_mult_le_compat_l : forall (kappa a b : Real),
  real_lt real_zero kappa -> real_le a b ->
  real_le (real_mult kappa a) (real_mult kappa b).
Proof.
  intros kappa a b Hk Hab. destruct Hab as [Hlt | Heq].
  - exact (inl (real_mult_lt_compat_l a b kappa Hlt Hk)).
  - exact (inr (RealSetoid.real_eq_mult_compat kappa a kappa b
                  (real_eq_refl kappa) Heq)).
Qed.

(* ============================================================ *)
(* F. 旗舰主件：t 步几何收缩（eps 形，单点余量全程不漂移）                *)
(*   KL(π*‖π_t) ≤ (1−η)^t·KL(π*‖π_0) + eps                              *)
(* ============================================================ *)
Theorem geodi_policy_iter_kl_geom_iter_eps :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n),
  forall (t : nat) (eps : Real) (Heps : real_lt real_zero eps),
  real_le
    (geod_lsum n
       (fun i : nat => real_kl_term (r i)
                       (geodi_iterate n r Hr eta p Hp Hn t i)
                       (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
    (real_plus
       (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
                  (geod_lsum n
                     (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
       eps).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn t eps Heps.
  induction t as [| m IH].
  - (* 基例 t=0：KL0 ≤ 1·KL0 + eps（1·KL0 == KL0 换形，UpGeomB 同款） *)
    apply (RealSetoid.real_le_id_l
             (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
             (real_mult (powb_pow (real_plus real_one (real_opp eta)) O)
                (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
             (real_plus
                (real_mult (powb_pow (real_plus real_one (real_opp eta)) O)
                   (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                eps)).
    + apply real_eq_sym.
      exact (real_eq_trans
               (real_mult (powb_pow (real_plus real_one (real_opp eta)) O)
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
               (real_mult real_one
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
               (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
               (RealSetoid.real_eq_mult_compat
                  (powb_pow (real_plus real_one (real_opp eta)) O)
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                  real_one
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                  (real_eq_refl real_one) (real_eq_refl
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
               (geodi_mult_one_l (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))).
    + exact (inl (real_lt_plus_r_zero
                    (real_mult (powb_pow (real_plus real_one (real_opp eta)) O)
                       (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                    eps Heps)).
  - (* 归纳步：单步件喂 η·eps，κ 加权，(κ+η)==1 末端收口 *)
    (* 轨道对子消解：IH 先 unfold+revert 使其随对子整体换形为 q 形——          *)
    (*   fold 包装的 IH 与消解后 q 不可转换（变量 m 上 fix 卡死），故证书族    *)
    (*   （范数/Z 正/逐点正）全部以 q/Hq 直供（geodi_seq_norm_pair 等）。      *)
    unfold geodi_iterate, geodi_iterate_pos in IH.
    unfold geodi_iterate, geodi_iterate_pos.
    revert IH.
    cbn [geodi_seq].
    destruct (geodi_seq n r Hr (real_plus real_one (real_opp eta)) p Hp Hn m)
      as [q Hq] eqn:Em.
    intro IH.
    pose proof (geodi_seq_norm_pair n r Hr
                  (real_plus real_one (real_opp eta)) p Hp Hn Hnormp m q Hq Em)
      as HnormQ.
    pose proof (geodi_zpos n r q (real_plus real_one (real_opp eta)) Hr Hq Hn)
      as HZq.
    pose proof (real_mult_positive eta eps Heta Heps) as Hetaeps.
    (* 单步放电件（GeomD 旗舰）实例：KL_{S m} ≤ κ·KL_q + η·eps               *)
    (*   HZ/Hqv 两槽须同字面项：geodi_next_pos 输出类型的 HZ 位烘焙为         *)
    (*   geodi_zpos … Hn，别名假设不可合一（rigid-rigid）。                   *)
    pose proof (geod_policy_iter_kl_geom_step_eps n r q eta Hr Hq
                  Hnormr HnormQ
                  (geodi_zpos n r q (real_plus real_one (real_opp eta)) Hr Hq Hn)
                  (geodi_next_pos n r q (real_plus real_one (real_opp eta))
                     Hr Hq Hn)
                  Heta Hlt1 (real_mult eta eps) Hetaeps) as Hstep.
    (* IH 的 κ 加权：κ·KL_q ≤ κ·(κ^m·KL0 + eps) == κ^{S m}·KL0 + κ·eps *)
    pose proof (geodi_mult_le_compat_l (real_plus real_one (real_opp eta))
                  (geod_lsum n
                     (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i)))
                  (real_plus (real_mult (powb_pow (real_plus real_one (real_opp eta)) m)
                                (geod_lsum n
                                   (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                             eps)
                  (geod_kappa_pos eta Hlt1) IH) as Hmul.
    pose proof (real_le_plus_compat
                  (real_mult (real_plus real_one (real_opp eta))
                     (geod_lsum n
                        (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i))))
                  (real_plus
                     (real_mult
                        (real_mult (real_plus real_one (real_opp eta))
                           (powb_pow (real_plus real_one (real_opp eta)) m))
                        (geod_lsum n
                           (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                     (real_mult (real_plus real_one (real_opp eta)) eps))
                  (real_mult eta eps)
                  (real_mult eta eps)
                  (RealSetoid.real_le_id_r
                     (real_mult (real_plus real_one (real_opp eta))
                        (geod_lsum n
                           (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i))))
                     (real_mult (real_plus real_one (real_opp eta))
                        (real_plus (real_mult (powb_pow (real_plus real_one (real_opp eta)) m)
                                      (geod_lsum n
                                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                                   eps))
                     (real_plus
                        (real_mult
                           (real_mult (real_plus real_one (real_opp eta))
                              (powb_pow (real_plus real_one (real_opp eta)) m))
                           (geod_lsum n
                              (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                        (real_mult (real_plus real_one (real_opp eta)) eps))
                     (real_eq_trans
                        (real_mult (real_plus real_one (real_opp eta))
                           (real_plus (real_mult (powb_pow (real_plus real_one (real_opp eta)) m)
                                         (geod_lsum n
                                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                                      eps))
                        (real_plus
                           (real_mult (real_plus real_one (real_opp eta))
                              (real_mult (powb_pow (real_plus real_one (real_opp eta)) m)
                                 (geod_lsum n
                                    (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                           (real_mult (real_plus real_one (real_opp eta)) eps))
                        (real_plus
                           (real_mult
                              (real_mult (real_plus real_one (real_opp eta))
                                 (powb_pow (real_plus real_one (real_opp eta)) m))
                              (geod_lsum n
                                 (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                           (real_mult (real_plus real_one (real_opp eta)) eps))
                        (real_distrib (real_plus real_one (real_opp eta))
                           (real_mult (powb_pow (real_plus real_one (real_opp eta)) m)
                              (geod_lsum n
                                 (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                           eps)
                        (RealSetoid.real_eq_plus_compat
                           (real_mult (real_plus real_one (real_opp eta))
                              (real_mult (powb_pow (real_plus real_one (real_opp eta)) m)
                                 (geod_lsum n
                                    (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                           (real_mult (real_plus real_one (real_opp eta)) eps)
                           (real_mult
                              (real_mult (real_plus real_one (real_opp eta))
                                 (powb_pow (real_plus real_one (real_opp eta)) m))
                              (geod_lsum n
                                 (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                           (real_mult (real_plus real_one (real_opp eta)) eps)
                           (real_mult_assoc (real_plus real_one (real_opp eta))
                              (powb_pow (real_plus real_one (real_opp eta)) m)
                              (geod_lsum n
                                 (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                           (real_eq_refl
                              (real_mult (real_plus real_one (real_opp eta)) eps))))
                     Hmul)
                  (real_le_refl (real_mult eta eps))) as Hmid.
    (* 末端收口：(A + κ·eps) + η·eps == A + (κ+η)·eps == A + 1·eps == A + eps *)
    assert (Hcollapse : real_eq
      (real_plus (real_plus (real_mult
                   (real_mult (real_plus real_one (real_opp eta))
                      (powb_pow (real_plus real_one (real_opp eta)) m))
                   (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                (real_mult (real_plus real_one (real_opp eta)) eps))
             (real_mult eta eps))
      (real_plus (real_mult
               (real_mult (real_plus real_one (real_opp eta))
                  (powb_pow (real_plus real_one (real_opp eta)) m))
               (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
             eps)).
    { apply (real_eq_trans _
               (real_plus
                  (real_mult
                     (real_mult (real_plus real_one (real_opp eta))
                        (powb_pow (real_plus real_one (real_opp eta)) m))
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                  (real_plus (real_mult (real_plus real_one (real_opp eta)) eps)
                             (real_mult eta eps)))).
      - apply real_eq_sym. apply real_plus_assoc.
      - apply (RealSetoid.real_eq_plus_compat
                 (real_mult
                    (real_mult (real_plus real_one (real_opp eta))
                       (powb_pow (real_plus real_one (real_opp eta)) m))
                    (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                 (real_plus (real_mult (real_plus real_one (real_opp eta)) eps)
                            (real_mult eta eps))
                 (real_mult
                    (real_mult (real_plus real_one (real_opp eta))
                       (powb_pow (real_plus real_one (real_opp eta)) m))
                    (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                 eps).
        + apply real_eq_refl.
        + (* κ·eps + η·eps == (κ+η)·eps == 1·eps == eps（distrib 翻面，E406） *)
          apply (real_eq_trans _
                     (real_plus (real_mult eps (real_plus real_one (real_opp eta)))
                                (real_mult eps eta))).
          * apply (RealSetoid.real_eq_plus_compat
                     (real_mult (real_plus real_one (real_opp eta)) eps)
                     (real_mult eta eps)
                     (real_mult eps (real_plus real_one (real_opp eta)))
                     (real_mult eps eta)
                     (real_mult_comm (real_plus real_one (real_opp eta)) eps)
                     (real_mult_comm eta eps)).
          * apply (real_eq_trans _
                       (real_mult eps (real_plus (real_plus real_one (real_opp eta)) eta))).
          -- apply real_eq_sym. apply real_distrib.
          -- apply (real_eq_trans _
                         (real_mult eps real_one)).
             ++ apply (RealSetoid.real_eq_mult_compat eps
                         (real_plus (real_plus real_one (real_opp eta)) eta) eps real_one
                         (real_eq_refl eps) (geodi_kappa_plus_eta eta)).
             ++ apply real_mult_one. }
    exact (real_le_trans _ _ _ Hstep
             (real_le_trans _ _ _ Hmid
                (RealSetoid.real_le_id_l
                   (real_plus
                      (real_plus
                         (real_mult
                            (real_mult (real_plus real_one (real_opp eta))
                               (powb_pow (real_plus real_one (real_opp eta)) m))
                            (geod_lsum n
                               (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                         (real_mult (real_plus real_one (real_opp eta)) eps))
                      (real_mult eta eps))
                   (real_plus
                      (real_mult
                         (real_mult (real_plus real_one (real_opp eta))
                            (powb_pow (real_plus real_one (real_opp eta)) m))
                         (geod_lsum n
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                      eps)
                   (real_plus
                      (real_mult
                         (real_mult (real_plus real_one (real_opp eta))
                            (powb_pow (real_plus real_one (real_opp eta)) m))
                         (geod_lsum n
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                      eps)
                   Hcollapse (real_le_refl
                      (real_plus
                         (real_mult
                            (real_mult (real_plus real_one (real_opp eta))
                               (powb_pow (real_plus real_one (real_opp eta)) m))
                            (geod_lsum n
                               (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                         eps))))).
Qed.

(* ============================================================ *)
(* G. 分层保底阶梯：一步件 / 两步件（主件实例，幂字面收口）               *)
(* ============================================================ *)
Theorem geodi_iter_one_step_eps :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n),
  forall (eps : Real) (Heps : real_lt real_zero eps),
  real_le
    (geod_lsum n
       (fun i : nat => real_kl_term (r i)
                       (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S O) i)
                       (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S O) i)))
    (real_plus (real_mult (real_plus real_one (real_opp eta))
                   (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
               eps).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn eps Heps.
  pose proof (geodi_policy_iter_kl_geom_iter_eps n r Hr eta Heta Hlt1 p Hp
                Hnormr Hnormp Hn (Datatypes.S O) eps Heps) as H.
  apply (RealSetoid.real_le_id_r
           (geod_lsum n
              (fun i : nat => real_kl_term (r i)
                              (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S O) i)
                              (Hr i)
                              (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S O) i)))
           (real_plus
              (real_mult (powb_pow (real_plus real_one (real_opp eta)) (Datatypes.S O))
                 (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
              eps)
           (real_plus (real_mult (real_plus real_one (real_opp eta))
                         (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                      eps)).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult (powb_pow (real_plus real_one (real_opp eta)) (Datatypes.S O))
                (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
             eps
             (real_mult (real_plus real_one (real_opp eta))
                (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
             eps).
    + (* κ^1·KL0 == κ·KL0：κ^1 ≡ κ·1（转换），assoc + mult_one 换形 *)
      exact (real_eq_trans
               (real_mult (powb_pow (real_plus real_one (real_opp eta)) (Datatypes.S O))
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
               (real_mult (real_mult (real_plus real_one (real_opp eta)) real_one)
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
               (real_mult (real_plus real_one (real_opp eta))
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
               (real_eq_refl
                  (real_mult (real_mult (real_plus real_one (real_opp eta)) real_one)
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
               (real_eq_trans
                  (real_mult (real_mult (real_plus real_one (real_opp eta)) real_one)
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                  (real_mult (real_plus real_one (real_opp eta))
                     (real_mult real_one
                        (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                  (real_mult (real_plus real_one (real_opp eta))
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                  (real_eq_sym _ _
                     (real_mult_assoc (real_plus real_one (real_opp eta)) real_one
                        (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                  (RealSetoid.real_eq_mult_compat
                     (real_plus real_one (real_opp eta))
                     (real_mult real_one
                        (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                     (real_plus real_one (real_opp eta))
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                     (real_eq_refl (real_plus real_one (real_opp eta)))
                     (geodi_mult_one_l (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))))).
    + apply real_eq_refl.
  - (* real_le 槽：恰为主件 t := S O 实例 H *)
    exact H.
Qed.

Theorem geodi_iter_two_steps_eps :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n),
  forall (eps : Real) (Heps : real_lt real_zero eps),
  real_le
    (geod_lsum n
       (fun i : nat => real_kl_term (r i)
                       (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S (Datatypes.S O)) i)
                       (Hr i)
                       (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S (Datatypes.S O)) i)))
    (real_plus (real_mult (real_plus real_one (real_opp eta))
                   (real_mult (real_plus real_one (real_opp eta))
                      (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
               eps).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn eps Heps.
  pose proof (geodi_policy_iter_kl_geom_iter_eps n r Hr eta Heta Hlt1 p Hp
                Hnormr Hnormp Hn (Datatypes.S (Datatypes.S O)) eps Heps) as H.
  apply (RealSetoid.real_le_id_r
           (geod_lsum n
              (fun i : nat => real_kl_term (r i)
                              (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S (Datatypes.S O)) i)
                              (Hr i)
                              (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S (Datatypes.S O)) i)))
           (real_plus
              (real_mult (powb_pow (real_plus real_one (real_opp eta))
                             (Datatypes.S (Datatypes.S O)))
                 (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
              eps)
           (real_plus (real_mult (real_plus real_one (real_opp eta))
                         (real_mult (real_plus real_one (real_opp eta))
                            (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                      eps)).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult (powb_pow (real_plus real_one (real_opp eta))
                           (Datatypes.S (Datatypes.S O)))
                (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
             eps
             (real_mult (real_plus real_one (real_opp eta))
                (real_mult (real_plus real_one (real_opp eta))
                   (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
             eps).
    + (* κ²·KL0 == κ·(κ·KL0)：κ² ≡ κ·(κ·1)（转换），assoc 两次 + mult_one *)
      exact (real_eq_trans
               (real_mult (powb_pow (real_plus real_one (real_opp eta))
                             (Datatypes.S (Datatypes.S O)))
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
               (real_mult
                  (real_mult (real_plus real_one (real_opp eta))
                     (real_mult (real_plus real_one (real_opp eta)) real_one))
                  (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
               (real_mult (real_plus real_one (real_opp eta))
                  (real_mult (real_plus real_one (real_opp eta))
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
               (real_eq_refl
                  (real_mult
                     (real_mult (real_plus real_one (real_opp eta))
                        (real_mult (real_plus real_one (real_opp eta)) real_one))
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
               (real_eq_trans
                  (real_mult
                     (real_mult (real_plus real_one (real_opp eta))
                        (real_mult (real_plus real_one (real_opp eta)) real_one))
                     (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                  (real_mult (real_plus real_one (real_opp eta))
                     (real_mult (real_mult (real_plus real_one (real_opp eta)) real_one)
                        (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                  (real_mult (real_plus real_one (real_opp eta))
                     (real_mult (real_plus real_one (real_opp eta))
                        (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                  (real_eq_sym _ _
                     (real_mult_assoc (real_plus real_one (real_opp eta))
                        (real_mult (real_plus real_one (real_opp eta)) real_one)
                        (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                  (RealSetoid.real_eq_mult_compat
                     (real_plus real_one (real_opp eta))
                     (real_mult (real_mult (real_plus real_one (real_opp eta)) real_one)
                        (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                     (real_plus real_one (real_opp eta))
                     (real_mult (real_plus real_one (real_opp eta))
                        (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                     (real_eq_refl (real_plus real_one (real_opp eta)))
                     (real_eq_trans
                        (real_mult (real_mult (real_plus real_one (real_opp eta)) real_one)
                           (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                        (real_mult (real_plus real_one (real_opp eta))
                           (real_mult real_one
                              (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                        (real_mult (real_plus real_one (real_opp eta))
                           (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                        (real_eq_sym _ _
                           (real_mult_assoc (real_plus real_one (real_opp eta)) real_one
                              (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                        (RealSetoid.real_eq_mult_compat
                           (real_plus real_one (real_opp eta))
                           (real_mult real_one
                              (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                           (real_plus real_one (real_opp eta))
                           (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                           (real_eq_refl (real_plus real_one (real_opp eta)))
                           (geodi_mult_one_l (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))))))).
    + apply real_eq_refl.
  - (* real_le 槽：恰为主件 t := S (S O) 实例 H *)
    exact H.
Qed.

(* ============================================================ *)
(* H. Bishop 伴件：KL(π*‖π_t) ≤_B (1−η)^t·KL(π*‖π_0)（B 线语言收口）      *)
(* ============================================================ *)
Theorem geodi_policy_iter_kl_geom_iter_B :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n) (t : nat),
  real_le_b
    (geod_lsum n
       (fun i : nat => real_kl_term (r i)
                       (geodi_iterate n r Hr eta p Hp Hn t i)
                       (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
    (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
               (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn t.
  (* B 收口（UpRealLeB real_le_closure_b_one，D:=1 特化）：主件本就是       *)
  (*   ∀eps>0 的 real_le X (Y+eps) 族——恰为收口引理前提形，直喂即闭合。     *)
  apply (real_le_closure_b_one
           (geod_lsum n
              (fun i : nat => real_kl_term (r i)
                              (geodi_iterate n r Hr eta p Hp Hn t i)
                              (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
           (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
              (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))).
  intros eps Heps.
  exact (geodi_policy_iter_kl_geom_iter_eps n r Hr eta Heta Hlt1 p Hp
           Hnormr Hnormp Hn t eps Heps).
Qed.

(* ============================================================ *)
(* I. KL Bishop 非负伴件（判词 I4 的可用侧标记）：0 ≤_B KL(π*‖π_0)        *)
(*   证书链：gibbs 逐 eps（le 形）→ le_b 半量抬升 → assoc+半量机换形。    *)
(* ============================================================ *)
Lemma geodi_kl_nonneg_B : forall (n : nat) (r p : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one),
  real_le_b real_zero
    (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))).
Proof.
  intros n r p Hr Hp Hnormr Hnormp. unfold real_le_b. intros eps Heps.
  pose proof (real_plus_positive real_one real_one
                real_lt_zero_one real_lt_zero_one) as Htwo.
  pose proof (real_inv_pos_pos (real_plus real_one real_one) Htwo) as Hinv.
  pose proof (real_mult_positive eps
                (real_inv_pos (real_plus real_one real_one) Htwo) Heps Hinv) as Hh.
  pose proof (real_le_to_le_b real_zero
                (real_plus (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                           (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)))
                (real_gibbs_inequality_eps nat (seq 0 n) r p Hr Hp Hnormr Hnormp
                   (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)) Hh)) as Hleb.
  apply (RealSetoid.real_lt_id_r real_zero
           (real_plus
              (real_plus (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                         (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)))
              (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)))
           (real_plus (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))) eps)).
  - apply (real_eq_trans
             (real_plus
                (real_plus (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                           (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)))
                (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)))
             (real_plus (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
                        (real_plus
                           (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo))
                           (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)))))
     .
    + apply real_eq_sym. apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat
               (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
               (real_plus
                  (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo))
                  (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)))
               (geod_lsum n (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i)))
               eps).
      * apply real_eq_refl.
      * exact (geod_b_half_double eps (real_inv_pos (real_plus real_one real_one) Htwo)
                  (real_inv_pos_correct (real_plus real_one real_one) Htwo)).
  - exact (Hleb (real_mult eps (real_inv_pos (real_plus real_one real_one) Htwo)) Hh).
Qed.

(* ============================================================ *)
(* 尾注：诚实台账                                                        *)
(* 【判词 I4 精确差距】「t ≤ t1 ⟹ KL_{t1} ≤ κ^t·KL_0（B 形）」合成件：    *)
(*   有 ①KL_{t1} ≤_B κ^{t1}·KL_0（主件 B 伴件）②0 ≤_B KL_0（伴件 I）     *)
(*   ③κ^{t1} ≤_B κ^t（PowB powb_one_minus_eta_mono_dec）。缺④le_b 乘法   *)
(*   保序闭包：a ≤_B b ∧ 0 ≤_B c ⟹ a·c ≤_B b·c——其逐 eps 证需把           *)
(*   κ^{t1} ≤ κ^t+δ 的 δ 乘出后压回 eps，即需 KL_0 上界（sup KL）材料；   *)
(*   单纯形上 sup KL 可由 min 正性给出，但库内无该上界件——④挂账未建，    *)
(*   缺口的准确形状如上，禁硬凑（分层保底纪律②）。                        *)
(* 【机器状态】四关证据：G1 禁词全零；G2 EXIT=0 + 主件族 Print            *)
(*   Assumptions 全 Closed（见文末逐件）；G3 提取探针 Obj.magic=0；        *)
(*   G4 coqchk 9.0 全路径通过（log 见 _gdi_* 序列）。                     *)
(* ============================================================ *)

Print Assumptions geodi_zpos.
Print Assumptions geodi_step_norm.
Print Assumptions geodi_seq_norm.
Print Assumptions geodi_mult_le_compat_l.
Print Assumptions geodi_policy_iter_kl_geom_iter_eps.
Print Assumptions geodi_iter_one_step_eps.
Print Assumptions geodi_iter_two_steps_eps.
Print Assumptions geodi_policy_iter_kl_geom_iter_B.
Print Assumptions geodi_kl_nonneg_B.
