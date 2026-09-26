(* UpReqStrictStepGen.v —— 严格步生成器族。                      *) (* 使命： 本件形式化 eps 拆分惯用法的接口级命名引理族：半量/季量  *)
(*   常数 h := real_const (1#2)、q := real_const (1#4) 的序与乘法 *) (*   严格步（库内 Q 层 eps/2、eps/4 内联惯用法的 Real 层命名件）。*)
(* 依赖： CW_ConstructiveWorld_219（S02/S07 导出面）。独立件，    *) (*   与 UpReqRealLtShiftBridge 互补：彼件供 Or 分解升温/平移桥，  *)
(*   本件供常数乘子严格步，零相互 Require。                      *) (* 构造性： Set 层语句（real_lt/real_eq）；全 Qed 闭合；零假设位； *)
(*   全显式项组装，可提取。                                      *) (* 编译配方： 9.1 直调（toolchain env.sh 同源）、cpu_guard 绑核。  *)
(* 验收面：G1 禁词为零；G2 全量编译通过；G3 提取面全 Set/Prop 桥  *) (*   零计算内容，以说明替代提取检验；G4 假设闭包检验 + coqchk。   *)
(* 对标： mathlib 的半量拆分恒等式（half_add）与常数严格序层；    *) (*   本库自建于柯西实数层。                                      *)
(* 件表： ssg_eq_const_plus（助记）/ ssg_lt_mul_one（参数化源）    *)
(*   / ssg_half_lt / ssg_lt_mul_one_l（实例与左乘副本）/          *)
(*   ssg_half_add（拆分恒等式）/ ssg_half_quarter_eps_lt（终局    *)
(*   主定理）/ ssg_h_lt_one / ssg_q_lt_h / ssg_q_lt_one /         *)
(*   …/ ssg_quarter_eps_lt / ssg_half_eps_lt（标准严格链）。       *)
(* 常数与设计：h := real_const (1#2)、q := real_const (1#4)。      *)
(* ①参数化源：ssg_lt_mul_one : c<1 -> 0<p -> p·c < p              *)
(*   （real_lt_mult_compat 左乘形 + 换形；实例 ssg_half_lt：      *)
(*    p·(1/2) < p，即 p/2<p）。                                   *)
(* ②拆分恒等式：ssg_half_add : p·(1/2) + p·(1/2) == p             *)
(*   （①的严格步组合基础：real_distrib + 常数和 + mult_one）。    *)
(* ③终局主定理：ssg_half_quarter_eps_lt :                        *)
(*   0<eps -> (1/2)·eps + (1/4)·eps < eps。                      *)
(*   （SCFIX 认定的终局严格步依存形参数化；路线 h·e + q·e ==     *)
(*    e·h + e·q == e·(h+q) < e·one == e，(h+q)==3/4 与 3/4<1      *)
(*    的常数链 + 乘法保序。）                                     *)
(* ④标准严格链：ssg_h_lt_one / ssg_q_lt_one /                    *)
(*   ssg_quarter_eps_lt / ssg_half_eps_lt                        *)
(*   （0<1 经 const 序 + 乘法保序组合的即用严格步）。             *)
(* 助记：ssg_eq_const_plus——常数和逐点恒等式（逐点差为零统一      *)
(*   模式：real_eq_of_zero_diff 入手 + 逐点计算闭合）。           *)
(* 独立性：本件与 UpReqRealLtShiftBridge 零相互 Require；         *)
(*   ssg_ 前缀库内独占，防同名。                                  *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.

(* ============ 常数乘子（Q 层 eps 拆分惯用法的 Real 载体化） ============ *)
Definition ssg_h : Real := real_const (1#2)%Q.
Definition ssg_q : Real := real_const (1#4)%Q.

(* ============ 助记：常数加法/常数幺（逐点差为零统一模式） ============ *)
Lemma ssg_eq_const_plus : forall c d : Q,
  real_eq (real_plus (real_const c) (real_const d)) (real_const (c + d)%Q).
Proof.
  intros c d.
  apply real_eq_of_zero_diff.
  intro n.
  simpl.
  ring.
Qed.

(* ============ ④链基：常数序（1/4 < 1/2 < 1、正性） ============ *)
Lemma ssg_h_lt_one : real_lt ssg_h real_one.
Proof.
  apply (real_const_lt (1#2)%Q 1%Q).
  compute.
  reflexivity.
Qed.

Lemma ssg_q_lt_h : real_lt ssg_q ssg_h.
Proof.
  apply (real_const_lt (1#4)%Q (1#2)%Q).
  compute.
  reflexivity.
Qed.

Lemma ssg_q_lt_one : real_lt ssg_q real_one.
Proof.
  apply (real_lt_trans ssg_q ssg_h real_one ssg_q_lt_h ssg_h_lt_one).
Qed.

Lemma ssg_zero_lt_h : real_lt real_zero ssg_h.
Proof.
  apply real_const_pos.
  apply Qlt_to_QltT.
  compute.
  reflexivity.
Qed.

Lemma ssg_zero_lt_q : real_lt real_zero ssg_q.
Proof.
  apply real_const_pos.
  apply Qlt_to_QltT.
  compute.
  reflexivity.
Qed.

(* ============ ① 参数化源模块：严格乘幺消去 p·c < p ============ *)
(* c<1、0<p ⟹ p·c < p·1 == p（real_lt_mult_compat 左乘形 + 换形） *)
Lemma ssg_lt_mul_one : forall c p : Real,
  real_lt c real_one -> real_lt real_zero p ->
  real_lt (real_mult p c) p.
Proof.
  intros c p Hc Hp.
  apply (RealSetoid.real_lt_id_r (real_mult p c) (real_mult p real_one) p           (real_mult_one p)).
  exact (real_lt_mult_compat c real_one p Hp Hc).
Qed.

(* —— ①实例：p/2 < p（半量严格小于） —— *)
Lemma ssg_half_lt : forall p : Real,
  real_lt real_zero p -> real_lt (real_mult p ssg_h) p.
Proof.
  intros p Hp.
  exact (ssg_lt_mul_one ssg_h p ssg_h_lt_one Hp).
Qed.

(* —— ①左乘副本：c·p < p（c<1、0<p） —— *)
Lemma ssg_lt_mul_one_l : forall c p : Real,
  real_lt c real_one -> real_lt real_zero p ->
  real_lt (real_mult c p) p.
Proof.
  intros c p Hc Hp.
  apply (RealSetoid.real_lt_id_r (real_mult c p)
           (real_mult real_one p) p).
  - exact (real_eq_trans (real_mult real_one p)
             (real_mult p real_one) p
             (real_mult_comm real_one p) (real_mult_one p)).
  - exact (real_mult_lt_compat c real_one p Hc Hp).
Qed.

(* ============ ② 拆分恒等式：p/2 + p/2 == p ============ *)
(* 半和常数 (1/2)+(1/2) 经 Q 层 Qeq 与幺逐点重合。                   *)
Lemma ssg_half_add : forall p : Real,
  real_eq (real_plus (real_mult p ssg_h) (real_mult p ssg_h)) p.
Proof.
  intros p.
  assert (Hhh : real_eq (real_plus ssg_h ssg_h) real_one).
  { apply (real_eq_trans (real_plus ssg_h ssg_h)
             (real_const ((1#2)%Q + (1#2)%Q)%Q) real_one).
    - exact (ssg_eq_const_plus (1#2)%Q (1#2)%Q).
    - apply real_eq_of_zero_diff.
      intro n.
      simpl.
      ring. }
  apply (real_eq_trans
           (real_plus (real_mult p ssg_h) (real_mult p ssg_h))
           (real_mult p real_one) p).
  - apply (real_eq_trans
             (real_plus (real_mult p ssg_h) (real_mult p ssg_h))
             (real_mult p (real_plus ssg_h ssg_h))
             (real_mult p real_one)).
    + exact (real_eq_sym (real_mult p (real_plus ssg_h ssg_h))
               (real_plus (real_mult p ssg_h) (real_mult p ssg_h))
               (real_distrib p ssg_h ssg_h)).
    + exact (RealSetoid.real_eq_mult_compat p
               (real_plus ssg_h ssg_h) p real_one
               (real_eq_refl p) Hhh).
  - exact (real_mult_one p).
Qed.

(* ============ ③ 终局母定理：half·eps + qrt·eps < eps ============ *)
(* SCFIX 认定的依存形参数化。路线：                                *)
(*   h·e + q·e == e·h + e·q == e·(h+q) < e·one == e                *)
(*   （(h+q)==3/4 与 3/4<1 的常数链 + 乘法保序）。                  *)
Lemma ssg_half_quarter_eps_lt : forall eps : Real,
  real_lt real_zero eps ->
  real_lt (real_plus (real_mult ssg_h eps) (real_mult ssg_q eps)) eps.
Proof.
  intros eps Heps.
  assert (Hhq : real_lt (real_plus ssg_h ssg_q) real_one).
  { apply (RealSetoid.real_lt_id_l (real_plus ssg_h ssg_q)
             (real_const ((1#2)%Q + (1#4)%Q)%Q) real_one
             (ssg_eq_const_plus (1#2)%Q (1#4)%Q)).
    apply (real_const_lt ((1#2)%Q + (1#4)%Q)%Q 1%Q).
    compute.
    reflexivity. }
  assert (Hre : real_eq (real_plus (real_mult ssg_h eps) (real_mult ssg_q eps))
                        (real_mult eps (real_plus ssg_h ssg_q))).
  { apply (real_eq_trans
             (real_plus (real_mult ssg_h eps) (real_mult ssg_q eps))
             (real_plus (real_mult eps ssg_h) (real_mult eps ssg_q))
             (real_mult eps (real_plus ssg_h ssg_q))).
    - exact (RealSetoid.real_eq_plus_compat
               (real_mult ssg_h eps) (real_mult ssg_q eps)
               (real_mult eps ssg_h) (real_mult eps ssg_q)
               (real_mult_comm ssg_h eps) (real_mult_comm ssg_q eps)).
    - exact (real_eq_sym
               (real_mult eps (real_plus ssg_h ssg_q))
               (real_plus (real_mult eps ssg_h) (real_mult eps ssg_q))
               (real_distrib eps ssg_h ssg_q)). }
  apply (RealSetoid.real_lt_id_l
           (real_plus (real_mult ssg_h eps) (real_mult ssg_q eps))
           (real_mult eps (real_plus ssg_h ssg_q)) eps Hre).
  apply (RealSetoid.real_lt_id_r
           (real_mult eps (real_plus ssg_h ssg_q))
           (real_mult eps real_one) eps
           (real_mult_one eps)).
  exact (real_mult_lt_compat_l (real_plus ssg_h ssg_q) real_one eps
           Hhq Heps).
Qed.

(* ============ ④ 标准严格链（即用严格步） ============ *)
(* q·eps < eps：季量乘幺消去（0<1 → q<1/2<1 链 + ①源模块）            *)
Lemma ssg_quarter_eps_lt : forall eps : Real,
  real_lt real_zero eps -> real_lt (real_mult ssg_q eps) eps.
Proof.
  intros eps Heps.
  exact (ssg_lt_mul_one_l ssg_q eps ssg_q_lt_one Heps).
Qed.

(* h·eps < eps：半量同构（①源模块实例于 c:=h）                         *)
Lemma ssg_half_eps_lt : forall eps : Real,
  real_lt real_zero eps -> real_lt (real_mult ssg_h eps) eps.
Proof.
  intros eps Heps.
  exact (ssg_lt_mul_one_l ssg_h eps ssg_h_lt_one Heps).
Qed.

(* ============ 关卡 G4：假设闭包检验（八件全 Closed 为过关判据） ==== *)
Print Assumptions ssg_eq_const_plus.
Print Assumptions ssg_lt_mul_one.
Print Assumptions ssg_half_lt.
Print Assumptions ssg_lt_mul_one_l.
Print Assumptions ssg_half_add.
Print Assumptions ssg_half_quarter_eps_lt.
Print Assumptions ssg_quarter_eps_lt.
Print Assumptions ssg_half_eps_lt.
