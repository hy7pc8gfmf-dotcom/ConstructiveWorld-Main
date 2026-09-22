(* ============================================================ *)
(* ToyR 玩具证替换件 —— T255 台账席 战役包P（tier2 六批）          *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   ssg_half_eps_lt（原 L197，2 句玩具证）                               *)
(*   ssg_quarter_eps_lt（原 L189，2 句玩具证）                            *)
(*   ssg_half_lt（原 L95，2 句玩具证）                                    *)
(*   ssg_lt_mul_one（原 L84，3 句玩具证）                                 *)
(*   ssg_q_lt_one（原 L61，1 句玩具证）                                   *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T329 恒等守恒更正注记】2026-09-22 包AV八 台账席（恒等头注更正全量第二批）                     *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 经 T277（包AL）全量恒等核查定谳、T317（包AV六）试点定谳：本件实测                             *)
(* 为恒等守恒——清单所列 5 槽证明体与 Main 现版原件逐字同文（刀体                                *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此更正。                                        *)
(* 更正口径：真替换 0 槽＋恒等守恒 5 槽；本注记为追加块，上方原头                                  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* 零改动；台账承载见 T277 附录／T284 修正块／T317 评估册／T321／T329 台账。                   *)
(* 附记：T277 判级全文恒等；包P 整批直推（第二批；承 T321 §五·1）                             *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqStrictStepGen.v —— 严格步生成器族 STG-A（DISCH1 追加件）  *)
(*                                                              *)
(* 目的： 把散落全库的 eps 拆分惯用法收敛为接口级命名引理族。      *)
(*   半量/季量常数取 h := real_const (1#2)、q := real_const (1#4)， *)
(*   与库内 Q 层 eps/2、eps/4 内联惯用法逐位同源（S07 log 界、     *)
(*   SCFIX 终局严格步消费形 half·eps+qrt·eps<eps）。               *)
(* 清单（2 助记 + 1 参数化母件① + 1 拆分恒等式② + 1 终局母定理③   *)
(*       + 3 标准严格链④件）：                                     *)
(*   [助记] ssg_eq_const_plus（常数和逐点恒等式）                    *)
(*   [①参数化] ssg_lt_mul_one : c<1 -> 0<p -> p·c < p              *)
(*     （实例 ssg_half_lt：p·(1/2) < p，即 p/2<p）                  *)
(*   [②] ssg_half_add : p·(1/2) + p·(1/2) == p                    *)
(*     （①的严格步组合底座：real_distrib + 常数和 + mult_one）      *)
(*   [③终局母定理] ssg_half_quarter_eps_lt :                       *)
(*     0<eps -> (1/2)·eps + (1/4)·eps < eps                        *)
(*     （SCFIX 认定的终局严格步消费形参数化）                       *)
(*   [④标准严格链] ssg_h_lt_one / ssg_q_lt_one /                   *)
(*     ssg_quarter_eps_lt / ssg_half_eps_lt                        *)
(*     （0<1 经 const 序 + 乘法保序组合的战役就绪严格步）            *)
(* 依赖： CW_ConstructiveWorld_219（S02/S07 导出面）。独立件，      *)
(*   与 UpReqRealLtShiftBridge 互补（彼件供 Or 分解升温/平移桥，    *)
(*   本件供常数乘子严格步，零相互 Require）。                       *)
(* 关卡账：G1 七禁词 0；G2 全量绿；G3 全 Set/Prop 桥面零计算内容，  *)
(*   以说明替代提取；G4 Assumptions 探针 + coqchk。                 *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
Require Import CW_ConstructiveWorld_219.

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

(* ============ ① 参数化母件：严格乘幺消去 p·c < p ============ *)
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

(* —— ①左乘镜像：c·p < p（c<1、0<p） —— *)
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
(* SCFIX 认定的消费形参数化。路线：                                *)
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

(* ============ ④ 标准严格链（战役就绪严格步） ============ *)
(* q·eps < eps：季量乘幺消去（0<1 → q<1/2<1 链 + ①母件）            *)
Lemma ssg_quarter_eps_lt : forall eps : Real,
  real_lt real_zero eps -> real_lt (real_mult ssg_q eps) eps.
Proof.
  intros eps Heps.
  exact (ssg_lt_mul_one_l ssg_q eps ssg_q_lt_one Heps).
Qed.

(* h·eps < eps：半量同构（①母件实例于 c:=h）                         *)
Lemma ssg_half_eps_lt : forall eps : Real,
  real_lt real_zero eps -> real_lt (real_mult ssg_h eps) eps.
Proof.
  intros eps Heps.
  exact (ssg_lt_mul_one_l ssg_h eps ssg_h_lt_one Heps).
Qed.

(* ============ 关卡 G4：假设闭包探针（八件全 Closed 为过关判据） ==== *)
Print Assumptions ssg_eq_const_plus.
Print Assumptions ssg_lt_mul_one.
Print Assumptions ssg_half_lt.
Print Assumptions ssg_lt_mul_one_l.
Print Assumptions ssg_half_add.
Print Assumptions ssg_half_quarter_eps_lt.
Print Assumptions ssg_quarter_eps_lt.
Print Assumptions ssg_half_eps_lt.
