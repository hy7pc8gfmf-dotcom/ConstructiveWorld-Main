(* ============================================================ *)
(* 玩具证替换件（消融落件）——替换面清单见下 *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   real_minus_r_compat（原 L144，3 句玩具证）                           *)
(* ============================================================ *)
(* ============================================================ *)
(* 上方头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经全量 *)
(* 恒等核查与试点复核：本件实测为恒等守恒——清单所列 1 参数位证明体与 *)
(* Main 现版原件逐字同文（刀体＝原体，零变化），头注「替换」声称与实物 *)
(* Require 面零改动；头注过程流水词面已作中性化处理。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqTrainingEquiv.v *)
(* *)
(* 目的： 定理 4.10 training_equivalence 的 Real 层构造。 *)
(* 主件： real_training_equivalence 与 real_cross_entropy_decomp 交叉熵分解。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： KL 项展开为构造核；训练等价性取显式恒等式形。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqTrainingEquiv.v —— 定理 4.10 training_equivalence *)

(* ------------------------------------------------------------------ *)
(* 【强度定稿注记（判定 C10 之 Real 层兑现）】                     *)
(*   ① Id 层为序档：training_equivalence @ S04_RealExpLogConv.v L4869   *)
(*     （S04_CauchyComplete.v 即本模块，L4869 实测在盘）。   *)
(*   ② 库内实义 = 「交叉熵下降 ⟹ KL 下降（固定目标 p）」——            *)
(*     交叉熵↔KL 单调对偶；**非**字面「ELBO=自由能」。                  *)
(*     【措辞差登记】论文叙述若作「ELBO=自由能」措辞，与库内声明        *)
(*     （交叉熵-相对熵-熵恒等式 cross_entropy_decomp @S04 L4306 +       *)
(*     修正；req 对位 req_training_equivalence @UpReqDist.v L2578       *)
(*   ③ Real 层形态 = real_le 版同一陈述（零缩水）：                     *)
(*     real_cross_entropy(p,q2) ≤ real_cross_entropy(p,q1) ⟹           *)
(*     Σ kl_term(p,q2) ≤ Σ kl_term(p,q1)。                              *)
(* ------------------------------------------------------------------ *)
(* 【组装链结构图（各步引用件名）】                                     *)
(*   第 0 件 定义件：real_cross_entropy（p·(−log q) 逐点和，            *)

(*     证人 Hq 前移——UpReqTempDefs real_entropy_dist 同位先例）。       *)
(*   第 1 件 局部序代数四小件（全 S02/S07/S08 基元拼装，零新数学）：    *)
(*     a. real_plus_opp_cancel_mid：(−x)+(x+y) ≡ y                      *)
(*        = real_plus_assoc + real_plus_opp + real_plus_comm/zero       *)
(*     b. real_plus_minus_r_cancel：a+(b+(−a)) ≡ b                      *)
(*        （Id minus_plus_cancel 副本；同 a 件基元）                    *)
(*     c. real_minus_r_compat：差分双侧换形                             *)
(*        = RealSetoid.real_eq_plus_compat + real_eq_opp_compat         *)
(*     d. real_minus_r_plus_common：共同被加项消去                      *)
(*        （Id minus_plus_common_local @S04 L4849 副本）                *)
(*        = real_opp_plus + S08 real_plus_swap_mid + real_plus_opp      *)
(*          + zero 群                                                   *)
(*   第 2 件 kl 项逐点展开桥：real_kl_term_expand                      *)

(*     = real_log_mult（S07 L7845）+ real_log_inv_pos_opp（本件：       *)

(*       real_log_one + real_one_pos_local（S13）+ a 件）+              *)
(*       real_opp_plus + real_opp_opp（S08 L95）+ 交换群。              *)
(*   第 3 件 分解件：real_cross_entropy_decomp（real_eq 恒等式）        *)
(*     CE(p,q) ≡ Ent(p) + Σ kl_term(p,q)                                *)
(*     按 S08 real_kl_sum_decomp（L2526）同族组装：逐点（a 件抵消链    *)
(*     + real_distrib）→ real_list_sum_ext（S08 L284，X 显式首参）      *)
(*     → real_list_sum_add（S08 L329）→ ext 换 kl 桥。                  *)
(*   第 4 件 主件完成：real_training_equivalence（real_le 四步法）      *)
(*     ① 差分非负：0 ≤ CE1−CE2 = S13 real_le_minus_nonneg_aux          *)
(*       （L3293，Or 两支均构造性消去，无排中 leakage——N1 实证）        *)
(*     ② 差分恒等：real_minus_r_compat + d 件（第 3 件传参位）            *)
(*     ③ 运输：RealSetoid.real_le_id_r（S07 L461）                      *)
(*     ④ 完成：S13 real_le_plus_nonneg_r_aux（L3283）+ b 件。           *)
(*   同源参照：rfep_rlhf_free_energy_kl @UpReqRealFEP L1079（任意 π*    *)
(*   版分解，定理 4.7 同源；本件固定目标 p 即其 q 位特化读法）。        *)
(* ------------------------------------------------------------------ *)
(* 【诚实申报】本件为序档组装件（非新数学）：分解恒等式的数学内容 =    *)
(*   Id cross_entropy_decomp（S04 L4306）与 S08 real_kl_sum_decomp     *)
(*   同族；序完成四步全为 S02/S07/S13 在盘序件拼装；本件增量 =          *)
(*   list 载体实例化（T7 UpReqMinFreeEps 同款）+ real_minus_r 载体上   *)
(*   的差分单调骨架首次成件。前提全显式：p、q1、q2 逐点正（real_log    *)
(*   正性证人位，UpReqTempDefs 同位先例）。                             *)
(* ------------------------------------------------------------------ *)
(* 【红线】Set 层零 Prop（real_le/real_lt/real_eq 全 Set 值）；全 Qed   *)
(*   闭合；禁词条目零命中（头注以中文转述）；real_eq 非 Id 禁改写，     *)
(*   全链 real_eq_trans/RealSetoid 运输（E393 纪律）。                  *)
(*   禁改红线：S04/S07/S12/S13 模块、UpReqRealFEP.v、UpReqDist.v、      *)
(*   UpReqMinFreeEps.v 全程只读。                                       *)
(* 编译配方：_t11_run.ps1 单一入口（T7 先例）+ cpu_guard CoreN 1        *)

(*   前置 .vo 全在 D:/ComplexAnalysis/ConstructiveWorld-Main/           *)
(*   ConstructiveWorld_vo/（vo 树编译，上游件零重编）。                 *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

(* ---------------------------------------------------------- *)
(* 第 0 件：定义件 real_cross_entropy                                  *)

(*   Id 形态对照：cross_entropy @S04 L4301                              *)
(*     Definition cross_entropy (p q : S -> R) : R :=                  *)

(*   real 载体副本（T7 list 载体同款）：sumf := real_list_sum X _ l；  *)
(*   唯一前提位差：real_log 带正性证人（S07 L7842 定义位），Hq 前移    *)
(*   （UpReqTempDefs real_entropy_dist 同位先例）。                     *)
(* ---------------------------------------------------------- *)
Definition real_cross_entropy
  (X : Type) (l : list X) (p q : X -> Real)
  (Hq : forall s : X, real_lt real_zero (q s)) : Real :=
  real_list_sum X (fun s => real_mult (p s) (real_opp (real_log (q s) (Hq s)))) l.

(* ---------------------------------------------------------- *)
(* 第 1a 件：(−x)+(x+y) ≡ y（抵消链基元，S08 real_kl_sum_decomp        *)
(*   Hin 块同族——x 与 y 位对调的 opp 版）。                             *)
(* ---------------------------------------------------------- *)
Lemma real_plus_opp_cancel_mid :
  forall x y : Real,
  real_eq (real_plus (real_opp x) (real_plus x y)) y.
Proof.
  intros x y.
  apply (real_eq_trans _ (real_plus (real_plus (real_opp x) x) y) _).
  - exact (real_plus_assoc (real_opp x) x y).
  - apply (real_eq_trans _ (real_plus real_zero y) _).
    + exact (RealSetoid.real_eq_plus_compat
                (real_plus (real_opp x) x) y real_zero y
                (real_eq_trans _ (real_plus x (real_opp x)) _
                   (real_plus_comm (real_opp x) x) (real_plus_opp x))
                (real_eq_refl y)).
    + apply (real_eq_trans _ _ _ (real_plus_comm real_zero y) (real_plus_zero y)).
Qed.

(* ---------------------------------------------------------- *)
(* 第 1b 件：a + (b + (−a)) ≡ b（Id minus_plus_cancel 的 real 副本；   *)
(*   主件第 ④ 步完成右元换形位）。                                     *)
(* ---------------------------------------------------------- *)
Lemma real_plus_minus_r_cancel :
  forall a b : Real,
  real_eq (real_plus a (real_plus b (real_opp a))) b.
Proof.
  intros a b.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp a) b)) _).
  - exact (RealSetoid.real_eq_plus_compat a (real_plus b (real_opp a))
              a (real_plus (real_opp a) b)
              (real_eq_refl a) (real_plus_comm b (real_opp a))).
  - apply (real_eq_trans _ (real_plus (real_plus a (real_opp a)) b) _).
    + exact (real_plus_assoc a (real_opp a) b).
    + apply (real_eq_trans _ (real_plus real_zero b) _).
      * exact (RealSetoid.real_eq_plus_compat
                  (real_plus a (real_opp a)) b real_zero b
                  (real_plus_opp a) (real_eq_refl b)).
      * apply (real_eq_trans _ _ _ (real_plus_comm real_zero b) (real_plus_zero b)).
Qed.

(* ---------------------------------------------------------- *)
(* 第 1c 件：差分双侧换形（real_minus_r 载体，S12 L13224 定义 unfold）。*)
(* ---------------------------------------------------------- *)
Lemma real_minus_r_compat :
  forall a b c d : Real,
  real_eq a c -> real_eq b d -> real_eq (real_minus_r a b) (real_minus_r c d).
Proof.
  intros a b c d Hac Hbd.
  unfold real_minus_r.
  exact (RealSetoid.real_eq_plus_compat a (real_opp b) c (real_opp d) Hac           (RealSetoid.real_eq_opp_compat b d Hbd)).
Qed.

(* ---------------------------------------------------------- *)
(* 第 1d 件：共同被加项消去（Id minus_plus_common_local @S04 L4849     *)
(*   的 real_minus_r 副本）。(A+B) − (A+C) ≡ B − C。                    *)
(* ---------------------------------------------------------- *)
Lemma real_minus_r_plus_common :
  forall A B C : Real,
  real_eq (real_minus_r (real_plus A B) (real_plus A C)) (real_minus_r B C).
Proof.
  intros A B C.
  apply (real_eq_trans
           _ (real_plus (real_plus A B) (real_plus (real_opp A) (real_opp C))) _).
  - exact (RealSetoid.real_eq_plus_compat
              (real_plus A B) (real_opp (real_plus A C))
              (real_plus A B) (real_plus (real_opp A) (real_opp C))
              (real_eq_refl (real_plus A B))
              (real_opp_plus A C)).
  - apply (real_eq_trans
             _ (real_plus (real_plus A (real_opp A)) (real_plus B (real_opp C))) _).
    + exact (real_plus_swap_mid A B (real_opp A) (real_opp C)).
    + apply (real_eq_trans _ (real_plus real_zero (real_plus B (real_opp C))) _).
      * exact (RealSetoid.real_eq_plus_compat
                  (real_plus A (real_opp A)) (real_plus B (real_opp C))
                  real_zero (real_plus B (real_opp C))
                  (real_plus_opp A) (real_eq_refl (real_plus B (real_opp C)))).
      * apply (real_eq_trans _ _ _
                  (real_plus_comm real_zero (real_plus B (real_opp C)))
                  (real_plus_zero (real_plus B (real_opp C)))).
Qed.

(* ---------------------------------------------------------- *)



(* ---------------------------------------------------------- *)
Lemma real_log_inv_pos_opp :
  forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
          (real_opp (real_log x Hx)).
Proof.
  intros x Hx.
  assert (Hone : real_lt real_zero real_one) by exact real_one_pos_local.
  assert (Hsum : real_eq
                   (real_plus (real_log x Hx)
                              (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                   real_zero).
  { apply (real_eq_trans
             _ (real_log (real_mult x (real_inv_pos x Hx))
                         (real_mult_positive x (real_inv_pos x Hx) Hx
                            (real_inv_pos_pos x Hx))) _).
    - apply real_eq_sym.
      exact (real_log_mult x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx)).
    - apply (real_eq_trans _ (real_log real_one Hone) _).
      + exact (real_log_wd (real_mult x (real_inv_pos x Hx)) real_one
                  (real_mult_positive x (real_inv_pos x Hx) Hx
                     (real_inv_pos_pos x Hx)) Hone
                  (real_inv_pos_correct x Hx)).
      + exact (real_log_one Hone). }
  apply (real_eq_trans
           _ (real_plus (real_opp (real_log x Hx))
                        (real_plus (real_log x Hx)
                                   (real_log (real_inv_pos x Hx)
                                             (real_inv_pos_pos x Hx)))) _).
  - apply real_eq_sym.
    exact (real_plus_opp_cancel_mid (real_log x Hx)
             (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))).
  - apply (real_eq_trans _ (real_plus (real_opp (real_log x Hx)) real_zero) _).
    + exact (RealSetoid.real_eq_plus_compat
                (real_opp (real_log x Hx))
                (real_plus (real_log x Hx)
                           (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                (real_opp (real_log x Hx)) real_zero
                (real_eq_refl (real_opp (real_log x Hx))) Hsum).
    + exact (real_plus_zero (real_opp (real_log x Hx))).
Qed.

(* ---------------------------------------------------------- *)
(* 第 2b 件：kl 项逐点展开桥                                           *)


(*   → 负号内搬（real_opp_plus S07 L7786 + real_opp_opp S08 L95 +      *)
(*   交换群）→ mult 换形（RealSetoid.real_eq_mult_compat）。           *)
(* ---------------------------------------------------------- *)
Lemma real_kl_term_expand :
  forall (p q : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_kl_term p q Hp Hq)
          (real_mult p (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
Proof.
  intros p q Hp Hq.
  unfold real_kl_term.
  set (Hwit := real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)).
  set (Lp := real_log p Hp).
  set (Lq := real_log q Hq).
  assert (Hlog : real_eq
                   (real_opp (real_log (real_mult q (real_inv_pos p Hp)) Hwit))
                   (real_plus Lp (real_opp Lq))).
  { apply (real_eq_trans
             _ (real_opp (real_plus Lq
                                    (real_log (real_inv_pos p Hp)
                                              (real_inv_pos_pos p Hp)))) _).
    - exact (RealSetoid.real_eq_opp_compat
                (real_log (real_mult q (real_inv_pos p Hp)) Hwit)
                (real_plus Lq
                           (real_log (real_inv_pos p Hp) (real_inv_pos_pos p Hp)))
                (real_log_mult q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))).
    - apply (real_eq_trans
               _ (real_opp (real_plus Lq (real_opp Lp))) _).
      + exact (RealSetoid.real_eq_opp_compat
                  (real_plus Lq
                             (real_log (real_inv_pos p Hp) (real_inv_pos_pos p Hp)))
                  (real_plus Lq (real_opp Lp))
                  (RealSetoid.real_eq_plus_compat Lq
                     (real_log (real_inv_pos p Hp) (real_inv_pos_pos p Hp))
                     Lq (real_opp Lp)
                     (real_eq_refl Lq) (real_log_inv_pos_opp p Hp))).
      + apply (real_eq_trans
                 _ (real_plus (real_opp Lq) (real_opp (real_opp Lp))) _).
        * exact (real_opp_plus Lq (real_opp Lp)).
        * apply (real_eq_trans _ (real_plus (real_opp Lq) Lp) _).
          -- exact (RealSetoid.real_eq_plus_compat
                       (real_opp Lq) (real_opp (real_opp Lp))
                       (real_opp Lq) Lp
                       (real_eq_refl (real_opp Lq))
                       (real_opp_opp Lp)).
          -- exact (real_plus_comm (real_opp Lq) Lp). }
  exact (RealSetoid.real_eq_mult_compat p
           (real_opp (real_log (real_mult q (real_inv_pos p Hp)) Hwit))
           p (real_plus Lp (real_opp Lq))
           (real_eq_refl p) Hlog).
Qed.

(* ---------------------------------------------------------- *)
(* 第 3 件：分解件 real_cross_entropy_decomp（real_eq 恒等式）          *)
(*   CE(p,q) ≡ Ent(p) + Σ kl_term(p,q)。                                *)
(*   交叉熵 = 自熵 + 相对熵（Id cross_entropy_decomp @S04 L4306 的     *)
(*   real 副本）；组装按 S08 real_kl_sum_decomp（L2526）同族：          *)
(*   逐点（1a 件抵消链 + real_distrib）→ ext → add → ext 换 kl 桥。     *)
(* ---------------------------------------------------------- *)
Lemma real_cross_entropy_decomp :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s)),
  real_eq (real_cross_entropy X l p q Hq)
          (real_plus
             (real_list_sum X
                (fun s => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
             (real_list_sum X
                (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)).
Proof.
  intros X l p q Hp Hq.
  assert (Hpt : forall s : X,
    real_eq (real_mult (p s) (real_opp (real_log (q s) (Hq s))))
            (real_plus (real_mult (p s) (real_opp (real_log (p s) (Hp s))))
                       (real_mult (p s)
                          (real_plus (real_log (p s) (Hp s))
                                     (real_opp (real_log (q s) (Hq s))))))).
  {
    intro s.
    assert (Ha : real_eq (real_opp (real_log (q s) (Hq s)))
                         (real_plus (real_opp (real_log (p s) (Hp s)))
                                    (real_plus (real_log (p s) (Hp s))
                                               (real_opp (real_log (q s) (Hq s)))))).
    { apply real_eq_sym.
      exact (real_plus_opp_cancel_mid (real_log (p s) (Hp s))
               (real_opp (real_log (q s) (Hq s)))). }
    apply (real_eq_trans
             _ (real_mult (p s)
                    (real_plus (real_opp (real_log (p s) (Hp s)))
                               (real_plus (real_log (p s) (Hp s))
                                          (real_opp (real_log (q s) (Hq s)))))) _).
    - exact (RealSetoid.real_eq_mult_compat (p s)
                (real_opp (real_log (q s) (Hq s))) (p s)
                (real_plus (real_opp (real_log (p s) (Hp s)))
                           (real_plus (real_log (p s) (Hp s))
                                      (real_opp (real_log (q s) (Hq s)))))
                (real_eq_refl (p s)) Ha).
    - exact (real_distrib (p s) (real_opp (real_log (p s) (Hp s)))
               (real_plus (real_log (p s) (Hp s)) (real_opp (real_log (q s) (Hq s))))).
  }
  unfold real_cross_entropy.
  apply (real_eq_trans _ (real_list_sum X
           (fun s => real_plus (real_mult (p s) (real_opp (real_log (p s) (Hp s))))
                               (real_mult (p s)
                                  (real_plus (real_log (p s) (Hp s))
                                             (real_opp (real_log (q s) (Hq s)))))) l) _).
  - exact (real_list_sum_ext X
             (fun s => real_mult (p s) (real_opp (real_log (q s) (Hq s))))
             (fun s => real_plus (real_mult (p s) (real_opp (real_log (p s) (Hp s))))
                                 (real_mult (p s)
                                    (real_plus (real_log (p s) (Hp s))
                                               (real_opp (real_log (q s) (Hq s))))))
             l Hpt).
  - apply (real_eq_trans _ (real_plus
               (real_list_sum X
                  (fun s => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
               (real_list_sum X
                  (fun s => real_mult (p s)
                                (real_plus (real_log (p s) (Hp s))
                                           (real_opp (real_log (q s) (Hq s))))) l)) _).
    + exact (real_list_sum_add X
               (fun s => real_mult (p s) (real_opp (real_log (p s) (Hp s))))
               (fun s => real_mult (p s)
                            (real_plus (real_log (p s) (Hp s))
                                       (real_opp (real_log (q s) (Hq s)))))
               l).
    + exact (RealSetoid.real_eq_plus_compat
               (real_list_sum X
                  (fun s => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
               (real_list_sum X
                  (fun s => real_mult (p s)
                                (real_plus (real_log (p s) (Hp s))
                                           (real_opp (real_log (q s) (Hq s))))) l)
               (real_list_sum X
                  (fun s => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
               (real_list_sum X
                  (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
               (real_eq_refl
                  (real_list_sum X
                     (fun s => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l))
               (real_list_sum_ext X
                  (fun s => real_mult (p s)
                                (real_plus (real_log (p s) (Hp s))
                                           (real_opp (real_log (q s) (Hq s)))))
                  (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
                  l
                  (fun s => real_eq_sym _ _
                              (real_kl_term_expand (p s) (q s) (Hp s) (Hq s))))).
Qed.

(* ---------------------------------------------------------- *)
(* 第 4 件：主件 real_training_equivalence（定理 4.10 Real 层）         *)
(*   real_le 版同一陈述（零缩水）：固定目标 p，交叉熵下降 ⟹ KL 下降。  *)
(*   组装链（序完成四步法）：                                           *)
(*   ① 差分非负：0 ≤ CE1 − CE2（S13 real_le_minus_nonneg_aux L3293，   *)
(*     Or 两支均构造性消去，无排中 leakage）                            *)
(*   ② 差分恒等：CE1 − CE2 ≡ K1 − K2（第 3 件传参位 → 1c 件 → 1d 件）    *)
(*   ③ 运输：RealSetoid.real_le_id_r（S07 L461）                        *)
(*   ④ 完成：K2 ≤ K2 + (K1 − K2) ≡ K1                                   *)
(*     （S13 real_le_plus_nonneg_r_aux L3283 + 1b 件）                  *)
(* ---------------------------------------------------------- *)
Theorem real_training_equivalence :
  forall (X : Type) (l : list X) (p q1 q2 : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq1 : forall s : X, real_lt real_zero (q1 s))
    (Hq2 : forall s : X, real_lt real_zero (q2 s)),
  real_le (real_cross_entropy X l p q2 Hq2) (real_cross_entropy X l p q1 Hq1) ->
  real_le (real_list_sum X (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l)
          (real_list_sum X (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l).
Proof.
  intros X l p q1 q2 Hp Hq1 Hq2 Hce.
  (* ① 差分非负（real_minus_r 载体 = real_plus b (real_opp a) 定义展开） *)
  assert (Hd0 : real_le real_zero
                  (real_minus_r (real_cross_entropy X l p q1 Hq1)
                                (real_cross_entropy X l p q2 Hq2)))
    by exact (real_le_minus_nonneg_aux
                (real_cross_entropy X l p q2 Hq2)
                (real_cross_entropy X l p q1 Hq1) Hce).
  (* ② 差分恒等：CE1 − CE2 ≡ K1 − K2 *)
  assert (Hdiff : real_eq
                    (real_minus_r (real_cross_entropy X l p q1 Hq1)
                                  (real_cross_entropy X l p q2 Hq2))
                    (real_minus_r
                       (real_list_sum X
                          (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l)
                       (real_list_sum X
                          (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l))).
  { apply (real_eq_trans
             _ (real_minus_r
                  (real_plus
                     (real_list_sum X
                        (fun s => real_mult (p s)
                                       (real_opp (real_log (p s) (Hp s)))) l)
                     (real_list_sum X
                        (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l))
                  (real_plus
                     (real_list_sum X
                        (fun s => real_mult (p s)
                                       (real_opp (real_log (p s) (Hp s)))) l)
                     (real_list_sum X
                        (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l))) _).
    - exact (real_minus_r_compat
                (real_cross_entropy X l p q1 Hq1)
                (real_cross_entropy X l p q2 Hq2)
                (real_plus
                   (real_list_sum X
                      (fun s => real_mult (p s)
                                     (real_opp (real_log (p s) (Hp s)))) l)
                   (real_list_sum X
                      (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l))
                (real_plus
                   (real_list_sum X
                      (fun s => real_mult (p s)
                                     (real_opp (real_log (p s) (Hp s)))) l)
                   (real_list_sum X
                      (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l))
                (real_cross_entropy_decomp X l p q1 Hp Hq1)
                (real_cross_entropy_decomp X l p q2 Hp Hq2)).
    - exact (real_minus_r_plus_common
                (real_list_sum X
                   (fun s => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
                (real_list_sum X
                   (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l)
                (real_list_sum X
                   (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l)). }
  (* ③ 运输：0 ≤ K1 − K2 *)
  assert (Hd : real_le real_zero
                  (real_minus_r
                     (real_list_sum X
                        (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l)
                     (real_list_sum X
                        (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l)))
    by exact (RealSetoid.real_le_id_r real_zero
                (real_minus_r (real_cross_entropy X l p q1 Hq1)
                              (real_cross_entropy X l p q2 Hq2))
                (real_minus_r
                   (real_list_sum X
                      (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l)
                   (real_list_sum X
                      (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l))
                Hdiff Hd0).
  (* ④ 完成：K2 ≤ K2 + (K1 − K2) ≡ K1 *)
  apply (RealSetoid.real_le_id_r
           (real_list_sum X (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l)
           (real_plus
              (real_list_sum X (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l)
              (real_minus_r
                 (real_list_sum X (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l)
                 (real_list_sum X (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l)))
           (real_list_sum X (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l)).
  - exact (real_plus_minus_r_cancel
             (real_list_sum X (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l)
             (real_list_sum X (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l)).
  - exact (real_le_plus_nonneg_r_aux
             (real_list_sum X (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l)
             (real_minus_r
                (real_list_sum X (fun s => real_kl_term (p s) (q1 s) (Hp s) (Hq1 s)) l)
                (real_list_sum X (fun s => real_kl_term (p s) (q2 s) (Hp s) (Hq2 s)) l))
             Hd).
Qed.

(* ============================================================ *)
(* G2 关：主件三件 Print Assumptions（全 Closed 口径）                  *)
(* ============================================================ *)
Print Assumptions real_cross_entropy.
Print Assumptions real_cross_entropy_decomp.
Print Assumptions real_training_equivalence.

Print Assumptions real_minus_r_compat.
