(* ==========================================================================)
   UpReqWeakTriangle.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：fkl_lin_opp、fkl_lin_path、fkl_lin_expand、fkl_kl_term_expand、fkl_pt_split_flip、fkl_pt_split_second_cross、fkl_path_split_pt、fkl_path_split_sum、fkl_dp_group_b。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import List.
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
Require Import UpRealLeB.
Require Import UpReqPinskerTransport.
From Stdlib Require Import Lia.

(* ================= §1 fkl_lin_opp 族 ================= *)
Set Printing Width 500.
(*   文尾 Print Assumptions 审计；红线四条自审通过。                    *)
(*   pi_star X == KL(pi_star‖X)，pi_star 互核第一参数位（首参数位参照系）。      *)
(*   本文件前向族 = 对该基准系施加方向翻转（KL(p‖q) ↦ KL(q‖p)，或拆分    *)
(*   权从第一参数位参照翻转为第二参数位参照）后诚实可达的形态，逐件语句面以符号  *)
(*   顺序定义方向：                                                   *)
(*     · fkl_pt_split_flip 主项 real_kl_term q p（q 首参数位）——            *)
(*       pnt_kl_pt_split（KL(p‖q) 框架）的方向翻转副本，非冒充件；       *)
(*     · fkl_pt_split_second_cross 拆分权取第二参数位参照 b——干净第二权      *)
(*       拆分结构性不达（无恒等式），本件=显式残差诚实形；               *)
(*     · fkl_path_split_pt/sum 链式残差 Σ f·(log g+opp(log h))          *)
(*       == E_f[log g − log h]：前向（第二参照）交叉熵差；               *)
(*     · fkl_dp_group_b 主项=分组 DP 界依存，方向随 pnt_dp_two_point。   *)
(*   全文逐处核对：无一处 backward 副本件冒充 forward 件。               *)
(*      → 结构性不达：翻转方向无 κ-线性收缩恒等（(1−η) 项翻转为非线性    *)
(*      因子，库内无引擎）；领地 UpReqIterGeomRate 勿碰。遗留。          *)
(*      → 结构性不达（残差 E_f[log g−log h] 无定号，≤ 形不闭合）；        *)
(*      → 前向对偶 rlhf_suboptimality_gap 形（J*−J==β·KL(π‖π＊)）属 S05    *)
(*   附账（任务 G1②③ 双验结论，防重复上报）：                            *)
(*   · 前向 Gibbs 逐点 B 形：库缺不成立——gibbsd_gibbs_pointwise_B        *)
(*   · 前向三角上界 KL(p,r) ≤_B f(KL(p,q),KL(q,r))：结构性不达——反向     *)
(*     Pinsker 不存在，残差无上界化引擎；定理化=遗留（障碍账）。诚实替代 *)
(*     交付=fkl_path_split_pt/sum（残差显式恒等）+fkl_dp_group_b。        *)
(*   支撑  fkl_kl_term_expand       kl_term 换形 p·(opp(log q)+log p)     *)
(*   G1①  fkl_pt_split_flip        两点积拆分·方向翻转副本    [非平凡低]   *)
(*   G1①' fkl_pt_split_second_cross 第二权拆分+显式残差交叉项  [非平凡高]  *)
(*   G1②  fkl_path_split_pt        逐点加法链式（三角替代形）  [非平凡中]   *)
(*   G1②  fkl_path_split_sum       list 级加法链式主件        [非平凡中]   *)
(*   G3    fkl_dp_group_b           pnt_dp_two_point×链式依存  [非平凡中]   *)
(*   G2    fkl_family               sigT 四件闭合账                        *)
(*   real_list_sum 系）；UpRealLeB real_le_b；UpReqPinskerTransport      *)
(*   （pnt_kl_pt_split/pnt_dp_two_point/pnt 组合件+pnt_ring_eq，四关绿    *)
(*   在盘）。禁碰件未 Require：UpReqIrrationalCriterion/UpReqMixingTime/  *)
(*   UpReqEnvelopeDual/UpReqIterGeomRate。                              *)
(* 编译：coqc（9.1 钉源 COQLIB=ROCQLIB=C:/Rocq-Platform~9.1~.01/     *)
(*   lib/coq）-q -native-compiler no -Q . "" UpReqForwardKLFamily        *)
(*   （cwd=Live_X）。                                                    *)

Import ListNotations.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.

(* ---- 0- 抽象线性闭肢（纯变量骨架：pnt_ring_eq 合法依存位） ---- *)
Lemma fkl_lin_opp : forall (U V : Real),
  real_eq (real_plus (real_opp U) (real_opp (real_opp V)))
          (real_plus (real_opp U) V).
Proof. intros U V. pnt_ring_eq. Qed.

Lemma fkl_lin_path : forall (P U V W : Real),
  real_eq (real_mult P (real_plus (real_opp W) U))
          (real_plus (real_mult P (real_plus (real_opp V) U))
                     (real_mult P (real_plus V (real_opp W)))).
Proof. intros P U V W. pnt_ring_eq. Qed.

Lemma fkl_lin_expand : forall (P X B Y A LP LQ LA LB : Real),
  real_eq (real_mult P (real_plus (real_opp LQ) LP))
    (real_plus
       (real_mult B (real_mult X
          (real_plus (real_opp (real_plus LQ (real_opp LB)))
                     (real_plus LP (real_opp LA)))))
       (real_plus
          (real_mult Y (real_mult A (real_plus (real_opp LB) LA)))
          (real_plus
             (real_mult (real_plus P (real_opp (real_mult B X)))
                        (real_plus LP (real_opp LQ)))
             (real_mult (real_plus (real_mult B X)
                         (real_opp (real_mult A Y)))
                        (real_plus LA (real_opp LB)))))).
Proof. intros P X B Y A LP LQ LA LB. pnt_ring_eq. Qed.

(* ---- 0. 支撑：kl_term 换形为「系数·(opp(log q)+log p)」原子形 ---- *)
(*   real_kl_term p q == p·(log p − log q)（方向以符号顺序呈现：首参数 p） *)
Lemma fkl_kl_term_expand : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_kl_term p q Hp Hq)
    (real_mult p (real_plus (real_opp (real_log q Hq))
                            (real_log p Hp))).
Proof.
  intros p q Hp Hq.
  unfold real_kl_term.
  apply (RealSetoid.real_eq_mult_compat _ _ _ _).
  { apply real_eq_refl. }
  { apply (real_eq_trans
             (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                (real_mult_positive q (real_inv_pos p Hp) Hq
                   (real_inv_pos_pos p Hp))))
             (real_plus (real_opp (real_log q Hq))
                        (real_opp (real_opp (real_log p Hp))))).
    - apply (real_eq_trans
               (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                  (real_mult_positive q (real_inv_pos p Hp) Hq
                     (real_inv_pos_pos p Hp))))
               (real_opp (real_plus (real_log q Hq)
                                    (real_opp (real_log p Hp))))).
      + apply (RealSetoid.real_eq_opp_compat).
        exact (real_log_div q p Hq Hp).
      + exact (pnt_opp_plus_distr (real_log q Hq)
                 (real_opp (real_log p Hp))).
    - exact (fkl_lin_opp (real_log q Hq) (real_log p Hp)). }
Qed.

(* ---- 1. G1① 前向两点积拆分（方向翻转副本件） ---- *)
(*   方向声明：主项 real_kl_term q p（q 首参数位）== b·KL(q/b‖p/a)           *)
(*   + (q/b)·KL(b‖a)。pnt_kl_pt_split（KL(p‖q) 框架，第一参数位加权）的      *)
(*   变换像：p↔q、a↔b 全翻转；非平凡性低（副本直引，诚实标注）。         *)
Lemma fkl_pt_split_flip : forall (p q a b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_eq (real_kl_term q p Hq Hp)
    (real_plus
       (real_mult b (real_kl_term
          (real_mult q (real_inv_pos b Hb))
          (real_mult p (real_inv_pos a Ha))
          (real_mult_positive q (real_inv_pos b Hb) Hq
             (real_inv_pos_pos b Hb))
          (real_mult_positive p (real_inv_pos a Ha) Hp
             (real_inv_pos_pos a Ha))))
       (real_mult (real_mult q (real_inv_pos b Hb))
                  (real_kl_term b a Hb Ha))).
Proof.
  intros p q a b Hp Hq Ha Hb.
  exact (pnt_kl_pt_split q p b a Hq Hp Hb Ha).
Qed.

(* ---- 2. G1①' 前向第二权拆分（真新件·障碍账定理化） ---- *)
(*   方向声明：主项 KL(p‖q)；拆分权取第二参数位参照系数 b（非第一参数 a）。     *)
(*   干净第二权分解 kl(p,q) == b·kl(p/a,q/b) + (q/b)·kl(a,b) 结构性不达  *)
(*   （取 p=a,q=b 即见多出交叉项）；本件=显式残差诚实形：                  *)
(*   C1=(p−bp/a)·(log p−log q)，C2=(bp/a−aq/b)·(log a−log b)。           *)
Lemma fkl_pt_split_second_cross : forall (p q a b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_eq (real_kl_term p q Hp Hq)
    (real_plus
       (real_mult b (real_kl_term
          (real_mult p (real_inv_pos a Ha))
          (real_mult q (real_inv_pos b Hb))
          (real_mult_positive p (real_inv_pos a Ha) Hp
             (real_inv_pos_pos a Ha))
          (real_mult_positive q (real_inv_pos b Hb) Hq
             (real_inv_pos_pos b Hb))))
       (real_plus
          (real_mult (real_mult q (real_inv_pos b Hb))
                     (real_kl_term a b Ha Hb))
          (real_plus
             (real_mult
                (real_plus p
                   (real_opp (real_mult b (real_mult p (real_inv_pos a Ha)))))
                (real_plus (real_log p Hp)
                           (real_opp (real_log q Hq))))
             (real_mult
                (real_plus (real_mult b (real_mult p (real_inv_pos a Ha)))
                           (real_opp (real_mult a (real_mult q (real_inv_pos b Hb)))))
                (real_plus (real_log a Ha)
                           (real_opp (real_log b Hb))))))).
Proof.
  intros p q a b Hp Hq Ha Hb.
  assert (ET1 : real_eq (real_mult b (real_kl_term (real_mult p (real_inv_pos a Ha)) (real_mult q (real_inv_pos b Hb)) (real_mult_positive p (real_inv_pos a Ha) Hp (real_inv_pos_pos a Ha)) (real_mult_positive q (real_inv_pos b Hb) Hq (real_inv_pos_pos b Hb)))) (real_mult b (real_mult (real_mult p (real_inv_pos a Ha)) (real_plus (real_opp (real_plus (real_log q Hq) (real_opp (real_log b Hb)))) (real_plus (real_log p Hp) (real_opp (real_log a Ha))))))).
  { apply (real_eq_trans (real_mult b (real_kl_term (real_mult p (real_inv_pos a Ha)) (real_mult q (real_inv_pos b Hb)) (real_mult_positive p (real_inv_pos a Ha) Hp (real_inv_pos_pos a Ha)) (real_mult_positive q (real_inv_pos b Hb) Hq (real_inv_pos_pos b Hb))))
             (real_mult b (real_mult (real_mult p (real_inv_pos a Ha))
                (real_plus (real_opp (real_log (real_mult q (real_inv_pos b Hb)) (real_mult_positive q (real_inv_pos b Hb) Hq (real_inv_pos_pos b Hb))))
                           (real_log (real_mult p (real_inv_pos a Ha)) (real_mult_positive p (real_inv_pos a Ha) Hp (real_inv_pos_pos a Ha))))))).
    - apply (RealSetoid.real_eq_mult_compat _ _ _ _).
      + apply real_eq_refl.
      + exact (fkl_kl_term_expand (real_mult p (real_inv_pos a Ha)) (real_mult q (real_inv_pos b Hb)) (real_mult_positive p (real_inv_pos a Ha) Hp (real_inv_pos_pos a Ha)) (real_mult_positive q (real_inv_pos b Hb) Hq (real_inv_pos_pos b Hb))).
    - apply (RealSetoid.real_eq_mult_compat _ _ _ _).
      + apply real_eq_refl.
      + apply (RealSetoid.real_eq_mult_compat _ _ _ _).
        * apply real_eq_refl.
        * apply (RealSetoid.real_eq_plus_compat _ _ _ _).
          { apply (RealSetoid.real_eq_opp_compat).
            exact (real_log_div q b Hq Hb). }
          { exact (real_log_div p a Hp Ha). } }
  assert (ET2 : real_eq (real_mult (real_mult q (real_inv_pos b Hb)) (real_kl_term a b Ha Hb)) (real_mult (real_mult q (real_inv_pos b Hb)) (real_mult a (real_plus (real_opp (real_log b Hb)) (real_log a Ha))))).
  { apply (RealSetoid.real_eq_mult_compat _ _ _ _).
     - apply real_eq_refl.
     - exact (fkl_kl_term_expand a b Ha Hb). }
  apply (real_eq_trans (real_kl_term p q Hp Hq) (real_mult p (real_plus (real_opp (real_log q Hq)) (real_log p Hp)))).
  { exact (fkl_kl_term_expand p q Hp Hq). }
  apply (real_eq_trans (real_mult p (real_plus (real_opp (real_log q Hq)) (real_log p Hp))) (real_plus (real_mult b (real_mult (real_mult p (real_inv_pos a Ha)) (real_plus (real_opp (real_plus (real_log q Hq) (real_opp (real_log b Hb)))) (real_plus (real_log p Hp) (real_opp (real_log a Ha)))))) (real_plus (real_mult (real_mult q (real_inv_pos b Hb)) (real_mult a (real_plus (real_opp (real_log b Hb)) (real_log a Ha)))) (real_plus (real_mult (real_plus p (real_opp (real_mult b (real_mult p (real_inv_pos a Ha))))) (real_plus (real_log p Hp) (real_opp (real_log q Hq))))  (real_mult (real_plus (real_mult b (real_mult p (real_inv_pos a Ha))) (real_opp (real_mult a (real_mult q (real_inv_pos b Hb))))) (real_plus (real_log a Ha) (real_opp (real_log b Hb)))) )))).
  { exact (fkl_lin_expand p (real_mult p (real_inv_pos a Ha)) b (real_mult q (real_inv_pos b Hb)) a (real_log p Hp) (real_log q Hq) (real_log a Ha) (real_log b Hb)). }
  apply (RealSetoid.real_eq_plus_compat _ _ _ _).
  - exact (real_eq_sym _ _ ET1).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    + exact (real_eq_sym _ _ ET2).
    + apply real_eq_refl.
Qed.

(* ---- 3. G1② 前向逐点加法链式（三角替代形·真新件） ---- *)
(*   方向声明：KL(p‖r) == KL(p‖q) + p·(log q+opp(log r))。第三肢为        *)
(*   前向交叉熵差 E_p[log q − log r]（第二参照），非 KL(q‖r)——诚实形：   *)
(*   KL 无三角不等式的结构性原因在本恒等式显形。                          *)
Lemma fkl_path_split_pt : forall (p q r : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hr : real_lt real_zero r),
  real_eq (real_kl_term p r Hp Hr)
    (real_plus (real_kl_term p q Hp Hq)
               (real_mult p (real_plus (real_log q Hq)
                                       (real_opp (real_log r Hr))))).
Proof.
  intros p q r Hp Hq Hr.
  apply (real_eq_trans (real_kl_term p r Hp Hr)
           (real_mult p (real_plus (real_opp (real_log r Hr))
                                   (real_log p Hp)))).
  { exact (fkl_kl_term_expand p r Hp Hr). }
  apply (real_eq_trans _
           (real_plus
              (real_mult p (real_plus (real_opp (real_log q Hq))
                                      (real_log p Hp)))
              (real_mult p (real_plus (real_log q Hq)
                                       (real_opp (real_log r Hr)))))).
  { exact (fkl_lin_path p (real_log p Hp) (real_log q Hq) (real_log r Hr)). }
  { apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    - exact (real_eq_sym _ _ (fkl_kl_term_expand p q Hp Hq)).
    - apply real_eq_refl. }
Qed.

(* ---- 4. G1② 前向 list 级加法链式（主件） ---- *)
(*   方向声明：Σ KL(f‖h) == Σ KL(f‖g) + Σ f·(log g+opp(log h))。          *)
(*   （gibbsd_cross_entropy_decomp）；本件为 KL-路径形独立重排             *)
Lemma fkl_path_split_sum : forall (Y : Type) (m : list Y)
  (f g h : Y -> Real)
  (Hf : forall s : Y, real_lt real_zero (f s))
  (Hg : forall s : Y, real_lt real_zero (g s))
  (Hh : forall s : Y, real_lt real_zero (h s)),
  real_eq
    (real_list_sum Y (fun s : Y => real_kl_term (f s) (h s) (Hf s) (Hh s)) m)
    (real_plus
       (real_list_sum Y
          (fun s : Y => real_kl_term (f s) (g s) (Hf s) (Hg s)) m)
       (real_list_sum Y
          (fun s : Y => real_mult (f s)
                         (real_plus (real_log (g s) (Hg s))
                                    (real_opp (real_log (h s) (Hh s))))) m)).
Proof.
  intros Y m f g h Hf Hg Hh.
  apply (real_eq_trans
           (real_list_sum Y
              (fun s : Y => real_kl_term (f s) (h s) (Hf s) (Hh s)) m)
           (real_list_sum Y
              (fun s : Y => real_plus
                              (real_kl_term (f s) (g s) (Hf s) (Hg s))
                              (real_mult (f s)
                                 (real_plus (real_log (g s) (Hg s))
                                    (real_opp (real_log (h s) (Hh s)))))) m)).
  { apply real_list_sum_ext. intro s.
    exact (fkl_path_split_pt (f s) (g s) (h s) (Hf s) (Hg s) (Hh s)). }
  apply (real_eq_trans
           (real_list_sum Y
              (fun s : Y => real_plus
                              (real_kl_term (f s) (g s) (Hf s) (Hg s))
                              (real_mult (f s)
                                 (real_plus (real_log (g s) (Hg s))
                                    (real_opp (real_log (h s) (Hh s)))))) m)
           (real_plus
              (real_list_sum Y
                 (fun s : Y => real_kl_term (f s) (g s) (Hf s) (Hg s)) m)
              (real_list_sum Y
                 (fun s : Y => real_mult (f s)
                                (real_plus (real_log (g s) (Hg s))
                                    (real_opp (real_log (h s) (Hh s))))) m))).
  { exact (real_list_sum_add Y _ _ m). }
  { apply real_eq_refl. }
Qed.

(* ---- 5. G3 依存件：pnt_dp_two_point × 前向链式合成 ---- *)
(*   方向声明：主项=分组 DP 界（随 pnt_dp_two_point KL(·‖·) 框架），        *)
(*   右端经 fkl_path_split_sum 换形为「Σ KL(f‖g) + 前向残差」显式形——     *)
(*   PNSKB pnt 系与本草前向族的复用/分工：分组机制归 pnt 系，链式残差归    *)
Theorem fkl_dp_group_b : forall (X : Type) (l : list X)
  (f g h : X -> Real)
  (Hf : forall s : X, real_lt real_zero (f s))
  (Hg : forall s : X, real_lt real_zero (g s))
  (Hh : forall s : X, real_lt real_zero (h s))
  (Hnf : real_eq (real_list_sum X f l) real_one)
  (Hnh : real_eq (real_list_sum X h l) real_one)
  (fb : X -> bool)
  (HAf : real_lt real_zero (real_list_sum X f (filter fb l)))
  (HAh : real_lt real_zero (real_list_sum X h (filter fb l)))
  (HBf : real_lt real_zero
           (real_list_sum X f (filter (fun x : X => negb (fb x)) l)))
  (HBh : real_lt real_zero
           (real_list_sum X h (filter (fun x : X => negb (fb x)) l))),
  real_le_b
    (real_plus
       (real_kl_term (real_list_sum X f (filter fb l))
                     (real_list_sum X h (filter fb l)) HAf HAh)
       (real_kl_term
          (real_list_sum X f (filter (fun x : X => negb (fb x)) l))
          (real_list_sum X h (filter (fun x : X => negb (fb x)) l))
          HBf HBh))
    (real_plus
       (real_list_sum X
          (fun s : X => real_kl_term (f s) (g s) (Hf s) (Hg s)) l)
       (real_list_sum X
          (fun s : X => real_mult (f s)
                         (real_plus (real_log (g s) (Hg s))
                                    (real_opp (real_log (h s) (Hh s))))) l)).
Proof.
  intros X l f g h Hf Hg Hh Hnf Hnh fb HAf HAh HBf HBh.
  apply (pnt_le_b_eq_r _
          (real_list_sum X
             (fun s : X => real_kl_term (f s) (h s) (Hf s) (Hh s)) l) _).
  - exact (fkl_path_split_sum X l f g h Hf Hg Hh).
  - exact (pnt_dp_two_point X l f h Hf Hh Hnf Hnh fb HAf HAh HBf HBh).
Qed.

(* ---- 6. G2 闭合件：前向族 sigT 四件账 ---- *)
(*   方向声明：四肢方向逐件见上文声明段；本件为装配账，无新语句面。        *)
(*   肢定义=四件主语句面（Set 层）的逐字引用，闭合件只做 sigT 装配。      *)
Definition fkl_leg_flip : Set := forall (p q a b : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b), real_eq (real_kl_term q p Hq Hp) (real_plus (real_mult b (real_kl_term (real_mult q (real_inv_pos b Hb)) (real_mult p (real_inv_pos a Ha)) (real_mult_positive q (real_inv_pos b Hb) Hq (real_inv_pos_pos b Hb)) (real_mult_positive p (real_inv_pos a Ha) Hp (real_inv_pos_pos a Ha)))) (real_mult (real_mult q (real_inv_pos b Hb)) (real_kl_term b a Hb Ha))).
Definition fkl_leg_second_cross : Set := forall (p q a b : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b), real_eq (real_kl_term p q Hp Hq) (real_plus (real_mult b (real_kl_term (real_mult p (real_inv_pos a Ha)) (real_mult q (real_inv_pos b Hb)) (real_mult_positive p (real_inv_pos a Ha) Hp (real_inv_pos_pos a Ha)) (real_mult_positive q (real_inv_pos b Hb) Hq (real_inv_pos_pos b Hb)))) (real_plus (real_mult (real_mult q (real_inv_pos b Hb)) (real_kl_term a b Ha Hb)) (real_plus (real_mult (real_plus p (real_opp (real_mult b (real_mult p (real_inv_pos a Ha))))) (real_plus (real_log p Hp) (real_opp (real_log q Hq)))) (real_mult (real_plus (real_mult b (real_mult p (real_inv_pos a Ha))) (real_opp (real_mult a (real_mult q (real_inv_pos b Hb))))) (real_plus (real_log a Ha) (real_opp (real_log b Hb))))))).
Definition fkl_leg_path_sum : Type := forall (Y : Type) (m : list Y) (f g h : Y -> Real) (Hf : forall s : Y, real_lt real_zero (f s)) (Hg : forall s : Y, real_lt real_zero (g s)) (Hh : forall s : Y, real_lt real_zero (h s)), real_eq (real_list_sum Y (fun s : Y => real_kl_term (f s) (h s) (Hf s) (Hh s)) m) (real_plus (real_list_sum Y (fun s : Y => real_kl_term (f s) (g s) (Hf s) (Hg s)) m) (real_list_sum Y (fun s : Y => real_mult (f s) (real_plus (real_log (g s) (Hg s)) (real_opp (real_log (h s) (Hh s))))) m)).
Definition fkl_leg_path_pt : Set := forall (p q r : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q) (Hr : real_lt real_zero r), real_eq (real_kl_term p r Hp Hr) (real_plus (real_kl_term p q Hp Hq) (real_mult p (real_plus (real_log q Hq) (real_opp (real_log r Hr))))).

(*   注：fkl_leg_path_sum 含 (Y : Type) 量词，落 Type 层（与             *)
(*   pnt_dp_two_point 同型）；闭合件收 Set 三肢，list 级延伸件独立在案。  *)
Theorem fkl_family :
  sigT (fun _ : fkl_leg_flip =>
    sigT (fun _ : fkl_leg_second_cross => fkl_leg_path_pt)).
Proof.
  exact (existT _ fkl_pt_split_flip           (existT _ fkl_pt_split_second_cross fkl_path_split_pt)).
Qed.

(* ---- 审计位 ---- *)
Print Assumptions fkl_kl_term_expand.
Print Assumptions fkl_pt_split_flip.
Print Assumptions fkl_pt_split_second_cross.
Print Assumptions fkl_path_split_pt.
Print Assumptions fkl_path_split_sum.
Print Assumptions fkl_dp_group_b.
Print Assumptions fkl_family.
(* ================= §2 wtl_min_ratio 族 ================= *)
Set Printing Width 500.
(*   文尾 Print Assumptions 审计（零 magic=零公理）。红线四条自审通过。   *)
(*   Q=(1/2,1/2), R=(9/10,1/10), P=(0,1) 使 RHS-LHS=ln(3/5)<0，           *)
(*   近退化采样违反 77/3000（attn/_texpd3_sanity.py 第 1/3 节）。          *)
(*   真形（EXPD1 报告 2.2 文字段）：                                      *)
(*     KL(p||r) <=_B KL(p||q) + KL(q||r) + log(1/c)，c := min_s(r_s/q_s)， *)
(*   证书取逐点乘法形 c·q_s <= r_s（Real 层 real_le 形，免除法）。         *)
(*   修正版压测违反 0/20000（同脚本第 2 节）。逐点路线：q_s/r_s <= 1/c    *)
(*   ⟹ log 单调（real_log_le_mono）⟹ 加权求和保序（real_list_sum_le）。   *)
(*   KL 符号顺序逐处核对：kl_term 首参数位=加权分布（p 或 q），全部前向。      *)
(*   G1①  wtl_qdiv_pos             Q 层除法正性             [非平凡低]    *)
(*   G1①  wtl_min_ratio_lb         min 证书下界（Prop）     [非平凡低]    *)
(*   G1①  wtl_min_ratio_pos        min 证书正性（Prop）     [非平凡低]    *)
(*   G1②  wtl_ratio_cert + wtl_min_ratio_cert_set  sigT 交付账 [非平凡低] *)
(*   G2    wtl_cond_triangle       条件化弱三角主件         [非平凡中]    *)
(*   G2    wtl_family              sigT 闭合账              [装配]        *)
(*   G3    CS 权渡形/unique-max 特例：遗留（需 Real 平方族引擎，          *)
(*   1. Qlt_bool/Qlt_bool_iff/Qle_ltb 不在 QArith_base（仅 micromega 有   *)
(*      Qlt_bool，避重不 Require）：正性证改 Qlt 0 c（Prop）；             *)
(*   2. Qmult_inv_r 前提为 Qeq 形 ~ x == 0（非 Leibniz <>），Hq0 同形。    *)
(*   3. G1 sigT 交付件正性证用 Qlt 0 c（Prop 件）；可计算部分=witness c    *)
(*      （wtl_min_ratio l）+ Qle_bool 逐点下界检查，诚实标注。            *)
(*   real_log_div/real_list_sum_le/real_list_sum_linear_r；S07 RealSetoid  *)
(*   （real_le_compat/real_le_id_l/real_le_id_r/real_eq_mult_compat/      *)
(*   real_eq_plus_compat）+ 顶层 real_le_mult_compat/real_le_plus_compat/ *)
(*   real_mult_positive；S02 real_mult_comm/assoc/one、real_plus_assoc/   *)
(*   comm；G01 real_log_le_mono；UpRealLeB real_le_b/real_le_to_le_b；     *)
(*   UpReqPinskerTransport pnt_le_b_refl/eq_r/trans/add_r/pnt_mult_inv_r/  *)
(*   pnt_list_gibbs_b；UpReqForwardKLFamily fkl_path_split_sum（依存供体）。*)
(*   禁碰件未 Require。                                                   *)
(* 编译：coqc（9.1 钉源 COQLIB=ROCQLIB=C:/Rocq-Platform~9.1~2026.01/      *)
(*   lib/coq）-q -native-compiler no -Q . "" UpReqWeakTriangle（cwd=Live_X，*)
(*   cpu_guard 包装）。                                                   *)

Import ListNotations.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.

Open Scope Q_scope.

(* G1：Q 层 min 证书（c := min_s(r_s/q_s) 的构造性下界与正性）        *)

(* ---- 0. 证书量：l 上逐点比 r/q 的扫描最小值（nil 支取 1，空载退化） ---- *)
Fixpoint wtl_min_ratio (l : list (Q * Q)) : Q :=
  match l with
  | nil => 1
  | (q, r) :: rest =>
      let m := wtl_min_ratio rest in
      if Qle_bool (r / q) m then (r / q) else m
  end.

Definition wtl_qrat (qr : Q * Q) : Q := (snd qr) / (fst qr).

(* ---- 1. 除法正性：0<q、0<r ⟹ 0<r/q（Qmult_lt_r×Qmult_inv_r 机械链） ---- *)
Lemma wtl_qdiv_pos : forall q r : Q, Qlt 0 q -> Qlt 0 r -> Qlt 0 (r / q).
Proof.
  intros q r Hq Hr. unfold Qdiv.
  assert (Hq0 : ~ q == 0).
  { intro Hz. exact (Qlt_not_eq 0 q Hq (Qeq_sym q 0 Hz)). }
  assert (Hinv : / q * q == 1).
  { apply (Qeq_trans (/ q * q) (q * / q) 1).
    - apply Qmult_comm.
    - apply Qmult_inv_r. exact Hq0. }
  apply (proj1 (Qmult_lt_r 0 (r * / q) q Hq)).
  rewrite <- Qmult_assoc. rewrite Hinv.
  rewrite (Qmult_0_l q). rewrite (Qmult_1_r r). exact Hr.
Qed.

(* ---- 2. min 证书下界：qr ∈ l ⟹ wtl_min_ratio l ≤ r_q/q_q ---- *)
Lemma wtl_min_ratio_lb : forall (l : list (Q * Q)) (qr : Q * Q),
  In qr l -> Qle (wtl_min_ratio l) (wtl_qrat qr).
Proof.
  intros l. induction l as [| [a b] rest IH]; intros qr Hin.
  - destruct Hin.
  - simpl in Hin. simpl. destruct Hin as [Heq | Hin].
    + replace (wtl_qrat qr) with (b / a)
        by (unfold wtl_qrat; rewrite <- Heq; reflexivity).
      destruct (Qle_bool (b / a) (wtl_min_ratio rest)) eqn:E.
      * apply Qle_refl.
      * apply Qlt_le_weak. unfold Qlt.
        unfold Qle_bool in E. apply Z.leb_gt in E. exact E.
    + destruct (Qle_bool (b / a) (wtl_min_ratio rest)) eqn:E.
      * eapply Qle_trans.
        -- apply Qle_bool_iff. exact E.
        -- apply IH. exact Hin.
      * apply IH. exact Hin.
Qed.

(* ---- 3. min 证书正性：逐点正 ⟹ 0 < wtl_min_ratio l ---- *)
Lemma wtl_min_ratio_pos : forall l : list (Q * Q),
  (forall qr : Q * Q, In qr l -> Qlt 0 (fst qr)) ->
  (forall qr : Q * Q, In qr l -> Qlt 0 (snd qr)) ->
  Qlt 0 (wtl_min_ratio l).
Proof.
  intros l. induction l as [| [a b] rest IH]; intros Hq Hr.
  - unfold Qlt. simpl. lia.
  - simpl. destruct (Qle_bool (b / a) (wtl_min_ratio rest)) eqn:E.
    + exact (wtl_qdiv_pos a b (Hq (a, b) (or_introl eq_refl))
                         (Hr (a, b) (or_introl eq_refl))).
    + apply IH.
      * intros qr0 Hin0. exact (Hq qr0 (or_intror Hin0)).
      * intros qr0 Hin0. exact (Hr qr0 (or_intror Hin0)).
Qed.

(* ---- 4. G1 Set/sigT 交付账：正性 + 逐点 Qle_bool 下界可计算证书 ---- *)
(*   witness=可计算 Q（wtl_min_ratio l）；正性证=Qlt（Prop，诚实标注）；   *)
(*   下界证=逐点 Qle_bool 等式（bool 可计算检查）。                       *)
Definition wtl_ratio_cert (l : list (Q * Q)) : Type :=
  sigT (fun c : Q =>
    sigT (fun _ : Qlt 0 c =>
      forall qr : Q * Q, In qr l -> Qle_bool c (wtl_qrat qr) = true)).

Theorem wtl_min_ratio_cert_set : forall l : list (Q * Q),
  (forall qr : Q * Q, In qr l -> Qlt 0 (fst qr)) ->
  (forall qr : Q * Q, In qr l -> Qlt 0 (snd qr)) ->
  wtl_ratio_cert l.
Proof.
  intros l Hq Hr.
  refine (existT _ (wtl_min_ratio l) (existT _ _ _)).
  - exact (wtl_min_ratio_pos l Hq Hr).
  - intros qr Hin.
    exact (proj2 (Qle_bool_iff (wtl_min_ratio l) (wtl_qrat qr))
                  (wtl_min_ratio_lb l qr Hin)).
Qed.

(* G2：Real 层条件化弱三角主件                                        *)
(*   KL(p||r) <=_B KL(p||q) + KL(q||r) + log(1/c)，证书 c·q_s ≤ r_s。  *)
(*   （c := min_s(r_s/q_s) 的逻辑内容；系数层由 G1 证书供给。）        *)

Theorem wtl_cond_triangle : forall (Y : Type) (m : list Y) (p q r : Y -> Real)
  (c : Real)
  (Hp : forall s : Y, real_lt real_zero (p s))
  (Hq : forall s : Y, real_lt real_zero (q s))
  (Hr : forall s : Y, real_lt real_zero (r s))
  (Hnp : real_eq (real_list_sum Y p m) real_one)
  (Hnq : real_eq (real_list_sum Y q m) real_one)
  (Hnr : real_eq (real_list_sum Y r m) real_one)
  (Hc : real_lt real_zero c)
  (Hcert : forall s : Y, real_le (real_mult c (q s)) (r s)),
  real_le_b
    (real_list_sum Y (fun s : Y => real_kl_term (p s) (r s) (Hp s) (Hr s)) m)
    (real_plus
       (real_list_sum Y (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
       (real_plus
          (real_list_sum Y (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s)) m)
          (real_log (real_inv_pos c Hc) (real_inv_pos_pos c Hc)))).
Proof.
  intros Y m p q r c Hp Hq Hr Hnp Hnq Hnr Hc Hcert.
  set (L := real_inv_pos c Hc).
  set (Llog := real_log L (real_inv_pos_pos c Hc)).
  (* 步 1a：证书消 inv —— q_s·inv(r_s) ≤ L := inv(c)。
     路线：c·q_s ≤ r_s 两边乘 L·inv(r_s)（正性证书 real_mult_positive），
     左端 (c·q_s)·(L·ir) == c·((q_s·ir)·L) == q_s·ir（pnt_mult_inv_r），
     右端 r_s·(L·ir) == L（pnt_mult_inv_r）。 *)
  assert (HqrL : forall s : Y,
    real_le (real_mult (q s) (real_inv_pos (r s) (Hr s))) L).
  { intro s.
    apply (RealSetoid.real_le_compat
             (real_mult (real_mult c (q s))
                        (real_mult L (real_inv_pos (r s) (Hr s))))
             (real_mult (q s) (real_inv_pos (r s) (Hr s)))
             (real_mult (r s) (real_mult L (real_inv_pos (r s) (Hr s))))
             L).
    - (* (c·q_s)·(L·ir) == q_s·ir：assoc/comm 三步 + pnt_mult_inv_r *)
      apply (real_eq_trans
               (real_mult (real_mult c (q s))
                          (real_mult L (real_inv_pos (r s) (Hr s))))
               (real_mult c
                  (real_mult (q s)
                             (real_mult L (real_inv_pos (r s) (Hr s)))))).
      + exact (real_eq_sym _ _
                 (real_mult_assoc c (q s)
                    (real_mult L (real_inv_pos (r s) (Hr s))))).
      + apply (real_eq_trans
                 (real_mult c
                    (real_mult (q s)
                               (real_mult L (real_inv_pos (r s) (Hr s)))))
                 (real_mult c
                    (real_mult (q s)
                               (real_mult (real_inv_pos (r s) (Hr s)) L)))).
        * apply (RealSetoid.real_eq_mult_compat
                   c (real_mult (q s) (real_mult L (real_inv_pos (r s) (Hr s))))
                   c (real_mult (q s)
                                (real_mult (real_inv_pos (r s) (Hr s)) L))).
          -- apply real_eq_refl.
          -- apply (RealSetoid.real_eq_mult_compat
                     (q s) (real_mult L (real_inv_pos (r s) (Hr s)))
                     (q s) (real_mult (real_inv_pos (r s) (Hr s)) L)).
            ++ apply real_eq_refl.
            ++ exact (real_mult_comm L (real_inv_pos (r s) (Hr s))).
        * apply (real_eq_trans
                   (real_mult c
                      (real_mult (q s)
                                 (real_mult (real_inv_pos (r s) (Hr s)) L)))
                   (real_mult c
                      (real_mult (real_mult (q s) (real_inv_pos (r s) (Hr s)))
                                 L))).
          -- apply (RealSetoid.real_eq_mult_compat
                     c (real_mult (q s)
                                (real_mult (real_inv_pos (r s) (Hr s)) L))
                     c (real_mult (real_mult (q s) (real_inv_pos (r s) (Hr s)))
                                  L)).
            ++ apply real_eq_refl.
            ++ exact (real_mult_assoc (q s) (real_inv_pos (r s) (Hr s)) L).
          -- exact (pnt_mult_inv_r c
                     (real_mult (q s) (real_inv_pos (r s) (Hr s))) Hc).
    - (* r_s·(L·ir) == L（逐字 pnt_mult_inv_r） *)
      exact (pnt_mult_inv_r (r s) L (Hr s)).
    - (* 证书原形 c·q_s ≤ r_s 两边乘正量 L·ir *)
      exact (real_le_mult_compat (real_mult c (q s)) (r s)
               (real_mult L (real_inv_pos (r s) (Hr s)))
               (real_mult_positive L (real_inv_pos (r s) (Hr s))
                  (real_inv_pos_pos c Hc) (real_inv_pos_pos (r s) (Hr s)))
               (Hcert s)). }
  (* 步 1b：逐点 log 单调升权 —— p_s·(log q_s − log r_s) ≤ p_s·log(1/c)。
     路线：real_le_mult_compat（权 p_s>0）+ real_log_div 换形 +
     real_log_le_mono（q_s·inv r_s ≤ L 由步 1a）。 *)
  assert (Hpt : forall s : Y,
    real_le (real_mult (p s)
               (real_plus (real_log (q s) (Hq s))
                          (real_opp (real_log (r s) (Hr s)))))
            (real_mult (p s) Llog)).
  { intro s.
    apply (RealSetoid.real_le_compat
             (real_mult
                (real_plus (real_log (q s) (Hq s))
                           (real_opp (real_log (r s) (Hr s)))) (p s))
             (real_mult (p s)
                (real_plus (real_log (q s) (Hq s))
                           (real_opp (real_log (r s) (Hr s)))))
             (real_mult Llog (p s))
             (real_mult (p s) Llog)).
    - exact (real_mult_comm
               (real_plus (real_log (q s) (Hq s))
                          (real_opp (real_log (r s) (Hr s)))) (p s)).
    - exact (real_mult_comm Llog (p s)).
    - apply (real_le_mult_compat
               (real_plus (real_log (q s) (Hq s))
                          (real_opp (real_log (r s) (Hr s))))
               Llog (p s) (Hp s)).
      exact (RealSetoid.real_le_compat
               (real_log (real_mult (q s) (real_inv_pos (r s) (Hr s)))
                  (real_mult_positive (q s) (real_inv_pos (r s) (Hr s))
                     (Hq s) (real_inv_pos_pos (r s) (Hr s))))
               (real_plus (real_log (q s) (Hq s))
                          (real_opp (real_log (r s) (Hr s))))
               Llog Llog
               (real_log_div (q s) (r s) (Hq s) (Hr s))
               (real_eq_refl Llog)
               (real_log_le_mono (real_mult (q s) (real_inv_pos (r s) (Hr s)))
                  L
                  (real_mult_positive (q s) (real_inv_pos (r s) (Hr s))
                     (Hq s) (real_inv_pos_pos (r s) (Hr s)))
                  (real_inv_pos_pos c Hc)
                  (HqrL s))). }
  (* 步 2：求和保序 ΣRes ≤ Σ(p·log(1/c)) *)
  assert (Hs2 : real_le
    (real_list_sum Y (fun s : Y =>
       real_mult (p s)
         (real_plus (real_log (q s) (Hq s))
                    (real_opp (real_log (r s) (Hr s))))) m)
    (real_list_sum Y (fun s : Y => real_mult (p s) Llog) m)).
  { apply real_list_sum_le. intro s. exact (Hpt s). }
  (* 步 3：归一化收肢 Σ(p·log(1/c)) == log(1/c)（real_list_sum_linear_r + Hnp） *)
  assert (Hs3 : real_eq
    (real_list_sum Y (fun s : Y => real_mult (p s) Llog) m) Llog).
  { apply (real_eq_trans
             (real_list_sum Y (fun s : Y => real_mult (p s) Llog) m)
             (real_mult Llog (real_list_sum Y p m))).
    - exact (real_list_sum_linear_r Y Llog p m).
    - apply (real_eq_trans
               (real_mult Llog (real_list_sum Y p m))
               (real_mult Llog real_one)).
      + exact (RealSetoid.real_eq_mult_compat Llog (real_list_sum Y p m)
                 Llog real_one
                 (real_eq_refl Llog) Hnp).
      + exact (real_mult_one Llog). }
  assert (Hs4 : real_le
    (real_list_sum Y (fun s : Y =>
       real_mult (p s)
         (real_plus (real_log (q s) (Hq s))
                    (real_opp (real_log (r s) (Hr s))))) m) Llog).
  { exact (RealSetoid.real_le_id_r
             (real_list_sum Y (fun s : Y =>
                real_mult (p s)
                  (real_plus (real_log (q s) (Hq s))
                             (real_opp (real_log (r s) (Hr s))))) m)
             (real_list_sum Y (fun s : Y => real_mult (p s) Llog) m)
             Llog Hs3 Hs2). }
  (* 步 4+5：fkl_path_split_sum 链式 + 加法保序 ⟹ ΣKL(p||r) ≤ ΣKL(p||q)+log(1/c) *)
  assert (Hs5 : real_le
    (real_list_sum Y (fun s : Y => real_kl_term (p s) (r s) (Hp s) (Hr s)) m)
    (real_plus
       (real_list_sum Y (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
       Llog)).
  { apply (real_le_trans
             (real_list_sum Y
                (fun s : Y => real_kl_term (p s) (r s) (Hp s) (Hr s)) m)
             (real_plus
                (real_list_sum Y
                   (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                (real_list_sum Y (fun s : Y =>
                   real_mult (p s)
                     (real_plus (real_log (q s) (Hq s))
                                (real_opp (real_log (r s) (Hr s))))) m))
             (real_plus
                (real_list_sum Y
                   (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                Llog)).
    - exact (RealSetoid.real_le_id_l
               (real_list_sum Y
                  (fun s : Y => real_kl_term (p s) (r s) (Hp s) (Hr s)) m)
               (real_plus
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                  (real_list_sum Y (fun s : Y =>
                     real_mult (p s)
                       (real_plus (real_log (q s) (Hq s))
                                  (real_opp (real_log (r s) (Hr s))))) m))
               (real_plus
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                  (real_list_sum Y (fun s : Y =>
                     real_mult (p s)
                       (real_plus (real_log (q s) (Hq s))
                                  (real_opp (real_log (r s) (Hr s))))) m))
               (fkl_path_split_sum Y m p q r Hp Hq Hr)
               (real_le_refl
                  (real_plus
                     (real_list_sum Y
                        (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s))
                        m)
                     (real_list_sum Y (fun s : Y =>
                        real_mult (p s)
                          (real_plus (real_log (q s) (Hq s))
                                     (real_opp (real_log (r s) (Hr s)))))
                        m)))).
    - exact (real_le_plus_compat
               (real_list_sum Y
                  (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
               (real_list_sum Y
                  (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
               (real_list_sum Y (fun s : Y =>
                  real_mult (p s)
                    (real_plus (real_log (q s) (Hq s))
                               (real_opp (real_log (r s) (Hr s))))) m)
               Llog
               (real_le_refl
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m))
               Hs4). }
  (* 步 7a：重排 (A+log(1/c))+C == A+(C+log(1/c))（assoc+comm 显式链） *)
  assert (Hreord : real_eq
    (real_plus
       (real_plus
          (real_list_sum Y
             (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
          Llog)
       (real_list_sum Y
          (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s)) m))
    (real_plus
       (real_list_sum Y
          (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
       (real_plus
          (real_list_sum Y
             (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s)) m)
          Llog))).
  { apply (real_eq_trans
             (real_plus
                (real_plus
                   (real_list_sum Y
                      (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                   Llog)
                (real_list_sum Y
                   (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s)) m))
             (real_plus
                (real_list_sum Y
                   (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                (real_plus Llog
                   (real_list_sum Y
                      (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s))
                      m)))).
    - exact (real_eq_sym _ _
               (real_plus_assoc
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                  Llog
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s))
                     m))).
    - exact (RealSetoid.real_eq_plus_compat
               (real_list_sum Y
                  (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
               (real_plus Llog
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s))
                     m))
               (real_list_sum Y
                  (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
               (real_plus
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s))
                     m)
                  Llog)
               (real_eq_refl
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s))
                     m))
               (real_plus_comm Llog
                  (real_list_sum Y
                     (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s))
                     m))). }
  (* 步 6+7b：升 Bishop + Gibbs 非负肢 + pnt 组合闭合 *)
  apply (pnt_le_b_trans
           (real_list_sum Y
              (fun s : Y => real_kl_term (p s) (r s) (Hp s) (Hr s)) m)
           (real_plus
              (real_list_sum Y
                 (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
              Llog)
           (real_plus
              (real_list_sum Y
                 (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
              (real_plus
                 (real_list_sum Y
                    (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s)) m)
                 Llog))).
  - exact (real_le_to_le_b _ _ Hs5).
  - exact (pnt_le_b_eq_r
             (real_plus
                (real_list_sum Y
                   (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                Llog)
             (real_plus
                (real_plus
                   (real_list_sum Y
                      (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                   Llog)
                (real_list_sum Y
                   (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s)) m))
             (real_plus
                (real_list_sum Y
                   (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                (real_plus
                   (real_list_sum Y
                      (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s))
                      m)
                   Llog))
             Hreord
             (pnt_le_b_add_r
                (real_plus
                   (real_list_sum Y
                      (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                   Llog)
                (real_plus
                   (real_list_sum Y
                      (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                   Llog)
                (real_list_sum Y
                   (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s)) m)
                (pnt_list_gibbs_b Y m q r Hq Hr Hnq Hnr)
                (pnt_le_b_refl
                   (real_plus
                      (real_list_sum Y
                         (fun s : Y =>
                            real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
                      Llog)))).
Qed.

(* G2 闭合件：wtl 族 sigT 账（照 fkl_family 模式）                    *)
Definition wtl_leg_min_cert : Type := forall l : list (Q * Q),
  (forall qr : Q * Q, In qr l -> Qlt 0 (fst qr)) ->
  (forall qr : Q * Q, In qr l -> Qlt 0 (snd qr)) ->
  wtl_ratio_cert l.

(* 注：含 (Y : Type) 量词，落 Type 层（与 fkl_leg_path_sum 同型注记）。 *)
Definition wtl_leg_cond_triangle : Type := forall (Y : Type) (m : list Y)
  (p q r : Y -> Real) (c : Real)
  (Hp : forall s : Y, real_lt real_zero (p s))
  (Hq : forall s : Y, real_lt real_zero (q s))
  (Hr : forall s : Y, real_lt real_zero (r s))
  (Hnp : real_eq (real_list_sum Y p m) real_one)
  (Hnq : real_eq (real_list_sum Y q m) real_one)
  (Hnr : real_eq (real_list_sum Y r m) real_one)
  (Hc : real_lt real_zero c)
  (Hcert : forall s : Y, real_le (real_mult c (q s)) (r s)),
  real_le_b
    (real_list_sum Y (fun s : Y => real_kl_term (p s) (r s) (Hp s) (Hr s)) m)
    (real_plus
       (real_list_sum Y (fun s : Y => real_kl_term (p s) (q s) (Hp s) (Hq s)) m)
       (real_plus
          (real_list_sum Y (fun s : Y => real_kl_term (q s) (r s) (Hq s) (Hr s)) m)
          (real_log (real_inv_pos c Hc) (real_inv_pos_pos c Hc)))).

Theorem wtl_family :
  sigT (fun _ : wtl_leg_min_cert => wtl_leg_cond_triangle).
Proof.
  exact (existT _ wtl_min_ratio_cert_set wtl_cond_triangle).
Qed.

(* ---- 审计位（零 magic 检查） ---- *)
Print Assumptions wtl_qdiv_pos.
Print Assumptions wtl_min_ratio_lb.
Print Assumptions wtl_min_ratio_pos.
Print Assumptions wtl_min_ratio_cert_set.
Print Assumptions wtl_cond_triangle.
Print Assumptions wtl_family.
