(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   fkl_family（原 L356，1 句玩具证）                                    *)
(*   fkl_pt_split_flip（原 L141，2 句玩具证）                             *)
(* ============================================================ *)
(* ============================================================ *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* 恒等守恒——清单所列 2 参数位证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* ============================================================ *)

Set Printing Width 500.
(* ============================================================ *)
(*                                                                *)
(* 【公理面】零 公理 / 零 承认件 / 零 弃证 / 零假设位；       *)
(*   语句面全 Set（real_eq S02:396 / real_le_b UpRealLeB:72 均 Set 层）； *)
(*   文尾 Print Assumptions 审计；红线四条自审通过。                    *)
(*                                                                *)
(* 【方向声明段】（用户令级红线：KL(p‖q) 符号顺序逐处核对，禁混写）       *)
(*   库内 backward 基准系（GEO1 §c-1 五件）：S05_AlignmentGRPO.v:3865/   *)
(*   3976/4080/4205 + UpAlignId.v:262，主项一律 relative_entropy        *)
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
(*                                                                *)
(*   1. S05:3865 policy_iter_backward_kl_step_beta（β 加权三 KL 恒等）   *)
(*      → 结构性不达：翻转方向无 κ-线性收缩恒等（(1−η) 项翻转为非线性    *)
(*      因子，库内无引擎）；领地 UpReqIterGeomRate 勿碰。遗留。          *)
(*   2. S05:3976 policy_iter_backward_kl_step（三 KL 精确恒等）           *)
(*   3. S05:4080 policy_iter_backward_kl_step_le（≤ 形）                  *)
(*      → 结构性不达（残差 E_f[log g−log h] 无定号，≤ 形不闭合）；        *)
(*   4. S05:4205 policy_iter_backward_kl_iter_le（迭代收缩链）            *)
(*   5. UpAlignId.v:262 policy_gap_backward_kl_exact（gap=J*−J 精确代换） *)
(*      → 前向对偶 rlhf_suboptimality_gap 形（J*−J==β·KL(π‖π＊)）属 S05    *)
(*   附账（任务 G1②③ 双验结论，防重复上报）：                            *)
(*   · 前向 Gibbs 逐点 B 形：库缺不成立——gibbsd_gibbs_pointwise_B        *)
(*     （G08_Gibbs.v:397，G05:581 复引）已成；不作交付件。               *)
(*   · 前向三角上界 KL(p,r) ≤_B f(KL(p,q),KL(q,r))：结构性不达——反向     *)
(*     Pinsker 不存在，残差无上界化引擎；定理化=遗留（障碍账）。诚实替代 *)
(*     交付=fkl_path_split_pt/sum（残差显式恒等）+fkl_dp_group_b。        *)
(*   · 交叉熵分解 Σp(−log q) == Σp(−log p)+Σkl(p,q)：G08:484 已成；       *)
(*                                                                *)
(* 【交付清单（7 件，前缀 fkl_ 全库零撞名，GEO1 表+全库 grep 双验）】      *)
(*   支撑  fkl_kl_term_expand       kl_term 换形 p·(opp(log q)+log p)     *)
(*   G1①  fkl_pt_split_flip        两点积拆分·方向翻转副本    [非平凡低]   *)
(*   G1①' fkl_pt_split_second_cross 第二权拆分+显式残差交叉项  [非平凡高]  *)
(*   G1②  fkl_path_split_pt        逐点加法链式（三角替代形）  [非平凡中]   *)
(*   G1②  fkl_path_split_sum       list 级加法链式主件        [非平凡中]   *)
(*   G3    fkl_dp_group_b           pnt_dp_two_point×链式依存  [非平凡中]   *)
(*   G2    fkl_family               sigT 四件闭合账                        *)
(*                                                                *)
(* 【引擎链（全只读依存）】CW219（S08 real_kl_term/real_log_div/          *)
(*   real_list_sum 系）；UpRealLeB real_le_b；UpReqPinskerTransport      *)
(*   （pnt_kl_pt_split/pnt_dp_two_point/pnt 组合件+pnt_ring_eq，四关绿    *)
(*   在盘）。禁碰件未 Require：UpReqIrrationalCriterion/UpReqMixingTime/  *)
(*   UpReqEnvelopeDual/UpReqIterGeomRate。                              *)
(* 编译：coqc（9.1 钉源 COQLIB=ROCQLIB=C:/Rocq-Platform~9.1~.01/     *)
(*   lib/coq）-q -native-compiler no -Q . "" UpReqForwardKLFamily        *)
(*   （cwd=Live_X）。                                                    *)
(* ============================================================ *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
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
(*   注：交叉熵分解等价排列在 G08_Gibbs.v:484 已成                        *)
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
