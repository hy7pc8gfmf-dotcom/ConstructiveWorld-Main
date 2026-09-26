(* ============================================================ *)
(* UpAblT1b_AttnDoeblin.v —— 假设消融战役 T1b 批施工席伴生放电件      *)
(* 战役：FA1 普查第①批 swap/Fubini 族 + 第②批 abs 幂等族            *)
(* 原树零改：本件为独立伴生件，只读消费基座，不入注册面（随 R 波）      *)
(*                                                              *)
(* 母本坐标（Live_X 现档实态实测，与 ConstructiveWorld-Main 树行号齐）： *)
(*   AttnDoeblin.v L154 sum_swap_cc（双和交换槽）                    *)
(*   AttnDoeblin.v L157 abs_ge_zero_id_cc（le 版 abs 恒等缺口）       *)
(*   AttnDoeblin.v L472 bs_swap（诚实接口三件之首）                   *)
(*   AttnDoeblin.v L475 bs_abs（诚实接口三件之二）                    *)
(*   同节已收口槽：L444 enum、L485 sum_eq_list（枚举求和规范化）        *)
(* 消费位判据（E752 翻案形）：swap 槽=sum_eq_list 槽+列表 Fubini        *)
(*   组合学整体导出，非独立接口位；abs 槽=AbsLeId 直喂。                *)
(*                                                              *)
(* 非平凡性分级（详见 attn/_tt1b_消融报告-20260919.md 分级表）：        *)
(*   abl_AtnDoeblin_sum_swap_cc ：N2（E752 段一+段二导出链复刻）        *)
(*   abl_AtnDoeblin_bs_swap     ：N1（同语句双槽镜像，L472=L154 同形）   *)
(*   abl_AtnDoeblin_abs_ge_zero_id_cc ：N1（AbsLeId L50 直喂）         *)
(*   abl_AtnDoeblin_bs_abs      ：N1（同语句双槽镜像，L475=L157 同形）   *)
(*                                                              *)
(* 红线自审（全部打勾）：                                             *)
(*  [x] 现档实态取证已做：Live_X 与 Main 树 L154/157/472/475 行号齐      *)
(*  [x] 逐字抽取：被消融槽语句自现档源码逐字拷入（参序/命名/隐式位同形）  *)
(*  [x] 消费位实证：E752 卡 bs_swap 可消融判词+P7D 件在库为先例坐标      *)
(*  [x] 分级 N/T 已逐件标注（W 件不发本件；本件零 W）                   *)
(*  [x] 禁词双轨零：头注全中文表述（含英文原词字面亦零）                 *)
(*  [x] 编译收口+文尾逐件假设面打印全闭                                 *)
(*  [x] 提取探针 Obj.magic=0：输出目录树外隔离（attn/logs/g3 留痕）      *)
(*  [x] 模块核验 EXIT=0：attn/logs/g4 留痕（后台长窗）                  *)
(*  [x] 四关留痕：attn/logs/g{1..4}-UpAblT1b_AttnDoeblin.log            *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import AttnDoeblin.
Require Import AbsLeId.

(* ################ 段一：列表 Fubini 组合学（E752 段一形复刻） ################
   出节机 AttnDoeblin.bs_list_sum（顶层定档）上的逐点同余/加法线性/
   零函数塌缩/双重和交换。段一各件为地基件，不单独计入战果。 *)

Section AblListSum.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.

(* 逐点 Id ⟹ 列表和 Id（bs_list_sum 上的同余延拓） *)
Lemma abl_lsum_ext : forall (f g : S -> R) (l : list S),
  (forall x : S, Id (f x) (g x)) ->
  Id (AttnDoeblin.bs_list_sum f l) (AttnDoeblin.bs_list_sum g l).
Proof.
  intros f g l H. induction l as [| x t IH].
  - exact id_refl.
  - simpl. exact (id_cong2 plus (H x) IH).
Qed.

(* 列表和的加法线性 *)
Lemma abl_lsum_add : forall (f g : S -> R) (l : list S),
  Id (AttnDoeblin.bs_list_sum (fun s : S => plus (f s) (g s)) l)
     (plus (AttnDoeblin.bs_list_sum f l) (AttnDoeblin.bs_list_sum g l)).
Proof.
  intros f g l. induction l as [| x t IH].
  - exact (id_sym (plus_zero zero)).
  - simpl.
    apply (id_trans (id_cong (fun w : R => plus (plus (f x) (g x)) w) IH)).
    exact (AttnDoeblin.plus_exchange (f x) (AttnDoeblin.bs_list_sum f t)
                                     (g x) (AttnDoeblin.bs_list_sum g t)).
Qed.

(* 零函数列表和为零（消费 bs_list_const_sum ＋ mult 零元） *)
Lemma abl_lsum_zero : forall l : list S,
  Id zero (AttnDoeblin.bs_list_sum (fun _ : S => zero) l).
Proof.
  intro l.
  exact (id_trans (id_sym (mult_zero (AttnDoeblin.nat_to_R (length l))))
          (id_sym (AttnDoeblin.bs_list_const_sum zero l))).
Qed.

(* 双重列表和交换（一般形：内外列表分立；Fubini 组合学核心） *)
Lemma abl_lsum_fubini_gen : forall (f : S -> S -> R) (l1 l2 : list S),
  Id (AttnDoeblin.bs_list_sum (fun s : S => AttnDoeblin.bs_list_sum (f s) l2) l1)
     (AttnDoeblin.bs_list_sum (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') l1) l2).
Proof.
  intros f l1. induction l1 as [| x t IH]; intro l2.
  - apply (id_trans (abl_lsum_zero l2)).
    exact (abl_lsum_ext (fun _ : S => zero)
                        (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') nil)
                        l2 (fun s' : S => id_refl)).
  - apply (id_trans (id_cong (fun w : R => plus (AttnDoeblin.bs_list_sum (f x) l2) w)
                             (IH l2))).
    apply (id_sym (abl_lsum_add (fun s' : S => f x s')
              (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') t) l2)).
Qed.

End AblListSum.

(* ################ 段二：swap 族消融主件（E752 段二形） ################
   sum_swap_cc 槽（L154）/bs_swap 槽（L472）在 sum_eq_list 槽（L485，
   已收口槽）+段一组合学下整体导出——swap 位非独立接口位。 *)

Section AblSwap.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Variable enum : list S.
Variable sum_eq_list : forall g : S -> R,
  Id (sum_over_S g) (AttnDoeblin.bs_list_sum g enum).

(* 主件：L154 sum_swap_cc 槽语句逐字形；前提减薄=仅需求和规范化槽 *)
Theorem abl_AtnDoeblin_sum_swap_cc : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Proof.
  intro f.
  apply (id_trans (sum_eq_list (fun s : S => sum_over_S (fun s' : S => f s s')))).
  apply (id_trans (abl_lsum_ext
            (fun s : S => sum_over_S (fun s' : S => f s s'))
            (fun s : S => AttnDoeblin.bs_list_sum (fun s' : S => f s s') enum) enum
            (fun s : S => sum_eq_list (fun s' : S => f s s')))).
  apply (id_trans (abl_lsum_fubini_gen f enum enum)).
  apply (id_trans (id_sym (abl_lsum_ext
            (fun s' : S => sum_over_S (fun s : S => f s s'))
            (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') enum) enum
            (fun s' : S => sum_eq_list (fun s : S => f s s'))))).
  exact (id_sym (sum_eq_list (fun s' : S => sum_over_S (fun s : S => f s s')))).
Qed.

(* 镜像件：L472 bs_swap 槽同语句（N1 双槽镜像，非重复计数） *)
Corollary abl_AtnDoeblin_bs_swap : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Proof.
  exact abl_AtnDoeblin_sum_swap_cc.
Qed.

End AblSwap.

(* ################ 段三：abs 幂等族消融（AbsLeId L50 直喂形） ################
   abs_ge_zero_id_cc 槽（L157）/bs_abs 槽（L475）：AbsLeId 抽象层主件
   直喂（其可判定序扩展槽出节全参化后全闭，先例件在库已验）。 *)

Section AblAbs.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* 主件：L157 abs_ge_zero_id_cc 槽语句逐字形 *)
Theorem abl_AtnDoeblin_abs_ge_zero_id_cc : forall a : R, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  exact (ali_abs_ge_zero_id a Ha).
Qed.

(* 镜像件：L475 bs_abs 槽同语句（N1 双槽镜像） *)
Corollary abl_AtnDoeblin_bs_abs : forall a : R, le zero a -> Id (abs a) a.
Proof.
  exact abl_AtnDoeblin_abs_ge_zero_id_cc.
Qed.

End AblAbs.

(* ################ 收尾：文尾逐件假设面打印（G2 留痕） ################ *)
Print Assumptions abl_lsum_ext.
Print Assumptions abl_lsum_add.
Print Assumptions abl_lsum_zero.
Print Assumptions abl_lsum_fubini_gen.
Print Assumptions abl_AtnDoeblin_sum_swap_cc.
Print Assumptions abl_AtnDoeblin_bs_swap.
Print Assumptions abl_AtnDoeblin_abs_ge_zero_id_cc.
Print Assumptions abl_AtnDoeblin_bs_abs.
