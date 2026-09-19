(* ============================================================ *)
(* UpAblEps49List.v —— AB7 席：4.9 接口族 list 载体升级件             *)
(*   （消融战役补强波，消融 AB3 席报告边界①），2026-09-20              *)
(* ============================================================ *)
(* 【使命（消融 AB3 报告边界①）】                                     *)
(*   AB3 席 e49m_real_kl_decomp_full_bool 以 bool 二点为载体完成       *)
(*   S08 槽真前件形（仅 Hp/Hnormp）的完全放电；其报告边界①指出：       *)
(*   抽象 sumf 上「Σexp>0」不可证（正性保持不在 ext/add/linear 接口内），*)
(*   Zp 内证一般化的唯一障碍=换 list 载体重建。本席执行该重建：         *)
(*   载体=list X 状态表（real_list_sum 折叠，S08 RealListSumMain 形态），*)
(*   四结构前提（求和 ext/add/linear + 配分正性 Zp）全部 list 形内证，  *)
(*   产出主件 e49l_real_kl_decomp_full_list——S08 槽真前件形的          *)
(*   list 载体完全放电实例。                                          *)
(* 【直接材料（消费勿重造）】                                         *)
(*   UpAblEps49RKDBase：rkd_kl_decomp_full_partition 装配链（AB3 私有  *)
(*   字节快照，功归 CWF 席原件）；UpAblZposReal：zabr_sum_over_S_pos   *)
(*   （非空有限和正性折叠链，AB2 交付）；UpReqExpPos：                 *)
(*   upreq_real_zero_ne_one（零壹分离底座）。                          *)
(* 【本席增量（自建非平凡部分）】                                     *)
(*   1. e49l_sumf：list 状态表求和载体（real_list_sum 的接口形包装）。 *)
(*   2. e49l_lsum_ext/_add/_linear：三结构内证 list 形——对任意有限     *)
(*      状态表归纳，收口步型沿 S08 RealListSumMain 同款（compat_adapt   *)
(*      成对拼装 / swap_mid 中点重排 / distrib 反向），把 AB3 的       *)
(*      bool 二点特判一般化为任意有限状态表。                          *)
(*   3. e49l_nonempty_of_norm：归一化⟹非空（AB2 卡第 9 坑范式升级为    *)
(*      独立具名件：Id→real_eq 内联传输桥 + 零壹分离件联合裁决）。      *)
(*   4. e49l_partition_pos：配分正性 list 形——逐项正（exp 恒正）经     *)
(*      AB2 折叠正性链收口，替代 AB3 bool 形的「两支相加」特判，        *)
(*      即边界①所指「Σexp>0 在 list 载体上的可证形」。                 *)
(*   5. 主件 e49l_real_kl_decomp_full_list：S08 槽真前件形（仅 Hp      *)
(*      Hnormp）的 list 载体完全放电实例；结论面与 S08 槽全局形零间隙   *)
(*      （exact 直喂 rkd_kl_decomp_full_partition 即对齐证书）；        *)
(*   6. 伴件 e49l_boltzmann_normalized_list：家族第 2 槽（Σp_b==1）    *)
(*      list 形伴锁（非空前提取 S01 集合层别名，诚实边界申报：list     *)
(*      非恒非空，空表和=零不归一，故显式携 Not (Id l nil)）。          *)
(* 【红线自检】零承认件；纯构造性（零未闭合证明、零经典逻辑）；Set 层  *)
(*   零泄露（语句面全 forall 型，Not/Id 用 S01 集合层别名，real_eq/    *)
(*   real_lt 全 Set 值）；提取零魔术常量；未触碰任何既有文件；         *)
(*   禁入 order.txt/_CoqProject（注册归主会话）。                      *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.
Require Import UpAblEps49RKDBase.
Require Import UpAblZposReal.
Require Import UpReqExpPos.

(* ===== 1. list 状态表求和载体（接口形包装，S08 RealListSumMain 形态） ===== *)
Definition e49l_sumf (X : Set) (l : list X) : (X -> Real) -> Real :=
  fun f => real_list_sum X f l.

(* ===== 2. 结构前提一：外延性（逐点 real_eq ⟹ 求和 real_eq，list 形） ===== *)
Lemma e49l_lsum_ext : forall (X : Set) (l : list X) (f g : X -> Real),
  (forall s : X, real_eq (f s) (g s)) ->
  real_eq (e49l_sumf X l f) (e49l_sumf X l g).
Proof.
  intros X l f g H. unfold e49l_sumf.
  induction l as [| w t IH]; simpl.
  - (* 空表：零 == 零 *)
    apply real_eq_refl.
  - (* 头项逐点换 + 尾和归纳换，compat 成对拼装 *)
    exact (RealSetoid.real_eq_plus_compat_adapt
             (f w) (g w) (real_list_sum X f t) (real_list_sum X g t)
             (H w) IH).
Qed.

(* ===== 3. 结构前提二：加法分配（list 形） ===== *)
Lemma e49l_lsum_add : forall (X : Set) (l : list X) (f g : X -> Real),
  real_eq (e49l_sumf X l (fun s : X => real_plus (f s) (g s)))
          (real_plus (e49l_sumf X l f) (e49l_sumf X l g)).
Proof.
  intros X l f g. unfold e49l_sumf.
  induction l as [| w t IH]; simpl.
  - (* 空表：零 == 零 + 零 *)
    apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
    apply (real_plus_zero real_zero).
  - (* 中点重排：(fw+gw)+(Σf+Σg) == (fw+Σf)+(gw+Σg)，swap_mid 收口 *)
    apply (real_eq_trans _
               (real_plus (real_plus (f w) (g w))
                          (real_plus (real_list_sum X f t)
                                     (real_list_sum X g t))) _).
    + exact (RealSetoid.real_eq_plus_compat_adapt
               (real_plus (f w) (g w)) (real_plus (f w) (g w))
               (real_list_sum X (fun s : X => real_plus (f s) (g s)) t)
               (real_plus (real_list_sum X f t) (real_list_sum X g t))
               (real_eq_refl _) IH).
    + exact (real_plus_swap_mid (f w) (g w)
               (real_list_sum X f t) (real_list_sum X g t)).
Qed.

(* ===== 4. 结构前提三：标量线性（list 形） ===== *)
Lemma e49l_lsum_linear : forall (X : Set) (l : list X) (a : Real) (f : X -> Real),
  real_eq (e49l_sumf X l (fun s : X => real_mult a (f s)))
          (real_mult a (e49l_sumf X l f)).
Proof.
  intros X l a f. unfold e49l_sumf.
  induction l as [| w t IH]; simpl.
  - (* 空表：零 == a·零 *)
    apply (real_eq_sym (real_mult a real_zero) real_zero).
    apply (real_mult_zero a).
  - (* distrib 反向 + 尾和归纳换 *)
    apply (real_eq_trans _
               (real_plus (real_mult a (f w))
                          (real_mult a (real_list_sum X f t))) _).
    + exact (RealSetoid.real_eq_plus_compat_adapt
               (real_mult a (f w)) (real_mult a (f w))
               (real_list_sum X (fun s : X => real_mult a (f s)) t)
               (real_mult a (real_list_sum X f t))
               (real_eq_refl _) IH).
    + apply (real_eq_sym (real_mult a (real_plus (f w) (real_list_sum X f t)))
                         (real_plus (real_mult a (f w))
                                    (real_mult a (real_list_sum X f t)))).
      apply (real_distrib a (f w) (real_list_sum X f t)).
Qed.

(* ===== 5. 归一化⟹非空（AB2 卡第 9 坑范式具名化） ===== *)
(* 空表和可证与零相等（Id→real_eq 传输桥 + iota），与归一化和=一         *)
(* 经零壹分离件联合矛盾。全链集合层别名，零命题面泄露。                  *)
Lemma e49l_nonempty_of_norm : forall (X : Set) (l : list X) (p : X -> Real),
  real_eq (real_list_sum X p l) real_one -> Not (Id l nil).
Proof.
  intros X l p Hnorm Hnil.
  assert (Hsum0 : real_eq (real_list_sum X p l) real_zero).
  { exact (real_eq_trans (real_list_sum X p l) (real_list_sum X p nil)
             real_zero
             (match Hnil in Id _ y return
                real_eq (real_list_sum X p l) (real_list_sum X p y)
              with id_refl => real_eq_refl _ end)
             (real_eq_refl real_zero)). }
  exact (upreq_real_zero_ne_one
          (real_eq_trans real_zero (real_list_sum X p l) real_one
             (real_eq_sym (real_list_sum X p l) real_zero Hsum0) Hnorm)).
Qed.

(* ===== 6. 配分正性（list 形）＝边界①所指「Σexp>0」的可证形 ===== *)
(* 逐项正（real_exp_neg_pos 恒正链，S03 cauchy_real_exp_pos 现态）      *)
(* 经 AB2 折叠正性链 zabr_sum_over_S_pos 收口；非空前提取 S01 集合层。  *)
Lemma e49l_partition_pos : forall (X : Set) (l : list X) (Hnn : Not (Id l nil))
  (e : X -> Real) (D : Real) (D_pos : real_lt real_zero D),
  real_lt real_zero
    (real_list_sum X (fun s : X => real_exp_neg
                         (real_mult (real_inv_pos D D_pos) (e s))) l).
Proof.
  intros X l Hnn e D D_pos.
  apply (zabr_sum_over_S_pos X
           (fun s : X => real_exp_neg
                          (real_mult (real_inv_pos D D_pos) (e s))) l).
  - exact Hnn.
  - intro s. apply real_exp_neg_pos.
Qed.

(* ===== 7. 主件：S08 槽真前件形（仅 Hp/Hnormp）list 载体完全放电实例 ===== *)
(* 载体全 concrete：S := X（任意有限状态表）、sumf := e49l_sumf X l      *)
(* （三结构内证见 2–4）、Z := Σexp(−e/D) 配分定义形（正性内证见 5–6，    *)
(* 非空性由 Hnormp 内导）。前提面与 S08:2527 槽逐字同形；结论面与 S08    *)
(* 槽全局形零间隙（exact 直喂 rkd_kl_decomp_full_partition 即对齐证书）。 *)
Theorem e49l_real_kl_decomp_full_list :
  forall (X : Set) (l : list X)
    (e : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
    (Hnormp : real_eq (real_list_sum X p l) real_one),
  real_eq (real_free_energy X (e49l_sumf X l) e D p Hp)
          (real_plus
             (real_free_energy X (e49l_sumf X l) e D
                (real_boltzmann_dist_r X e D D_pos
                   (real_list_sum X (fun s : X => real_exp_neg
                                        (real_mult (real_inv_pos D D_pos) (e s))) l)
                   (e49l_partition_pos X l (e49l_nonempty_of_norm X l p Hnormp)
                      e D D_pos))
                (real_boltzmann_dist_r_pos X e D D_pos
                   (real_list_sum X (fun s : X => real_exp_neg
                                        (real_mult (real_inv_pos D D_pos) (e s))) l)
                   (e49l_partition_pos X l (e49l_nonempty_of_norm X l p Hnormp)
                      e D D_pos)))
             (real_mult D
                (e49l_sumf X l (fun s : X =>
                   real_kl_term (p s)
                     (real_boltzmann_dist_r X e D D_pos
                        (real_list_sum X (fun s0 : X => real_exp_neg
                                             (real_mult (real_inv_pos D D_pos) (e s0))) l)
                        (e49l_partition_pos X l (e49l_nonempty_of_norm X l p Hnormp)
                           e D D_pos) s)
                     (Hp s)
                     (real_boltzmann_dist_r_pos X e D D_pos
                        (real_list_sum X (fun s0 : X => real_exp_neg
                                             (real_mult (real_inv_pos D D_pos) (e s0))) l)
                        (e49l_partition_pos X l (e49l_nonempty_of_norm X l p Hnormp)
                           e D D_pos) s))))).
Proof.
  intros X l e D D_pos p Hp Hnormp.
  exact (rkd_kl_decomp_full_partition X (e49l_sumf X l)
           (e49l_lsum_ext X l) (e49l_lsum_add X l) (e49l_lsum_linear X l)
           e D D_pos p Hp Hnormp
           (e49l_partition_pos X l (e49l_nonempty_of_norm X l p Hnormp)
              e D D_pos)).
Qed.

(* ===== 8. 伴件：家族第 2 槽（Σp_b==1）list 形伴锁 ===== *)
(* Z 取配分定义形，Hpart 逐字自反（real_eq_refl）；归一化 Σp_b == 1      *)
(* 内证（消费 rkd_boltzmann_normalized）。诚实边界申报：list 非恒非空，  *)
(* 空表和=零不归一，故显式携非空前提取 S01 集合层别名（零命题面泄露）。  *)
Theorem e49l_boltzmann_normalized_list :
  forall (X : Set) (l : list X) (Hnn : Not (Id l nil))
    (e : X -> Real) (D : Real) (D_pos : real_lt real_zero D),
  real_eq
    (real_list_sum X
       (real_boltzmann_dist_r X e D D_pos
          (real_list_sum X (fun s : X => real_exp_neg
                               (real_mult (real_inv_pos D D_pos) (e s))) l)
          (e49l_partition_pos X l Hnn e D D_pos)) l)
    real_one.
Proof.
  intros X l Hnn e D D_pos.
  exact (rkd_boltzmann_normalized X (e49l_sumf X l)
           (e49l_lsum_ext X l) (e49l_lsum_linear X l) e D D_pos
           (real_list_sum X (fun s : X => real_exp_neg
                                (real_mult (real_inv_pos D D_pos) (e s))) l)
           (e49l_partition_pos X l Hnn e D D_pos)
           (real_eq_refl _)).
Qed.

(* ===== 证据区：零外部未证假设 + 独立目录提取（一人一目录） ===== *)
Print Assumptions e49l_lsum_ext.
Print Assumptions e49l_lsum_add.
Print Assumptions e49l_lsum_linear.
Print Assumptions e49l_nonempty_of_norm.
Print Assumptions e49l_partition_pos.
Print Assumptions e49l_real_kl_decomp_full_list.
Print Assumptions e49l_boltzmann_normalized_list.

From Stdlib Require Import Extraction.
Set Extraction Output Directory "../_ab7_list_extract".
(* 单条命令合并提取全部八件（多条 Separate Extraction 各自重写模块文件， *)
(*   仅存末条闭包——AB3 席同款坑，本席合并规避）。                        *)
Separate Extraction e49l_sumf e49l_lsum_ext e49l_lsum_add e49l_lsum_linear
  e49l_nonempty_of_norm e49l_partition_pos
  e49l_real_kl_decomp_full_list e49l_boltzmann_normalized_list.
