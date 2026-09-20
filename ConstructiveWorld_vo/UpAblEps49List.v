(* ============================================================ *)
(* UpAblEps49List.v —— KL 分解（定理 4.9）接口族的 list 载体版本：              *)
(* 有限状态表上的完全实例。                                                  *)
(*                                                               *)
(* 使命：bool 二点实例 e49m_real_kl_decomp_full_bool 完成了 S08 假设形        *)
(*   （仅 Hp、Hnormp）的实例化；其适用边界指出：抽象 sumf 上「Σexp 为正」                *)
(*   不可证（正性保持不在 ext/add/linear 接口内），将 Zp 内证一般化的                  *)
(*   途径即改用 list 载体重建。本件执行该重建：载体 = list X 状态表                     *)
(*   （real_list_sum 折叠，S08 RealListSumMain 形态），四结构前提             *)
(*   （求和 ext/add/linear + 配分正性 Zp）全部以 list 形内证，产出主件              *)
(*   e49l_real_kl_decomp_full_list——S08 假设形的 list 载体完全实例。        *)
(*                                                               *)
(* 使用清单：UpAblEps49RKDBase 的 rkd_kl_decomp_full_partition；        *)
(*   UpAblZposReal 的 zabr_sum_over_S_pos（非空有限和正性折叠引理）；           *)
(*   UpReqExpPos 的 upreq_real_zero_ne_one（零壹分离）。                 *)
(*                                                               *)
(* 内容：§1 求和载体 e49l_sumf（real_list_sum 的接口形包装）；                   *)
(*   §2–§4 三结构前提的 list 形内证（对任意有限状态表归纳，收尾步沿                       *)
(*   S08 RealListSumMain 同款：real_eq_plus_compat_adapt 成对使用、      *)
(*   real_plus_swap_mid 中点重排、real_distrib 逆向），把 bool 二点          *)
(*   特判一般化为任意有限状态表；§5 归一化⟹非空（Id 到 real_eq 的                      *)
(*   传输 + 零壹分离 upreq_real_zero_ne_one 联合排除空表）；§6 配分              *)
(*   正性 list 形（逐项正经 zabr_sum_over_S_pos 收尾）；§7 主件；               *)
(*   §8 伴件（Boltzmann 归一化 list 形）。                                *)
(*                                                               *)
(* 适用边界（§8）：list 不恒非空，空表之和为零不归一，故归一化命题                           *)
(*   显式携非空前提 Not (Id l nil)。                                     *)
(*                                                               *)
(* 构造性注记：零承认；纯构造性；Set 层承载（语句面全 forall 型，                         *)
(*   Not/Id 用 S01 集合层别名，real_eq/real_lt 全 Set 值）；提取零             *)
(*   魔术常量。                                                       *)
(*                                                               *)
(* 依赖：CW_ConstructiveWorld_219、UpAblEps49RKDBase、UpAblZposReal、  *)
(*   UpReqExpPos、Stdlib QArith.Qring。                            *)
(*                                                               *)
(* 对标：mathlib 有限表求和的正性与归一化引理（List.sum 系）。                        *)
(* 编译配方：Rocq 9.1 直调 + cpu_guard；                                 *)
(*   编译输出 -o 临时目录，树内 .vo 不动。                                     *)
(*                                                               *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.
Require Import UpAblEps49RKDBase.
Require Import UpAblZposReal.
Require Import UpReqExpPos.

(* §1 list 状态表求和载体（real_list_sum 的接口形，S08 RealListSumMain 形态）    *)
Definition e49l_sumf (X : Set) (l : list X) : (X -> Real) -> Real :=
  fun f => real_list_sum X f l.

(* §2 结构前提一：外延性（逐点 real_eq ⟹ 求和 real_eq，list 形）                  *)
Lemma e49l_lsum_ext : forall (X : Set) (l : list X) (f g : X -> Real),
  (forall s : X, real_eq (f s) (g s)) ->
  real_eq (e49l_sumf X l f) (e49l_sumf X l g).
Proof.
  intros X l f g H. unfold e49l_sumf.
  induction l as [| w t IH]; simpl.
  - (* 空表：零 == 零 *)
    apply real_eq_refl.
  - (* 头项逐点换 + 尾和归纳换，real_eq_plus_compat_adapt 成对使用                  *)
    exact (RealSetoid.real_eq_plus_compat_adapt
             (f w) (g w) (real_list_sum X f t) (real_list_sum X g t)
             (H w) IH).
Qed.

(* §3 结构前提二：加法分配（list 形）                                         *)
Lemma e49l_lsum_add : forall (X : Set) (l : list X) (f g : X -> Real),
  real_eq (e49l_sumf X l (fun s : X => real_plus (f s) (g s)))
          (real_plus (e49l_sumf X l f) (e49l_sumf X l g)).
Proof.
  intros X l f g. unfold e49l_sumf.
  induction l as [| w t IH]; simpl.
  - (* 空表：零 == 零 + 零 *)
    apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
    apply (real_plus_zero real_zero).
  - (* 中点重排：(fw+gw)+(Σf+Σg) == (fw+Σf)+(gw+Σg)，real_plus_swap_mid 收尾 *)
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

(* §4 结构前提三：标量线性（list 形）                                         *)
Lemma e49l_lsum_linear : forall (X : Set) (l : list X) (a : Real) (f : X -> Real),
  real_eq (e49l_sumf X l (fun s : X => real_mult a (f s)))
          (real_mult a (e49l_sumf X l f)).
Proof.
  intros X l a f. unfold e49l_sumf.
  induction l as [| w t IH]; simpl.
  - (* 空表：零 == a·零 *)
    apply (real_eq_sym (real_mult a real_zero) real_zero).
    apply (real_mult_zero a).
  - (* real_distrib 逆向 + 尾和归纳换                                       *)
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

(* §5 归一化⟹非空（独立具名引理）                                             *)
(* 空表之和可证与零相等（Id 到 real_eq 的传输 + iota 简约），与归一化和为一                *)
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

(* §6 配分正性（list 形）：「Σexp>0」的可证形                                  *)
(* 逐项正（real_exp_neg_pos 恒正链，S03 cauchy_real_exp_pos）             *)
(* 经折叠正性引理 zabr_sum_over_S_pos 收尾；非空前提以 S01 集合层别名表达。             *)
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

(* §7 主件：S08 假设形（仅 Hp、Hnormp）在 list 载体上的完全实例                     *)
(* 载体全具体：S := X（任意有限状态表）、sumf := e49l_sumf X l                   *)
(* （三结构前提内证见 §2–§4）、Z := Σexp(−e/D) 配分定义形（正性内证见 §5–§6，           *)
(* 非空性由 Hnormp 内导）。前提与 S08 原假设逐字同形；结论与 S08 假设                    *)
(* 全局形逐字同构（证明体 exact 直引 rkd_kl_decomp_full_partition）。           *)
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

(* §8 伴件：家族第 2 假设（Σ p_b == 1）的 list 形伴生命题                        *)
(* Z 取配分定义形，Hpart 为 real_eq_refl；归一化 Σ p_b == 1 内证               *)
(* （使用 rkd_boltzmann_normalized）。适用边界：list 不恒非空，空表之和             *)
(* 为零不归一，故显式携非空前提（S01 集合层别名，零命题面泄露）。                             *)
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

(* 依赖审计：零外部未证假设；独立目录提取                                           *)
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
(* 仅存末条的闭包，故合并为一条命令）。                                            *)
Separate Extraction e49l_sumf e49l_lsum_ext e49l_lsum_add e49l_lsum_linear
  e49l_nonempty_of_norm e49l_partition_pos
  e49l_real_kl_decomp_full_list e49l_boltzmann_normalized_list.
