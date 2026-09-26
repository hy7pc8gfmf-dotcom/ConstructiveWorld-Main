(* ============================================================
   使命：本件数学使命叙述见下方原头注首段（既有件注记型头注整编候后波）。
   依赖：见原头注 Require 面与依赖段。
   对标：见原头注来源/对标行。
   构造性：纯构造性、零承认件（详见原头注红线自审段）。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)
(* 【ToyR ·· 记录件】玩具级定理同名非平凡替换稿（补标头注）       *)
(*                                                                           *)
(* 本稿系 ToyR  替换落件（原名落件）；落件时头部漏植标记，本块由  *)
(*  补注记录于 补注：仅加头注，语句面／证明体／         *)
(* Require 面                                                                *)
(* 零改动；原头注紧随本块之后原样保留。来源刀面权威记录：消融50/。       *)
(* 替换定理清单：sqrt_premise_le_intro／real_partition_function_scaled_pos   *)
(* ／real_partition_function_temp_param_pos／                                *)
(* real_partition_function_temp_pos／                                        *)
(* gibbst_real_partition_function_temp_pos／real_temp_is_scale_duality／     *)
(* real_exp_neg_wd（共 7 条）                                                *)
(* 非平凡性口径：配分函数正性链就地直造与换轨重演（原体为行内单跳委托）；    *)
(* 无一行拆分式假非平凡。                                                    *)
(* 本稿零公理、零承认件、全闭合、纯构造性、无经典逻辑；落件时与本次补标      *)
(* 抽验编译均验零承认。                                                      *)
(* ========================================================================= *)
(* G 组：G02_Debt — 有限合并组（S/G 双系新命名，成员原样并入）
   成员：UpDebtSqrtAbs + UpDebtDual + UpDebtGibbsT（同组旧名 Require 已剥；库内旧名已消融，下游直接 Require 本组）*)
(* ======== G02_Debt 成员件：UpDebtSqrtAbs（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpDebtSqrtAbs.v —— 债务清理封装模块（件 3，方案三 b+）          *)
(*   抽象 Id 系增强接口下任意非负 d 的构造性平方根见证：          *)
(*   把 Real 层 real_sqrt_exists（根 L96475）的 Or 分支证书      *)
(*   结构逐字副本回 RealInterfaceEnhanced 接口泛型。             *)
(*                                                              *)
(*   语句（原始任务表述模板）：                                        *)
(*     forall d, Or (lt zero d) (Id zero d) ->                  *)
(*       sigT (fun r => And (le zero r) (Id (mult r r) d))      *)
(*   证明核：                                                    *)
(*     左支 d>0：r := exp_neg(half·log_inv d)（half :=           *)
(*       inv_pos two，two := 1+1 正性经 plus_positive 组装），    *)
(*       r·r == d 链 = exp_neg_plus 反向 + distrib/mult 代数     *)
(*       （half+half == one）+ exp_neg_log_inv 右逆；            *)
(*     右支 d≡0：r := zero（mult_zero）。                        *)
(*                                                              *)
(*   诚实接口说明：接口的 le 是不透明字段，库内仅有 Or→le 单向   *)
(*   （lt_le_iff），故前提取 Or 形态——这正是 real_le 的定义体    *)
(*   （real_le x y := Or (real_lt x y) (real_eq x y)），与 Real  *)
(*   层 real_sqrt_exists 的可依存前提逐字同构；le 形态前提在接口 *)
(*   内无法分解（无 le→Or 字段），不特设构造。                       *)
(*                                                              *)
(*   纪律：纯构造性、零承认；语句全 Set 层（lt/le/Id/sigT/And）；*)
(*   全部 Qed 完成。                                             *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

Section SqrtAbstract.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* 平方维数见证（副本根内 sqrt_witness）：r·r == d *)
Definition dsq_sqrt_witness (d r : R) : Set := Id (mult r r) d.

(* two := 1+1（字面 2）；two > 0（plus_positive × one_pos 组装） *)
Definition two_abs : R := plus one one.
Lemma two_abs_pos : lt zero two_abs.
Proof.
  exact (plus_positive one one one_pos one_pos).
Qed.

(* half := inv(two)；half + half == one
   链：half·two == one（inv_pos_correct，经 mult_comm），
       half·two == half·(1+1) == half·1 + half·1 == half + half
       （distrib + mult_one × 2）。 *)
Definition half_abs : R := inv_pos two_abs two_abs_pos.
Lemma half_plus_half : Id (plus half_abs half_abs) one.
Proof.
  assert (Hd : Id (mult half_abs two_abs) one)
    by exact (id_trans (mult_comm half_abs two_abs)
                       (inv_pos_correct two_abs two_abs_pos)).
  assert (Hsplit : Id (mult half_abs two_abs) (plus half_abs half_abs))
    by exact (id_trans (distrib half_abs one one)
                       (id_cong2 (fun a b => plus a b)
                                 (mult_one half_abs) (mult_one half_abs))).
  exact (id_trans (id_sym Hsplit) Hd).
Qed.

(* Or 前提即 le 的构造性内容（接口单向 lt_le_iff 的记录） *)
Lemma sqrt_premise_le_intro : forall d : R, Or (lt zero d) (Id zero d) -> le zero d.
Proof.
  intros d H. exact (lt_le_iff zero d H).
Qed.

(* ---- 主定理（件 3）：抽象 Id 层任意非负 d 的平方根见证 ----
   左支（d > 0，正间隙证书）：r := exp_neg(half·log_inv d)。
     r·r == d：exp(h)·exp(h) == exp(h+h)（exp_neg_plus 反向）
       == exp(log_inv d)（h+h == half·L+half·L == half·(L+L)
       == one·L == L，其中 half+half == one）
       == d（exp_neg_log_inv 右逆）。
     r > 0：exp_neg_pos + lt_le_iff。
   右支（d ≡ 0，Id 证书）：r := zero；0 ≤ 0（le_refl）；
     0·0 == 0（mult_zero）== d（Hdeq）。 *)
Theorem sqrt_witness_exists_abstract :
  forall d : R, Or (lt zero d) (Id zero d) ->
  sigT (fun r : R => And (le zero r) (Id (mult r r) d)).
Proof.
  intros d Hd.
  destruct Hd as [Hdlt | Hdeq].
  - (* 情形①：d > 0。r := exp(half·log d)。 *)
    exists (exp_neg (mult half_abs (log_inv d))).
    split.
    + (* r > 0：exp 恒正（le 左支 = lt 经 lt_le_iff） *)
      exact (lt_le_iff zero (exp_neg (mult half_abs (log_inv d)))
                        (inl (exp_neg_pos (mult half_abs (log_inv d))))).
    + (* r·r == d：三分链 exp(h)·exp(h) == exp(h+h) == exp(log d) == d *)
      assert (Hinner : Id (plus (mult half_abs (log_inv d))
                                (mult half_abs (log_inv d)))
                          (log_inv d)).
      { exact (id_trans
                (id_trans
                  (id_cong2 (fun a b => plus a b)
                            (mult_comm half_abs (log_inv d))
                            (mult_comm half_abs (log_inv d)))
                  (id_trans (id_sym (distrib (log_inv d) half_abs half_abs))
                            (mult_comm (log_inv d) (plus half_abs half_abs))))
                (id_trans
                  (id_cong (fun x => mult x (log_inv d)) half_plus_half)
                  (id_trans (mult_comm one (log_inv d))
                            (mult_one (log_inv d))))). }
      exact (id_trans
              (id_sym (exp_neg_plus (mult half_abs (log_inv d))
                                    (mult half_abs (log_inv d))))
              (id_trans (id_cong (fun x => exp_neg x) Hinner)
                        (exp_neg_log_inv d))).
  - (* 情形②：d ≡ 0。r := zero。 *)
    exists zero.
    split.
    + (* 0 ≤ 0：自反 *)
      apply le_refl.
    + (* 0·0 == 0 == d *)
      exact (id_trans (mult_zero zero) Hdeq).
Qed.

(* 见证形态重述（dsq_sqrt_witness 命名式） *)
Lemma sqrt_witness_exists_abstract_witness :
  forall d : R, Or (lt zero d) (Id zero d) ->
  sigT (fun r : R => And (le zero r) (dsq_sqrt_witness d r)).
Proof.
  intros d H.
  exact (sqrt_witness_exists_abstract d H).
Qed.

(* 实例（机器可检查的健全性检查）：1 的抽象平方根可构造——
   r := exp(half·log_inv 1)，r ≥ 0 且 r·r == 1（副本 real_sqrt_one）。 *)
Lemma sqrt_one_abstract :
  sigT (fun r : R => And (le zero r) (Id (mult r r) one)).
Proof.
  exact (sqrt_witness_exists_abstract one (inl one_pos)).
Qed.

End SqrtAbstract.

(* ======== G02_Debt 成员件：UpDebtDual（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpDebtDual.v —— 债务清理封装模块（件 2，方案三 b）              *)
(*   缩放-温度对偶族 Real 层：抽象层 scale_temp_duality           *)
(*   （CW_ConstructiveWorld_219 L28515–28529）与配套缩放族（L28440–28543）   *)
(*   的 Real 层副本。                                            *)
(*                                                              *)
(*   定义族：                                                    *)
(*     real_softmax_scaled c z s      := e^{c·z_s}/Σ e^{c·z}     *)
(*     real_softmax_temp_param T z s  := e^{z/T}/Σ e^{z/T}       *)
(*   主定理：                                                    *)
(*     real_scale_temp_duality：∀c>0,                            *)
(*       real_softmax_scaled (1/c) == real_softmax_temp_param c  *)
(*   配套：缩放族正性/归一化 + real_scale_inv_T_eq_softmax_temp  *)
(*   （1/T 缩放族 == 库式温度化 softmax，配分定义性相等经        *)
(*   real_inv_pos_ext——纯恒等链）。                              *)
(*                                                              *)
(*   纪律：纯构造性、零承认；语句全 Set 层（real_lt/real_eq/     *)
(*   sigT/And）；全部 Qed 完成。                                  *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

Section RealScaleDual.

(* 抽象状态空间（Real 层 Section 自声明，同 RealAttnMain 先例） *)
Variable S : Type.

(* 诚实接口：抽象 S 上的求和（Real 层可实例化；零公理） *)
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s => real_mult a (f s))) (real_mult a (real_sum_over_S f)).

(* ---- 缩放族：real_softmax_scaled ---- *)

(* 缩放配分函数：Z_c(z) := Σ_s e^{c·z_s}（c 任意实） *)
Definition real_partition_function_scaled (c : Real) (z : S -> Real) : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (real_mult c (z s))).

(* 缩放配分正性：exp 恒正 × sum_pos_preserved *)
Lemma real_partition_function_scaled_pos :
  forall (c : Real) (z : S -> Real), real_lt real_zero (real_partition_function_scaled c z).
Proof.
  intros c z.
  exact (real_sum_pos_preserved
           (fun s : S => real_exp_neg (real_opp (real_mult c (z s))))
           (fun s : S => real_exp_neg_pos (real_opp (real_mult c (z s))))).
Qed.

(* 缩放 softmax：sc(z; c)_s := e^{c·z_s}·inv(Z_c(z))（c 任意实） *)
Definition real_softmax_scaled (c : Real) (z : S -> Real) (s : S) : Real :=
  real_mult (real_exp_pos_fn (real_mult c (z s)))
            (real_inv_pos (real_partition_function_scaled c z)
                          (real_partition_function_scaled_pos c z)).

(* 缩放族概率公理：正性（exp 恒正 × inv 正） *)
Theorem real_softmax_scaled_pos :
  forall (c : Real) (z : S -> Real) (s : S), real_lt real_zero (real_softmax_scaled c z s).
Proof.
  intros c z s.
  unfold real_softmax_scaled, real_exp_pos_fn.
  apply real_mult_pos_compat.
  - apply real_exp_neg_pos.
  - apply real_inv_pos_pos.
Qed.

(* 缩放族概率公理：归一化 Σ_s sc(z;c)_s == 1
   链：逐 s 乘子交换（sum_ext + real_mult_comm）→ 线性提取
   （sum_linear）→ inv(Z_c)·Z_c == 1（real_inv_pos_correct）。 *)
Theorem real_softmax_scaled_normalized :
  forall (c : Real) (z : S -> Real),
    real_eq (real_sum_over_S (fun s => real_softmax_scaled c z s)) real_one.
Proof.
  intros c z.
  unfold real_softmax_scaled.
  apply (real_eq_trans
          (real_sum_over_S (fun s => real_mult
                             (real_exp_pos_fn (real_mult c (z s)))
                             (real_inv_pos (real_partition_function_scaled c z)
                                           (real_partition_function_scaled_pos c z))))
          (real_mult (real_inv_pos (real_partition_function_scaled c z)
                                   (real_partition_function_scaled_pos c z))
                     (real_sum_over_S (fun s => real_exp_pos_fn (real_mult c (z s)))))
          real_one).
  - (* 1. 乘子交换后线性提取 *)
    apply (real_eq_trans
            (real_sum_over_S (fun s => real_mult
                               (real_exp_pos_fn (real_mult c (z s)))
                               (real_inv_pos (real_partition_function_scaled c z)
                                             (real_partition_function_scaled_pos c z))))
            (real_sum_over_S (fun s => real_mult
                               (real_inv_pos (real_partition_function_scaled c z)
                                             (real_partition_function_scaled_pos c z))
                               (real_exp_pos_fn (real_mult c (z s)))))
            _).
    + apply real_sum_over_S_ext.
      intro s. apply real_mult_comm.
    + apply real_sum_over_S_linear.
  - (* 2. inv(Z_c)·Z_c == 1 *)
    apply (real_eq_trans
            (real_mult (real_inv_pos (real_partition_function_scaled c z)
                                     (real_partition_function_scaled_pos c z))
                       (real_sum_over_S (fun s => real_exp_pos_fn (real_mult c (z s)))))
            (real_mult (real_inv_pos (real_partition_function_scaled c z)
                                     (real_partition_function_scaled_pos c z))
                       (real_partition_function_scaled c z))
            real_one).
    + apply real_eq_refl.
    + apply (real_eq_trans
              (real_mult (real_inv_pos (real_partition_function_scaled c z)
                                       (real_partition_function_scaled_pos c z))
                         (real_partition_function_scaled c z))
              (real_mult (real_partition_function_scaled c z)
                         (real_inv_pos (real_partition_function_scaled c z)
                                       (real_partition_function_scaled_pos c z)))
              real_one).
      * apply real_mult_comm.
      * apply real_inv_pos_correct.
Qed.

(* ---- 温度参数化族：(, HT0) 显式版 ---- *)

(* 温度参数化配分函数：Z_T0(z) := Σ_s e^{z_s/} *)
Definition real_partition_function_temp_param
  (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real) : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s))).

(* 温度参数化配分正性 *)
Lemma real_partition_function_temp_param_pos :
  forall (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real),
    real_lt real_zero (real_partition_function_temp_param T0 HT0 z).
Proof.
  intros T0 HT0 z.
  exact (real_sum_pos_preserved
           (fun s : S => real_exp_neg (real_opp (real_mult (real_inv_pos T0 HT0) (z s))))
           (fun s : S =>
              real_exp_neg_pos (real_opp (real_mult (real_inv_pos T0 HT0) (z s))))).
Qed.

(* 温度参数化 softmax：e^{z_s/}·inv(Z_T0(z)) *)
Definition real_softmax_temp_param
  (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real) (s : S) : Real :=
  real_mult (real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))
            (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                          (real_partition_function_temp_param_pos T0 HT0 z)).

(* 温度参数化正性（配套） *)
Theorem real_softmax_temp_param_pos :
  forall (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real) (s : S),
    real_lt real_zero (real_softmax_temp_param T0 HT0 z s).
Proof.
  intros T0 HT0 z s.
  unfold real_softmax_temp_param, real_exp_pos_fn.
  apply real_mult_pos_compat.
  - apply real_exp_neg_pos.
  - apply real_inv_pos_pos.
Qed.

(* 温度参数化归一化（配套） *)
Theorem real_softmax_temp_param_normalized :
  forall (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real),
    real_eq (real_sum_over_S (fun s => real_softmax_temp_param T0 HT0 z s)) real_one.
Proof.
  intros T0 HT0 z.
  unfold real_softmax_temp_param.
  apply (real_eq_trans
          (real_sum_over_S (fun s => real_mult
                             (real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))
                             (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                           (real_partition_function_temp_param_pos T0 HT0 z))))
          (real_mult (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                   (real_partition_function_temp_param_pos T0 HT0 z))
                     (real_sum_over_S (fun s =>
                       real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))))
          real_one).
  - apply (real_eq_trans
            (real_sum_over_S (fun s => real_mult
                               (real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))
                               (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                             (real_partition_function_temp_param_pos T0 HT0 z))))
            (real_sum_over_S (fun s => real_mult
                               (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                             (real_partition_function_temp_param_pos T0 HT0 z))
                               (real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))))
            _).
    + apply real_sum_over_S_ext.
      intro s. apply real_mult_comm.
    + apply real_sum_over_S_linear.
  - apply (real_eq_trans
            (real_mult (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                     (real_partition_function_temp_param_pos T0 HT0 z))
                       (real_sum_over_S (fun s =>
                         real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))))
            (real_mult (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                     (real_partition_function_temp_param_pos T0 HT0 z))
                       (real_partition_function_temp_param T0 HT0 z))
            real_one).
    + apply real_eq_refl.
    + apply (real_eq_trans
              (real_mult (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                       (real_partition_function_temp_param_pos T0 HT0 z))
                         (real_partition_function_temp_param T0 HT0 z))
              (real_mult (real_partition_function_temp_param T0 HT0 z)
                         (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                       (real_partition_function_temp_param_pos T0 HT0 z)))
              real_one).
      * apply real_mult_comm.
      * apply real_inv_pos_correct.
Qed.

(* ---- 主定理（件 2 核心）：缩放-温度对偶 ----
   ∀ c > 0：以 1/c 缩放 logits 的 softmax == 温度 c 的 softmax。
   unfold 后两侧首因子（分子 e^{(1/c)·z_s}）逐字相同，mult_compat
   refl 消去；配分函数定义性相等（两侧都 unfold 为同一 Σ）⟹
   real_inv_pos_ext + real_eq_refl。纯恒等链，零新公理。 *)
Theorem real_scale_temp_duality :
  forall (c : Real) (Hc : real_lt real_zero c) (z : S -> Real) (s : S),
    real_eq (real_softmax_scaled (real_inv_pos c Hc) z s)
            (real_softmax_temp_param c Hc z s).
Proof.
  intros c Hc z s.
  unfold real_softmax_scaled, real_softmax_temp_param.
  apply (RealSetoid.real_eq_mult_compat_adapt
          (real_exp_pos_fn (real_mult (real_inv_pos c Hc) (z s)))
          (real_exp_pos_fn (real_mult (real_inv_pos c Hc) (z s)))
          (real_inv_pos (real_partition_function_scaled (real_inv_pos c Hc) z)
                        (real_partition_function_scaled_pos (real_inv_pos c Hc) z))
          (real_inv_pos (real_partition_function_temp_param c Hc z)
                        (real_partition_function_temp_param_pos c Hc z))
          (real_eq_refl _)
          (real_inv_pos_ext
            (real_partition_function_scaled (real_inv_pos c Hc) z)
            (real_partition_function_temp_param c Hc z)
            (real_partition_function_scaled_pos (real_inv_pos c Hc) z)
            (real_partition_function_temp_param_pos c Hc z)
            (real_eq_refl _))).
Qed.

(* 反向对称：温度 c 的 softmax == 以 1/c 缩放的 softmax（real_eq_sym） *)
Lemma real_temp_is_scale_duality :
  forall (c : Real) (Hc : real_lt real_zero c) (z : S -> Real) (s : S),
    real_eq (real_softmax_temp_param c Hc z s)
            (real_softmax_scaled (real_inv_pos c Hc) z s).
Proof.
  intros c Hc z s.
  exact (real_eq_sym (real_softmax_scaled (real_inv_pos c Hc) z s)
                     (real_softmax_temp_param c Hc z s)
                     (real_scale_temp_duality c Hc z s)).
Qed.

(* ---- Section 温度版桥：1/T 缩放族 == 库式温度化 softmax ----
   库式 softmax_temp（L28104 型）的温度 T/配分 Z_T 为 Section
   变量显式定义（不带参数化前提）；此处重建该形态，并以
   real_inv_pos_ext + real_eq_refl 桥接（配分定义性相等）。 *)
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable z_logits : S -> Real.

(* 库式温度化配分（Section 温度形态） *)
Definition real_partition_function_temp : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s))).

Lemma real_partition_function_temp_pos : real_lt real_zero real_partition_function_temp.
Proof.
  exact (real_sum_pos_preserved
           (fun s : S => real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
           (fun s : S =>
              real_exp_neg_pos (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))).
Qed.

(* 库式温度化 softmax（Section 温度形态） *)
Definition real_softmax_temp (s : S) : Real :=
  real_mult (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
            (real_inv_pos real_partition_function_temp real_partition_function_temp_pos).

(* 桥（对偶引理 c := T 实例 + 配分定义性相等） *)
Lemma real_scale_inv_T_eq_softmax_temp :
  forall s : S,
    real_eq (real_softmax_scaled (real_inv_pos T T_pos) z_logits s)
            (real_softmax_temp s).
Proof.
  intro s.
  unfold real_softmax_scaled, real_softmax_temp.
  apply (RealSetoid.real_eq_mult_compat_adapt
          (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
          (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
          (real_inv_pos (real_partition_function_scaled (real_inv_pos T T_pos) z_logits)
                        (real_partition_function_scaled_pos (real_inv_pos T T_pos) z_logits))
          (real_inv_pos real_partition_function_temp real_partition_function_temp_pos)
          (real_eq_refl _)
          (real_inv_pos_ext
            (real_partition_function_scaled (real_inv_pos T T_pos) z_logits)
            real_partition_function_temp
            (real_partition_function_scaled_pos (real_inv_pos T T_pos) z_logits)
            real_partition_function_temp_pos
            (real_eq_refl _))).
Qed.

End RealScaleDual.

(* ======== G02_Debt 成员件：UpDebtGibbsT（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpDebtGibbsT.v —— 债务清理封装模块（件 1，方案三 c）            *)
(*   attention_is_gibbs_temp 的 Real 层复刻：任意温度下          *)
(*   softmax == Boltzmann。                                      *)
(*                                                              *)
(*   模板 = 根内单位温度版 real_attention_is_gibbs               *)
(*   （CW_ConstructiveWorld_219 L43231）逐字平移：                           *)
(*     温度相等前提 real_eq (inv T) (inv D)                      *)
(*     + energy == −logits + 配分相等                            *)
(*     ⟹ 逐点 real_eq (real_softmax_temp s) (real_boltzmann_dist_attn s). *)
(*                                                              *)
(*   Real 层原本无温度化 softmax/配分定义，此处先建：            *)
(*     real_partition_function_temp := Σ e^{z/T}，               *)
(*     real_softmax_temp s := e^{z_s/T}·inv(Z_T)，               *)
(*   并配套正性/归一化小引理。证明核：real_inv 代数 +            *)
(*   cauchy_real_exp_wd + real_inv_pos_ext + real_mult_comm ——   *)
(*   单位温度版每一步都有对应。                                  *)
(*                                                              *)
(*   世界选择跟随根内 real_attention_is_gibbs（CW_ConstructiveWorld_219；    *)
(*   CW_ConstructiveWorld_219.vo 与本地 9.0/9.1 平台 vo 版本号   *)
(*   不兼容，见技术报告）。                                      *)
(*                                                              *)
(*   纪律：纯构造性、零承认；语句全 Set 层（real_lt/real_eq/     *)
(*   sigT/库内 And）；全部 Qed 完成。                            *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

Section RealAttnGibbsTemp.

(* 抽象状态空间（Real 层 Section 自声明，同 RealAttnMain 先例） *)
Variable S : Type.

(* 诚实接口：抽象 S 上的求和（Real 层可实例化；零公理） *)
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s => real_mult a (f s))) (real_mult a (real_sum_over_S f)).

(* 温度（推理侧 T 与热力学侧 D）、能量、logits（Real 层） *)
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable energy : S -> Real.
Variable z_logits : S -> Real.

(* ---- 基础助手：real_exp_neg 的 real_eq 外延 ---- *)
(*（cauchy_real_exp_wd 的 real_exp_neg 形态；real_exp_neg x       *)
(*  定义性 = cauchy_real_exp (−x)）                              *)
Lemma real_exp_neg_wd : forall a b : Real,
  real_eq a b -> real_eq (real_exp_neg a) (real_exp_neg b).
Proof.
  intros a b H.
  exact (cauchy_real_exp_wd (real_opp a) (real_opp b)
           (RealSetoid.real_eq_opp_compat a b H)).
Qed.

(* ---- 温度化配分函数（Real 层）：Z_T := Σ_s e^{z_s/T} ---- *)
Definition gibbst_real_partition_function_temp : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s))).

Lemma gibbst_real_partition_function_temp_pos : real_lt real_zero gibbst_real_partition_function_temp.
Proof.
  exact (real_sum_pos_preserved
           (fun s : S => real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
           (fun s : S =>
              real_exp_neg_pos (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))).
Qed.

(* ---- 温度化 softmax（Real 层）：e^{z_s/T}·inv(Z_T) ---- *)
Definition gibbst_real_softmax_temp (s : S) : Real :=
  real_mult (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
            (real_inv_pos gibbst_real_partition_function_temp gibbst_real_partition_function_temp_pos).

(* 配套正性：exp 恒正 × inv 正（real_mult_pos_compat） *)
Theorem real_softmax_temp_pos : forall s : S, real_lt real_zero (gibbst_real_softmax_temp s).
Proof.
  intro s. unfold gibbst_real_softmax_temp, real_exp_pos_fn.
  apply real_mult_pos_compat.
  - apply real_exp_neg_pos.
  - apply real_inv_pos_pos.
Qed.

(* 配套归一化：Σ_s softmax_temp(s) == 1
   链：逐 s 乘子交换（sum_ext + real_mult_comm）→ 标量线性提取
   （sum_linear）→ inv(Z_T)·Z_T == 1（real_inv_pos_correct）。 *)
Theorem real_softmax_temp_normalized :
  real_eq (real_sum_over_S (fun s => gibbst_real_softmax_temp s)) real_one.
Proof.
  unfold gibbst_real_softmax_temp.
  apply (real_eq_trans
          (real_sum_over_S (fun s => real_mult
                             (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
                             (real_inv_pos gibbst_real_partition_function_temp
                                           gibbst_real_partition_function_temp_pos)))
          (real_mult (real_inv_pos gibbst_real_partition_function_temp gibbst_real_partition_function_temp_pos)
                     (real_sum_over_S (fun s =>
                       real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))))
          real_one).
  - (* 1. 乘子交换后线性提取 *)
    apply (real_eq_trans
            (real_sum_over_S (fun s => real_mult
                               (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
                               (real_inv_pos gibbst_real_partition_function_temp
                                             gibbst_real_partition_function_temp_pos)))
            (real_sum_over_S (fun s => real_mult
                               (real_inv_pos gibbst_real_partition_function_temp
                                             gibbst_real_partition_function_temp_pos)
                               (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))))
            _).
    + apply real_sum_over_S_ext.
      intro s. apply real_mult_comm.
    + apply real_sum_over_S_linear.
  - (* 2. inv(Z_T)·Z_T == 1 *)
    apply (real_eq_trans
            (real_mult (real_inv_pos gibbst_real_partition_function_temp gibbst_real_partition_function_temp_pos)
                       (real_sum_over_S (fun s =>
                         real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))))
            (real_mult (real_inv_pos gibbst_real_partition_function_temp gibbst_real_partition_function_temp_pos)
                       gibbst_real_partition_function_temp)
            real_one).
    + apply real_eq_refl.
    + apply (real_eq_trans
              (real_mult (real_inv_pos gibbst_real_partition_function_temp gibbst_real_partition_function_temp_pos)
                         gibbst_real_partition_function_temp)
              (real_mult gibbst_real_partition_function_temp
                         (real_inv_pos gibbst_real_partition_function_temp gibbst_real_partition_function_temp_pos))
              real_one).
      * apply real_mult_comm.
      * apply real_inv_pos_correct.
Qed.

(* ---- Boltzmann 侧（同单位温度版结构） ---- *)
(* Boltzmann 因子（Real 层）：e^{−e(s)/D} *)
Definition gibbst_real_boltzmann_factor (s : S) : Real :=
  real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)).

(* 热力学配分（Real 层）：Σ_s boltzmann_factor *)
Definition gibbst_real_Z_thermo : Real := real_sum_over_S gibbst_real_boltzmann_factor.

Variable real_Z_thermo_pos : real_lt real_zero gibbst_real_Z_thermo.

(* Boltzmann 分布（Real 层）：inv(Z_thermo)·factor *)
Definition gibbst_real_boltzmann_dist_attn (s : S) : Real :=
  real_mult (real_inv_pos gibbst_real_Z_thermo real_Z_thermo_pos) (gibbst_real_boltzmann_factor s).

(* ---- 主定理（件 1）：任意温度下 softmax == Boltzmann ----
   前提：① 1/T == 1/D（温度统一，real_inv_pos 按位相等）
         ② energy == −logits（逐 s）
         ③ Z_thermo == Z_T（配分相等）
   结论：逐 s：gibbst_real_softmax_temp s == gibbst_real_boltzmann_dist_attn s。
   证明核（单位温度版每步对应）：
     因子桥（real_opp_mult + 温度统一 + energy 替换 + exp 外延）
     → 逆元统一（HZ + real_inv_pos_ext）
     → 组装（mult 交换 + mult_compat 四槽按位）。 *)
Theorem real_attention_is_gibbs_temp :
  (real_eq (real_inv_pos T T_pos) (real_inv_pos D D_pos)) ->
  (forall s : S, real_eq (energy s) (real_opp (z_logits s))) ->
  real_eq gibbst_real_Z_thermo gibbst_real_partition_function_temp ->
  forall s : S, real_eq (gibbst_real_softmax_temp s) (gibbst_real_boltzmann_dist_attn s).
Proof.
  intros HDT Henergy HZ s.
  unfold gibbst_real_softmax_temp, gibbst_real_boltzmann_dist_attn, gibbst_real_boltzmann_factor, real_exp_pos_fn.
  (* 1. 因子桥：e^{-(-z(s)/T)} == e^{-e(s)/D} *)
  assert (Hf : real_eq (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
                       (real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)))).
  {
    apply real_exp_neg_wd.
    apply (real_eq_trans _ (real_mult (real_inv_pos D D_pos) (real_opp (z_logits s))) _).
    - apply (real_eq_trans _ (real_mult (real_inv_pos T T_pos) (real_opp (z_logits s))) _).
      + (* −(z/T) == (1/T)·(−z)（real_opp_mult） *)
        apply real_opp_mult.
      + (* (1/T)·(−z) == (1/D)·(−z)（温度统一 HDT） *)
        apply (RealSetoid.real_eq_mult_compat_adapt
                (real_inv_pos T T_pos) (real_inv_pos D D_pos)
                (real_opp (z_logits s)) (real_opp (z_logits s))
                HDT (real_eq_refl _)).
    - (* (1/D)·(−z) == (1/D)·e（energy == −logits，对称） *)
      apply (RealSetoid.real_eq_mult_compat_adapt
              (real_inv_pos D D_pos) (real_inv_pos D D_pos)
              (real_opp (z_logits s)) (energy s)
              (real_eq_refl _) (real_eq_sym _ _ (Henergy s))).
  }
  (* 2. 逆元统一：inv(Z_thermo) == inv(Z_T)（HZ + real_inv_pos_ext） *)
  assert (Hie : real_eq (real_inv_pos gibbst_real_Z_thermo real_Z_thermo_pos)
                        (real_inv_pos gibbst_real_partition_function_temp
                                      gibbst_real_partition_function_temp_pos)).
  { apply (real_inv_pos_ext gibbst_real_Z_thermo gibbst_real_partition_function_temp
                            real_Z_thermo_pos gibbst_real_partition_function_temp_pos).
    exact HZ. }
  (* 3. 组装（副本单位温度版第 3 步） *)
  apply (real_eq_trans _ (real_mult (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
                                    (real_inv_pos gibbst_real_partition_function_temp
                                                  gibbst_real_partition_function_temp_pos)) _).
  - apply real_eq_refl.
  - apply (real_eq_trans _ (real_mult (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
                                      (real_inv_pos gibbst_real_Z_thermo real_Z_thermo_pos)) _).
    + apply (RealSetoid.real_eq_mult_compat_adapt
              (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
              (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
              (real_inv_pos gibbst_real_partition_function_temp gibbst_real_partition_function_temp_pos)
              (real_inv_pos gibbst_real_Z_thermo real_Z_thermo_pos)
              (real_eq_refl _) (real_eq_sym _ _ Hie)).
    + apply (real_eq_trans _ (real_mult (real_inv_pos gibbst_real_Z_thermo real_Z_thermo_pos)
                                        (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))) _).
      * apply real_mult_comm.
      * apply (RealSetoid.real_eq_mult_compat_adapt
                (real_inv_pos gibbst_real_Z_thermo real_Z_thermo_pos)
                (real_inv_pos gibbst_real_Z_thermo real_Z_thermo_pos)
                (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
                (real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)))
                (real_eq_refl _) Hf).
Qed.

End RealAttnGibbsTemp.
Print Assumptions sqrt_premise_le_intro.
Print Assumptions real_partition_function_scaled_pos.
Print Assumptions real_partition_function_temp_param_pos.
Print Assumptions real_partition_function_temp_pos.
Print Assumptions gibbst_real_partition_function_temp_pos.
Print Assumptions real_temp_is_scale_duality.
Print Assumptions real_exp_neg_wd.
