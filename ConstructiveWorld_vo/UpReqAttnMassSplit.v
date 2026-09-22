(* ============================================================ *)
(* ToyR 玩具证替换件 —— T268 台账席 战役包AC（tier2 末段第一批）      *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   ams_sum_switch_self（原 L340，4 句轻证）	*)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqAttnMassSplit.v —— 质量分裂四件链（Σw 拆分至 L1 上界）        *)
(*                                                              *)
(* 目的：补齐上游冻结链的后四件（mass_split → deficit_eq →           *)
(*   mass_rest_le → l1_le），消费上游 UpReqAttnUniformLimit 的       *)
(*   alm_ 面（alm_switch/alm_k/alm_invk/alm_uniform）。蓝图四恒等式： *)
(*   Σw = k·w(m)+M；k·(inv k−w(m))=M；M≤n·decay；L1 ≤ 2n·decay；      *)
(*   数值核验（vocab=m,m,c,d 四温度点 L1==2M）先行通过。               *)
(*   落盘前另以精确有理数/浮点双算术随机复核 3000 样本                *)
(*   （n∈[1,7]、k∈[1,n]、T∈[0.05,2]，逐项验 mass_split/deficit_eq/     *)
(*   mass_rest_le/wm_le_invk/L1==2M/L1≤2n·decay）——假命题拦截纪律。   *)
(*                                                              *)
(* 主件（前缀 ams_，避免与库内既有名冲突）：                          *)
(*   关键构造判断：上游 swg_switch_sum_gen 的 g 槽是 Real 常量，        *)
(*   质量分裂需「副本支 w(m)、非副本支 w(x)」的函数形开关。自建         *)
(*   ams_mswitch（match 直写，c 槽常量＋g 槽函数），并按上游证明骨架    *)
(*   逐行转录函数形归纳件 ams_switch_sum_fun（alm_switch 常量 g 版      *)
(*   不可直接消费——c2 槽喂函数即形槽不合）。其余沿既定链：              *)
(*   ① ams_mass_split：Σ w_T == k·w_T(m) + M；                        *)
(*   ② ams_deficit_eq：k·(1/k − w_T(m)) == M（亏差=溢出）；            *)
(*   ③ ams_mass_rest_le：M ≤ n·e^{−γ/T}（复用 core_decay_bound，        *)
(*      免 m_count_one，其 post-End 签名已核）；                       *)
(*   ④ ams_l1_le：L1(w_T,u) = Σ|u−w| == 2M ≤ 2·(n·decay)（链式          *)
(*      组装①②③＋内部件 ams_wm_le_invk；2n·decay 写成 n·decay＋       *)
(*      n·decay 直写形，免 of_nat 算术）。                             *)
(*   内部件（非平凡性所在，全 ams_ 前缀）：ams_mswitch、                *)
(*   ams_switch_sum_fun（函数形 m-开关求和恒等式，约 130 行真归纳）、    *)
(*   ams_switch_self_eq/ams_sum_switch_self（开关自逐点等值）、          *)
(*   ams_minus_r_plus（minus_r 右消还原）、ams_plus_reg_r（Real 层      *)
(*   加法右消去——蓝图预留件，opp 路线构造，零序判定依赖）、              *)
(*   ams_M_nonneg、ams_abs_pointwise（|u−w| 逐点折叠）、                 *)
(*   ams_wm_le_invk（w_T(m) ≤ 1/k：eq_mult_inv_absorb 右乘 inv          *)
(*   换序收尾，免 35 行消去引理）。                                     *)
(*                                                              *)
(* 陈述面：结论全 real_eq/real_le（Set 层），前提镜像上游               *)
(*   core_decay_bound 的 post-End 形（vocab_nonempty/m_in_vocab/        *)
(*   gap_le 显式入参）；T/Ht 逐件全称量化（全称 Token/vocab 形）。       *)
(*                                                              *)
(* 依赖（全部只读消费）：UpReqAttnUniformLimit（上游）、                 *)
(*   CW_ConstructiveWorld_219、AttnHardLimit218。零改既有文件。          *)
(*                                                              *)
(* 备注：公理面：零公理、零承认件、零弃证；零经典逻辑；                  *)
(*   文末 Print Assumptions 对四主件审计全 Closed；提取口零 magic。      *)
(*   战术纪要：match 包装 Definition 一律 destruct 前显式 unfold         *)
(*   （ams_mswitch/alm_uniform 双 unfold）；Real 层幺零元用右形           *)
(*   （real_plus_zero/real_mult_one）＋comm 桥；分配律左因子              *)
(*   real_distrib、右因子 real_distrib_r 分槽取用。                      *)
(* ============================================================ *)

(* Require 顺序：上游件 UpReqAttnUniformLimit 先入。 *)
Require Import UpReqAttnUniformLimit.
Require Import CW_ConstructiveWorld_219.
Require Import AttnHardLimit218.
From Stdlib Require Import List Arith.

(* ============================================================ *)
(* Section AmsMassSplit：镜像上游 AlmUniform 变量面（去 gamma_pos， *)
(* 本链四件+内部件未消费它；T/Ht 逐件全称量化）。                    *)
(* ============================================================ *)

Section AmsMassSplit.

Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable token_eq_dec : forall a b : Token, Or (Id a b) (Not (Id a b)).
Variable z : Token -> Real.
Variable m : Token.
Variable m_in_vocab : InT m vocab.
Variable gamma : Real.
Variable gap_le : forall x : Token, Not (Id x m) ->
  real_le (real_plus (z x) gamma) (z m).

(* 硬注意力权重缩写（post-End w_T 五参直引，delta 透明） *)
Definition ams_w (T : Real) (Ht : real_lt real_zero T) (x : Token) : Real :=
  w_T Token vocab vocab_nonempty z T Ht x.

(* 函数形 m-开关：副本支取常量 c，非副本支取 g x（c : Real 常量槽 +  *)
(* g : Token -> Real 函数槽——上游 alm_switch 双常量槽的函数形补全） *)
Definition ams_mswitch (c : Real) (g : Token -> Real) (x : Token) : Real :=
  match token_eq_dec x m with
  | inl _ => c
  | inr _ => g x
  end.

(* 非 m 副本质量 M：switch(0, w_T) 的 vocab 和（上游蓝图 §1 的 M） *)
Definition ams_M (T : Real) (Ht : real_lt real_zero T) : Real :=
  real_list_sum Token (ams_mswitch real_zero (ams_w T Ht)) vocab.

(* ---------- 函数形 m-开关求和恒等式（上游原证明骨架逐行转录） ---------- *)
(* Σ ams_mswitch c g == count(m)·c + Σ ams_mswitch 0 g（对显式表 vl 归纳： *)
(* 空表零元代数 / 副本支 of_nat(S) 定义折叠+右分配+左幺元交换桥 /          *)
(* 非副本支中项交换。g 为函数形（对上游常量 g 版的形槽补全）。         *)

Lemma ams_switch_sum_fun : forall (c : Real) (g : Token -> Real) (vl : list Token),
  real_eq (real_list_sum Token (ams_mswitch c g) vl)
    (real_plus
       (real_mult (real_of_nat (count_token Token token_eq_dec m vl)) c)
       (real_list_sum Token (ams_mswitch real_zero g) vl)).
Proof.
  intros c g vl. induction vl as [| y rest IH].
  - (* 空表：0 == 0·c + 0（real_of_nat O ≡ real_zero 定义折叠） *)
    cbn [real_list_sum count_token real_of_nat].
    apply (real_eq_trans _ (real_plus real_zero real_zero) _).
    + apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
      apply (real_plus_zero real_zero).
    + apply (RealSetoid.real_eq_plus_compat real_zero real_zero
               (real_mult real_zero c) real_zero).
      * apply (real_eq_trans _ (real_mult c real_zero) _).
        -- apply (real_eq_sym (real_mult c real_zero) real_zero).
           apply (real_mult_zero c).
        -- apply (real_mult_comm c real_zero).
      * apply real_eq_refl.
  - cbn [real_list_sum count_token]. unfold ams_mswitch.
    destruct (token_eq_dec y m) as [Hym | Hnym].
    + (* 副本支：of_nat(S k) ≡ 1 + of_nat k 定义折叠；
         核 = (1+a)·c == c + a·c（右分配 + 左幺元经交换桥） *)
      cbn [real_of_nat].
      assert (Hcore : real_eq
                (real_mult (real_plus real_one
                              (real_of_nat
                                 (count_token Token token_eq_dec m rest))) c)
                (real_plus c
                   (real_mult (real_of_nat
                                 (count_token Token token_eq_dec m rest)) c))).
      { apply (real_eq_trans _
            (real_plus (real_mult real_one c)
                       (real_mult
                          (real_of_nat
                             (count_token Token token_eq_dec m rest)) c)) _).
        - apply (real_eq_sym
              (real_plus (real_mult real_one c)
                         (real_mult
                            (real_of_nat
                               (count_token Token token_eq_dec m rest)) c))
              (real_mult (real_plus real_one
                            (real_of_nat
                               (count_token Token token_eq_dec m rest))) c)).
          apply (real_distrib_r real_one
                   (real_of_nat (count_token Token token_eq_dec m rest)) c).
        - apply (RealSetoid.real_eq_plus_compat (real_mult real_one c)
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c)
                   c
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c)).
          + apply (real_eq_trans _ (real_mult c real_one) _).
            * apply (real_mult_comm real_one c).
            * apply (real_mult_one c).
          + apply real_eq_refl. }
      apply (real_eq_trans _
        (real_plus c
           (real_plus
              (real_mult
                 (real_of_nat
                    (count_token Token token_eq_dec m rest)) c)
              (real_list_sum Token (ams_mswitch real_zero g) rest))) _).
      * apply (RealSetoid.real_eq_plus_compat c
                 (real_list_sum Token (ams_mswitch c g) rest) c
                 (real_plus
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (ams_mswitch real_zero g) rest))).
        -- apply real_eq_refl.
        -- exact IH.
      * apply (real_eq_trans _
          (real_plus
             (real_plus c
                (real_mult
                   (real_of_nat
                      (count_token Token token_eq_dec m rest)) c))
             (real_list_sum Token (ams_mswitch real_zero g) rest)) _).
        -- apply (real_plus_assoc c
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (ams_mswitch real_zero g) rest)).
        -- apply (real_eq_trans _
             (real_plus
                (real_plus c
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c))
                (real_plus real_zero
                   (real_list_sum Token (ams_mswitch real_zero g)
                      rest))) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus c
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_list_sum Token (ams_mswitch real_zero g)
                          rest)
                       (real_plus c
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_plus real_zero
                          (real_list_sum Token (ams_mswitch real_zero g)
                             rest))).
              ** apply real_eq_refl.
              ** apply (real_eq_sym
                         (real_plus real_zero
                            (real_list_sum Token (ams_mswitch real_zero g)
                               rest))
                         (real_list_sum Token (ams_mswitch real_zero g)
                            rest)).
                 apply (real_eq_trans _
                           (real_plus
                              (real_list_sum Token (ams_mswitch real_zero g)
                                 rest) real_zero) _).
                 apply (real_plus_comm real_zero
                          (real_list_sum Token (ams_mswitch real_zero g)
                             rest)).
                 apply (real_plus_zero
                          (real_list_sum Token (ams_mswitch real_zero g)
                             rest)).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus c
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_plus real_zero
                          (real_list_sum Token (ams_mswitch real_zero g)
                             rest))
                       (real_mult
                          (real_plus real_one
                             (real_of_nat
                                (count_token Token token_eq_dec m rest))) c)
                       (real_plus real_zero
                          (real_list_sum Token (ams_mswitch real_zero g)
                             rest))).
              ** apply (real_eq_sym
                          (real_mult
                             (real_plus real_one
                                (real_of_nat
                                   (count_token Token token_eq_dec m rest)))
                             c)
                          (real_plus c
                             (real_mult
                                (real_of_nat
                                   (count_token Token token_eq_dec m rest))
                                c))).
                 exact Hcore.
              ** apply real_eq_refl.
    + (* 非副本支：IH + assoc + comm 拼中项交换 *)
      apply (real_eq_trans _
        (real_plus (g y)
           (real_plus
              (real_mult
                 (real_of_nat
                    (count_token Token token_eq_dec m rest)) c)
              (real_list_sum Token (ams_mswitch real_zero g) rest))) _).
      * apply (RealSetoid.real_eq_plus_compat (g y)
                 (real_list_sum Token (ams_mswitch c g) rest) (g y)
                 (real_plus
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (ams_mswitch real_zero g) rest))).
        -- apply real_eq_refl.
        -- exact IH.
      * apply (real_eq_trans _
          (real_plus
             (real_plus (g y)
                (real_mult
                   (real_of_nat
                      (count_token Token token_eq_dec m rest)) c))
             (real_list_sum Token (ams_mswitch real_zero g) rest)) _).
        -- apply (real_plus_assoc (g y)
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_list_sum Token (ams_mswitch real_zero g) rest)).
        -- apply (real_eq_trans _
             (real_plus
                (real_plus
                   (real_mult
                      (real_of_nat
                         (count_token Token token_eq_dec m rest)) c) (g y))
                (real_list_sum Token (ams_mswitch real_zero g) rest)) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus (g y)
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c))
                       (real_list_sum Token (ams_mswitch real_zero g)
                          rest)
                       (real_plus
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c)
                          (g y))
                       (real_list_sum Token (ams_mswitch real_zero g)
                          rest)).
              ** apply (real_plus_comm (g y)
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c)).
              ** apply real_eq_refl.
           ++ apply (real_eq_sym
                 (real_plus
                    (real_mult
                       (real_of_nat
                          (count_token Token token_eq_dec m rest)) c)
                    (real_plus (g y)
                       (real_list_sum Token (ams_mswitch real_zero g)
                          rest)))
                 (real_plus
                    (real_plus
                       (real_mult
                          (real_of_nat
                             (count_token Token token_eq_dec m rest)) c)
                       (g y))
                    (real_list_sum Token (ams_mswitch real_zero g)
                       rest))).
              ** apply (real_plus_assoc
                          (real_mult
                             (real_of_nat
                                (count_token Token token_eq_dec m rest)) c)
                          (g y)
                          (real_list_sum Token (ams_mswitch real_zero g)
                             rest)).
Qed.

(* ---------- 内部件 0：开关自逐点等值（mass_split 的 pointwise 面） ---------- *)

Lemma ams_switch_self_eq : forall (f : Token -> Real) (x : Token),
  real_eq (ams_mswitch (f m) f x) (f x).
Proof.
  intros f x. unfold ams_mswitch.
  destruct (token_eq_dec x m) as [Hxm | Hnxm].
  - (* Id 非 setoid：id_cong + id_sym + aid_real_eq 桥（基库惯用法） *)
    exact (aid_real_eq (f m) (f x) (id_sym (id_cong f Hxm))).
  - apply real_eq_refl.
Qed.

Lemma ams_sum_switch_self : forall f : Token -> Real,
  real_eq (real_list_sum Token (ams_mswitch (f m) f) vocab)
          (real_list_sum Token f vocab).
Proof.
  intro f. apply real_list_sum_ext. intro w.
  exact (ams_switch_self_eq f w).
Qed.

(* ---------- 内部件 1：minus_r 右消还原：(a − b) + b == a ---------- *)

Lemma ams_minus_r_plus : forall a b : Real,
  real_eq (real_plus (real_minus_r a b) b) a.
Proof.
  intros a b. unfold real_minus_r.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp b) b)) _).
  - (* (a + −b) + b == a + (−b + b)：右嵌形 = assoc 的对称 *)
    apply (real_eq_sym (real_plus a (real_plus (real_opp b) b))
                       (real_plus (real_plus a (real_opp b)) b)).
    apply real_plus_assoc.
  - apply (real_eq_trans _ (real_plus a (real_plus b (real_opp b))) _).
    + apply (RealSetoid.real_eq_plus_compat a
               (real_plus (real_opp b) b) a (real_plus b (real_opp b))).
      * apply real_eq_refl.
      * apply real_plus_comm.
    + apply (real_eq_trans _ (real_plus a real_zero) _).
      * apply (RealSetoid.real_eq_plus_compat a
                 (real_plus b (real_opp b)) a real_zero).
        -- apply real_eq_refl.
        -- apply real_plus_opp.
      * apply real_plus_zero.
Qed.

(* ---------- 内部件 2：Real 层加法右消去（上游蓝图预留件） ----------
   c + a == c + b ⟹ a == b。构造路线：两侧加 −c（compat），assoc/comm
   折叠 (−c + c) → 0 → 0 + d == d。零序判定依赖，纯 eq 代数。       *)

Lemma ams_plus_reg_r : forall a b c : Real,
  real_eq (real_plus c a) (real_plus c b) -> real_eq a b.
Proof.
  intros a b c H.
  assert (Hshift : forall d : Real,
    real_eq (real_plus (real_opp c) (real_plus c d)) d).
  { intro d.
    apply (real_eq_trans _ (real_plus (real_plus (real_opp c) c) d) _).
    - apply (real_plus_assoc (real_opp c) c d).
    - apply (real_eq_trans _ (real_plus (real_plus c (real_opp c)) d) _).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_plus (real_opp c) c) d
                 (real_plus c (real_opp c)) d).
        * apply real_plus_comm.
        * apply real_eq_refl.
      + apply (real_eq_trans _ (real_plus real_zero d) _).
        * apply (RealSetoid.real_eq_plus_compat
                   (real_plus c (real_opp c)) d real_zero d).
          -- apply real_plus_opp.
          -- apply real_eq_refl.
        * apply (real_eq_trans _ (real_plus d real_zero) _).
          -- apply real_plus_comm.
          -- apply real_plus_zero. }
  apply (real_eq_trans a (real_plus (real_opp c) (real_plus c a)) b).
  - exact (real_eq_sym _ _ (Hshift a)).
  - apply (real_eq_trans (real_plus (real_opp c) (real_plus c a))
             (real_plus (real_opp c) (real_plus c b)) b).
    + apply (RealSetoid.real_eq_plus_compat (real_opp c) (real_plus c a)
               (real_opp c) (real_plus c b)).
      * apply real_eq_refl.
      * exact H.
    + exact (Hshift b).
Qed.

(* ---------- 内部件 3：M ≥ 0（switch 保非负 + sum_nonneg） ---------- *)

Lemma ams_M_nonneg : forall (T : Real) (Ht : real_lt real_zero T),
  real_le real_zero (ams_M T Ht).
Proof.
  intros T Ht. unfold ams_M.
  apply (sum_nonneg_aux Token (ams_mswitch real_zero (ams_w T Ht)) vocab).
  intro y. unfold ams_mswitch.
  destruct (token_eq_dec y m) as [Hym | Hnym].
  - apply real_le_refl.
  - apply real_le_from_lt_aux.
    exact (w_T_pos Token vocab vocab_nonempty z T Ht y).
Qed.

(* ---------- 内部件 4：w_T(m) ≤ 1/k（wm_le_invk） ----------
   链：k·w(m) + M == Σw == 1 且 M ≥ 0 ⟹ k·w(m) ≤ 1 == k·(1/k)；
   右乘 1/k（正数保序）后 eq_mult_inv_absorb 两侧换序收尾——
   上游蓝图 alm_w_m_le_invk 的免消去引理实现。                   *)

Lemma ams_wm_le_invk : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (ams_w T Ht m) (alm_invk Token vocab token_eq_dec m m_in_vocab).
Proof.
  intros T Ht.
  assert (Hk1 : real_eq (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                             (alm_invk Token vocab token_eq_dec m m_in_vocab))
                        real_one)
    by exact (real_inv_pos_correct (real_of_nat (alm_k Token vocab token_eq_dec m))
                (alm_k_pos Token vocab token_eq_dec m m_in_vocab)).
  (* 步 1：k·w(m) ≤ 1 *)
  assert (Hle1 : real_le (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                              (ams_w T Ht m))
                         real_one).
  { apply (RealSetoid.real_le_id_r
             (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m)) (ams_w T Ht m))
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (ams_w T Ht m))
                        (ams_M T Ht))
             real_one).
    - apply (real_eq_trans
               (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                     (ams_w T Ht m))
                          (ams_M T Ht))
               (real_list_sum Token (ams_w T Ht) vocab) real_one).
      + apply (real_eq_trans
                 (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                       (ams_w T Ht m))
                            (ams_M T Ht))
                 (real_list_sum Token
                    (ams_mswitch (ams_w T Ht m) (ams_w T Ht)) vocab) _).
        * exact (real_eq_sym _ _
                   (ams_switch_sum_fun (ams_w T Ht m) (ams_w T Ht) vocab)).
        * exact (ams_sum_switch_self (ams_w T Ht)).
      + exact (w_T_sum_one Token vocab vocab_nonempty z T Ht).
    - apply (real_le_plus_nonneg_r_aux _ _ (ams_M_nonneg T Ht)). }
  (* 步 2：k·w(m) ≤ k·(1/k)（eq 1 == k·(1/k) 适配 + 步 1） *)
  assert (Hle2 : real_le (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                              (ams_w T Ht m))
                         (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                    (alm_invk Token vocab token_eq_dec m m_in_vocab))).
  { apply (RealSetoid.real_le_id_r
             (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m)) (ams_w T Ht m))
             real_one
             (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                        (alm_invk Token vocab token_eq_dec m m_in_vocab))).
    - exact (real_eq_sym _ _ Hk1).
    - exact Hle1. }
  (* 步 3：右乘 1/k（正数）保序 *)
  assert (Hle4 : real_le (real_mult (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                (ams_w T Ht m))
                                     (alm_invk Token vocab token_eq_dec m m_in_vocab))
                         (real_mult (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                (alm_invk Token vocab token_eq_dec m m_in_vocab))
                                    (alm_invk Token vocab token_eq_dec m m_in_vocab))).
  { apply (real_le_mult_compat _ _
             (alm_invk Token vocab token_eq_dec m m_in_vocab)).
    - exact (real_inv_pos_pos (real_of_nat (alm_k Token vocab token_eq_dec m))
                (alm_k_pos Token vocab token_eq_dec m m_in_vocab)).
    - exact Hle2. }
  (* 步 4：eq_mult_inv_absorb 两侧换序 + le 适配收尾 *)
  apply (RealSetoid.real_le_id_l (ams_w T Ht m)
           (real_mult (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                 (ams_w T Ht m))
                      (alm_invk Token vocab token_eq_dec m m_in_vocab))
           (alm_invk Token vocab token_eq_dec m m_in_vocab)).
  - apply (real_eq_sym _ _ (eq_mult_inv_absorb
              (real_of_nat (alm_k Token vocab token_eq_dec m))
              (ams_w T Ht m)
              (alm_k_pos Token vocab token_eq_dec m m_in_vocab) Hk1)).
  - apply (RealSetoid.real_le_id_r
             (real_mult (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                    (ams_w T Ht m))
                        (alm_invk Token vocab token_eq_dec m m_in_vocab))
             (real_mult (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                    (alm_invk Token vocab token_eq_dec m m_in_vocab))
                        (alm_invk Token vocab token_eq_dec m m_in_vocab))
             (alm_invk Token vocab token_eq_dec m m_in_vocab)).
    + exact (eq_mult_inv_absorb
               (real_of_nat (alm_k Token vocab token_eq_dec m))
               (alm_invk Token vocab token_eq_dec m m_in_vocab)
               (alm_k_pos Token vocab token_eq_dec m m_in_vocab) Hk1).
    + exact Hle4.
Qed.

(* ============================================================ *)
(* 链件 ①：ams_mass_split —— vocab 质量分裂引理                     *)
(*   Σ_vocab w_T == k·w_T(m) + M（上游原申报形；自逐点等值 +          *)
(*   ams_switch_sum_fun 直接消费）。                                 *)
(* ============================================================ *)

Theorem ams_mass_split : forall (T : Real) (Ht : real_lt real_zero T),
  real_eq (real_list_sum Token (ams_w T Ht) vocab)
          (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                (ams_w T Ht m))
                     (ams_M T Ht)).
Proof.
  intros T Ht.
  apply (real_eq_trans
           (real_list_sum Token (ams_w T Ht) vocab)
           (real_list_sum Token
              (ams_mswitch (ams_w T Ht m) (ams_w T Ht)) vocab) _).
  - apply (real_eq_sym _ _ (ams_sum_switch_self (ams_w T Ht))).
  - exact (ams_switch_sum_fun (ams_w T Ht m) (ams_w T Ht) vocab).
Qed.

(* ============================================================ *)
(* 链件 ②：ams_deficit_eq —— 亏量恒等式                             *)
(*   k·(1/k − w_T(m)) == M（亏差=溢出；上游原申报形）。              *)
(*   链：D + w(m) == 1/k（minus_r 右消）⟹ k·(D + w(m)) == k·(1/k)    *)
(*   == 1 == k·w(m) + M（①+Σw==1）⟹ 交换后 ams_plus_reg_r 消去。   *)
(* ============================================================ *)

Theorem ams_deficit_eq : forall (T : Real) (Ht : real_lt real_zero T),
  real_eq (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                     (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                   (ams_w T Ht m)))
          (ams_M T Ht).
Proof.
  intros T Ht.
  assert (Hk1 : real_eq (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                             (alm_invk Token vocab token_eq_dec m m_in_vocab))
                        real_one)
    by exact (real_inv_pos_correct (real_of_nat (alm_k Token vocab token_eq_dec m))
                (alm_k_pos Token vocab token_eq_dec m m_in_vocab)).
  (* k·w(m) + M == 1（①+Σw==1） *)
  assert (Hsum1 : real_eq (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                 (ams_w T Ht m))
                                      (ams_M T Ht))
                          real_one).
  { apply (real_eq_trans
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (ams_w T Ht m))
                        (ams_M T Ht))
             (real_list_sum Token (ams_w T Ht) vocab) _).
    - exact (real_eq_sym _ _ (ams_mass_split T Ht)).
    - exact (w_T_sum_one Token vocab vocab_nonempty z T Ht). }
  (* D + w(m) == 1/k（D := 1/k − w(m) 的右消还原） *)
  assert (Hcan : real_eq (real_plus (real_minus_r
                                      (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                      (ams_w T Ht m))
                                    (ams_w T Ht m))
                         (alm_invk Token vocab token_eq_dec m m_in_vocab))
    by exact (ams_minus_r_plus _ _).
  (* k·(D + w(m)) == k·D + k·w(m)（分配，左因子槽） *)
  assert (Hdist : real_eq (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                              (real_plus (real_minus_r
                                            (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                            (ams_w T Ht m))
                                         (ams_w T Ht m)))
                  (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                        (real_minus_r
                                           (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                           (ams_w T Ht m)))
                             (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                        (ams_w T Ht m))))
    by exact (real_distrib _ _ _).
  (* k·D + k·w(m) == k·(D + w(m)) == k·(1/k) == 1 *)
  assert (Hone2 : real_eq (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                 (real_minus_r
                                                    (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                    (ams_w T Ht m)))
                                      (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                 (ams_w T Ht m)))
                          real_one).
  { apply (real_eq_trans
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r
                                      (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                      (ams_w T Ht m)))
                        (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (ams_w T Ht m)))
             (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                        (real_plus (real_minus_r
                                      (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                      (ams_w T Ht m))
                                   (ams_w T Ht m))) _).
    - exact (real_eq_sym _ _ Hdist).
    - apply (real_eq_trans
               (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                          (real_plus (real_minus_r
                                        (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                        (ams_w T Ht m))
                                     (ams_w T Ht m)))
               (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                          (alm_invk Token vocab token_eq_dec m m_in_vocab)) _).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_of_nat (alm_k Token vocab token_eq_dec m))
                 (real_plus (real_minus_r
                               (alm_invk Token vocab token_eq_dec m m_in_vocab)
                               (ams_w T Ht m))
                            (ams_w T Ht m))
                 (real_of_nat (alm_k Token vocab token_eq_dec m))
                 (alm_invk Token vocab token_eq_dec m m_in_vocab)).
        * apply real_eq_refl.
        * exact Hcan.
      + exact Hk1. }
  (* 交换 + 过 1 + 右消去 ⟹ k·D == M *)
  assert (Hswap : real_eq (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                 (ams_w T Ht m))
                                      (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                                 (real_minus_r
                                                    (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                    (ams_w T Ht m))))
                          real_one).
  { apply (real_eq_trans
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (ams_w T Ht m))
                        (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r
                                      (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                      (ams_w T Ht m))))
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r
                                      (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                      (ams_w T Ht m)))
                        (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (ams_w T Ht m))) _).
    - apply real_plus_comm.
    - exact Hone2. }
  exact (ams_plus_reg_r _ _ _
           (real_eq_trans _ _ _ Hswap (real_eq_sym _ _ Hsum1))).
Qed.

(* ============================================================ *)
(* 链件 ③：ams_mass_rest_le —— 其余部分质量上界                     *)
(*   M ≤ n·e^{−γ/T}（上游原申报形；逐点：副本支 0 ≤ decay（exp 恒    *)
(*   正），非副本支 core_decay_bound 复用；求和步 sum_nonneg_le_     *)
(*   const_aux（n = length vocab）。                                 *)
(* ============================================================ *)

Theorem ams_mass_rest_le : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (ams_M T Ht)
          (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht)).
Proof.
  intros T Ht. unfold ams_M.
  apply (sum_nonneg_le_const_aux Token
           (ams_mswitch real_zero (ams_w T Ht))
           (decay_T gamma T Ht) vocab).
  intros x Hin. unfold ams_mswitch.
  destruct (token_eq_dec x m) as [Hxm | Hnxm].
  - (* 副本支：0 ≤ decay_T，exp 恒正 *)
    apply real_le_from_lt_aux. unfold decay_T. apply cauchy_real_exp_pos.
  - (* 非副本支：w_T(x) ≤ decay_T（免 m_count_one 的衰减界） *)
    exact (core_decay_bound Token vocab vocab_nonempty z m m_in_vocab
              gamma gap_le T Ht x Hnxm).
Qed.

(* ---------- 内部件 5：逐点 |u − w| == switch(D, w) ----------
   u = alm_uniform；副本支 D := 1/k − w(m) ≥ 0（wm_le_invk 入件）
   经 real_abs_minus_r_nonneg_aux 折叠 abs；非副本支 |0 − w(x)| ==
   w(x)（w ≥ 0）。unfold 双件在前、destruct 在后（上游件同款处置）。   *)

Lemma ams_abs_pointwise : forall (T : Real) (Ht : real_lt real_zero T) (x : Token),
  real_eq (real_abs (real_minus_r (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                                  (ams_w T Ht x)))
          (ams_mswitch (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                     (ams_w T Ht m))
                       (ams_w T Ht) x).
Proof.
  intros T Ht x.
  assert (Hwmle : real_le (ams_w T Ht m)
                    (alm_invk Token vocab token_eq_dec m m_in_vocab))
    by exact (ams_wm_le_invk T Ht).
  unfold ams_mswitch, alm_uniform.
  destruct (token_eq_dec x m) as [Hxm | Hnxm].
  - (* 副本支：x==m 的 Id 传输（id_cong 链）后 |D| == D（D ≥ 0 折叠） *)
    assert (HTx : real_eq (real_minus_r
                             (alm_invk Token vocab token_eq_dec m m_in_vocab)
                             (ams_w T Ht x))
                          (real_minus_r
                             (alm_invk Token vocab token_eq_dec m m_in_vocab)
                             (ams_w T Ht m)))
      by exact (aid_real_eq _ _
                  (id_cong (fun t =>
                              real_minus_r
                                (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                t)
                     (id_cong (ams_w T Ht) Hxm))).
    apply (real_eq_trans
             (real_abs (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                     (ams_w T Ht x)))
             (real_abs (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                     (ams_w T Ht m))) _).
    + exact (real_abs_eq_compat _ _ HTx).
    + (* |1/k − w(m)| == |−(w(m) − 1/k)| == |w(m) − 1/k| == 1/k − w(m) *)
      apply (real_eq_trans
               (real_abs (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                       (ams_w T Ht m)))
               (real_abs (real_opp (real_minus_r (ams_w T Ht m)
                                                 (alm_invk Token vocab token_eq_dec m m_in_vocab)))) _).
      * (* 1/k − w(m) == −(w(m) − 1/k)：comm + opp_opp + opp_plus 翻转 *)
        apply real_abs_eq_compat.
        apply (real_eq_trans
                 (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                               (ams_w T Ht m))
                 (real_plus (real_opp (ams_w T Ht m))
                            (alm_invk Token vocab token_eq_dec m m_in_vocab)) _).
        -- apply real_plus_comm.
        -- apply (real_eq_trans
                    (real_plus (real_opp (ams_w T Ht m))
                               (alm_invk Token vocab token_eq_dec m m_in_vocab))
                    (real_plus (real_opp (ams_w T Ht m))
                               (real_opp (real_opp
                                            (alm_invk Token vocab token_eq_dec m m_in_vocab)))) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_opp (ams_w T Ht m))
                       (alm_invk Token vocab token_eq_dec m m_in_vocab)
                       (real_opp (ams_w T Ht m))
                       (real_opp (real_opp
                                    (alm_invk Token vocab token_eq_dec m m_in_vocab)))).
              ** apply real_eq_refl.
              ** apply (real_eq_sym _ _
                       (real_opp_opp
                          (alm_invk Token vocab token_eq_dec m m_in_vocab))).
           ++ apply (real_eq_sym _ _ (real_opp_plus (ams_w T Ht m)
                        (real_opp (alm_invk Token vocab token_eq_dec m m_in_vocab)))).
      * (* |−(w(m) − 1/k)| == |w(m) − 1/k| == 1/k − w(m)（wm_le_invk 入件） *)
        apply (real_eq_trans
                 (real_abs (real_opp (real_minus_r (ams_w T Ht m)
                                                   (alm_invk Token vocab token_eq_dec m m_in_vocab))))
                 (real_abs (real_minus_r (ams_w T Ht m)
                                         (alm_invk Token vocab token_eq_dec m m_in_vocab))) _).
        -- exact (real_abs_opp (real_minus_r (ams_w T Ht m)
                              (alm_invk Token vocab token_eq_dec m m_in_vocab))).
        -- exact (real_abs_minus_r_nonneg_aux (ams_w T Ht m)
                    (alm_invk Token vocab token_eq_dec m m_in_vocab) Hwmle).
  - (* 非副本支：|0 − w(x)| == |−w(x)| == w(x)（w ≥ 0） *)
    apply (real_eq_trans
             (real_abs (real_minus_r real_zero (ams_w T Ht x)))
             (real_abs (real_opp (ams_w T Ht x))) _).
    + apply real_abs_eq_compat.
      apply (real_eq_trans
               (real_minus_r real_zero (ams_w T Ht x))
               (real_plus (real_opp (ams_w T Ht x)) real_zero) _).
      * apply real_plus_comm.
      * apply real_plus_zero.
    + apply (real_eq_trans (real_abs (real_opp (ams_w T Ht x)))
               (real_abs (ams_w T Ht x)) (ams_w T Ht x)).
      * apply real_abs_opp.
      * apply (real_abs_pos_req (ams_w T Ht x)
                  (w_T_pos Token vocab vocab_nonempty z T Ht x)).
Qed.

(* ============================================================ *)
(* 链件 ④：ams_l1_le —— L1 距离上界收口                             *)
(*   L1(w_T, u) = Σ|u − w| == 2M ≤ 2·(n·decay)（上游原申报形；       *)
(*   2n·decay 写成 n·decay + n·decay 直写形）。链式组装：逐点 abs    *)
(*   折叠（部件 5）+ ams_switch_sum_fun（①同款）+ ②（k·D == M）+ ③。 *)
(* ============================================================ *)

Theorem ams_l1_le : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (real_list_sum Token
             (fun x : Token => real_abs (real_minus_r
                            (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                            (ams_w T Ht x))) vocab)
          (real_plus (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))
                     (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))).
Proof.
  intros T Ht.
  (* L1 == k·D + M（逐点折叠 + 函数形开关求和恒等式）⟹ == M+M ⟹ ≤ n·d+n·d *)
  apply (real_le_trans
           (real_list_sum Token
              (fun x : Token => real_abs (real_minus_r
                             (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                             (ams_w T Ht x))) vocab)
           (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                 (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                               (ams_w T Ht m)))
                      (ams_M T Ht))
           (real_plus (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))
                      (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht)))).
  - (* L1 ≤ k·D + M：eq-链后 le_refl 适配 *)
    apply (RealSetoid.real_le_id_l
             (real_list_sum Token
                (fun x : Token => real_abs (real_minus_r
                               (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                               (ams_w T Ht x))) vocab)
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                 (ams_w T Ht m)))
                        (ams_M T Ht))
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                 (ams_w T Ht m)))
                        (ams_M T Ht))).
    + apply (real_eq_trans
               (real_list_sum Token
                  (fun x : Token => real_abs (real_minus_r
                                 (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
                                 (ams_w T Ht x))) vocab)
               (real_list_sum Token
                  (ams_mswitch (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                             (ams_w T Ht m))
                               (ams_w T Ht)) vocab)
               (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                     (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                   (ams_w T Ht m)))
                          (ams_M T Ht))).
      * apply real_list_sum_ext. intro w.
        exact (ams_abs_pointwise T Ht w).
      * exact (ams_switch_sum_fun
                 (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                               (ams_w T Ht m))
                 (ams_w T Ht) vocab).
    + apply real_le_refl.
  - (* k·D + M == M + M（②）⟹ M+M ≤ n·d + n·d（③×2） *)
    apply (real_le_trans
             (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                   (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                 (ams_w T Ht m)))
                        (ams_M T Ht))
             (real_plus (ams_M T Ht) (ams_M T Ht))
             (real_plus (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))
                        (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht)))).
    + apply (RealSetoid.real_le_id_l
               (real_plus (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                                     (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                                   (ams_w T Ht m)))
                          (ams_M T Ht))
               (real_plus (ams_M T Ht) (ams_M T Ht))
               (real_plus (ams_M T Ht) (ams_M T Ht))).
      * exact (RealSetoid.real_eq_plus_compat
                 (real_mult (real_of_nat (alm_k Token vocab token_eq_dec m))
                            (real_minus_r (alm_invk Token vocab token_eq_dec m m_in_vocab)
                                          (ams_w T Ht m)))
                 (ams_M T Ht) (ams_M T Ht) (ams_M T Ht)
                 (ams_deficit_eq T Ht) (real_eq_refl (ams_M T Ht))).
      * apply real_le_refl.
    + apply (real_le_trans
               (real_plus (ams_M T Ht) (ams_M T Ht))
               (real_plus (ams_M T Ht)
                          (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht)))
               (real_plus (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht))
                          (real_mult (real_of_nat (length vocab)) (decay_T gamma T Ht)))).
      * apply real_le_plus_compat.
        -- apply real_le_refl.
        -- exact (ams_mass_rest_le T Ht).
      * apply real_le_plus_compat.
        -- exact (ams_mass_rest_le T Ht).
        -- apply real_le_refl.
Qed.

End AmsMassSplit.

(* ============================================================ *)
(* 提取口（计算核；判据 = 零 magic）+ 公理面审计           *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Extraction "attn_masssplit_q18c.ml"
  ams_w ams_M ams_mswitch alm_switch alm_k count_token.

Print Assumptions ams_mass_split.
Print Assumptions ams_deficit_eq.
Print Assumptions ams_mass_rest_le.
Print Assumptions ams_l1_le.

(* ---- ToyR 追印：清单件假设面逐件打印，判读全闭 ---- *)
Print Assumptions ams_sum_switch_self.
