(* ============================================================ *)
(* ============================================================ *)
(*   bcoef 加法同调/Qeq 同调字段——本件以显式假设（hplus/hwd）承载，   *)
(*   上游扩类后即消」；UpReqBanachClassExt.v 尾注（:197-200）         *)
(*   「下游 18 件摘除 hplus/hwd 携带（bpa_scal_plus/bpa_pair_mid/     *)
(*   bpa_pair_tail/bpa_bpow_add/bpa_esp_term_binom/bpa_esp_binom     *)
(*   bcoef_plus : forall q r, bae (bplus (bcoef q) (bcoef r))        *)
(*                                (bcoef (q + r))  （Exp.v:89）      *)
(*   bcoef_wd   : forall q r, q == r -> bae (bcoef q) (bcoef r)      *)
(*                                                 （Exp.v:90）      *)
(*   bnorm_wd 余域同日 Id→QeqT（Exp.v:80）。                          *)
(* 本件承载（前缀 bnh_，全库零撞名：grep "bnh_|BanachNoHyp"           *)
(*   三树零命中）：                                                  *)
(*   S0 形状机器锚两件：类字段 ≡ BA 件显式假设形（类型即证明，        *)
(*      BCE 卡 bxce_hplus_shape 同款技法）；                          *)
(*   S1 标量面：bnh_scal_plus（消 hplus）/ bnh_mult_coef_wd（消 hwd    *)
(*      乘法下拉形）；                                                *)
(*   S2 配对件：bnh_pair_mid（消 hplus）/ bnh_pair_tail（消 hwd）；    *)
(*   S3 主件：bnh_bpow_add（二项式恒等，hab 数学前提保留，             *)
(*      hplus/hwd 双假设摘除）；                                      *)
(*   S4 E 级数：bnh_esp_term_binom / bnh_esp_binom（二项式重组）。     *)
(* 同位对账（原假设 → 新字段消费）：                                   *)
(*   bpa_scal_plus  的 hplus → @bcoef_plus B q r                     *)
(*   bpa_pair_mid   的 hplus → bnh_scal_plus（底座=bcoef_plus 字段）  *)
(*   bpa_pair_tail  的 hwd   → @bcoef_wd  B q r H                    *)
(*   bpa_bpow_add   的 hplus/hwd → S1/S2 件级联（根=bcoef 两字段）    *)
(*   bpa_esp_term_binom / bpa_esp_binom 同上；                        *)
(*   hab : bae (a·b) (b·a) 系数学前提（非交换代数二项式必需），        *)
(*   同位保留，非接口假设。                                           *)
(* 依赖复用（Require，禁重定义）：                                    *)
(*   UpReqBanachExp（手术后类 BanachAlg/bpow/exp_series_partial）；    *)
(*   UpReqBanachProd（bsum 引擎：bsum/bsum_ext/bsum_plus/bsum_rot/    *)
(*     bsum_scal/bplus_swap4/esp_as_bsum）；                          *)
(*   UpReqBanachAdd（零假设件白名单复用：Q 层 bpa_binom 系            *)
(*     bpa_binom/bpa_binom_out + bae 助件 bpa_bmult_zero_l/           *)
(*     bpa_bsum_mult_r/bpa_term_A/bpa_term_B/bpa_pair_head/           *)
(*     bpa_scal_repack——该八件本不带 hplus/hwd，逐字复用不重证）。     *)
(* 红线自审：                                                        *)
(*   —— 禁词全零（按全文件计含头注：承认件/半途弃证/自由变元声明/      *)
(*      中途弃证六类字面零命中）；                                    *)
(*   —— 语句面全 Set 层：bae:BA→BA→Set 承载等词、Qeq 仅既有假设       *)
(*      面形、QltT/QleT'/sigT 承载序与存在，零 Prop 泄露；            *)
(*      bae 面一律 change（定义形）+ bae_trans 显式中件链，            *)
(*      无 rewrite 于 bae（Q 层 Qeq 的 setoid 改写除外，库内先例）；   *)
(*   —— 全件 Qed 真证，term-mode 显式组装，无降级占位；                *)
(*   —— 提取探针 Obj.magic=0（独立小探针，验后删，证据在日志）；       *)
(*   —— Print Assumptions 全件 Closed（文末八连打，证据在编译日志）。  *)
(* 工程注（沿 B3Sv2/BINV3/PB 三卡）：                                 *)
(*   类字段/字段引理一律 @显式喂实例（Rocq 9 类投影实例参隐式，        *)
(*   「先槽后证」）；bmult_wd 源对 (a,b) 在前、目标对 (c,d) 在后        *)
(*   （左固定 X T Y T）；bae_trans 中件在 y 槽第 3 显式参；            *)
(*   主链 L1..L13 分段 assert + 末尾 @bae_trans 项式嵌套组链           *)
(*   （沿 UpReqBanachAdd.v 原骨架逐段同位）。                          *)
(* 编译配方（温控内，Rocq 9.1 同轨）：                                *)
(*   source Live/toolchain/env.sh && cd Live/build                    *)
(*   cpu_guard.sh -c "rocq compile -Q . '' BanachNoHyp.v"             *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachProd.
Require Import UpReqBanachAdd.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S0：形状机器锚 —— 类字段 ≡ BA 件显式假设形（类型即证明）           *)
(* （BCE 卡技法：Definition 体注旧假设形，类型检查即机器验证；        *)
(*   提取实形 e.bcoef_plus q r 为字段消费铁证。）                     *)
(* ============================================================ *)

(* 锚一：bcoef_plus 字段形 ≡ hplus 假设形（bcoef 加法同调） *)
Definition bnh_hplus_shape (B : BanachAlg) (q r : Q) :
  @bae B (@bplus B (@bcoef B q) (@bcoef B r)) (@bcoef B (q + r)%Q)
  := @bcoef_plus B q r.

(* 锚二：bcoef_wd 字段形 ≡ hwd 假设形（Qeq 同调入 bcoef） *)
Definition bnh_hwd_shape (B : BanachAlg) (q r : Q) :
  q == r -> @bae B (@bcoef B q) (@bcoef B r)
  := @bcoef_wd B q r.

(* ============================================================ *)
(* S1：标量面零假设重证                                               *)
(* ============================================================ *)

(* 件一（↔ bpa_scal_plus，hplus 摘除）：标量配对合并
   bcoef q·T + bcoef r·T == bcoef (q+r)·T
   （消费类字段 bcoef_plus：bdistrib_r 对称向 + bmult_wd 右槽换形） *)
Lemma bnh_scal_plus : forall (B : BanachAlg) (q r : Q) (T : (@BA B)),
  @bae B (@bplus B (@bmult B (@bcoef B q) T) (@bmult B (@bcoef B r) T))
         (@bmult B (@bcoef B (q + r)%Q) T).
Proof.
  intros B q r T. eapply bae_trans.
  - apply (@bae_sym B).
    exact (@bdistrib_r B (@bcoef B q) (@bcoef B r) T).
  - apply (@bmult_wd B (@bplus B (@bcoef B q) (@bcoef B r)) T
                       (@bcoef B (q + r)%Q) T).
    + exact (@bcoef_plus B q r).
    + apply (@bae_refl B).
Qed.

(* 件二（hwd 乘法下拉形，↔ ClassExt bxce_mult_coef_wd 在普通类上的同位）：
   q == r ⟹ bcoef q·X == bcoef r·X（消费类字段 bcoef_wd） *)
Lemma bnh_mult_coef_wd : forall (B : BanachAlg) (q r : Q) (X : (@BA B)),
  q == r ->
  @bae B (@bmult B (@bcoef B q) X) (@bmult B (@bcoef B r) X).
Proof.
  intros B q r X H.
  apply (@bmult_wd B (@bcoef B q) X (@bcoef B r) X).
  - exact (@bcoef_wd B q r H).
  - apply (@bae_refl B).
Qed.

(* ============================================================ *)
(* S2：配对件零假设重证（Pascal 装配的对角/出界收拢位）                *)
(* ============================================================ *)

(* 件三（↔ bpa_pair_mid，hplus 摘除）：配对中段
   gA i + gB (S i) == h (S i)（i < n'）
   系数 C(n',i)+C(n',S i) 恰为 C(S n',S i) 定义形（Pascal 递归
   配对序）；b 幂 S(n'−S i)=n'−i（lia 桥）与 S n'−S i（iota）归一；
   合并步消费 bnh_scal_plus（底座=bcoef_plus 类字段） *)
Lemma bnh_pair_mid : forall (B : BanachAlg) (a b : (@BA B)) (n' i : nat),
  (i < n')%nat ->
  @bae B (@bplus B
            (@bmult B (@bcoef B (bpa_binom n' i))
                      (@bmult B (bpow B a (Datatypes.S i))
                               (bpow B b (Nat.sub n' i))))
            (@bmult B (@bcoef B (bpa_binom n' (Datatypes.S i)))
                      (@bmult B (bpow B a (Datatypes.S i))
                               (bpow B b (Datatypes.S (Nat.sub n' (Datatypes.S i)))))))
         (@bmult B (@bcoef B (bpa_binom (Datatypes.S n') (Datatypes.S i)))
                   (@bmult B (bpow B a (Datatypes.S i))
                            (bpow B b (Nat.sub (Datatypes.S n') (Datatypes.S i))))).
Proof.
  intros B a b n' i Hi.
  assert (E : (Datatypes.S (Nat.sub n' (Datatypes.S i)))%nat = Nat.sub n' i)
    by lia.
  rewrite E.
  change (bpa_binom (Datatypes.S n') (Datatypes.S i))
    with (bpa_binom n' i + bpa_binom n' (Datatypes.S i))%Q.
  change (bpow B b (Nat.sub (Datatypes.S n') (Datatypes.S i)))
    with (bpow B b (Nat.sub n' i)).
  eapply bae_trans.
  - exact (bnh_scal_plus B (bpa_binom n' i) (bpa_binom n' (Datatypes.S i))
             (@bmult B (bpow B a (Datatypes.S i)) (bpow B b (Nat.sub n' i)))).
  - apply (@bae_refl B).
Qed.

(* 件四（↔ bpa_pair_tail，hwd 摘除）：配对尾项 gA n' == h (S n')
   C(S n',S n') ≡ C(n',n')+C(n',S n') 定义形；C(n',S n')==0（出界，
   bpa_binom_out）经类字段 bcoef_wd + Qplus_0_r 收拢；b 幂双侧 iota 归一 *)
Lemma bnh_pair_tail : forall (B : BanachAlg) (a b : (@BA B)) (n' : nat),
  @bae B (@bmult B (@bcoef B (bpa_binom n' n'))
                   (@bmult B (bpow B a (Datatypes.S n'))
                            (bpow B b (Nat.sub n' n'))))
         (@bmult B (@bcoef B (bpa_binom (Datatypes.S n') (Datatypes.S n')))
                   (@bmult B (bpow B a (Datatypes.S n'))
                            (bpow B b (Nat.sub (Datatypes.S n')
                                               (Datatypes.S n'))))).
Proof.
  intros B a b n'.
  change (bpa_binom (Datatypes.S n') (Datatypes.S n'))
    with (bpa_binom n' n' + bpa_binom n' (Datatypes.S n'))%Q.
  change (bpow B b (Nat.sub (Datatypes.S n') (Datatypes.S n')))
    with (bpow B b (Nat.sub n' n')).
  apply (@bae_sym B).
  apply (@bmult_wd B
           (@bcoef B (bpa_binom n' n' + bpa_binom n' (Datatypes.S n'))%Q)
           (@bmult B (bpow B a (Datatypes.S n')) (bpow B b (Nat.sub n' n')))
           (@bcoef B (bpa_binom n' n'))
           (@bmult B (bpow B a (Datatypes.S n')) (bpow B b (Nat.sub n' n')))).
  - apply (@bcoef_wd B (bpa_binom n' n' + bpa_binom n' (Datatypes.S n'))%Q
             (bpa_binom n' n')).
    setoid_rewrite (bpa_binom_out n' (Datatypes.S n') (Nat.lt_succ_diag_r n')).
    apply Qplus_0_r.
  - apply (@bae_refl B).
Qed.

(* ============================================================ *)
(* S3：主件（↔ bpa_bpow_add，hplus/hwd 双摘除，hab 数学前提保留）      *)
(* ============================================================ *)

(* bpow_add 二项式恒等：ab=ba ⟹
   bpow (a+b) n == Σ_{k≤n} C(n,k)·a^k·b^(n−k)
   （Pascal 归纳 L1..L13 显式中件链，骨架与 UpReqBanachAdd.v 逐段同位；
     ①④②③⑤..⑨ 各步消费面：bsum 引擎（Prod）+ 零假设助件（Add 白名单）
     + 配对件 bnh_pair_mid/bnh_pair_tail（本件 S2，根=类字段）。） *)
Lemma bnh_bpow_add : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bmult B a b) (@bmult B b a) ->
  forall n : nat,
    @bae B (bpow B (@bplus B a b) n)
           (bsum B (Datatypes.S n)
              (fun k : nat =>
                 @bmult B (@bcoef B (bpa_binom n k))
                          (@bmult B (bpow B a k)
                                   (bpow B b (Nat.sub n k))))).
Proof.
  intros B a b hab n.
  induction n as [| n' IH].
  - (* 基例 n=0：bone == bzero + C(0,0)·(bone·bone) *)
    change (bpow B (@bplus B a b) 0%nat) with (@bone B).
    change (bsum B (Datatypes.S 0%nat)
              (fun k : nat => @bmult B (@bcoef B (bpa_binom 0%nat k))
                                       (@bmult B (bpow B a k)
                                                (bpow B b (Nat.sub 0%nat k)))))
      with (@bplus B (@bzero B)
              (@bmult B (@bcoef B (bpa_binom 0%nat 0%nat))
                       (@bmult B (@bpow B a 0%nat)
                                (@bpow B b (Nat.sub 0%nat 0%nat))))).
    assert (E : bpa_binom 0%nat 0%nat = 1%Q) by reflexivity.
    rewrite E.
    change (@bpow B a 0%nat) with (@bone B).
    change (@bpow B b (Nat.sub 0%nat 0%nat)) with (@bone B).
    assert (HX : @bae B (@bmult B (@bcoef B 1%Q)
                                  (@bmult B (@bone B) (@bone B)))
                        (@bone B)).
    { eapply bae_trans.
      - apply (@bmult_wd B (@bcoef B 1%Q)
                 (@bmult B (@bone B) (@bone B))
                 (@bone B)
                 (@bmult B (@bone B) (@bone B))).
        + exact (@bcoef_one B).
        + apply (@bae_refl B).
      - eapply bae_trans.
        + exact (@bmult_one_l B (@bmult B (@bone B) (@bone B))).
        + exact (@bmult_one_l B (@bone B)). }
    eapply bae_trans.
    + apply (@bae_sym B). exact (@bplus_zero_l B (@bone B)).
    + apply (@bplus_wd_r B).
      apply (@bae_sym B). exact HX.
  - (* 归纳步：Pascal 配对组装（蓝图 E152-13 降层） *)
    set (g := fun k : nat =>
                @bmult B (@bcoef B (bpa_binom n' k))
                         (@bmult B (bpow B a k)
                                  (bpow B b (Nat.sub n' k)))).
    set (gA := fun k : nat =>
                 @bmult B (@bcoef B (bpa_binom n' k))
                          (@bmult B (bpow B a (Datatypes.S k))
                                   (bpow B b (Nat.sub n' k)))).
    set (gB := fun k : nat =>
                 @bmult B (@bcoef B (bpa_binom n' k))
                          (@bmult B (bpow B a k)
                                   (bpow B b (Datatypes.S (Nat.sub n' k))))).
    set (h := fun k : nat =>
                @bmult B (@bcoef B (bpa_binom (Datatypes.S n') k))
                         (@bmult B (bpow B a k)
                                  (bpow B b (Nat.sub (Datatypes.S n') k)))).
    (* ① 幂拆出 + IH 代入 *)
    assert (L1 : @bae B (@bmult B (bpow B (@bplus B a b) n') (@bplus B a b))
                        (@bmult B (bsum B (Datatypes.S n') g)
                                  (@bplus B a b))).
    { exact (@bmult_wd B (bpow B (@bplus B a b) n')
                       (@bplus B a b)
                       (bsum B (Datatypes.S n') g)
                       (@bplus B a b) IH
                       (@bae_refl B (@bplus B a b))). }
    (* ② (a+b) 拉入和内（bsum_mult_r 对称向） *)
    assert (L2 : @bae B (@bmult B (bsum B (Datatypes.S n') g)
                                  (@bplus B a b))
                        (bsum B (Datatypes.S n')
                                  (fun k : nat => @bmult B (g k) (@bplus B a b)))).
    { apply (@bae_sym B).
      exact (bpa_bsum_mult_r B (Datatypes.S n') (@bplus B a b) g). }
    (* ③ 逐项 bdistrib_l 拆 a 项/b 项（ext 直拆双和） *)
    assert (L3 : @bae B (bsum B (Datatypes.S n')
                                  (fun k : nat => @bmult B (g k) (@bplus B a b)))
                        (@bplus B (bsum B (Datatypes.S n')
                                            (fun k : nat => @bmult B (g k) a))
                                  (bsum B (Datatypes.S n')
                                            (fun k : nat => @bmult B (g k) b)))).
    { eapply bae_trans.
      - apply (bsum_ext B (Datatypes.S n')
                  (fun k : nat => @bmult B (g k) (@bplus B a b))
                  (fun k : nat =>
                     @bplus B (@bmult B (g k) a) (@bmult B (g k) b))).
        intros k _. apply (@bdistrib_l B (g k) a b).
      - apply (bsum_plus B (Datatypes.S n')
                  (fun k : nat => @bmult B (g k) a)
                  (fun k : nat => @bmult B (g k) b)). }
    (* ④ 逐项清形：a 项提幂（bpa_term_A）、b 项清交换（bpa_term_B） *)
    assert (L4 : @bae B (@bplus B (bsum B (Datatypes.S n')
                                            (fun k : nat => @bmult B (g k) a))
                                  (bsum B (Datatypes.S n')
                                            (fun k : nat => @bmult B (g k) b)))
                        (@bplus B (bsum B (Datatypes.S n') gA)
                                  (bsum B (Datatypes.S n') gB))).
    { apply (@bplus_wd B
               (bsum B (Datatypes.S n') (fun k : nat => @bmult B (g k) a))
               (bsum B (Datatypes.S n') (fun k : nat => @bmult B (g k) b))
               (bsum B (Datatypes.S n') gA)
               (bsum B (Datatypes.S n') gB)).
      - apply (bsum_ext B (Datatypes.S n')
                  (fun k : nat => @bmult B (g k) a) gA).
        intros k _.
        exact (bpa_term_A B a b hab (bpa_binom n' k) k (Nat.sub n' k)).
      - apply (bsum_ext B (Datatypes.S n')
                  (fun k : nat => @bmult B (g k) b) gB).
        intros k _.
        exact (bpa_term_B B a b (bpa_binom n' k) k (Nat.sub n' k)). }
    (* ⑤ b 和换元（rot 首项提出） *)
    assert (L5 : @bae B (@bplus B (bsum B (Datatypes.S n') gA)
                                  (bsum B (Datatypes.S n') gB))
                        (@bplus B (bsum B (Datatypes.S n') gA)
                                  (@bplus B (gB 0%nat)
                                     (bsum B n'
                                        (fun i : nat => gB (Datatypes.S i)))))).
    { apply (@bplus_wd_r B). exact (bsum_rot B n' gB). }
    (* ⑥ a 和尾项拆出（bsum 定义形，转换面闭合） *)
    assert (L6 : @bae B (@bplus B (bsum B (Datatypes.S n') gA)
                                  (@bplus B (gB 0%nat)
                                     (bsum B n'
                                        (fun i : nat => gB (Datatypes.S i)))))
                        (@bplus B (@bplus B (bsum B n' gA) (gA n'))
                                  (@bplus B (gB 0%nat)
                                     (bsum B n'
                                        (fun i : nat => gB (Datatypes.S i)))))).
    { apply (@bae_refl B). }
    (* ⑦ 加法 AC 重排：gB 0 提首、gA n' 收尾、两主段并列 *)
    assert (L7 : @bae B (@bplus B (@bplus B (bsum B n' gA) (gA n'))
                                  (@bplus B (gB 0%nat)
                                     (bsum B n'
                                        (fun i : nat => gB (Datatypes.S i)))))
                        (@bplus B (@bplus B (gB 0%nat) (bsum B n' gA))
                                  (@bplus B (bsum B n'
                                                (fun i : nat => gB (Datatypes.S i)))
                                            (gA n')))).
    { eapply bae_trans.
      - exact (bplus_swap4 B (bsum B n' gA) (gA n') (gB 0%nat)
                   (bsum B n' (fun i : nat => gB (Datatypes.S i)))).
      - apply (@bplus_wd B (@bplus B (bsum B n' gA) (gB 0%nat))
                 (@bplus B (gA n')
                            (bsum B n' (fun i : nat => gB (Datatypes.S i))))
                 (@bplus B (gB 0%nat) (bsum B n' gA))
                 (@bplus B (bsum B n'
                               (fun i : nat => gB (Datatypes.S i)))
                            (gA n'))).
        + exact (@bplus_comm B (bsum B n' gA) (gB 0%nat)).
        + exact (@bplus_comm B (gA n')
                   (bsum B n' (fun i : nat => gB (Datatypes.S i)))). }
    assert (L8 : @bae B (@bplus B (@bplus B (gB 0%nat) (bsum B n' gA))
                                  (@bplus B (bsum B n'
                                                (fun i : nat => gB (Datatypes.S i)))
                                            (gA n')))
                        (@bplus B (gB 0%nat)
                           (@bplus B (@bplus B (bsum B n' gA)
                                                (bsum B n'
                                                   (fun i : nat => gB (Datatypes.S i))))
                                     (gA n')))).
    { eapply bae_trans.
      - apply (@bae_sym B).
        exact (@bplus_assoc B (gB 0%nat) (bsum B n' gA)
                 (@bplus B (bsum B n' (fun i : nat => gB (Datatypes.S i)))
                            (gA n'))).
      - apply (@bplus_wd_r B).
        exact (@bplus_assoc B (bsum B n' gA)
                 (bsum B n' (fun i : nat => gB (Datatypes.S i)))
                 (gA n')). }
    (* ⑧ Pascal 中段并段 + 逐项配对合并（消费 bnh_pair_mid）+ 首尾对位 *)
    assert (L9 : @bae B (@bplus B (gB 0%nat)
                                  (@bplus B (@bplus B (bsum B n' gA)
                                                       (bsum B n'
                                                          (fun i : nat => gB (Datatypes.S i))))
                                            (gA n')))
                        (@bplus B (gB 0%nat)
                                  (@bplus B (bsum B n'
                                                (fun i : nat =>
                                                   @bplus B (gA i)
                                                     (gB (Datatypes.S i))))
                                            (gA n')))).
    { apply (@bplus_wd_r B
               (@bplus B (@bplus B (bsum B n' gA)
                                  (bsum B n'
                                     (fun i : nat => gB (Datatypes.S i))))
                          (gA n'))
               (@bplus B (bsum B n'
                             (fun i : nat => @bplus B (gA i) (gB (Datatypes.S i))))
                          (gA n'))
               (gB 0%nat)).
      apply (@bplus_wd_l B
               (@bplus B (bsum B n' gA)
                          (bsum B n' (fun i : nat => gB (Datatypes.S i))))
               (bsum B n'
                  (fun i : nat => @bplus B (gA i) (gB (Datatypes.S i))))
               (gA n')).
      apply (@bae_sym B).
      exact (bsum_plus B n' gA (fun i : nat => gB (Datatypes.S i))). }
    assert (L10 : @bae B (@bplus B (gB 0%nat)
                                   (@bplus B (bsum B n'
                                                 (fun i : nat =>
                                                    @bplus B (gA i)
                                                      (gB (Datatypes.S i))))
                                              (gA n')))
                         (@bplus B (gB 0%nat)
                                   (@bplus B (bsum B n'
                                                 (fun i : nat => h (Datatypes.S i)))
                                              (gA n')))).
    { apply (@bplus_wd_r B
               (@bplus B (bsum B n'
                             (fun i : nat => @bplus B (gA i) (gB (Datatypes.S i))))
                          (gA n'))
               (@bplus B (bsum B n' (fun i : nat => h (Datatypes.S i)))
                          (gA n'))
               (gB 0%nat)).
      apply (@bplus_wd_l B
               (bsum B n'
                  (fun i : nat => @bplus B (gA i) (gB (Datatypes.S i))))
               (bsum B n' (fun i : nat => h (Datatypes.S i)))
               (gA n')).
      apply (bsum_ext B n'
                (fun i : nat => @bplus B (gA i) (gB (Datatypes.S i)))
                (fun i : nat => h (Datatypes.S i))).
      intros i Hi.
      exact (bnh_pair_mid B a b n' i Hi). }
    assert (L11 : @bae B (@bplus B (gB 0%nat)
                                   (@bplus B (bsum B n'
                                                 (fun i : nat => h (Datatypes.S i)))
                                              (gA n')))
                         (@bplus B (@bplus B (gB 0%nat)
                                               (bsum B n'
                                                  (fun i : nat => h (Datatypes.S i))))
                                            (gA n'))).
    { exact (@bplus_assoc B (gB 0%nat)
               (bsum B n' (fun i : nat => h (Datatypes.S i))) (gA n')). }
    assert (L12 : @bae B (@bplus B (@bplus B (gB 0%nat)
                                               (bsum B n'
                                                  (fun i : nat => h (Datatypes.S i))))
                                            (gA n'))
                         (@bplus B (@bplus B (h 0%nat)
                                               (bsum B n'
                                                  (fun i : nat => h (Datatypes.S i))))
                                            (h (Datatypes.S n')))).
    { apply (@bplus_wd B
               (@bplus B (gB 0%nat)
                          (bsum B n' (fun i : nat => h (Datatypes.S i))))
               (gA n')
               (@bplus B (h 0%nat)
                          (bsum B n' (fun i : nat => h (Datatypes.S i))))
               (h (Datatypes.S n'))).
      - apply (@bplus_wd B (gB 0%nat)
                 (bsum B n' (fun i : nat => h (Datatypes.S i)))
                 (h 0%nat)
                 (bsum B n' (fun i : nat => h (Datatypes.S i)))).
        + exact (bpa_pair_head B a b n').
        + apply (@bae_refl B).
      - exact (bnh_pair_tail B a b n'). }
    (* ⑨ 目标和拆形闭合：rot 反向归位（bsum 定义形 change + 转换） *)
    assert (L13 : @bae B (@bplus B (@bplus B (h 0%nat)
                                               (bsum B n'
                                                  (fun i : nat => h (Datatypes.S i))))
                                            (h (Datatypes.S n')))
                         (bsum B (Datatypes.S (Datatypes.S n')) h)).
    { change (bsum B (Datatypes.S (Datatypes.S n')) h)
        with (@bplus B (bsum B (Datatypes.S n') h) (h (Datatypes.S n'))).
      eapply bae_trans.
      - apply (@bplus_wd_l B).
        apply (@bae_sym B). exact (bsum_rot B n' h).
      - apply (@bae_refl B). }
    (* 幂拆出（定义形）+ L1..L13 组链 *)
    change (bpow B (@bplus B a b) (Datatypes.S n'))
      with (@bmult B (bpow B (@bplus B a b) n') (@bplus B a b)).
    exact (@bae_trans B _ _ _ L1
             (@bae_trans B _ _ _ L2
                (@bae_trans B _ _ _ L3
                   (@bae_trans B _ _ _ L4
                      (@bae_trans B _ _ _ L5
                         (@bae_trans B _ _ _ L6
                            (@bae_trans B _ _ _ L7
                               (@bae_trans B _ _ _ L8
                                  (@bae_trans B _ _ _ L9
                                     (@bae_trans B _ _ _ L10
                                        (@bae_trans B _ _ _ L11
                                           (@bae_trans B _ _ _ L12 L13)))))))))))).
Qed.

(* ============================================================ *)
(* S4：E 级数二项式重组（↔ bpa_esp_term_binom/bpa_esp_binom）          *)
(* ============================================================ *)

(* 项级（↔ bpa_esp_term_binom，hab 保留 + hplus/hwd 摘除）：
   bpow (a+b) k·(1/k!) == Σ_{j≤k} (C(k,j)/k!)·a^j·b^(k−j)
   （bnh_bpow_add 喂 bmult_wd 左槽 + bsum_scal 拉出 + 重打包
     bpa_scal_repack（bcoef_mult/comm 类字段链，零假设）） *)
Lemma bnh_esp_term_binom : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bmult B a b) (@bmult B b a) ->
  forall k : nat,
    @bae B (@bmult B (bpow B (@bplus B a b) k)
                     (@bcoef B (/ q_fact k)))
           (bsum B (Datatypes.S k)
              (fun j : nat =>
                 @bmult B (@bcoef B (bpa_binom k j * / q_fact k)%Q)
                          (@bmult B (bpow B a j)
                                   (bpow B b (Nat.sub k j))))).
Proof.
  intros B a b hab k.
  set (F := fun j : nat =>
              @bmult B (@bcoef B (bpa_binom k j))
                       (@bmult B (bpow B a j)
                                (bpow B b (Nat.sub k j)))).
  eapply bae_trans.
  - apply (@bmult_wd B (bpow B (@bplus B a b) k)
                     (@bcoef B (/ q_fact k))
                     (bsum B (Datatypes.S k) F)
                     (@bcoef B (/ q_fact k))).
    + exact (bnh_bpow_add B a b hab k).
    + apply (@bae_refl B).
  - eapply bae_trans.
    + apply (@bae_sym B).
      exact (bsum_scal B (Datatypes.S k) (/ q_fact k) F).
    + apply (bsum_ext B (Datatypes.S k)
                (fun j : nat => @bmult B (F j) (@bcoef B (/ q_fact k)))
                (fun j : nat =>
                   @bmult B (@bcoef B (bpa_binom k j * / q_fact k)%Q)
                            (@bmult B (bpow B a j)
                                     (bpow B b (Nat.sub k j))))).
      intros j _.
      exact (bpa_scal_repack B (bpa_binom k j) (/ q_fact k)
               (@bmult B (bpow B a j) (bpow B b (Nat.sub k j)))).
Qed.

(* 级数级（↔ bpa_esp_binom，hab 保留 + hplus/hwd 摘除）：
   esp n (a+b) == Σ_{k≤n} Σ_{j≤k} (C(k,j)/k!)·a^j·b^(k−j)
   （esp_as_bsum 展开 + 逐项 bnh_esp_term_binom，对接 esp_as_bsum 面） *)
Lemma bnh_esp_binom : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bmult B a b) (@bmult B b a) ->
  forall n : nat,
    @bae B (exp_series_partial B (@bplus B a b) n)
           (bsum B (Datatypes.S n)
              (fun k : nat =>
                 bsum B (Datatypes.S k)
                   (fun j : nat =>
                      @bmult B (@bcoef B (bpa_binom k j * / q_fact k)%Q)
                               (@bmult B (bpow B a j)
                                        (bpow B b (Nat.sub k j)))))).
Proof.
  intros B a b hab n.
  eapply bae_trans.
  - exact (esp_as_bsum B (@bplus B a b) n).
  - apply (bsum_ext B (Datatypes.S n)
              (fun k : nat => @bmult B (bpow B (@bplus B a b) k)
                                      (@bcoef B (/ q_fact k)))
              (fun k : nat =>
                 bsum B (Datatypes.S k)
                   (fun j : nat =>
                      @bmult B (@bcoef B (bpa_binom k j * / q_fact k)%Q)
                               (@bmult B (bpow B a j)
                                        (bpow B b (Nat.sub k j)))))).
    intros k _.
    exact (bnh_esp_term_binom B a b hab k).
Qed.

(* ============================================================ *)
(*   ① 本件即 UpReqBanachAdd.v 挂账① 的执行：六件 hplus/hwd 携带件     *)
(*     下游新消费面一律 Require 本件取 bnh_ 系；冻结件 bpa_ 系维持      *)
(*     原状只读不回改（双轨并存，禁互替）。                            *)
(*   ② hab : bae (a·b) (b·a) 为非交换代数二项式恒等的数学前提，         *)
(*     同位保留（bpa_ 件同款），非接口假设。                           *)
(* ============================================================ *)

Print Assumptions bnh_hplus_shape.
Print Assumptions bnh_hwd_shape.
Print Assumptions bnh_scal_plus.
Print Assumptions bnh_mult_coef_wd.
Print Assumptions bnh_pair_mid.
Print Assumptions bnh_pair_tail.
Print Assumptions bnh_bpow_add.
Print Assumptions bnh_esp_term_binom.
Print Assumptions bnh_esp_binom.
