(* ==========================================================================)
   abl_concmix_step_calc.v — 收敛计算器滚转第三件（ConcMixSelFeed 面，cmc_ 前缀）
   谱系: born-green 独立成件（非既有件改写；使命见下）。
   使命: 按 K 矿脉表与任务项——把 ConcMixSelFeed 收缩收敛面的步数见证升格为
     mtg_k_calc 式可提取计算器。现档重拍实锤: ConcMixSelFeed.v 本体（300 行，
     与 Live 同文）为零收缩件的 cms_ 接口转接层，其收缩收敛面在供给链
     UpReqConcMixSel.v 的 cmk_attention_mixing_time（ConcMixSelFeed 头注自注
     「cb1_mixing_cert 闭合件」位）——率显式在案: kappa := omd := one − delta_star,
     delta_star = lo·lo, lo = rsq_exp_pos_fn(invT·opp Delta) 即 e^(-Delta/T) 的
     req 面形，双证书 cmk_omd_pos/cmk_ds_omd_lt_one 导出在役——按首件策略
     A 支「率显式在案则直接定点档」执行，抽取步骤记录于头注与本注释尾。
   件名与前缀: abl_concmix_step_calc.v，cmc_ 前缀（施工前 grep 防撞：全库零命中）。
   本件陈述（三段）:
     Part 2 nat 定点档（真 Fixpoint）: cmc_ceil_div/cmc_iter/cmc_pow_iter/
       cmc_k_enum（有界燃料衰减枚举，x 走上取整乘步 x·p/q 直到落入预算 E）＋
       正确性两半（cmc_k_enum_correct 上取整面 / cmc_k_enum_logface 精确面
       x·p^N ≤ E·q^N，即 log 模量方程 nat 形）＋【本件新增·BQ 诚实边界4
       的闭合】cmc_iter_lt_decay/cmc_iter_lt_half/cmc_iter_lt_q 严格衰减
       三件＋cmc_fuel_sufficient_gen/half/qbound 燃料充足性见证（调用侧
       Hterm 由 cmc_fuel_sufficient_half/qbound 自动供给，cmc_k_enum_auto）
     Part 3 实面桥: 幂分裂定律（cmc_rpow_mult/cmc_nat_r_pow/cmc_rpow_inv）
       ＋逆唯一（cmc_inv_unique/cmc_mult_one_l）＋nat 单调嵌入桥
       （cmc_nat_le_embed/cmc_nat_le_plus_aux）＋cmc_enum_real_correct
       （有理数据 kappa:=p/q 上枚举读数的实面 le 正确性，零 arch 依赖）。
     Part 1 req 实面对应形（UpReqConcMixSel CmkMixTime 证书子集同形对应）:
       cmc_rate_pos/cmc_rate_lt_one（率抽取: kappa := cmc_omd 双证书直接使用
       宿主导出件）＋cmc_rate_step_calc/cmc_rate_step_calc_correct（mtg_k_calc
       同构通用率面计算器）＋cmc_omd_step_calc/cmc_omd_step_calc_correct
       （抽取率上的具体计算器）＋cmc_mix_step_calc/cmc_mix_step_tv_correct
       （宿主 cmk_attention_mixing_time 的 projT1/projT2 双投影，TV 收缩面
       正确性）＋cmc_mixing_modulus_sigT/cmc_omd_modulus_sigT（sigT 封装）。
   诚实边界记录: ConcMixSelFeed.v 本体零收缩主件（K 表只列其「计算器缺位
     负判据」位），滚转目标按任务项「或 grep 收缩/converge 形主件」条款落至
     供给链闭合件 cmk_attention_mixing_time——现档实拍已记 attn 报告；
     实数 log 到 nat ceil 的构造性桥库内确缺（同 BQ 结论），实面正确性以
     有理数据 kappa:=p/q 闭合（有界精度档），任意实数 kappa 的 ceil 计算
     器仍为开放矿脉；燃料充足性见证限衰减域（half 域 2·p ≤ q 任意 E ≥ 1，
     qbound 域 E ≥ q−1 任意 p<q；p/q 逼近 1 且 E < q−1 时上取整走步可停滞，
     属宿主几何率显式面之外的定点档诚实边界，已记 attn 报告）。
   依赖: S01_BaseRing–S04_RealExpLogConv（RealInterfaceEnhanced 面/lt_le_iff/
     le_id_l 等在役）；Arch_PA_02（nat_to_R/nat_to_R_mult_hom）；UpReqAlgebra
     （req_minus/req_two_pos）；UpReqSampling（rsq_exp_pos_fn/k_titer/
     rsq_bs_list_sum）；UpReqConcMixSel（cmk_attention_mixing_time/cmk_k_select/
     cmk_scale/cmk_r_pow/cmk_omd_pos/cmk_ds_omd_lt_one 均在役）；Stdlib
     Arith/Lia。Require-only 零改动，Live/注册面/缓存根零触碰。
   构造性: 纯构造性/Set 层零 Prop 载体（步数见证 nat 面 sigT；误差谓词 lt/le
     为接口 Set 层值）；非平凡（cmc_k_enum 为真 Fixpoint 上取整枚举）；
     可提取（Separate Extraction Obj.magic=0 附加证，照 BF/BQ 模式）；零公理
     （尾 Print Assumptions 全 Closed 预期）。头注 Not 字面仅宿主接口位
     enum_nonempty 一处（S01_BaseRing.Not，UpReqConcMixSel 同文原样对应）。
   工艺红线: 零 not/~/<> 书写（宿主接口位除外）；零 Qeq 坑（本件零 Q）；
     term-mode 全显式实参（BN 坑卡）；数值定装（BB 坑卡：vm_compute 烟测
     入日志）；坑卡八条操作卡照 BQ（注释禁 literal 右括号星杠/先 simpl 露
     if/term-mode id 链/nat le 不消入 Set）。
   编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&
     ulimit -s 65532 && nice -19 rocq c -native-compiler no -Q
     vo_local_world_unified_0930 "" abl_concmix_step_calc.v（池内执行）。
   ========================================================================== *)

Require Import S07_RealSetoidExpLog.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import Arch_PA_02.
Require Import UpReqAlgebra.
Require Import UpReqSampling.
Require Import UpReqConcMixSel.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Part 2：log 模量方程的 nat 定点枚举解算器（真 Fixpoint/ceil 形）    *)
(*   模量方程 log(a·kappa^N) ≤ log eps 的 nat 面：以 kappa=p/q（0<p<q）、 *)
(*   初值 a=A、预算 eps=E 的公共尺度定点表示，枚举 N 使 A·p^N ≤ E·q^N。  *)
(*   枚举器用上取整衰减步（ceil 除法保上界方向）。本段含燃料充足性       *)
(*   见证三件（BQ 件诚实边界4 的闭合，本件新增）。                       *)
(* ============================================================ *)

(* ceil 整除：上取整 (a+q−1)/q（q ≥ 1），上取整保上界方向 *)
Definition cmc_ceil_div (a q : nat) : nat := Nat.div (a + q - 1) q.

Lemma cmc_ceil_div_le : forall a q, (0 < q)%nat -> (a <= cmc_ceil_div a q * q)%nat.
Proof.
  intros a q Hq. unfold cmc_ceil_div.
  pose proof (Nat.div_mod_eq (a + q - 1) q) as Hdm.
  pose proof (Nat.mod_upper_bound (a + q - 1) q (proj2 (Nat.neq_0_lt_0 q) Hq)) as Hmb.
  lia.
Qed.

(* 衰减步：x 走 kappa=p/q 的定点乘步（上取整） *)
Definition cmc_iter (p q x : nat) : nat := cmc_ceil_div (x * p) q.

Lemma cmc_iter_step_bound : forall p q x, (0 < q)%nat ->
  (x * p <= cmc_iter p q x * q)%nat.
Proof.
  intros p q x Hq. unfold cmc_iter. apply (cmc_ceil_div_le (x * p) q Hq).
Qed.

(* 迭代幂：cmc_iter 的 k 次复合（几何衰减序列的上取整面） *)
Fixpoint cmc_pow_iter (p q x k : nat) : nat :=
  match k with
  | O => x
  | Datatypes.S k' => cmc_iter p q (cmc_pow_iter p q x k')
  end.

(* 复合交换：先走一步再迭代 k 步 = 迭代 k 步后再走一步（同一 S+1 次复合） *)
Lemma cmc_pow_iter_comm : forall p q x k,
  cmc_pow_iter p q (cmc_iter p q x) k = cmc_iter p q (cmc_pow_iter p q x k).
Proof.
  intros p q x k. induction k as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. simpl. reflexivity.
Qed.

(* 枚举器：有界燃料 Fixpoint——x ≤ E 即停（返回已走步数），否则走衰减步再搜 *)
Fixpoint cmc_k_enum (fuel p q x e : nat) : nat :=
  match fuel with
  | O => O
  | Datatypes.S f =>
      if Nat.leb x e then O else Datatypes.S (cmc_k_enum f p q (cmc_iter p q x) e)
  end.

(* 正确性（上取整面）：燃料内可达，枚举返回的 N 步处上取整值 ≤ e *)
Theorem cmc_k_enum_correct : forall fuel p q x e,
  (exists k : nat, (k <= fuel)%nat /\ (cmc_pow_iter p q x k <= e)%nat) ->
  (cmc_pow_iter p q x (cmc_k_enum fuel p q x e) <= e)%nat.
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x e [k [Hk Hbound]].
  - assert (Hk0 : k = 0%nat) by lia. subst k. simpl. exact Hbound.
  - simpl. destruct (Nat.leb x e) eqn:Hle.
    + simpl. exact (proj1 (Nat.leb_le x e) Hle).
    + assert (Hgt : (e < x)%nat) by (apply (proj1 (Nat.leb_gt x e)); exact Hle).
      destruct k as [| k'].
      * simpl in Hbound. lia.
      * simpl in Hbound.
        rewrite <- (cmc_pow_iter_comm p q x k') in Hbound.
        assert (Hexists' : (exists k0 : nat,
                            (k0 <= f)%nat /\
                            (cmc_pow_iter p q (cmc_iter p q x) k0 <= e)%nat)).
        { exists k'. split.
          - lia.
          - exact Hbound. }
        specialize (IH p q (cmc_iter p q x) e Hexists').
        simpl.
        rewrite <- (cmc_pow_iter_comm p q x (cmc_k_enum f p q (cmc_iter p q x) e)).
        exact IH.
Qed.

(* 精确面不变量：上取整值恒盖住精确几何值（x·p^k ≤ iter^k(x)·q^k） *)
Lemma cmc_pow_iter_exact_ge : forall p q x k, (0 < p)%nat -> (0 < q)%nat ->
  (x * p ^ k <= cmc_pow_iter p q x k * q ^ k)%nat.
Proof.
  intros p q x k Hp Hq. induction k as [| k IH].
  - simpl. lia.
  - simpl.
    pose proof (cmc_iter_step_bound p q (cmc_pow_iter p q x k) Hq) as Hstep.
    apply (Nat.le_trans _ (cmc_pow_iter p q x k * q ^ k * p)).
    + rewrite (Nat.mul_comm p (p ^ k)).
      rewrite (Nat.mul_assoc x (p ^ k) p).
      apply (Nat.mul_le_mono_r _ _ p). exact IH.
    + rewrite <- (Nat.mul_assoc (cmc_pow_iter p q x k) (q ^ k) p).
      rewrite (Nat.mul_comm (q ^ k) p).
      rewrite (Nat.mul_assoc (cmc_pow_iter p q x k) p (q ^ k)).
      apply (Nat.le_trans _ (cmc_iter p q (cmc_pow_iter p q x k) * q * q ^ k)).
      * apply (Nat.mul_le_mono_r _ _ (q ^ k)). exact Hstep.
      * rewrite (Nat.mul_assoc (cmc_iter p q (cmc_pow_iter p q x k)) q (q ^ k)).
        apply (Nat.le_refl _).
Qed.

(* log 模量方程的 nat 形：枚举终止，x·p^N ≤ e·q^N（log 单调下的等价面） *)
Theorem cmc_k_enum_logface : forall fuel p q x e,
  (0 < p)%nat -> (0 < q)%nat ->
  (exists k : nat, (k <= fuel)%nat /\ (cmc_pow_iter p q x k <= e)%nat) ->
  (x * p ^ cmc_k_enum fuel p q x e <= e * q ^ cmc_k_enum fuel p q x e)%nat.
Proof.
  intros fuel p q x e Hp Hq Hterm.
  pose proof (cmc_k_enum_correct fuel p q x e Hterm) as H1.
  pose proof (cmc_pow_iter_exact_ge p q x (cmc_k_enum fuel p q x e) Hp Hq) as H2.
  apply (Nat.le_trans _
           (cmc_pow_iter p q x (cmc_k_enum fuel p q x e)
              * q ^ cmc_k_enum fuel p q x e)).
  - exact H2.
  - apply (Nat.mul_le_mono_r _ _ (q ^ cmc_k_enum fuel p q x e)). exact H1.
Qed.

(* ---------- 本件新增：严格衰减与燃料充足性（BQ 诚实边界4 闭合） ---------- *)

(* 衰减核：x·p + q ≤ x·q 时上取整走步严格递降（floor 判据 d·q ≤ a < x·q） *)
Lemma cmc_iter_lt_decay : forall p q x,
  (0 < q)%nat -> (x * p + q <= x * q)%nat -> (cmc_iter p q x < x)%nat.
Proof.
  intros p q x Hq Hdecay. unfold cmc_iter, cmc_ceil_div.
  assert (Hcore : (Nat.div (x * p + q - 1) q < x)%nat).
  { destruct (Nat.lt_ge_cases (Nat.div (x * p + q - 1) q) x) as [Hlt | Hge].
    - exact Hlt.
    - exfalso.
      assert (Hmon : (x * q <= Nat.div (x * p + q - 1) q * q)%nat)
        by (apply Nat.mul_le_mono_r; exact Hge).
      pose proof (Nat.div_mod_eq (x * p + q - 1) q) as Hdm.
      pose proof (Nat.mod_upper_bound (x * p + q - 1) q
                    (proj2 (Nat.neq_0_lt_0 q) Hq)) as Hmb.
      lia. }
  exact Hcore.
Qed.

(* half 域衰减：2·p ≤ q 且 x ≥ 2 时走步严格递降（x·(q−p) ≥ 2(q−p) ≥ q） *)
Lemma cmc_iter_lt_half : forall p q x,
  (0 < p)%nat -> (2 * p <= q)%nat -> (2 <= x)%nat -> (cmc_iter p q x < x)%nat.
Proof.
  intros p q x Hp H2p Hx. apply (cmc_iter_lt_decay p q x).
  - lia.
  - assert (Hsplit : (x * q = x * p + x * (q - p))%nat).
    { rewrite <- (Nat.mul_add_distr_l x p (q - p)). f_equal. lia. }
    assert (H2le : (2 * (q - p) <= x * (q - p))%nat)
      by (apply Nat.mul_le_mono_r; exact Hx).
    rewrite Hsplit. lia.
Qed.

(* qbound 域衰减：p < q 且 x ≥ q 时走步严格递降（x·(q−p) ≥ q·1 ≥ q） *)
Lemma cmc_iter_lt_q : forall p q x,
  (0 < p)%nat -> (p < q)%nat -> (q <= x)%nat -> (cmc_iter p q x < x)%nat.
Proof.
  intros p q x Hp Hpq Hx. apply (cmc_iter_lt_decay p q x).
  - lia.
  - assert (Hsplit : (x * q = x * p + x * (q - p))%nat).
    { rewrite <- (Nat.mul_add_distr_l x p (q - p)). f_equal. lia. }
    assert (H1 : (1 <= q - p)%nat) by lia.
    assert (H2le : (q * 1 <= x * (q - p))%nat)
      by (apply Nat.mul_le_mono; lia).
    rewrite Nat.mul_1_r in H2le.
    rewrite Hsplit. lia.
Qed.

(* 燃料充足性（泛形）：凡预算以上走步严格递降，则 A 步燃料必达预算内。
   结构归纳（燃料单调），零 Prop 消入 Set（结论为 ex 存在形）。 *)
Lemma cmc_fuel_sufficient_gen : forall fuel p q x E,
  (0 < q)%nat -> (0 < E)%nat -> (x <= fuel)%nat ->
  (forall y : nat, (E < y)%nat -> (cmc_iter p q y < y)%nat) ->
  (exists k : nat, (k <= fuel)%nat /\ (cmc_pow_iter p q x k <= E)%nat).
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x E Hq HE Hx Hdecay.
  - assert (Hx0 : (x = 0)%nat) by lia. subst x.
    exists 0%nat. split.
    + lia.
    + simpl. lia.
  - destruct (Nat.leb x E) eqn:Hle.
    + exists 0%nat. split.
      * lia.
      * simpl. exact (proj1 (Nat.leb_le x E) Hle).
    + assert (HEx : (E < x)%nat) by (apply (proj1 (Nat.leb_gt x E)); exact Hle).
      assert (Hdec : (cmc_iter p q x < x)%nat) by (apply Hdecay; exact HEx).
      assert (Hiterf : (cmc_iter p q x <= f)%nat) by lia.
      destruct (IH p q (cmc_iter p q x) E Hq HE Hiterf Hdecay) as [k [Hk Hb]].
      exists (Datatypes.S k). split.
      * lia.
      * simpl. rewrite <- (cmc_pow_iter_comm p q x k). exact Hb.
Qed.

(* half 域燃料充足性：2·p ≤ q、预算 E ≥ 1，fuel := x 即足 *)
Theorem cmc_fuel_sufficient_half : forall fuel p q x E,
  (0 < p)%nat -> (2 * p <= q)%nat -> (0 < E)%nat -> (x <= fuel)%nat ->
  (exists k : nat, (k <= fuel)%nat /\ (cmc_pow_iter p q x k <= E)%nat).
Proof.
  intros fuel p q x E Hp H2p HE Hx.
  apply (cmc_fuel_sufficient_gen fuel p q x E).
  - lia.
  - exact HE.
  - exact Hx.
  - intros y Hy. apply (cmc_iter_lt_half p q y Hp H2p). lia.
Qed.

(* qbound 域燃料充足性：预算 E ≥ q−1、任意 p<q，fuel := x 即足 *)
Theorem cmc_fuel_sufficient_qbound : forall fuel p q x E,
  (0 < p)%nat -> (p < q)%nat -> (q <= E)%nat -> (x <= fuel)%nat ->
  (exists k : nat, (k <= fuel)%nat /\ (cmc_pow_iter p q x k <= E)%nat).
Proof.
  intros fuel p q x E Hp Hpq HqE Hx.
  apply (cmc_fuel_sufficient_gen fuel p q x E).
  - lia.
  - lia.
  - exact Hx.
  - intros y Hy. apply (cmc_iter_lt_q p q y Hp Hpq). lia.
Qed.

(* 调用侧自动燃料：half 域上枚举器读数即正确步数（Hterm 供给面闭合） *)
Theorem cmc_k_enum_auto_half : forall p q A E,
  (0 < p)%nat -> (2 * p <= q)%nat -> (0 < E)%nat -> (E < A)%nat ->
  (cmc_pow_iter p q A (cmc_k_enum A p q A E) <= E)%nat.
Proof.
  intros p q A E Hp H2p HE HAE.
  apply (cmc_k_enum_correct A p q A E).
  apply (cmc_fuel_sufficient_half A p q A E Hp H2p HE).
  lia.
Qed.

(* 定点档烟测一（BB 数值定装）：kappa=1/2、A=1000、E=5 的减半枚举 *)
Eval vm_compute in (cmc_k_enum 30 1 2 1000 5).

(* 定点档烟测二：kappa=3/4（qbound 域 E=4 ≥ q−1=3）、A=50、E=4 *)
Eval vm_compute in (cmc_k_enum 30 3 4 50 4).

(* ============================================================ *)
(* Part 3：实面桥——定点档计算器在具体有理数据上的实面正确性。          *)
(*   注: 本段置前于 Part 1（Import RealInterfaceEnhancedMod 之前），      *)
(*   俾 S01 RealInterfaceEnhanced 访问器名不被 Setoid 模组名遮蔽          *)
(*   （BQ 首件同环境解析实拍）。                                        *)
(* ============================================================ *)

Section CmcEnumReal.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let lt := @lt RI.
Let le := @le RI.

(* 左单位律补桥（Id 面一跳） *)
Lemma cmc_mult_one_l : forall t : R, Id (mult one t) t.
Proof.
  intros t. apply (id_trans (mult_comm one t)). apply (mult_one t).
Qed.

(* 逆元唯一性：y·z == 1 则 z == inv y *)
Lemma cmc_inv_unique : forall (y z : R) (Hy : lt zero y),
  Id (mult y z) one -> Id z (inv_pos y Hy).
Proof.
  intros y z Hy Hz.
  exact (id_trans (id_sym (mult_one z))
         (id_trans (id_cong (fun t => mult z t) (id_sym (inv_pos_correct y Hy)))
         (id_trans (mult_assoc z y (inv_pos y Hy))
         (id_trans (id_cong (fun t => mult t (inv_pos y Hy)) (mult_comm z y))
         (id_trans (id_cong (fun t => mult t (inv_pos y Hy)) Hz)
         (cmc_mult_one_l (inv_pos y Hy))))))).
Qed.

(* 幂对乘法的分裂：r_pow(a·b,n) == r_pow(a,n)·r_pow(b,n)（库缺，本件补；
   Id 面 rewrite 匹配不可靠（BQ 坑卡5），全链 term-mode） *)
Lemma cmc_rpow_mult : forall (a b : R) (n : nat),
  Id (r_pow (mult a b) n) (mult (r_pow a n) (r_pow b n)).
Proof.
  intros a b n. induction n as [| n IH].
  - simpl. exact (id_sym (mult_one one)).
  - simpl.
    exact (id_trans
             (id_cong (fun t => mult (mult a b) t) IH)
             (id_trans (id_sym (mult_assoc a b (mult (r_pow a n) (r_pow b n))))
             (id_trans (id_cong (fun t => mult a t) (mult_assoc b (r_pow a n) (r_pow b n)))
             (id_trans (id_cong (fun t => mult a t)
                                (id_cong (fun t => mult t (r_pow b n)) (mult_comm b (r_pow a n))))
             (id_trans (id_cong (fun t => mult a t) (id_sym (mult_assoc (r_pow a n) b (r_pow b n))))
                       (mult_assoc a (r_pow a n) (mult b (r_pow b n)))))))).
Qed.

(* nat_to_R 与幂交换：r_pow(nat_to_R k,n) == nat_to_R(k^n)（乘法同态归纳） *)
Lemma cmc_nat_r_pow : forall k n : nat,
  Id (r_pow (nat_to_R k) n) (nat_to_R (k ^ n)%nat).
Proof.
  intros k n. induction n as [| n IH].
  - exact (id_sym (plus_zero one)).
  - exact (id_trans
             (id_cong (fun t => mult (nat_to_R k) t) IH)
             (id_sym (nat_to_R_mult_hom k (k ^ n)%nat))).
Qed.

(* 幂对逆的分裂：r_pow(inv x,n) == inv(r_pow x,n)（逆唯一性归纳；
   逆的正性证书 Hp 作显式槽——防 Qed 不透明常数上的换形，BQ 坑卡7） *)
Lemma cmc_rpow_inv : forall (x : R) (Hx : lt zero x) (n : nat) (Hp : lt zero (r_pow x n)),
  Id (r_pow (inv_pos x Hx) n) (inv_pos (r_pow x n) Hp).
Proof.
  intros x Hx n. induction n as [| n IH]; intros Hp.
  - exact (id_sym (id_trans (id_sym (cmc_mult_one_l (inv_pos one Hp)))
                            (inv_pos_correct one Hp))).
  - specialize (IH (r_pow_pos x n Hx)).
    exact (id_trans
             (id_cong (fun t => mult (inv_pos x Hx) t) IH)
             (cmc_inv_unique (mult x (r_pow x n))
                             (mult (inv_pos x Hx)
                                   (inv_pos (r_pow x n) (r_pow_pos x n Hx)))
                             Hp
                             (id_trans
                                (id_sym (mult_assoc x (r_pow x n)
                                           (mult (inv_pos x Hx)
                                                 (inv_pos (r_pow x n) (r_pow_pos x n Hx)))))
                             (id_trans
                                (id_cong (fun t => mult x t)
                                         (mult_assoc (r_pow x n) (inv_pos x Hx)
                                                     (inv_pos (r_pow x n) (r_pow_pos x n Hx))))
                             (id_trans
                                (id_cong (fun t => mult x t)
                                         (id_cong (fun t => mult t (inv_pos (r_pow x n) (r_pow_pos x n Hx)))
                                                  (mult_comm (r_pow x n) (inv_pos x Hx))))
                             (id_trans
                                (id_cong (fun t => mult x t)
                                         (id_sym (mult_assoc (inv_pos x Hx) (r_pow x n)
                                                        (inv_pos (r_pow x n) (r_pow_pos x n Hx)))))
                             (id_trans
                                (id_cong (fun t => mult x t)
                                         (id_cong (fun t => mult (inv_pos x Hx) t)
                                                  (inv_pos_correct (r_pow x n) (r_pow_pos x n Hx))))
                             (id_trans
                                (id_cong (fun t => mult x t) (mult_one (inv_pos x Hx)))
                                (inv_pos_correct x Hx))))))))).
Qed.

(* nat ≤ 到实面 le 嵌入单调桥（库缺，BQ 补、本件滚转）。
   消除纪律：nat ≤ 是 Prop 归纳、不得消入 Set 目标——走 Set 层 nat 归纳
   （加法辅助件）＋Nat.leb 判定分支＋差值等式 replace，零 Prop 消除。 *)
Lemma cmc_nat_le_plus_aux : forall n m : nat, le (nat_to_R m) (nat_to_R (n + m)%nat).
Proof.
  intros n m. induction n as [| n IH].
  - simpl. apply le_refl.
  - simpl.
    apply (le_trans _ (nat_to_R (n + m)%nat)).
    + exact IH.
    + apply (le_id_l (nat_to_R (n + m)) (plus (nat_to_R (n + m)) zero)
              (plus one (nat_to_R (n + m)))
              (id_sym (plus_zero (nat_to_R (n + m))))).
      apply (le_id_r (plus (nat_to_R (n + m)) zero) (plus (nat_to_R (n + m)) one)
              (plus one (nat_to_R (n + m))) (plus_comm (nat_to_R (n + m)) one)).
      apply (le_plus_compat (nat_to_R (n + m)) (nat_to_R (n + m)) zero one
               (le_refl (nat_to_R (n + m)))).
      exact (lt_le_iff zero one (inl one_pos)).
Qed.

Lemma cmc_nat_le_embed : forall m n : nat, (m <= n)%nat -> le (nat_to_R m) (nat_to_R n).
Proof.
  intros m n Hmn. destruct (Nat.leb n m) eqn:E.
  - assert (Heq : n = m%nat).
    { apply (Nat.le_antisymm n m).
      - exact (proj1 (Nat.leb_le n m) E).
      - exact Hmn. }
    rewrite Heq. apply le_refl.
  - destruct n as [| n'].
    + assert (Hc : (m < 0)%nat) by (apply (proj1 (Nat.leb_gt 0 m)); exact E).
      destruct (Nat.nlt_0_r m Hc).
    + assert (Hlt : (m < Datatypes.S n')%nat)
        by (apply (proj1 (Nat.leb_gt (Datatypes.S n') m)); exact E).
      assert (Hmn' : (m <= n')%nat) by (apply (proj1 (Nat.lt_succ_r m n')); exact Hlt).
      replace (Datatypes.S n')%nat with ((Datatypes.S (n' - m)) + m)%nat by lia.
      apply (cmc_nat_le_plus_aux (Datatypes.S (n' - m)) m).
Qed.

(* 定点档主件：有理数据 kappa:=p/q、a:=A、eps:=E 上，枚举 N 的实面正确性
   （le 形，零 arch 依赖——全桥由本件幂分裂定律闭合） *)
Theorem cmc_enum_real_correct : forall (fuel p q A E : nat)
  (Hqr : lt zero (nat_to_R q)),
  (0 < p)%nat -> (0 < q)%nat -> (0 < A)%nat -> (0 < E)%nat ->
  (exists k : nat, (k <= fuel)%nat /\ (cmc_pow_iter p q A k <= E)%nat) ->
  le (mult (nat_to_R A)
            (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr))
                   (cmc_k_enum fuel p q A E)))
     (nat_to_R E).
Proof.
  intros fuel p q A E Hqr Hp Hq HA HE Hterm.
  set (N := cmc_k_enum fuel p q A E).
  set (w := inv_pos (r_pow (nat_to_R q) N) (r_pow_pos (nat_to_R q) N Hqr)).
  pose proof (cmc_k_enum_logface fuel p q A E Hp Hq Hterm) as Hlog.
  pose proof (cmc_nat_le_embed (A * p ^ N) (E * q ^ N) Hlog) as Hemb.
  assert (Hsplit : le (mult (nat_to_R A) (nat_to_R (p ^ N)))
                      (mult (nat_to_R E) (nat_to_R (q ^ N)))).
  { apply (le_id_l (mult (nat_to_R A) (nat_to_R (p ^ N)))
                   (nat_to_R (A * p ^ N))).
    - exact (id_sym (nat_to_R_mult_hom A (p ^ N))).
    - apply (le_id_r (nat_to_R (A * p ^ N))
                     (nat_to_R (E * q ^ N))
                     (mult (nat_to_R E) (nat_to_R (q ^ N)))
                     (nat_to_R_mult_hom E (q ^ N))).
      exact Hemb. }
  assert (H3 : le (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)
                  (mult (mult (nat_to_R E) (nat_to_R (q ^ N))) w))
    by exact (le_mult_compat (mult (nat_to_R A) (nat_to_R (p ^ N)))
                             (mult (nat_to_R E) (nat_to_R (q ^ N))) w
                             (inv_pos_pos (r_pow (nat_to_R q) N)
                                (r_pow_pos (nat_to_R q) N Hqr))
                             Hsplit).
  assert (HL : Id (mult (nat_to_R A)
                        (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr)) N))
                  (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)).
  { pose proof (cmc_rpow_mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr) N) as Hpm.
    pose proof (cmc_nat_r_pow p N) as Hpo.
    pose proof (cmc_rpow_inv (nat_to_R q) Hqr N (r_pow_pos (nat_to_R q) N Hqr)) as Hpi.
    assert (Hs2 : Id (mult (r_pow (nat_to_R p) N)
                           (r_pow (inv_pos (nat_to_R q) Hqr) N))
                     (mult (nat_to_R (p ^ N)) w)).
    { apply (id_trans
               (id_cong (fun u => mult u (r_pow (inv_pos (nat_to_R q) Hqr) N)) Hpo)).
      exact (id_cong (fun u => mult (nat_to_R (p ^ N)) u) Hpi). }
    apply (id_trans (id_cong (fun t => mult (nat_to_R A) t) Hpm)).
    apply (id_trans (id_cong (fun t => mult (nat_to_R A) t) Hs2)).
    exact (mult_assoc (nat_to_R A) (nat_to_R (p ^ N)) w). }
  assert (HR : Id (mult (mult (nat_to_R E) (nat_to_R (q ^ N))) w) (nat_to_R E)).
  { exact (id_trans
             (id_sym (mult_assoc (nat_to_R E) (nat_to_R (q ^ N)) w))
             (id_trans
                (id_cong (fun t => mult (nat_to_R E) t)
                         (id_trans
                            (id_cong (fun u => mult u w)
                                     (id_sym (cmc_nat_r_pow q N)))
                            (inv_pos_correct (r_pow (nat_to_R q) N)
                                             (r_pow_pos (nat_to_R q) N Hqr))))
                (mult_one (nat_to_R E)))). }
  apply (le_id_l (mult (nat_to_R A)
                         (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr)) N))
                 (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)
                 (nat_to_R E) HL).
  apply (le_id_r (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)
                 (mult (mult (nat_to_R E) (nat_to_R (q ^ N))) w)
                 (nat_to_R E) HR H3).
Qed.

End CmcEnumReal.

(* ============================================================ *)
(* Part 1：req 实面对应形（UpReqConcMixSel CmkMixTime 证书子集同形对应）——    *)
(*   mtg_k_calc 同构计算器＋率抽取件＋sigT 封装。Import 置本段前。        *)
(* ============================================================ *)

Import RealInterfaceEnhancedMod.

Section CmcMixStepCalc.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* 诚实接口（CmkMixTime 证书全集原样对应，实参序经 Check @ 检验确定） *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

Variable S0 : Set.
Variable sumf : (S0 -> R) -> R.

Hypothesis sum_ext :
  forall f g : S0 -> R, (forall s : S0, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_linear :
  forall (a : R) (f : S0 -> R),
    req (sumf (fun s : S0 => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_add :
  forall f g : S0 -> R,
    req (sumf (fun s : S0 => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_le :
  forall f g : S0 -> R, (forall s : S0, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis abs_sum_le_h :
  forall f : S0 -> R, le (abs (sumf f)) (sumf (fun s : S0 => abs (f s))).

Variable enum : list S0.
Variable enum_nonempty : Not (enum = nil).
Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable z : S0 -> S0 -> R.
Variable z_lb : forall s s' : S0, le (opp Delta) (z s s').
Variable z_ub : forall s s' : S0, le (z s s') Delta.
Variable bs_swap : forall f : S0 -> S0 -> R,
  req (sumf (fun s : S0 => sumf (fun s' : S0 => f s s')))
      (sumf (fun s' : S0 => sumf (fun s : S0 => f s s'))).
Variable bs_abs : forall a : R, le zero a -> req (abs a) a.
Variable bs_lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Variable sum_eq_list : forall g : S0 -> R, req (sumf g) (rsq_bs_list_sum S0 g enum).

(* TV 算子与迭代器（CmkMixTime 同位） *)
Let inv_two := inv_pos (plus one one) req_two_pos.
Let cmc_tv (mu nu : S0 -> R) : R :=
  mult inv_two (sumf (fun s : S0 => abs (req_minus (mu s) (nu s)))).
Let cmc_titer (n : nat) (mu : S0 -> R) : S0 -> R :=
  k_titer S0 sumf enum enum_nonempty temp temp_pos Delta z z_lb sum_eq_list n mu.

(* ===== 率抽取件（首件策略 A 支：率显式在案，直接使用宿主导出证书） ==== *)
(*   lo = rsq_exp_pos_fn(invT·opp Delta)（req 面 e^(−Δ/T) 形），          *)
(*   kappa := cmc_omd := one − lo·lo（CmkMixTime 证明体内第二行原样）。   *)

Let lo := rsq_exp_pos_fn (mult (inv_pos temp temp_pos) (opp Delta)).
Let cmc_omd := req_minus one (mult lo lo).

Lemma cmc_rate_pos : lt zero cmc_omd.
Proof.
  exact (cmk_omd_pos lt_plus_compat_lt_le temp temp_pos Delta Delta_pos).
Qed.

Lemma cmc_rate_lt_one : lt cmc_omd one.
Proof.
  exact (cmk_ds_omd_lt_one temp temp_pos Delta lt_plus_compat_lt_le).
Qed.

(* ===== 通用率面计算器（mtg_k_calc 同构：kappa/TV0/budget 走 cmk_k_select） *)
(*   Arch 证书槽 Harch 为宿主原样接口位（非公理，Assumptions 实证）——     *)
(*   实例化属下游供给（UpReqConcB1 的 RealEnhancedReal 闭合同款）。        *)

Definition cmc_rate_step_calc (kappa TV0 budget : R)
  (Hk1 : lt zero kappa) (Hk2 : lt kappa one)
  (Ha : le zero TV0) (Hbudget : lt zero budget)
  (Harch : forall x : R, le zero x ->
            sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))) : nat :=
  projT1 (@cmk_k_select R RIS lt_plus_compat_lt_le kappa TV0 budget
            Hk1 Hk2 Ha Hbudget Harch).

Theorem cmc_rate_step_calc_correct : forall (kappa TV0 budget : R)
  (Hk1 : lt zero kappa) (Hk2 : lt kappa one)
  (Ha : le zero TV0) (Hbudget : lt zero budget)
  (Harch : forall x : R, le zero x ->
            sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))),
  lt (mult (cmk_r_pow kappa (cmc_rate_step_calc kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch))
           TV0)
     budget.
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch.
  exact (projT2 (@cmk_k_select R RIS lt_plus_compat_lt_le kappa TV0 budget
                   Hk1 Hk2 Ha Hbudget Harch)).
Qed.

(* ===== 抽取率上的具体计算器：kappa := cmc_omd（率面读数） ========== *)

Definition cmc_omd_step_calc (TV0 : R) (Ha : le zero TV0)
  (budget : R) (Hbudget : lt zero budget)
  (Harch : forall x : R, le zero x ->
            sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))) : nat :=
  projT1 (@cmk_k_select R RIS lt_plus_compat_lt_le cmc_omd TV0 budget
            cmc_rate_pos cmc_rate_lt_one Ha Hbudget Harch).

Theorem cmc_omd_step_calc_correct : forall (TV0 : R) (Ha : le zero TV0)
  (budget : R) (Hbudget : lt zero budget)
  (Harch : forall x : R, le zero x ->
            sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))),
  lt (mult (cmk_r_pow cmc_omd (cmc_omd_step_calc TV0 Ha budget Hbudget Harch)) TV0)
     budget.
Proof.
  intros TV0 Ha budget Hbudget Harch.
  exact (projT2 (@cmk_k_select R RIS lt_plus_compat_lt_le cmc_omd TV0 budget
                   cmc_rate_pos cmc_rate_lt_one Ha Hbudget Harch)).
Qed.

(* sigT 封装（率面）：精度预算到步数的见证型 *)
Theorem cmc_omd_modulus_sigT : forall (TV0 : R) (Ha : le zero TV0)
  (budget : R) (Hbudget : lt zero budget)
  (Harch : forall x : R, le zero x ->
            sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))),
  sigT (fun k : nat => lt (mult (cmk_r_pow cmc_omd k) TV0) budget).
Proof.
  intros TV0 Ha budget Hbudget Harch.
  exists (cmc_omd_step_calc TV0 Ha budget Hbudget Harch).
  exact (cmc_omd_step_calc_correct TV0 Ha budget Hbudget Harch).
Defined.

(* ===== 宿主主件双投影：TV 收缩面计算器（cmk_attention_mixing_time 同构） *)

Definition cmc_mix_step_calc (mu nu : S0 -> R)
  (Hmu : req (sumf mu) one) (Hnu : req (sumf nu) one)
  (budget : R) (Hbudget : lt zero budget)
  (Harch : forall x : R, le zero x ->
            sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one)))
  (Htv0 : le zero (cmc_tv mu nu)) : nat :=
  projT1 (@cmk_attention_mixing_time R RIS lt_plus_compat_lt_le S0 sumf sum_ext
            sum_linear sum_add sum_le abs_sum_le_h enum enum_nonempty temp
            temp_pos Delta Delta_pos z z_lb z_ub bs_swap bs_abs bs_lpc
            sum_eq_list mu nu Hmu Hnu budget Hbudget Harch Htv0).

(* 正确性（TV 收缩面）：N := 读数处，TV(T^N mu, T^N nu) < budget *)
Theorem cmc_mix_step_tv_correct : forall (mu nu : S0 -> R)
  (Hmu : req (sumf mu) one) (Hnu : req (sumf nu) one)
  (budget : R) (Hbudget : lt zero budget)
  (Harch : forall x : R, le zero x ->
            sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one)))
  (Htv0 : le zero (cmc_tv mu nu)),
  lt (cmc_tv (cmc_titer (cmc_mix_step_calc mu nu Hmu Hnu budget Hbudget Harch Htv0) mu)
             (cmc_titer (cmc_mix_step_calc mu nu Hmu Hnu budget Hbudget Harch Htv0) nu))
     budget.
Proof.
  intros mu nu Hmu Hnu budget Hbudget Harch Htv0.
  exact (projT2 (@cmk_attention_mixing_time R RIS lt_plus_compat_lt_le S0 sumf
            sum_ext sum_linear sum_add sum_le abs_sum_le_h enum enum_nonempty
            temp temp_pos Delta Delta_pos z z_lb z_ub bs_swap bs_abs bs_lpc
            sum_eq_list mu nu Hmu Hnu budget Hbudget Harch Htv0)).
Qed.

(* sigT 封装（TV 面）：混合时间模量见证型 *)
Theorem cmc_mixing_modulus_sigT : forall (mu nu : S0 -> R)
  (Hmu : req (sumf mu) one) (Hnu : req (sumf nu) one)
  (budget : R) (Hbudget : lt zero budget)
  (Harch : forall x : R, le zero x ->
            sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one)))
  (Htv0 : le zero (cmc_tv mu nu)),
  sigT (fun k : nat => lt (cmc_tv (cmc_titer k mu) (cmc_titer k nu)) budget).
Proof.
  intros mu nu Hmu Hnu budget Hbudget Harch Htv0.
  exists (cmc_mix_step_calc mu nu Hmu Hnu budget Hbudget Harch Htv0).
  exact (cmc_mix_step_tv_correct mu nu Hmu Hnu budget Hbudget Harch Htv0).
Defined.

End CmcMixStepCalc.

(* ============================================================ *)
(* G4 审计口：公理面（全 Closed 预期）＋可提取强证（照 BF/BQ 模式）       *)
(* ============================================================ *)

Print Assumptions cmc_k_enum_correct.
Print Assumptions cmc_k_enum_logface.
Print Assumptions cmc_fuel_sufficient_half.
Print Assumptions cmc_fuel_sufficient_qbound.
Print Assumptions cmc_enum_real_correct.
Print Assumptions cmc_rate_step_calc_correct.
Print Assumptions cmc_omd_step_calc_correct.
Print Assumptions cmc_mix_step_tv_correct.
Print Assumptions cmc_mixing_modulus_sigT.
Print Assumptions cmc_omd_modulus_sigT.

(* 提取口：nat 面计算器四件（真 Fixpoint，无桩无截断） *)
Separate Extraction cmc_ceil_div cmc_iter cmc_pow_iter cmc_k_enum.
