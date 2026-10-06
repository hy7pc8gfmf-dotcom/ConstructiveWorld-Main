(* ============================================================ *)
(* abl_Pr_lcmdecomp_04.v —— 素数域成域件单第 4 件（域成件/收尾砖）     *)
(*   （plm_v p-adic 赋值面＋互素积整除核＋Hanson L(n) 分解衔接）      *)
(* 模块名：abl_Pr_lcmdecomp_04                                    *)
(* 数学使命：①互素积整除核（N 件单点名风险位，全强度闭合）——        *)
(*   plm_gauss（Bezout 核：gcd b a=1 ∧ b∏a·c ⟹ b∣c，Nat.gcd_bezout  *)
(*   双定向拆解）；plm_dvd_mul_coprime（a∣c ∧ b∣c ∧ gcd a b=1 ⟹     *)
(*   a·b∣c）；plm_coprime_mul（gcd x y=1 ∧ gcd x z=1 ⟹ gcd x y·z=1， *)
(*   gcd_greatest＋Gauss 两级闭合）；plm_gcd_prod_1（逐元素互素 ⟹    *)
(*   与列表积互素，fold_right 归纳）；主件 plm_coprime_prod_dvd：     *)
(*   逐元素整除 c ＋ 列表两两互素 ⟹ 列表积整除 c（构造性归纳）。      *)
(*   ②素数互素面：plm_prime_gcd_1（相异素数 gcd=1，pr_prime 试除形   *)
(*   谓词三分支闭合）；plm_gcd_pow（互素基底的幂提升：gcd p q=1 ⟹    *)
(*   gcd p^a q^b=1）。                                              *)
(*   ③p-adic 赋值面（N 件单 pr_v 全函数化，e-结构递归照 N 警示）：    *)
(*   plm_vmax p k e（0..e 上逐级登攀取最大赋值，Fixpoint 结构于 e）   *)
(*   ＋plm_v p k = plm_vmax p k k（界 k 保险：p^w∣k ⟹ p^w≤k ⟹        *)
(*   w≤k，pow_gt_lin_r 闭合）；plm_vmax_dvd／plm_vmax_ceil（登攀不    *)
(*   越顶二择一）⟹ plm_v_spec 双肢（p^{plm_v p k}∣k ∧ p^{S(...)}∤k   *)
(*   的 -> False 形）。                                             *)
(*   ④素因子工具：plm_prime_dvd_mul（素数整除积则整除一因子，        *)
(*   gcd 三分定向）；plm_lcm_split（素数整除 lcm 则整除其一，Nat.lcm  *)
(*   = a·(b/gcd a b) 展开面＋div_mod 桥）；plm_hit_find（燃料扫描    *)
(*   可计算见证机）＋spec（p∣L(n) ⟹ 1≤hit≤n ∧ p∣hit）。            *)
(*   ⑤Hanson 衔接三桥（hl_lcm_upto 使用位）：                        *)
(*   桥一 plm_lcm_dvd_pow：p^{plm_v p n}∣L(n)（plm_v_spec 肢一＋      *)
(*   divide_pos_le＋hl_lcm_divide_all）；                            *)
(*   桥二 plm_lcm_pow_prod_dvd：互异素数表的 n-赋值幂表之积整除 L(n)  *)
(*   （核件 plm_coprime_prod_dvd＋plm_gcd_pow＋桥一——N 件单 ⊇ 方向   *)
(*   的素幂积骨架）；                                                *)
(*   桥三 plm_fact_dvd_lcm／plm_fact_exists_dvd_lcm：件 1 素因子      *)
(*   分解存在形（pr_factor_exists sigT）之分解积整除 L(n)（件 1 ⟷    *)
(*   HansonLcm 直连）。                                              *)
(*   ⑥件 3 使用闭合 plm_peu_next_outside_lcm：peu_next n（n 之外的新   *)
(*   素数）整除 L(n) 则爆炸——新素数不在 lcm(1..n) 素基中（件 1＋     *)
(*   件 3＋HansonLcm＋本件见证机四链合拢）。                          *)
(* 设计依据：N 素数域设计 §②-件 4；链序      *)
(*   1→3→本件（件 2 枚举件 pen_ 属 prime_enum 池，不在本链——全等式   *)
(*   分解 L(n)=Π_{p≤n} p^{e_p} 需枚举表，留登记未竟，见头注边界）。   *)
(* 依赖清单：件 1 abl_Pr_core_01（pr_prime／pr_mod0_dvd／pr_dvd_mod0／*)
(*   pr_factor_exists）＋件 3 abl_Pr_euclid_03（peu_next／           *)
(*   peu_next_prime／peu_next_gt）＋HansonLcm（hl_lcm_upto／          *)
(*   hl_lcm_divide_all，缓存根 -Q 只读引用）＋纯 Stdlib（Arith.Arith／*)
(*   List／Bool／Lia）。stdlib 9.1 核验（zz_plm_probe 快扫）：       *)
(*   Nat.gcd_1_l／gcd_1_r／gcd_mul_l／gcd_divide_iff 均缺位——自建     *)
(*   plm_gcd_1_r／plm_gcd_1_l（Nat.gcd_unique_alt' 闭合），Gauss 核走 *)
(*   Nat.gcd_bezout（disjunctive Bezout，无前提定向拆解）；在册直引：  *)
(*   Nat.gcd_greatest／gcd_bezout／gcd_unique_alt'／divide_pos_le／   *)
(*   divide_mul_r／pow_le_mono_r／pow_gt_lin_r／Nat.Div0.mod_divides。 *)
(* 构造性注记：Set 面承载——计算件 plm_vmax／plm_v／plm_hit_find 皆   *)
(*   一阶 nat Fixpoint 可提取（G3 提取检验 Obj.magic 计 0）；Prop 面  *)
(*   谓词（pr_prime／plm_pairwise_coprime）仅作推理脚手架（件 1/件 3  *)
(*   同款）；否定面全走 -> False 形（本安装无否定记号，照 AQ 坑卡，   *)
(*   全件零否定记号书写，含证明内部）；零公理零承认零经典逻辑；数值   *)
(*   定装走小实例 vm_compute（≤12，plm_v 实例底数≤2 上限 2^13，      *)
(*   照 CZR14 大数值 Qed 打点墙纪律）。                              *)
(* 红线四条自审：                                                   *)
(*   - 红线一（零公理声明词）：全件 Qed/Defined，PA 取证块收尾；      *)
(*   - Set 层：主承载 plm_v／plm_hit_find 为 Set 值可计算函数，        *)
(*     plm_v_spec／plm_hit_find_spec 为其 Prop 面 spec（Ln2Escape／   *)
(*     HansonLcm 先例同构）；                                        *)
(*   - 非平凡：互素积整除核（N 件单登记最大工程风险位）全强度闭合，   *)
(*     赋值面 spec 双肢全给，三桥真使用 HansonLcm；未达面（全等式     *)
(*     分解）显式登记，非默默降档；                                  *)
(*   - 可提取：plm_vmax／plm_v／plm_hit_find Fixpoint 直提，提取实体   *)
(*     即逐级试登赋值算法与整除扫描见证机（无桩无截断）。             *)
(* 编译配方（链序 1→3→本件，逐件编译——BJ 教训）：                  *)
(*   source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/    *)
(*   env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 && cd <池> &&   *)
(*   nice -19 rocq c -native-compiler no -Q /Users/apple/Desktop/      *)
(*   ConstructiveWorld/vo_local_world_unified_0930 "" abl_Pr_core_01.v *)
(*   && nice -19 rocq c -native-compiler no -Q <缓存根> "" -Q . ""     *)
(*   abl_Pr_euclid_03.v && nice -19 rocq c -native-compiler no \       *)
(*   -Q <缓存根> "" -Q . "" abl_Pr_lcmdecomp_04.v                     *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import HansonLcm.
Require Import abl_Pr_core_01.
Require Import abl_Pr_euclid_03.

(* ---- §0 gcd 单位元件（stdlib 9.1 缺位自建：gcd_unique_alt' 闭合） ---- *)

Lemma plm_gcd_1_r : forall n : nat, Nat.gcd n 1 = 1.
Proof.
  intros n. apply Nat.gcd_unique_alt.
  intros q. split.
  - intros Hq. apply Nat.divide_1_r in Hq. subst q. split.
    + apply Nat.divide_1_l.
    + apply Nat.divide_refl.
  - intros [H1 H2]. exact H2.
Qed.

Lemma plm_gcd_1_l : forall n : nat, Nat.gcd 1 n = 1.
Proof.
  intros n. rewrite Nat.gcd_comm. apply plm_gcd_1_r.
Qed.

(* ---- §1 互素积整除核（N 件单点名风险位） ---- *)

(* 核 1（Bezout/Gauss）：gcd b a = 1 ∧ b∏a·c ⟹ b∣c。
   Nat.gcd_bezout 给 disjunctive Bezout，两定向各出见证。 *)
Lemma plm_gauss : forall b a c : nat,
  Nat.gcd b a = 1 -> Nat.divide b (a * c) -> Nat.divide b c.
Proof.
  intros b a c Hg Hd.
  destruct (Nat.gcd_bezout b a) as [Hbez | Hbez].
  - (* Bezout b a：u·b = gcd b a + v·a *)
    destruct Hbez as [u [v Hu]]. rewrite Hg in Hu.
    destruct Hd as [q Hq].
    assert (H3 : u * c * b = c + v * q * b).
    { replace (u * c * b) with (u * b * c) by ring.
      rewrite Hu, Nat.mul_add_distr_r, Nat.mul_1_l.
      rewrite <- Nat.mul_assoc, Hq, Nat.mul_assoc. reflexivity. }
    exists (u * c - v * q).
    rewrite Nat.mul_sub_distr_r.
    assert (H4 : u * c * b - v * q * b = c) by lia.
    lia.
  - (* Bezout a b：u·a = gcd b a + v·b *)
    destruct Hbez as [u [v Hu]]. rewrite Hg in Hu.
    destruct Hd as [q Hq].
    assert (H3 : u * q * b = c + v * c * b).
    { rewrite <- Nat.mul_assoc, <- Hq, Nat.mul_assoc, Hu.
      rewrite Nat.mul_add_distr_r, Nat.mul_1_l. ring. }
    exists (u * q - v * c).
    rewrite Nat.mul_sub_distr_r.
    assert (H4 : u * q * b - v * c * b = c) by lia.
    lia.
Qed.

(* 核 2：a∣c ∧ b∣c ∧ gcd a b=1 ⟹ a·b∣c *)
Lemma plm_dvd_mul_coprime : forall a b c : nat,
  Nat.divide a c -> Nat.divide b c -> Nat.gcd a b = 1 ->
  Nat.divide (a * b) c.
Proof.
  intros a b c Hac Hbc Hg.
  destruct Hac as [c1 Hc1].
  assert (Hba : Nat.gcd b a = 1) by (rewrite Nat.gcd_comm; exact Hg).
  assert (Hb : Nat.divide b (a * c1)).
  { rewrite Nat.mul_comm, <- Hc1. exact Hbc. }
  destruct Hbc as [c2 Hc2].
  destruct (plm_gauss b a c1 Hba Hb) as [c3 Hc3].
  exists c3. rewrite Hc1, Hc3. ring.
Qed.

(* 核 3：gcd x y=1 ∧ gcd x z=1 ⟹ gcd x y·z=1 *)
Lemma plm_coprime_mul : forall x y z : nat,
  Nat.gcd x y = 1 -> Nat.gcd x z = 1 -> Nat.gcd x (y * z) = 1.
Proof.
  intros x y z Hxy Hxz.
  apply Nat.divide_1_r.
  apply (Nat.divide_trans (Nat.gcd x (y * z)) (Nat.gcd x z) 1).
  - apply (Nat.gcd_greatest x z (Nat.gcd x (y * z))).
    + apply Nat.gcd_divide_l.
    + apply (plm_gauss (Nat.gcd x (y * z)) y z).
      * apply Nat.divide_1_r.
        apply (Nat.divide_trans
          (Nat.gcd (Nat.gcd x (y * z)) y) (Nat.gcd x y) 1).
        -- apply (Nat.gcd_greatest x y (Nat.gcd (Nat.gcd x (y * z)) y)).
           ++ apply (Nat.divide_trans
                (Nat.gcd (Nat.gcd x (y * z)) y) (Nat.gcd x (y * z)) x).
              ** apply Nat.gcd_divide_l.
              ** apply Nat.gcd_divide_l.
           ++ apply Nat.gcd_divide_r.
        -- rewrite Hxy. apply Nat.divide_1_l.
      * apply Nat.gcd_divide_r.
  - rewrite Hxz. apply Nat.divide_1_l.
Qed.

(* 核 4：逐元素与 x 互素 ⟹ x 与列表积互素 *)
Lemma plm_gcd_prod_1 : forall (t : list nat) (x : nat),
  (forall y : nat, In y t -> Nat.gcd x y = 1) ->
  Nat.gcd x (fold_right Nat.mul 1 t) = 1.
Proof.
  induction t as [| y t' IH]; intros x Hall.
  - exact (plm_gcd_1_r x).
  - change (fold_right Nat.mul 1 (y :: t'))
      with (Nat.mul y (fold_right Nat.mul 1 t')).
    apply plm_coprime_mul.
    + apply Hall. apply in_eq.
    + apply IH. intros y' Hy'. apply Hall. apply in_cons. exact Hy'.
Qed.

(* 两两互素（列表全对无前提 gcd=1——重复元自被排除：gcd x x = x） *)
Definition plm_pairwise_coprime (l : list nat) : Prop :=
  forall x y : nat, In x l -> In y l -> Nat.gcd x y = 1.

(* 主件（N 件单 plm_coprime_prod_dvd 型）：逐元素整除＋两两互素
   ⟹ 列表积整除（构造性归纳：头元与尾积互素＝核 3 级联） *)
Theorem plm_coprime_prod_dvd : forall (l : list nat) (c : nat),
  (forall x : nat, In x l -> Nat.divide x c) ->
  plm_pairwise_coprime l ->
  Nat.divide (fold_right Nat.mul 1 l) c.
Proof.
  induction l as [| x t IH]; intros c Hdiv Hpw.
  - apply Nat.divide_1_l.
  - apply plm_dvd_mul_coprime.
    + apply Hdiv. apply in_eq.
    + apply IH.
      * intros y Hy. apply Hdiv. apply in_cons. exact Hy.
      * intros x' y' Hx' Hy'. apply Hpw.
        -- apply in_cons. exact Hx'.
        -- apply in_cons. exact Hy'.
    + apply plm_gcd_prod_1. intros y Hy.
      apply Hpw; [apply in_eq | apply in_cons; exact Hy].
Qed.

(* ---- §2 素数互素面 ---- *)

(* 相异素数互素（pr_prime 试除形谓词三分支闭合） *)
Lemma plm_prime_gcd_1 : forall p q : nat,
  pr_prime p -> pr_prime q -> (p = q -> False) -> Nat.gcd p q = 1.
Proof.
  intros p q [Hp2 Hpd] [Hq2 Hqd] Hne.
  assert (Hgp : Nat.divide (Nat.gcd p q) p) by apply Nat.gcd_divide_l.
  assert (Hgq : Nat.divide (Nat.gcd p q) q) by apply Nat.gcd_divide_r.
  assert (Hlep : Nat.gcd p q <= p) by (apply Nat.divide_pos_le; [lia | exact Hgp]).
  assert (Hleq : Nat.gcd p q <= q) by (apply Nat.divide_pos_le; [lia | exact Hgq]).
  remember (Nat.gcd p q) as g eqn:Eg.
  destruct g as [| [| g'']].
  - exfalso. apply Nat.divide_0_l in Hgp. lia.
  - reflexivity.
  - exfalso.
    destruct (Nat.eq_dec p q) as [Epq|Npq].
    + apply Hne. exact Epq.
    + destruct (Nat.eq_dec (S (S g'')) p) as [Egp|Ngp].
      * rewrite Egp in Hgq.
        assert (Hpq_lt : p < q).
        { destruct (le_lt_dec q p) as [Hqle|Hlt2].
          - exfalso. apply Npq. lia.
          - exact Hlt2. }
        apply (Hqd p Hp2 Hpq_lt Hgq).
      * apply (Hpd (S (S g''))); [lia | lia | exact Hgp].
Qed.

(* 幕提升单基：gcd x y=1 ⟹ gcd x y^b=1（b 归纳） *)
Lemma plm_coprime_pow1 : forall x y b : nat,
  Nat.gcd x y = 1 -> Nat.gcd x (y ^ b) = 1.
Proof.
  intros x y b Hxy. induction b as [| b' IH].
  - rewrite Nat.pow_0_r. apply plm_gcd_1_r.
  - rewrite Nat.pow_succ_r'. apply plm_coprime_mul; [exact Hxy | exact IH].
Qed.

(* 互素基底的幂提升：gcd p q=1 ⟹ gcd p^a q^b=1 *)
Lemma plm_gcd_pow : forall p q a b : nat,
  Nat.gcd p q = 1 -> Nat.gcd (p ^ a) (q ^ b) = 1.
Proof.
  intros p q a b Hpq. induction a as [| a' IH].
  - rewrite Nat.pow_0_r. apply plm_gcd_1_l.
  - rewrite Nat.pow_succ_r'.
    rewrite (Nat.gcd_comm (p * p ^ a') (q ^ b)).
    apply plm_coprime_mul.
    + rewrite (Nat.gcd_comm (q ^ b) p).
      exact (plm_coprime_pow1 p q b Hpq).
    + rewrite (Nat.gcd_comm (q ^ b) (p ^ a')). exact IH.
Qed.

(* ---- §3 p-adic 赋值面（N 件单 pr_v 全函数化：e-结构递归） ---- *)

(* 0..e 逐级登攀：v₀=0；v_{e+1} = p^{v_e+1}∣k 则 v_e+1 否则 v_e。
   N 件单警示照办：递降形 plm_v p (k/p) 的 k/p 非结构子项，弃；
   界 e 上取最大，e-结构递归合法。 *)
Fixpoint plm_vmax (p k e : nat) : nat :=
  match e with
  | 0 => 0
  | S e' =>
      if Nat.eqb (k mod p ^ S (plm_vmax p k e')) 0
      then S (plm_vmax p k e')
      else plm_vmax p k e'
  end.

Definition plm_v (p k : nat) : nat := plm_vmax p k k.

(* 肢一：登攀值永远整除（p=0 底形 mod 0 = k 路径显式分支） *)
Lemma plm_vmax_dvd : forall p k e : nat, Nat.divide (p ^ plm_vmax p k e) k.
Proof.
  intros p k e. induction e as [| e' IH].
  - rewrite Nat.pow_0_r. apply Nat.divide_1_l.
  - change (plm_vmax p k (S e'))
      with (if Nat.eqb (k mod p ^ S (plm_vmax p k e')) 0
            then S (plm_vmax p k e')
            else plm_vmax p k e').
    destruct (Nat.eqb (k mod p ^ S (plm_vmax p k e')) 0) eqn:Em.
    + apply Nat.eqb_eq in Em.
      destruct (Nat.eq_dec p 0) as [Ep0|Ep0].
      * rewrite Ep0 in Em |- *.
        change (0 ^ S (plm_vmax 0 k e')) with 0 in Em.
        rewrite Nat.mod_0_r in Em.
        rewrite Em. apply Nat.divide_0_r.
      * assert (Hpos : 1 <= p ^ S (plm_vmax p k e')).
        { pose proof (Nat.pow_nonzero p (S (plm_vmax p k e')) Ep0). lia. }
        exact (pr_mod0_dvd (p ^ S (plm_vmax p k e')) k Hpos Em).
    + exact IH.
Qed.

(* 肢二：登攀值=界 e，或下一幂整除爆炸（-> False 形） *)
Lemma plm_vmax_ceil : forall p k e : nat,
  plm_vmax p k e = e \/ (Nat.divide (p ^ S (plm_vmax p k e)) k -> False).
Proof.
  intros p k e. induction e as [| e' IH].
  - left. reflexivity.
  - change (plm_vmax p k (S e'))
      with (if Nat.eqb (k mod p ^ S (plm_vmax p k e')) 0
            then S (plm_vmax p k e')
            else plm_vmax p k e').
    destruct (Nat.eqb (k mod p ^ S (plm_vmax p k e')) 0) eqn:Em.
    + (* 已登攀：p^{S v'}∣k，与肢二型假说相斥，故 v'=e' ⟹ 值=S e'=e *)
      assert (Hclimb : Nat.divide (p ^ S (plm_vmax p k e')) k).
      { apply Nat.eqb_eq in Em.
        destruct (Nat.eq_dec p 0) as [Ep0|Ep0].
        - rewrite Ep0 in Em |- *.
          change (0 ^ S (plm_vmax 0 k e')) with 0 in Em.
          rewrite Nat.mod_0_r in Em.
          rewrite Em. apply Nat.divide_0_r.
        - assert (Hpos : 1 <= p ^ S (plm_vmax p k e')).
          { pose proof (Nat.pow_nonzero p (S (plm_vmax p k e')) Ep0). lia. }
          exact (pr_mod0_dvd (p ^ S (plm_vmax p k e')) k Hpos Em). }
      destruct IH as [Heq | Hfail].
      * left. rewrite Heq. reflexivity.
      * exfalso. apply Hfail. exact Hclimb.
    + right. intros Hd.
      apply Nat.eqb_neq in Em.
      destruct (Nat.eq_dec p 0) as [Ep0|Ep0].
      * rewrite Ep0 in Hd, Em.
        change (0 ^ S (plm_vmax 0 k e')) with 0 in Hd, Em.
        rewrite Nat.mod_0_r in Em.
        apply Nat.divide_0_l in Hd. lia.
      * assert (Hpos : 1 <= p ^ S (plm_vmax p k e')).
        { pose proof (Nat.pow_nonzero p (S (plm_vmax p k e')) Ep0). lia. }
        apply Em. exact (pr_dvd_mod0 (p ^ S (plm_vmax p k e')) k Hpos Hd).
Qed.

(* 赋值面 spec 双肢（全函数化交付；界 k 保险性：p^w∣k ⟹ p^w≤k，
   而 1<p ⟹ S k < p^{S k}（pow_gt_lin_r），故 w≤k 界不截真值） *)
Theorem plm_v_dvd : forall p k : nat, Nat.divide (p ^ plm_v p k) k.
Proof. intros p k. apply plm_vmax_dvd. Qed.

Theorem plm_v_max : forall p k : nat,
  1 < p -> 1 <= k -> Nat.divide (p ^ S (plm_v p k)) k -> False.
Proof.
  intros p k Hp Hk Hd.
  destruct (plm_vmax_ceil p k k) as [Heq | Hfail].
  - exfalso. unfold plm_v in Hd. rewrite Heq in Hd.
    assert (Hdle : p ^ S k <= k)
      by (apply Nat.divide_pos_le; [exact Hk | exact Hd]).
    pose proof (Nat.pow_gt_lin_r p (S k) Hp). lia.
  - exact (Hfail Hd).
Qed.

Theorem plm_v_spec : forall p k : nat, 1 < p -> 1 <= k ->
  Nat.divide (p ^ plm_v p k) k /\
  (Nat.divide (p ^ S (plm_v p k)) k -> False).
Proof.
  intros p k Hp Hk. split.
  - apply plm_v_dvd.
  - intros Hd. apply (plm_v_max p k Hp Hk Hd).
Qed.

(* ---- §4 素因子工具 ---- *)

(* 素数整除积则整除一因子（gcd 三分定向） *)
Lemma plm_prime_dvd_mul : forall p x y : nat,
  pr_prime p -> Nat.divide p (x * y) -> Nat.divide p x \/ Nat.divide p y.
Proof.
  intros p x y [Hp2 Hpd] Hdvd.
  destruct (Nat.eq_dec (Nat.gcd p x) 1) as [E1|N1].
  - right. apply (plm_gauss p x y E1 Hdvd).
  - destruct (Nat.eq_dec (Nat.gcd p x) p) as [Ep|Np].
    + left. rewrite <- Ep. apply Nat.gcd_divide_r.
    + exfalso.
      assert (Hgp : Nat.divide (Nat.gcd p x) p) by apply Nat.gcd_divide_l.
      assert (Hle : Nat.gcd p x <= p)
        by (apply Nat.divide_pos_le; [lia | exact Hgp]).
      remember (Nat.gcd p x) as g eqn:Eg.
      destruct g as [| [| g']].
      * exfalso. apply Nat.divide_0_l in Hgp. lia.
      * apply N1. reflexivity.
      * apply (Hpd (S (S g'))); [lia | lia | exact Hgp].
Qed.

(* 素数整除 lcm 则整除其一（Nat.lcm a b = a·(b/gcd a b) 展开面） *)
Lemma plm_lcm_split : forall p a b : nat,
  pr_prime p -> Nat.divide p (Nat.lcm a b) ->
  Nat.divide p a \/ Nat.divide p b.
Proof.
  intros p a b Hpp Hd. unfold Nat.lcm in Hd.
  destruct (plm_prime_dvd_mul p a (b / Nat.gcd a b) Hpp Hd) as [H1|H2].
  - left. exact H1.
  - right.
    destruct (Nat.eq_dec (Nat.gcd a b) 0) as [E0|N0].
    + assert (Hgb : Nat.divide (Nat.gcd a b) b) by apply Nat.gcd_divide_r.
      rewrite E0 in Hgb. apply Nat.divide_0_l in Hgb.
      rewrite Hgb. apply Nat.divide_0_r.
    + assert (Hgb : Nat.divide (Nat.gcd a b) b) by apply Nat.gcd_divide_r.
      assert (Hg1 : 1 <= Nat.gcd a b) by lia.
      assert (Hb : b = Nat.gcd a b * (b / Nat.gcd a b)).
      { pose proof (Nat.div_mod b (Nat.gcd a b) N0) as Hdm.
        assert (Hm0 : b mod Nat.gcd a b = 0)
          by (apply (pr_dvd_mod0 _ b Hg1 Hgb)).
        rewrite Hm0 in Hdm. rewrite Nat.add_0_r in Hdm. exact Hdm. }
      rewrite Hb. apply Nat.divide_mul_r. exact H2.
Qed.

(* 整除见证扫描机（燃料递降：p∣S f 则取 S f，否则降燃料） *)
Fixpoint plm_hit_find (p fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f => if Nat.eqb (S f mod p) 0 then S f else plm_hit_find p f
  end.

(* 见证机 spec：p∣L(fuel) ⟹ 1≤hit≤fuel ∧ p∣hit（Set 面可计算见证） *)
Lemma plm_hit_find_spec : forall p fuel : nat, pr_prime p ->
  Nat.divide p (hl_lcm_upto fuel) ->
  1 <= plm_hit_find p fuel /\ plm_hit_find p fuel <= fuel /\
  Nat.divide p (plm_hit_find p fuel).
Proof.
  intros p fuel [Hp2 Hpd]. induction fuel as [| f IH]; intros HL.
  - exfalso. simpl in HL.
    apply Nat.divide_1_r in HL. lia.
  - change (plm_hit_find p (S f))
      with (if Nat.eqb (S f mod p) 0 then S f else plm_hit_find p f).
    destruct (Nat.eqb (S f mod p) 0) eqn:Em.
      * apply Nat.eqb_eq in Em.
        assert (HpS : Nat.divide p (S f))
          by (apply (pr_mod0_dvd p (S f)); [lia | exact Em]).
        repeat split; [lia | lia | exact HpS].
      * apply Nat.eqb_neq in Em.
        change (hl_lcm_upto (S f)) with (Nat.lcm (hl_lcm_upto f) (S f)).
        destruct (plm_lcm_split p (hl_lcm_upto f) (S f) (conj Hp2 Hpd) HL)
          as [HLf | HLf].
        -- destruct (IH HLf) as [H1 [H2 H3]].
           repeat split; [exact H1 | lia | exact H3].
        -- exfalso. apply Em.
           apply (pr_dvd_mod0 p (S f)); [lia | exact HLf].
Qed.

(* ---- §5 Hanson 衔接三桥＋件 3 使用闭合 ---- *)

(* 桥一：素幂入 lcm 列——p^{plm_v p n}∣L(n) *)
Theorem plm_lcm_dvd_pow : forall p n : nat,
  1 < p -> 1 <= n -> Nat.divide (p ^ plm_v p n) (hl_lcm_upto n).
Proof.
  intros p n Hp Hn.
  assert (Hdvd : Nat.divide (p ^ plm_v p n) n) by apply plm_v_dvd.
  assert (Hpos : 1 <= p ^ plm_v p n).
  { destruct (p ^ plm_v p n) as [| q'] eqn:Ep.
    - exfalso. apply Nat.divide_0_l in Hdvd. lia.
    - lia. }
  assert (Hle : p ^ plm_v p n <= n)
    by (apply Nat.divide_pos_le; [exact Hn | exact Hdvd]).
  apply (hl_lcm_divide_all n (p ^ plm_v p n)); [exact Hpos | exact Hle].
Qed.

(* 桥二（核件主使用）：互异素数表的 n-赋值幂表之积整除 L(n)
   ——N 件单 ⊇ 方向素幂积骨架（全等式分解需枚举表，留登记） *)
Theorem plm_lcm_pow_prod_dvd : forall (l : list nat) (n : nat),
  1 <= n ->
  (forall p : nat, In p l -> pr_prime p) ->
  plm_pairwise_coprime l ->
  Nat.divide
    (fold_right Nat.mul 1 (map (fun p => p ^ plm_v p n) l))
    (hl_lcm_upto n).
Proof.
  intros l n Hn Hall Hpw.
  apply plm_coprime_prod_dvd.
  - intros q Hq. apply in_map_iff in Hq. destruct Hq as [p [Hp Hin]].
    rewrite <- Hp.
    apply (plm_lcm_dvd_pow p n); [destruct (Hall p Hin) as [Hp2 _]; lia | exact Hn].
  - intros x y Hx Hy.
    apply in_map_iff in Hx. destruct Hx as [p [Hpx Hinp]].
    apply in_map_iff in Hy. destruct Hy as [q [Hqy Hinq]].
    rewrite <- Hpx, <- Hqy. apply plm_gcd_pow.
    apply Hpw; [exact Hinp | exact Hinq].
Qed.

(* 桥三：件 1 素因子分解积 ∣ L(n)（件 1 ⟷ HansonLcm 直连） *)
Theorem plm_fact_dvd_lcm : forall (l : list nat) (m n : nat),
  fold_right Nat.mul 1 l = m -> 1 <= m -> m <= n ->
  Nat.divide (fold_right Nat.mul 1 l) (hl_lcm_upto n).
Proof.
  intros l m n Hfold Hm Hn. rewrite Hfold.
  apply hl_lcm_divide_all; assumption.
Qed.

Theorem plm_fact_exists_dvd_lcm : forall (m n : nat) (Hm : 2 <= m),
  m <= n ->
  Nat.divide
    (fold_right Nat.mul 1 (proj1_sig (pr_factor_exists m Hm)))
    (hl_lcm_upto n).
Proof.
  intros m n Hm Hn.
  destruct (proj2_sig (pr_factor_exists m Hm)) as [_ Hfold].
  apply (plm_fact_dvd_lcm _ m n); [exact Hfold | lia | exact Hn].
Qed.

(* 件 3 使用闭合：新素数 peu_next n 不整除 L(n)——
   「Euclid 新素数不在 lcm(1..n) 素基中」（四链合拢：件 1 见证投影＋
   件 3 主定理＋本件扫描机 spec＋HansonLcm） *)
Theorem plm_peu_next_outside_lcm : forall n : nat,
  Nat.divide (peu_next n) (hl_lcm_upto n) -> False.
Proof.
  intros n Hd.
  destruct (plm_hit_find_spec (peu_next n) n (peu_next_prime n) Hd)
    as [H1 [H2 H3]].
  assert (Hle : peu_next n <= plm_hit_find (peu_next n) n)
    by (apply Nat.divide_pos_le; [lia | exact H3]).
  pose proof (peu_next_gt n). lia.
Qed.

(* ---- §6 数值定装烟测（小实例 vm_compute 直算零公设） ---- *)

Lemma plm_v_smoke_2_12 : plm_v 2 12 = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma plm_v_smoke_3_12 : plm_v 3 12 = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma plm_v_smoke_5_12 : plm_v 5 12 = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma plm_v_smoke_2_8 : plm_v 2 8 = 3.
Proof. vm_compute. reflexivity. Qed.

Lemma plm_v_smoke_3_6 : plm_v 3 6 = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma plm_hit_smoke_5_6 : plm_hit_find 5 6 = 5.
Proof. vm_compute. reflexivity. Qed.

Lemma plm_hit_smoke_7_6 : plm_hit_find 7 6 = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma plm_lcm_smoke_6 : hl_lcm_upto 6 = 60.
Proof. vm_compute. reflexivity. Qed.

(* 幂像实例：plm_v 2 6=1→2；plm_v 3 6=1→3；plm_v 5 6=0→1；积=6 *)
Lemma plm_powprod_smoke_6 :
  fold_right Nat.mul 1 (map (fun p => p ^ plm_v p 6) (2 :: 3 :: 5 :: nil))
  = 6.
Proof. vm_compute. reflexivity. Qed.

Lemma plm_bridge_smoke_6 :
  Nat.eqb (hl_lcm_upto 6 mod 30) 0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma plm_gcd_pow_smoke : Nat.gcd 4 9 = 1.
Proof. vm_compute. reflexivity. Qed.

(* ---- §7 公理审计（Print Assumptions 取证面） ---- *)

Print Assumptions plm_gauss.
Print Assumptions plm_dvd_mul_coprime.
Print Assumptions plm_coprime_mul.
Print Assumptions plm_gcd_prod_1.
Print Assumptions plm_coprime_prod_dvd.
Print Assumptions plm_prime_gcd_1.
Print Assumptions plm_gcd_pow.
Print Assumptions plm_vmax_dvd.
Print Assumptions plm_vmax_ceil.
Print Assumptions plm_v_spec.
Print Assumptions plm_lcm_dvd_pow.
Print Assumptions plm_lcm_pow_prod_dvd.
Print Assumptions plm_fact_exists_dvd_lcm.
Print Assumptions plm_peu_next_outside_lcm.
