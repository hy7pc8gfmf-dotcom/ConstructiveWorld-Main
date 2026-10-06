(* ============================================================ *)
(* abl_Pr_lcm_eq.v —— 素数域成域终件：L(n)=Π_{p≤n} p^{e_p} 全等式     *)
(*   （BL 登记未竟 pr_lcm_eq_decomp 的闭合件；素数域第五砖）          *)
(* 模块名：abl_Pr_lcm_eq                                          *)
(* 数学使命：闭合 N 件单草案 pr_lcm_eq_decomp——hl_lcm_upto n（lcm    *)
(*   (1..n)，HansonLcm 折叠承载）与素幂分解积的全等式，等式承载走     *)
(*   hl_id（Set 面，宿主口径照 N 件单原形）：                       *)
(*   pr_lcm_eq_decomp : hl_id (hl_lcm_upto n)                      *)
(*     (fold_right Nat.mul 1                                       *)
(*        (map (fun p => p ^ plm_v p (hl_lcm_upto n))               *)
(*             (pen_primes_upto n))).                              *)
(*   【实文调形记录（fail-loud）】N 草案指数位为 pr_v p n（n 本身的   *)
(*   赋值），n=6 处 2^1·3^1·5^0=30 与 L(6)=60 不等，语句面系草案笔误； *)
(*   N 自己的 ⊆ 路线论证「p^{a+1}∣k 且 k≤n ⟹ p^{a+1}≤n 破 e_p 最大性」  *)
(*   对应 e_p=max{e : p^e≤n}=plm_v p (hl_lcm_upto n)（lcm 自身赋值：  *)
(*   p^e∣L(n) ⟺ p^e≤n）。本件按数学为真的指数位 plm_v p (hl_lcm_upto n) *)
(*   落件，其余语句面（hl_id 承载、两表、fold 形）全照 N 草案原形。    *)
(*   双肢：⊇ plq_powprod_dvd_lcm——素幂积整除 L(n)（自建「相异位互素  *)
(*   积整除」plq_powprod_dvd：NoDup 表＋逐元素整除＋相异位 gcd=1     *)
(*   ⟹ 折积整除；BL 桥二 plm_lcm_pow_prod_dvd 的 plm_pairwise_coprime  *)
(*   全对形在素表上不可满足（gcd p p = p），故按相异位形重建并登记）； *)
(*   ⊆ plq_lcm_dvd_powprod——L(n) 整除素幂积（h3_lcm_fold_divide     *)
(*   现成闭合＋燃料强归纳逐数整除件 plq_num_dvd_powprod：m=p^w·m''   *)
(*   剥全幂裂解，plm_v 单调性＋plm_gcd_pow 互素＋plm_dvd_mul_coprime  *)
(*   合拢）。                                                        *)
(* 依赖清单：件 1 abl_Pr_core_01（pr_prime／pr_prime_bool_spec／      *)
(*   pr_mod0_dvd／pr_dvd_mod0／pr_min_factor_exists）＋件 2           *)
(*   abl_Pr_enum_02（pen_primes_upto／pen_primes_upto_S／             *)
(*   pen_in_primes_upto／pen_fold_in_divide／pen_fold_mul_pos）＋件 4  *)
(*   abl_Pr_lcmdecomp_04（plm_v／plm_v_dvd／plm_v_max／plm_gcd_pow／  *)
(*   plm_prime_gcd_1／plm_gcd_prod_1／plm_dvd_mul_coprime）＋         *)
(*   HansonLcm（hl_id／hl_lcm_upto／hl_lcm_divide_all，缓存根 -Q 只读） *)
(*   ＋Hanson3Pow（h3_lcm_fold_divide，缓存根 -Q 只读）＋纯 Stdlib。   *)
(*   编译链序（按各件 Require 面实拍）：core_01 → euclid_03 →         *)
(*   lcmdecomp_04 → enum_02 → 本件（件 3 经件 4 Require 面入链，本件   *)
(*   使用面无件 3 直引）。                                           *)
(* 构造性注记：Set 面承载——主件语句即两 nat 闭式之 hl_id（Set 值      *)
(*   等式归纳型，hl_idrefl 闭合），计算面由 plm_v／pen_primes_upto／   *)
(*   hl_lcm_upto 三个既有可提取 Fixpoint 承载，本件零新增计算件；      *)
(*   Prop 面仅推理脚手架（先例同构）；否定面全走 -> False 形（照 AQ    *)
(*   坑卡，全件零否定记号书写，含证明内部）；零公理零承认零经典逻辑；  *)
(*   数值定装走小实例 vm_compute（n ≤ 4，L(4)=12，坑卡九见烟测注记，    *)
(*   照 CZR14 大数值墙钟纪律）。                                      *)
(* 红线四条自审：                                                   *)
(*   - 红线一（零公理声明词）：全件 Qed，PA 取证块收尾；              *)
(*   - Set 层：主承载＝hl_id Set 面等式（N 件单指定承载），非平凡数学   *)
(*     内容全在证明面与既有 Fixpoint 使用；                          *)
(*   - 非平凡：BL 登记未竟全等式闭合，⊇⊇ 双肢全强度（⊆ 肢含逐数强      *)
(*     归纳剥幂裂解），BL 桥二假说缺陷核验登记并重建，N 语句面指数位    *)
(*     笔误核验调形登记——未达面零、拼凑零；                          *)
(*   - 可提取：语句两面皆为闭式可计算 nat 表达式（烟测 vm_compute      *)
(*     实算验证），提取面随 plm_v/pen/hl 既有账。                     *)
(* 编译配方（链序五件逐件编译）：                                   *)
(*   source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/    *)
(*   env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 && cd <池> &&   *)
(*   nice -19 rocq c -native-compiler no \                            *)
(*   -Q /Users/apple/Desktop/ConstructiveWorld/                        *)
(*   vo_local_world_unified_0930 "" <件>.v   （各件依次，本件起加      *)
(*   -Q . ""；见各件 compile log）                                   *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import HansonLcm.
Require Import Hanson3Pow.
Require Import abl_Pr_core_01.
Require Import abl_Pr_enum_02.
Require Import abl_Pr_lcmdecomp_04.

(* ---- §0 零星元件 ---- *)

(* 折积：w ≤ v ⟹ p^w ∣ p^v *)
Lemma plq_pow_le_dvd : forall p w v : nat,
  w <= v -> Nat.divide (p ^ w) (p ^ v).
Proof.
  intros p w v Hw. exists (p ^ (v - w)).
  rewrite <- Nat.pow_add_r. f_equal. lia.
Qed.

(* lcm 正性：1 ≤ L(n)（L(0)=1；步进位 lcm=a·(b/g)，g∣b 桥出 b/g ≥ 1） *)
Lemma plq_lcm_pos : forall n : nat, 1 <= hl_lcm_upto n.
Proof.
  induction n as [| n IH].
  - cbn [hl_lcm_upto]. lia.
  - cbn [hl_lcm_upto]. unfold Nat.lcm.
    assert (Hgd : Nat.divide (Nat.gcd (hl_lcm_upto n) (S n)) (S n))
      by apply Nat.gcd_divide_r.
    assert (Hg0 : Nat.gcd (hl_lcm_upto n) (S n) = 0 -> False).
    { intro Hz.
      assert (Hdv : Nat.divide (Nat.gcd (hl_lcm_upto n) (S n)) (S n))
        by apply Nat.gcd_divide_r.
      rewrite Hz in Hdv. apply Nat.divide_0_l in Hdv. lia. }
    pose proof (Nat.div_mod (S n) (Nat.gcd (hl_lcm_upto n) (S n)) Hg0) as Hdm.
    assert (Hmod : S n mod Nat.gcd (hl_lcm_upto n) (S n) = 0)
      by (apply (pr_dvd_mod0 _ (S n)); [lia | exact Hgd]).
    rewrite Hmod, Nat.add_0_r in Hdm.
    destruct (S n / Nat.gcd (hl_lcm_upto n) (S n)) as [| q] eqn:Eq.
    + exfalso. rewrite Nat.mul_0_r in Hdm. lia.
    + apply Nat.le_trans with (1 * 1).
      * lia.
      * apply Nat.mul_le_mono; lia.
Qed.

(* 折积正性：逐元素 ≥1 ⟹ 折积 ≥1（枚举件 pen_fold_mul_pos 复用即可） *)

(* 素 p 不整除 m ⟹ gcd p m = 1（gcd 三分定向：g∣p 素 ⟹ g=1 或 g=p） *)
Lemma plq_gcd_1_of_nondvd : forall p m : nat,
  pr_prime p -> 1 <= m -> (Nat.divide p m -> False) -> Nat.gcd p m = 1.
Proof.
  intros p m [Hp2 Hpdiv] Hm Hnd.
  destruct (Nat.eq_dec (Nat.gcd p m) 1) as [E1 | NE1].
  - exact E1.
  - exfalso.
    assert (Hgp : Nat.divide (Nat.gcd p m) p) by apply Nat.gcd_divide_l.
    assert (Hgm : Nat.divide (Nat.gcd p m) m) by apply Nat.gcd_divide_r.
    assert (Hle : Nat.gcd p m <= p)
      by (apply Nat.divide_pos_le; [lia | exact Hgp]).
    remember (Nat.gcd p m) as g eqn:Eg.
    destruct g as [| [| g']].
    + apply Nat.divide_0_l in Hgp. lia.
    + apply NE1. reflexivity.
    + rewrite Eg in Hgp. rewrite Eg in Hgm.
      assert (Hg2 : Nat.gcd p m = p).
      { destruct (Nat.eq_dec (Nat.gcd p m) p) as [Eg2 | NEg2].
        - exact Eg2.
        - exfalso. apply (Hpdiv (Nat.gcd p m)); [lia | lia | exact Hgp]. }
      rewrite Hg2 in Hgm. apply Hnd. exact Hgm.
Qed.

(* NoDup 表拼接（stdlib 缺位自建：in_app_iff 三分） *)
Lemma plq_nodup_app : forall l1 l2 : list nat,
  NoDup l1 -> NoDup l2 ->
  (forall x : nat, In x l1 -> In x l2 -> False) ->
  NoDup (l1 ++ l2).
Proof.
  induction l1 as [| a t IH]; intros l2 H1 H2 Hdisj.
  - simpl. exact H2.
  - simpl. apply NoDup_cons.
    + intro Hin. apply in_app_or in Hin. destruct Hin as [Hit | Hin2].
      * inversion H1 as [| a0 t0 Hnin Hnd0 Heq]; subst.
        apply Hnin. exact Hit.
      * apply (Hdisj a). apply in_eq. exact Hin2.
    + apply IH.
      * inversion H1 as [| a0 t0 Hnin Hnd0 Heq]; subst. exact Hnd0.
      * exact H2.
      * intros x Hx1 Hx2. apply (Hdisj x); [apply in_cons; exact Hx1 | exact Hx2].
Qed.

(* 枚举表无重：pen_primes_upto n NoDup（S n ∉ pen n 由 In 刻画） *)
Lemma plq_pen_nodup : forall n : nat, NoDup (pen_primes_upto n).
Proof.
  induction n as [| n IH].
  - apply NoDup_nil.
  - rewrite pen_primes_upto_S. destruct (pr_prime_bool (S n)) eqn:Eb.
    + apply plq_nodup_app.
      * exact IH.
      * apply NoDup_cons.
        -- intros Hc. destruct Hc.
        -- apply NoDup_nil.
      * intros x Hx1 Hx2. destruct Hx2 as [Ex | Hc].
        -- subst x.
           destruct (proj1 (pen_in_primes_upto (S n) n) Hx1) as [_ Hle].
           lia.
        -- destruct Hc.
    + change (if false then S n :: nil else nil) with (@nil nat).
      rewrite app_nil_r. exact IH.
Qed.

(* ---- §1 赋值面补强：plm_v 的下幂整除肢与单调性 ---- *)

(* 登攀值下幂全整除：w ≤ plm_vmax p k e ⟹ p^w ∣ k *)
Lemma plq_vmax_dvd_le : forall p k e w : nat,
  w <= plm_vmax p k e -> Nat.divide (p ^ w) k.
Proof.
  intros p k e. induction e as [| e' IH]; intros w Hw.
  - simpl in Hw. assert (E : w = 0) by lia. subst w.
    rewrite Nat.pow_0_r. apply Nat.divide_1_l.
  - change (plm_vmax p k (S e'))
      with (if Nat.eqb (k mod p ^ S (plm_vmax p k e')) 0
            then S (plm_vmax p k e')
            else plm_vmax p k e') in Hw.
    destruct (Nat.eqb (k mod p ^ S (plm_vmax p k e')) 0) eqn:Em.
    + simpl in Hw.
      apply Nat.eqb_eq in Em.
      destruct (Nat.eq_dec w (S (plm_vmax p k e'))) as [Ew | NEw].
      * subst w.
        destruct (Nat.eq_dec p 0) as [Ep0 | Ep0].
        -- rewrite Ep0 in Em |- *.
           change (0 ^ S (plm_vmax 0 k e')) with 0 in Em.
           rewrite Nat.mod_0_r in Em. rewrite Em.
           change (0 ^ S (plm_vmax 0 k e')) with 0.
           apply Nat.divide_0_r.
        -- assert (Hpos : 1 <= p ^ S (plm_vmax p k e')).
           { pose proof (Nat.pow_nonzero p (S (plm_vmax p k e')) Ep0). lia. }
           exact (pr_mod0_dvd (p ^ S (plm_vmax p k e')) k Hpos Em).
      * apply IH. lia.
    + simpl in Hw. exact (IH w Hw).
Qed.

(* plm_v 下幂整除肢（件 4 spec 双肢之外的第三肢，本件补齐） *)
Lemma plq_v_dvd_le : forall p k w : nat,
  w <= plm_v p k -> Nat.divide (p ^ w) k.
Proof.
  intros p k w Hw. unfold plm_v.
  exact (plq_vmax_dvd_le p k k w Hw).
Qed.

(* 赋值单调性：x ∣ y ∧ 1 ≤ y ∧ 1 < p ⟹ plm_v p x ≤ plm_v p y
   （反证：若反向，则 p^{S(v_y)}∣x∣y 破 v_y 最大性） *)
Lemma plq_v_mono : forall p x y : nat,
  1 < p -> 1 <= y -> Nat.divide x y -> plm_v p x <= plm_v p y.
Proof.
  intros p x y Hp Hy Hdvd.
  destruct (le_lt_dec (plm_v p x) (plm_v p y)) as [Hle | Hlt].
  - exact Hle.
  - exfalso.
    assert (Hd1 : Nat.divide (p ^ S (plm_v p y)) x)
      by (apply plq_v_dvd_le; lia).
    apply (plm_v_max p y Hp Hy).
    apply (Nat.divide_trans (p ^ S (plm_v p y)) x y); assumption.
Qed.

(* ---- §2 ⊇ 肢：素幂积整除 L(n)（相异位互素积整除件重建） ---- *)

(* 相异位互素积整除：NoDup 表＋逐元素整除 c＋相异位 gcd(f p, f q)=1
   ⟹ 映像折积整除 c（头尾裂解：头元与尾折积互素＝plm_gcd_prod_1）。
   【BL 桥二重建注记】plm_pairwise_coprime 全对形（含 x=y）在素表上
   不可满足（gcd p p = p），故按相异位形＋NoDup 重建。 *)
Lemma plq_powprod_dvd : forall (l : list nat) (f : nat -> nat) (c : nat),
  NoDup l ->
  (forall p : nat, In p l -> Nat.divide (f p) c) ->
  (forall p q : nat, In p l -> In q l ->
    (p = q -> False) -> Nat.gcd (f p) (f q) = 1) ->
  Nat.divide (fold_right Nat.mul 1 (map f l)) c.
Proof.
  intros l f c. induction l as [| x t IH]; intros Hnd Hdiv Hcop.
  - simpl. apply Nat.divide_1_l.
  - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnin Hnd0].
    simpl. apply plm_dvd_mul_coprime.
    + apply Hdiv. apply in_eq.
    + apply IH.
      * exact Hnd0.
      * intros p Hp. apply Hdiv. apply in_cons. exact Hp.
      * intros p q Hp Hq Hpq. apply Hcop.
        -- apply in_cons. exact Hp.
        -- apply in_cons. exact Hq.
        -- exact Hpq.
    + apply (plm_gcd_prod_1 (map f t) (f x)).
      intros y Hy. apply in_map_iff in Hy. destruct Hy as [p [Hfp Hpt]].
      rewrite <- Hfp. apply Hcop.
      * apply in_eq.
      * apply in_cons. exact Hpt.
      * intro Hxp. subst p. apply Hnin. exact Hpt.
Qed.

(* ⊇ 肢主件：素表（≤n 的素数表）之 L(n)-赋值幂表折积整除 L(n) *)
Theorem plq_powprod_dvd_lcm : forall n : nat,
  Nat.divide
    (fold_right Nat.mul 1
       (map (fun p : nat => p ^ plm_v p (hl_lcm_upto n))
            (pen_primes_upto n)))
    (hl_lcm_upto n).
Proof.
  intro n.
  apply (plq_powprod_dvd _ (fun p : nat => p ^ plm_v p (hl_lcm_upto n))).
  - apply plq_pen_nodup.
  - intros p Hp. exact (plm_v_dvd p (hl_lcm_upto n)).
  - intros p q Hp Hq Hpq. apply plm_gcd_pow.
    destruct (proj1 (pen_in_primes_upto p n) Hp) as [Hpp _].
    destruct (proj1 (pen_in_primes_upto q n) Hq) as [Hqq _].
    exact (plm_prime_gcd_1 p q Hpp Hqq Hpq).
Qed.

(* ---- §3 ⊆ 肢：L(n) 整除素幂积（逐数剥幂强归纳） ---- *)

(* 逐数整除件：1 ≤ m ≤ n ⟹ m 整除「≤n 素表之 L(n)-赋值幂表折积」。
   燃料强归纳（燃料=n 界，m 递降于真除因子 m''）：素位直入表；合数位
   取最小素因子 p，剥全幂 m = p^w·m''（p 不整除 m''），m'' 强归纳整除，
   p^w 经赋值单调性（m ∣ L(n)）幂界入表，互素积整除合拢。 *)
Lemma plq_num_dvd_powprod : forall fuel m : nat, m <= fuel -> 1 <= m ->
  forall n : nat, m <= n ->
  Nat.divide m
    (fold_right Nat.mul 1
       (map (fun p : nat => p ^ plm_v p (hl_lcm_upto n))
            (pen_primes_upto n))).
Proof.
  intro fuel. induction fuel as [| f IH]; intros m Hmf Hm n Hmn.
  - exfalso. lia.
  - destruct (Nat.eq_dec m 1) as [E1 | NE1].
    + rewrite E1. apply Nat.divide_1_l.
    + assert (Hm2 : 2 <= m) by lia.
      destruct (pr_min_factor_exists m Hm2) as [p Hpf].
      destruct Hpf as [Hpd Hpp]. destruct Hpp as [Hp2 Hpdiv].
      assert (Hpm : p <= m)
        by (apply Nat.divide_pos_le; [lia | exact Hpd]).
      assert (Hw1 : 1 <= plm_v p m).
      { destruct (plm_v p m) as [| w'] eqn:Ew; [ | lia].
        exfalso. apply (plm_v_max p m); [lia | exact Hm |].
        rewrite Ew, Nat.pow_1_r. exact Hpd. }
      assert (Hpw : Nat.divide (p ^ plm_v p m) m) by apply plm_v_dvd.
      assert (Hpw0 : p ^ plm_v p m = 0 -> False)
        by (apply Nat.pow_nonzero; lia).
      assert (Hsplit : p ^ plm_v p m * (m / p ^ plm_v p m) = m).
      { pose proof (Nat.div_mod m (p ^ plm_v p m) Hpw0) as Hdm.
        assert (Hmod : m mod p ^ plm_v p m = 0)
          by (apply (pr_dvd_mod0 (p ^ plm_v p m) m); [lia | exact Hpw]).
        rewrite Hmod, Nat.add_0_r in Hdm. symmetry. exact Hdm. }
      assert (Hm2p : 1 <= m / p ^ plm_v p m).
      { destruct (m / p ^ plm_v p m) as [| q] eqn:Eq; [ | lia].
        exfalso. rewrite Nat.mul_0_r in Hsplit. lia. }
      assert (H2pw : 2 <= p ^ plm_v p m).
      { apply Nat.le_trans with (p ^ 1).
        - rewrite Nat.pow_1_r. lia.
        - apply Nat.pow_le_mono_r; lia. }
      assert (Hm2lt : m / p ^ plm_v p m < m).
      { assert (Hstep : 2 * (m / p ^ plm_v p m)
                        <= p ^ plm_v p m * (m / p ^ plm_v p m))
          by (apply Nat.mul_le_mono_r; exact H2pw).
        lia. }
      assert (Hm2f : m / p ^ plm_v p m <= f) by lia.
      assert (Hm2n : m / p ^ plm_v p m <= n) by lia.
      specialize (IH (m / p ^ plm_v p m) Hm2f Hm2p n Hm2n) as IHm2.
      assert (Hpnd : Nat.divide p (m / p ^ plm_v p m) -> False).
      { intros [t Ht].
        apply (plm_v_max p m); [lia | exact Hm |].
        exists t. rewrite Nat.pow_succ_r'.
        rewrite Nat.mul_assoc.
        rewrite <- Ht.
        symmetry.
        rewrite (Nat.mul_comm (m / p ^ plm_v p m) (p ^ plm_v p m)).
        exact Hsplit. }
      assert (Hg1 : Nat.gcd p (m / p ^ plm_v p m) = 1)
        by (apply plq_gcd_1_of_nondvd; [split; [lia | exact Hpdiv] | lia | exact Hpnd]).
      assert (Hgw : Nat.gcd (p ^ plm_v p m) (m / p ^ plm_v p m) = 1).
      { rewrite <- (Nat.pow_1_r (m / p ^ plm_v p m)).
        apply plm_gcd_pow. exact Hg1. }
      assert (Hpwn : plm_v p m <= plm_v p (hl_lcm_upto n)).
      { apply (plq_v_mono p m (hl_lcm_upto n)); [lia | exact (plq_lcm_pos n) |].
        apply (hl_lcm_divide_all n m Hm Hmn). }
      rewrite <- Hsplit. apply plm_dvd_mul_coprime.
      { apply (Nat.divide_trans (p ^ plm_v p m)
                 (p ^ plm_v p (hl_lcm_upto n))).
        { apply plq_pow_le_dvd. exact Hpwn. }
        { apply (pen_fold_in_divide (p ^ plm_v p (hl_lcm_upto n))).
          apply (in_map (fun p0 : nat => p0 ^ plm_v p0 (hl_lcm_upto n))).
          apply (proj2 (pen_in_primes_upto p n)). split.
          - split; [lia | exact Hpdiv].
          - lia. } }
      { exact IHm2. }
      { exact Hgw. }
Qed.

(* ⊆ 肢主件：L(n) 整除素幂积（h3_lcm_fold_divide 现成闭合：
   1..n 全数整除 D ⟹ L(n) ∣ D） *)
Theorem plq_lcm_dvd_powprod : forall n : nat,
  Nat.divide (hl_lcm_upto n)
    (fold_right Nat.mul 1
       (map (fun p : nat => p ^ plm_v p (hl_lcm_upto n))
            (pen_primes_upto n))).
Proof.
  intro n. apply (h3_lcm_fold_divide n). intros m Hm Hmn.
  apply (plq_num_dvd_powprod n m Hmn Hm n Hmn).
Qed.

(* ---- §4 主件（BL 登记未竟闭合）：全等式，hl_id Set 面承载 ---- *)

Theorem pr_lcm_eq_decomp : forall n : nat,
  hl_id (hl_lcm_upto n)
    (fold_right Nat.mul 1
       (map (fun p : nat => p ^ plm_v p (hl_lcm_upto n))
            (pen_primes_upto n))).
Proof.
  intro n.
  assert (Hsup : Nat.divide
    (fold_right Nat.mul 1
       (map (fun p : nat => p ^ plm_v p (hl_lcm_upto n))
            (pen_primes_upto n)))
    (hl_lcm_upto n)) by apply plq_powprod_dvd_lcm.
  assert (Hsub : Nat.divide (hl_lcm_upto n)
    (fold_right Nat.mul 1
       (map (fun p : nat => p ^ plm_v p (hl_lcm_upto n))
            (pen_primes_upto n)))) by apply plq_lcm_dvd_powprod.
  assert (HP : 1 <= fold_right Nat.mul 1
    (map (fun p : nat => p ^ plm_v p (hl_lcm_upto n))
         (pen_primes_upto n))).
  { apply pen_fold_mul_pos. intros x Hx.
    apply in_map_iff in Hx. destruct Hx as [p [Hpv Hpt]].
    rewrite <- Hpv.
    destruct (proj1 (pen_in_primes_upto p n) Hpt) as [Hpp _].
    destruct Hpp as [Hp2 _].
    pose proof (Nat.pow_nonzero p (plm_v p (hl_lcm_upto n))).
    lia. }
  assert (HL : 1 <= hl_lcm_upto n) by apply plq_lcm_pos.
  assert (E : hl_lcm_upto n = fold_right Nat.mul 1
    (map (fun p : nat => p ^ plm_v p (hl_lcm_upto n))
         (pen_primes_upto n))).
  { apply Nat.le_antisymm.
    - apply Nat.divide_pos_le; [lia | exact Hsub].
    - apply Nat.divide_pos_le; [lia | exact Hsup]. }
  rewrite <- E. apply hl_idrefl.
Qed.

(* ---- §5 数值定装烟测（小实例 vm_compute 直算零公设：
   两闭式 nat 面逐点相等） ---- *)

Lemma plq_smoke_0 : hl_lcm_upto 0 =
  fold_right Nat.mul 1
    (map (fun p : nat => p ^ plm_v p (hl_lcm_upto 0))
         (pen_primes_upto 0)).
Proof. vm_compute. reflexivity. Qed.

Lemma plq_smoke_1 : hl_lcm_upto 1 =
  fold_right Nat.mul 1
    (map (fun p : nat => p ^ plm_v p (hl_lcm_upto 1))
         (pen_primes_upto 1)).
Proof. vm_compute. reflexivity. Qed.

Lemma plq_smoke_2 : hl_lcm_upto 2 =
  fold_right Nat.mul 1
    (map (fun p : nat => p ^ plm_v p (hl_lcm_upto 2))
         (pen_primes_upto 2)).
Proof. vm_compute. reflexivity. Qed.

Lemma plq_smoke_4 : hl_lcm_upto 4 =
  fold_right Nat.mul 1
    (map (fun p : nat => p ^ plm_v p (hl_lcm_upto 4))
         (pen_primes_upto 4)).
Proof. vm_compute. reflexivity. Qed.

(* 实例上界注记（本件新坑卡九）：plm_vmax 函数体三处递归调用不共享，
   vm_compute 每层二倍化＝对燃料 k 指数化（核验：plm_v 2 60 > 25s，
   perl-alarm 杀；plm_v 2 12 瞬时）。烟测按 CZR14 纪律取 n ≤ 4
   （L(4)=12，指数 2^12 叶即止）；n=6 起 L(6)=60 必超墙钟，禁止打点
   ——主定理对任意 n 由证明面承载（证明零计算），大实例走提取面。 *)

(* ---- §6 公理审计（Print Assumptions 取证面） ---- *)

Print Assumptions plq_pow_le_dvd.
Print Assumptions plq_lcm_pos.
Print Assumptions plq_gcd_1_of_nondvd.
Print Assumptions plq_nodup_app.
Print Assumptions plq_pen_nodup.
Print Assumptions plq_vmax_dvd_le.
Print Assumptions plq_v_dvd_le.
Print Assumptions plq_v_mono.
Print Assumptions plq_powprod_dvd.
Print Assumptions plq_powprod_dvd_lcm.
Print Assumptions plq_num_dvd_powprod.
Print Assumptions plq_lcm_dvd_powprod.
Print Assumptions pr_lcm_eq_decomp.
