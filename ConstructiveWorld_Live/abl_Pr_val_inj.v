(* ============================================================ *)
(* abl_Pr_val_inj.v —— 素因子指数向量的单射性（折积分解平行验算）      *)
(* 模块名：abl_Pr_val_inj                                        *)
(* 数学使命：设 p 为素数，l 为两两互异的素数表，各表元 q 配正指数        *)
(*   b q，折积记 ∏_{q∈l} q^(b q)。该折积承载 p 的幂次信息唯一：        *)
(*   p^a 整除折积当且仅当 p 位于表中且 a ≤ b p。三条主结果——           *)
(*   pzb_pow_dvd_prod_le：p^a 整除折积则 p 在表且 a ≤ b p；            *)
(*   pzb_pow_nodvd_prod：p 不在表时折积与 p 的幂互素，二者肢择一；      *)
(*   pzb_prime_dvd_pow：一素数整除他素数的正次幂则二者重合。            *)
(*   论证路径：折积头部裂解——素数 p 整除乘积必落于头因子或尾折积，      *)
(*   头肢经素数重合桥闭合，尾肢归纳递降；强形核心由互素高斯消去完成      *)
(*   （gcd(p^a, q^b) = 1 时 p^a 整除 q^b 乘尾折积则整除尾折积）。       *)
(* 依赖清单：abl_Pr_core_01（pr_prime／pr_mod0_dvd）、                  *)
(*   abl_Pr_lcmdecomp_04（plm_prime_dvd_mul／plm_gcd_pow／              *)
(*   plm_prime_gcd_1／plm_gauss）、Stdlib（Arith.Arith／List／          *)
(*   Bool／Lia）。                                                    *)
(* 构造性注记：全件在 nat 层承载，零公理零承认零经典逻辑；表隶属的       *)
(*   二分判定取和积布尔型，居于 Set 层；否定命题一律写成 P -> False      *)
(*   的自持形；零假设声明、零悬置假设。                                *)
(* 编译配方：                                                       *)
(*   source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&          *)
(*   ulimit -s 65532 && cd <池目录> && nice -19 rocq c                  *)
(*   -native-compiler no -Q <vo_local_world_unified_0930> "" -Q . ""   *)
(*   abl_Pr_val_inj.v                                                *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import abl_Pr_core_01.
Require Import abl_Pr_lcmdecomp_04.

(* ---- §0 幂与整除的基本积木 ---- *)

Lemma pzb_pow_pos : forall p m : nat,
  1 <= p -> 1 <= p ^ m.
Proof.
  intros p m Hp. induction m as [| m' IH].
  - reflexivity.
  - rewrite Nat.pow_succ_r'. apply (Nat.mul_le_mono 1 p 1 (p ^ m')); lia.
Qed.

Lemma pzb_dvd_pow_succ : forall p k : nat,
  1 <= k -> Nat.divide p (p ^ k).
Proof.
  intros p k Hk. destruct k as [| k']; [lia |].
  rewrite Nat.pow_succ_r'. exists (p ^ k').
  apply Nat.mul_comm.
Qed.

Lemma pzb_dvd_cancel_mul : forall x u v : nat,
  x <> 0 -> Nat.divide (x * u) (x * v) -> Nat.divide u v.
Proof.
  intros x u v Hx Hdvd. destruct Hdvd as [z Hz].
  exists z.
  apply (proj1 (Nat.mul_cancel_l v (z * u) x Hx)).
  rewrite Hz. ring.
Qed.

Lemma pzb_dvd_pow_dvd_base : forall p a W : nat,
  1 <= a -> Nat.divide (p ^ a) W -> Nat.divide p W.
Proof.
  intros p a W Ha Hdvd. destruct a as [| a']; [lia |].
  rewrite Nat.pow_succ_r' in Hdvd.
  destruct Hdvd as [z Hz].
  exists (z * p ^ a'). rewrite Hz. ring.
Qed.

(* 正指数整除乘积时的指数上界：p 不落在余因子中则幂次不越界 *)
Lemma pzb_pow_le_of_dvd_mul : forall p a m W : nat,
  pr_prime p -> 1 <= a -> (Nat.divide p W -> False) ->
  Nat.divide (p ^ a) (p ^ m * W) -> a <= m.
Proof.
  intros p a m W Hp Ha Hnp Hdvd.
  destruct Hp as [Hp2 _].
  destruct (le_lt_dec a m) as [Hle | Hlt]; [exact Hle |].
  exfalso.
  assert (Hsplit : exists k, a = m + k /\ 1 <= k)
    by (exists (a - m); split; lia).
  destruct Hsplit as [k [Hk Hk1]].
  rewrite Hk, Nat.pow_add_r in Hdvd.
  assert (Hpm : p ^ m <> 0).
  { assert (Hpos : 1 <= p ^ m) by (apply pzb_pow_pos; lia).
    lia. }
  assert (Hdk : Nat.divide (p ^ k) W)
    by (apply (pzb_dvd_cancel_mul (p ^ m) (p ^ k) W Hpm Hdvd)).
  apply Hnp.
  apply (Nat.divide_trans p (p ^ k) W).
  - apply pzb_dvd_pow_succ. exact Hk1.
  - exact Hdk.
Qed.

(* ---- §1 素数重合桥 ---- *)

Theorem pzb_prime_dvd_pow : forall p q e : nat,
  pr_prime p -> pr_prime q -> 1 <= e -> Nat.divide q (p ^ e) -> q = p.
Proof.
  intros p q e Hp Hq He Hdvd.
  destruct (Nat.eq_dec q p) as [Eq | Neq]; [exact Eq |].
  exfalso.
  assert (Hg : Nat.gcd q p = 1)
    by (apply plm_prime_gcd_1; [exact Hq | exact Hp | exact Neq]).
  destruct Hq as [Hq2 _].
  assert (Hg1 : Nat.gcd (q ^ 1) (p ^ e) = 1)
    by (apply (plm_gcd_pow q p 1 e); exact Hg).
  rewrite Nat.pow_1_r in Hg1.
  assert (Hgd : Nat.divide q (Nat.gcd q (p ^ e)))
    by (apply Nat.gcd_greatest; [apply Nat.divide_refl | exact Hdvd]).
  rewrite Hg1 in Hgd.
  assert (Hle : q <= 1) by (apply (Nat.divide_pos_le q 1); [lia | exact Hgd]).
  lia.
Qed.

(* ---- §2 折积伴件：尾段拒斥与表隶属 ---- *)

(* p 不在表中时 p 不整除折积（对列表归纳的头部裂解） *)
Lemma pzb_nodvd_fold : forall (p : nat) (l : list nat) (b : nat -> nat),
  pr_prime p ->
  (forall q, In q l -> pr_prime q) ->
  (forall q, In q l -> q <> p) ->
  (forall q, In q l -> 1 <= b q) ->
  Nat.divide p (fold_right Nat.mul 1 (map (fun q => q ^ b q) l)) -> False.
Proof.
  intros p l b Hpp Hpr Hne Hb.
  revert Hpr Hne Hb.
  induction l as [| q rest IH]; intros Hpr Hne Hb Hdvd.
  - cbn [map fold_right] in Hdvd.
    destruct Hpp as [Hp2 _].
    assert (Hle : p <= 1)
      by (apply (Nat.divide_pos_le p 1); [lia | exact Hdvd]).
    lia.
  - cbn [map fold_right] in Hdvd.
    destruct (plm_prime_dvd_mul p (q ^ b q)
                (fold_right Nat.mul 1 (map (fun q => q ^ b q) rest))
                Hpp Hdvd) as [Hdq | Hdvr].
    + assert (Hqp : p = q)
        by (apply (pzb_prime_dvd_pow q p (b q));
            [apply Hpr; apply in_eq | exact Hpp
            | apply Hb; apply in_eq | exact Hdq]).
      apply (Hne q (in_eq q rest)). symmetry. exact Hqp.
    + apply IH.
      * intros r Hr. apply Hpr. apply in_cons. exact Hr.
      * intros r Hr. apply Hne. apply in_cons. exact Hr.
      * intros r Hr. apply Hb. apply in_cons. exact Hr.
      * exact Hdvr.
Qed.

(* p 整除折积则 p 位于表中（弱形，无需无重性） *)
Lemma pzb_in_of_dvd : forall (p : nat) (l : list nat) (b : nat -> nat),
  pr_prime p ->
  (forall q, In q l -> pr_prime q) ->
  (forall q, In q l -> 1 <= b q) ->
  Nat.divide p (fold_right Nat.mul 1 (map (fun q => q ^ b q) l)) ->
  In p l.
Proof.
  intros p l b Hpp Hpr Hb Hdvd.
  revert Hpr Hb Hdvd.
  induction l as [| q rest IH]; intros Hpr Hb Hdvd.
  - cbn [map fold_right] in Hdvd.
    destruct Hpp as [Hp2 _].
    assert (Hle : p <= 1)
      by (apply (Nat.divide_pos_le p 1); [lia | exact Hdvd]).
    lia.
  - cbn [map fold_right] in Hdvd.
    destruct (plm_prime_dvd_mul p (q ^ b q)
                (fold_right Nat.mul 1 (map (fun q => q ^ b q) rest))
                Hpp Hdvd) as [Hdq | Hdvr].
    + left. symmetry.
      apply (pzb_prime_dvd_pow q p (b q));
        [apply Hpr; apply in_eq | exact Hpp
        | apply Hb; apply in_eq | exact Hdq].
    + right. apply IH.
      * intros r Hr. apply Hpr. apply in_cons. exact Hr.
      * intros r Hr. apply Hb. apply in_cons. exact Hr.
      * exact Hdvr.
Qed.

(* ---- §3 强形核心与两条主结果 ---- *)

(* 表内定位后的指数上界：非 p 头因子经互素高斯消去剥落 *)
Lemma pzb_le_of_in_dvd : forall (p a : nat) (l : list nat) (b : nat -> nat),
  pr_prime p -> 1 <= a ->
  In p l -> NoDup l ->
  (forall q, In q l -> pr_prime q) ->
  (forall q, In q l -> 1 <= b q) ->
  Nat.divide (p ^ a) (fold_right Nat.mul 1 (map (fun q => q ^ b q) l)) ->
  a <= b p.
Proof.
  intros p a l b Hpp Ha Hin Hnd Hpr Hb Hdvd.
  revert Hin Hnd Hpr Hb Hdvd.
  induction l as [| q rest IH]; intros Hin Hnd Hpr Hb Hdvd.
  - destruct Hin.
  - cbn [map fold_right] in Hdvd.
    simpl in Hin.
    destruct Hin as [Heq | HinR].
    + subst q.
      assert (Hnin : ~ In p rest) by (inversion Hnd; assumption).
      assert (HneR : forall r, In r rest -> r <> p).
      { intros r Hr Hep. apply Hnin. rewrite <- Hep. exact Hr. }
      assert (Hnp : Nat.divide p
                (fold_right Nat.mul 1 (map (fun q => q ^ b q) rest)) -> False).
      { intros Hd.
        apply (pzb_nodvd_fold p rest b Hpp).
        - intros r Hr. apply Hpr. apply in_cons. exact Hr.
        - exact HneR.
        - intros r Hr. apply Hb. apply in_cons. exact Hr.
        - exact Hd. }
      exact (pzb_pow_le_of_dvd_mul p a (b p)
               (fold_right Nat.mul 1 (map (fun q => q ^ b q) rest))
               Hpp Ha Hnp Hdvd).
    + assert (Hnin : ~ In q rest) by (inversion Hnd; assumption).
      assert (Hqp : q <> p).
      { intro Heq. apply Hnin. rewrite Heq. exact HinR. }
      assert (Hndr : NoDup rest) by (inversion Hnd; assumption).
      assert (Hg : Nat.gcd p q = 1)
        by (apply plm_prime_gcd_1;
            [exact Hpp | apply Hpr; apply in_eq
            | intro Heq2; apply Hqp; symmetry; exact Heq2]).
      assert (Hgc : Nat.gcd (p ^ a) (q ^ b q) = 1)
        by (apply (plm_gcd_pow p q a (b q)); exact Hg).
      assert (Hdvr : Nat.divide (p ^ a)
                (fold_right Nat.mul 1 (map (fun q => q ^ b q) rest)))
        by (apply (plm_gauss (p ^ a) (q ^ b q)
                   (fold_right Nat.mul 1 (map (fun q => q ^ b q) rest))
                   Hgc Hdvd)).
      apply IH.
      * exact HinR.
      * exact Hndr.
      * intros r Hr. apply Hpr. apply in_cons. exact Hr.
      * intros r Hr. apply Hb. apply in_cons. exact Hr.
      * exact Hdvr.
Qed.

Theorem pzb_pow_dvd_prod_le : forall p a (l : list nat) (b : nat -> nat),
  pr_prime p -> NoDup l ->
  (forall q, In q l -> pr_prime q) ->
  (forall q, In q l -> 1 <= b q) ->
  1 <= a ->
  Nat.divide (p ^ a) (fold_right Nat.mul 1 (map (fun q => q ^ b q) l)) ->
  exists q, In q l /\ q = p /\ a <= b q.
Proof.
  intros p a l b Hpp Hnd Hpr Hb Ha Hdvd.
  assert (Hin : In p l).
  { apply (pzb_in_of_dvd p l b Hpp Hpr Hb).
    exact (pzb_dvd_pow_dvd_base p a
             (fold_right Nat.mul 1 (map (fun q => q ^ b q) l)) Ha Hdvd). }
  assert (Hle : a <= b p)
    by (apply (pzb_le_of_in_dvd p a l b Hpp Ha Hin Hnd Hpr Hb Hdvd)).
  exists p. split; [exact Hin | split; [reflexivity | exact Hle]].
Qed.

Theorem pzb_pow_nodvd_prod : forall p a (l : list nat) (b : nat -> nat),
  pr_prime p -> NoDup l ->
  (forall q, In q l -> pr_prime q) ->
  (forall q, In q l -> q <> p) ->
  (forall q, In q l -> 1 <= b q) ->
  1 <= a ->
  (Nat.divide (p ^ a) (fold_right Nat.mul 1 (map (fun q => q ^ b q) l)) -> False) \/
  (exists q, In q l /\ q = p).
Proof.
  intros p a l b Hpp Hnd Hpr Hne Hb Ha.
  destruct (In_dec Nat.eq_dec p l) as [Hin | Hnin].
  - right. exists p. split; [exact Hin | reflexivity].
  - left. intros Hdvd.
    apply (pzb_nodvd_fold p l b Hpp Hpr Hne Hb).
    exact (pzb_dvd_pow_dvd_base p a
             (fold_right Nat.mul 1 (map (fun q => q ^ b q) l)) Ha Hdvd).
Qed.

(* ---- §4 数值例证 ---- *)

Example pzb_smoke_fold : fold_right Nat.mul 1 (map (fun q => q ^ 3) (cons 2 (cons 3 nil))) = 216.
Proof. vm_compute. reflexivity. Qed.

Example pzb_smoke_dvd : Nat.eqb ((2 ^ 3 * 3 ^ 2) mod (2 ^ 3)) 0 = true.
Proof. vm_compute. reflexivity. Qed.

Example pzb_smoke_nodvd : Nat.eqb ((2 ^ 3 * 3 ^ 2) mod (5 ^ 1)) 0 = false.
Proof. vm_compute. reflexivity. Qed.

(* ---- §5 尾舱：构造纯度审计 ---- *)

Print Assumptions pzb_pow_pos.
Print Assumptions pzb_dvd_pow_succ.
Print Assumptions pzb_dvd_cancel_mul.
Print Assumptions pzb_dvd_pow_dvd_base.
Print Assumptions pzb_pow_le_of_dvd_mul.
Print Assumptions pzb_prime_dvd_pow.
Print Assumptions pzb_nodvd_fold.
Print Assumptions pzb_in_of_dvd.
Print Assumptions pzb_le_of_in_dvd.
Print Assumptions pzb_pow_dvd_prod_le.
Print Assumptions pzb_pow_nodvd_prod.
