(* ============================================================ *)
(* LW6CosZeroQuant.v                                            *)
(*                                                              *)
(* 使命：本件形式化 cos 在区间 (3/2, 2) 内零点的定量单纯性，      *)
(*       即非退化零点的构造性形态：把「∀eps 距离控制」的唯一性   *)
(*       语句强化为带显式常数的逆界语句——零点 w 连同窗 [lo,hi]   *)
(*       与逆界常数 K，使窗内任意两点 u ≤ v 的 cos 值在第 j 项    *)
(*       分别低于 du、dv 时，|u − v| ≤ K·(du + dv)。主定理给出   *)
(*       cos_pi_half 系非退化零点（K 取 2），推论给出窗内两点    *)
(*       的分离模量形态。                                       *)
(* 依赖：S01_BaseRing（And、NatLe 系）、S02_CauchyComplete（Real、  *)
(*       real_eq、real_lt、QltT/QleT' 及其转换、qeq_le）、        *)
(*       S10_KVQuantTrig（cos_inv_dist_le2、cos_inv_pt、         *)
(*       cauchy_real_cos、cos_pi_half、real_cos_pi_half_zero、    *)
(*       cos_zero_seq、real_lt_three_halves_cos_pi_half、         *)
(*       real_lt_cos_pi_half_five_thirds、real_lt_lower_pt、      *)
(*       real_lt_upper_pt、real_cos_proj、real_lt_eq_lt、         *)
(*       real_eq_of_zero_diff）；Stdlib QArith/Setoid/Morphisms。  *)
(* 对标：S10_KVQuantTrig.v 的 cos_pi_half_unique_widened：本件   *)
(*       把其「∀eps 距离控制」读法改写为「∃K 逆界」读法，        *)
(*       常数 2 即 cos_inv_dist_le2 的原生值，其内部核心估计     *)
(*       为 cos_inv_pt 的 (v²−u²)/6 < du+dv。                    *)
(* 构造性注记：全件 Set/Type 层；零 公理、零 承认件、零经典逻辑；  *)
(*   Q 层比较与存在取 QltT/QleT'/sigT，实层取 real_lt/real_eq；  *)
(*   推论的可判定三支以 Type 层三择归纳证书 lw6q_sep_cert 表出     *)
(*   （QleT' 证书载荷，无 sumbool 注入）；证明位均可擦除，        *)
(*   不引入经典实数公理。                                        *)
(* 编译配方：coqc -q -Q <主vo库根> "" LW6CosZeroQuant.v，         *)
(*   环境变量 COQLIB 与 ROCQLIB 全字面指向 9.1 库根。            *)
(* ============================================================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ---- 非退化零点（Set 层定义）----
   零点 w 连同窗 [lo, hi] 与逆界常数 K 的三元组形态：
   w 是 cos 的零点、落在窗内，且逆界成立——窗内任意两点
   u ≤ v 的 cos 值（第 j 项，j ≥ 2）分别低于 du、dv 时，
   |u − v| ≤ K·(du + dv)。K 有限即「窗内 cos 值小强制两点
   靠近」的定量表达，亦即零点单纯性的量化内容。 *)
Definition lw6q_nondegenerate_zero (w : Real) (lo hi : Q) : Set :=
  And (real_lt (real_const lo) w)
    (And (real_lt w (real_const hi))
      (And (real_eq (cauchy_real_cos w) real_zero)
        (sigT (fun K : Q =>
          And (QltT 0 K)
            (forall (u v du dv : Q) (j : nat), (2 <= j)%nat ->
              QleT' lo u -> QleT' u v -> QleT' v hi ->
              QltT (Qabs (projT1 (cauchy_real_cos (real_const u)) j
                            - projT1 real_zero j)) du ->
              QltT (Qabs (projT1 (cauchy_real_cos (real_const v)) j
                            - projT1 real_zero j)) dv ->
              QleT' (Qabs (u - v)) (K * (du + dv))%Q))))).

(* ---- 逆界引理（常数 2）----
   由 cos_inv_dist_le2 转写：Qlt/Qle 前提面换为 QltT/QleT' 面，
   结论 v − u 换为 |u − v|（u ≤ v 给 Qabs (u−v) == v−u），
   并把 2·(du+dv) 经 qleT'_trans 拆为两步。 *)
Lemma lw6q_cos_inv_bound : forall (u v du dv : Q) (j : nat),
  (2 <= j)%nat ->
  QleT' (3 / 2) u -> QleT' u v -> QleT' v 2 ->
  QltT (Qabs (projT1 (cauchy_real_cos (real_const u)) j
                - projT1 real_zero j)) du ->
  QltT (Qabs (projT1 (cauchy_real_cos (real_const v)) j
                - projT1 real_zero j)) dv ->
  QleT' (Qabs (u - v)) (2 * (du + dv))%Q.
Proof.
  intros u v du dv j Hj Hu0 Huv Hv2 Hdu Hdv.
  assert (Habs : Qabs (u - v) == v - u).
  { rewrite (Qabs_Qminus u v). apply Qabs_pos.
    apply (proj1 (Qle_minus_iff u v)). apply QleT'_to_Qle. exact Huv. }
  apply (qleT'_trans _ (v - u) _).
  - apply Qle_to_QleT'. apply qeq_le. exact Habs.
  - apply qltT_leT'. apply Qlt_to_QltT.
    apply (cos_inv_dist_le2 u v du dv j Hj).
    + apply QleT'_to_Qle. exact Hu0.
    + apply QleT'_to_Qle. exact Huv.
    + apply QleT'_to_Qle. exact Hv2.
    + apply QltT_to_Qlt. exact Hdu.
    + apply QltT_to_Qlt. exact Hdv.
Qed.

(* ---- 端值引理：cos_pi_half < 2 ----
   经 5/3 的序传递：real_lt_cos_pi_half_five_thirds 与
   real_const_lt（5/3 < 2）作 real_lt_trans。 *)
Lemma lw6q_cos_pi_half_lt_two : real_lt cos_pi_half (real_const 2).
Proof.
  apply (real_lt_trans cos_pi_half (real_const (5 / 3)) (real_const 2)).
  - exact real_lt_cos_pi_half_five_thirds.
  - apply real_const_lt. change (Qlt (5 / 3) 2). compute. reflexivity.
Qed.

(* ---- 主定理：cos_pi_half 系非退化零点（K 取 2）----
   窗端点：左端 real_lt_three_halves_cos_pi_half，右端
   lw6q_cos_pi_half_lt_two；零性 real_cos_pi_half_zero；
   逆界分量即 lw6q_cos_inv_bound。 *)
Theorem lw6q_cos_pi_half_nondegenerate :
  lw6q_nondegenerate_zero cos_pi_half (3 / 2) 2.
Proof.
  unfold lw6q_nondegenerate_zero.
  split.
  - exact real_lt_three_halves_cos_pi_half.
  - split.
    + exact lw6q_cos_pi_half_lt_two.
    + split.
      * exact real_cos_pi_half_zero.
      * exists 2.
        split.
        -- apply Qlt_to_QltT. change (Qlt 0 2). compute. reflexivity.
        -- exact lw6q_cos_inv_bound.
Qed.

(* ---- 分离证书（Type 层三择归纳）----
   推论结论面的证书类型：靠近支携带距离的 QleT' 证书，远支两翼
   各携带对应点 cos 值不低于其显式界的 QleT' 证书。与旧形
   （bool 索引 match 族＋远支内层 sumbool）语义等价，全 Type 层。 *)
Inductive lw6q_sep_cert (u v : Real) (du dv : Q) (k : nat) : Set :=
| lw6q_cert_near :
    QleT' (Qabs (projT1 u k - projT1 v k)) (2 * (du + dv))%Q ->
    lw6q_sep_cert u v du dv k
| lw6q_cert_far_u :
    QleT' du (Qabs (projT1 (cauchy_real_cos u) k - projT1 real_zero k)) ->
    lw6q_sep_cert u v du dv k
| lw6q_cert_far_v :
    QleT' dv (Qabs (projT1 (cauchy_real_cos v) k - projT1 real_zero k)) ->
    lw6q_sep_cert u v du dv k.

(* ---- 推论：分离模量形态 ----
   窗内任意两点 u、v：或者二者已互相靠近至模量 2·(du+dv) 之内，
   或者至少一者的 cos 值距零不低于其显式界（du 或 dv）——
   「两点不能同时各自贴近零而又彼此远离」的定量表达。
   三支在 Q 层可判定，证书以 Type 层三择归纳 lw6q_sep_cert
   表出（远支非依赖重铸，消 sumbool 注入位）。 *)
Corollary lw6q_zero_separation_modulus : forall (u v : Real),
  real_lt (real_const (3 / 2)) u -> real_lt u (real_const 2) ->
  real_lt (real_const (3 / 2)) v -> real_lt v (real_const 2) ->
  forall du dv : Q, QltT 0 du -> QltT 0 dv ->
  sigT (fun N : nat => forall k : nat, (N <= k)%nat ->
    lw6q_sep_cert u v du dv k).
Proof.
  intros u v Hul Huu Hvl Hvu du dv Hdu Hdv.
  destruct (real_lt_lower_pt (3 / 2) u Hul) as [Nul HNul].
  destruct (real_lt_upper_pt 2 u Huu) as [Nuu HNuu].
  destruct (real_lt_lower_pt (3 / 2) v Hvl) as [Nvl HNvl].
  destruct (real_lt_upper_pt 2 v Hvu) as [Nvu HNvu].
  exists (Nat.max 2 (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu)))).
  intros k Hk.
  assert (Hk2 : (2 <= k)%nat).
  { apply (Nat.le_trans _ (Nat.max 2 (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu)))) _);
      [apply Nat.le_max_l | exact Hk]. }
  assert (Hkul : (Nul <= k)%nat).
  { apply (Nat.le_trans _ (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu))) _);
      [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max 2 (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu)))) _);
        [apply Nat.le_max_r | exact Hk]]. }
  assert (Hkuu : (Nuu <= k)%nat).
  { apply (Nat.le_trans _ (Nat.max Nuu (Nat.max Nvl Nvu)) _);
      [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu))) _);
        [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max 2 (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu)))) _);
          [apply Nat.le_max_r | exact Hk]]]. }
  assert (Hkvl : (Nvl <= k)%nat).
  { apply (Nat.le_trans _ (Nat.max Nvl Nvu) _);
      [apply Nat.le_max_l | apply (Nat.le_trans _ (Nat.max Nuu (Nat.max Nvl Nvu)) _);
        [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu))) _);
          [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max 2 (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu)))) _);
            [apply Nat.le_max_r | exact Hk]]]]. }
  assert (Hkvu : (Nvu <= k)%nat).
  { apply (Nat.le_trans _ (Nat.max Nvl Nvu) _);
      [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max Nuu (Nat.max Nvl Nvu)) _);
        [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu))) _);
          [apply Nat.le_max_r | apply (Nat.le_trans _ (Nat.max 2 (Nat.max Nul (Nat.max Nuu (Nat.max Nvl Nvu)))) _);
            [apply Nat.le_max_r | exact Hk]]]]. }
  assert (Hul' : Qle (3 / 2) (projT1 u k)) by (apply Qlt_le_weak; apply (HNul k Hkul)).
  assert (Huu' : Qle (projT1 u k) 2) by (apply Qlt_le_weak; apply (HNuu k Hkuu)).
  assert (Hvl' : Qle (3 / 2) (projT1 v k)) by (apply Qlt_le_weak; apply (HNvl k Hkvl)).
  assert (Hvu' : Qle (projT1 v k) 2) by (apply Qlt_le_weak; apply (HNvu k Hkvu)).
  destruct (Qlt_le_dec (Qabs (projT1 (cauchy_real_cos u) k
                                - projT1 real_zero k)) du) as [Hcu | Hcu].
  - (* cos 值 u_k 低于 du：再看 cos 值 v_k *)
    destruct (Qlt_le_dec (Qabs (projT1 (cauchy_real_cos v) k
                                - projT1 real_zero k)) dv) as [Hcv | Hcv].
    + (* 两点 cos 值皆低于界：距离收进模量 2·(du+dv) *)
      apply lw6q_cert_near. apply Qle_to_QleT'. apply Qlt_le_weak.
      assert (Hcu' : Qlt (Qabs (projT1 (cauchy_real_cos (real_const (projT1 u k))) k
                                - projT1 real_zero k)) du).
      { apply (Qle_lt_trans _ (Qabs (projT1 (cauchy_real_cos u) k
                                      - projT1 real_zero k)) _).
        - apply qeq_le. apply Qabs_wd.
          assert (Hq : projT1 (cauchy_real_cos (real_const (projT1 u k))) k ==
                       projT1 (cauchy_real_cos u) k).
          { rewrite (real_cos_proj (real_const (projT1 u k)) k).
            rewrite (real_cos_proj u k). reflexivity. }
          rewrite Hq. reflexivity.
        - exact Hcu. }
      assert (Hcv' : Qlt (Qabs (projT1 (cauchy_real_cos (real_const (projT1 v k))) k
                                - projT1 real_zero k)) dv).
      { apply (Qle_lt_trans _ (Qabs (projT1 (cauchy_real_cos v) k
                                      - projT1 real_zero k)) _).
        - apply qeq_le. apply Qabs_wd.
          assert (Hq : projT1 (cauchy_real_cos (real_const (projT1 v k))) k ==
                       projT1 (cauchy_real_cos v) k).
          { rewrite (real_cos_proj (real_const (projT1 v k)) k).
            rewrite (real_cos_proj v k). reflexivity. }
          rewrite Hq. reflexivity.
        - exact Hcv. }
      destruct (Qlt_le_dec (projT1 v k) (projT1 u k)) as [Hvlu | Huvl].
      * (* v_k < u_k：u 为上点；界随点互换（du↔dv） *)
        assert (Habs : Qabs (projT1 u k - projT1 v k) == projT1 u k - projT1 v k).
        { apply Qabs_pos. apply (proj1 (Qle_minus_iff (projT1 v k) (projT1 u k))).
          apply Qlt_le_weak. exact Hvlu. }
        rewrite Habs.
        assert (Hd : Qlt (projT1 u k - projT1 v k) (2 * (dv + du))).
        { apply (cos_inv_dist_le2 (projT1 v k) (projT1 u k) dv du k Hk2 Hvl'
                                  (Qlt_le_weak (projT1 v k) (projT1 u k) Hvlu)
                                  Huu' Hcv' Hcu'). }
        rewrite (Qplus_comm du dv). exact Hd.
      * (* u_k ≤ v_k：v 为上点 *)
        assert (Habs : Qabs (projT1 u k - projT1 v k) == projT1 v k - projT1 u k).
        { rewrite (Qabs_Qminus (projT1 u k) (projT1 v k)). apply Qabs_pos.
          exact (proj1 (Qle_minus_iff (projT1 u k) (projT1 v k)) Huvl). }
        rewrite Habs.
        apply (cos_inv_dist_le2 (projT1 u k) (projT1 v k) du dv k Hk2 Hul'
                                Huvl Hvu' Hcu' Hcv').
    + (* cos 值 v_k 不低于 dv：远支取 v 翼 *)
      apply lw6q_cert_far_v. apply Qle_to_QleT'. exact Hcv.
  - (* cos 值 u_k 不低于 du：远支取 u 翼 *)
    apply lw6q_cert_far_u. apply Qle_to_QleT'. exact Hcu.
Qed.

(* ---- 闭合核对 ---- *)
Print Assumptions lw6q_cos_inv_bound.
Print Assumptions lw6q_cos_pi_half_lt_two.
Print Assumptions lw6q_cos_pi_half_nondegenerate.
Print Assumptions lw6q_zero_separation_modulus.
