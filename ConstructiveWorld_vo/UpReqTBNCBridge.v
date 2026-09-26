(* ==========================================================================)
   UpReqTBNCBridge.v — 二重卷积和的对角折分解
   使命: tbg_ncvsum_bsum/tbg_row_dock/tbg_conv_bsum（ncv 面 == bsum 面桥）、tbg_fold_diagf、tbg_corner 定义与 tbg_diag_face/tbg_diag_seq（卷和对 == 对角折和 + 角块）。
   依赖: S01_BaseRing、S02_CauchyComplete、S03_QExp、UpReqBanachExp、UpReqBanachProd、UpReqBanachDouble等；Stdlib QArith、Lia、Extraction
   对标: 二重 Cauchy 卷积和的三角/对角折求和分解（级数乘积换序面）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachProd.
Require Import UpReqBanachDouble.
Require Import UpReqNormConv.
Require Import UpReqBanachCauchyD.
From Stdlib Require Import QArith.QArith Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* ① 保底半边（ncv 侧）：行面重述桥 + 方块 bsum 折叠形            *)
(* ============================================================ *)

(* 两套求和 Fixpoint（ncv_sum/bsum）逐点 bae 等价——体同形但在     *)
(* 开放 n 处并非转换相等，须经归纳（bae 面禁 rewrite：走           *)
(* change+wd_l 沿库规）。                                          *)
Lemma tbg_ncvsum_bsum : forall (B : BanachAlg) (f : nat -> (@BA B)) (n : nat),
  @bae B (ncv_sum B f n) (bsum B n f).
Proof.
  intros B f n. induction n as [| m IH].
  - change (ncv_sum B f 0%nat) with (@bzero B).
    change (bsum B 0%nat f) with (@bzero B).
    apply (@bae_refl B).
  - change (ncv_sum B f (Datatypes.S m))
      with (@bplus B (ncv_sum B f m) (f m)).
    change (bsum B (Datatypes.S m) f)
      with (@bplus B (bsum B m f) (f m)).
    apply (@bplus_wd_l B). exact IH.
Qed.

(* 行面桥：ncv 行（计数宽 S n）== bd2 行（闭宽 n）——经上件重述。 *)
Lemma tbg_row_dock : forall (B : BanachAlg) (a b : nat -> (@BA B)) (k n : nat),
  @bae B (ncv_row B a b k (Datatypes.S n)) (bd2_row B a b k n).
Proof.
  intros B a b k n.
  unfold ncv_row, bd2_row.
  exact (tbg_ncvsum_bsum B (fun j : nat => @bmult B (a k) (b j))                         (Datatypes.S n)).
Qed.

(* 方块折叠形：ncv_conv m n == Σ_{k<m} ncv_row k n（bsum 承载）    *)
Lemma tbg_conv_bsum : forall (B : BanachAlg) (a b : nat -> (@BA B)) (m n : nat),
  @bae B (ncv_conv B a b m n)
         (bsum B m (fun k : nat => ncv_row B a b k n)).
Proof.
  intros B a b m n. induction m as [| m' IH].
  - change (ncv_conv B a b 0%nat n) with (@bzero B).
    change (bsum B 0%nat (fun k : nat => ncv_row B a b k n))
      with (@bzero B).
    apply (@bae_refl B).
  - change (ncv_conv B a b (Datatypes.S m') n)
      with (@bplus B (ncv_conv B a b m' n) (ncv_row B a b m' n)).
    change (bsum B (Datatypes.S m') (fun k : nat => ncv_row B a b k n))
      with (@bplus B (bsum B m' (fun k : nat => ncv_row B a b k n))
                     (ncv_row B a b m' n)).
    apply (@bplus_wd_l B). exact IH.
Qed.

(* ============================================================ *)
(* ② 保底半边（bd2 侧）：三角行折叠加和 == bd2_diagf 逐项面       *)
(* ============================================================ *)

Lemma tbg_fold_diagf : forall (B : BanachAlg) (a b : nat -> (@BA B)) (n : nat),
  @bae B (bsum B (Datatypes.S n) (fun i : nat => bd2_row B a b i (Nat.sub n i)))
         (bd2_diagf B a b 0%nat n).
Proof.
  intros B a b n.
  apply (@bae_trans B
      (bsum B (Datatypes.S n) (fun i : nat => bd2_row B a b i (Nat.sub n i)))
      (bd2_rect B a b 0%nat n)).
  - unfold bd2_rect.
    apply (@bsum_ext B (Datatypes.S n)
             (fun i : nat => bd2_row B a b i (Nat.sub n i))
             (fun i : nat =>
                bsum B (Datatypes.S (Nat.sub n i))
                   (fun j : nat => @bmult B (a (0%nat + i)%nat) (b j)))).
    intros k Hk.
    unfold bd2_row.
    assert (H0k : (0%nat + k)%nat = k) by apply Nat.add_0_l.
    rewrite H0k.
    apply (@bae_refl B).
  - apply (@bae_trans B
        (bd2_rect B a b 0%nat n) (bd2_tfrom B a b 0%nat n)).
    + exact (@bae_sym B (bd2_tfrom B a b 0%nat n)
                       (bd2_rect B a b 0%nat n)
                       (bd2_tfrom_rect B a b n 0%nat)).
    + apply (@bae_trans B
          (bd2_tfrom B a b 0%nat n) (bd2_diag B n a b)).
      * exact (bd2_tri_eq_diag B n a b).
      * apply (@bae_refl B).
Qed.

(* ============================================================ *)
(* ③ 角余定义（bxcd_U 的一般族化：方块内 i+j>n 的对角外余项）     *)
(* ============================================================ *)

Definition tbg_corner (B : BanachAlg) (a b : nat -> (@BA B)) (n : nat) : (@BA B) :=
  bsum B (Datatypes.S n)
    (fun i : nat =>
       bsum B (Datatypes.S n)
          (fun j : nat =>
             if Nat.ltb (Nat.sub n i) j
             then @bmult B (a i) (b j)
             else @bzero B)).

(* ============================================================ *)
(* ④ 主件：对角逐项桥                                             *)
(*   方块（收敛侧 ncv_conv 依存域）== bd2_diagf 三角逐项面 + 角余 *)
(* ============================================================ *)

Theorem tbg_diag_face : forall (B : BanachAlg) (a b : nat -> (@BA B)) (n : nat),
  @bae B (ncv_conv B a b (Datatypes.S n) (Datatypes.S n))
         (@bplus B (bd2_diagf B a b 0%nat n) (tbg_corner B a b n)).
Proof.
  intros B a b n.
  apply (@bae_trans B
      (ncv_conv B a b (Datatypes.S n) (Datatypes.S n))
      (bsum B (Datatypes.S n) (fun k : nat => ncv_row B a b k (Datatypes.S n)))).
  - exact (tbg_conv_bsum B a b (Datatypes.S n) (Datatypes.S n)).
  - apply (@bae_trans B
        (bsum B (Datatypes.S n) (fun k : nat => ncv_row B a b k (Datatypes.S n)))
        (bsum B (Datatypes.S n) (fun k : nat => bd2_row B a b k n))).
  + apply (@bsum_ext B (Datatypes.S n)
           (fun k : nat => ncv_row B a b k (Datatypes.S n))
           (fun k : nat => bd2_row B a b k n)).
    intros k Hk. exact (tbg_row_dock B a b k n).
  + apply (@bae_trans B
        (bsum B (Datatypes.S n) (fun k : nat => bd2_row B a b k n))
        (bsum B (Datatypes.S n)
           (fun i : nat =>
              @bplus B (bd2_row B a b i (Nat.sub n i))
                      (bsum B (Datatypes.S n)
                         (fun j : nat =>
                            if Nat.ltb (Nat.sub n i) j
                            then @bmult B (a i) (b j)
                            else @bzero B))))).
    * (* 逐行补零拆分（i < S n ⟹ n−i ≤ n） *)
      apply (@bsum_ext B (Datatypes.S n)
               (fun k : nat => bd2_row B a b k n)
               (fun i : nat =>
                  @bplus B (bd2_row B a b i (Nat.sub n i))
                          (bsum B (Datatypes.S n)
                             (fun j : nat =>
                                if Nat.ltb (Nat.sub n i) j
                                then @bmult B (a i) (b j)
                                else @bzero B)))).
      intros i Hi.
      eapply bae_trans.
      -- apply (@bae_refl B).
      -- exact (bxcd_bsum_pad_split B (Nat.sub n i) n
                    (fun j : nat => @bmult B (a i) (b j)) (Nat.le_sub_l n i)).
      * (* 双和拆并：Σ(行+角) == Σ行 + Σ角；行侧折叠 == diagf *)
      eapply bae_trans.
      -- exact (bsum_plus B (Datatypes.S n)
                   (fun i : nat => bd2_row B a b i (Nat.sub n i))
                   (fun i : nat =>
                      bsum B (Datatypes.S n)
                         (fun j : nat =>
                            if Nat.ltb (Nat.sub n i) j
                            then @bmult B (a i) (b j)
                            else @bzero B))).
      -- exact (@bplus_wd_l B
                 (bsum B (Datatypes.S n)
                    (fun i : nat => bd2_row B a b i (Nat.sub n i)))
                 (bd2_diagf B a b 0%nat n)
                 (bsum B (Datatypes.S n)
                    (fun i : nat =>
                       bsum B (Datatypes.S n)
                          (fun j : nat =>
                             if Nat.ltb (Nat.sub n i) j
                             then @bmult B (a i) (b j)
                             else @bzero B)))
                 (tbg_fold_diagf B a b n)).
Qed.

(* 对角序列面（bd2_diag 命名形，收敛侧直接依存形） *)
Corollary tbg_diag_seq : forall (B : BanachAlg) (a b : nat -> (@BA B)) (n : nat),
  @bae B (ncv_conv B a b (Datatypes.S n) (Datatypes.S n))
         (@bplus B (bd2_diag B n a b) (tbg_corner B a b n)).
Proof.
  intros B a b n.
  apply (@bae_trans B
      (ncv_conv B a b (Datatypes.S n) (Datatypes.S n))
      (@bplus B (bd2_diagf B a b 0%nat n) (tbg_corner B a b n))).
  - exact (tbg_diag_face B a b n).
  - exact (@bplus_wd_l B
             (bd2_diagf B a b 0%nat n) (bd2_diag B n a b)
             (tbg_corner B a b n)
             (@bae_refl B (bd2_diagf B a b 0%nat n))).
Qed.

(* ============================================================ *)

(* ============================================================ *)

Print Assumptions tbg_ncvsum_bsum.
Print Assumptions tbg_row_dock.
Print Assumptions tbg_conv_bsum.
Print Assumptions tbg_fold_diagf.
Print Assumptions tbg_diag_face.
Print Assumptions tbg_diag_seq.

From Stdlib Require Import Extraction.
Extraction "_taa9_tbg_extract.ml" tbg_diag_face.
