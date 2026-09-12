(* ============================================================ *)
(* UpReqBanachDouble.v —— 席BT：路径 B 双和三角转置席（20260912） *)
(* ============================================================ *)
(* 任务：三角-对角线-矩形 双和换序恒等式族：                     *)
(*   Σ_{i+j≤n} f i·g j（三角形，行序）                           *)
(*   == Σ_{k≤n} Σ_{a≤k} f a·g(k−a)（对角线分块，k 增序）         *)
(*   == Σ_{i≤n} Σ_{j≤n−i} f i·g j（矩形行化，bsum 承载）         *)
(* —— exp(a+b)=e^a·e^b 总装把柯西方块（UpReqBanachProd 已绿      *)
(*    esp_prod_square）对接到 exp(a+b) 级数的必经换序层。        *)
(* 分层：S1 双和 Fixpoint 定义+小 n 例暖身；S2 三角==对角线      *)
(*   （本席核心）；S3 三角==矩形+行乘积拉出（esp 对接件）。       *)
(* 依赖复用：UpReqBanachProd（bsum 全出口+swap4/rot/ext/mult_l），*)
(*   UpReqBanachExp（Class BanachAlg 面全出口），禁重定义。       *)
(* 红线自审：语句面全 Set 层（bae:BA->BA->Set 承载等词），证内    *)
(*   无经典逻辑；无承认件（不落挂账字面量）。挂账仅注释登记：     *)
(*   exp_add 总装（需 bpow_add，BA 席在飞）+带尾收敛链不属本席。  *)
(* 工程注（沿同款）：类字段投影一律 @显式喂实例；bae 面无         *)
(*   rewrite 实例——一律 change（定义形）+ bae_trans 显式中件，    *)
(*   禁 rewrite 于 bae（nat 层 Leibniz 等式 rewrite 除外，沿      *)
(*   esp_as_bsum 先例）；Fixpoint 均 {struct 预算参}（下标 i 只   *)
(*   前移不动预算，结构递归落在预算参上）。                       *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachProd.
From Stdlib Require Import QArith.QArith Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* ① S1：双和定义（Fixpoint 形）                                  *)
(* ============================================================ *)

(* 矩形行：row i n = Σ_{j≤n} f i·g j（bsum 承载，S3 矩形化复用） *)
Definition bd2_row (B : BanachAlg) (f g : nat -> (@BA B)) (i n : nat) : (@BA B) :=
  bsum B (Datatypes.S n) (fun j : nat => @bmult B (f i) (g j)).

(* 三角形（行序）：tfrom i n = Σ_{a≤n} Σ_{j≤n−a} f(i+a)·g j
   递归：tfrom i (S m) = row i (S m) + tfrom (S i) m（剥首行，预算减一） *)
Fixpoint bd2_tfrom (B : BanachAlg) (f g : nat -> (@BA B)) (i n : nat)
                   {struct n} : (@BA B) :=
  match n with
  | 0%nat => @bmult B (f i) (g 0%nat)
  | Datatypes.S m =>
      @bplus B (bd2_row B f g i (Datatypes.S m))
               (bd2_tfrom B f g (Datatypes.S i) m)
  end.

(* 对角线单块：dline i k = f i·g k + f(i+1)·g(k−1) + … + f(i+k)·g 0
   递归：dline i (S m) = f i·g(S m) + dline (S i) m（首项提出，下标前移） *)
Fixpoint bd2_dline (B : BanachAlg) (f g : nat -> (@BA B)) (i k : nat)
                   {struct k} : (@BA B) :=
  match k with
  | 0%nat => @bmult B (f i) (g 0%nat)
  | Datatypes.S m =>
      @bplus B (@bmult B (f i) (g (Datatypes.S m)))
               (bd2_dline B f g (Datatypes.S i) m)
  end.

(* 对角线分块：diagf i n = Σ_{k≤n} dline i k *)
Fixpoint bd2_diagf (B : BanachAlg) (f g : nat -> (@BA B)) (i n : nat)
                   {struct n} : (@BA B) :=
  match n with
  | 0%nat => @bmult B (f i) (g 0%nat)
  | Datatypes.S m =>
      @bplus B (bd2_diagf B f g i m)
               (bd2_dline B f g i (Datatypes.S m))
  end.

(* 全局域包装：bd2_tri n = Σ_{i+j≤n} f i·g j；
   bd2_diag n = Σ_{k≤n} Σ_{i+j=k} f i·g j *)
Definition bd2_tri (B : BanachAlg) (n : nat) (f g : nat -> (@BA B)) : (@BA B) :=
  bd2_tfrom B f g 0%nat n.
Definition bd2_diag (B : BanachAlg) (n : nat) (f g : nat -> (@BA B)) : (@BA B) :=
  bd2_diagf B f g 0%nat n.

(* S1 暖身例：小 n 定义形闭合（bae_refl 统一至转换闭包） *)
Example bd2_ex_tri0 : forall (B : BanachAlg) (f g : nat -> (@BA B)),
  @bae B (bd2_tri B 0%nat f g) (@bmult B (f 0%nat) (g 0%nat)).
Proof. intros B f g. apply (@bae_refl B). Qed.

Example bd2_ex_diag0 : forall (B : BanachAlg) (f g : nat -> (@BA B)),
  @bae B (bd2_diag B 0%nat f g) (@bmult B (f 0%nat) (g 0%nat)).
Proof. intros B f g. apply (@bae_refl B). Qed.

Example bd2_ex_row0 : forall (B : BanachAlg) (f g : nat -> (@BA B)) (i : nat),
  @bae B (bd2_row B f g i 0%nat)
         (@bplus B (@bzero B) (@bmult B (f i) (g 0%nat))).
Proof. intros B f g i. apply (@bae_refl B). Qed.

(* n=1 全具体例（f=g=常 bone）：三角(1) 行序定义形（含 bsum 基零项） *)
Example bd2_ex_tri1_bone : forall (B : BanachAlg),
  @bae B (bd2_tri B 1%nat (fun _ : nat => @bone B) (fun _ : nat => @bone B))
         (@bplus B (@bplus B (@bplus B (@bzero B) (@bmult B (@bone B) (@bone B)))
                             (@bmult B (@bone B) (@bone B)))
                   (@bmult B (@bone B) (@bone B))).
Proof. intros B. apply (@bae_refl B). Qed.

(* ============================================================ *)
(* ② S2 核心：三角和 == 对角线分块和                              *)
(*    关键几何引理 peel：diagf i (S m) = row i (S m) + diagf (S i) m *)
(* ============================================================ *)

Lemma bd2_diag_peel : forall (B : BanachAlg) (f g : nat -> (@BA B)) (i m : nat),
  @bae B (bd2_diagf B f g i (Datatypes.S m))
         (@bplus B (bd2_row B f g i (Datatypes.S m))
                   (bd2_diagf B f g (Datatypes.S i) m)).
Proof.
  intros B f g i m. induction m as [| m' IH].
  - (* 基例 m=0：A+(B+C) = ((0+A)+B)+C，assoc + bzero 清项 *)
    change (bd2_diagf B f g i (Datatypes.S 0%nat))
      with (@bplus B (@bmult B (f i) (g 0%nat))
                     (@bplus B (@bmult B (f i) (g (Datatypes.S 0%nat)))
                              (@bmult B (f (Datatypes.S i)) (g 0%nat)))).
    change (bd2_diagf B f g (Datatypes.S i) 0%nat)
      with (@bmult B (f (Datatypes.S i)) (g 0%nat)).
    apply (@bae_trans B _
      (@bplus B (@bplus B (@bmult B (f i) (g 0%nat))
                          (@bmult B (f i) (g (Datatypes.S 0%nat))))
                (@bmult B (f (Datatypes.S i)) (g 0%nat))) _).
    + exact (@bplus_assoc B (@bmult B (f i) (g 0%nat))
                           (@bmult B (f i) (g (Datatypes.S 0%nat)))
                           (@bmult B (f (Datatypes.S i)) (g 0%nat))).
    + apply (@bplus_wd_l B
               (@bplus B (@bmult B (f i) (g 0%nat))
                         (@bmult B (f i) (g (Datatypes.S 0%nat))))
               (bd2_row B f g i (Datatypes.S 0%nat))
               (@bmult B (f (Datatypes.S i)) (g 0%nat))).
      apply (@bae_sym B).
      exact (@bplus_wd_l B (@bplus B (@bzero B) (@bmult B (f i) (g 0%nat)))
                          (@bmult B (f i) (g 0%nat))
                          (@bmult B (f i) (g (Datatypes.S 0%nat)))
                          (@bplus_zero_l B (@bmult B (f i) (g 0%nat)))).
  - (* 归纳步：(A'+D)+(E+F') 经 swap4 重排为 (A'+E)+(D+F')；
       尾部 row/diagf 定义形闭合 *)
    change (bd2_diagf B f g i (Datatypes.S (Datatypes.S m')))
      with (@bplus B (bd2_diagf B f g i (Datatypes.S m'))
                     (@bplus B (@bmult B (f i) (g (Datatypes.S (Datatypes.S m'))))
                              (bd2_dline B f g (Datatypes.S i) (Datatypes.S m')))).
    apply (@bae_trans B _
      (@bplus B (@bplus B (bd2_row B f g i (Datatypes.S m'))
                          (bd2_diagf B f g (Datatypes.S i) m'))
                (@bplus B (@bmult B (f i) (g (Datatypes.S (Datatypes.S m'))))
                         (bd2_dline B f g (Datatypes.S i) (Datatypes.S m')))) _).
    + apply (@bplus_wd_l B). exact IH.
    + apply (@bae_trans B _
        (@bplus B (@bplus B (bd2_row B f g i (Datatypes.S m'))
                            (@bmult B (f i) (g (Datatypes.S (Datatypes.S m')))))
                  (@bplus B (bd2_diagf B f g (Datatypes.S i) m')
                           (bd2_dline B f g (Datatypes.S i) (Datatypes.S m')))) _).
      * exact (bplus_swap4 B (bd2_row B f g i (Datatypes.S m'))
                            (bd2_diagf B f g (Datatypes.S i) m')
                            (@bmult B (f i) (g (Datatypes.S (Datatypes.S m'))))
                            (bd2_dline B f g (Datatypes.S i) (Datatypes.S m'))).
      * apply (@bae_refl B).
Qed.

(* 主归纳（n 归纳、i 泛化）：行序三角 == 对角线分块（带下标起点） *)
Lemma bd2_tfrom_diag : forall (B : BanachAlg) (f g : nat -> (@BA B)) (n i : nat),
  @bae B (bd2_tfrom B f g i n) (bd2_diagf B f g i n).
Proof.
  intros B f g n. induction n as [| m IH]; intros i.
  - exact (@bae_refl B (@bmult B (f i) (g 0%nat))).
  - change (bd2_tfrom B f g i (Datatypes.S m))
      with (@bplus B (bd2_row B f g i (Datatypes.S m))
                     (bd2_tfrom B f g (Datatypes.S i) m)).
    apply (@bae_trans B _
      (@bplus B (bd2_row B f g i (Datatypes.S m))
                (bd2_diagf B f g (Datatypes.S i) m)) _).
    + apply (@bplus_wd_r B (bd2_tfrom B f g (Datatypes.S i) m)
                           (bd2_diagf B f g (Datatypes.S i) m)
                           (bd2_row B f g i (Datatypes.S m))).
      exact (IH (Datatypes.S i)).
    + apply (@bae_sym B). exact (bd2_diag_peel B f g i m).
Qed.

(* S2 主件：三角和 == 对角线分块和（全局域） *)
Theorem bd2_tri_eq_diag : forall (B : BanachAlg) (n : nat) (f g : nat -> (@BA B)),
  @bae B (bd2_tri B n f g) (bd2_diag B n f g).
Proof. intros B n f g. exact (bd2_tfrom_diag B f g n 0%nat). Qed.

(* n=1 语义例：三角(1) == 对角线分块(1)，主件特化暖身 *)
Example bd2_ex_n1 : forall (B : BanachAlg) (f g : nat -> (@BA B)),
  @bae B (bd2_tri B 1%nat f g) (bd2_diag B 1%nat f g).
Proof. intros B f g. exact (bd2_tri_eq_diag B 1%nat f g). Qed.

(* ============================================================ *)
(* ③ S3：矩形化（bsum 承载）+ 行乘积拉出对接件                    *)
(* ============================================================ *)

(* 矩形行化：rect i n = Σ_{a≤n} Σ_{j≤n−a} f(i+a)·g j（bsum 双和） *)
Definition bd2_rect (B : BanachAlg) (f g : nat -> (@BA B)) (i n : nat) : (@BA B) :=
  bsum B (Datatypes.S n)
    (fun a : nat => bsum B (Datatypes.S (Nat.sub n a))
                       (fun j : nat => @bmult B (f (i + a)%nat) (g j))).

(* 矩形剥首行：rect i (S m) = row i (S m) + rect (S i) m
   （bsum_rot 首行提出；尾族 (i+S a) 与 (S i+a) 经 nat Leibniz 换标） *)
Lemma bd2_rect_split : forall (B : BanachAlg) (f g : nat -> (@BA B)) (i m : nat),
  @bae B (bd2_rect B f g i (Datatypes.S m))
         (@bplus B (bd2_row B f g i (Datatypes.S m))
                   (bd2_rect B f g (Datatypes.S i) m)).
Proof.
  intros B f g i m.
  change (bd2_rect B f g i (Datatypes.S m))
    with (bsum B (Datatypes.S (Datatypes.S m))
            (fun a : nat => bsum B (Datatypes.S (Nat.sub (Datatypes.S m) a))
                               (fun j : nat => @bmult B (f (i + a)%nat) (g j)))).
  change (bd2_rect B f g (Datatypes.S i) m)
    with (bsum B (Datatypes.S m)
            (fun a : nat => bsum B (Datatypes.S (Nat.sub m a))
                               (fun j : nat => @bmult B (f ((Datatypes.S i) + a)%nat) (g j)))).
  apply (@bae_trans B _
    (@bplus B (bsum B (Datatypes.S (Nat.sub (Datatypes.S m) 0%nat))
                      (fun j : nat => @bmult B (f (i + 0%nat)%nat) (g j)))
              (bsum B (Datatypes.S m)
                 (fun a : nat =>
                    bsum B (Datatypes.S (Nat.sub (Datatypes.S m) (Datatypes.S a)))
                      (fun j : nat => @bmult B (f (i + (Datatypes.S a))%nat) (g j))))) _).
  - apply (@bsum_rot B (Datatypes.S m)
              (fun a : nat => bsum B (Datatypes.S (Nat.sub (Datatypes.S m) a))
                                 (fun j : nat => @bmult B (f (i + a)%nat) (g j)))).
  - apply (@bplus_wd B).
    + (* 首行闭合：i+0 经 nat 换标后定义形收敛 *)
      assert (Hi0 : (i + 0%nat)%nat = i) by lia.
      rewrite Hi0.
      apply (@bae_refl B).
    + (* 尾族换标：(i + S a) = (S i + a)，bsum_ext 逐点 *)
      apply (@bsum_ext B (Datatypes.S m)
        (fun a : nat => bsum B (Datatypes.S (Nat.sub (Datatypes.S m) (Datatypes.S a)))
                           (fun j : nat => @bmult B (f (i + (Datatypes.S a))%nat) (g j)))
        (fun a : nat => bsum B (Datatypes.S (Nat.sub m a))
                           (fun j : nat => @bmult B (f ((Datatypes.S i) + a)%nat) (g j)))).
      intros k Hk.
      assert (Hik : (i + Datatypes.S k)%nat = (Datatypes.S i + k)%nat) by lia.
      rewrite Hik.
      apply (@bae_refl B).
Qed.

(* 三角 == 矩形（带下标一般形；主件全局域特化见 bd2_tri_eq_rect） *)
Lemma bd2_tfrom_rect : forall (B : BanachAlg) (f g : nat -> (@BA B)) (n i : nat),
  @bae B (bd2_tfrom B f g i n) (bd2_rect B f g i n).
Proof.
  intros B f g n. induction n as [| m IH]; intros i.
  - change (bd2_tfrom B f g i 0%nat) with (@bmult B (f i) (g 0%nat)).
    change (bd2_rect B f g i 0%nat)
      with (@bplus B (@bzero B)
                     (@bplus B (@bzero B)
                              (@bmult B (f (i + 0%nat)%nat) (g 0%nat)))).
    assert (Hi0 : (i + 0%nat)%nat = i) by lia.
    rewrite Hi0.
    apply (@bae_trans B _
      (@bplus B (@bzero B) (@bmult B (f i) (g 0%nat))) _).
    + apply (@bae_sym B). apply (@bplus_zero_l B).
    + apply (@bae_sym B). apply (@bplus_zero_l B).
  - change (bd2_tfrom B f g i (Datatypes.S m))
      with (@bplus B (bd2_row B f g i (Datatypes.S m))
                     (bd2_tfrom B f g (Datatypes.S i) m)).
    apply (@bae_trans B _
      (@bplus B (bd2_row B f g i (Datatypes.S m))
                (bd2_rect B f g (Datatypes.S i) m)) _).
    + apply (@bplus_wd_r B (bd2_tfrom B f g (Datatypes.S i) m)
                             (bd2_rect B f g (Datatypes.S i) m)
                             (bd2_row B f g i (Datatypes.S m))).
      exact (IH (Datatypes.S i)).
    + apply (@bae_sym B). exact (bd2_rect_split B f g i m).
Qed.

(* S3 主件：三角和 == 矩形行化双和（全局域） *)
Theorem bd2_tri_eq_rect : forall (B : BanachAlg) (n : nat) (f g : nat -> (@BA B)),
  @bae B (bd2_tri B n f g) (bd2_rect B f g 0%nat n).
Proof. intros B n f g. exact (bd2_tfrom_rect B f g n 0%nat). Qed.

(* 行乘积拉出对接件：row i n = f i · (Σ_{j≤n} g j)——直接换用冻结     *)
(* bsum_mult_l（逐行把矩形行收成乘积，柯西方块对接用）                *)
Lemma bd2_row_mult_l : forall (B : BanachAlg) (i n : nat) (f g : nat -> (@BA B)),
  @bae B (bd2_row B f g i n)
         (@bmult B (f i) (bsum B (Datatypes.S n) g)).
Proof. intros B i n f g. exact (bsum_mult_l B (Datatypes.S n) (f i) g). Qed.

(* S3 对接主件：三角和 == Σ_{i≤n} f i · (Σ_{j≤n−i} g j)
   —— exp 总装注记：以 f := a^k/k!、g := b^k/k! 特化后，
   esp_prod_square 的方块 Σ_{j≤n}Σ_{i≤n} 即本式前 (n+1) 行的前缀块；
   对角线侧 bd2_diag 配 bpow_comm_r（ab=ba）即可做块内换序。 *)
Theorem bd2_tri_eq_rect_row : forall (B : BanachAlg) (n : nat)
                                     (f g : nat -> (@BA B)),
  @bae B (bd2_tri B n f g)
         (bsum B (Datatypes.S n)
            (fun i : nat => @bmult B (f i)
                               (bsum B (Datatypes.S (Nat.sub n i)) g))).
Proof.
  intros B n f g.
  apply (@bae_trans B _ (bd2_rect B f g 0%nat n) _).
  - exact (bd2_tfrom_rect B f g n 0%nat).
  - unfold bd2_rect.
    apply (@bsum_ext B (Datatypes.S n)
      (fun i : nat => bsum B (Datatypes.S (Nat.sub n i))
                         (fun j : nat => @bmult B (f (0%nat + i)%nat) (g j)))
      (fun i : nat => @bmult B (f i)
                         (bsum B (Datatypes.S (Nat.sub n i)) g))).
    intros k Hk.
    apply (@bae_trans B _
      (bsum B (Datatypes.S (Nat.sub n k))
               (fun j : nat => @bmult B (f k) (g j))) _).
    + (* 0 + k ≡ k 定义形闭合 *)
      apply (@bae_refl B).
    + exact (bsum_mult_l B (Datatypes.S (Nat.sub n k)) (f k) g).
Qed.

(* ============================================================ *)
(* 挂账登记（对称挂账，不落承认件）：                             *)
(*   exp_add 总装：e^(a+b) 级数重组需 bpow_add（ab=ba 二项式，     *)
(*     BA 席在飞交付）对接本件 bd2_diag/esp_prod_square；          *)
(*   带尾收敛链（esp_diff_le_tail/exp_series_cauchy 已绿于         *)
(*   UpReqBanachExp）为收敛收尾件，不属本席。                      *)
(* ============================================================ *)
