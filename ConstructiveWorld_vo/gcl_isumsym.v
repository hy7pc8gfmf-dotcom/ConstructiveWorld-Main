(* ===================================================================== *)
(*  gcl_isumsym.v —— μ_lib 实降：Isum^sym 积分值序列＋分母链装配             *)
(*  模块名：gcl_isumsym。                                                  *)
(*  使命：承 gcl_famv 族载体与 gcl_sep_generic 分离骨架，铸对称化截断族的    *)
(*        【真二重积分值序列 Isum^sym】与【Hanson 分母链装配】——            *)
(*        μ_lib 8.6377 档的积分面供给链。                                   *)
(*  数学核：                                                                *)
(*    · 二项式和引理 gcl_q_pow_binom：q_pow (1−t) n == Σ_{j≤n} (−1)^j C(n,j) t^j *)
(*      （sgn 定义式递归 + bkC_pascal_shift + 和的平移/加法/数乘五件）。      *)
(*    · 族展开段列 gcl_segsym m M：把 (1−xy)^(m+2)·F_m 与                    *)
(*      (1−(1−x)(1−y))^(m+2)·F_m(1−x,1−y) 按 j×k 双重展开为 zb2 段列          *)
(*      （T 段因子 pei(m+1+j+k, m+1)、C 段因子 pei(m+1, m+1+j+k)，            *)
(*      系数 (1/2)·(−1)^j·C(m+2,j)·C(m+1+k,m+1)）；                          *)
(*      主定理 I【逐点一致】gcl_famsym_beval：zb2_beval_l (gcl_segsym m M)    *)
(*      x y == gcl_famv m M x y 于全点——段列即族被积式的规范展开。            *)
(*    · 积分值序列 gcl_Isum_sym m M := zb2_di_l (gcl_segsym m M)              *)
(*      （库规范两次单积分迭代算子＝段列二重积分，abl_z2_itg_carrier 口径）；   *)
(*      主定理 II【积分闭式一致】gcl_Isum_sym_closed：gcl_Isum_sym m M ==     *)
(*      Σ_{j≤m+2} (−1)^j C(m+2,j)·Σ_{k≤M} C(m+1+k,m+1)·B(m+1+j+k,m+1)²       *)
(*      （B(a,b)=a!b!/(a+b+1)!；C 段 Beta 对称 B(a,b)=B(b,a) 吸收）。         *)
(*      数值锚：gcl_Isum_sym 0 0 = 59/3600、1 1 = 17/21168、                 *)
(*      3 3 = 6634961/3127445521200（vm_compute 字面·独立复算一致）。         *)
(*    · 分母链装配：gcl_dmod m := lcm(1..m+1) 的 Q 嵌入（HansonLcm 列表机）；  *)
(*      ① 0 ≤ dmod 机内；② dmod ≤ 3^(m+1) 由 Hanson 熵上界前提消解；         *)
(*      主定理 III【供给链装配】gcl_supply_sym_weld：熵前提＋积分族界双肢      *)
(*      给定 ⟹ 存在 d 使五层面成立：0 ≤ d、d ≤ 3^(m+1)、0 ≤ Isum^sym、        *)
(*      Isum^sym ≤ weight、d²·Isum^sym < 1（⑤肢＝gcl_sep_generic             *)
(*      零改动使用接合）。                                                  *)
(*  实现注记：QltT/QleT' 包裹内禁 rewrite——全部 Qeq 层证明用 ring/rewrite    *)
(*        直收，Set 肢仅在边界经 Qle_to_QleT'/Qlt_to_QltT 桥换向；乘法单调    *)
(*        一律 Qmult_le_compat_r（_l 不存在）；字面判定用 Qle_bool_iff/       *)
(*        Qlt_bool id_refl 或 cbn 全约列 lia。                               *)
(*  依赖：Stdlib（QArith/ZArith/Arith/Lia/List/Setoid）；S01_BaseRing、       *)
(*        S02_CauchyComplete、S03_QExp、BeukersLists、PolyIntegral、          *)
(*        PadeErrorIntegral、HansonLcm；abl_z2_truncfam/abl_z2_itg_carrier；  *)
(*        abl_dmw2_pointwise_sharp；dig_machine；gcl_coefficient              *)
(*        （gcl_sep_generic/gcl_weight_G）与 gcl_famsym（gcl_famv）。          *)
(*  对标：Rhin–Viola 组结构置换群法之积分序列供给链（μ_lib 8.6377 档）。       *)
(*  构造性注记：全语句 Set 承载；Print Assumptions 全谱 Closed；              *)
(*        Separate Extraction Obj.magic=0；零实数层、零经典逻辑、零 Admitted。 *)
(*  诚实边界：积分族界双肢（0 ≤ Isum^sym ≤ (1/4)(1/12)^m，Rhin 型积分估计）    *)
(*        与 Hanson 熵上界（lcm(1..n) ≤ 3^n）为语句显式前提位（非全局假设，    *)
(*        Print Assumptions 仍 Closed）——五层面供给链其余三肢机内成立。       *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" gcl_isumsym.v             *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists
              PolyIntegral PadeErrorIntegral HansonLcm.
Require Import abl_z2_truncfam abl_z2_itg_carrier abl_dmw2_pointwise_sharp dig_machine.
Require Import gcl_coefficient gcl_famsym.

Open Scope Q_scope.
Open Scope list_scope.

(* ============================================================ *)
(* §0 小件舱：符号递归、natQ 桥、系数和机                                        *)
(* ============================================================ *)

(* 符号 (−1)^j：定义式递归（succ 肢即取负·免 Nat.even 坑） *)
Fixpoint gcl_sgn (j : nat) : Q :=
  match j with
  | 0%nat => 1
  | Datatypes.S j' => 0 - gcl_sgn j'
  end.

Lemma gcl_sgn_succ : forall j : nat, gcl_sgn (Datatypes.S j) == 0 - gcl_sgn j.
Proof. intro j. reflexivity. Qed.

(* natQ 加法桥：(a+b)#1 == a#1 + b#1 *)
Lemma gcl_natQ_add : forall a b : nat,
  (Z.of_nat (a + b) # 1) == (Z.of_nat a # 1) + (Z.of_nat b # 1).
Proof.
  intros a b. unfold Qeq, Qplus. cbn [Qnum Qden Pos.mul].
  rewrite Nat2Z.inj_add. lia.
Qed.

(* Pascal 的 Q 系数推论（预约简 match·免 rewrite 残留红ex） *)
Lemma gcl_bkC_pascal_Q : forall n i : nat,
  (Z.of_nat (bkC (Datatypes.S n) (Datatypes.S i)) # 1)
  == (Z.of_nat (bkC n i) # 1) + (Z.of_nat (bkC n (Datatypes.S i)) # 1).
Proof.
  intros n i. rewrite <- (bkC_pascal_shift n (Datatypes.S i)).
  rewrite gcl_natQ_add. reflexivity.
Qed.

(* (−1)² = 1 *)
Lemma gcl_m1 : (0 - 1) * (0 - 1) == 1.
Proof. vm_compute. reflexivity. Qed.

(* bkC n 0 = 1（Pascal 零列·bkC_pascal_shift 推论） *)
Lemma gcl_bkC_zero : forall n : nat, bkC n 0%nat = 1%nat.
Proof.
  induction n as [| n IH].
  - apply bkC_diag.
  - rewrite <- (bkC_pascal_shift n 0). cbn. exact IH.
Qed.

(* 系数和：Σ_{j≤n} f j·t^j *)
Fixpoint gcl_bsum (f : nat -> Q) (n : nat) (t : Q) : Q :=
  match n with
  | 0%nat => f 0%nat * q_pow t 0%nat
  | Datatypes.S n' => gcl_bsum f n' t + f (Datatypes.S n') * q_pow t (Datatypes.S n')
  end.

(* 一步展开（归纳步显式展开用·免 cbn 迭代摧毁 IH 模式） *)
Lemma gcl_bsum_unfold : forall (f : nat -> Q) (n : nat) (t : Q),
  gcl_bsum f (Datatypes.S n) t
  == gcl_bsum f n t + f (Datatypes.S n) * q_pow t (Datatypes.S n).
Proof. reflexivity. Qed.

(* 逐点相等外延 *)
Lemma gcl_bsum_ext : forall (f g : nat -> Q) (n : nat) (t : Q),
  (forall j : nat, f j == g j) -> gcl_bsum f n t == gcl_bsum g n t.
Proof.
  intros f g n t H. induction n as [| n IH].
  - cbn [gcl_bsum]. rewrite H. reflexivity.
  - cbn [gcl_bsum]. rewrite IH, H. reflexivity.
Qed.

(* 和的加法拆分 *)
Lemma gcl_bsum_add : forall (f g : nat -> Q) (n : nat) (t : Q),
  gcl_bsum (fun j => f j + g j) n t == gcl_bsum f n t + gcl_bsum g n t.
Proof.
  intros f g n t. induction n as [| n IH].
  - cbn [gcl_bsum q_pow]. ring.
  - cbn [gcl_bsum q_pow]. rewrite IH. ring.
Qed.

(* 和的数乘 *)
Lemma gcl_bsum_scale : forall (a : Q) (f : nat -> Q) (n : nat) (t : Q),
  gcl_bsum (fun j => a * f j) n t == a * gcl_bsum f n t.
Proof.
  intros a f n t. induction n as [| n IH].
  - cbn [gcl_bsum q_pow]. ring.
  - cbn [gcl_bsum q_pow]. rewrite IH. ring.
Qed.

(* 和的 t-倍：Σ f j t^(j+1) == t·Σ f j t^j *)
Lemma gcl_bsum_tmul : forall (f : nat -> Q) (n : nat) (t : Q),
  gcl_bsum f n t * t == gcl_bsum (fun j => f j * t) n t.
Proof.
  intros f n t. induction n as [| n IH].
  - cbn [gcl_bsum q_pow]. ring.
  - pose proof (gcl_bsum_unfold f n t) as H1.
    rewrite H1.
    rewrite (gcl_bsum_unfold (fun j => f j * t) n t).
    rewrite <- IH. ring.
Qed.

(* 零首项平移和：Σ_{j≤S n} [j=0 ↦ 0; S i ↦ −f i]·t^j == −t·Σ f i t^i *)
Lemma gcl_bsum_zshift : forall (f : nat -> Q) (n : nat) (t : Q),
  gcl_bsum (fun j => match j with
                     | 0%nat => 0
                     | Datatypes.S i => (0 - 1) * f i
                     end) (Datatypes.S n) t
  == (0 - 1) * (t * gcl_bsum f n t).
Proof.
  intros f n t. induction n as [| n IH].
  - cbn [gcl_bsum q_pow]. ring.
  - pose proof (gcl_bsum_unfold (fun j => match j with
                                          | 0%nat => 0
                                          | Datatypes.S i => (0 - 1) * f i
                                          end) (Datatypes.S n) t) as H1.
    rewrite H1, IH.
    rewrite (gcl_bsum_unfold f n t), (q_pow_succ t (Datatypes.S n)). ring.
Qed.

(* 核心小件·二项式和恒等：q_pow (1−t) n == Σ_{j≤n} (−1)^j C(n,j) t^j
   （bkC_pascal_shift 拆列＋零首项平移和吸收 t·Σ 肢；fn0 (S n)=0 由 bkC_out） *)
Lemma gcl_q_pow_binom : forall (n : nat) (t : Q),
  q_pow (1 - t) n
  == gcl_bsum (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1)) n t.
Proof.
  intros n t. induction n as [| n IH].
  - cbn [q_pow gcl_bsum gcl_sgn]. rewrite bkC_diag. ring.
  - rewrite (q_pow_succ (1 - t) n). rewrite IH.
    assert (E1 : (1 - t) * gcl_bsum (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1)) n t
              == gcl_bsum (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1)) n t
                 - t * gcl_bsum (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1)) n t)
      by ring.
    rewrite E1.
    assert (E2 : t * gcl_bsum (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1)) n t
              == gcl_bsum (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1) * t) n t).
    { rewrite (Qmult_comm t (gcl_bsum (fun j => gcl_sgn j * (Z.of_nat (bkC n j) # 1)) n t)).
      apply gcl_bsum_tmul. }
    rewrite E2.
    (* Pascal 拆列：bkC (S n) j = [j=0↦0; S i↦bkC n i] + bkC n j（natQ 桥拆系数） *)
    assert (Hpt : forall j : nat,
              gcl_sgn j * (Z.of_nat (bkC (Datatypes.S n) j) # 1)
              == gcl_sgn j * (Z.of_nat (bkC n j) # 1)
                 + gcl_sgn j * (Z.of_nat (match j with
                                          | 0%nat => 0
                                          | Datatypes.S i => bkC n i
                                          end) # 1)).
    { intro j. destruct j as [| i].
      - cbn [gcl_sgn]. rewrite !gcl_bkC_zero.
        assert (E0 : (Z.of_nat 0 # 1) == 0) by reflexivity.
        rewrite E0. ring.
      - cbn [gcl_sgn]. rewrite gcl_bkC_pascal_Q. ring. }
    rewrite (gcl_bsum_ext _ _ _ _ Hpt). rewrite gcl_bsum_add.
    (* 平移肢：sgn (S i)·(bkC n i)#1 == −(sgn i·(bkC n i)#1) *)
    assert (Hzpt : forall j : nat,
              gcl_sgn j * (Z.of_nat (match j with
                                     | 0%nat => 0
                                     | Datatypes.S i => bkC n i
                                     end) # 1)
              == match j with
                 | 0%nat => 0
                 | Datatypes.S i => (0 - 1) * (gcl_sgn i * (Z.of_nat (bkC n i) # 1))
                 end).
    { intro j. destruct j as [| i].
      - cbn [gcl_sgn].
        assert (E0 : (Z.of_nat 0 # 1) == 0) by reflexivity.
        rewrite E0. ring.
      - cbn [gcl_sgn]. ring. }
    rewrite (gcl_bsum_ext _ _ _ _ Hzpt). rewrite gcl_bsum_zshift.
    cbn [gcl_bsum].
    (* 首出肢归零：fn0 (S n) = ±bkC n (S n)#1 = 0（bkC_out） *)
    assert (Hzero : gcl_sgn (Datatypes.S n) * (Z.of_nat (bkC n (Datatypes.S n)) # 1)
                      * q_pow t (Datatypes.S n) == 0).
    { rewrite (bkC_out n (Datatypes.S n) (Nat.lt_succ_diag_r n)).
      assert (E0' : (Z.of_nat 0 # 1) == 0) by reflexivity.
      rewrite E0', Qmult_0_r. apply Qmult_0_l. }
    rewrite Hzero, E2. ring.
Qed.

(* ============================================================ *)
(* §1 族展开段列与逐点一致（主定理 I）                                              *)
(* ============================================================ *)

(* 规范段：系数 c、x/y 因子同为 pei_list a b *)
Definition gcl_segof2 (c : Q) (a b : nat) : zb2_seg :=
  (c, (pei_list a b, pei_list a b)).

(* T 形 k-段列：系数 c·C(m+1+k,m+1)、因子 pei(m+1+j+k, m+1)
   （(1−xy)^(m+2)·F 的 j-档展开，k 为部分和指标） *)
Fixpoint gcl_kl (c : Q) (m j k : nat) : list zb2_seg :=
  match k with
  | 0%nat => gcl_segof2 (c * (Z.of_nat (bkC (Datatypes.S m) (Datatypes.S m)) # 1))
                    (Datatypes.S m + j) (Datatypes.S m) :: nil
  | Datatypes.S k' =>
      gcl_segof2 (c * (Z.of_nat (bkC (Datatypes.S m + Datatypes.S k') (Datatypes.S m)) # 1))
                (Datatypes.S m + j + Datatypes.S k') (Datatypes.S m)
      :: gcl_kl c m j k'
  end.

(* C 形 k-段列：同系数、因子 pei(m+1, m+1+j+k)
   （(1−(1−x)(1−y))^(m+2)·F(1−x,1−y) 的 j-档展开——在 (x,y) 求值） *)
Fixpoint gcl_klC (c : Q) (m j k : nat) : list zb2_seg :=
  match k with
  | 0%nat => gcl_segof2 (c * (Z.of_nat (bkC (Datatypes.S m) (Datatypes.S m)) # 1))
                    (Datatypes.S m) (Datatypes.S m + j) :: nil
  | Datatypes.S k' =>
      gcl_segof2 (c * (Z.of_nat (bkC (Datatypes.S m + Datatypes.S k') (Datatypes.S m)) # 1))
                (Datatypes.S m) (Datatypes.S m + j + Datatypes.S k')
      :: gcl_klC c m j k'
  end.

(* 段列逐点求值的拼接律 *)
Lemma gcl_beval_l_app : forall (l1 l2 : list zb2_seg) (x y : Q),
  zb2_beval_l (l1 ++ l2) x y == zb2_beval_l l1 x y + zb2_beval_l l2 x y.
Proof.
  intros l1 l2 x y. induction l1 as [| s l1 IH].
  - cbn [app zb2_beval_l]. ring.
  - cbn [zb2_beval_l app]. rewrite IH. ring.
Qed.

(* T 形 k-段列逐点恒等：beval_l (gcl_kl c m j k) x y == c·(xy)^j·F(m+1,k,x,y) *)
Lemma gcl_beval_kl_T : forall (c : Q) (m j k : nat) (x y : Q),
  zb2_beval_l (gcl_kl c m j k) x y
  == c * q_pow (x * y) j * zb2_beval_l (zb2_segl (Datatypes.S m) k) x y.
Proof.
  intros c m j k x y. induction k as [| k IH].
  - cbn [gcl_kl]. unfold gcl_segof2. cbn [zb2_beval_l]. unfold zb2_beval. cbn [fst snd].
    rewrite (pei_beta_eval (Datatypes.S m + j) (Datatypes.S m) x).
    rewrite (pei_beta_eval (Datatypes.S m + j) (Datatypes.S m) y).
    rewrite (zb2_beval_segl (Datatypes.S m) 0 x y). rewrite zb2_ps_zero.
    rewrite bkC_diag.
    assert (E1 : (Z.of_nat 1 # 1) == 1) by reflexivity.
    rewrite E1.
    rewrite (q_pow_add x (Datatypes.S m) j), (q_pow_add y (Datatypes.S m) j).
    rewrite (zb2_q_pow_mul x y j).
    rewrite (zb2_q_pow_mul x (1 - x) (Datatypes.S m)).
    rewrite (zb2_q_pow_mul y (1 - y) (Datatypes.S m)).
    ring.
  - cbn [gcl_kl]. unfold gcl_segof2. cbn [zb2_beval_l]. unfold zb2_beval. cbn [fst snd].
    rewrite (pei_beta_eval (Datatypes.S m + j + Datatypes.S k) (Datatypes.S m) x).
    rewrite (pei_beta_eval (Datatypes.S m + j + Datatypes.S k) (Datatypes.S m) y).
    rewrite (q_pow_add x (Datatypes.S m + j) (Datatypes.S k)).
    rewrite (q_pow_add y (Datatypes.S m + j) (Datatypes.S k)).
    rewrite (q_pow_add x (Datatypes.S m) j), (q_pow_add y (Datatypes.S m) j).
    rewrite IH.
    rewrite (zb2_beval_segl (Datatypes.S m) (Datatypes.S k) x y).
    rewrite (zb2_beval_segl (Datatypes.S m) k x y).
    rewrite (zb2_ps_unfold (Datatypes.S m) k (x * y)).
    rewrite (zb2_q_pow_mul x y j), (zb2_q_pow_mul x y (Datatypes.S k)).
    rewrite (zb2_q_pow_mul x (1 - x) (Datatypes.S m)).
    rewrite (zb2_q_pow_mul y (1 - y) (Datatypes.S m)).
    ring.
Qed.

(* C 形 k-段列逐点恒等：beval_l (gcl_klC c m j k) x y
   == c·((1−x)(1−y))^j·F(m+1,k,1−x,1−y) *)
Lemma gcl_beval_kl_C : forall (c : Q) (m j k : nat) (x y : Q),
  zb2_beval_l (gcl_klC c m j k) x y
  == c * q_pow ((1 - x) * (1 - y)) j
     * zb2_beval_l (zb2_segl (Datatypes.S m) k) (1 - x) (1 - y).
Proof.
  intros c m j k x y. induction k as [| k IH].
  - cbn [gcl_klC]. unfold gcl_segof2. cbn [zb2_beval_l]. unfold zb2_beval. cbn [fst snd].
    rewrite (pei_beta_eval (Datatypes.S m) (Datatypes.S m + j) x).
    rewrite (pei_beta_eval (Datatypes.S m) (Datatypes.S m + j) y).
    rewrite (zb2_beval_segl (Datatypes.S m) 0 (1 - x) (1 - y)). rewrite zb2_ps_zero.
    rewrite bkC_diag.
    assert (E1 : (Z.of_nat 1 # 1) == 1) by reflexivity.
    rewrite E1.
    rewrite (q_pow_add (1 - x) (Datatypes.S m) j),
            (q_pow_add (1 - y) (Datatypes.S m) j).
    rewrite (zb2_q_pow_mul (1 - x) (1 - y) j).
    rewrite (zb2_q_pow_mul (1 - x) (1 - (1 - x)) (Datatypes.S m)).
    rewrite (zb2_q_pow_mul (1 - y) (1 - (1 - y)) (Datatypes.S m)).
    assert (Ex : (1 - (1 - x)) == x) by ring.
    assert (Ey : (1 - (1 - y)) == y) by ring.
    rewrite (q_pow_wd (1 - (1 - x)) x (Datatypes.S m) Ex).
    rewrite (q_pow_wd (1 - (1 - y)) y (Datatypes.S m) Ey).
    ring.
  - cbn [gcl_klC]. unfold gcl_segof2. cbn [zb2_beval_l]. unfold zb2_beval. cbn [fst snd].
    rewrite (pei_beta_eval (Datatypes.S m) (Datatypes.S m + j + Datatypes.S k) x).
    rewrite (pei_beta_eval (Datatypes.S m) (Datatypes.S m + j + Datatypes.S k) y).
    rewrite (q_pow_add (1 - x) (Datatypes.S m + j) (Datatypes.S k)).
    rewrite (q_pow_add (1 - y) (Datatypes.S m + j) (Datatypes.S k)).
    rewrite (q_pow_add (1 - x) (Datatypes.S m) j).
    rewrite (q_pow_add (1 - y) (Datatypes.S m) j).
    rewrite IH.
    rewrite (zb2_beval_segl (Datatypes.S m) (Datatypes.S k) (1 - x) (1 - y)).
    rewrite (zb2_beval_segl (Datatypes.S m) k (1 - x) (1 - y)).
    rewrite (zb2_ps_unfold (Datatypes.S m) k ((1 - x) * (1 - y))).
    rewrite (zb2_q_pow_mul (1 - x) (1 - y) j),
            (zb2_q_pow_mul (1 - x) (1 - y) (Datatypes.S k)).
    rewrite (zb2_q_pow_mul (1 - x) (1 - (1 - x)) (Datatypes.S m)).
    rewrite (zb2_q_pow_mul (1 - y) (1 - (1 - y)) (Datatypes.S m)).
    assert (Ex : (1 - (1 - x)) == x) by ring.
    assert (Ey : (1 - (1 - y)) == y) by ring.
    rewrite (q_pow_wd (1 - (1 - x)) x (Datatypes.S m) Ex).
    rewrite (q_pow_wd (1 - (1 - y)) y (Datatypes.S m) Ey).
    ring.
Qed.

(* 对称族 j-档系数：cfsym m j = (1/2)·(−1)^j·C(m+2,j) *)
Definition gcl_cfsym (m j : nat) : Q :=
  (1#2) * (gcl_sgn j * (Z.of_nat (bkC (Datatypes.S (Datatypes.S m)) j) # 1)).

(* j-段列（T/C 各一）：r 层累计 j = 0..r，尾拼接 *)
Fixpoint gcl_jlT (cf : nat -> Q) (m M r : nat) : list zb2_seg :=
  match r with
  | 0%nat => gcl_kl (cf 0%nat) m 0%nat M
  | Datatypes.S r' => gcl_jlT cf m M r' ++ gcl_kl (cf (Datatypes.S r')) m (Datatypes.S r') M
  end.

Fixpoint gcl_jlC (cf : nat -> Q) (m M r : nat) : list zb2_seg :=
  match r with
  | 0%nat => gcl_klC (cf 0%nat) m 0%nat M
  | Datatypes.S r' => gcl_jlC cf m M r' ++ gcl_klC (cf (Datatypes.S r')) m (Datatypes.S r') M
  end.

(* j-段列逐点恒等：Σ_{j≤r} cf j·(xy)^j·F == bsum cf r (xy)·F *)
Lemma gcl_beval_jl_T : forall (cf : nat -> Q) (m M r : nat) (x y : Q),
  zb2_beval_l (gcl_jlT cf m M r) x y
  == gcl_bsum cf r (x * y) * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y.
Proof.
  intros cf m M r x y. induction r as [| r IH].
  - cbn [gcl_jlT]. rewrite gcl_beval_kl_T. cbn [gcl_bsum q_pow]. ring.
  - cbn [gcl_jlT]. rewrite gcl_beval_l_app. rewrite IH.
    rewrite (gcl_beval_kl_T (cf (Datatypes.S r)) m (Datatypes.S r) M x y).
    cbn [gcl_bsum]. ring.
Qed.

Lemma gcl_beval_jl_C : forall (cf : nat -> Q) (m M r : nat) (x y : Q),
  zb2_beval_l (gcl_jlC cf m M r) x y
  == gcl_bsum cf r ((1 - x) * (1 - y))
     * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1 - x) (1 - y).
Proof.
  intros cf m M r x y. induction r as [| r IH].
  - cbn [gcl_jlC]. rewrite gcl_beval_kl_C. cbn [gcl_bsum q_pow]. ring.
  - cbn [gcl_jlC]. rewrite gcl_beval_l_app. rewrite IH.
    rewrite (gcl_beval_kl_C (cf (Datatypes.S r)) m (Datatypes.S r) M x y).
    cbn [gcl_bsum]. ring.
Qed.

(* 对称族展开段列：T 侧 j-段列与 C 侧 j-段列拼接，j = 0..m+2 *)
Definition gcl_segsym (m M : nat) : list zb2_seg :=
  gcl_jlT (gcl_cfsym m) m M (Datatypes.S (Datatypes.S m))
  ++ gcl_jlC (gcl_cfsym m) m M (Datatypes.S (Datatypes.S m)).

(* cfsym 和 == (1/2)·幂（二项式和改写） *)
Lemma gcl_bsum_cfsym : forall (m : nat) (t : Q),
  gcl_bsum (gcl_cfsym m) (Datatypes.S (Datatypes.S m)) t
  == (1#2) * q_pow (1 - t) (Datatypes.S (Datatypes.S m)).
Proof.
  intros m t.
  assert (Hpt : forall j : nat,
            gcl_cfsym m j
            == (1#2) * (gcl_sgn j * (Z.of_nat (bkC (Datatypes.S (Datatypes.S m)) j) # 1)))
    by (intro j; reflexivity).
  rewrite (gcl_bsum_ext _ _ _ _ Hpt). rewrite gcl_bsum_scale.
  rewrite gcl_q_pow_binom. reflexivity.
Qed.

(* 主定理 I【逐点一致】：对称展开段列逐点求值 == 对称族载体 gcl_famv 于全点 *)
Theorem gcl_famsym_beval : forall (m M : nat) (x y : Q),
  zb2_beval_l (gcl_segsym m M) x y == gcl_famv m M x y.
Proof.
  intros m M x y. unfold gcl_segsym. rewrite gcl_beval_l_app.
  rewrite gcl_beval_jl_T, gcl_beval_jl_C.
  rewrite gcl_bsum_cfsym, gcl_bsum_cfsym.
  unfold gcl_famv. ring.
Qed.

(* ============================================================ *)
(* §2 积分值序列 Isum^sym 与闭式一致（主定理 II）                                    *)
(* ============================================================ *)

(* Beta 闭式：B(a,b) = a!·b!/(a+b+1)! *)
Definition gcl_beta2 (a b : nat) : Q :=
  q_fact a * q_fact b / q_fact (a + b + 1)%nat.

(* 规范段的两次单积分值：c·B(a,b)²（zb2_di_seg_eq 改档） *)
Lemma gcl_di_seg2 : forall (c : Q) (a b : nat),
  zb2_di (gcl_segof2 c a b) == c * gcl_beta2 a b * gcl_beta2 a b.
Proof.
  intros c a b. unfold zb2_di, zb2_yint, gcl_segof2. cbn [fst snd].
  assert (Hs := qeqT_imp_qeq _ _
           (pint_integral_scale (c * pint_integral (pei_list a b)) (pei_list a b))).
  rewrite Hs. rewrite (pei_beta_value a b). unfold gcl_beta2. ring.
Qed.

(* T 形 k-段列积分和（闭式·逐项 c·C·B²） *)
Fixpoint gcl_isum_kl (c : Q) (m j k : nat) : Q :=
  match k with
  | 0%nat => c * (Z.of_nat (bkC (Datatypes.S m) (Datatypes.S m)) # 1)
         * (gcl_beta2 (Datatypes.S m + j) (Datatypes.S m)
            * gcl_beta2 (Datatypes.S m + j) (Datatypes.S m))
  | Datatypes.S k' =>
      gcl_isum_kl c m j k'
      + c * (Z.of_nat (bkC (Datatypes.S m + Datatypes.S k') (Datatypes.S m)) # 1)
        * (gcl_beta2 (Datatypes.S m + j + Datatypes.S k') (Datatypes.S m)
           * gcl_beta2 (Datatypes.S m + j + Datatypes.S k') (Datatypes.S m))
  end.

(* C 形 k-段列积分和（因子 pei(m+1, m+1+j+k)·Beta 对称档） *)
Fixpoint gcl_isum_klC (c : Q) (m j k : nat) : Q :=
  match k with
  | 0%nat => c * (Z.of_nat (bkC (Datatypes.S m) (Datatypes.S m)) # 1)
         * (gcl_beta2 (Datatypes.S m) (Datatypes.S m + j)
            * gcl_beta2 (Datatypes.S m) (Datatypes.S m + j))
  | Datatypes.S k' =>
      gcl_isum_klC c m j k'
      + c * (Z.of_nat (bkC (Datatypes.S m + Datatypes.S k') (Datatypes.S m)) # 1)
        * (gcl_beta2 (Datatypes.S m) (Datatypes.S m + j + Datatypes.S k')
           * gcl_beta2 (Datatypes.S m) (Datatypes.S m + j + Datatypes.S k'))
  end.

(* 段列积分和的拼接律 *)
Lemma gcl_di_l_app : forall (l1 l2 : list zb2_seg),
  zb2_di_l (l1 ++ l2) == zb2_di_l l1 + zb2_di_l l2.
Proof.
  intros l1 l2. induction l1 as [| s l1 IH].
  - cbn [app zb2_di_l]. ring.
  - cbn [zb2_di_l app]. rewrite IH. ring.
Qed.

(* T 形段列积分 == 闭式和 *)
Lemma gcl_di_kl : forall (c : Q) (m j k : nat),
  zb2_di_l (gcl_kl c m j k) == gcl_isum_kl c m j k.
Proof.
  intros c m j k. induction k as [| k IH].
  - cbn [gcl_kl zb2_di_l gcl_isum_kl]. rewrite gcl_di_seg2. ring.
  - cbn [gcl_kl zb2_di_l gcl_isum_kl]. rewrite gcl_di_seg2. rewrite IH. ring.
Qed.

(* C 形段列积分 == 闭式和 *)
Lemma gcl_di_klC : forall (c : Q) (m j k : nat),
  zb2_di_l (gcl_klC c m j k) == gcl_isum_klC c m j k.
Proof.
  intros c m j k. induction k as [| k IH].
  - cbn [gcl_klC zb2_di_l gcl_isum_klC]. rewrite gcl_di_seg2. ring.
  - cbn [gcl_klC zb2_di_l gcl_isum_klC]. rewrite gcl_di_seg2. rewrite IH. ring.
Qed.

(* Beta 对称：C 形闭式和 == T 形闭式和（q_fact 交换） *)
Lemma gcl_isum_klC_eq : forall (c : Q) (m j k : nat),
  gcl_isum_klC c m j k == gcl_isum_kl c m j k.
Proof.
  intros c m j k. induction k as [| k IH].
  - cbn [gcl_isum_klC gcl_isum_kl].
    assert (E : gcl_beta2 (Datatypes.S m) (Datatypes.S m + j)
             == gcl_beta2 (Datatypes.S m + j) (Datatypes.S m))
      by (unfold gcl_beta2, Qdiv;
          replace (Datatypes.S m + (Datatypes.S m + j) + 1)%nat
             with (Datatypes.S m + j + Datatypes.S m + 1)%nat by lia;
          ring).
    rewrite E. ring.
  - cbn [gcl_isum_klC gcl_isum_kl]. rewrite IH.
    assert (E : gcl_beta2 (Datatypes.S m) (Datatypes.S m + j + Datatypes.S k)
             == gcl_beta2 (Datatypes.S m + j + Datatypes.S k) (Datatypes.S m))
      by (unfold gcl_beta2, Qdiv;
          replace (Datatypes.S m + (Datatypes.S m + j + Datatypes.S k) + 1)%nat
             with (Datatypes.S m + j + Datatypes.S k + Datatypes.S m + 1)%nat by lia;
          ring).
    rewrite E. ring.
Qed.

(* j-段列积分和（累计 j = 0..r） *)
Fixpoint gcl_isum_jl (cf : nat -> Q) (m M r : nat) : Q :=
  match r with
  | 0%nat => gcl_isum_kl (cf 0%nat) m 0%nat M
  | Datatypes.S r' =>
      gcl_isum_jl cf m M r' + gcl_isum_kl (cf (Datatypes.S r')) m (Datatypes.S r') M
  end.

(* T 形 j-段列积分 == 闭式 j-和 *)
Lemma gcl_di_jl_T : forall (cf : nat -> Q) (m M r : nat),
  zb2_di_l (gcl_jlT cf m M r) == gcl_isum_jl cf m M r.
Proof.
  intros cf m M r. induction r as [| r IH].
  - cbn [gcl_jlT gcl_isum_jl]. rewrite gcl_di_kl. reflexivity.
  - cbn [gcl_jlT gcl_isum_jl]. rewrite gcl_di_l_app.
    rewrite IH, (gcl_di_kl (cf (Datatypes.S r)) m (Datatypes.S r) M). reflexivity.
Qed.

(* C 形 j-段列积分 == 同一闭式 j-和（Beta 对称吸收） *)
Lemma gcl_di_jl_C : forall (cf : nat -> Q) (m M r : nat),
  zb2_di_l (gcl_jlC cf m M r) == gcl_isum_jl cf m M r.
Proof.
  intros cf m M r. induction r as [| r IH].
  - cbn [gcl_jlC gcl_isum_jl]. rewrite gcl_di_klC, gcl_isum_klC_eq. reflexivity.
  - cbn [gcl_jlC gcl_isum_jl]. rewrite gcl_di_l_app.
    rewrite IH, (gcl_di_klC (cf (Datatypes.S r)) m (Datatypes.S r) M),
            (gcl_isum_klC_eq (cf (Datatypes.S r)) m (Datatypes.S r) M). reflexivity.
Qed.

(* 无权 j-和（闭式装订形） *)
Fixpoint gcl_jsum (f : nat -> Q) (n : nat) : Q :=
  match n with
  | 0%nat => f 0%nat
  | Datatypes.S n' => gcl_jsum f n' + f (Datatypes.S n')
  end.

Lemma gcl_jsum_ext : forall (f g : nat -> Q) (n : nat),
  (forall j : nat, f j == g j) -> gcl_jsum f n == gcl_jsum g n.
Proof.
  intros f g n H. induction n as [| n IH].
  - cbn [gcl_jsum]. rewrite H. reflexivity.
  - cbn [gcl_jsum]. rewrite IH, H. reflexivity.
Qed.

Lemma gcl_jsum_scale : forall (a : Q) (f : nat -> Q) (n : nat),
  gcl_jsum (fun j => a * f j) n == a * gcl_jsum f n.
Proof.
  intros a f n. induction n as [| n IH].
  - cbn [gcl_jsum]. ring.
  - cbn [gcl_jsum]. rewrite IH. ring.
Qed.

(* 系数归一：isum_kl c == c·isum_kl 1 *)
Lemma gcl_isum_kl_unit : forall (c : Q) (m j k : nat),
  gcl_isum_kl c m j k == c * gcl_isum_kl 1 m j k.
Proof.
  intros c m j k. induction k as [| k IH].
  - cbn [gcl_isum_kl]. ring.
  - cbn [gcl_isum_kl]. rewrite IH. ring.
Qed.

(* isum_jl == 无权 j-和（cf j·isum_kl 1 形） *)
Lemma gcl_isum_jl_jsum : forall (cf : nat -> Q) (m M r : nat),
  gcl_isum_jl cf m M r == gcl_jsum (fun j => cf j * gcl_isum_kl 1 m j M) r.
Proof.
  intros cf m M r. induction r as [| r IH].
  - cbn [gcl_isum_jl gcl_jsum]. rewrite gcl_isum_kl_unit. reflexivity.
  - cbn [gcl_isum_jl gcl_jsum]. rewrite IH, gcl_isum_kl_unit. reflexivity.
Qed.

(* 积分值序列：对称展开段列的库规范两次单积分迭代值 *)
Definition gcl_Isum_sym (m M : nat) : Q := zb2_di_l (gcl_segsym m M).

(* 闭式和：Σ_{j≤m+2} (−1)^j C(m+2,j)·Σ_{k≤M} C(m+1+k,m+1)·B(m+1+j+k,m+1)² *)
Definition gcl_isym_closed (m M : nat) : Q :=
  gcl_jsum (fun j => gcl_sgn j * (Z.of_nat (bkC (Datatypes.S (Datatypes.S m)) j) # 1)
                    * gcl_isum_kl 1 m j M)
           (Datatypes.S (Datatypes.S m)).

(* 主定理 II【积分闭式一致】：Isum^sym == 闭式和 *)
Theorem gcl_Isum_sym_closed : forall m M : nat,
  gcl_Isum_sym m M == gcl_isym_closed m M.
Proof.
  intros m M. unfold gcl_Isum_sym, gcl_segsym. rewrite gcl_di_l_app.
  rewrite gcl_di_jl_T, gcl_di_jl_C.
  rewrite !gcl_isum_jl_jsum.
  assert (Hpt : forall j : nat,
            gcl_cfsym m j * gcl_isum_kl 1 m j M
            == (1#2) * (gcl_sgn j * (Z.of_nat (bkC (Datatypes.S (Datatypes.S m)) j) # 1)
                        * gcl_isum_kl 1 m j M))
    by (intro j; unfold gcl_cfsym; ring).
  rewrite (gcl_jsum_ext _ _ _ Hpt), !gcl_jsum_scale.
  unfold gcl_isym_closed. ring.
Qed.

(* 数值锚（独立复算⑤一致·vm_compute 字面） *)
Lemma gcl_Isum_sym_val0 : gcl_Isum_sym 0%nat 0%nat == (59#3600).
Proof. vm_compute. reflexivity. Qed.

Lemma gcl_Isum_sym_val1 : gcl_Isum_sym 1%nat 1%nat == (17#21168).
Proof. vm_compute. reflexivity. Qed.

Lemma gcl_Isum_sym_val3 : gcl_Isum_sym 3%nat 3%nat == (6634961#3127445521200).
Proof. vm_compute. reflexivity. Qed.

(* 逐点/积分双面一致锚（m=0 档字面） *)
Lemma gcl_segsym_beval_val0 : zb2_beval_l (gcl_segsym 0%nat 0%nat) (1#2) (1#2)
  == gcl_famv 0%nat 0%nat (1#2) (1#2).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §3 Hanson 分母链装配与五层面供给链（主定理 III）                                  *)
(* ============================================================ *)

(* 分离分母的规范嵌入：lcm(1..m+1) 的 Q 像 *)
Definition gcl_dmod (m : nat) : Q :=
  (Z.of_nat (hl_lcm_upto (Datatypes.S m)) # 1)%Q.

(* 肢①：分母嵌入非负（机内） *)
Theorem gcl_dmod_ge0 : forall m : nat, QleT' 0 (gcl_dmod m).
Proof.
  intro m. unfold gcl_dmod. apply Qle_to_QleT'.
  unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* q_pow 3 与 nat 幂的 Q 像逐档相等（幂桥） *)
Lemma gcl_qpow3_eq : forall k : nat, q_pow 3 k == (Z.of_nat (3 ^ k) # 1)%Q.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - cbn [q_pow Nat.pow]. rewrite IH.
    unfold Qeq. cbn [Qnum Qden Qmult]. rewrite Nat2Z.inj_mul. reflexivity.
Qed.

(* natQ 单调 *)
Lemma gcl_natQ_le : forall a b : nat,
  (a <= b)%nat -> QleT' (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof.
  intros a b H. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* 肢②：dmod ≤ 3^(m+1)——由 Hanson 熵上界前提消解（显式前提位·语句内承载） *)
Theorem gcl_dmod_bound : forall m : nat,
  (hl_lcm_upto (Datatypes.S m) <= 3 ^ (Datatypes.S m))%nat ->
  QleT' (gcl_dmod m) (q_pow 3 (Datatypes.S m)).
Proof.
  intros m H. unfold gcl_dmod. apply Qle_to_QleT'.
  apply (Qle_trans _ (Z.of_nat (3 ^ (Datatypes.S m)) # 1)).
  - apply QleT'_to_Qle. apply gcl_natQ_le. exact H.
  - rewrite gcl_qpow3_eq. apply Qle_refl.
Qed.

(* ζ(2) 积分序列五层面供给链（Set 层·sigT 见证形）
   ① 0 ≤ d；② d ≤ 3^(m+1)（Hanson 链）；③ 0 ≤ Isum^sym；
   ④ Isum^sym ≤ (1/4)(1/12)^m（载体界·8.6377 档）；⑤ d²·Isum^sym < 1（分离见证） *)
Definition gcl_supply_sym (m M : nat) : Set :=
  sigT (fun d : Q =>
    And (QleT' 0 d)
      (And (QleT' d (q_pow 3 (Datatypes.S m)))
        (And (QleT' 0 (gcl_Isum_sym m M))
          (And (QleT' (gcl_Isum_sym m M) (gcl_weight_G m))
               (QltT (d * d * gcl_Isum_sym m M) 1))))).

(* 主定理 III【供给链装配】：Hanson 熵前提＋积分族界双肢（显式前提证书位）给定
   ⟹ 供给链 inhabited——⑤肢由 gcl_coefficient 的 gcl_sep_generic 零改动使用接合 *)
Theorem gcl_supply_sym_weld : forall (m M : nat),
  (3 <= m)%nat ->
  (hl_lcm_upto (Datatypes.S m) <= 3 ^ (Datatypes.S m))%nat ->
  QleT' 0 (gcl_Isum_sym m M) ->
  QleT' (gcl_Isum_sym m M) (gcl_weight_G m) ->
  gcl_supply_sym m M.
Proof.
  intros m M Hm HL HI0 HI1. unfold gcl_supply_sym.
  exists (gcl_dmod m).
  split.
  - exact (gcl_dmod_ge0 m).
  - split.
    + exact (gcl_dmod_bound m HL).
    + split.
      * exact HI0.
      * split.
        -- exact HI1.
        -- exact (gcl_sep_generic (fun _ : nat => gcl_Isum_sym m M) m (gcl_dmod m)
                    Hm (gcl_dmod_ge0 m) (gcl_dmod_bound m HL) HI0 HI1).
Defined.

(* ============================================================ *)
(* §4 提取与假设审计                                                              *)
(* ============================================================ *)

Separate Extraction gcl_Isum_sym gcl_isym_closed gcl_segsym gcl_dmod
  gcl_supply_sym_weld.

Print Assumptions gcl_q_pow_binom.
Print Assumptions gcl_famsym_beval.
Print Assumptions gcl_Isum_sym_closed.
Print Assumptions gcl_Isum_sym_val3.
Print Assumptions gcl_segsym_beval_val0.
Print Assumptions gcl_dmod_ge0.
Print Assumptions gcl_dmod_bound.
Print Assumptions gcl_supply_sym_weld.
