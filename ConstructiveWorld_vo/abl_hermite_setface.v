(* ========================================================================= *)
(* abl_hermite_setface —— LW2Hermite 插值机·核心恒等式面·Set 载体形态重述件    *)
(* （LW2Hermite Set 载体形态重述吸收）                                      *)
(* ========================================================================= *)
(* 使命：把 LW2Hermite 机（Hermite 1873 积分恒等式的纯多项式代数化）的恒等式  *)
(* 面从 Qeq/eq（Prop 根）重述为 QeqT/sigT（Set 载体）形，使泛型逼近机可入本地 *)
(* Set 使用链。CJ/CG 两轮勘定三个 Prop 根位，本件逐条处置：                    *)
(*   ①主恒等式（核恒等式 eps K f 的导数=求值−原函数）——hst_eps_deriv_kernel   *)
(*     Set 面闭合（本件锚）；并附零前提精确版 hst_eps_exact（对一切 K 无条件，  *)
(*     源 §11 lw2i_eps_exact 的 Set 重述）。                                   *)
(*   ②求值和结构（lw2_eps 求值和 = sum_{k<K} f^{(k)} 与逐点律）——             *)
(*     hst_eps_eval_sum_T / hst_qsum0_ext_T / hst_qsum0_add_T /               *)
(*     hst_qsum0_shift_T / hst_eval_add_T：归纳全部在 Set 面原生重证。         *)
(*   ③形式导数交互位（lw2_trans_deriv_iter_eval / lw2_eval_di_add）——余量     *)
(*     不及，按首件策略以 §3 接口类型登记（*_face），不施工不拼凑。            *)
(* 池：沙箱/现役/abl_tmine04_pool/hermite_set/（独占；integ_adopt 三源     *)
(*     LW0QPoly/LW2Hermite/LW2IntegMachine 拷入，链序编译）。                  *)
(* 依赖清单：LW0QPoly（QPoly 及点面律）→ LW2Hermite（lw2_qsum0/lw2_eps/lw2_trans *)
(*     全机）→ 本件；Stdlib QArith/Lia/Arith/Extraction。本件对源机只使用不    *)
(*     改写：定义零复制，恒等式面原生重证。                                   *)
(* 构造性注记：零公理零承认零经典；语句面全部 Set 载体形（hst_Id 为 Set 层      *)
(*     同一型，hst_QeqT 为其 Qcompare 布尔包装，沿 ln2int_adopt/S02 判例）；   *)
(*     hst_Id 居 Set 可自由消去入 Set（Prop 大排除之墙不触）。证内工艺按       *)
(*     E-STAGING-D038 定式：结构性归纳/ext/shift/ext 组装全部在 Set 面走       *)
(*     hst_QeqT 定义展开 + id 系运算（hst_id_eq/hst_qeqT_of_compare/           *)
(*     hst_compare_of_qeqT 双门）；算术叶位降 Qeq 脚手架（ring/Qeq_alt），      *)
(*     禁 Qeq_bool 桥整件硬翻；同余族与锚的组装链逐条留痕于证行。              *)
(* 对标行：Hermite 1873 (C. R. Acad. Sci. Paris 77)；Niven, Irrational        *)
(*     Numbers (1956) 相应章（母工程令注册引用，未在线复核）。载体判例：       *)
(*     ln2int_adopt/S01_BaseRing.v（Set 层 Id）、S02_CauchyComplete.v（QeqT）；*)
(*     工艺卡：E-STAGING-D038（QeqT 目标先降档）、E-STAGING-LW0-PROPELIM-SET。 *)
(* 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&           *)
(*     ulimit -s 65532 && nice -19 coqc -native-compiler no -q -Q . ""         *)
(*     abl_hermite_setface.v（池内先编 LW0QPoly.v、LW2Hermite.v，链序）；      *)
(*     起编前道闸 ps rocq 计 ≤1；coqchk 同 -Q 映射。                          *)
(* 诚实边界：③导数交互位仅登记接口（§3 两个 *_face），未闭合；同余族正门走    *)
(*     QeqT↔Qeq 双门（Prop 脚手架位，语句面 Set）；lw2_deriv_iter_zero_eval    *)
(*     尾零位使用源机 Qeq 面绿件（叶位），未 Set 面重证——均如实登记于 attn。  *)
(* ========================================================================= *)

From Stdlib Require Import QArith Lia Arith.
Require Import LW0QPoly LW2Hermite.

Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Section 0.  Set 载体工具族：Set 层同一型 hst_Id、QeqT 包装、         *)
(* id 系运算与 QeqT↔Qeq 双门、Set 面同余族。                            *)
(* ------------------------------------------------------------------ *)

(* Set 层同一型（S01_BaseRing 判例同构，本件自带以免跨池 Require）。 *)
Inductive hst_Id {A : Set} (x : A) : A -> Set :=
| hst_id_refl : hst_Id x x.

Arguments hst_id_refl {A} {x}.

(* id 系运算：消去（入 Prop eq，合法向下消去）与对称/传递。 *)
Definition hst_id_eq {A : Set} {x y : A} (p : hst_Id x y) : x = y :=
  match p with
  | hst_id_refl => eq_refl
  end.

Definition hst_id_sym {A : Set} {x y : A} (p : hst_Id x y) : hst_Id y x :=
  match p with
  | hst_id_refl => hst_id_refl
  end.

(* QeqT：Q 相等的 Set 载体形——Qcompare 布尔包装（S02 判例形）。 *)
Definition hst_QeqT (a b : Q) : Set :=
  hst_Id (match Qcompare a b with
          | Eq => true
          | _ => false
          end) true.

(* 门一（正向）：Qcompare = Eq 给出 QeqT——定义展开 + 构造。 *)
Lemma hst_qeqT_of_compare : forall a b : Q, Qcompare a b = Eq -> hst_QeqT a b.
Proof.
  intros a b H.
  unfold hst_QeqT.
  rewrite H.
  cbn.
  apply hst_id_refl.
Qed.

(* comparison 变元上的反演（先于 a b 引入，避免项上 destruct 抽象歧义）。 *)
Lemma hst_compare_of_bool : forall c : comparison,
  (match c with Eq => true | _ => false end) = true -> c = Eq.
Proof.
  intros c H.
  destruct c.
  - reflexivity.
  - discriminate H.
  - discriminate H.
Qed.

(* 门二（反向）：QeqT 消出 Qcompare = Eq——hst_id_eq（id 系消去）。 *)
Lemma hst_compare_of_qeqT : forall a b : Q, hst_QeqT a b -> Qcompare a b = Eq.
Proof.
  intros a b H.
  apply hst_compare_of_bool.
  unfold hst_QeqT in H.
  exact (hst_id_eq H).
Qed.

(* QeqT ↔ Qeq 双门（Prop 脚手架位；语句面保持 Set）。 *)
Lemma hst_qeqT_imp_qeq : forall a b : Q, hst_QeqT a b -> a == b.
Proof.
  intros a b H.
  apply (proj2 (Qeq_alt a b)).
  apply hst_compare_of_qeqT.
  exact H.
Qed.

Lemma hst_qeqT_of_qeq : forall a b : Q, a == b -> hst_QeqT a b.
Proof.
  intros a b Hab.
  apply hst_qeqT_of_compare.
  apply (proj1 (Qeq_alt a b)).
  exact Hab.
Qed.

(* 叶位规则（D038 闭合定式）：纯 ring 恒等式叶一步入门。 *)
Ltac hst_ring := apply hst_qeqT_of_qeq; ring.

(* Set 面同余族：自反/对称/传递/加减乘（右偏/左偏运备）。 *)
Lemma hst_qeqT_refl : forall a : Q, hst_QeqT a a.
Proof.
  intros a.
  apply hst_qeqT_of_qeq.
  apply Qeq_refl.
Qed.

Lemma hst_qeqT_sym : forall a b : Q, hst_QeqT a b -> hst_QeqT b a.
Proof.
  intros a b H.
  apply hst_qeqT_of_qeq.
  apply (Qeq_sym a b).
  apply hst_qeqT_imp_qeq.
  exact H.
Qed.

Lemma hst_qeqT_trans : forall a b c : Q,
  hst_QeqT a b -> hst_QeqT b c -> hst_QeqT a c.
Proof.
  intros a b c H1 H2.
  assert (Hab : a == b) by (apply hst_qeqT_imp_qeq; exact H1).
  assert (Hbc : b == c) by (apply hst_qeqT_imp_qeq; exact H2).
  rewrite <- Hab in Hbc.
  apply hst_qeqT_of_qeq.
  exact Hbc.
Qed.

Lemma hst_qeqT_add : forall a b c d : Q,
  hst_QeqT a b -> hst_QeqT c d -> hst_QeqT (a + c) (b + d).
Proof.
  intros a b c d H1 H2.
  apply hst_qeqT_of_qeq.
  rewrite (hst_qeqT_imp_qeq a b H1).
  rewrite (hst_qeqT_imp_qeq c d H2).
  apply Qeq_refl.
Qed.

Lemma hst_qeqT_sub : forall a b c d : Q,
  hst_QeqT a b -> hst_QeqT c d -> hst_QeqT (a - c) (b - d).
Proof.
  intros a b c d H1 H2.
  apply hst_qeqT_of_qeq.
  rewrite (hst_qeqT_imp_qeq a b H1).
  rewrite (hst_qeqT_imp_qeq c d H2).
  apply Qeq_refl.
Qed.

Lemma hst_qeqT_mul : forall a b c d : Q,
  hst_QeqT a b -> hst_QeqT c d -> hst_QeqT (a * c) (b * d).
Proof.
  intros a b c d H1 H2.
  apply hst_qeqT_of_qeq.
  rewrite (hst_qeqT_imp_qeq a b H1).
  rewrite (hst_qeqT_imp_qeq c d H2).
  apply Qeq_refl.
Qed.

Lemma hst_qeqT_add_r : forall a c d : Q,
  hst_QeqT c d -> hst_QeqT (a + c) (a + d).
Proof.
  intros a c d H.
  apply (hst_qeqT_add a a c d).
  - apply hst_qeqT_refl.
  - exact H.
Qed.

Lemma hst_qeqT_add_l : forall a b c : Q,
  hst_QeqT a b -> hst_QeqT (a + c) (b + c).
Proof.
  intros a b c H.
  apply (hst_qeqT_add a b c c).
  - exact H.
  - apply hst_qeqT_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 1.  求值和结构位（Prop 根②）：逐点律 Set 载体化。            *)
(* 归纳全部在 Set 面原生重证；算术叶位走 hst_ring。                     *)
(* ------------------------------------------------------------------ *)

(* 逐点加法求值（qpoly_eval_add 的 Set 面）。 *)
Lemma hst_eval_add_T : forall p q x,
  hst_QeqT (qpoly_eval (qpoly_add p q) x)
           (qpoly_eval p x + qpoly_eval q x).
Proof.
  induction p as [|a p IH]; intros q x.
  - destruct q as [|b q'].
    + cbn [qpoly_add qpoly_eval]. hst_ring.
    + cbn [qpoly_add qpoly_eval]. hst_ring.
  - destruct q as [|b q'].
    + cbn [qpoly_add qpoly_eval]. hst_ring.
    + replace (qpoly_add (cons a p) (cons b q'))
        with (cons (a + b) (qpoly_add p q')) by reflexivity.
      cbn [qpoly_eval].
      eapply hst_qeqT_trans.
      * apply hst_qeqT_add.
        -- apply hst_qeqT_refl.
        -- apply hst_qeqT_mul.
           ++ apply hst_qeqT_refl.
           ++ apply (IH q' x).
      * hst_ring.
Qed.

(* 求值和的单步展开（定义性，cbn 后两侧语法同形）。 *)
Lemma hst_qsum0_succ_T : forall (F : nat -> Q) n,
  hst_QeqT (lw2_qsum0 F (S n)) (lw2_qsum0 F n + F n).
Proof.
  intros F n.
  cbn [lw2_qsum0].
  apply hst_qeqT_refl.
Qed.

(* 求和逐点加法律（lw2_qsum0_add 的 Set 面，归纳在 Set 面）。 *)
Lemma hst_qsum0_add_T : forall n (g h : nat -> Q),
  hst_QeqT (lw2_qsum0 (fun j => g j + h j) n)
           (lw2_qsum0 g n + lw2_qsum0 h n).
Proof.
  intros n g h.
  induction n as [|n IH].
  - cbn [lw2_qsum0]. hst_ring.
  - cbn [lw2_qsum0].
    eapply hst_qeqT_trans.
    + apply hst_qeqT_add.
      * exact IH.
      * apply hst_qeqT_refl.
    + hst_ring.
Qed.

(* 求和逐点外延律（lw2_qsum0_ext 的 Set 面；逐点前提即 QeqT 载体形）。 *)
Lemma hst_qsum0_ext_T : forall n (g h : nat -> Q),
  (forall j, (j < n)%nat -> hst_QeqT (g j) (h j)) ->
  hst_QeqT (lw2_qsum0 g n) (lw2_qsum0 h n).
Proof.
  intros n g h.
  induction n as [|n IH]; intros H.
  - cbn [lw2_qsum0]. apply hst_qeqT_refl.
  - cbn [lw2_qsum0].
    apply hst_qeqT_add.
    + apply IH.
      intros j Hj.
      apply H.
      lia.
    + apply (H n). apply Nat.lt_succ_diag_r.
Qed.

(* 求和移位律（lw2_qsum0_shift 的 Set 面）：sum g(S·) = sum g − g0 + g n。 *)
Lemma hst_qsum0_shift_T : forall n (g : nat -> Q),
  hst_QeqT (lw2_qsum0 (fun k => g (S k)) n)
           (lw2_qsum0 g n - g (0%nat) + g n).
Proof.
  intros n g.
  induction n as [|n IH].
  - cbn [lw2_qsum0]. hst_ring.
  - cbn [lw2_qsum0].
    apply (hst_qeqT_trans
             (lw2_qsum0 (fun k => g (S k)) n + g (S n))%Q
             (lw2_qsum0 g n - g (0%nat) + g n + g (S n))%Q
             (lw2_qsum0 g n + g n - g (0%nat) + g (S n))%Q).
    + apply hst_qeqT_add.
      * exact IH.
      * apply hst_qeqT_refl.
    + hst_ring.
Qed.

(* eps 表求值和（lw2_eps_eval_sum 的 Set 面）：eps K f 的求值              *)
(* = sum_{k<K} f^{(k)}——核恒等式的求值和结构位。                           *)
Lemma hst_eps_eval_sum_T : forall K f x,
  hst_QeqT (qpoly_eval (lw2_eps K f) x)
           (lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) x) K).
Proof.
  intros K f x.
  induction K as [|K IH].
  - cbn [lw2_eps qpoly_eval lw2_qsum0]. apply hst_qeqT_refl.
  - cbn [lw2_eps].
    eapply hst_qeqT_trans.
    + apply hst_eval_add_T.
    + eapply hst_qeqT_trans.
      * apply hst_qeqT_add.
        -- apply hst_qeqT_refl.
        -- exact IH.
      * change (lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) x) (S K))
          with (lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter k f) x) K
                + qpoly_eval (qpoly_deriv_iter K f) x)%Q.
        hst_ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 2.  核恒等式锚（Prop 根①）：eps 的导数和 / 核方程 Set 面。    *)
(* ------------------------------------------------------------------ *)

(* eps 表导数和（lw2_eps_deriv_sum 的 Set 面）：eps K f 的导数求值          *)
(* = sum_{k<K} f^{(k+1)}。归纳在 Set 面；导数交互位经 Qeq 面绿件叶位入门。  *)
Lemma hst_eps_deriv_sum_T : forall K f x,
  hst_QeqT (qpoly_eval (qpoly_deriv (lw2_eps K f)) x)
           (lw2_qsum0 (fun k => qpoly_eval (qpoly_deriv_iter (S k) f) x) K).
Proof.
  intros K f x.
  induction K as [|K IH].
  - cbn [lw2_eps qpoly_deriv qpoly_eval lw2_qsum0]. apply hst_qeqT_refl.
  - cbn [lw2_eps].
    eapply hst_qeqT_trans.
    + (* 叶位：qpoly_eval_deriv_add + qpoly_eval_add（Qeq 面绿件，D038 降档） *)
      apply hst_qeqT_of_qeq.
      rewrite (qpoly_eval_deriv_add (qpoly_deriv_iter K f) (lw2_eps K f) x).
      apply (qpoly_eval_add (qpoly_deriv (qpoly_deriv_iter K f))
                            (qpoly_deriv (lw2_eps K f)) x).
    + rewrite <- (qpoly_deriv_iter_succ K f).
      cbn [lw2_qsum0].
      eapply hst_qeqT_trans.
      * apply hst_qeqT_add_r.
        exact IH.
      * hst_ring.
Qed.

(* 锚：核恒等式 Set 载体形——eps K f 满足核方程                             *)
(*   (eps K f)' == eps K f − f（length f ≤ K）。                           *)
(* 组装全在 Set 面：HA（导数和）→ HC（移位）→ 同余运输（HE0/HD）→ Hsw      *)
(* （求值和回 eps，经 hst_qeqT_sym/hst_qeqT_sub）。                        *)
Theorem hst_eps_deriv_kernel : forall K f x,
  (length f <= K)%nat ->
  hst_QeqT (qpoly_eval (qpoly_deriv (lw2_eps K f)) x)
           (qpoly_eval (lw2_eps K f) x - qpoly_eval f x).
Proof.
  intros K f x HN.
  assert (HA := hst_eps_deriv_sum_T K f x).
  assert (HB := hst_eps_eval_sum_T K f x).
  assert (HC := hst_qsum0_shift_T K (fun j => qpoly_eval (qpoly_deriv_iter j f) x)).
  assert (HE0 : hst_QeqT (qpoly_eval (qpoly_deriv_iter 0 f) x) (qpoly_eval f x)).
  { apply hst_qeqT_of_qeq. reflexivity. }
  (* 尾零位（叶位）：f^{(K)} 在 length f ≤ K 时求值为零——源机 Qeq 面绿件入门。 *)
  assert (HD : hst_QeqT (qpoly_eval (qpoly_deriv_iter K f) x) 0%Q).
  { apply hst_qeqT_of_qeq.
    apply (lw2_deriv_iter_zero_eval K f x HN). }
  (* 求值和回 eps 表（HB 对称入减法左元）。 *)
  assert (Hsw : hst_QeqT (lw2_qsum0 (fun j => qpoly_eval (qpoly_deriv_iter j f) x) K
                          - qpoly_eval f x)
                         (qpoly_eval (lw2_eps K f) x - qpoly_eval f x)).
  { apply hst_qeqT_sub.
    - apply hst_qeqT_sym. exact HB.
    - apply hst_qeqT_refl. }
  (* Set 面组装链：HA → HC → 同余运输（HE0/HD）→ 去零项 → Hsw。 *)
  eapply hst_qeqT_trans.
  { exact HA. }
  { eapply hst_qeqT_trans.
    { exact HC. }
    { eapply hst_qeqT_trans.
      { apply hst_qeqT_add.
        { apply hst_qeqT_sub.
          { apply hst_qeqT_refl. }
          { exact HE0. } }
        { exact HD. } }
      { apply (hst_qeqT_trans
                 ((lw2_qsum0 (fun j => qpoly_eval (qpoly_deriv_iter j f) x) K
                   - qpoly_eval f x) + 0)%Q
                 (lw2_qsum0 (fun j => qpoly_eval (qpoly_deriv_iter j f) x) K
                  - qpoly_eval f x)%Q
                 (qpoly_eval (lw2_eps K f) x - qpoly_eval f x)%Q).
        { hst_ring. }
        { exact Hsw. } } } }
Qed.

(* 精确核恒等式（零前提位，源 §11 lw2i_eps_exact 的 Set 重述）：            *)
(*   (eps K f)' == eps K f − f + f^{(K)}，对一切 K 无条件。                 *)
Theorem hst_eps_exact : forall K f x,
  hst_QeqT (qpoly_eval (qpoly_deriv (lw2_eps K f)) x)
           (qpoly_eval (lw2_eps K f) x - qpoly_eval f x
            + qpoly_eval (qpoly_deriv_iter K f) x).
Proof.
  intros K f x.
  assert (HA := hst_eps_deriv_sum_T K f x).
  assert (HB := hst_eps_eval_sum_T K f x).
  assert (HC := hst_qsum0_shift_T K (fun j => qpoly_eval (qpoly_deriv_iter j f) x)).
  assert (HE0 : hst_QeqT (qpoly_eval (qpoly_deriv_iter 0 f) x) (qpoly_eval f x))
    by (apply hst_qeqT_of_qeq; reflexivity).
  assert (Hsw : hst_QeqT (lw2_qsum0 (fun j => qpoly_eval (qpoly_deriv_iter j f) x) K
                          - qpoly_eval f x)
                         (qpoly_eval (lw2_eps K f) x - qpoly_eval f x)).
  { apply hst_qeqT_sub.
    - apply hst_qeqT_sym. exact HB.
    - apply hst_qeqT_refl. }
  eapply hst_qeqT_trans.
  { exact HA. }
  { eapply hst_qeqT_trans.
    { exact HC. }
    { eapply hst_qeqT_trans.
      { apply hst_qeqT_add_l.
        { apply hst_qeqT_sub.
          { apply hst_qeqT_refl. }
          { exact HE0. } } }
      { apply hst_qeqT_add_l.
        exact Hsw. } } }
Qed.

(* ------------------------------------------------------------------ *)
(* Section 3.  形式导数交互位（Prop 根③）——接口登记（不施工，           *)
(* 首件策略余量裁决；后续件按此签名对齐闭合）。                           *)
(* ------------------------------------------------------------------ *)

Definition hst_eval_di_add_face : Type :=
  forall k u v x,
    hst_QeqT (qpoly_eval (qpoly_deriv_iter k (qpoly_add u v)) x)
             (qpoly_eval (qpoly_deriv_iter k u) x
              + qpoly_eval (qpoly_deriv_iter k v) x).

Definition hst_trans_deriv_iter_eval_face : Type :=
  forall k f c x,
    hst_QeqT (qpoly_eval (qpoly_deriv_iter k (lw2_trans f c)) x)
             (qpoly_eval (qpoly_deriv_iter k f) (x + c)).

(* ------------------------------------------------------------------ *)
(* Section 4.  提取检验与假设检查（红线四条取证位）。                     *)
(* ------------------------------------------------------------------ *)

From Stdlib Require Import Extraction.
Separate Extraction hst_eps_deriv_kernel hst_eps_exact hst_eps_eval_sum_T
  hst_eps_deriv_sum_T hst_qsum0_shift_T hst_qsum0_ext_T hst_eval_add_T.

Print Assumptions hst_eps_deriv_kernel.
Print Assumptions hst_eps_exact.
Print Assumptions hst_eps_eval_sum_T.
Print Assumptions hst_eps_deriv_sum_T.
Print Assumptions hst_qsum0_ext_T.
Print Assumptions hst_eval_add_T.
