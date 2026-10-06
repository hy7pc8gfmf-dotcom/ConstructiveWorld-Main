(* ===================================================================== *)
(*  五字段指针｜使命：Q 多项式带余除法【一般形】引擎——ln2 路线③第二段      *)
(*    （CK）。闭合件 CC 登记的接口 qpd_divmod_gen_type：任意次数除数     *)
(*    （真首项非零＋度≥1）的长除法构造性版。依赖：Stdlib QArith/Qring/      *)
(*    Qfield/List/Arith/ZArith/Lia/Extraction；S01_BaseRing                *)
(*    S02_CauchyComplete PolyIntegral（池外世界树在册件）；前件             *)
(*    abl_qpoly_divmod（池内 CC 首件，使用其 qpd_divmod_gen_pred/type       *)
(*    容器与 qpd_eval_add/qpd_eval_cons/qpd_deglt 度肢）。 构造性：纯构造   *)
(*    性、零承认件；语句面全 Set（sigT＋S01.And＋S02.QeqT＋S01.Id 面），   *)
(*    Qeq==仅证内推理脚手架；环闭全走「全变量形纯环小件」模式（坑卡         *)
(*    AL/AX，前件 §1 同款）。 编译配方：source Live/toolchain/env.sh &&    *)
(*    unset COQLIB ROCQLIB && ulimit -s 65532 && nice -19 rocq c           *)
(*    -native-compiler no -Q vo_local_world_unified_0930 ""                *)
(*    abl_qpoly_divmod_gen.v（先编前件 abl_qpoly_divmod.v；道闸≤1＝单进程  *)
(*    串行）。 对标：CC abl_qpoly_divmod（线性综合除法首件）；PolyIntegral  *)
(*    pint_*（Q 系数列表先例）；BT §诚实边界路线③；AE §3.3 路线③。        *)
(* ===================================================================== *)
(*  abl_qpoly_divmod_gen.v —— Q 层多项式除法引擎·一般形（第二段）           *)
(*                                                                        *)
(*  使命：闭合 CC 登记的 qpd_divmod_gen_type p q 容器（照用其形状：         *)
(*    sigT 封装（商表, 余表）＋双正确性肢                                  *)
(*      ①等式肢 ∀x, QeqT (eval p x) (eval q x · eval 商 x + eval 余 x)      *)
(*      ②度肢   qpd_deglt 余 q（Id bool 可判定面）                          *)
(*    交付 qpg_divmod_gen : forall p q, qpg_divisor_ok q ->                *)
(*                            qpd_divmod_gen_type p q。                    *)
(*                                                                        *)
(*  路线（经典长除法构造性版）：按首项系数消去递归——                       *)
(*    商系数 c = lead p / lead q（Q 层 Qdiv，在册）；p − c·x^k·q 顶位相消   *)
(*    归零，截去顶位得 p1，deg p1 = deg p − 1 严格递减；燃料 = length p，   *)
(*    真结构 Fixpoint（nat 燃料递归，非平凡算法体，可提取）。终止性＝长度   *)
(*    度量；正确性＝归纳步环等式（全变量形纯环小件直取）。                 *)
(*                                                                        *)
(*  与 CC 接口 diff（诚实边界）：除数前提升为 qpg_divisor_ok q ＝           *)
(*    ①deg q ≥ 1（Id bool 面：ltb 0 (deg q) = true——度肢自动排除常除数）  *)
(*    ②lead q ≠ 0（Qcompare Set 面：真首项非零）。理由：头=常数项稠密表    *)
(*    下 listdeg ≠ 真度（尾零例 q=[1;2;0] listdeg=2 而真度=1，lead=0），   *)
(*    首项消去须真首项非零方可除；任务指令「deg q ≥ 1」单前提对本引擎不足，  *)
(*    此为表示法层面诚实扩题，容器面与 CC 登记零改动。                     *)
(*                                                                        *)
(*  首件策略（45 分钟切片）：本件闭合「递归引擎＋存在性肢」；唯一性肢       *)
(*    （商余唯一）§5 只登记不施工。                                        *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qfield.
From Stdlib Require Import Lists.List Arith.Arith ZArith.ZArith Lia Extraction.
Import ListNotations.
Require Import S01_BaseRing S02_CauchyComplete PolyIntegral abl_qpoly_divmod.

Open Scope Q_scope.

(* ============================================================ *)
(* §0 除子良态面与前件使用件（全 Set 面；Qeq/Prop 仅证内）         *)
(* ============================================================ *)

(* 度 ≥ 1 的 Id bool 可判定面（与前件 qpd_deglt 同款） *)
Definition qpg_degge1 (q : list Q) : Set :=
  @Id bool true (Nat.ltb 0 (qpd_deg q)).

(* 真首项非零的 Qcompare Set 面（Eq 分支不可 inhabited 即「非零」） *)
Definition qpg_leadne0 (q : list Q) : Set :=
  match Qcompare (qpd_lead q) 0 with
  | Datatypes.Eq => Empty_set
  | Datatypes.Lt => unit
  | Datatypes.Gt => unit
  end.

(* 除子良态＝度≥1 ∧ 真首项非零（S01.Set 级 And） *)
Definition qpg_divisor_ok (q : list Q) : Set :=
  And (qpg_degge1 q) (qpg_leadne0 q).

(* Id bool 面使用：由 Id true b 取布尔等式 *)
Lemma qpg_id_true_inv : forall b : bool, @Id bool true b -> b = true.
Proof. intros b H. destruct H. reflexivity. Qed.

Lemma qpg_degge1_inv : forall q : list Q,
  qpg_degge1 q -> Nat.ltb 0 (qpd_deg q) = true.
Proof. intros q H. exact (qpg_id_true_inv _ H). Qed.

Lemma qpg_leadne0_inv : forall q : list Q,
  qpg_leadne0 q -> ~ (qpd_lead q == 0).
Proof.
  intros q H Hz. unfold qpg_leadne0 in H.
  assert (Hc : Qcompare (qpd_lead q) 0 = Datatypes.Eq).
  { apply (proj1 (Qeq_alt (qpd_lead q) 0)). exact Hz. }
  rewrite Hc in H. inversion H.
Qed.

(* §1 前置两只（qpg_div_cancel 依赖，全变量形纯环小件） *)
Lemma qpg_ring_assoc : forall w i v : Q, w * i * v == w * (i * v).
Proof. intros w i v. ring. Qed.

Lemma qpg_ring_mul1 : forall a : Q, a * 1 == a.
Proof. intros a. ring. Qed.

(* Q 层除法消去（Qdiv 在册）：b ≠ 0 时 a/b·b == a *)
Lemma qpg_div_cancel : forall a b : Q, ~ b == 0 -> a / b * b == a.
Proof.
  intros a b Hb. unfold Qdiv.
  assert (H1 : b * (/ b) == 1) by exact (Qmult_inv_r b Hb).
  assert (H2 : (/ b) * b == 1)
    by exact (Qeq_trans _ _ _ (Qmult_comm (/ b) b) H1).
  assert (H3 : a * (/ b) * b == a * ((/ b) * b))
    by exact (qpg_ring_assoc a (/ b) b).
  rewrite H2 in H3.
  exact (Qeq_trans _ _ _ H3 (qpg_ring_mul1 a)).
Qed.

(* 消去位归零：a − a/b·b == 0 *)
Lemma qpg_lead_cancel : forall a b : Q, ~ b == 0 -> a - a / b * b == 0.
Proof.
  intros a b Hb. rewrite (qpg_div_cancel a b Hb). ring.
Qed.

(* ============================================================ *)
(* §1 全变量形纯环小件组（坑卡 AL/AX 模式：环闭原子全为变量，      *)
(*    调用位以复合项直取代参；assoc/mul1 两只前置 §0）             *)
(* ============================================================ *)

Lemma qpg_ring_leaf : forall e : Q, 0 == e * 0 + 0.
Proof. intros e. ring. Qed.

Lemma qpg_ring_lt : forall h t e : Q, h + t == e * 0 + (h + t).
Proof. intros h t e. ring. Qed.

Lemma qpg_ring_remlast0 : forall e f : Q, e == e + f * 0.
Proof. intros e f. ring. Qed.

Lemma qpg_ring_align0 : forall e c : Q, e == e - c * 0.
Proof. intros e c. ring. Qed.

Lemma qpg_ring_align : forall h c q x e1 e2 : Q,
  (h - c * q) + x * (e1 - c * e2) == (h + x * e1) - c * (q + x * e2).
Proof. intros h c q x e1 e2. ring. Qed.

Lemma qpg_ring_shift0 : forall e c d : Q, e - c * d == e - 1 * (c * d).
Proof. intros e c d. ring. Qed.

Lemma qpg_ring_shift : forall h x e1 p c d : Q,
  h + x * (e1 - p * (c * d)) == (h + x * e1) - (x * p) * (c * d).
Proof. intros h x e1 p c d. ring. Qed.

Lemma qpg_ring_mono0 : forall c x : Q, c + x * 0 == 1 * c.
Proof. intros c x. ring. Qed.

Lemma qpg_ring_monoS : forall x p c : Q, 0 + x * (p * c) == x * p * c.
Proof. intros x p c. ring. Qed.

Lemma qpg_ring_main : forall w c d s r : Q,
  w * (c * d) + (d * s + r) == d * (w * c + s) + r.
Proof. intros w c d s r. ring. Qed.

Lemma qpg_ring_shift_edge : forall h x c : Q,
  h + x * 0 == (h + x * 0) - x * 1 * (c * 0).
Proof. intros h x c. ring. Qed.

(* Qeq 迁移：b == a − x ⟹ a == x + b *)
Lemma qpg_qeq_move : forall a b x : Q, b == a - x -> a == x + b.
Proof. intros a b x H. rewrite H. ring. Qed.

(* 烟测配套：(x²+2x+1) ÷ (x+1) 求值恒等式 *)
Lemma qpg_ring_smokeA : forall x : Q,
  1 + x * (2 + x * (1 + x * 0))
  == (1 + x * (1 + x * 0)) * (1 + x * (1 + x * 0)) + (0 + x * 0).
Proof. intros x. ring. Qed.

(* ============================================================ *)
(* §2 基础表运算：幂、零段、单项、去尾（皆真 Fixpoint，可提取）    *)
(* ============================================================ *)

Fixpoint qpg_pow (x : Q) (k : nat) : Q :=
  match k with
  | 0%nat => 1
  | Datatypes.S k' => x * qpg_pow x k'
  end.

Fixpoint qpg_zeros (k : nat) : list Q :=
  match k with
  | 0%nat => []
  | Datatypes.S k' => 0 :: qpg_zeros k'
  end.

(* 单项 c·x^k 的系数表：k 个 0 接一个 c *)
Definition qpg_mono (c : Q) (k : nat) : list Q := qpg_zeros k ++ c :: nil.

(* 去尾（截去最高次位；稠密表头=常数项，最高次位在表尾） *)
Fixpoint qpg_remlast (p : list Q) : list Q :=
  match p with
  | [] => []
  | a :: p' =>
      match p' with
      | [] => []
      | _ :: _ => a :: qpg_remlast p'
      end
  end.

(* 二层 cons 的去尾定义性方程（证明内防 cbn 过展递归位） *)
Lemma qpg_remlast_cons2 : forall (a b : Q) (L : list Q),
  qpg_remlast (a :: b :: L) = a :: qpg_remlast (b :: L).
Proof. intros a b L. reflexivity. Qed.

Lemma qpg_eval_mono : forall (k : nat) (c x : Q),
  pint_eval (qpg_mono c k) x == qpg_pow x k * c.
Proof.
  unfold qpg_mono. induction k as [|k' IH]; intros c x.
  - cbn [qpg_zeros app pint_eval qpg_pow]. exact (qpg_ring_mono0 c x).
  - cbn [qpg_zeros app pint_eval qpg_pow]. rewrite (IH c x).
    exact (qpg_ring_monoS x (qpg_pow x k') c).
Qed.

Lemma qpg_remlast_length : forall p : list Q,
  length (qpg_remlast p) = Nat.pred (length p).
Proof.
  induction p as [|a p' IH].
  - reflexivity.
  - destruct p' as [|b p''].
    + reflexivity.
    + rewrite (qpg_remlast_cons2 a b p''). cbn [length].
      rewrite IH. reflexivity.
Qed.

(* 非空尾的表，去一位后首项系数不变（度账与求值账的对齐件） *)
Lemma qpg_lead_cons_ne : forall (a : Q) (rest : list Q),
  rest <> [] -> qpd_lead (a :: rest) == qpd_lead rest.
Proof.
  intros a rest Hne. destruct rest as [|b rest'].
  - exfalso. apply Hne. reflexivity.
  - cbn [qpd_lead pint_coeff length pred]. apply Qeq_refl.
Qed.

(* 首项系数为零的表，截尾不改求值（消去步顶位归零的求值面） *)
Lemma qpg_eval_remlast0 : forall (p : list Q) (x : Q),
  qpd_lead p == 0 -> pint_eval (qpg_remlast p) x == pint_eval p x.
Proof.
  induction p as [|a p' IH]; intros x H.
  - cbn [qpg_remlast pint_eval]. apply Qeq_refl.
  - destruct p' as [|b p''].
    + cbn [qpd_lead pint_coeff length pred] in H.
      cbn [qpg_remlast pint_eval]. rewrite H.
      exact (qpg_ring_remlast0 0 x).
    + assert (Hne : b :: p'' <> []) by discriminate.
      assert (H2 : qpd_lead (b :: p'') == 0).
      { exact (Qeq_trans _ _ _ (Qeq_sym _ _ (qpg_lead_cons_ne a (b :: p'') Hne)) H). }
      rewrite (qpg_remlast_cons2 a b p''). cbn [pint_eval].
      rewrite (IH x H2). apply Qeq_refl.
Qed.

(* ============================================================ *)
(* §3 消去步：qpg_align_sub（对位减 c·q）与 qpg_shift_sub（升位）  *)
(*    头=常数项表示下，q 的头位对齐 p 的第 k 位（x^k·q 展开）      *)
(* ============================================================ *)

Fixpoint qpg_align_sub (c : Q) (q p : list Q) : list Q :=
  match q with
  | [] => p
  | qh :: qt =>
      match p with
      | [] => []
      | ph :: pt => (ph - c * qh) :: qpg_align_sub c qt pt
      end
  end.

Fixpoint qpg_shift_sub (c : Q) (k : nat) (q p : list Q) : list Q :=
  match k with
  | 0%nat => qpg_align_sub c q p
  | Datatypes.S k' =>
      match p with
      | [] => []
      | ph :: pt => ph :: qpg_shift_sub c k' q pt
      end
  end.

Lemma qpg_length_align : forall (c : Q) (q p : list Q),
  (length q <= length p)%nat -> length (qpg_align_sub c q p) = length p.
Proof.
  intros c q. induction q as [|qh qt IH]; intros p H.
  - reflexivity.
  - destruct p as [|ph pt].
    + cbn [length] in H. lia.
    + cbn [length] in H.
      assert (H2 : (length qt <= length pt)%nat) by lia.
      cbn [qpg_align_sub length]. rewrite (IH pt H2). reflexivity.
Qed.

Lemma qpg_length_shift : forall (c : Q) (k : nat) (q p : list Q),
  (k + length q <= length p)%nat -> length (qpg_shift_sub c k q p) = length p.
Proof.
  intros c k. induction k as [|k' IH]; intros q p H.
  - cbn [qpg_shift_sub]. apply (qpg_length_align c q p). exact H.
  - destruct p as [|ph pt].
    + cbn [length] in H. lia.
    + destruct pt as [|b pt'].
      * cbn [length] in H.
        assert (H0 : (k' + length q <= 0)%nat) by lia.
        destruct k' as [|k''].
        -- assert (Hq0 : (length q = 0)%nat) by lia.
           destruct q as [|q1 q2].
           ++ cbn [qpg_shift_sub qpg_align_sub length]. reflexivity.
           ++ cbn [length] in Hq0. discriminate Hq0.
        -- exfalso. lia.
      * cbn [length] in H.
        assert (H2 : (k' + length q <= Datatypes.S (length pt'))%nat) by lia.
        cbn [qpg_shift_sub length]. rewrite (IH q (b :: pt') H2). reflexivity.
Qed.

(* 对位减的求值语义：eval (p − c·q) == eval p − c·eval q *)
Lemma qpg_eval_align : forall (c : Q) (q p : list Q) (x : Q),
  (length q <= length p)%nat ->
  pint_eval (qpg_align_sub c q p) x == pint_eval p x - c * pint_eval q x.
Proof.
  intros c q. induction q as [|qh qt IH]; intros p x H.
  - cbn [qpg_align_sub]. exact (qpg_ring_align0 (pint_eval p x) c).
  - destruct p as [|ph pt].
    + cbn [length] in H. lia.
    + cbn [length] in H.
      assert (H2 : (length qt <= length pt)%nat) by lia.
      cbn [qpg_align_sub pint_eval]. rewrite (IH pt x H2).
      exact (qpg_ring_align ph c qh x (pint_eval pt x) (pint_eval qt x)).
Qed.

(* 升位减的求值语义：eval (p − c·x^k·q) == eval p − x^k·(c·eval q) *)
Lemma qpg_eval_shift : forall (c : Q) (k : nat) (q p : list Q) (x : Q),
  (k + length q <= length p)%nat ->
  pint_eval (qpg_shift_sub c k q p) x
  == pint_eval p x - qpg_pow x k * (c * pint_eval q x).
Proof.
  intros c k. induction k as [|k' IH]; intros q p x H.
  - assert (H0 : (length q <= length p)%nat) by lia.
    cbn [qpg_shift_sub qpg_pow]. rewrite (qpg_eval_align c q p x H0).
    apply (qpg_ring_shift0 (pint_eval p x) c (pint_eval q x)).
  - destruct p as [|ph pt].
    + cbn [length] in H. lia.
    + destruct pt as [|b pt'].
      * cbn [length] in H.
        assert (H0 : (k' + length q <= 0)%nat) by lia.
        destruct k' as [|k''].
        -- assert (Hq0 : (length q = 0)%nat) by lia.
           destruct q as [|q1 q2].
           ++ cbn [qpg_shift_sub qpg_align_sub qpg_pow pint_eval].
              apply (qpg_ring_shift_edge ph x c).
           ++ cbn [length] in Hq0. discriminate Hq0.
        -- exfalso. lia.
      * cbn [length] in H.
        assert (H2 : (k' + length q <= Datatypes.S (length pt'))%nat) by lia.
        cbn [qpg_shift_sub qpg_pow pint_eval]. rewrite (IH q (b :: pt') x H2).
        exact (qpg_ring_shift ph x (pint_eval (b :: pt') x) (qpg_pow x k') c
                             (pint_eval q x)).
Qed.

(* 非空表的长度-度换算（引擎等式账用） *)
Lemma qpg_length_deg : forall q : list Q,
  q <> [] -> (length q = Datatypes.S (qpd_deg q))%nat.
Proof.
  intros q Hne. destruct q as [|q1 q2].
  - exfalso. apply Hne. reflexivity.
  - cbn [qpd_deg length pred]. reflexivity.
Qed.

(* 对位减的首项账（顶位对齐版：length q = length p 时 q 的首项恰配 p 的
   首项）：lead (p − c·q) == lead p − c·lead q *)
Lemma qpg_lead_align : forall (c : Q) (q p : list Q),
  (length q = length p)%nat ->
  qpd_lead (qpg_align_sub c q p) == qpd_lead p - c * qpd_lead q.
Proof.
  intros c q. induction q as [|qh qt IH]; intros p H.
  - destruct p as [|ph pt].
    + cbn [qpg_align_sub qpd_lead pint_coeff length pred].
      exact (qpg_ring_align0 0 c).
    + cbn [length] in H. lia.
  - destruct p as [|ph pt].
    + cbn [length] in H. lia.
    + cbn [length] in H.
      assert (H2 : (length qt = length pt)%nat) by lia.
      destruct qt as [|a qt'].
      * (* qt = []，长度相等迫 pt = [] *)
        destruct pt as [|b pt'].
        -- cbn [qpg_align_sub qpd_lead pint_coeff length pred]. apply Qeq_refl.
        -- cbn [length] in H. lia.
      * destruct pt as [|b pt'].
        -- cbn [length] in H. lia.
        -- assert (Hne1 : b :: pt' <> []) by discriminate.
           assert (Hne2 : a :: qt' <> []) by discriminate.
           assert (Hne3 : qpg_align_sub c (a :: qt') (b :: pt') <> []).
           { intro E0.
             assert (Hlen : length (qpg_align_sub c (a :: qt') (b :: pt')) = length (b :: pt'))
               by (apply (qpg_length_align c (a :: qt') (b :: pt')); lia).
             rewrite E0 in Hlen. cbn [length] in Hlen. discriminate Hlen. }
           cbn [qpg_align_sub].
           rewrite (qpg_lead_cons_ne (ph - c * qh) (qpg_align_sub c (a :: qt') (b :: pt')) Hne3).
           rewrite (IH (b :: pt') H2).
           rewrite (qpg_lead_cons_ne ph (b :: pt') Hne1).
           rewrite (qpg_lead_cons_ne qh (a :: qt') Hne2).
           apply Qeq_refl.
Qed.

(* 升位减的首项账（等式版：length p = k + length q，顶位恰被消去位）：
   lead (p − c·x^k·q) == lead p − c·lead q（顶位归零之源） *)
Lemma qpg_lead_shift : forall (c : Q) (k : nat) (q p : list Q),
  (k + length q = length p)%nat ->
  qpd_lead (qpg_shift_sub c k q p) == qpd_lead p - c * qpd_lead q.
Proof.
  intros c k. induction k as [|k' IH]; intros q p H.
  - cbn [qpg_shift_sub]. apply (qpg_lead_align c q p). exact H.
  - destruct p as [|ph pt].
    + cbn [length] in H. lia.
    + destruct pt as [|b pt'].
      * (* pt = []：迫 k' = 0 ∧ q = []，升位减退化为单元素表 *)
        cbn [length] in H.
        assert (H0 : (k' + length q = 0)%nat) by lia.
        destruct k' as [|k''].
        -- assert (Hq0 : (length q = 0)%nat) by lia.
           destruct q as [|q1 q2].
           ++ cbn [qpg_shift_sub qpg_align_sub qpd_lead pint_coeff length pred].
              apply (qpg_ring_align0 ph c).
           ++ cbn [length] in Hq0. discriminate Hq0.
        -- exfalso. lia.
      * cbn [length] in H.
        assert (H2 : (k' + length q = Datatypes.S (length pt'))%nat) by lia.
        assert (H2le : (k' + length q <= Datatypes.S (length pt'))%nat) by lia.
        assert (Hne1 : b :: pt' <> []) by discriminate.
        assert (Hne2 : qpg_shift_sub c k' q (b :: pt') <> []).
        { intro E0.
          assert (Hlen : length (qpg_shift_sub c k' q (b :: pt')) = length (b :: pt'))
            by exact (qpg_length_shift c k' q (b :: pt') H2le).
          rewrite E0 in Hlen. cbn [length] in Hlen. discriminate Hlen. }
        cbn [qpg_shift_sub].
        rewrite (qpg_lead_cons_ne ph (qpg_shift_sub c k' q (b :: pt')) Hne2).
        rewrite (IH q (b :: pt') H2).
        rewrite (qpg_lead_cons_ne ph (b :: pt') Hne1).
        apply Qeq_refl.
Qed.

(* ============================================================ *)
(* §4 递归引擎（真 Fixpoint：nat 燃料结构递归）＋存在性肢＋顶层      *)
(*    不变式：p == q·s + r；每步余式长度严格减一（终止性度量）。    *)
(* ============================================================ *)

Fixpoint qpg_engine (fuel : nat) (q p : list Q) : list Q * list Q :=
  match fuel with
  | 0%nat => ([], p)
  | Datatypes.S f =>
      if Nat.ltb (qpd_deg p) (qpd_deg q) then ([], p)
      else
        let k := Nat.sub (qpd_deg p) (qpd_deg q) in
        let c := qpd_lead p / qpd_lead q in
        match qpg_engine f q (qpg_remlast (qpg_shift_sub c k q p)) with
        | (sq, rr) => (pint_add (qpg_mono c k) sq, rr)
        end
  end.

(* 存在性肢：燃料 = length p 时引擎产出满足 CC 登记的一般形双正确性肢 *)
Lemma qpg_engine_sound : forall (fuel : nat) (q p : list Q),
  qpg_divisor_ok q -> (length p <= fuel)%nat ->
  qpd_divmod_gen_pred p q (qpg_engine fuel q p).
Proof.
  induction fuel as [|f IH]; intros q p Hq Hlen.
  - (* 燃料尽：p 必空；0 == eval q·0 + 0，余 [] 度 0 < deg q（由 degge1） *)
    destruct p as [|a p'].
    + cbn [qpg_engine fst snd]. unfold qpd_divmod_gen_pred. cbn [fst snd]. split.
      * intros x. apply qeq_imp_qeqT. cbn [pint_eval].
        exact (qpg_ring_leaf (pint_eval q x)).
      * exact (fst Hq).
    + cbn [length] in Hlen. lia.
  - destruct p as [|a p'].
    + (* 空被除式：度肢条件 deg q ≥ 1 直取，走基例分支 *)
      destruct Hq as [Hd Hl].
      cbn [qpg_engine qpd_deg].
      rewrite (qpg_id_true_inv _ Hd). cbn [fst snd].
      unfold qpd_divmod_gen_pred. cbn [fst snd]. split.
      * intros x. apply qeq_imp_qeqT. cbn [pint_eval].
        exact (qpg_ring_leaf (pint_eval q x)).
      * exact Hd.
    + (* 主消去步：首项系数除法消顶位，余表长度严格减一 *)
      destruct Hq as [Hd Hl].
      cbn [qpg_engine].
      destruct (Nat.ltb (qpd_deg (a :: p')) (qpd_deg q)) eqn:E.
      * (* deg p < deg q：基例，商 0 余 p *)
        cbn [fst snd]. unfold qpd_divmod_gen_pred. cbn [fst snd]. split.
        -- intros x. apply qeq_imp_qeqT. cbn [pint_eval].
           exact (qpg_ring_lt a (x * pint_eval p' x) (pint_eval q x)).
        -- unfold qpd_deglt. rewrite E. exact id_refl.
      * (* deg q ≤ deg p：消去一步后递归 *)
        assert (Hge : (qpd_deg q <= qpd_deg (a :: p'))%nat)
          by (apply Nat.ltb_ge; exact E).
        assert (Hdp : qpd_deg (a :: p') = length p') by reflexivity.
        rewrite Hdp in Hge.
        remember (Nat.sub (qpd_deg (a :: p')) (qpd_deg q)) as k eqn:Hk.
        remember (qpd_lead (a :: p') / qpd_lead q) as c eqn:Hc.
        (* 长度账：k + length q ≤ length p（求值账用），且取等（首项账用） *)
        assert (Hd' : Nat.ltb 0 (qpd_deg q) = true)
          by exact (qpg_degge1_inv q Hd).
        assert (Hneq : q <> []).
        { intro E0. rewrite E0 in Hd'.
          cbn [qpd_deg Nat.ltb Nat.leb] in Hd'. discriminate Hd'. }
        assert (F1 : (k + length q <= length (a :: p'))%nat).
        { rewrite Hk, Hdp, (qpg_length_deg q Hneq). cbn [length]. lia. }
        assert (F1eq : (k + length q = length (a :: p'))%nat).
        { rewrite Hk, Hdp.
          assert (Hl1 : length (a :: p') = Datatypes.S (length p')) by reflexivity.
          rewrite Hl1, (qpg_length_deg q Hneq). lia. }
        assert (Hlen3 : (length (qpg_remlast (qpg_shift_sub c k q (a :: p'))) <= f)%nat).
        { rewrite (qpg_remlast_length _), (qpg_length_shift c k q (a :: p') F1).
          assert (Hl1 : length (a :: p') = Datatypes.S (length p')) by reflexivity.
          rewrite Hl1. cbn [Nat.pred]. cbn [length Nat.pred] in Hlen. lia. }
        (* 顶位归零：lead (升位减) == 0（Qdiv 消去在此进场） *)
        assert (Hlead0 : qpd_lead (qpg_shift_sub c k q (a :: p')) == 0).
        { rewrite (qpg_lead_shift c k q (a :: p') F1eq). rewrite Hc.
          exact (qpg_lead_cancel (qpd_lead (a :: p')) (qpd_lead q)
                                 (qpg_leadne0_inv q Hl)). }
        (* 递归内引擎解构与归纳肢 *)
        destruct (qpg_engine f q (qpg_remlast (qpg_shift_sub c k q (a :: p'))))
          as [sq rr] eqn:Eeng.
        specialize (IH q (qpg_remlast (qpg_shift_sub c k q (a :: p')))
                         (pair Hd Hl) Hlen3).
        rewrite Eeng in IH. unfold qpd_divmod_gen_pred in IH. cbn [fst snd] in IH.
        destruct IH as [IH1 IH2].
        (* 求值账：eval p == x^k·(c·eval q) + eval 余表 *)
        assert (Hev1 : forall x : Q,
          pint_eval (qpg_remlast (qpg_shift_sub c k q (a :: p'))) x
          == pint_eval (qpg_shift_sub c k q (a :: p')) x).
        { intros x0. apply qpg_eval_remlast0. exact Hlead0. }
        assert (Hev2 : forall x : Q,
          pint_eval (qpg_shift_sub c k q (a :: p')) x
          == pint_eval (a :: p') x - qpg_pow x k * (c * pint_eval q x)).
        { intros x0. exact (qpg_eval_shift c k q (a :: p') x0 F1). }
        assert (Hp : forall x : Q,
          pint_eval (a :: p') x
          == qpg_pow x k * (c * pint_eval q x)
             + pint_eval (qpg_remlast (qpg_shift_sub c k q (a :: p'))) x).
        { intros x0.
          apply (qpg_qeq_move (pint_eval (a :: p') x0)
                  (pint_eval (qpg_remlast (qpg_shift_sub c k q (a :: p'))) x0)
                  (qpg_pow x0 k * (c * pint_eval q x0))).
          exact (Qeq_trans _ _ _ (Hev1 x0) (Hev2 x0)). }
        assert (HIH : forall x : Q,
          pint_eval (qpg_remlast (qpg_shift_sub c k q (a :: p'))) x
          == pint_eval q x * pint_eval sq x + pint_eval rr x).
        { intros x0. exact (qeqT_imp_qeq _ _ (IH1 x0)). }
        unfold qpd_divmod_gen_pred. cbn [fst snd]. split.
        -- intros x. apply qeq_imp_qeqT.
           rewrite (Hp x), (HIH x), qpd_eval_add, qpg_eval_mono.
           exact (qpg_ring_main (qpg_pow x k) c (pint_eval q x) (pint_eval sq x)
                                (pint_eval rr x)).
        -- exact IH2.
Qed.

(* 顶层：CC 登记容器的一般形交付——任意次数除数（良态前提）带余除法 *)
Definition qpg_divmod_gen (p q : list Q) (Hq : qpg_divisor_ok q)
  : qpd_divmod_gen_type p q :=
  existT _ (qpg_engine (length p) q p)
           (qpg_engine_sound (length p) q p Hq (Nat.le_refl (length p))).

(* ============================================================ *)
(* §5 唯一性肢接口（只登记不施工——首件策略 45 分钟切片既定）       *)
(*    商余唯一：两分解均满足双正确性肢则商表/余表 Id 相等。        *)
(* ============================================================ *)

Definition qpg_gen_unique_type (p q : list Q) : Set :=
  forall (s r s' r' : list Q),
    And (qpd_divmod_gen_pred p q (s, r)) (qpd_divmod_gen_pred p q (s', r')) ->
    And (@Id (list Q) s s') (@Id (list Q) r r').

(* ============================================================ *)
(* §6 数值烟测（BF 模式：vm_compute 零公设定装，实例小形）         *)
(* ============================================================ *)

(* 除子良态见证：q = x+1（表 [1;1]）与 q = x+2（表 [2;1]） *)
Definition qpg_ok_xp1 : qpg_divisor_ok (1 :: 1 :: nil).
Proof.
  unfold qpg_divisor_ok. split.
  - unfold qpg_degge1. cbn [qpd_deg length pred Nat.ltb Nat.leb]. exact id_refl.
  - unfold qpg_leadne0. cbn [qpd_lead pint_coeff length pred Qcompare]. exact tt.
Defined.

Definition qpg_ok_xp2 : qpg_divisor_ok (2 :: 1 :: nil).
Proof.
  unfold qpg_divisor_ok. split.
  - unfold qpg_degge1. cbn [qpd_deg length pred Nat.ltb Nat.leb]. exact id_refl.
  - unfold qpg_leadne0. cbn [qpd_lead pint_coeff length pred Qcompare]. exact tt.
Defined.

(* 烟测 A（完全整除）：(x+1)² ÷ (x+1) ⟹ 商 [1;1]（=x+1）余 [0] *)
Lemma qpg_smokeA_q :
  fst (projT1 (qpg_divmod_gen (1 :: 2 :: 1 :: nil) (1 :: 1 :: nil) qpg_ok_xp1))
  = 1 :: 1 :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma qpg_smokeA_r :
  snd (projT1 (qpg_divmod_gen (1 :: 2 :: 1 :: nil) (1 :: 1 :: nil) qpg_ok_xp1))
  = 0 :: nil.
Proof. vm_compute. reflexivity. Qed.

(* 烟测 A 语义面：p == q·商 + 余 的 QeqT 全等式（含被除式求值） *)
Lemma qpg_smokeA_sem : forall x : Q,
  QeqT (pint_eval (1 :: 2 :: 1 :: nil) x)
       (pint_eval (1 :: 1 :: nil) x
          * pint_eval (fst (projT1 (qpg_divmod_gen (1 :: 2 :: 1 :: nil)
                                                   (1 :: 1 :: nil) qpg_ok_xp1))) x
        + pint_eval (snd (projT1 (qpg_divmod_gen (1 :: 2 :: 1 :: nil)
                                                 (1 :: 1 :: nil) qpg_ok_xp1))) x).
Proof.
  intros x. apply qeq_imp_qeqT.
  assert (Heng : projT1 (qpg_divmod_gen (1 :: 2 :: 1 :: nil) (1 :: 1 :: nil) qpg_ok_xp1)
                 = ((1 :: 1 :: nil), (0 :: nil)%list)) by (vm_compute; reflexivity).
  rewrite Heng. cbn [fst snd].
  rewrite qpd_eval_cons, qpd_eval_cons, qpd_eval_cons, qpd_eval_nil.
  apply (qpg_ring_smokeA x).
Qed.

(* 烟测 B（带余）：(x²+1) ÷ (x+2) ⟹ 商 [−2;1]（=x−2）余 [5] *)
Lemma qpg_smokeB_q :
  fst (projT1 (qpg_divmod_gen (1 :: 0 :: 1 :: nil) (2 :: 1 :: nil) qpg_ok_xp2))
  = (-2) :: 1 :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma qpg_smokeB_r :
  snd (projT1 (qpg_divmod_gen (1 :: 0 :: 1 :: nil) (2 :: 1 :: nil) qpg_ok_xp2))
  = 5 :: nil.
Proof. vm_compute. reflexivity. Qed.

(* 烟测 C（度 0 被除式）：3 ÷ (x+2) ⟹ 商 []（=0）余 [3] *)
Lemma qpg_smokeC :
  projT1 (qpg_divmod_gen (3 :: nil) (2 :: 1 :: nil) qpg_ok_xp2)
  = ((@nil Q), (3 :: nil)%list).
Proof. vm_compute. reflexivity. Qed.

(* 烟测 D（空被除式边例）：0 ÷ (x+2) ⟹ 商 [] 余 [] *)
Lemma qpg_smokeD :
  projT1 (qpg_divmod_gen (@nil Q) (2 :: 1 :: nil) qpg_ok_xp2)
  = ((@nil Q), (@nil Q)%list).
Proof. vm_compute. reflexivity. Qed.

(* 烟测 E（二次÷一次第三例）：(x²−1) ÷ (x+3) ⟹ 商 x−3 余 8 *)
Lemma qpg_smokeE_q :
  fst (projT1 (qpg_divmod_gen ((-1) :: 0 :: 1 :: nil) (3 :: 1 :: nil) qpg_ok_xp2))
  = (-3) :: 1 :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma qpg_smokeE_r :
  snd (projT1 (qpg_divmod_gen ((-1) :: 0 :: 1 :: nil) (3 :: 1 :: nil) qpg_ok_xp2))
  = 8 :: nil.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §7 闭合：提取面 + Print Assumptions（红线四条逐条 PA）          *)
(* ============================================================ *)

Separate Extraction qpg_engine qpg_shift_sub qpg_align_sub qpg_remlast
  qpg_pow qpg_zeros qpg_mono.

Print Assumptions qpg_id_true_inv.
Print Assumptions qpg_degge1_inv.
Print Assumptions qpg_leadne0_inv.
Print Assumptions qpg_div_cancel.
Print Assumptions qpg_lead_cancel.
Print Assumptions qpg_ring_main.
Print Assumptions qpg_ring_shift.
Print Assumptions qpg_ring_align.
Print Assumptions qpg_eval_mono.
Print Assumptions qpg_length_align.
Print Assumptions qpg_length_shift.
Print Assumptions qpg_remlast_length.
Print Assumptions qpg_lead_cons_ne.
Print Assumptions qpg_eval_remlast0.
Print Assumptions qpg_eval_align.
Print Assumptions qpg_eval_shift.
Print Assumptions qpg_lead_align.
Print Assumptions qpg_lead_shift.
Print Assumptions qpg_engine_sound.
Print Assumptions qpg_divmod_gen.
Print Assumptions qpg_ok_xp1.
Print Assumptions qpg_ok_xp2.
Print Assumptions qpg_smokeA_q.
Print Assumptions qpg_smokeA_r.
Print Assumptions qpg_smokeA_sem.
Print Assumptions qpg_smokeB_q.
Print Assumptions qpg_smokeB_r.
Print Assumptions qpg_smokeC.
Print Assumptions qpg_smokeD.
Print Assumptions qpg_smokeE_q.
Print Assumptions qpg_smokeE_r.

(* CK·多项式除法引擎一般形终（born-green 目标） *)
