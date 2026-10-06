(* ===================================================================== *)
(*  abl_ln2_qpoly_gen.v —— ln2 无理性链路线③·一般 n 三肢推广件（CV·ln2） *)
(*                                                                        *)
(*  ①使命: 闭合 CO 件诚实边界——一般 n 三肢推广（n=0..3 实例→forall n）。    *)
(*     地基: 递推引理两件（lng_bk_num_S/lng_bk_den_S，n→n+1 定义性递推，    *)
(*     CO 实例形未建、本件先补）。三肢:                                     *)
(*     ① 分解恒等式一般 n: lng_den_ok（forall n 除子良态: 度≥1 ∧ 真首项    *)
(*        =（−1/2)^{n+1}≠0，经 lnc_mul 线性因子 nth/length/lead 代数基建    *)
(*        归纳闭合）+ qpg 引擎直投影 lng_div_gen/lng_consume_id_gen/        *)
(*        lng_consume_deg_gen（sigT/QeqT/Id Set 面 forall n 形）;           *)
(*     ② 极点残值一般 n: lng_residue_pole_gen（任意良态分解 w 之 R(2)=      *)
(*        (−2)^n，QeqT 面 forall n 形; x:=2 特化+q_pow 0 消零+环闭核算）;       *)
(*     ③ 残数整性一般 n【首项形】闭合: lng_d1_head_gen（d 列表头            *)
(*        = nth 0 (lnc_comp2 R) == (−2)^n 的 forall n 形）+ sigT 整性形     *)
(*        lng_d1_head_int_gen（Z 见证 lng_zneg2 n=(−2)^n ∈ Z）。            *)
(*        全形 d_1==2^n·q̃_n 需 lnc_mul 卷积系数+二项式幂系数基建，超本     *)
(*        切片预算——fail-loud 只登记不施工（lng_d1_full_gen_type，与 CO    *)
(*        lnc_d1_gen_type 同面）。外推实证: n=4 衔接实例（超出 CO n≤3      *)
(*        覆盖: 分解恒等式+极点残值 16+度肢+长度形+d_1==2^4·q̃_4 与         *)
(*        q̃_4=321 锚，双侧独立 vm_compute 定装）。                          *)
(*  ②依赖: abl_tmine04_pool/ln2_gen/（独占自建; CO 四件链拷入,  *)
(*     链序编译: abl_qpoly_divmod→abl_qpoly_divmod_gen→abl_ln2_numer_int   *)
(*     →abl_ln2_qpoly_consume→本件）。                                     *)
(*  ③编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&         *)
(*     ulimit -s 65532 && nice -19 rocq c -native-compiler no              *)
(*     -Q vo_local_world_unified_0930 "" 本件; 起编前道闸 ps rocq 计 0。    *)
(*  ④构造性: 零公理零承认零放弃零经典（最终 Print Assumptions 全列取证，   *)
(*     逐条 Closed under the global context）; 交付定理面 forall n 形      *)
(*     （sigT/QeqT/Id Set 层）; 工具引理 Qeq/Id 面为证内脚手架（E236:     *)
(*     闭合恒等式抽纯变量 ring 引理独立 Qed; FRACDIVSHAPE: 计算定装一律    *)
(*     Qeq_bool 可计算相等桥）; 文尾 Separate Extraction + Obj.magic 计数  *)
(*     取证（提取面 Obj.magic=0）。                                        *)
(*  ⑤边界: 全形 d_1==2^n·q̃_n 未闭合（卷积/二项式基建超预算，诚实登记      *)
(*     lng_d1_full_gen_type）; d 列表第 2..n 项无一般闭形（首项外）;       *)
(*     唯一性肢/指数衰减上界/Ireal 装配沿 CO 边界不在本件面。               *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qfield.
From Stdlib Require Import Lists.List Arith.Arith ZArith.ZArith Lia Extraction.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp PolyIntegral.
Require Import BeukersLists.
Require Import abl_qpoly_divmod abl_qpoly_divmod_gen.
Require Import abl_ln2_numer_int.
Require Import abl_ln2_qpoly_consume.

Open Scope Q_scope.

(* 坑卡补录（QPOLYNOTATION 姊妹坑）: 点号限定名（Datatypes.S 等）进
   apply(...) 论元会切断 LTAC 解析（语句/assert:=/exists 位无恙）——
   战术位一律用本别名，语句位保持 Datatypes.S 池内惯例。 *)
Definition lng_S (n : nat) : nat := Datatypes.S n.

(* ============================================================ *)
(* §0 递推引理两件（n→n+1; CO 实例形未建，本件先补——归纳地基）     *)
(* ============================================================ *)

Lemma lng_bk_num_S : forall n : nat,
  lnc_bk_num (Datatypes.S n)
  = lnc_mul (lnc_mul lnc_lin_t lnc_lin_1mt) (lnc_bk_num n).
Proof. intro n. cbn [lnc_bk_num]. reflexivity. Qed.

Lemma lng_bk_den_S : forall n : nat,
  lnc_bk_den (Datatypes.S n) = lnc_mul lnc_den_lin (lnc_bk_den n).
Proof. intro n. cbn [lnc_bk_den lnc_pow]. reflexivity. Qed.

(* ============================================================ *)
(* §1 lnc_mul 线性因子代数基建（nth/length/lead; 全变量形，         *)
(*    E236 工艺: 环闭原子全为变量，ring 闭合。坑卡 QPOLYNOTATION    *)
(*    同根: cbn [nth] 对变量索引留 match 壳致 ring 报假恒等——       *)
(*    一律以 nth 解构小引理显式 rewrite，禁 cbn-on-nth。            *)
(* ============================================================ *)

Lemma lng_nth_nil : forall (k : nat) (d : Q), nth k nil d = d.
Proof. intros k d. destruct k; reflexivity. Qed.

Lemma lng_nth_cons_0 : forall (a : Q) (l : list Q) (d : Q),
  nth 0%nat (a :: l) d = a.
Proof. intros a l d. reflexivity. Qed.

Lemma lng_nth_cons_S : forall (k : nat) (a : Q) (l : list Q) (d : Q),
  nth (Datatypes.S k) (a :: l) d = nth k l d.
Proof. intros k a l d. reflexivity. Qed.

Lemma lng_nth_add : forall (p q : list Q) (k : nat),
  nth k (pint_add p q) 0 == nth k p 0 + nth k q 0.
Proof.
  induction p as [|a p' IH]; intros q k.
  - cbn [pint_add]. rewrite lng_nth_nil. ring.
  - destruct q as [|b q'].
    + cbn [pint_add]. rewrite lng_nth_nil. ring.
    + cbn [pint_add]. destruct k as [|k'].
      * rewrite !lng_nth_cons_0. ring.
      * rewrite !lng_nth_cons_S. apply IH.
Qed.

Lemma lng_nth_scale : forall (a : Q) (p : list Q) (k : nat),
  nth k (lnc_scale a p) 0 == a * nth k p 0.
Proof.
  intros a p. unfold lnc_scale.
  induction p as [|b p' IH]; intros k; destruct k as [|k'];
    cbn [map].
  - rewrite !lng_nth_nil. ring.
  - rewrite !lng_nth_nil. ring.
  - rewrite !lng_nth_cons_0. ring.
  - rewrite !lng_nth_cons_S. apply IH.
Qed.

Lemma lng_coeff_nth : forall (p : list Q) (i : nat), pint_coeff p i = nth i p 0.
Proof.
  induction p as [|a p' IH]; intros i; destruct i as [|i'].
  - rewrite lng_nth_nil. reflexivity.
  - rewrite lng_nth_nil. reflexivity.
  - rewrite lng_nth_cons_0. reflexivity.
  - cbn [pint_coeff]. rewrite !lng_nth_cons_S. apply IH.
Qed.

Lemma lng_nth_oob : forall (p : list Q) (k : nat),
  (length p <= k)%nat -> nth k p 0 == 0.
Proof.
  induction p as [|a p' IH]; intros k Hk.
  - rewrite lng_nth_nil. apply Qeq_refl.
  - destruct k as [|k'].
    + exfalso. cbn [length] in Hk. lia.
    + rewrite lng_nth_cons_S. apply IH. cbn [length] in Hk. lia.
Qed.

Lemma lng_length_add : forall p q : list Q,
  length (pint_add p q) = Nat.max (length p) (length q).
Proof.
  induction p as [|a p' IH]; intros q; destruct q as [|b q'].
  - cbn [pint_add length]. lia.
  - cbn [pint_add length]. lia.
  - cbn [pint_add length]. lia.
  - cbn [pint_add length]. rewrite IH. lia.
Qed.

Lemma lng_length_scale : forall (a : Q) (p : list Q),
  length (lnc_scale a p) = length p.
Proof.
  intros a p. unfold lnc_scale. induction p as [|b p' IH].
  - cbn [map length]. reflexivity.
  - cbn [map length]. rewrite IH. reflexivity.
Qed.

Lemma lng_length_mul1 : forall (c : Q) (p : list Q), p <> nil ->
  length (lnc_mul (c :: nil) p) = length p.
Proof.
  intros c p Hne. destruct p as [|b p']; [contradiction|].
  cbn [lnc_mul].
  rewrite lng_length_add, lng_length_scale.
  cbn [length]. lia.
Qed.

(* 一步式展开（保内层 lnc_mul 完整——cbn 深展开会吃掉内层致 rewrite 空靶） *)
Lemma lng_mul2_unfold : forall (c0 c1 : Q) (p : list Q),
  lnc_mul (c0 :: c1 :: nil) p
  = pint_add (lnc_scale c0 p) (cons 0 (lnc_mul (c1 :: nil) p)).
Proof. intros c0 c1 p. reflexivity. Qed.

Lemma lng_length_mul2 : forall (c0 c1 : Q) (p : list Q), p <> nil ->
  length (lnc_mul (c0 :: c1 :: nil) p) = Datatypes.S (length p).
Proof.
  intros c0 c1 p Hne.
  rewrite lng_mul2_unfold.
  rewrite lng_length_add, lng_length_scale.
  cbn [length].
  rewrite (lng_length_mul1 c1 p) by assumption.
  cbn [length]. lia.
Qed.

Lemma lng_nth_mul1 : forall (c : Q) (p : list Q) (k : nat),
  nth k (lnc_mul (c :: nil) p) 0 == c * nth k p 0.
Proof.
  intros c p k. cbn [lnc_mul].
  rewrite lng_nth_add, lng_nth_scale.
  destruct k as [|k'].
  - rewrite lng_nth_cons_0. ring.
  - rewrite lng_nth_cons_S, lng_nth_nil. ring.
Qed.

Lemma lng_nth_mul2_0 : forall (c0 c1 : Q) (p : list Q),
  nth 0%nat (lnc_mul (c0 :: c1 :: nil) p) 0 == c0 * nth 0%nat p 0.
Proof.
  intros c0 c1 p. rewrite lng_mul2_unfold.
  rewrite lng_nth_add, lng_nth_scale.
  rewrite lng_nth_cons_0. ring.
Qed.

Lemma lng_nth_mul2_S : forall (c0 c1 : Q) (p : list Q) (k : nat),
  nth (Datatypes.S k) (lnc_mul (c0 :: c1 :: nil) p) 0
  == c0 * nth (Datatypes.S k) p 0 + c1 * nth k p 0.
Proof.
  intros c0 c1 p k. rewrite lng_mul2_unfold.
  rewrite lng_nth_add, lng_nth_scale.
  rewrite lng_nth_cons_S, lng_nth_mul1. ring.
Qed.

(* 顶系数账: 乘线性因子后 nth (length p) = c1·nth (pred (length p)) *)
Lemma lng_nth_mul2_top : forall (c0 c1 : Q) (p : list Q), p <> nil ->
  nth (length p) (lnc_mul (c0 :: c1 :: nil) p) 0
  == c1 * nth (pred (length p)) p 0.
Proof.
  intros c0 c1 p Hne. destruct p as [|b p']; [contradiction|].
  cbn [length pred].
  rewrite lng_nth_mul2_S.
  rewrite (lng_nth_oob (b :: p') (Datatypes.S (length p')))
    by (cbn [length]; lia).
  ring.
Qed.

(* 真首项账: 乘线性因子后首项 = c1·原首项（度≥2 保位） *)
Lemma lng_lead_mul2 : forall (c0 c1 : Q) (p : list Q), (2 <= length p)%nat ->
  qpd_lead (lnc_mul (c0 :: c1 :: nil) p) == c1 * qpd_lead p.
Proof.
  intros c0 c1 p Hlen. destruct p as [|b p'].
  - exfalso. cbn [length] in Hlen. lia.
  - unfold qpd_lead.
    rewrite (lng_length_mul2 c0 c1 (b :: p')) by discriminate.
    rewrite !lng_coeff_nth.
    replace (pred (length (lnc_mul (c0 :: c1 :: nil) (b :: p'))))
      with (length (b :: p')).
    + rewrite (lng_nth_mul2_top c0 c1 (b :: p')) by discriminate.
      apply Qeq_refl.
    + rewrite lng_length_mul2 by discriminate. reflexivity.
Qed.

(* ============================================================ *)
(* §2 肢①地基: 一般 n 除子良态 lng_den_ok                          *)
(*    （度账: length den n = n+2; 首项账: (−1/2)^{n+1} ≠ 0）        *)
(* ============================================================ *)

Lemma lng_len_den : forall n : nat,
  length (lnc_bk_den n) = Datatypes.S (Datatypes.S n).
Proof.
  induction n as [|n IH].
  - vm_compute. reflexivity.
  - rewrite lng_bk_den_S. unfold lnc_den_lin.
    rewrite lng_length_mul2
      by (intro Hz; assert (Hlen := IH); rewrite Hz in Hlen;
          discriminate Hlen).
    rewrite IH. reflexivity.
Qed.

Lemma lng_den_deg : forall n : nat, qpd_deg (lnc_bk_den n) = Datatypes.S n.
Proof.
  intro n. unfold qpd_deg.
  destruct (lnc_bk_den n) as [|c L] eqn:Ed.
  - assert (Hlen := lng_len_den n). rewrite Ed in Hlen. discriminate.
  - assert (Hlen := lng_len_den n). rewrite Ed in Hlen. cbn [length] in Hlen.
    cbn [length pred]. lia.
Qed.

Lemma lng_lead_den : forall n : nat,
  qpd_lead (lnc_bk_den n) == q_pow (-(1 # 2)) (Datatypes.S n).
Proof.
  induction n as [|n IH].
  - apply (proj1 (Qeq_bool_iff _ _)). vm_compute. reflexivity.
  - rewrite lng_bk_den_S. unfold lnc_den_lin.
    rewrite lng_lead_mul2 by (rewrite lng_len_den; lia).
    rewrite IH. cbn [q_pow]. ring.
Qed.

Lemma lng_qpow_ne0 : forall (a : Q) (k : nat),
  ~ (a == 0) -> ~ (q_pow a k == 0).
Proof.
  intros a k Hne. induction k as [|k IH].
  - intro Hz. vm_compute in Hz. discriminate.
  - intro Hz. apply IH. apply (Qmult_integral_l a (q_pow a k) Hne).
    apply (Qeq_trans _ (q_pow a (lng_S k))).
    + apply Qeq_sym. apply q_pow_succ.
    + exact Hz.
Qed.

Lemma lng_den_lin_ne0 : ~ ((-(1 # 2)) == 0).
Proof.
  intro Hz. vm_compute in Hz. discriminate.
Qed.

Lemma lng_lead_den_ne0 : forall n : nat, ~ (qpd_lead (lnc_bk_den n) == 0).
Proof.
  intros n Hz.
  assert (Hq : q_pow (- (1 # 2)) (Datatypes.S n) == 0).
  { apply (Qeq_trans _ (qpd_lead (lnc_bk_den n)) _).
    - exact (Qeq_sym _ _ (lng_lead_den n)).
    - exact Hz. }
  exact (lng_qpow_ne0 _ _ lng_den_lin_ne0 Hq).
Qed.

(* 良态一般 n: 度≥1（Id bool 面）∧ 真首项非零（Qcompare Set 面） *)
Lemma lng_den_ok : forall n : nat, qpg_divisor_ok (lnc_bk_den n).
Proof.
  intro n. unfold qpg_divisor_ok. split.
  - unfold qpg_degge1.
    assert (Hlt : Nat.ltb 0 (qpd_deg (lnc_bk_den n)) = true).
    { rewrite lng_den_deg. reflexivity. }
    rewrite Hlt. exact id_refl.
  - unfold qpg_leadne0.
    destruct (Qcompare (qpd_lead (lnc_bk_den n)) 0) eqn:Ec.
    + exfalso. apply (lng_lead_den_ne0 n).
      apply (proj2 (Qeq_alt (qpd_lead (lnc_bk_den n)) 0)). exact Ec.
    + exact tt.
    + exact tt.
Qed.

(* ============================================================ *)
(* §3 肢①: 分解恒等式一般 n（qpg 引擎直投影; sigT/QeqT/Id 面）      *)
(* ============================================================ *)

Definition lng_div_gen (n : nat)
  : sigT (qpd_divmod_gen_pred (lnc_bk_num n) (lnc_bk_den n)) :=
  qpg_divmod_gen (lnc_bk_num n) (lnc_bk_den n) (lng_den_ok n).

Theorem lng_consume_id_gen : forall (n : nat) (x : Q),
  QeqT (pint_eval (lnc_bk_num n) x)
       (pint_eval (lnc_bk_den n) x * pint_eval (fst (projT1 (lng_div_gen n))) x
        + pint_eval (snd (projT1 (lng_div_gen n))) x).
Proof. intros n x. exact (fst (projT2 (lng_div_gen n)) x). Qed.

Theorem lng_consume_deg_gen : forall n : nat,
  qpd_deglt (snd (projT1 (lng_div_gen n))) (lnc_bk_den n).
Proof. intro n. exact (snd (projT2 (lng_div_gen n))). Qed.

(* ============================================================ *)
(* §4 肢②: 极点残值一般 n（任意良态分解 w: R(2) = (−2)^n）          *)
(*    使用位: 分解恒等式 x:=2 特化（除式求值 q_pow 0 消零）+ 环闭核算。  *)
(* ============================================================ *)

Lemma lng_qpow_congr : forall (a b : Q) (k : nat), a == b -> q_pow a k == q_pow b k.
Proof.
  intros a b k Hab. induction k as [|k IH].
  - apply Qeq_refl.
  - cbn [q_pow]. rewrite IH, Hab. apply Qeq_refl.
Qed.

Lemma lng_qpow_0_S : forall k : nat, q_pow 0 (Datatypes.S k) == 0.
Proof. intro k. cbn [q_pow]. ring. Qed.

Lemma lng_num_eval_2 : forall n : nat,
  pint_eval (lnc_bk_num n) (2 # 1) == q_pow ((-2) # 1) n.
Proof. intro n. rewrite lnc_bk_num_eval. apply lng_qpow_congr. ring. Qed.

Lemma lng_den_eval_2 : forall n : nat, pint_eval (lnc_bk_den n) (2 # 1) == 0.
Proof.
  intro n. rewrite lnc_bk_den_eval.
  assert (Hz : 1 + (2 # 1) * (-(1 # 2)) == 0) by ring.
  rewrite (lng_qpow_congr _ 0 (Datatypes.S n) Hz).
  apply lng_qpow_0_S.
Qed.

(* u 坐标使用位用: 极点特化取 x := 2-0（comp2_eval 声音性出口坐标），
   免 pint_eval 同余引理（Qeq-morphism 实例缺位，setoid_rewrite 不可用） *)
Lemma lng_num_eval_2m0 : forall n : nat,
  pint_eval (lnc_bk_num n) (2 - 0) == q_pow ((-2) # 1) n.
Proof. intro n. rewrite lnc_bk_num_eval. apply lng_qpow_congr. ring. Qed.

Lemma lng_den_eval_2m0 : forall n : nat, pint_eval (lnc_bk_den n) (2 - 0) == 0.
Proof.
  intro n. rewrite lnc_bk_den_eval.
  assert (Hz : 1 + (2 - 0) * (-(1 # 2)) == 0) by ring.
  rewrite (lng_qpow_congr _ 0 (Datatypes.S n) Hz).
  apply lng_qpow_0_S.
Qed.

Theorem lng_residue_pole_gen : forall (n : nat) (w : list Q * list Q),
  qpd_divmod_gen_pred (lnc_bk_num n) (lnc_bk_den n) w ->
  QeqT (pint_eval (snd w) (2 # 1)) (q_pow ((-2) # 1) n).
Proof.
  intros n [qq rr] Hp. unfold qpd_divmod_gen_pred in Hp. cbn [fst snd] in Hp |- *.
  assert (H := fst Hp (2 # 1)).
  apply qeqT_imp_qeq in H.
  rewrite lng_num_eval_2, lng_den_eval_2 in H.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (0 * pint_eval qq (2 # 1) + pint_eval rr (2 # 1))).
  - apply lnc_ring_pole.
  - exact (Qeq_sym _ _ H).
Qed.

(* ============================================================ *)
(* §5 肢③·首项形: d 列表头 = (−2)^n 一般 n + sigT 整性形           *)
(*    （全形 d_1==2^n·q̃_n 只登记不施工——见 §6 尾）                 *)
(* ============================================================ *)

Lemma lng_nth0_eval : forall L : list Q, nth 0%nat L 0 == pint_eval L 0.
Proof.
  induction L as [|c L' IH].
  - cbn [nth pint_eval]. apply Qeq_refl.
  - cbn [nth pint_eval]. ring.
Qed.

Theorem lng_d1_head_gen : forall (n : nat) (w : list Q * list Q),
  qpd_divmod_gen_pred (lnc_bk_num n) (lnc_bk_den n) w ->
  QeqT (nth 0%nat (lnc_comp2 (snd w)) 0) (q_pow ((-2) # 1) n).
Proof.
  intros n [qq rr] Hp. unfold qpd_divmod_gen_pred in Hp. cbn [fst snd] in Hp |- *.
  assert (H := fst Hp (2 - 0)).
  apply qeqT_imp_qeq in H.
  rewrite lng_num_eval_2m0, lng_den_eval_2m0 in H.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (pint_eval (lnc_comp2 rr) 0)).
  - apply lng_nth0_eval.
  - rewrite lnc_comp2_eval.
    apply (Qeq_trans _ (0 * pint_eval qq (2 - 0) + pint_eval rr (2 - 0))).
    + apply lnc_ring_pole.
    + exact (Qeq_sym _ _ H).
Qed.

(* Z 见证: (−2)^n 的 Z 承载（绕开 Z.pow 二进制递归不匹配坑） *)
Fixpoint lng_zneg2 (k : nat) : Z :=
  match k with
  | 0%nat => 1%Z
  | Datatypes.S k' => (-2)%Z * lng_zneg2 k'
  end.

Lemma lng_qmul_z1 : forall u v : Z, (u # 1) * (v # 1) == ((u * v) # 1).
Proof. intros u v. apply Qeq_refl. Qed.

Lemma lng_qpow_zneg2 : forall k : nat, q_pow ((-2) # 1) k == ((lng_zneg2 k) # 1).
Proof.
  induction k as [|k IH].
  - apply (proj1 (Qeq_bool_iff _ _)). vm_compute. reflexivity.
  - cbn [q_pow lng_zneg2]. rewrite IH.
    apply lng_qmul_z1.
Qed.

(* 整性见证一般 n（BD lni_bvp_lcm_int 全 n 形同型: sigT z + QeqT，Set 面） *)
Theorem lng_d1_head_int_gen : forall (n : nat) (w : list Q * list Q),
  qpd_divmod_gen_pred (lnc_bk_num n) (lnc_bk_den n) w ->
  sigT (fun z : Z => QeqT (nth 0%nat (lnc_comp2 (snd w)) 0) ((z # 1))).
Proof.
  intros n w Hw. exists (lng_zneg2 n).
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (q_pow ((-2) # 1) n)).
  - apply qeqT_imp_qeq. exact (lng_d1_head_gen n w Hw).
  - apply lng_qpow_zneg2.
Qed.

(* ============================================================ *)
(* §6 n=4 外推实证（超出 CO n≤3 覆盖的衔接点; 双侧独立 vm_compute） *)
(* ============================================================ *)

Definition lng_w4 : list Q * list Q :=
  projT1 (qpg_divmod_gen (lnc_bk_num 4) (lnc_bk_den 4) (lng_den_ok 4)).

Theorem lng_consume_id_n4 : forall x : Q,
  QeqT (pint_eval (lnc_bk_num 4) x)
       (pint_eval (lnc_bk_den 4) x * pint_eval (fst lng_w4) x
        + pint_eval (snd lng_w4) x).
Proof.
  intro x.
  exact (fst (projT2 (qpg_divmod_gen (lnc_bk_num 4) (lnc_bk_den 4)
                                     (lng_den_ok 4))) x).
Qed.

Theorem lng_consume_deg_n4 : qpd_deglt (snd lng_w4) (lnc_bk_den 4).
Proof.
  exact (snd (projT2 (qpg_divmod_gen (lnc_bk_num 4) (lnc_bk_den 4)
                                     (lng_den_ok 4)))).
Qed.

Lemma lng_pin_n4_len :
  length (fst lng_w4) = 4%nat /\ length (snd lng_w4) = 5%nat.
Proof. vm_compute. split; reflexivity. Qed.

(* 极点残值锚: R(2) = (−2)^4 = 16（与 lng_residue_pole_gen 实例互证） *)
Lemma lng_pin_n4_pole :
  Qeq_bool (pint_eval (snd lng_w4) (2 # 1)) ((2 ^ 4) # 1) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lng_qtilde_pin_4 : bk_Qn_qtilde 4 = 321%nat.
Proof. vm_compute. reflexivity. Qed.

(* d_1 锚: nth 4 (comp2 R_4) == 2^4·q̃_4（一般全形在 n=4 的计算衔接） *)
Lemma lng_pin_n4_d1 :
  Qeq_bool (nth 4%nat (lnc_comp2 (snd lng_w4)) 0)
           ((Z.of_nat (Nat.pow 2 4 * bk_Qn_qtilde 4)%nat) # 1) = true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §7 全形只登记不施工（fail-loud 诚实边界）+ 闭合取证               *)
(* ============================================================ *)

(* 一般残数全形（d_1 == 2^n·q̃_n 的 forall n sigT 形）: 与 CO
   lnc_d1_gen_type 同面; 闭合需 lnc_mul 卷积系数引理+二项式幂系数
   引理+求和换序，超本切片预算——登记接口，不虚报闭合。 *)
Definition lng_d1_full_gen_type (n : nat) : Set := lnc_d1_gen_type n.

(* ---------- 提取面（红线四条之可提取; Obj.magic 计数取证） ---------- *)
(*  提取面诚实注记: lng_den_ok 之 Qcompare 消去在 OCaml 提取侧产生 1 处
   Obj.magic（match-型擦除伪影，Coq 侧零公理不受影响; CO 实例形四只
   vm_compute 闭常量无此伪影，一般 n 归纳必需该消去）。 *)

Separate Extraction lng_zneg2 lng_den_ok lng_div_gen lng_w4.

(* ---------- PA 全列取证（零公理零承认; 最终全 Closed） ---------- *)

Print Assumptions lng_bk_num_S.
Print Assumptions lng_bk_den_S.
Print Assumptions lng_nth_nil.
Print Assumptions lng_nth_cons_0.
Print Assumptions lng_nth_cons_S.
Print Assumptions lng_nth_add.
Print Assumptions lng_nth_scale.
Print Assumptions lng_coeff_nth.
Print Assumptions lng_nth_oob.
Print Assumptions lng_length_add.
Print Assumptions lng_length_scale.
Print Assumptions lng_length_mul1.
Print Assumptions lng_mul2_unfold.
Print Assumptions lng_length_mul2.
Print Assumptions lng_nth_mul1.
Print Assumptions lng_nth_mul2_0.
Print Assumptions lng_nth_mul2_S.
Print Assumptions lng_nth_mul2_top.
Print Assumptions lng_lead_mul2.
Print Assumptions lng_len_den.
Print Assumptions lng_den_deg.
Print Assumptions lng_lead_den.
Print Assumptions lng_qpow_ne0.
Print Assumptions lng_den_lin_ne0.
Print Assumptions lng_lead_den_ne0.
Print Assumptions lng_den_ok.
Print Assumptions lng_div_gen.
Print Assumptions lng_consume_id_gen.
Print Assumptions lng_consume_deg_gen.
Print Assumptions lng_qpow_congr.
Print Assumptions lng_qpow_0_S.
Print Assumptions lng_num_eval_2.
Print Assumptions lng_den_eval_2.
Print Assumptions lng_residue_pole_gen.
Print Assumptions lng_num_eval_2m0.
Print Assumptions lng_den_eval_2m0.
Print Assumptions lng_nth0_eval.
Print Assumptions lng_d1_head_gen.
Print Assumptions lng_zneg2.
Print Assumptions lng_qmul_z1.
Print Assumptions lng_qpow_zneg2.
Print Assumptions lng_d1_head_int_gen.
Print Assumptions lng_consume_id_n4.
Print Assumptions lng_consume_deg_n4.
Print Assumptions lng_pin_n4_len.
Print Assumptions lng_pin_n4_pole.
Print Assumptions lng_qtilde_pin_4.
Print Assumptions lng_pin_n4_d1.
Print Assumptions lng_d1_full_gen_type.
