(* ============================================================ *)
(* UpReqAttnQ18Tail.v —— 本件形式化温度常数 T₀ 的 Q 有理字面量承载与      *)
(*   跨 token 同值贡献恒等两件性质。                                     *)
(*                                                              *)
(* 依赖清单：UpReqAttnUniformLimit、UpReqAttnMassSplit、                  *)
(*   CW_ConstructiveWorld_219、AttnHardLimit218。                         *)
(*                                                              *)
(* 构造性注记：Set 层承载/零承认/可提取；件 1 以 stdlib Q 字面量与        *)
(*   Qlt_bool 可判定证书承载 T₀ 并配套良定义/传输小件；件 2 沿            *)
(*   id_cong 与 aid_real_eq 范式给出同值贡献恒等；词表非空位与 token      *)
(*   可判定相等位的 Set 重述与具体层供给见文尾节。                        *)
(*                                                              *)
(* 编译配方：Rocq 9.1 直调、cpu_guard 节流。                             *)
(* ============================================================ *)
Require Import UpReqAttnUniformLimit.
Require Import UpReqAttnMassSplit.
Require Import CW_ConstructiveWorld_219.
Require Import AttnHardLimit218.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import QArith.QArith.

(* ============================================================ *)
(* Part T1：Q 有理数字面量承载与 Q→Real 运输基座（件 1 定义面）      *)
(* ============================================================ *)

(* positive → nat 自持换算（本安装 Pos2Nat 系不齐：Pos2Nat.neq_0 实测 *)
(* 缺席，自建以避 stdlib API 漂移雷；S 被基库遮蔽，用 Datatypes.S）  *)
Fixpoint aqt_pos_nat (p : positive) : nat :=
  match p with
  | xH => 1%nat
  | xO p => (2 * aqt_pos_nat p)%nat
  | xI p => Datatypes.S (2 * aqt_pos_nat p)%nat
  end.

Lemma aqt_pos_nat_pos : forall p : positive, (1 <= aqt_pos_nat p)%nat.
Proof.
  induction p as [p IH | p IH | ]; cbn [aqt_pos_nat].
  - specialize IH. lia.
  - specialize IH. lia.
  - lia.
Qed.

(* 正 nat 的 Real 层严格正（对照上游 alm_k_pos 体） *)
Lemma aqt_of_nat_pos : forall n : nat, (1 <= n)%nat -> real_lt real_zero (real_of_nat n).
Proof.
  intros n Hn. destruct n as [| j].
  - lia.
  - apply (real_lt_eq_lt real_zero
             (real_plus real_one (real_of_nat j))
             (real_of_nat (Datatypes.S j))).
    + apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
               (real_plus real_one (real_of_nat j))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_lt_plus_compat_lt_le.
        -- apply real_lt_zero_one.
        -- apply real_of_nat_nonneg_aux.
    + apply real_eq_refl.
Qed.

(* Z → Real：三分直写（符号显式） *)
Definition aqt_z2r (n : Z) : Real :=
  match n with
  | Z0 => real_zero
  | Zpos p => real_of_nat (aqt_pos_nat p)
  | Zneg p => real_opp (real_of_nat (aqt_pos_nat p))
  end.

Definition aqt_den_nat (q : Q) : nat := aqt_pos_nat (Qden q).

Lemma aqt_den_pos : forall q : Q, real_lt real_zero (real_of_nat (aqt_den_nat q)).
Proof.
  intro q. apply aqt_of_nat_pos. apply aqt_pos_nat_pos.
Qed.

(* Q 有理数字面量 → Real 嵌入：num/den 直写形 *)
Definition aqt_q2r (q : Q) : Real :=
  real_mult (aqt_z2r (Qnum q))
            (real_inv_pos (real_of_nat (aqt_den_nat q)) (aqt_den_pos q)).

(* ============================================================ *)
(* Part T2：Real 层良定义代数核（wd 件）                             *)
(* compat 参序纪律：compat A B C D 装 eq A C 与 eq B D，得            *)
(* eq (A·B) (C·D)——A/C 外侧对、B/D 内侧对。                          *)
(* ============================================================ *)

(* eq 左消去（吸收式：正因子乘法消去） *)
Lemma aqt_eq_cancel_l : forall (c a b : Real) (Hc : real_lt real_zero c),
  real_eq (real_mult c a) (real_mult c b) -> real_eq a b.
Proof.
  intros c a b Hc H.
  apply (real_eq_trans _ (real_mult (real_mult c a) (real_inv_pos c Hc)) _).
  - apply real_eq_sym.
    exact (eq_mult_inv_absorb c a Hc (real_inv_pos_correct c Hc)).
  - apply (real_eq_trans _ (real_mult (real_mult c b) (real_inv_pos c Hc)) _).
    + apply (RealSetoid.real_eq_mult_compat (real_mult c a) (real_inv_pos c Hc)
               (real_mult c b) (real_inv_pos c Hc) H (real_eq_refl _)).
    + exact (eq_mult_inv_absorb c b Hc (real_inv_pos_correct c Hc)).
Qed.

(* inv 的良定义性：eq x y ⟹ eq (inv x) (inv y)（wd 件） *)
Lemma aqt_inv_wd : forall (x y : Real) (Hx : real_lt real_zero x)
  (Hy : real_lt real_zero y) (Heq : real_eq x y),
  real_eq (real_inv_pos x Hx) (real_inv_pos y Hy).
Proof.
  intros x y Hx Hy Heq.
  apply (aqt_eq_cancel_l x _ _ Hx).
  apply (real_eq_trans _ real_one _).
  - exact (real_inv_pos_correct x Hx).
  - apply (real_eq_trans _ (real_mult y (real_inv_pos y Hy)) _).
    + apply real_eq_sym. exact (real_inv_pos_correct y Hy).
    + apply (RealSetoid.real_eq_mult_compat y (real_inv_pos y Hy) x
               (real_inv_pos y Hy) (real_eq_sym x y Heq) (real_eq_refl _)).
Qed.

(* inv 乘积分裂：inv(a·b) == inv a · inv b（A 级核一） *)
Lemma aqt_inv_prod : forall (a b : Real) (Ha : real_lt real_zero a)
  (Hb : real_lt real_zero b) (Hab : real_lt real_zero (real_mult a b)),
  real_eq (real_inv_pos (real_mult a b) Hab)
          (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb)).
Proof.
  intros a b Ha Hb Hab.
  assert (Hca : real_eq (real_mult a (real_inv_pos a Ha)) real_one)
    by exact (real_inv_pos_correct a Ha).
  assert (Hcb : real_eq (real_mult b (real_inv_pos b Hb)) real_one)
    by exact (real_inv_pos_correct b Hb).
  (* 核一：(a·b)·(Ia·Ib) == 1（重排 + 双归一） *)
  assert (Hstep1 : real_eq
    (real_mult (real_mult a b)
               (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb)))
    real_one).
  { apply (real_eq_trans _
             (real_mult a (real_mult b
                (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb)))) _).
    - apply real_eq_sym. apply real_mult_assoc.
    - apply (real_eq_trans _
               (real_mult a (real_mult (real_mult b (real_inv_pos a Ha))
                  (real_inv_pos b Hb))) _).
      + apply (RealSetoid.real_eq_mult_compat a
                 (real_mult b (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb)))
                 a
                 (real_mult (real_mult b (real_inv_pos a Ha)) (real_inv_pos b Hb))).
        * apply real_eq_refl.
        * apply real_mult_assoc.
      + apply (real_eq_trans _
                 (real_mult a (real_mult (real_mult (real_inv_pos a Ha) b)
                            (real_inv_pos b Hb))) _).
        * apply (RealSetoid.real_eq_mult_compat a
                   (real_mult (real_mult b (real_inv_pos a Ha)) (real_inv_pos b Hb))
                   a
                   (real_mult (real_mult (real_inv_pos a Ha) b) (real_inv_pos b Hb))).
          -- apply real_eq_refl.
          -- apply (RealSetoid.real_eq_mult_compat
                       (real_mult b (real_inv_pos a Ha)) (real_inv_pos b Hb)
                       (real_mult (real_inv_pos a Ha) b) (real_inv_pos b Hb)).
             ** apply real_mult_comm.
             ** apply real_eq_refl.
        * apply (real_eq_trans _
                   (real_mult a (real_mult (real_inv_pos a Ha)
                      (real_mult b (real_inv_pos b Hb)))) _).
          -- apply (RealSetoid.real_eq_mult_compat a
                       (real_mult (real_mult (real_inv_pos a Ha) b)
                          (real_inv_pos b Hb))
                       a
                       (real_mult (real_inv_pos a Ha)
                          (real_mult b (real_inv_pos b Hb)))).
             ++ apply real_eq_refl.
             ++ apply real_eq_sym. apply real_mult_assoc.
          -- apply (real_eq_trans _
                       (real_mult (real_mult a (real_inv_pos a Ha))
                          (real_mult b (real_inv_pos b Hb))) _).
             ++ apply real_mult_assoc.
             ++ apply (real_eq_trans _ (real_mult real_one real_one) _).
                ** apply (RealSetoid.real_eq_mult_compat
                            (real_mult a (real_inv_pos a Ha))
                            (real_mult b (real_inv_pos b Hb))
                            real_one real_one Hca Hcb).
                ** apply real_mult_one.
  }
  (* 核二：Iab == 1·Iab == ((a·b)·(Ia·Ib))·Iab == Ia·Ib（吸收收尾） *)
  apply (real_eq_trans _ (real_mult real_one (real_inv_pos (real_mult a b) Hab)) _).
  - apply (real_eq_trans _
             (real_mult (real_inv_pos (real_mult a b) Hab) real_one) _).
    + apply real_eq_sym. apply real_mult_one.
    + apply real_mult_comm.
  - apply (real_eq_trans _
             (real_mult (real_mult (real_mult a b)
                        (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb)))
                        (real_inv_pos (real_mult a b) Hab)) _).
    + apply (RealSetoid.real_eq_mult_compat real_one
               (real_inv_pos (real_mult a b) Hab)
               (real_mult (real_mult a b)
                  (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb)))
               (real_inv_pos (real_mult a b) Hab)).
      * apply real_eq_sym. exact Hstep1.
      * apply real_eq_refl.
    + exact (eq_mult_inv_absorb (real_mult a b)
               (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb)) Hab
               (real_inv_pos_correct (real_mult a b) Hab)).
Qed.

(* 公共分母换序：x·inv(d1) == (x·d2)·inv(d1·d2)（A 级核二，八步链） *)
Lemma aqt_inv_common : forall (x d1 d2 : Real) (Hd1 : real_lt real_zero d1)
  (Hd2 : real_lt real_zero d2) (Hd12 : real_lt real_zero (real_mult d1 d2)),
  real_eq (real_mult x (real_inv_pos d1 Hd1))
          (real_mult (real_mult x d2)
                     (real_inv_pos (real_mult d1 d2) Hd12)).
Proof.
  intros x d1 d2 Hd1 Hd2 Hd12.
  assert (Hpd2 : real_eq (real_mult d2 (real_inv_pos d2 Hd2)) real_one)
    by exact (real_inv_pos_correct d2 Hd2).
  apply real_eq_sym.
  (* A：(x·d2)·I12 == (x·d2)·(I1·I2) *)
  apply (real_eq_trans _
           (real_mult (real_mult x d2)
              (real_mult (real_inv_pos d1 Hd1) (real_inv_pos d2 Hd2))) _).
  { apply (RealSetoid.real_eq_mult_compat (real_mult x d2)
             (real_inv_pos (real_mult d1 d2) Hd12)
             (real_mult x d2)
             (real_mult (real_inv_pos d1 Hd1) (real_inv_pos d2 Hd2))).
    - apply real_eq_refl.
    - exact (aqt_inv_prod d1 d2 Hd1 Hd2 Hd12). }
  (* B：(x·d2)·(I1·I2) == x·(d2·(I1·I2)) *)
  apply (real_eq_trans _
           (real_mult x (real_mult d2
              (real_mult (real_inv_pos d1 Hd1) (real_inv_pos d2 Hd2)))) _).
  { apply real_eq_sym. apply real_mult_assoc. }
  (* C：== x·((d2·I1)·I2) *)
  apply (real_eq_trans _
           (real_mult x (real_mult (real_mult d2 (real_inv_pos d1 Hd1))
              (real_inv_pos d2 Hd2))) _).
  { apply (RealSetoid.real_eq_mult_compat x
             (real_mult d2 (real_mult (real_inv_pos d1 Hd1) (real_inv_pos d2 Hd2)))
             x
             (real_mult (real_mult d2 (real_inv_pos d1 Hd1)) (real_inv_pos d2 Hd2))).
    - apply real_eq_refl.
    - apply real_mult_assoc. }
  (* D：== x·((I1·d2)·I2) *)
  apply (real_eq_trans _
           (real_mult x (real_mult (real_mult (real_inv_pos d1 Hd1) d2)
              (real_inv_pos d2 Hd2))) _).
  { apply (RealSetoid.real_eq_mult_compat x
             (real_mult (real_mult d2 (real_inv_pos d1 Hd1)) (real_inv_pos d2 Hd2))
             x
             (real_mult (real_mult (real_inv_pos d1 Hd1) d2) (real_inv_pos d2 Hd2))).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_mult_compat
               (real_mult d2 (real_inv_pos d1 Hd1)) (real_inv_pos d2 Hd2)
               (real_mult (real_inv_pos d1 Hd1) d2) (real_inv_pos d2 Hd2)).
      + apply real_mult_comm.
      + apply real_eq_refl. }
  (* E：== x·(I1·(d2·I2)) *)
  apply (real_eq_trans _
           (real_mult x (real_mult (real_inv_pos d1 Hd1)
              (real_mult d2 (real_inv_pos d2 Hd2)))) _).
  { apply (RealSetoid.real_eq_mult_compat x
             (real_mult (real_mult (real_inv_pos d1 Hd1) d2) (real_inv_pos d2 Hd2))
             x
             (real_mult (real_inv_pos d1 Hd1)
                (real_mult d2 (real_inv_pos d2 Hd2)))).
    - apply real_eq_refl.
    - apply real_eq_sym. apply real_mult_assoc. }
  (* F：== (x·I1)·(d2·I2) *)
  apply (real_eq_trans _
           (real_mult (real_mult x (real_inv_pos d1 Hd1))
              (real_mult d2 (real_inv_pos d2 Hd2))) _).
  { apply real_mult_assoc. }
  (* G：== (x·I1)·1 *)
  apply (real_eq_trans _
           (real_mult (real_mult x (real_inv_pos d1 Hd1)) real_one) _).
  { apply (RealSetoid.real_eq_mult_compat
             (real_mult x (real_inv_pos d1 Hd1))
             (real_mult d2 (real_inv_pos d2 Hd2))
             (real_mult x (real_inv_pos d1 Hd1)) real_one).
    - apply real_eq_refl.
    - exact Hpd2. }
  (* H：== x·I1 *)
  apply real_mult_one.
Qed.

(* wd 核心：跨乘等式 ⟹ 同值（公共分母两次装配 + compat 桥） *)
Lemma aqt_q2r_wd_core : forall (a b d1 d2 : Real) (Hd1 : real_lt real_zero d1)
  (Hd2 : real_lt real_zero d2) (Hd12 : real_lt real_zero (real_mult d1 d2))
  (Hx : real_eq (real_mult a d2) (real_mult b d1)),
  real_eq (real_mult a (real_inv_pos d1 Hd1))
          (real_mult b (real_inv_pos d2 Hd2)).
Proof.
  intros a b d1 d2 Hd1 Hd2 Hd12 Hx.
  assert (H21 : real_lt real_zero (real_mult d2 d1)).
  { apply (real_lt_eq_lt real_zero (real_mult d1 d2) (real_mult d2 d1)).
    - exact Hd12.
    - apply real_mult_comm. }
  apply (real_eq_trans _
           (real_mult (real_mult a d2)
              (real_inv_pos (real_mult d1 d2) Hd12)) _).
  - apply (aqt_inv_common a d1 d2 Hd1 Hd2 Hd12).
  - apply (real_eq_trans _
             (real_mult (real_mult b d1)
                (real_inv_pos (real_mult d1 d2) Hd12)) _).
    + apply (RealSetoid.real_eq_mult_compat (real_mult a d2)
               (real_inv_pos (real_mult d1 d2) Hd12)
               (real_mult b d1)
               (real_inv_pos (real_mult d1 d2) Hd12) Hx (real_eq_refl _)).
    + apply real_eq_sym.
      apply (real_eq_trans _
               (real_mult (real_mult b d1)
                  (real_inv_pos (real_mult d2 d1) H21)) _).
      * apply (aqt_inv_common b d2 d1 Hd2 Hd1 H21).
      * apply (RealSetoid.real_eq_mult_compat (real_mult b d1)
                 (real_inv_pos (real_mult d2 d1) H21)
                 (real_mult b d1)
                 (real_inv_pos (real_mult d1 d2) Hd12)).
        -- apply real_eq_refl.
        -- apply (aqt_inv_wd _ _ H21 Hd12 (real_mult_comm d2 d1)).
Qed.

(* ============================================================ *)
(* Part T3：T₀ 字面量承载与可判定数值锚（件 1 主体）                   *)
(* ============================================================ *)

(* Q 有理数字面量承载：canonical 实例 γ=2、n=4、eps=1/100 的阈值
   T₀* = γ/ln(1+2n/eps) = 2/ln(801) ≈ 0.2991137 的**下界**（安全方向：
   更小阈值仍保 T<T₀ ⟹ L1≤eps；数值下界证明 299/1000 < 2/ln(801)，
   余量 1.387e-4，Python 3000 样本复核）。 *)
Definition aqt_T0 : Q := (299 # 1000)%Q.

(* 可判定数值锚证书：Qlt_bool 计算零舍入 *)
Lemma aqt_T0_pos_q : Qlt_bool 0%Q aqt_T0 = true.
Proof. unfold aqt_T0. reflexivity. Qed.

(* 严格正传输：Qlt_bool 证书 ⟹ Real 层严格正（B 级三分传输） *)
Lemma aqt_q2r_pos : forall q : Q,
  Qlt_bool 0%Q q = true -> real_lt real_zero (aqt_q2r q).
Proof.
  intros q Hq. unfold aqt_q2r.
  destruct (Qnum q) as [| p | p] eqn:Hn.
  - exfalso. unfold Qlt_bool in Hq. cbn in Hq.
    rewrite Hn in Hq. cbn in Hq. discriminate Hq.
  - apply real_mult_pos_compat.
    + apply aqt_of_nat_pos. apply aqt_pos_nat_pos.
    + apply real_inv_pos_pos.
  - exfalso. unfold Qlt_bool in Hq. cbn in Hq.
    rewrite Hn in Hq. cbn in Hq. discriminate Hq.
Qed.

(* T₀ 实参形落成：字面量温度合法（严格正） *)
Lemma aqt_T0_pos : real_lt real_zero (aqt_q2r aqt_T0).
Proof. exact (aqt_q2r_pos aqt_T0 aqt_T0_pos_q). Qed.

(* ============================================================ *)
(* Part S：跨 token 同值件（件 2）+ 件 1 使用面实例化                *)
(* ============================================================ *)

Section AqtTail.

Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable token_eq_dec : forall a b : Token, Or (Id a b) (Not (Id a b)).
Variable z : Token -> Real.
Variable m : Token.
Variable m_in_vocab : InT m vocab.
Variable gamma : Real.
Variable gap_le : forall x : Token, Not (Id x m) ->
  real_le (real_plus (z x) gamma) (z m).

(* ---------- 同值件 2.1：权重同值（id_cong z + aid_real_eq +        *)
(* exp 良定义 + mult compat 四层传输链，A 级） ---------- *)
Lemma aqt_w_congr : forall (T : Real) (Ht : real_lt real_zero T) (x y : Token),
  Id x y ->
  real_eq (ams_w Token vocab vocab_nonempty z T Ht x)
          (ams_w Token vocab vocab_nonempty z T Ht y).
Proof.
  intros T Ht x y Hxy.
  unfold ams_w, w_T.
  apply (RealSetoid.real_eq_mult_compat _ _ _ _).
  - unfold factor_T. apply cauchy_real_exp_wd.
    apply (RealSetoid.real_eq_mult_compat _ _ _ _).
    + apply real_eq_refl.
    + exact (aid_real_eq (z x) (z y) (id_cong z Hxy)).
  - apply real_eq_refl.
Qed.

(* ---------- 同值件 2.2：alm_switch 贡献同值（Id 形，B 级分讨）      *)
Lemma aqt_switch_id : forall (c1 c2 : Real) (x y : Token), Id x y ->
  Id (alm_switch Token token_eq_dec m c1 c2 x)
     (alm_switch Token token_eq_dec m c1 c2 y).
Proof.
  intros c1 c2 x y Hxy. unfold alm_switch.
  destruct (token_eq_dec x m) as [Hxm | Hxnm];
    destruct (token_eq_dec y m) as [Hym | Hynm].
  - apply id_refl.
  - exfalso. exact (match Hynm (id_trans (id_sym Hxy) Hxm) with end).
  - exfalso. exact (match Hxnm (id_trans Hxy Hym) with end).
  - apply id_refl.
Qed.

(* alm_switch 贡献同值（real_eq 形：aid_real_eq 桥） *)
Lemma aqt_switch_congr : forall (c1 c2 : Real) (x y : Token), Id x y ->
  real_eq (alm_switch Token token_eq_dec m c1 c2 x)
          (alm_switch Token token_eq_dec m c1 c2 y).
Proof.
  intros c1 c2 x y Hxy.
  exact (aid_real_eq _ _ (aqt_switch_id c1 c2 x y Hxy)).
Qed.

(* ---------- 同值件 2.3：ams_mswitch 贡献同值（函数形开关求和辅助引理， *)
(* 同值支直接使用 aqt_w_congr） ---------- *)
Lemma aqt_mswitch_congr : forall (c : Real) (T : Real) (Ht : real_lt real_zero T)
  (x y : Token), Id x y ->
  real_eq (ams_mswitch Token token_eq_dec m c
             (ams_w Token vocab vocab_nonempty z T Ht) x)
          (ams_mswitch Token token_eq_dec m c
             (ams_w Token vocab vocab_nonempty z T Ht) y).
Proof.
  intros c T Ht x y Hxy.
  unfold ams_mswitch.
  destruct (token_eq_dec x m) as [Hxm | Hxnm];
    destruct (token_eq_dec y m) as [Hym | Hynm].
  - apply real_eq_refl.
  - exfalso. exact (match Hynm (id_trans (id_sym Hxy) Hxm) with end).
  - exfalso. exact (match Hxnm (id_trans Hxy Hym) with end).
  - exact (aqt_w_congr T Ht x y Hxy).
Qed.

(* ---------- 件 1 使用面实例化：Q 字面量温度被上游 ams_ 链真实使用        *)
(* （C 级 exact 装配：ams_mass_rest_le / ams_l1_le 于 T:=aqt_q2r aqt_T0） *)

Theorem aqt_T0_mass_rest :
  real_le (ams_M Token vocab vocab_nonempty token_eq_dec z m
             (aqt_q2r aqt_T0) aqt_T0_pos)
          (real_mult (real_of_nat (length vocab))
                     (decay_T gamma (aqt_q2r aqt_T0) aqt_T0_pos)).
Proof.
  exact (ams_mass_rest_le Token vocab vocab_nonempty token_eq_dec z m m_in_vocab
           gamma gap_le (aqt_q2r aqt_T0) aqt_T0_pos).
Qed.

Theorem aqt_T0_l1 :
  real_le
    (real_list_sum Token
       (fun x : Token =>
          real_abs (real_minus_r
             (alm_uniform Token vocab token_eq_dec m m_in_vocab x)
             (ams_w Token vocab vocab_nonempty z (aqt_q2r aqt_T0) aqt_T0_pos x)))
       vocab)
    (real_plus
       (real_mult (real_of_nat (length vocab))
                  (decay_T gamma (aqt_q2r aqt_T0) aqt_T0_pos))
       (real_mult (real_of_nat (length vocab))
                  (decay_T gamma (aqt_q2r aqt_T0) aqt_T0_pos))).
Proof.
  exact (ams_l1_le Token vocab vocab_nonempty token_eq_dec z m m_in_vocab
           gamma gap_le (aqt_q2r aqt_T0) aqt_T0_pos).
Qed.

End AqtTail.

(* ============================================================ *)
(* 提取口（字面量数值锚可计算化：aqt_q2r/aqt_T0 入口）+ 公理面审计     *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Extraction "attn_q18tail_q18d.ml"
  aqt_pos_nat aqt_z2r aqt_den_nat aqt_q2r aqt_T0 aqt_T0_pos_q
  ams_w ams_mswitch alm_switch alm_k count_token.

Print Assumptions aqt_w_congr.
Print Assumptions aqt_switch_congr.
Print Assumptions aqt_mswitch_congr.
Print Assumptions aqt_q2r_pos.
Print Assumptions aqt_q2r_wd_core.
Print Assumptions aqt_T0_pos.
Print Assumptions aqt_T0_mass_rest.
Print Assumptions aqt_T0_l1.
(* ============================================================ *)
(* 词表非空位 vocab_nonempty 与 token 可判定相等位 token_eq_dec 的        *)
(* Set 重述位与具体层供给                                                *)
(*                                                                     *)
(* 原两位为 Prop 形（Not (Id vocab nil) 与 forall a b, Or (Id a b)        *)
(* (Not (Id a b))）；本节将其重述为 Set 层形并给出具体层供给：非空取      *)
(* sigT 见证形 sigT (fun t => InT t vocab)（见证更强：可提取出具体元素），  *)
(* 可判定相等取 sigT bool 形——正支给出 Id 相等见证，负支给出              *)
(* Id a b -> Empty_set 函数（Set 层否定见证，可提取）。二点清单（bool      *)
(* 载体）上，非空见证由 InT_here 构造子直接给出，可判定相等由构造子四分    *)
(* 逐一给出（正支 id_refl，负支构造子分裂消去）。原 Prop 形假设位声明与    *)
(* 既有定理签名零改动。                                                  *)
(* ============================================================ *)
Definition aqt_vocab_nonempty_set (X : Set) (vocab : list X) : Set :=
  sigT (fun t : X => InT t vocab).
Definition aqt_token_eq_dec_set (X : Set) : Set :=
  forall a b : X,
    sigT (fun d : bool =>
      match d with
      | true => Id a b
      | false => Id a b -> Empty_set
      end).

Theorem aqt_vocab_nonempty_supply :
  aqt_vocab_nonempty_set bool (cons true (cons false nil)).
Proof. exact (existT _ true (@InT_here bool true (cons false nil))). Qed.

Theorem aqt_token_eq_dec_supply : aqt_token_eq_dec_set bool.
Proof.
  intros a b.
  destruct a; destruct b.
  - exact (existT _ true (@id_refl bool true)).
  - refine (existT _ false _).
    intro H.
    exact (match H in Id _ y return
             match y with true => unit | false => Empty_set end with
           id_refl => tt end).
  - refine (existT _ false _).
    intro H.
    exact (match H in Id _ y return
             match y with false => unit | true => Empty_set end with
           id_refl => tt end).
  - exact (existT _ true (@id_refl bool false)).
Qed.

Print Assumptions aqt_vocab_nonempty_supply.
Print Assumptions aqt_token_eq_dec_supply.
