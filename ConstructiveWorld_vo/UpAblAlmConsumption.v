(* ==========================================================================)
   UpAblAlmConsumption.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：aqt_pos_nat、aqt_pos_nat_pos、aqt_of_nat_pos、aqt_z2r、aqt_den_nat、aqt_den_pos、aqt_q2r、aqt_eq_cancel_l、aqt_inv_wd。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

Require Import UpReqAttnUniformLimit.
Require Import UpReqAttnMassSplit.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import AttnHardLimit218.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Extraction.
From Stdlib Require Import List Arith.

(* ================= §1 aqt_pos_nat 族 ================= *)
From Stdlib Require Import QArith.QArith.

(* Part T1：Q 有理数字面量承载与 Q→Real 运输基座（件 1 定义面）      *)

(* positive → nat 自持换算（本安装 Pos2Nat 系不齐：Pos2Nat.neq_0 实测 *)
(* 缺位，自建以避 stdlib API 漂移；S 被基库遮蔽，用 Datatypes.S）  *)
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

(* Part T2：Real 层良定义代数核（wd 件）                             *)
(* compat 参序纪律：compat A B C D 装 eq A C 与 eq B D，得            *)
(* eq (A·B) (C·D)——A/C 外侧对、B/D 内侧对。                          *)

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

(* Part T3：T₀ 字面量承载与可判定数值锚（件 1 主体）                   *)

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

(* Part S：跨 token 同值件（件 2）+ 件 1 使用面实例化                *)

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

(* 提取口（字面量数值锚可计算化：aqt_q2r/aqt_T0 入口）+ 公理面审计     *)

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
(* 词表非空位 vocab_nonempty 与 token 可判定相等位 token_eq_dec 的        *)
(* Set 重述位与具体层供给                                                *)
(* 原两位为 Prop 形（Not (Id vocab nil) 与 forall a b, Or (Id a b)        *)
(* (Not (Id a b))）；本节将其重述为 Set 层形并给出具体层供给：非空取      *)
(* sigT 见证形 sigT (fun t => InT t vocab)（见证更强：可提取出具体元素），  *)
(* 可判定相等取 sigT bool 形——正支给出 Id 相等见证，负支给出              *)
(* Id a b -> Empty_set 函数（Set 层否定见证，可提取）。二点清单（bool      *)
(* 载体）上，非空见证由 InT_here 构造子直接给出，可判定相等由构造子四分    *)
(* 逐一给出（正支 id_refl，负支构造子分裂消去）。原 Prop 形假设位声明与    *)
(* 既有定理签名零改动。                                                  *)
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
(* ================= §2 almc_vocab 族 ================= *)
(* ================= §1 并列双 max 最小世界（二元词表载体） ================= *)

(* 词汇表：二元词表；logit 常值实一——两 token 并列同为 max。 *)
Definition almc_vocab : list bool := true :: false :: nil.

Definition almc_z : bool -> Real := fun _ => real_one.

(* 并列证书：双 max 同值（z 常值，定义形） *)
Lemma almc_tie : real_eq (almc_z true) (almc_z false).
Proof.
  (* 并列证书：双 max 同值——常值载体两侧定义性归约为 real_one，恒等见证取该公共项。 *)
  exact (real_eq_refl real_one).
Qed.

(* 表可判定等词（S01 Id 面，@inl／@inr 构造；异构造子支以
   J-式依赖返回子句排除：P(y) 在失配指标取空型、在参数侧取 unit，
   id_refl 支由 tt 满足——Id 消除子的指标失配消解范式）。 *)
Definition almc_eq_dec (a b : bool) : Or (Id a b) (Not (Id a b)).
Proof.
  destruct a as [ | ]; destruct b as [ | ].
  - exact (@inl _ _ (@id_refl bool true)).
  - exact (@inr (Id true false) (Not (Id true false))
             (fun H : Id true false =>
                match H in Id _ y
                  return (match y with false => Empty_set | _ => unit end) with
                | id_refl => tt
                end)).
  - exact (@inr (Id false true) (Not (Id false true))
             (fun H : Id false true =>
                match H in Id _ y
                  return (match y with true => Empty_set | _ => unit end) with
                | id_refl => tt
                end)).
  - exact (@inl _ _ (@id_refl bool false)).
Defined.

(* 表非空证书：[true; false] 异于空表（同上 J-式范式）。 *)
Definition almc_vocab_ne : Not (Id almc_vocab nil) :=
  fun H : Id almc_vocab nil =>
    match H in Id _ y
      return (match y with nil => Empty_set | _ => unit end) with
    | id_refl => tt
    end.

(* 副本代表 m := true 入表。 *)
Definition almc_m_in : InT true almc_vocab :=
  @InT_here bool true (false :: nil).

(* 一致间隙前提在本世界的构造：γ := real_zero 非严格档。
   （严格档 γ>0 需 real_plus real_one γ ≤ real_one，与并列证书
   相斥——并列副本为严格间隙前提的未覆盖面，故链件在此只能以
   剩余前提形承载；见文件头注。） *)
Lemma almc_gap0 : forall x : bool, Not (Id x true) ->
  real_le (real_plus (almc_z x) real_zero) (almc_z true).
Proof.
  intros x Hx. destruct x as [ | ].
  - (* 情形 x = true：与 Not (Id true true) 相斥 *)
    exact (match Hx (@id_refl bool true) with end).
  - (* 情形 x = false：1 + 0 ≤ 1（加零恒等经 eq-le 可解码面） *)
    exact (RealSetoid.real_eq_le (real_plus (almc_z false) real_zero)
             (almc_z true) (real_plus_zero real_one)).
Qed.

(* ================= §2 T₀ 温度载体与所用链件 ================= *)

(* 温度载体：Q 字面量 T₀ = 299/1000（取自 UpReqAttnQ18Tail 之 aqt_T0） *)
Definition almc_T : Real := aqt_q2r aqt_T0.

(* 正性证明须透明（Defined 数据面）：其作为 real_inv_pos／decay_T／
   ams_w 的实参进入词项，Qed 不透明会阻断转换。 *)
Definition almc_Tpos : real_lt real_zero almc_T := aqt_T0_pos.

(* 硬注意力权重与副本均匀目标（并列世界实例） *)
Definition almc_w (x : bool) : Real :=
  ams_w bool almc_vocab almc_vocab_ne almc_z almc_T almc_Tpos x.

Definition almc_u (x : bool) : Real :=
  alm_uniform bool almc_vocab almc_eq_dec true almc_m_in x.

(* L1(w_T₀, δ_u) := Σ_vocab |u − w_T₀|（与上游 TV 同口径） *)
Definition almc_l1 : Real :=
  real_list_sum bool
    (fun x : bool => real_abs (real_minus_r (almc_u x) (almc_w x)))
    almc_vocab.

(* 非 m 质量 M（ams_M 之并列世界实例） *)
Definition almc_M : Real :=
  ams_M bool almc_vocab almc_vocab_ne almc_eq_dec almc_z true
    almc_T almc_Tpos.

(* γ=0 档衰减因子与词表质量实（n = 2，词表长） *)
Definition almc_decay : Real := decay_T real_zero almc_T almc_Tpos.
Definition almc_n : Real := real_of_nat (length almc_vocab).

(* ---------- 所用引理其一：aqt_T0_mass_rest（经 ams_mass_rest_le） ----------
   以并列世界九参全参显式实例化，得质量界
   M ≤ n·decay_T₀。 *)
Theorem almc_M_le_decay :
  real_le almc_M (real_mult almc_n almc_decay).
Proof.
  exact (aqt_T0_mass_rest bool almc_vocab almc_vocab_ne almc_eq_dec
           almc_z true almc_m_in real_zero almc_gap0).
Qed.

(* ---------- 所用引理其二：aqt_T0_l1（经 ams_l1_le） ----------
   同样全参显式实例化，得 L1 ≤ n·decay + n·decay。 *)
Theorem almc_l1_le_2nd :
  real_le almc_l1
    (real_plus (real_mult almc_n almc_decay)
               (real_mult almc_n almc_decay)).
Proof.
  exact (aqt_T0_l1 bool almc_vocab almc_vocab_ne almc_eq_dec
           almc_z true almc_m_in real_zero almc_gap0).
Qed.

(* ================= §3 TV 半和因子（alm_invk 并列实例）与副本数 ================= *)

(* 副本数：k = alm_k = count_token true [true; false]（并列世界
   的副本多重数=2；由 count_token 实际归约而得，非平凡计算步） *)
Definition almc_k2 : Real :=
  real_of_nat (alm_k bool almc_vocab almc_eq_dec true).

(* 每副本份额：alm_invk 并列实例 = 1/k = 1/2（半和因子）。注：real_eq 为
   sigT 见证和形，n≡k2 的反射证明须柯西见证归约，非本件目标，
   不在此构造；后续证明不依赖该重合（n 与 k 各自独立使用）。 *)
Definition almc_inv2 : Real :=
  alm_invk bool almc_vocab almc_eq_dec true almc_m_in.

Lemma almc_inv2_pos : real_lt real_zero almc_inv2.
Proof.
  exact (real_inv_pos_pos almc_k2
           (alm_k_pos bool almc_vocab almc_eq_dec true almc_m_in)).
Qed.

(* 逆元恒等式：k · (1/k) == 1（real_inv_pos_correct 经 alm_invk 展开） *)
Lemma almc_k2_inv2_one : real_eq (real_mult almc_k2 almc_inv2) real_one.
Proof.
  exact (real_inv_pos_correct almc_k2
           (alm_k_pos bool almc_vocab almc_eq_dec true almc_m_in)).
Qed.

(* TV(w_T₀, δ_u) := (1/k)·L1（k=2 即半和形） *)
Definition almc_tv : Real := real_mult almc_l1 almc_inv2.

(* 分解恒等式（由定义即得）：TV == (1/k)·L1 的交换重构 *)
Theorem almc_tv_decomp : real_eq almc_tv (real_mult almc_inv2 almc_l1).
Proof. exact (real_mult_comm almc_l1 almc_inv2). Qed.

(* 缩放消去：((k·eps)·(1/k)) == eps（交换／结合／逆元恒等式／幺元四步，
   使用 almc_k2_inv2_one） *)
Lemma almc_scale_cancel : forall e : Real,
  real_eq (real_mult (real_mult almc_k2 e) almc_inv2) e.
Proof.
  intro e.
  apply (real_eq_trans (real_mult (real_mult almc_k2 e) almc_inv2)
           (real_mult almc_inv2 (real_mult almc_k2 e)) _).
  - apply (real_mult_comm (real_mult almc_k2 e) almc_inv2).
  - apply (real_eq_trans (real_mult almc_inv2 (real_mult almc_k2 e))
             (real_mult (real_mult almc_inv2 almc_k2) e) _).
    + apply (real_mult_assoc almc_inv2 almc_k2 e).
    + apply (real_eq_trans (real_mult (real_mult almc_inv2 almc_k2) e)
               (real_mult real_one e) _).
      * apply (RealSetoid.real_eq_mult_compat
                 (real_mult almc_inv2 almc_k2) e real_one e).
        -- apply (real_eq_trans (real_mult almc_inv2 almc_k2)
                    (real_mult almc_k2 almc_inv2) _).
           ++ apply (real_mult_comm almc_inv2 almc_k2).
           ++ exact almc_k2_inv2_one.
        -- apply real_eq_refl.
      * apply (real_eq_trans (real_mult real_one e)
                 (real_mult e real_one) _).
        -- apply (real_mult_comm real_one e).
        -- apply (real_mult_one e).
Qed.

(* ================= §4 主件：TV ≤ eps 分解上界链（剩余前提形） =================
   显式前提清单：
     ① 主前提：L1(w_T₀, δ_u) ≤ k·eps —— 主定理 alm_uniform_limit
        （上游陈述 ∀eps>0, sigT T₀(>0) ∧ ∀T<T₀, L1 ≤ eps）在 T₀
        载体温度的实例；其证明归上游后续工作，本件以显式前提保留。
     ② 数据前提：eps > 0（量词面）。
   证明实际使用：almc_inv2_pos（半和因子正性），主前提经
   real_le_mult_compat 乘入半和因子，almc_scale_cancel 代数收尾。 *)
Theorem almc_tv_split : forall eps : Real,
  real_lt real_zero eps ->
  real_le almc_l1 (real_mult almc_k2 eps) ->
  real_le almc_tv eps.
Proof.
  intros eps Heps Hslot. unfold almc_tv.
  apply (RealSetoid.real_le_id_r
           (real_mult almc_l1 almc_inv2)
           (real_mult (real_mult almc_k2 eps) almc_inv2) eps).
  - (* 代数收尾：((k·eps)·(1/k)) == eps *)
    exact (almc_scale_cancel eps).
  - (* 半和因子乘入：·(1/k) ≤ (k·eps)·(1/k) *)
    exact (real_le_mult_compat almc_l1 (real_mult almc_k2 eps)
             almc_inv2 almc_inv2_pos Hslot).
Qed.

(* ================= §5 全链装配：衰减界与 TV 的衔接 =================
   链形：L1 ≤ n·decay + n·decay（almc_l1_le_2nd）
         ⟹ TV ≤ eps（剩余前提：n·decay + n·decay ≤ k·eps——γ=0 档
            decay 不趋于 0，此位即主定理闭合缺口，显式保留；
            前提接通后 TV ≤ eps 即可推得）。
   范围注记：本件验证「分解结构完整可验」，非本体闭合。 *)
Theorem almc_bound_decomp : forall eps : Real,
  real_lt real_zero eps ->
  real_le (real_plus (real_mult almc_n almc_decay)
                      (real_mult almc_n almc_decay))
          (real_mult almc_k2 eps) ->
  real_le almc_tv eps.
Proof.
  intros eps Heps Hbd.
  apply (almc_tv_split eps Heps).
  apply (real_le_trans almc_l1
           (real_plus (real_mult almc_n almc_decay)
                      (real_mult almc_n almc_decay))
           (real_mult almc_k2 eps)).
  - exact almc_l1_le_2nd.
  - exact Hbd.
Qed.

(* ================= §6 提取核验面（单条命令列出全部常量） ================= *)
(* 出口=零公理数值核（z／温度／衰减／词表质量四实函数）。             *)
(* 范围注记：世界实例面（almc_w 依赖 vocab_nonempty、almc_u/M/l1/tv/  *)
(* inv2 依赖 eq_dec）含 Id-依赖消除的证明值，提取必出公理占位——其可计算核  *)
(* （ams_w/alm_k/alm_uniform/alm_switch/count_token/aqt_q2r）已在上游  *)
(* 以节参参数化形式零公理提取（attn_q18tail_q18d.ml/               *)
(* attn_uniformlimit_q18.ml/attn_hardlimit218.ml），本件出口与上游     *)
(* 同范围收窄；世界实例面留在理论侧承载。                               *)

Set Extraction Output Directory "attn/z1bex".
Extraction "almc_consumption"
  almc_z almc_T almc_Tpos almc_decay almc_n.

(* ================= 收尾：逐件公理依赖核验（应全为 Closed） ================= *)

Print Assumptions almc_tie.
Print Assumptions almc_gap0.
Print Assumptions almc_Tpos.
Print Assumptions almc_M_le_decay.
Print Assumptions almc_l1_le_2nd.
Print Assumptions almc_inv2_pos.
Print Assumptions almc_k2_inv2_one.
Print Assumptions almc_tv_decomp.
Print Assumptions almc_scale_cancel.
Print Assumptions almc_tv_split.
Print Assumptions almc_bound_decomp.
