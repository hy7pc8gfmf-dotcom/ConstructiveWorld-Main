(* ============================================================ *)
(* UpReqAttnQ18Tail.v —— 温度常数 T₀ 有理化与跨 token 同值两件        *)
(*                                                              *)
(* 目的：补齐上游注意力极限链申报的两件尾残（消费面 alm_/swg_/ams_     *)
(*   只读参照）：                                                    *)
(*   件 1（T₀ 有理化件）：线温度常数 T₀ 从实参形改为 Q 有理数字面量    *)
(*      承载（stdlib Q 层字面量＋可判定 Qlt_bool 证书），配套良定义/   *)
(*      运输小件（Q→Real 嵌入＋严格正传输＋inv 乘积良定义核＋公共      *)
(*      分母换序），目标=后续数值哨兵可计算化。上游原申报的诚实障碍     *)
(*      （有理化 T₀ 需 cw_log 的有理上界包装）仍在：本件先把可承载、    *)
(*      可判定、可传输、可被 ams_ 链消费的字面量面落盘；ln 有理上界     *)
(*      包装与跨字面量表示 wd 消费（of_nat 乘法同态缺席）为待续工作。   *)
(*   件 2（跨 token 同值件）：同一 token 值在开关求和下的同值引理——     *)
(*      token 相等（Id）则 alm_switch/ams_mswitch 贡献相等、softmax    *)
(*      权重相等；Id/setoid 传输走 id_cong＋aid_real_eq 范式            *)
(*      （Id 非 setoid，禁 rewrite）。上游范围边界（全覆盖需 argmax     *)
(*      可判定证书墙）仍在：本件交付其 building block（同值贡献恒等），  *)
(*      整墙不伸。                                                    *)
(*                                                              *)
(* 数值验真先行（假命题拦截）：3000 随机样本（canonical 实例            *)
(*   vocab=m,m,c,d、γ=2、eps=1/100；字面量 299/1000 < 2/ln(801)        *)
(*   下界余量 1.387e-4；T<0.299 逐点 L1==2M≤eps 全绿；同值贡献相等      *)
(*   3000 样本零失败）。                                              *)
(*                                                              *)
(* 主件非平凡性分级（前缀 aqt_，避免与库内既有名冲突）：                *)
(*   A 级（真代数核）aqt_inv_prod（inv 乘积分裂：吸收＋重排＋双归一）、  *)
(*      aqt_inv_common（公共分母换序八步链）、aqt_q2r_wd_core（换序     *)
(*      两次装配＋跨乘等式 compat 桥）、aqt_w_congr（id_cong z＋        *)
(*      aid_real_eq＋exp 良定义＋mult compat 四层传输链）。             *)
(*   B 级（分讨/传输）aqt_eq_cancel_l/aqt_inv_wd（eq 消去与 inv 良      *)
(*      定义）、aqt_q2r_pos（Qlt_bool 证书三分传输）、aqt_switch_id/     *)
(*      aqt_switch_congr/aqt_mswitch_congr（Id 分讨：矛盾支             *)
(*      id_trans/id_sym 构造消去，同值支消费 aqt_w_congr）。            *)
(*   C 级（消费面 exact 装配）aqt_T0_mass_rest/aqt_T0_l1                *)
(*      （ams_mass_rest_le/ams_l1_le 在 T:=aqt_q2r aqt_T0 处真实例化    *)
(*      ——Q 字面量作合法温度被上游链消费）。                            *)
(*                                                              *)
(* 陈述面：Set 层（real_eq/real_le/real_lt/Id/bool 证书），              *)
(*   无 Hypothesis 位语句。                                            *)
(*                                                              *)
(* 依赖（全部只读消费）：UpReqAttnUniformLimit / UpReqAttnMassSplit      *)
(*   及其上游面；零改既有文件。                                        *)
(*                                                              *)
(* 备注：公理面：零公理、零承认件、零弃证；零经典逻辑；                  *)
(*   文末 Print Assumptions 审计。提取口零 magic。                      *)
(*   战术纪要：match 包装 Definition 一律 destruct 前显式 unfold         *)
(*   （alm_switch/ams_mswitch）；compat 参序 (A B C D) 左内/右内成对：    *)
(*   compat A B C D 要求 eq A C 与 eq B D 得 eq (A·B) (C·D)；            *)
(*   Q 层 lia 不食（Z 层字面量计算走 cbn/reflexivity）；S 遮蔽用         *)
(*   Datatypes.S；Q 投影小写 Qden（QDen 是 Z 值 abbrev）。               *)
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

(* 正 nat 的 Real 层严格正（镜像上游 alm_k_pos 体） *)
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
(* Part T3：T₀ 字面量承载与可判定哨兵（件 1 主体）                   *)
(* ============================================================ *)

(* Q 有理数字面量承载：canonical 实例 γ=2、n=4、eps=1/100 的阈值
   T₀* = γ/ln(1+2n/eps) = 2/ln(801) ≈ 0.2991137 的**下界**（安全方向：
   更小阈值仍保 T<T₀ ⟹ L1≤eps；数值下界证明 299/1000 < 2/ln(801)，
   余量 1.387e-4，Python 3000 样本复核）。 *)
Definition aqt_T0 : Q := (299 # 1000)%Q.

(* 可判定哨兵证书：Qlt_bool 计算零舍入 *)
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
(* Part S：跨 token 同值件（件 2）+ 件 1 消费面实例化                *)
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

(* ---------- 同值件 2.3：ams_mswitch 贡献同值（函数形开关求和工作马， *)
(* 同值支真消费 aqt_w_congr） ---------- *)
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

(* ---------- 件 1 消费面实例化：Q 字面量温度被上游 ams_ 链真实消费        *)
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
(* 提取口（字面量哨兵可计算化：aqt_q2r/aqt_T0 入口）+ 公理面审计     *)
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
