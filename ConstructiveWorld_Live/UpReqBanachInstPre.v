(* ═════════════════════════════════════════════════════════════════════ *) (* UpReqBanachInstPre.v —— S02 Real 载体上的 BanachAlgPre 具体实例          *)
(* 使命：本件形式化 B 路首个具体实例：把 S02 Real 载体装配进                *) (*       BanachAlgPre 弱化类（含 bcoef_plus/bcoef_wd 两字段的消解）。        *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、UpReqBanachExp、       *) (*       UpReqBanachInstB。                                                *)
(* 对标：stdlib QArith gcd/div 正规化；Banach 代数范数公理组。              *) (* 构造性注记：Set 层承载——语句面零 Prop 泄露；零承认件、零假目标、        *)
(*   零中断；证明口逐条配平，全部真闭合；前缀 bxip_ 全库零撞名。            *)
(* 编译配方：Rocq 9.1 直调，cpu_guard 温控包装，-Q 单根。                   *)
(* ═════════════════════════════════════════════════════════════════════ *)
(* 架构＝canon-germ（INSTB E-载体机器的 Real-类型移植）：                   *)
(*   载体 := Real（sigT(序列,柯西见证)）；bae := 规范种型等价               *)
(*   Id(qnorm(head a))(qnorm(head b))；一切运算＝首项有理运算后             *)
(*   规范化再包常值实数（real_const 透明，head 定义级还原）；               *)
(*   范数 := Qabs ∘ qnorm ∘ head（INSTB 处方修正定形）。                    *)
(* 分工核验：E-载体（UpReqBanachInstB）＝Q 基自由项树；本件＝Real          *)
(*   基种型载体——互补不重复；bxib_qnorm/qnorm 机器全套复用。               *)
(* 钉定面语句：按处方修正，bnorm_coef 用 Qabs∘qnorm 形；原始                *)
(*   Qabs-钉定在规范形下不可满足，以 bxip_raw_pin_wall 机器固化。           *)
(* 钉定面实测修正：bnorm_opp 点态 Id 形依赖「Qopp 与 qnorm 的               *)
(*   Qabs-范数不变」（INSTB 同位未消解项，此处未闭合）——诚实降为 QeqT      *)
(*   形消解；bxip_qeqT_cong_mult＝cong 机器补乘法位。                       *)
(* 完备性：bxin_pre_complete 同构语句照录；本架构下不可交付                 *)
(*   （范数读首项 ⟹ 完备性＝Q 列完备，1/n 模量列压死，与 INS 候选          *)
(*   B 同构）——诚实登记为未消解项，零无依据凑形。                          *)
(* 证明方法（同族范式）：①定义层受控展开（head 评估与 real_const 透明      *)
(*   delta 消化 projT1 iota；qnorm match 分支各别处理：Z0 分支 cbv 一跳闭合，   *)
(*   Zpos 分支 gcd/div 逐位以 Z.gcd_1_l／Z.div_1_r 具名换算收束）；         *)
(*   ②换轨桥接（germ 定义层 unfold 后 id_cong／id_sym／@id_trans 中间项    *)
(*   显式命名闭合；qeqT 形改走 bxib_qeqT_of_id 桥直连）；                   *)
(*   ③结构性推导（Qabs 非负叶由 Qabs_nonneg 直接给出；实例投影 delta       *)
(*   展开＋同族引擎体重演，消除跨层单跳）。                                 *)
(* ═════════════════════════════════════════════════════════════════════ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachInstB.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S0：载体面工具（head 评估 / 常值规范实数 / 种型等价 / 范数）      *)
(* ============================================================ *)

(* 首项评估：Real -> Q（定义级） *)
Definition bxip_head (x : Real) : Q := projT1 x 0%nat.

(* 常值实数构造器（S02 real_const 透明：head 定义级还原） *)
Definition bxip_cR (q : Q) : Real := real_const q.

Lemma bxip_head_cR : forall q : Q, Id (bxip_head (bxip_cR q)) q.
Proof.
  intro q.
  unfold bxip_head, bxip_cR, real_const.
  cbv beta iota zeta.
  apply id_refl.
Qed.

(* 种型等价：规范种型（Set 层，全库唯一实例位） *)
Definition bxip_bae_germ (a b : Real) : Set :=
  Id (bxib_qnorm (bxip_head a)) (bxib_qnorm (bxip_head b)).

(* 范数：Qabs∘qnorm∘head（处方定形） *)
Definition bxip_bnorm_f (x : Real) : Q := Qabs (bxib_qnorm (bxip_head x)).

(* 运算面：首项有理运算后规范化，包常值实数 *)
Definition bxip_bplus_f (x y : Real) : Real :=
  bxip_cR (bxib_qnorm (bxip_head x + bxip_head y)%Q).
Definition bxip_bmult_f (x y : Real) : Real :=
  bxip_cR (bxib_qnorm (bxip_head x * bxip_head y)%Q).
Definition bxip_bopp_f (x : Real) : Real :=
  bxip_cR (bxib_qnorm (- bxip_head x)%Q).
Definition bxip_bzero_f : Real := bxip_cR 0%Q.
Definition bxip_bone_f : Real := bxip_cR 1%Q.
Definition bxip_bcoef_f (q : Q) : Real := bxip_cR (bxib_qnorm q).

(* head 面还原（运算输出位定义级消化） *)
Lemma bxip_head_bplus : forall x y : Real,
  Id (bxip_head (bxip_bplus_f x y)) (bxib_qnorm (bxip_head x + bxip_head y)%Q).
Proof.
  intros x y.
  unfold bxip_head, bxip_bplus_f, bxip_cR, real_const.
  cbv beta iota zeta.
  apply id_refl.
Qed.

(* ============================================================ *)
(* S1：Q 层工作件（==-合同 / Qabs 助件 / 规范不动点）               *)
(* ============================================================ *)

(* QeqT 乘法合同（INSTB cong 机器补位） *)
Lemma bxip_qeqT_cong_mult : forall a b c d : Q,
  QeqT a b -> QeqT c d -> QeqT (a * c)%Q (b * d)%Q.
Proof.
  intros a b c d Hab Hcd.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq a b Hab), (qeqT_imp_qeq c d Hcd).
  apply Qeq_refl.
Qed.

(* |xy| = |x||y|（Qabs_mult 缺名，自建） *)
Lemma bxip_qabs_mult : forall x y : Q, Qabs (x * y)%Q == Qabs x * Qabs y%Q.
Proof.
  intros [n d] [m e].
  unfold Qabs, Qmult, Qeq; simpl.
  rewrite Z.abs_mul. ring.
Qed.

(* Qabs 非负（QleT' 叶；由 Qabs_nonneg 一步给出） *)
Lemma bxip_qleT_zero_abs_qn : forall x : Q, QleT' 0 (Qabs (bxib_qnorm x)).
Proof.
  intro x. exact (Qle_to_QleT' _ _ (Qabs_nonneg (bxib_qnorm x))).
Qed.

(* 规范正偶对不动点：互素正偶对的 qnorm 定义级自返 *)
Lemma bxip_qnorm_pos_pair_fix : forall w t : positive,
  (Z.gcd (Zpos w) (Z.pos t) = Z.pos 1)%Z ->
  Id (bxib_qnorm (Qmake (Zpos w) t)) (Qmake (Zpos w) t).
Proof.
  intros w t Hg1.
  rewrite bxib_qnorm_pos_shape, Hg1.
  repeat rewrite Z.div_1_r.
  reflexivity.
Qed.

(* Qabs 壳形偶对不动点（apply 统一友好形） *)
Lemma bxip_qnorm_abs_pair_fix : forall w t : positive,
  (Z.gcd (Zpos w) (Z.pos t) = Z.pos 1)%Z ->
  Id (bxib_qnorm (Qabs (Qmake (Zpos w) t))) (Qabs (Qmake (Zpos w) t)).
Proof.
  intros w t Hg1.
  change (Id (bxib_qnorm (Qmake (Zpos w) t)) (Qmake (Zpos w) t)).
  apply bxip_qnorm_pos_pair_fix. exact Hg1.
Qed.

(* INSTB 未消解项闭合：Qopp 与 qnorm 的 Qabs-范数不变 *)
(* 墙一弱化形（实为 Id 形直证）：种型等价的范数 Id-良定 *)
Lemma bxip_norm_wd : forall a b : Real,
  bxip_bae_germ a b -> Id (bxip_bnorm_f a) (bxip_bnorm_f b).
Proof.
  intros a b H.
  unfold bxip_bae_germ in H.
  unfold bxip_bnorm_f.
  exact (id_cong Qabs H).
Qed.

(* 墙一 QeqT 形 *)
Lemma bxip_norm_wd_qeqt : forall a b : Real,
  bxip_bae_germ a b -> QeqT (bxip_bnorm_f a) (bxip_bnorm_f b).
Proof.
  intros a b H.
  unfold bxip_bnorm_f.
  apply bxib_qeqT_of_id.
  unfold bxip_bae_germ in H.
  exact (id_cong Qabs H).
Qed.

(* 墙二弱化形：钉定面的 QeqT 形（原始 Qabs 右端，代表元级成立） *)
Lemma bxip_norm_coef_qeqt : forall q : Q,
  QeqT (bxip_bnorm_f (bxip_bcoef_f q)) (Qabs q).
Proof.
  intro q.
  apply qeq_imp_qeqT.
  unfold bxip_bnorm_f, bxip_bcoef_f.
  rewrite (bxip_head_cR (bxib_qnorm q)).
  rewrite (bxib_qnorm_fix_id q).
  apply (Qeq_trans _ (Qabs (bxib_qnorm q))).
  - apply Qabs_wd. apply Qeq_refl.
  - apply (Qeq_trans _ (Qabs q)).
    + apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
    + apply Qeq_refl.
Qed.

(* 原始钉定墙固化：Id 形 Qabs-原始钉定在规范形下不可满足 *)
Lemma bxip_raw_pin_wall :
  Id (bxip_bnorm_f (bxip_bcoef_f (2#4)%Q)) (Qabs (2#4)%Q) ->
  Id (1#2)%Q (2#4)%Q.
Proof.
  intro H.
  change (Id (Qabs (bxib_qnorm (bxib_qnorm (2#4)%Q))) (Qabs (2#4)%Q)) in H.
  rewrite bxib_qnorm_fix_id in H.
  exact H.
Qed.

Lemma bxip_raw_pin_absurd : Id (1#2)%Q (2#4)%Q -> False.
Proof.
  intro H.
  apply (id_cong Qnum) in H.
  change (Id (Zpos 1) (Zpos 2)) in H.
  inversion H.
Qed.

(* ============================================================ *)
(* S3：BanachAlgPre 弱化类（39 字段＝两字段扩容对齐后的同构副本，       *)
(*   钉定面按处方修正）＋首例装配                                  *)
(* ============================================================ *)

Class bxip_BanachAlgPre := {
  bxip_BA : Set;
  bxip_bae : bxip_BA -> bxip_BA -> Set;
  bxip_bae_refl   : forall a : bxip_BA, bxip_bae a a;
  bxip_bae_sym    : forall a b : bxip_BA, bxip_bae a b -> bxip_bae b a;
  bxip_bae_trans  : forall a b c : bxip_BA,
    bxip_bae a b -> bxip_bae b c -> bxip_bae a c;
  bxip_bzero : bxip_BA;
  bxip_bone : bxip_BA;
  bxip_bplus : bxip_BA -> bxip_BA -> bxip_BA;
  bxip_bmult : bxip_BA -> bxip_BA -> bxip_BA;
  bxip_bopp : bxip_BA -> bxip_BA;
  bxip_bcoef : Q -> bxip_BA;
  bxip_bnorm : bxip_BA -> Q;
  bxip_bplus_assoc : forall a b c : bxip_BA,
    bxip_bae (bxip_bplus a (bxip_bplus b c)) (bxip_bplus (bxip_bplus a b) c);
  bxip_bplus_comm  : forall a b : bxip_BA,
    bxip_bae (bxip_bplus a b) (bxip_bplus b a);
  bxip_bplus_zero  : forall a : bxip_BA, bxip_bae (bxip_bplus a bxip_bzero) a;
  bxip_bplus_opp   : forall a : bxip_BA,
    bxip_bae (bxip_bplus a (bxip_bopp a)) bxip_bzero;
  bxip_bmult_assoc : forall a b c : bxip_BA,
    bxip_bae (bxip_bmult a (bxip_bmult b c)) (bxip_bmult (bxip_bmult a b) c);
  bxip_bmult_one_l : forall a : bxip_BA, bxip_bae (bxip_bmult bxip_bone a) a;
  bxip_bmult_one_r : forall a : bxip_BA, bxip_bae (bxip_bmult a bxip_bone) a;
  bxip_bdistrib_l  : forall a b c : bxip_BA,
    bxip_bae (bxip_bmult a (bxip_bplus b c))
             (bxip_bplus (bxip_bmult a b) (bxip_bmult a c));
  bxip_bdistrib_r  : forall a b c : bxip_BA,
    bxip_bae (bxip_bmult (bxip_bplus a b) c)
             (bxip_bplus (bxip_bmult a c) (bxip_bmult b c));
  bxip_bmult_zero  : forall a : bxip_BA,
    bxip_bae (bxip_bmult a bxip_bzero) bxip_bzero;
  bxip_bplus_wd : forall a b c d : bxip_BA,
    bxip_bae a c -> bxip_bae b d -> bxip_bae (bxip_bplus a b) (bxip_bplus c d);
  bxip_bmult_wd : forall a b c d : bxip_BA,
    bxip_bae a c -> bxip_bae b d -> bxip_bae (bxip_bmult a b) (bxip_bmult c d);
  bxip_bopp_wd  : forall a b : bxip_BA,
    bxip_bae a b -> bxip_bae (bxip_bopp a) (bxip_bopp b);
  bxip_bnorm_wd : forall a b : bxip_BA,
    bxip_bae a b -> Id (bxip_bnorm a) (bxip_bnorm b);
  bxip_bcoef_zero : bxip_bae (bxip_bcoef 0%Q) bxip_bzero;
  bxip_bcoef_one  : bxip_bae (bxip_bcoef 1%Q) bxip_bone;
  bxip_bcoef_mult : forall q r : Q,
    bxip_bae (bxip_bcoef (q * r)%Q) (bxip_bmult (bxip_bcoef q) (bxip_bcoef r));
  bxip_bcoef_comm : forall (q : Q) (a : bxip_BA),
    bxip_bae (bxip_bmult a (bxip_bcoef q)) (bxip_bmult (bxip_bcoef q) a);
(* ---- 两字段扩容联动：Pre 副本扩容（37→39，                    *)
(*   语句形逐字承 UpReqBanachInst.v 同构副本）---- *)
  bxip_bcoef_plus : forall q r : Q,
    bxip_bae (bxip_bplus (bxip_bcoef q) (bxip_bcoef r)) (bxip_bcoef (q + r)%Q);
  bxip_bcoef_wd : forall q r : Q, q == r -> bxip_bae (bxip_bcoef q) (bxip_bcoef r);
  bxip_bnorm_zero : Id (bxip_bnorm bxip_bzero) 0%Q;
  bxip_bnorm_one  : Id (bxip_bnorm bxip_bone) 1%Q;
  bxip_bnorm_opp  : forall a : bxip_BA, QeqT (bxip_bnorm (bxip_bopp a)) (bxip_bnorm a);
  bxip_bnorm_pos  : forall a : bxip_BA, QleT' 0 (bxip_bnorm a);
  bxip_bnorm_plus : forall a b : bxip_BA,
    QleT' (bxip_bnorm (bxip_bplus a b)) (bxip_bnorm a + bxip_bnorm b)%Q;
  bxip_bnorm_mult : forall a b : bxip_BA,
    QleT' (bxip_bnorm (bxip_bmult a b)) (bxip_bnorm a * bxip_bnorm b)%Q;
  bxip_bnorm_coef : forall q : Q, Id (bxip_bnorm (bxip_bcoef q)) (Qabs (bxib_qnorm q));
}.

(* Pre 上的完备性语句（与 INS bxin_pre_complete 逐字同构） *)
Definition bxip_pre_complete (p : bxip_BanachAlgPre) : Set :=
  forall (u : nat -> (@bxip_BA p)),
    (forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall m n : nat,
        NatLe N m -> NatLe N n ->
        QltT (@bxip_bnorm p
          (@bxip_bplus p (u m) (@bxip_bopp p (u n)))) eps)) ->
    sigT (fun l : (@bxip_BA p) => forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall n : nat,
        NatLe N n ->
        QltT (@bxip_bnorm p
          (@bxip_bplus p (u n) (@bxip_bopp p l))) eps)).

(* ---- 字段 discharge 件（种型载体） ---- *)

Lemma bxip_f_plus_assoc : forall a b c : Real,
  bxip_bae_germ (bxip_bplus_f a (bxip_bplus_f b c))
                (bxip_bplus_f (bxip_bplus_f a b) c).
Proof.
  intros a b c. unfold bxip_bae_germ.
  rewrite (bxip_head_bplus a (bxip_bplus_f b c)).
  rewrite (bxip_head_bplus b c).
  rewrite (bxip_head_bplus (bxip_bplus_f a b) c).
  rewrite (bxip_head_bplus a b).
  rewrite (bxib_qnorm_fix_id (bxip_head a + bxib_qnorm (bxip_head b + bxip_head c))%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxip_head a + bxip_head b)%Q + bxip_head c)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxip_head a + (bxip_head b + bxip_head c))%Q).
  - apply bxib_qeqT_cong_plus; [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply (bxib_qeqT_trans _ (bxip_head a + bxip_head b + bxip_head c)%Q).
    + apply qeq_imp_qeqT. apply Qplus_assoc.
    + apply bxib_qeqT_cong_plus;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix | apply bxib_qeqT_refl].
Qed.

Lemma bxip_head_bmult : forall x y : Real,
  Id (bxip_head (bxip_bmult_f x y)) (bxib_qnorm (bxip_head x * bxip_head y)%Q).
Proof.
  intros x y.
  unfold bxip_head, bxip_bmult_f, bxip_cR, real_const.
  cbv beta iota zeta.
  apply id_refl.
Qed.

Lemma bxip_head_bopp : forall x : Real,
  Id (bxip_head (bxip_bopp_f x)) (bxib_qnorm (- bxip_head x)%Q).
Proof.
  intro x.
  unfold bxip_head, bxip_bopp_f, bxip_cR, real_const.
  cbv beta iota zeta.
  apply id_refl.
Qed.

(* ---- 等价三律 ---- *)

Lemma bxip_f_refl : forall a : Real, bxip_bae_germ a a.
Proof.
  intro a.
  unfold bxip_bae_germ.
  exact (@id_refl _ (bxib_qnorm (bxip_head a))).
Qed.

Lemma bxip_f_sym : forall a b : Real, bxip_bae_germ a b -> bxip_bae_germ b a.
Proof.
  intros a b H.
  unfold bxip_bae_germ in H |- *.
  exact (id_sym H).
Qed.

Lemma bxip_f_trans : forall a b c : Real,
  bxip_bae_germ a b -> bxip_bae_germ b c -> bxip_bae_germ a c.
Proof.
  intros a b c H1 H2.
  unfold bxip_bae_germ in H1 |- *.
  unfold bxip_bae_germ in H2.
  exact (@id_trans _ (bxib_qnorm (bxip_head a))
            (bxib_qnorm (bxip_head b)) (bxib_qnorm (bxip_head c)) H1 H2).
Qed.

(* ---- 加法群 ---- *)

Lemma bxip_f_plus_comm : forall a b : Real,
  bxip_bae_germ (bxip_bplus_f a b) (bxip_bplus_f b a).
Proof.
  intros a b. unfold bxip_bae_germ.
  rewrite (bxip_head_bplus a b), (bxip_head_bplus b a).
  rewrite (bxib_qnorm_fix_id (bxip_head a + bxip_head b)%Q).
  rewrite (bxib_qnorm_fix_id (bxip_head b + bxip_head a)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qplus_comm.
Qed.

Lemma bxip_f_plus_zero : forall a : Real,
  bxip_bae_germ (bxip_bplus_f a bxip_bzero_f) a.
Proof.
  intro a. unfold bxip_bae_germ.
  rewrite (bxip_head_bplus a bxip_bzero_f).
  unfold bxip_bzero_f.
  rewrite (bxip_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id (bxip_head a + 0%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (bxip_head a)).
  - apply Qplus_0_r.
  - apply Qeq_refl.
Qed.

Lemma bxip_f_plus_opp : forall a : Real,
  bxip_bae_germ (bxip_bplus_f a (bxip_bopp_f a)) bxip_bzero_f.
Proof.
  intro a. unfold bxip_bae_germ.
  rewrite (bxip_head_bplus a (bxip_bopp_f a)).
  rewrite (bxip_head_bopp a).
  unfold bxip_bzero_f.
  rewrite (bxip_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id (bxip_head a + bxib_qnorm (- bxip_head a)%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxip_head a + (- bxip_head a))%Q).
  - apply bxib_qeqT_cong_plus;
      [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply qeq_imp_qeqT. apply Qplus_opp_r.
Qed.

(* ---- 乘法群 ---- *)

Lemma bxip_f_mult_assoc : forall a b c : Real,
  bxip_bae_germ (bxip_bmult_f a (bxip_bmult_f b c))
                (bxip_bmult_f (bxip_bmult_f a b) c).
Proof.
  intros a b c. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult a (bxip_bmult_f b c)).
  rewrite (bxip_head_bmult b c).
  rewrite (bxip_head_bmult (bxip_bmult_f a b) c).
  rewrite (bxip_head_bmult a b).
  rewrite (bxib_qnorm_fix_id (bxip_head a * bxib_qnorm (bxip_head b * bxip_head c))%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxip_head a * bxip_head b)%Q * bxip_head c)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxip_head a * (bxip_head b * bxip_head c))%Q).
  - apply bxip_qeqT_cong_mult; [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply (bxib_qeqT_trans _ (bxip_head a * bxip_head b * bxip_head c)%Q).
    + apply qeq_imp_qeqT. apply Qmult_assoc.
    + apply bxip_qeqT_cong_mult;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix | apply bxib_qeqT_refl].
Qed.

Lemma bxip_f_mult_one_l : forall a : Real,
  bxip_bae_germ (bxip_bmult_f bxip_bone_f a) a.
Proof.
  intro a. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult bxip_bone_f a).
  unfold bxip_bone_f.
  rewrite (bxip_head_cR 1%Q).
  rewrite (bxib_qnorm_fix_id (1%Q * bxip_head a)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_1_l.
Qed.

Lemma bxip_f_mult_one_r : forall a : Real,
  bxip_bae_germ (bxip_bmult_f a bxip_bone_f) a.
Proof.
  intro a. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult a bxip_bone_f).
  unfold bxip_bone_f.
  rewrite (bxip_head_cR 1%Q).
  rewrite (bxib_qnorm_fix_id (bxip_head a * 1%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_1_r.
Qed.

Lemma bxip_f_distrib_l : forall a b c : Real,
  bxip_bae_germ (bxip_bmult_f a (bxip_bplus_f b c))
                (bxip_bplus_f (bxip_bmult_f a b) (bxip_bmult_f a c)).
Proof.
  intros a b c. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult a (bxip_bplus_f b c)).
  rewrite (bxip_head_bplus b c).
  rewrite (bxip_head_bplus (bxip_bmult_f a b) (bxip_bmult_f a c)).
  rewrite (bxip_head_bmult a b), (bxip_head_bmult a c).
  rewrite (bxib_qnorm_fix_id (bxip_head a * bxib_qnorm (bxip_head b + bxip_head c))%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxip_head a * bxip_head b)%Q
                              + bxib_qnorm (bxip_head a * bxip_head c))%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxip_head a * (bxip_head b + bxip_head c))%Q).
  - apply bxip_qeqT_cong_mult; [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply (bxib_qeqT_trans _ (bxip_head a * bxip_head b + bxip_head a * bxip_head c)%Q).
    + apply qeq_imp_qeqT. apply Qmult_plus_distr_r.
    + apply bxib_qeqT_cong_plus;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix |
         apply bxib_qeqT_sym; apply bxib_qnorm_fix].
Qed.

Lemma bxip_f_distrib_r : forall a b c : Real,
  bxip_bae_germ (bxip_bmult_f (bxip_bplus_f a b) c)
                (bxip_bplus_f (bxip_bmult_f a c) (bxip_bmult_f b c)).
Proof.
  intros a b c. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult (bxip_bplus_f a b) c).
  rewrite (bxip_head_bplus a b).
  rewrite (bxip_head_bplus (bxip_bmult_f a c) (bxip_bmult_f b c)).
  rewrite (bxip_head_bmult a c), (bxip_head_bmult b c).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxip_head a + bxip_head b)%Q * bxip_head c)%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxip_head a * bxip_head c)%Q
                              + bxib_qnorm (bxip_head b * bxip_head c))%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ ((bxip_head a + bxip_head b) * bxip_head c)%Q).
  - apply bxip_qeqT_cong_mult; [apply bxib_qnorm_fix | apply bxib_qeqT_refl].
  - apply (bxib_qeqT_trans _ (bxip_head a * bxip_head c + bxip_head b * bxip_head c)%Q).
    + apply qeq_imp_qeqT. apply Qmult_plus_distr_l.
    + apply bxib_qeqT_cong_plus;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix |
         apply bxib_qeqT_sym; apply bxib_qnorm_fix].
Qed.

Lemma bxip_f_mult_zero : forall a : Real,
  bxip_bae_germ (bxip_bmult_f a bxip_bzero_f) bxip_bzero_f.
Proof.
  intro a. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult a bxip_bzero_f).
  unfold bxip_bzero_f.
  rewrite (bxip_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id (bxip_head a * 0%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_0_r.
Qed.

(* ---- 良定三件 ---- *)

Lemma bxip_f_plus_wd : forall a b c d : Real,
  bxip_bae_germ a c -> bxip_bae_germ b d ->
  bxip_bae_germ (bxip_bplus_f a b) (bxip_bplus_f c d).
Proof.
  intros a b c d Hac Hbd. unfold bxip_bae_germ.
  rewrite (bxip_head_bplus a b), (bxip_head_bplus c d).
  rewrite (bxib_qnorm_fix_id (bxip_head a + bxip_head b)%Q).
  rewrite (bxib_qnorm_fix_id (bxip_head c + bxip_head d)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_plus.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head a))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head c))).
      * apply bxib_qeqT_of_id. exact Hac.
      * apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head b))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head d))).
      * apply bxib_qeqT_of_id. exact Hbd.
      * apply bxib_qnorm_fix.
Qed.

Lemma bxip_f_mult_wd : forall a b c d : Real,
  bxip_bae_germ a c -> bxip_bae_germ b d ->
  bxip_bae_germ (bxip_bmult_f a b) (bxip_bmult_f c d).
Proof.
  intros a b c d Hac Hbd. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult a b), (bxip_head_bmult c d).
  rewrite (bxib_qnorm_fix_id (bxip_head a * bxip_head b)%Q).
  rewrite (bxib_qnorm_fix_id (bxip_head c * bxip_head d)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxip_qeqT_cong_mult.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head a))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head c))).
      * apply bxib_qeqT_of_id. exact Hac.
      * apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head b))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head d))).
      * apply bxib_qeqT_of_id. exact Hbd.
      * apply bxib_qnorm_fix.
Qed.

Lemma bxip_f_opp_wd : forall a b : Real,
  bxip_bae_germ a b -> bxip_bae_germ (bxip_bopp_f a) (bxip_bopp_f b).
Proof.
  intros a b Hab. unfold bxip_bae_germ.
  rewrite (bxip_head_bopp a), (bxip_head_bopp b).
  rewrite (bxib_qnorm_fix_id (- bxip_head a)%Q).
  rewrite (bxib_qnorm_fix_id (- bxip_head b)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_opp.
  apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head a))).
  - apply bxib_qeqT_sym. apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxip_head b))).
    + apply bxib_qeqT_of_id. exact Hab.
    + apply bxib_qnorm_fix.
Qed.

(* ---- 标量嵌入面 ---- *)

Lemma bxip_f_coef_zero : bxip_bae_germ (bxip_bcoef_f 0%Q) bxip_bzero_f.
Proof.
  unfold bxip_bae_germ, bxip_bcoef_f, bxip_bzero_f, bxip_head, real_const.
  unfold bxib_qnorm.
  cbv beta iota zeta.
  apply id_refl.
Qed.

Lemma bxip_f_coef_one : bxip_bae_germ (bxip_bcoef_f 1%Q) bxip_bone_f.
Proof.
  unfold bxip_bae_germ, bxip_bcoef_f, bxip_bone_f, bxip_head, real_const.
  unfold bxib_qnorm.
  cbv beta iota zeta.
  replace (Z.gcd (Z.pos 1) (Z.pos 1)) with (Zpos 1) by (symmetry; apply Z.gcd_1_l).
  replace (Z.div (Z.pos 1) (Z.pos 1)) with (Zpos 1) by (symmetry; apply Z.div_1_r).
  apply id_refl.
Qed.

Lemma bxip_f_coef_mult : forall q r : Q,
  bxip_bae_germ (bxip_bcoef_f (q * r)%Q)
                (bxip_bmult_f (bxip_bcoef_f q) (bxip_bcoef_f r)).
Proof.
  intros q r. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult (bxip_bcoef_f q) (bxip_bcoef_f r)).
  unfold bxip_bcoef_f.
  repeat rewrite bxip_head_cR.
  rewrite (bxib_qnorm_fix_id (q * r)%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q * bxib_qnorm r)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_sym.
  apply bxip_qeqT_cong_mult; apply bxib_qnorm_fix.
Qed.

Lemma bxip_f_coef_comm : forall (q : Q) (a : Real),
  bxip_bae_germ (bxip_bmult_f a (bxip_bcoef_f q))
                (bxip_bmult_f (bxip_bcoef_f q) a).
Proof.
  intros q a. unfold bxip_bae_germ.
  rewrite (bxip_head_bmult a (bxip_bcoef_f q)).
  rewrite (bxip_head_bmult (bxip_bcoef_f q) a).
  unfold bxip_bcoef_f.
  repeat rewrite bxip_head_cR.
  rewrite (bxib_qnorm_fix_id (bxip_head a * bxib_qnorm q)%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q * bxip_head a)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_comm.
Qed.

(* ---- W6a 二字段 discharge（INST3 已建 qnorm 机器同款链） ---- *)

(* bcoef_plus：q+r 嵌入＝嵌入和（种型载体上归 qnorm 环链一发修） *)
Lemma bxip_f_coef_plus : forall q r : Q,
  bxip_bae_germ (bxip_bplus_f (bxip_bcoef_f q) (bxip_bcoef_f r))
                (bxip_bcoef_f (q + r)%Q).
Proof.
  intros q r. unfold bxip_bae_germ.
  rewrite (bxip_head_bplus (bxip_bcoef_f q) (bxip_bcoef_f r)).
  unfold bxip_bcoef_f.
  repeat rewrite bxip_head_cR.
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q + bxib_qnorm r)%Q).
  rewrite (bxib_qnorm_fix_id (q + r)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_plus; apply bxib_qnorm_fix.
Qed.

(* bcoef_wd：Qeq 代表元无关（QeqT 过桥 qnorm 良定） *)
Lemma bxip_f_coef_wd : forall q r : Q,
  q == r -> bxip_bae_germ (bxip_bcoef_f q) (bxip_bcoef_f r).
Proof.
  intros q r Hqr. unfold bxip_bae_germ, bxip_bcoef_f.
  repeat rewrite bxip_head_cR.
  rewrite (bxib_qnorm_fix_id q), (bxib_qnorm_fix_id r).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. exact Hqr.
Qed.

(* ---- 范数面 ---- *)

Lemma bxip_f_norm_zero : Id (bxip_bnorm_f bxip_bzero_f) 0%Q.
Proof.
  unfold bxip_bnorm_f, bxip_bzero_f, bxip_head, real_const, bxib_qnorm, Qabs.
  cbv beta iota zeta.
  apply id_refl.
Qed.

Lemma bxip_f_norm_one : Id (bxip_bnorm_f bxip_bone_f) 1%Q.
Proof.
  unfold bxip_bnorm_f, bxip_bone_f, bxip_head, real_const, bxib_qnorm, Qabs.
  cbv beta iota zeta.
  replace (Z.gcd (Z.pos 1) (Z.pos 1)) with (Zpos 1) by (symmetry; apply Z.gcd_1_l).
  replace (Z.div (Z.pos 1) (Z.pos 1)) with (Zpos 1) by (symmetry; apply Z.div_1_r).
  apply id_refl.
Qed.

Lemma bxip_f_norm_opp : forall a : Real,
  QeqT (bxip_bnorm_f (bxip_bopp_f a)) (bxip_bnorm_f a).
Proof.
  intro a. unfold bxip_bnorm_f.
  rewrite (bxip_head_bopp a).
  rewrite (bxib_qnorm_fix_id (- bxip_head a)%Q).
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (Qabs (- bxip_head a)%Q)).
  - apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
  - rewrite Qabs_opp.
    apply (Qeq_sym (Qabs (bxib_qnorm (bxip_head a))) (Qabs (bxip_head a))).
    apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
Qed.

Lemma bxip_f_norm_pos : forall a : Real, QleT' 0 (bxip_bnorm_f a).
Proof.
  intro a.
  exact (Qle_to_QleT' _ _ (Qabs_nonneg (bxib_qnorm (bxip_head a)))).
Qed.

Lemma bxip_f_norm_plus : forall a b : Real,
  QleT' (bxip_bnorm_f (bxip_bplus_f a b))
        (bxip_bnorm_f a + bxip_bnorm_f b)%Q.
Proof.
  intros a b. unfold bxip_bnorm_f.
  rewrite (bxip_head_bplus a b).
  rewrite (bxib_qnorm_fix_id (bxip_head a + bxip_head b)%Q).
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (bxip_head a + bxip_head b)%Q)).
  - apply qeq_imp_qle.
    apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
  - apply (Qle_trans _ (Qabs (bxip_head a) + Qabs (bxip_head b))%Q).
    + apply Qabs_triangle.
    + apply qeq_imp_qle.
      apply (@Qplus_comp (Qabs (bxip_head a)) (Qabs (bxib_qnorm (bxip_head a)))
           (Qeq_sym (Qabs (bxib_qnorm (bxip_head a))) (Qabs (bxip_head a))
                (Qabs_wd (bxib_qnorm (bxip_head a)) (bxip_head a)
                     (qeqT_imp_qeq (bxib_qnorm (bxip_head a)) (bxip_head a)
                          (bxib_qnorm_fix (bxip_head a)))))
           (Qabs (bxip_head b)) (Qabs (bxib_qnorm (bxip_head b)))
           (Qeq_sym (Qabs (bxib_qnorm (bxip_head b))) (Qabs (bxip_head b))
                (Qabs_wd (bxib_qnorm (bxip_head b)) (bxip_head b)
                     (qeqT_imp_qeq (bxib_qnorm (bxip_head b)) (bxip_head b)
                          (bxib_qnorm_fix (bxip_head b)))))).
Qed.

Lemma bxip_f_norm_mult : forall a b : Real,
  QleT' (bxip_bnorm_f (bxip_bmult_f a b))
        (bxip_bnorm_f a * bxip_bnorm_f b)%Q.
Proof.
  intros a b. unfold bxip_bnorm_f.
  rewrite (bxip_head_bmult a b).
  rewrite (bxib_qnorm_fix_id (bxip_head a * bxip_head b)%Q).
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (bxip_head a) * Qabs (bxip_head b))%Q).
  - apply qeq_imp_qle.
    apply (Qeq_trans (Qabs (bxib_qnorm (bxip_head a * bxip_head b)%Q))
                     (Qabs (bxip_head a * bxip_head b)%Q)
                     (Qabs (bxip_head a) * Qabs (bxip_head b))%Q).
    + apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
    + apply bxip_qabs_mult.
  - apply qeq_imp_qle.
    apply (@Qmult_comp (Qabs (bxip_head a)) (Qabs (bxib_qnorm (bxip_head a)))
         (Qeq_sym (Qabs (bxib_qnorm (bxip_head a))) (Qabs (bxip_head a))
              (Qabs_wd (bxib_qnorm (bxip_head a)) (bxip_head a)
                   (qeqT_imp_qeq (bxib_qnorm (bxip_head a)) (bxip_head a)
                        (bxib_qnorm_fix (bxip_head a)))))
         (Qabs (bxip_head b)) (Qabs (bxib_qnorm (bxip_head b)))
         (Qeq_sym (Qabs (bxib_qnorm (bxip_head b))) (Qabs (bxip_head b))
              (Qabs_wd (bxib_qnorm (bxip_head b)) (bxip_head b)
                   (qeqT_imp_qeq (bxib_qnorm (bxip_head b)) (bxip_head b)
                        (bxib_qnorm_fix (bxip_head b)))))).
Qed.

Lemma bxip_f_norm_coef : forall q : Q,
  Id (bxip_bnorm_f (bxip_bcoef_f q)) (Qabs (bxib_qnorm q)).
Proof.
  intro q. unfold bxip_bnorm_f, bxip_bcoef_f.
  rewrite (bxip_head_cR (bxib_qnorm q)).
  rewrite (bxib_qnorm_fix_id q).
  reflexivity.
Qed.

(* ---- 首例装配（B 路第一个具体实例，弱化形） ---- *)

Instance bxip_real_pre : bxip_BanachAlgPre := {|
  bxip_BA := Real;
  bxip_bae := bxip_bae_germ;
  bxip_bae_refl := bxip_f_refl;
  bxip_bae_sym := bxip_f_sym;
  bxip_bae_trans := bxip_f_trans;
  bxip_bzero := bxip_bzero_f;
  bxip_bone := bxip_bone_f;
  bxip_bplus := bxip_bplus_f;
  bxip_bmult := bxip_bmult_f;
  bxip_bopp := bxip_bopp_f;
  bxip_bcoef := bxip_bcoef_f;
  bxip_bnorm := bxip_bnorm_f;
  bxip_bplus_assoc := bxip_f_plus_assoc;
  bxip_bplus_comm := bxip_f_plus_comm;
  bxip_bplus_zero := bxip_f_plus_zero;
  bxip_bplus_opp := bxip_f_plus_opp;
  bxip_bmult_assoc := bxip_f_mult_assoc;
  bxip_bmult_one_l := bxip_f_mult_one_l;
  bxip_bmult_one_r := bxip_f_mult_one_r;
  bxip_bdistrib_l := bxip_f_distrib_l;
  bxip_bdistrib_r := bxip_f_distrib_r;
  bxip_bmult_zero := bxip_f_mult_zero;
  bxip_bplus_wd := bxip_f_plus_wd;
  bxip_bmult_wd := bxip_f_mult_wd;
  bxip_bopp_wd := bxip_f_opp_wd;
  bxip_bnorm_wd := bxip_norm_wd;
  bxip_bcoef_zero := bxip_f_coef_zero;
  bxip_bcoef_one := bxip_f_coef_one;
  bxip_bcoef_mult := bxip_f_coef_mult;
  bxip_bcoef_comm := bxip_f_coef_comm;
  bxip_bcoef_plus := bxip_f_coef_plus;
  bxip_bcoef_wd := bxip_f_coef_wd;
  bxip_bnorm_zero := bxip_f_norm_zero;
  bxip_bnorm_one := bxip_f_norm_one;
  bxip_bnorm_opp := bxip_f_norm_opp;
  bxip_bnorm_pos := bxip_f_norm_pos;
  bxip_bnorm_plus := bxip_f_norm_plus;
  bxip_bnorm_mult := bxip_f_norm_mult;
  bxip_bnorm_coef := bxip_f_norm_coef;
|}.

(* 装配检验：实例投影面（bcoef 1 ~ bone，经实例字段） *)
Lemma bxip_inst_smoke :
  @bxip_bae bxip_real_pre
    (@bxip_bcoef bxip_real_pre 1%Q)
    (@bxip_bone bxip_real_pre).
Proof.
  unfold bxip_bae, bxip_bcoef, bxip_bone.
  cbv delta [bxip_real_pre] beta iota zeta.
  unfold bxip_bae_germ, bxip_bcoef_f, bxip_bone_f, bxip_head, real_const.
  unfold bxib_qnorm.
  cbv beta iota zeta.
  replace (Z.gcd (Z.pos 1) (Z.pos 1)) with (Zpos 1) by (symmetry; apply Z.gcd_1_l).
  replace (Z.div (Z.pos 1) (Z.pos 1)) with (Zpos 1) by (symmetry; apply Z.div_1_r).
  apply id_refl.
Qed.

(* 装配检验：W6a 二字段投影位（bcoef plus/wd 经实例字段） *)
Lemma bxip_inst_smoke_plus : forall q r : Q,
  @bxip_bae bxip_real_pre
    (@bxip_bplus bxip_real_pre (@bxip_bcoef bxip_real_pre q)
                               (@bxip_bcoef bxip_real_pre r))
    (@bxip_bcoef bxip_real_pre (q + r)%Q).
Proof.
  intros q r.
  unfold bxip_bae, bxip_bcoef, bxip_bplus.
  cbv delta [bxip_real_pre] beta iota zeta.
  unfold bxip_bae_germ.
  rewrite (bxip_head_bplus (bxip_bcoef_f q) (bxip_bcoef_f r)).
  unfold bxip_bcoef_f.
  repeat rewrite bxip_head_cR.
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q + bxib_qnorm r)%Q).
  rewrite (bxib_qnorm_fix_id (q + r)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_plus; apply bxib_qnorm_fix.
Qed.

Lemma bxip_inst_smoke_wd : forall q r : Q,
  q == r ->
  @bxip_bae bxip_real_pre
    (@bxip_bcoef bxip_real_pre q) (@bxip_bcoef bxip_real_pre r).
Proof.
  intros q r Hqr.
  unfold bxip_bae, bxip_bcoef.
  cbv delta [bxip_real_pre] beta iota zeta.
  unfold bxip_bae_germ, bxip_bcoef_f.
  repeat rewrite bxip_head_cR.
  rewrite (bxib_qnorm_fix_id q), (bxib_qnorm_fix_id r).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. exact Hqr.
Qed.

(* ============================================================ *)
(* 提取检验 + 假设面自审                                      *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Separate Extraction bxip_bnorm_f bxip_qeqT_cong_mult bxip_qabs_mult bxip_raw_pin_wall bxip_norm_wd_qeqt
  bxip_norm_coef_qeqt bxip_f_coef_plus bxip_f_coef_wd.

Print Assumptions bxip_raw_pin_wall.
Print Assumptions bxip_norm_wd_qeqt.
Print Assumptions bxip_f_plus_assoc.
Print Assumptions bxip_f_norm_mult.
Print Assumptions bxip_inst_smoke.
Print Assumptions bxip_f_coef_plus.
Print Assumptions bxip_f_coef_wd.
Print Assumptions bxip_inst_smoke_plus.
Print Assumptions bxip_inst_smoke_wd.
