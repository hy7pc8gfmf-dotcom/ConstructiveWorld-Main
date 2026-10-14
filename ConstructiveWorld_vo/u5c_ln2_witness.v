(* ===================================================================== *)
(*  u5c_ln2_witness.v —— ln2 供给链第五肢 cloₙ 下界见证（轻铸件）           *)
(* ===================================================================== *)
(*  模块名：u5c_ln2_witness。                                              *)
(*  使命：为 ln2 供给链五层接口的第五肢（下界肢 ∀n, clo_n ≤ I_n）铸造       *)
(*    可计算的下界见证函数 u5c_ln2_clo_witness n = n! · (2n)! / (3n+1)!。   *)
(*    数学核：Beukers 型积分 I'_n = ∫₀¹ tⁿ(1−t)ⁿ/(1+t)^(n+1) dt 的          *)
(*    全正项级数首项（Beta 值 B(n+1,2n+1)）。全级数各项为正，故首项是       *)
(*    I'_n 的正下界。见证用 Defined 透明定义、自含阶乘、可直接提取。        *)
(*    主定理：见证正性 u5c_ln2_witness_pos；数值锚 n=2 时见证值             *)
(*    2!·4!/7! = 1/105；锚形⟹第五肢组装 u5c_ln2_witness_limb_of_anchor；   *)
(*    双验收面 u5c_ln2_witness_accept / u5c_ln2_witness_accept_asm         *)
(*    （乙件 slot 与装配件 slot 逐字形态）。                                *)
(*  实现注记：自含双阶乘不依赖 stdlib Factorial 名位（提取自足）；          *)
(*    分母面 positive 阶乘（Q 记号 # 的分母须 positive，Pos.of_succ_nat     *)
(*    桥沿 UpReqBanachInst.v:88 在役先例——分母类型即正，诚实面更强）；      *)
(*    后继构造子全资格 Datatypes.S（S01_BaseRing 之 S 常量遮蔽裸 S）。      *)
(*  依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、                      *)
(*    UpReqBanachNormOpp、UpReqIrrationalCriterion、u5c_ln2_gap2_bridge、   *)
(*    u5c_ln2_assembly；Stdlib：QArith/Qabs/ZArith/Arith/Lia/Setoid/Qfield。 *)
(*  对标：BeukersVariant.v §A 级数定形 bv_term n m = C(n+m,n)·B(n+2m+1,     *)
(*    2n+1)（首项 m=0 时 C(n,n)=1，得 B(n+1,2n+1) = n!·(2n)!/(3n+1)!，      *)
(*    即本件见证值）；树内在位支撑＝bv_term_pos（BeukersVariant.v:59）与    *)
(*    pei_beta_value（PadeErrorIntegral.v）；接口形态＝乙件 u5c_gap2_slot   *)
(*    （u5c_ln2_gap2_bridge.v:155）第三肢与第五肢、装配件                   *)
(*    u5c_ln2_assembly_slot（u5c_ln2_assembly.v:166）同名两位。             *)
(*  构造性注记：语句面全 Set 层；见证函数 Defined 透明、自含阶乘 Fixpoint、  *)
(*    提取友好；正性定理为归纳实质推导；实数层锚形迁移肢按 real_lt          *)
(*    定义构造显式分离量见证（取逐点尾锚自带的分离量 d）；数值锚为          *)
(*    计算链判定件（辅助面豁免，沿乙件 θ 锚先例）；零承认、零经典逻辑、     *)
(*    零提取逃逸。                                                          *)
(*  诚实边界：「首项 ≤ 真族载体 I_n」的全正项级数不等式不在本件闭合——       *)
(*    第五肢对具体载体的下界命题以 u5c_ln2_w5_limb（Set 形显式接口参数位）  *)
(*    如实披露：非全局假设，Print Assumptions 仍 Closed。下游使用形＝       *)
(*    u5c_ln2_w5_limb_anchor：只需对每个 n 给出逐点尾锚（存在 d>0，使       *)
(*    I_n 的第 m 项与见证值之差大于 d，m≥1），                              *)
(*    u5c_ln2_witness_limb_of_anchor 即得第五肢（real_lt 左支）；树内       *)
(*    正项级数件 bv_term_pos 的第二项即天然分离量。                         *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" u5c_ln2_witness.v       *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import u5c_ln2_gap2_bridge.
Require Import u5c_ln2_assembly.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith.
From Stdlib Require Import Lia Setoid Qfield.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 见证本体：自含阶乘 + Defined 透明见证函数                            *)
(* ============================================================ *)

(* 自含双阶乘（不依赖 stdlib Factorial 名位，提取自足）：
   分子面 nat 阶乘；分母面 positive 阶乘（Q 记号 # 的分母须 positive，
   Pos.of_succ_nat 桥沿 UpReqBanachInst.v:88 在役先例——分母类型即正，
   诚实面更强）。后继构造子全资格 Datatypes.S——S01_BaseRing 之 S
   常量遮蔽裸 S，池内既录坑位（u5c_aux_natpow.v:39 同款）。 *)
Fixpoint u5c_ln2_wfact (n : nat) : nat :=
  match n with
  | Datatypes.O => 1
  | Datatypes.S k => Datatypes.S k * u5c_ln2_wfact k
  end.

Fixpoint u5c_ln2_wfactp (n : nat) : positive :=
  match n with
  | Datatypes.O => xH
  | Datatypes.S k => Pos.mul (Pos.of_succ_nat k) (u5c_ln2_wfactp k)
  end.

(* 第五肢下界见证：clo_n = n!·(2n)!/(3n+1)!
   ＝Beukers 级数（bv_term）首项 C(n,n)·B(n+1,2n+1)，见头注§三 *)
Definition u5c_ln2_clo_witness (n : nat) : Q :=
  ((Z.of_nat (u5c_ln2_wfact n) * Z.of_nat (u5c_ln2_wfact (2 * n))) #
   (u5c_ln2_wfactp (3 * n + 1)))%Q.

(* ============================================================ *)
(* §1 见证正性（归纳实质推导；乙件 slot 第三肢对见证的无条件闭合）           *)
(* ============================================================ *)

Lemma u5c_ln2_wfact_pos : forall n : nat, (0 < u5c_ln2_wfact n)%nat.
Proof.
  induction n as [| k IH].
  - simpl. apply Nat.lt_0_succ.
  - assert (Hnm : (0 <= k * u5c_ln2_wfact k)%nat) by apply Nat.le_0_l.
    simpl. lia.
Qed.

Theorem u5c_ln2_witness_pos : forall n : nat, QltT 0 (u5c_ln2_clo_witness n).
Proof.
  intro n.
  assert (Ha : (Z.of_nat 0 < Z.of_nat (u5c_ln2_wfact n))%Z).
  { apply Nat2Z.inj_lt. exact (u5c_ln2_wfact_pos n). }
  assert (Hb : (Z.of_nat 0 < Z.of_nat (u5c_ln2_wfact (2 * n)))%Z).
  { apply Nat2Z.inj_lt. exact (u5c_ln2_wfact_pos (2 * n)). }
  assert (Hz : (Z.of_nat 0
                < Z.of_nat (u5c_ln2_wfact n)
                  * Z.of_nat (u5c_ln2_wfact (2 * n)))%Z) by nia.
  apply Qlt_to_QltT.
  unfold Qlt, u5c_ln2_clo_witness.
  cbn [Qnum Qden].
  rewrite Z.mul_0_l, Z.mul_1_r.
  exact Hz.
Qed.

(* ============================================================ *)
(* §2 数值锚（计算链判定件·辅助面豁免）：n=2 时见证值 2!·4!/7! = 1/105      *)
(* ============================================================ *)

Theorem u5c_ln2_witness_2_anchor : QeqT (u5c_ln2_clo_witness 2) (1 # 105)%Q.
Proof.
  unfold QeqT, u5c_ln2_clo_witness.
  vm_compute.
  reflexivity.
Qed.

(* ============================================================ *)
(* §3 实数层锚形迁移肢（real_lt 显式分离量构造；锚形接口见头注·诚实边界）      *)
(* ============================================================ *)

(* 逐点尾锚形：存在分离量 d>0，使载体第 m 项与常值 c 之差大于 d（m≥1） *)
Definition u5c_ln2_w5_anchor (x : Real) (c : Q) : Set :=
  sigT (fun d : Q => And (QltT 0 d)
    (forall m : nat, NatLe 1 m -> QltT d (projT1 x m - c))).

(* 锚形 ⟹ real_lt 左支：exists d 与 N:=1 的显式见证构造 *)
Lemma u5c_ln2_w5_lt_of_anchor : forall (x : Real) (c : Q),
  u5c_ln2_w5_anchor x c -> real_lt (real_const c) x.
Proof.
  intros x c Hanch.
  destruct Hanch as [d [Hd Hpt]].
  unfold real_lt.
  exists d.
  split.
  - exact Hd.
  - exists 1%nat.
    intros m Hm.
    (* projT1 (real_const c) m 与 c 定义性可转换（real_const_proj 以
       reflexivity 证成为凭）；走 exact 转换通道，
       禁对 Qeq 目标裸 rewrite/apply。 *)
    exact (Hpt m Hm).
Qed.

(* ============================================================ *)
(* §4 第五肢接口面与双验收（乙件 slot 与装配件 slot 逐字形态）              *)
(* ============================================================ *)

(* 第五肢残面（见证代入后余留的唯一义务·Set 形显式接口位） *)
Definition u5c_ln2_w5_limb (I : nat -> Real) : Set :=
  forall n : nat, real_le (real_const (u5c_ln2_clo_witness n)) (I n).

(* 第五肢残面的锚形（逐点尾锚版：树内正项级数第二项即天然分离量） *)
Definition u5c_ln2_w5_limb_anchor (I : nat -> Real) : Set :=
  forall n : nat, u5c_ln2_w5_anchor (I n) (u5c_ln2_clo_witness n).

(* 锚形 ⟹ 第五肢（real_lt 左支逐点组装） *)
Theorem u5c_ln2_witness_limb_of_anchor : forall I : nat -> Real,
  u5c_ln2_w5_limb_anchor I -> u5c_ln2_w5_limb I.
Proof.
  intros I Hanch n.
  exact (inl (u5c_ln2_w5_lt_of_anchor (I n) (u5c_ln2_clo_witness n)
               (Hanch n))).
Qed.

(* 验收一（乙件 slot 逐字形态）：见证代入后，第三肢由本件正性定理
   无条件闭合，第五肢化为锚形残面——①②④⑥照旧为参数位 *)
Theorem u5c_ln2_witness_accept :
  forall (X : Real) (A B : nat -> Z) (th : Q) (I : nat -> Real),
    QltT th (1 # 1) ->
    (forall n : nat, QltT 0 (Qabs ((A n) # 1)%Q)) ->
    (forall n : nat, real_eq (I n) (u5c_ln2b_line X A B n)) ->
    (forall n : nat, real_le (I n) (real_const (q_pow th n))) ->
    u5c_ln2_w5_limb I ->
    u5c_gap2_slot X A B u5c_ln2_clo_witness th I.
Proof.
  intros X A B th I Hth Hap Hw Hup Hw5.
  unfold u5c_gap2_slot.
  split.
  - exact Hth.
  - split.
    + exact Hap.
    + split.
      * exact u5c_ln2_witness_pos.
      * split.
        -- exact Hw.
        -- split.
           ++ exact Hw5.
           ++ exact Hup.
Qed.

(* 验收二（装配件 slot 逐字形态）：见证代入后，③位无条件闭合、
   ⑤位化为锚形残面——②②换④缝④焊⑥照旧为参数位 *)
Theorem u5c_ln2_witness_accept_asm :
  forall (X : Real) (Aface Amod Bmod : nat -> Z) (I : nat -> Real),
    (forall n : nat, QltT 0 (Qabs ((Aface n) # 1)%Q)) ->
    (forall n : nat, QeqT ((Aface n) # 1)%Q ((Amod n) # 1)%Q) ->
    (forall n : nat, real_eq (I n) (u5c_ln2b_line X Aface Bmod n)) ->
    (forall n : nat,
        real_eq (u5c_ln2b_line X Aface Bmod n)
                (u5c_ln2b_line X Amod Bmod n)) ->
    (forall n : nat,
        real_le (I n) (real_const (q_pow u5c_lna_theta_mod n))) ->
    u5c_ln2_w5_limb I ->
    u5c_ln2_assembly_slot X Aface Amod Bmod u5c_ln2_clo_witness I.
Proof.
  intros X Aface Amod Bmod I Haf2 HeqAM Hw Hdock Hup Hw5.
  unfold u5c_ln2_assembly_slot.
  split.
  - exact Haf2.
  - split.
    + exact HeqAM.
    + split.
      * exact u5c_ln2_witness_pos.
      * split.
        -- exact Hw.
        -- split.
           ++ exact Hdock.
           ++ split.
              ** exact Hw5.
              ** exact Hup.
Qed.

(* ============================================================ *)
(* §5 提取与假设审计（零承认复核）                                         *)
(* ============================================================ *)

Separate Extraction u5c_ln2_clo_witness u5c_ln2_wfact u5c_ln2_wfactp.

Print Assumptions u5c_ln2_wfact_pos.
Print Assumptions u5c_ln2_witness_pos.
Print Assumptions u5c_ln2_witness_2_anchor.
Print Assumptions u5c_ln2_w5_lt_of_anchor.
Print Assumptions u5c_ln2_witness_limb_of_anchor.
Print Assumptions u5c_ln2_witness_accept.
Print Assumptions u5c_ln2_witness_accept_asm.
