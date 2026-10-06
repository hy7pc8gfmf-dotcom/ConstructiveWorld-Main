(* ===================================================================== *)
(*  abl_ln2_integmachine_bridge.v —— LW2IntegMachine→ln2 路线④           *)
(*  桥接件（跨线互补主桥·联合基线 #187·CH 协议对应形）                    *)
(*  模块名：abl_ln2_integmachine_bridge.                                 *)
(*  使命: 同事塔 LW2IntegMachine（e^{-t}-核端点泛函机，197 行/9 Qed）      *)
(*    桥接进本地 ln2 路线④——「库内无 Real 积分机」缺口的无权重            *)
(*    替代通路：端点泛函 lw2_exp_L E K f X := eps K f (0) − E·eps K f (X) *)
(*    代数化积分语义，权函数只以显式标量 E 存活，零积分对象入库。          *)
(*    勘定: 本机与本地 pint 逐项定积分机（PolyIntegral）及 lnw 有理求和    *)
(*    容器是互补而非重复——两套代数化在同为 (1+t)·t^k 核数据上给出两个     *)
(*    互异闭值（锚件 lni2_pair_w00/w22 实拍：pint 面 3/4·7/16 对机面      *)
(*    1/4·(−5/16)，隙 1/2·3/4 皆 Q 判定），机面不声称等于积分读数。        *)
(*  新数学: ①燃料规范化消解——同事机全族 K≥length f 的 nat 序前提位        *)
(*    当场消解：定 K:=length f 为规范燃料（lni2_exp_L），机递归/双线性/    *)
(*    闭形四律重述为**零前提** QeqT 语句（§A，Prop 前提位=0）；②lnw 核    *)
(*    数据注册——lnw_wcore 的 (1+t)t^k/2^{k+1} 核多项式（lni2_lnw_wpoly，  *)
(*    低位在前 QPoly 编码）输入端点泛函机：双线性律把核拆两肢（§B 结构件）  *)
(*    ＋四锚件 vm_compute 全数值判定（§B 计算件）——同事面（lw2_eps/       *)
(*    lw2_exp_int_parts/lw2_exp_L_add/scalar/closed_form）与本地面        *)
(*    （lnw_wterm/lnw_anchor_w22）同语句真使用，非转述。                   *)
(*  依赖: Stdlib QArith/List/Arith/ZArith/Lia；S01_BaseRing S02_Cauchy-  *)
(*    Complete S03_QExp（QeqT/And Set 面）；**同事塔拷贝** LW0QPoly        *)
(*    LW2Hermite LW2IntegMachine（md5 6f836288/7b6d5d71/1d1408ea 与        *)
(*    ConstructiveWorld-Main 塔源逐字节同）；本地链拷贝 abl_ln2_tail_bound *)
(*    abl_ln2_sharp_weight（#187 Live 源；池内平铺 Require）。              *)
(*  对标: Hermite 1873 端点收敛术（C. R. Acad. Sci. Paris 77）的机内化；   *)
(*    Beukers 1979 ln2 锐权变体（lnw 系）的姊妹代数化；有理求和版          *)
(*    降档的对接位——IBP 机=积分语义代数化替代（对拍表见交付报告）。         *)
(*  构造性: 纯构造性、零公理/零承认件；语句面全 Set（QeqT/S01 And 积），   *)
(*    载体面全 Set（QPoly/Q/nat）；同事件 Prop 面 `==`（Qeq）仅证体内作    *)
(*    推理使用、经 qeq_imp_qeqT 吸收入 QeqT 语句面；新立假设位=0（燃料     *)
(*    规范化消解 K≥length f 前提，无悬置）；文尾 Print Assumptions 全      *)
(*    Closed＋独立提取验证。                                              *)
(*  编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&      *)
(*    ulimit -s 65532 && nice -19 rocq c -native-compiler no              *)
(*    -Q <vo_local_world_unified_0930> "" -Q . ""（编译目录=本池，链序     *)
(*    LW0QPoly→LW2Hermite→LW2IntegMachine→tail_bound→sharp_weight→本件，  *)
(*    道闸≤1 单道串行）。                                                 *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import LW0QPoly LW2Hermite LW2IntegMachine.
Require Import abl_ln2_tail_bound abl_ln2_sharp_weight.

Open Scope nat_scope.

(* ============================================================ *)
(* §A 链吸收·燃料规范化：同事端点泛函机的零前提 Set 面重述           *)
(*    （三道门之三「从严 Prop 门」的吸收执行位）                     *)
(* ============================================================ *)

(* 规范燃料端点泛函：定 K := length f。同事机全族语句的前提位
   (length f <= K)%nat 由燃料取齐**当场消解**——K 是机器的表深燃料，
   lw2_exp_L_fuel 保证 K ≥ length f 时值与表深无关，故取 length f
   为规范代表不损失任何机器值；此后本件语句零前提。 *)
Definition lni2_exp_L (E : Q) (f : QPoly) (X : Q) : Q :=
  lw2_exp_L E (length f) f X.

(* 零多项式基例（Set 面）：机在零多项式上积零。 *)
Lemma lni2_exp_L_nil_T : forall (E : Q) (X : Q),
  QeqT (lni2_exp_L E nil X) 0%Q.
Proof.
  intros E X. apply qeq_imp_qeqT. unfold lni2_exp_L.
  apply lw2_exp_L_nil.
Qed.

(* 主件吸收：IBP 一步递归（燃料规范形）——
   L f == f(0) − E·f(X) + L f'，零前提。同事前提 (length f <= K) 在
   K := length f 处取 le_n 消解；f' 侧经 lw2_len_deriv + fuel 律归位。 *)
Lemma lni2_exp_L_parts_T : forall (E : Q) (f : QPoly) (X : Q),
  QeqT (lni2_exp_L E f X)
    ((qpoly_eval f 0%Q - E * qpoly_eval f X
      + lni2_exp_L E (qpoly_deriv f) X)%Q).
Proof.
  intros E f X. apply qeq_imp_qeqT. unfold lni2_exp_L.
  rewrite (lw2_exp_int_parts E (length f) f X (le_n (length f))).
  rewrite <- (lw2_exp_L_fuel E (length f) (qpoly_deriv f) X (lw2_len_deriv f)).
  reflexivity.
Qed.

(* 双线性·加法肢（Set 面，零前提）：机对多项式加法可加。
   燃料面经 lw2_len_add_max 取 max 为公共表深，两肢各 fuel 归位。 *)
Lemma lni2_exp_L_add_T : forall (E : Q) (u v : QPoly) (X : Q),
  QeqT (lni2_exp_L E (qpoly_add u v) X)
       ((lni2_exp_L E u X + lni2_exp_L E v X)%Q).
Proof.
  intros E u v X. apply qeq_imp_qeqT. unfold lni2_exp_L.
  rewrite (lw2_len_add_max u v).
  rewrite (lw2_exp_L_add E (Nat.max (length u) (length v)) u v X).
  rewrite (lw2_exp_L_fuel E (Nat.max (length u) (length v)) u X
             (Nat.le_max_l (length u) (length v))).
  rewrite (lw2_exp_L_fuel E (Nat.max (length u) (length v)) v X
             (Nat.le_max_r (length u) (length v))).
  reflexivity.
Qed.

(* 双线性·齐次肢（Set 面，零前提）：机对 Q 标量齐次。 *)
Lemma lni2_exp_L_scalar_T : forall (E : Q) (c : Q) (f : QPoly) (X : Q),
  QeqT (lni2_exp_L E (qpoly_scalar c f) X) ((c * lni2_exp_L E f X)%Q).
Proof.
  intros E c f X. apply qeq_imp_qeqT. unfold lni2_exp_L.
  rewrite lw2_len_scalar.
  rewrite (lw2_exp_L_scalar E (length f) c f X).
  reflexivity.
Qed.

(* 闭形（Set 面，零前提）：机值 == 端点导数表组合
   Σ_{k<length f} f^{(k)}(0) − E·Σ_{k<length f} f^{(k)}(X)——
   无穷远只经显式标量 E 进入，无任何极限构造。 *)
Lemma lni2_exp_L_closed_T : forall (E : Q) (f : QPoly) (X : Q),
  QeqT (lni2_exp_L E f X)
    ((lw2_qsum0 (fun k : nat => qpoly_eval (qpoly_deriv_iter k f) 0%Q) (length f)
      - E * lw2_qsum0 (fun k : nat => qpoly_eval (qpoly_deriv_iter k f) X)
               (length f))%Q).
Proof.
  intros E f X. apply qeq_imp_qeqT. unfold lni2_exp_L.
  apply lw2_exp_L_closed_form.
Qed.

(* ============================================================ *)
(* §B lnw 核数据注册：真使用示范（同事机 × 本地锐权件）              *)
(* ============================================================ *)

(* 单项式 t^k：低位在前 QPoly 编码（LW0QPoly 约定：首项常数、
   eval (a::p) x = a + x·eval p x）。 *)
Fixpoint lni2_mono (k : nat) : QPoly :=
  match k with
  | Datatypes.O => (1 # 1)%Q :: nil
  | Datatypes.S k' => (0 # 1)%Q :: lni2_mono k'
  end.

(* lnw 权核多项式：(1+t)·t^k/2^{k+1}——即 lnw_wcore k 的被积函数
   ∫₀¹(1+t)·(1/2^{k+1})·t^k dt 的 QPoly 数据面（lnw_pint_wcore 的
   pint 读数与机面共同使用的同一数据对象）。 *)
Definition lni2_lnw_wpoly (k : nat) : QPoly :=
  qpoly_scalar ((1 # 1)%Q / q_pow (2 # 1)%Q (Datatypes.S k))
    (qpoly_add (lni2_mono k) (lni2_mono (Datatypes.S k))).

(* 结构件①（双线性拆肢）：机在 lnw 核多项式上的值按 (1+t) 两肢
   显式拆解——同事双线性律（经 §A Set 面吸收）使用本地核数据。
   E := 1/2 为显式有理标量权槽（2 幂几何核的规范取档；e^{-1} < 1/2
   的上档替代，机面不声称等于积分读数）。 *)
Lemma lni2_lnwpoly_limbs : forall (E : Q) (k : nat) (X : Q),
  QeqT (lni2_exp_L E (lni2_lnw_wpoly k) X)
    ((((1 # 1)%Q / q_pow (2 # 1)%Q (Datatypes.S k))
        * lni2_exp_L E (lni2_mono k) X
      + ((1 # 1)%Q / q_pow (2 # 1)%Q (Datatypes.S k))
        * lni2_exp_L E (lni2_mono (Datatypes.S k)) X)%Q).
Proof.
  intros E k X. apply qeq_imp_qeqT.
  unfold lni2_lnw_wpoly.
  pose proof (qeqT_imp_qeq _ _
    (lni2_exp_L_scalar_T E ((1 # 1)%Q / q_pow (2 # 1)%Q (Datatypes.S k))
       (qpoly_add (lni2_mono k) (lni2_mono (Datatypes.S k))) X)) as Hs.
  pose proof (qeqT_imp_qeq _ _
    (lni2_exp_L_add_T E (lni2_mono k) (lni2_mono (Datatypes.S k)) X)) as Ha.
  rewrite Hs. rewrite Ha. ring.
Qed.

(* 计算锚①：机面在 lnw 核 k=0 数据（(1+t)/2）上全数值判定——
   eps(0)=1、eps(1)=3/2、E=1/2 ⟹ 1 − 3/4 = 1/4（vm_compute 即编译）。 *)
Theorem lni2_anchor_machine_w00 :
  QeqT (lni2_exp_L (1 # 2)%Q (lni2_lnw_wpoly 0) 1%Q) (1 # 4)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 计算锚②：机面在 lnw 核 k=2 数据（(1+t)t²/8）上全数值判定——
   eps(0)=1、eps(1)=21/8、E=1/2 ⟹ 1 − 21/16 = −5/16（vm_compute 即编译）。
   负值实拍：机面（IBP 端点组合）非 pint 积分读数的再编码。 *)
Theorem lni2_anchor_machine_w22 :
  QeqT (lni2_exp_L (1 # 2)%Q (lni2_lnw_wpoly 2) 1%Q) ((-5 # 16)%Q).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 对拍锚①（k=0 双面配对·S01 Set 积语句）：pint/lnw 面 w(0,0)=3/4 与
   机面 1/4 在同一核数据上互异闭值共存，隙 3/4 − 1/4 = 1/2 判定——
   IBP 机=积分语义的代数化替代而非重复（防重复三闸的机器证）。 *)
Theorem lni2_pair_w00 :
  And (QeqT (lnw_wterm 0 0) (3 # 4)%Q)
      (QeqT ((lnw_wterm 0 0
               - lw2_exp_L (1 # 2)%Q (length (lni2_lnw_wpoly 0))
                   (lni2_lnw_wpoly 0) 1%Q)%Q) (1 # 2)%Q).
Proof.
  split.
  - apply lnw_anchor_w00.
  - apply qeq_imp_qeqT. vm_compute. reflexivity.
Qed.

(* 对拍锚②（k=2 双面配对·S01 Set 积语句）：lnw 面 w(2,2)=7/16 与
   同事塔生面 lw2_exp_L（显式 K=length 数据，非规范燃料形）机值
   −5/16 配对，隙 7/16 − (−5/16) = 3/4 判定——同事面直接使用本地
   lnw_wterm 数据（真使用非转述），E=1/2、K=4 下两代数化互异。 *)
Theorem lni2_pair_w22 :
  And (QeqT (lnw_wterm 2 2) (7 # 16)%Q)
      (QeqT ((lnw_wterm 2 2
               - lw2_exp_L (1 # 2)%Q (length (lni2_lnw_wpoly 2))
                   (lni2_lnw_wpoly 2) 1%Q)%Q) (3 # 4)%Q).
Proof.
  split.
  - apply lnw_anchor_w22.
  - apply qeq_imp_qeqT. vm_compute. reflexivity.
Qed.

(* ============================================================ *)
(* §D 假设审计与独立提取（构造性验证位）                             *)
(* ============================================================ *)

Print Assumptions lni2_exp_L_nil_T.
Print Assumptions lni2_exp_L_parts_T.
Print Assumptions lni2_exp_L_add_T.
Print Assumptions lni2_exp_L_scalar_T.
Print Assumptions lni2_exp_L_closed_T.
Print Assumptions lni2_lnwpoly_limbs.
Print Assumptions lni2_anchor_machine_w00.
Print Assumptions lni2_anchor_machine_w22.
Print Assumptions lni2_pair_w00.
Print Assumptions lni2_pair_w22.

From Stdlib Require Import Extraction.
Separate Extraction lni2_exp_L_nil_T lni2_exp_L_parts_T lni2_exp_L_add_T
  lni2_exp_L_scalar_T lni2_exp_L_closed_T lni2_lnwpoly_limbs
  lni2_anchor_machine_w00 lni2_anchor_machine_w22
  lni2_pair_w00 lni2_pair_w22.
