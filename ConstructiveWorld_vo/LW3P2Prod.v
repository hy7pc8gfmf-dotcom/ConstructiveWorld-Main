(* ------------------------------------------------------------------ *)
(* LW3P2Prod.v — M3(e 超越)premise-2 生产端·勘形首件（229 原件） *)
(* 血统/机改清单（沙箱预制 10-01 时窗·16-b∩A4 俱裁生效形）：原名 _tlw229_p2prod.v *)
(*   ＝f6dd9099（CRLF）→486 LF 归一＝4fef2396→合并终值钉见 _tlw493 记录；机改＝头注 *)
(*   重稿（补对标行/构造性注记）＋自名正名；L25-109 字节零改；逻辑名照 446 裁定保留。 *)
(* 五字段｜使命：premise-2 生产端「p(e)=0 前提下 Kinst-Z 不为零解析链」的求值式桥 *)
(*   先行件——lambda 求值式（F(0)-F(Datatypes.S n) 型）与积分机器 LW2IntegMachine *)
(*   端点泛函 lw2_exp_L 的逐值桥（Q 层半边），218 交接段路线（后续）（_tlw218 记录 §六2 alpha）。 *)
(* 构造性注记：语句/前提/断言面全 Set——主句 QeqT（S02 L303 Set 判定）＋实例锚 *)
(*   Id（S01 Set 排序地基）；证明体零等词新断言（apply/rewrite 驱动，库内 Qeq 桥 *)
(*   引理按存量使用登记，见记录 Prop 存量清单节）。 *)
(* 对标行：lw2_lambda/lw2_exp_L（LW2IntegMachine）；lw2_niven_int_f（LW2NivenInt）； *)
(*   lw3_p202/lw3_fbuild（LW3ETranscendental p202）；qeq_imp_qeqT（S02）； *)
(*   交付面三定理＝tlw229_lam_expL（L39）/_niven（L91）/_p202（L98）实例钉。 *)
(* 诚实登记（fail-loud）：Real 层积分算子（积分映 Real 的机器）与 real_deriv 面库无； *)
(*   M0 谱系件 LW0Endpoint（lw0_qp_antideriv/IBP/sin-cos series real_eq 面）在 *)
(*   Live_X 2080 行面，不在本沙箱 Require 闭包（其 real 面另依赖 S10_KVQuantTrig）； *)
(*   本件只闭求值式桥 Q 层半边，Real 层半边与 p(e)=0 使用链候后续段，路线图见记录。 *)
(* 依赖：S01_BaseRing（Id）/S02_CauchyComplete（QeqT+qeq_imp_qeqT）/    *)
(*   S03_QExp/LW0QPoly/LW2Hermite（lambda+eps+qsum0 面）/LW2IntegMachine*)
(*   （lw2_exp_L）/LW2NivenInt（锚例数据）/LW3ETranscendental（p202）。 *)
(* 编译配方：cpu_guard 全包裹（-LoadLimit 60 -CoolSec 5 -CoreN 0），双发复现＋提取取证＋ *)
(*   coqchk；PA=3（L107-109 三锚）预期不变；实录 _g229_* 日志与 229 交付账。 *)
(* ------------------------------------------------------------------ *)
Require Import QArith Arith ZArith List.
From Stdlib Require Import QArith_base.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW2Hermite.
Require Import LW2IntegMachine.
Require Import LW2NivenInt.
Require Import LW3ETranscendental.

(* (i) 一般桥：lambda 求值式与积分机器端点泛函逐值相等——              *)
(* F(0)-F(Datatypes.S n) 型求值式的 Q 层半边（端点表按 eps_eval_sum 摊开，        *)
(* S(Datatypes.S n) 节点上望远镜分解后仅首末两支存活，系数表 k 无关）。           *)
Theorem tlw229_lam_expL : forall (n : nat) (f : QPoly),
  QeqT (lw2_lambda n f)
       (lw2_exp_L (1 # 1)%Q (length f) f (lw2_node (Datatypes.S n))).
Proof.
  intros n f. apply qeq_imp_qeqT.
  unfold lw2_lambda, lw2_exp_L.
  rewrite (lw2_eps_eval_sum (length f) f 0%Q).
  rewrite (lw2_eps_eval_sum (length f) f (lw2_node (Datatypes.S n))).
  transitivity
    (lw2_qsum0 (fun j : nat =>
       (lw2_lambda_coef n j 0 # 1)%Q *
       lw2_qsum0 (fun k : nat =>
         qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) (length f))
       (Datatypes.S (Datatypes.S n)))%Q.
  - apply lw2_qsum0_ext. intros j Hj.
    transitivity
      ((lw2_lambda_coef n j 0 # 1)%Q *
       lw2_qsum0 (fun k : nat =>
         qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) (length f))%Q.
    + transitivity
        (lw2_qsum0 (fun k : nat =>
           (lw2_lambda_coef n j 0 # 1)%Q *
           qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) (length f))%Q.
      * apply lw2_qsum0_ext. intros k Hk. exact (Qeq_refl _).
      * apply lw2_qsum0_scale.
    + exact (Qeq_refl _).
  - cbn [lw2_qsum0].
    rewrite (lw2_qsum0_dirac (Datatypes.S n)
      (fun j : nat => (lw2_lambda_coef n j 0 # 1)%Q *
        lw2_qsum0 (fun k : nat =>
          qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) (length f))).
    + cbv beta.
      unfold lw2_lambda_coef. rewrite !Nat.eqb_refl.
      cbn [Nat.eqb Z.add].
      change (lw2_node 0) with (0 # 1)%Q. ring.
    + apply le_n_S. apply Nat.le_0_l.
    + intros j Hj1 Hj2. destruct (Nat.eqb_spec j 0) as [Hj0 | Hj0].
      * rewrite Hj0 in Hj1. inversion Hj1.
      * destruct (Nat.eqb_spec j (Datatypes.S n)) as [Hjn | Hjn].
        -- rewrite Hjn in Hj2. destruct (Nat.lt_irrefl (Datatypes.S n) Hj2).
        -- unfold lw2_lambda_coef.
           rewrite (proj2 (Nat.eqb_neq j 0) Hj0).
           rewrite (proj2 (Nat.eqb_neq j (Datatypes.S n)) Hjn).
           cbn [Nat.eqb Z.add]. ring.
Qed.

(* 锚例数据面：Niven 源头件 a=1 b=1 n=2（即 t 的 2 次幂乘 (1-t) 的 2 次 *)
(* 幂，系数带 [0;0;1;-2;1]，LW2NivenInt 闭式，纯 Set 数据）。           *)
Definition tlw229_niven : QPoly := lw2_niven_int_f 1%Z 1%Z 2%nat.

(* (ii) Niven 锚例实例钉（Id 面，内核计算归约）：对应 218 件① 工作面  *)
(* 上成立——两侧同归约到同一有理字面（-240 档，对账 F(0)=14、F(3)=254）。*)
Theorem tlw229_lam_expL_niven :
  Id (lw2_exp_L (1 # 1)%Q (length tlw229_niven) tlw229_niven (lw2_node 3))
     (lw2_lambda 2 tlw229_niven).
Proof. vm_compute. apply id_refl. Qed.

(* The recorded zero-instance datum of the case (iii) pin below:      *)
(* p202 = [-46;7], i.e. -46 + 7 t, at exponent N = 1 with Kinst = 0.  *)
Definition lw3_p202 := cons (-46)%Z (cons 7%Z nil).

(* (iii) p202 判例实例钉（Id 面）：202 判例 p202=[-46;7] N=1 的      *)
(* Kinst=0 面上桥亦成立——桥无条件成立，不为生产端非零性背书。           *)
Theorem tlw229_lam_expL_p202 :
  Id (lw2_exp_L (1 # 1)%Q
        (length (lw3_fbuild lw3_p202 (lw3_deg lw3_p202) 1))
        (lw3_fbuild lw3_p202 (lw3_deg lw3_p202) 1)
        (lw2_node (Datatypes.S (lw3_nodecount lw3_p202 1))))
     (lw2_lambda (lw3_nodecount lw3_p202 1)
                 (lw3_fbuild lw3_p202 (lw3_deg lw3_p202) 1)).
Proof. vm_compute. apply id_refl. Qed.

Print Assumptions tlw229_lam_expL.
Print Assumptions tlw229_lam_expL_niven.
Print Assumptions tlw229_lam_expL_p202.
