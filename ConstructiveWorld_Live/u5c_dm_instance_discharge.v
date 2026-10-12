(* 五字段指针｜使命：tdm225 消解件——u5c_dm_escape_window 两前提语句的
   实例点无条件 P'×2＋四件无条件形审计申报。
   依据：诚实接口律与实质律——全部假设消解以非平凡供给定理承载。
   依赖：池内在册件只读 Require——S01_BaseRing、S02_CauchyComplete、S03_QExp、
   SumInvFactEscape、UpReqBanachNormOpp、UpReqIrrationalCriterion、UpReqSqrt3Irrational、
   u5c_dm_escape_window（本件使用）；Stdlib QArith、Qabs、ZArith、Arith、Bool、Lia、
   Setoid、Morphisms、Qfield。
   对标行：u5c_dm_escape_window.v dmew_delta_pow_inv（113）/dmew_e_bnd（131）/
   dmew_escape_closed_window Hb0+Hn1 实例（178–183）/Hq12 实例（193–194）/Hdn 使用点（290–295）。
   构造性注记：两 P' 语句面全 Set 层（QleT'），零承认、零经典逻辑、零全局假设位；
   证明体实质推导链＝Qinv 换算（Pos2Z.inj_mul 双反改写→dmew_Qinv_1p）＋Z2Nat 数值实例
   （正数型 to_nat≥1 的构造子归约反驳，Hn1 实例）＋已绿件实例点供给（非空壳）。
   ── P' 实形偏差登记（诚实接口）：裸 `Z.to_nat b`（b:positive）无 positive→Z coercion
   不可编译——语句面按实际编译口径取 Z.to_nat (Z.pos b)（在册件先例形），
   P' 实质（无 n0 前提形）不变。
   ── dmew_delta_pow_inv 原件 (1<=n) 前提登记：n=0 处 δ(0)=2>2^0=1 假——
   前提系数学必需，原件不可建全量无条件形；本件 dmew_delta_pow_inv' 为使用点实例形
   （n0=den(q)+3≥4，前提在该实例点由 Hn1 数值推导非平凡消解，非人为限制）。
   编译配方：source Live/toolchain/env.sh 后
   rocq c -native-compiler no -q -Q . "" u5c_dm_instance_discharge.v。 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqSqrt3Irrational.
Require Import u5c_dm_escape_window.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* P'一：dmew_e_bnd 实例点无条件形（n0 := den(b)+3 内部实例化）           *)
(*   原件前提 (Z.to_nat (Z.pos b) + 3 <= n) 系人为限制（语句内容本身），      *)
(*   在实例点 n := n0 处由 Nat.le_refl 消解。                            *)
(* ============================================================ *)

Lemma dmew_e_bnd' : forall b : positive,
  QleT' (ir2_e (Z.to_nat (Z.pos b) + 3)%nat) ((1 # (12 * (b * b)))%Q).
Proof.
  intro b.
  assert (Hq12 : Qinv ((12 * (Z.pos b * Z.pos b)) # 1) == (1 # (12 * (b * b)))%Q)
    by (rewrite <- (Pos2Z.inj_mul b b), <- (Pos2Z.inj_mul 12 (b * b));
        apply qeqT_imp_qeq; apply dmew_Qinv_1p).
  pose proof (dmew_e_bnd b (Z.to_nat (Z.pos b) + 3)%nat
                (Nat.le_refl (Z.to_nat (Z.pos b) + 3))) as He.
  (* 最小适配注记：dmew_Qinv_1p 现势面为 QeqT 形（窗内 :196 绿链同款
     qeqT_imp_qeq 桥）；Qeq 桥不可 rewrite 进 QleT'（无 morphism 实例，:44/:48
     失配源）——降 Qle 层 Qle_trans＋qeq_le 过桥再升回。 *)
  pose proof (QleT'_to_Qle _ _ He) as Hel.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qinv ((12 * (Z.pos b * Z.pos b)) # 1))).
  - exact Hel.
  - apply qeq_le. exact Hq12.
Qed.

(* ============================================================ *)
(* P'二：dmew_delta_pow_inv 使用点实例形（n0 := den(b)+3，前提数值消解）     *)
(*   原件 (1<=n) 系数学必需（n=0 处 δ(0)=2>1 假，头注已登记）；使用点 n0≥4      *)
(*   处前提由 Hn1（Z2Nat 数值实例）非平凡推导，语句面无前提。                     *)
(* ============================================================ *)

Lemma dmew_delta_pow_inv' : forall b : positive,
  QleT' (ir2_delta (Z.to_nat (Z.pos b) + 3)%nat)
        (Qinv ((Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 3)%nat)) # 1)).
Proof.
  intro b.
  assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (Hn1 : (1 <= Z.to_nat (Z.pos b))%nat).
  { destruct (Z.to_nat (Z.pos b)) as [|t] eqn:Et; [ | lia].
    exfalso. pose proof (Z2Nat.id (Z.pos b) (Z.lt_le_incl 0 (Z.pos b) Hb0)) as Hz.
    rewrite Et in Hz. cbn [Z.of_nat] in Hz. discriminate. }
  (* 最小适配注记：dmew_delta_pow_inv 现势结论面已直接为 QleT'
     （窗 :113-114），旧形 Qle→QleT' 升转换摘除，直接实例。 *)
  apply (dmew_delta_pow_inv (Z.to_nat (Z.pos b) + 3)%nat). lia.
Qed.

Print Assumptions dmew_e_bnd'.
Print Assumptions dmew_delta_pow_inv'.
