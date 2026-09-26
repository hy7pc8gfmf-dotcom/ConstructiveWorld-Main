(* ==========================================================================)
   ToyR_AbsLeId.v — 绝对值恒等引理的抽象层兑现
   使命: ali_abs_ge_zero_id（le zero a -> Id (abs a) a，DecidableOrder 三分编码下构造消去）、对称形 ali_abs_ge_zero_id_sym、乘法兼容 ali_abs_id_mult_l/r，及具体 Real 层兑现 ali_real_abs_ge_zero_id。
   依赖: S01_BaseRing、fa53_compat_abs、S02_CauchyComplete、S03_QExp、S07_RealSetoidExpLog。
   对标: abs_ge_zero_id 槽（S06_DiffSamplingGibbs:4035）的 le 版真引理；抽象层同形件为 fa53_compat_abs。
   构造性: 语句面全 Set 层（Or/Not 用 S01 Set 层定义）；零承认词面、无经典逻辑；fa53_compat_abs 只 Require 不改。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树原地重编），cpu_guard 包裹限载。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import fa53_compat_abs.

(* ============ 第一层：抽象接口层（S06:4035 槽语句形） ============ *)
(* 与 fa53 同款上下文（RI_base :> RealInterface 子类投影 +        *)
(* Existing Instance 解析裸名；DO 为可选可判定序扩展类）。          *)
Section AbsLeIdAbstract.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* ---- 主件：abs_ge_zero_id_cc 槽语句同形（A 类核验引用 fa53 件3） ---- *)
Theorem ali_abs_ge_zero_id : forall a : R, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI DO a Ha).
Qed.

(* ---- 反向形：le zero a -> a == |a|（rewrite 另一向所需） ---- *)
Theorem ali_abs_ge_zero_id_sym : forall a : R, le zero a -> Id a (abs a).
Proof.
  intros a Ha.
  exact (id_sym (ali_abs_ge_zero_id a Ha)).
Qed.

(* ---- 依存位封装形（左乘位）：S06:4371 直接匹配 ----
   该处原文 id_cong (fun x => mult (abs (f s)) x)
                    (abs_ge_zero_id_cc (q_kernel s s') (q_kernel_nonneg s s'))
   ——本件把 id_cong 拼好，下游一步喂。 *)
Theorem ali_abs_id_mult_l : forall a b : R, le zero a -> Id (mult (abs a) b) (mult a b).
Proof.
  intros a b Ha.
  exact (id_cong (fun w => mult w b) (ali_abs_ge_zero_id a Ha)).
Qed.

(* ---- 依存位封装形（右乘位）：S06:4447 直接匹配 ---- *)
Theorem ali_abs_id_mult_r : forall a b : R, le zero b -> Id (mult a (abs b)) (mult a b).
Proof.
  intros a b Hb.
  exact (id_cong (fun w => mult a w) (ali_abs_ge_zero_id b Hb)).
Qed.

End AbsLeIdAbstract.

(* ============ 第二层：具体 Real 层兑现 ============ *)
(* 柯西实数层（S02 Real := sigT (fun u : Qseq => cauchy u)）：     *)
(* real_le = Or real_lt real_eq（S02:469，Set 层 Or）两支分决。    *)
(* 注意此处 Require 置于抽象节之后，避免具体层名遮蔽接口投影名。    *)
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.

Theorem ali_real_abs_ge_zero_id :
  forall a : Real, real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  intros a H.
  unfold real_le in H.
  destruct H as [Hlt | Heq].
  - (* 0 < a：严格版逐点件直给（S07:7289） *)
    exact (real_abs_pos_req a Hlt).
  - (* 0 == a：|a| ≈ |0| ≈ 0 ≈ a（compat + zero_req + sym 链） *)
    apply (real_eq_trans _ (real_abs real_zero)).
    + apply (RealSetoid.real_eq_abs_compat a real_zero).
      apply real_eq_sym.
      exact Heq.
    + apply (real_eq_trans _ real_zero).
      * exact real_abs_zero_req.
      * exact Heq.
Qed.

(* ---- G1 内嵌自检段（文件内显式 PA 声明，min-pa≥1） ---- *)
Print Assumptions ali_abs_ge_zero_id.
Print Assumptions ali_abs_ge_zero_id_sym.
Print Assumptions ali_abs_id_mult_l.
Print Assumptions ali_abs_id_mult_r.
Print Assumptions ali_real_abs_ge_zero_id.
