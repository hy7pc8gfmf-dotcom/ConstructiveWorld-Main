(* ============================================================
   AbsLeId —— 使命行：本件构造前期核验遗留真缺口的构造性兑现：为
   S06_DiffSamplingGibbs 的 abs_ge_zero_id_cc 接口参数位
   （forall a, le zero a -> Id (abs a) a，Let 别名展开后
   = forall a : @R (@RI_base RI), @le (@RI_base RI) ...）给出
   抽象接口层主定理与具体 Real 层兑现。
   依赖：S01_BaseRing、fa53_compat_abs、S02_CauchyComplete、
   S03_QExp、S07_RealSetoidExpLog。
   对标：fa53_compat_abs.v 件3 fa53_abs_ge_zero_id_dec——语句面
   同形（le zero a -> Id (abs a) a），前提是可选扩展类
   DecidableOrder（S01:329，Set 层 Or 三分）；本件主件按引用
   复用（只 Require 不改）；另交付：(a) 反向形
   ali_abs_ge_zero_id_sym（id_sym 运河）；(b) S06 两个使用位
   封装形 ali_abs_id_mult_l/r（S06:4371 与 S06:4447 的
   id_cong 直接匹配件，免下游再拼 id_cong）；(c) 具体 Real 层
   兑现 ali_real_abs_ge_zero_id：real_le 的 Or 编码（S02:469）
   两支分决——lt 支走 real_abs_pos_req（S07:7289），eq 支走
   real_eq_abs_compat（S07:410，Module RealSetoid 内须限定）
   + real_abs_zero_req（S07:7266）+ real_eq_sym/trans 三步链。
   构造性注记：语句面全 Set 层（Or/Not 用 S01:67-68 Set 层定义，
   real_lt 为 sigT 见证 S02:465）；零 Prop 泄露；
   无 公理/承认件/参数/猜想/弃证；
   fa53_compat_abs 只 Require 引用零改；原树零改。
   前缀 ali_ 全库防撞已核。
   编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），
   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行。
   ============================================================ *)

Require Import S01_BaseRing.
Require Import fa53_compat_abs.

(* ============ 第一层：抽象接口层（S06:4035 语句形） ============ *)
(* 与 fa53 同款上下文（RI_base :> RealInterface 子类投影 +        *)
(* Existing Instance 解析裸名；DO 为可选可判定序扩展类）。          *)
Section AbsLeIdAbstract.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* ---- 主件：abs_ge_zero_id_cc 语句同形（复用 fa53 件3） ---- *)
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

(* ---- 使用位封装形（左乘位）：S06:4371 直接匹配 ----
   该处原文 id_cong (fun x => mult (abs (f s)) x)
                    (abs_ge_zero_id_cc (q_kernel s s') (q_kernel_nonneg s s'))
   ——本件把 id_cong 拼好，下游一步喂。 *)
Theorem ali_abs_id_mult_l : forall a b : R, le zero a -> Id (mult (abs a) b) (mult a b).
Proof.
  intros a b Ha.
  (* id_cong 隐参 x,y 由 p 端点定（abs a / a），f 须在乘法首参处改写 *)
  exact (id_cong (fun w => mult w b) (ali_abs_ge_zero_id a Ha)).
Qed.

(* ---- 使用位封装形（右乘位）：S06:4447 直接匹配 ---- *)
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

(* ---- 自检段：文件内显式 Print Assumptions 声明 ---- *)
Print Assumptions ali_abs_ge_zero_id.
Print Assumptions ali_abs_ge_zero_id_sym.
Print Assumptions ali_abs_id_mult_l.
Print Assumptions ali_abs_id_mult_r.
Print Assumptions ali_real_abs_ge_zero_id.
