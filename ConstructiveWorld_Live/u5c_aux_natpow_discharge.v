(* 五字段指针｜使命：u5c_aux_natpow 消解件——
   为已绿源件构建无条件精简版 P'×2：
   u5c_pow12' : forall k : nat, (12 * k * k <= 2 ^ (k + 5))%nat
   u5c_pow4'  : forall k : nat, (4 * k * k <= 2 ^ (k + 3))%nat
   消解依据：原 u5c_pow12/u5c_pow4 的 (1 <= k) 前提系人为限制——k = 0 处
   12·0·0 = 0 ≤ 2^5 = 32 与 4·0·0 = 0 ≤ 2^3 = 8 恒真，陈述无条件化后全域可证。
   非平凡达标方式＝自足全量归纳（禁「exact 前提版拼接」形，全程不使用带前提的
   u5c_pow12/u5c_pow4）：k = 0 与 k = 1,2,3 基座逐点数值计算收尾，k ≥ 4 步进以
   (k+1)² ≤ 2k²（nia 拆积原子化后 lia 线性收尾）接归纳假设，步进改写复用已绿
   u5c_pow2_shift（reflexivity 换算件，Datatypes.S 全资格）。
   消解登记（诚实接口·一行）：u5c_pow64 的 (1 <= k) 系数学必需——k = 0 处
   64 ≤ 2^5 = 32 为假，边缘即假不可消解，登记保留；下游逃逸点
   n0 = den(q) + 3 ≥ 4 使用恒在前提域内，不受影响。
   依赖：池内已绿 u5c_aux_natpow（u5c_pow2_shift，只读 Require）；Stdlib Lia。
   构造性注记：消解证体自足全量归纳（非平凡达标方式如上），陈述无条件化后全域可证；
   零承认、零经典、零全局假设。
   编译配方：source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh
   后于池目录 rocq c -native-compiler no -q -Q . "" u5c_aux_natpow_discharge.v。 *)

(* Require 序沿已绿源件（在册库件链在前、Stdlib 在后）：nat 幂记法 `_ ^ _`
   的 nat_scope 解释面由该链供给（实测单 Require u5c_aux_natpow + Lia 不足）。 *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import u5c_aux_natpow.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* P'-1：无条件 12 二次界                                              *)
(* ============================================================ *)

(* 12k² ≤ 2^(k+5) 对一切 k（含 k = 0）。全量归纳自足：基座 k=0 数值收尾，
   k=1,2,3 逐点计算，k≥4 步进 nia 拆积 (k+1)² ≤ 2k² 后接 IH 线性收尾。 *)
Lemma u5c_pow12' : forall k : nat, (12 * k * k <= 2 ^ (k + 5))%nat.
Proof.
  intro k.
  induction k as [| k IH].
  - cbn. lia.
  - destruct k as [|[|[|k]]].
    + cbn. lia.
    + cbn. lia.
    + cbn. lia.
    + rewrite !u5c_pow2_shift in IH.
      rewrite !u5c_pow2_shift.
      assert (E1 : (12 * Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k))) * Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))
                    <= 2 * (12 * Datatypes.S (Datatypes.S (Datatypes.S k)) * Datatypes.S (Datatypes.S (Datatypes.S k))))%nat) by nia.
      lia.
Qed.

(* ============================================================ *)
(* P'-2：无条件 4 二次界                                               *)
(* ============================================================ *)

(* 4k² ≤ 2^(k+3) 对一切 k（含 k = 0）。与 12 界同构全量归纳：
   (k+3)² ≤ 2(k+2)² 对 k ≥ 0 恒真保步进，基座逐点计算。 *)
Lemma u5c_pow4' : forall k : nat, (4 * k * k <= 2 ^ (k + 3))%nat.
Proof.
  intro k.
  induction k as [| k IH].
  - cbn. lia.
  - destruct k as [|[|[|k]]].
    + cbn. lia.
    + cbn. lia.
    + cbn. lia.
    + rewrite !u5c_pow2_shift in IH.
      rewrite !u5c_pow2_shift.
      assert (E1 : (4 * Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k))) * Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))
                    <= 2 * (4 * Datatypes.S (Datatypes.S (Datatypes.S k)) * Datatypes.S (Datatypes.S (Datatypes.S k))))%nat) by nia.
      lia.
Qed.

Print Assumptions u5c_pow12'.
Print Assumptions u5c_pow4'.
