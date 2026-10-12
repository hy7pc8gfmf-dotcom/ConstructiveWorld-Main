(* 五字段指针｜使命：「√2 闭式分离常元」新数学件的 nat 幂界与 Q 微转换基础库——
   A 组四件 nat 幂界（12k² ≤ 2^(k+5)、4k² ≤ 2^(k+3)、2k < 2^(k+5)、64 ≤ 2^(k+5)，
   k ≥ 1）为下游四分支边距链提供整数指数上的定量衔接：δ<μ 由 4b² ≤ 2^(b+3)
   导出、逃逸点一致量化 e(n0) ≤ 2^−(b+5)（n0 = b+3 ≥ 4）皆使用于此。
   B 组四件 Q 微转换（加法右消去、减法非负、Qle ↔ QleT' 双向桥）在 Qle 的
   证明体推理与 Set 层判定承载 QleT' 之间提供逐点无损改写。全件为下游各件
   装配显式无理性测度 c(q) = 1/(12b²) 的公共基础件。
   依赖：池内 S01_BaseRing、S02_CauchyComplete（QleT'/Qle_bool/Qcompare
   定义面，只读引用）；Stdlib QArith、ZArith、Lia（nia）。
   对标行：S02_CauchyComplete.v Qle_to_QleT'、QleT'_to_Qle、qeq_imp_qle；
   任务指令 §2 四分支边距链（μ−δ 分支 4b² ≤ 2^(b+3) 衔接位、n0 = den(q)+3
   一致逃逸点）。
   构造性注记：语句面沿池内 lic_escape_window 先例，(1 <= k)%nat 与 Qle 前提
   经 Prop⊆Set 累积性入 Set 位；承载位（QleT'、nat 算术）全 Set 层。
   A 组以归纳法证明：基座 k = 1,2,3 逐点数值计算收尾，步进改写
   2^(S k + c) = 2·2^(k + c)（换算件 reflexivity 可判），末端乘积切割
   交 nia。B 组沿 Qcompare 三分支构造性判定：Qle 展开为 Z 交叉积比较后
   以 Z 正分母（Qden > 0）切割，Zpos(Pos.mul ·) 经 Pos2Z.inj_mul 归一为
   Z 乘积；双向桥走 Qle_bool 展开分情况，不需 Leibniz 相等。
   lia/nia 使用范围限辅助界与微改写（任务指令 A 组点名形），触发例外册
   lia/lra 存量冻结条款的触碰重认证义务，本件响亮登记；零承认、零经典、
   零全局假设。
   诚实接口披露：任务指令原列 u5c_pow64 无前提形在 k = 0 处为假
   （2^5 = 32 < 64），本件依律五增补前提 (1 <= k)%nat；下游逃逸点
   n0 = den(q) + 3 ≥ 4 使用不受影响。
   编译配方：source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh
   后于池目录 rocq c -native-compiler no -q -Q . "" u5c_aux_natpow.v。 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* A 组：nat 幂界（12 的二次界 / 4 的二次界 / 2k 界 / 64 界）          *)
(* ============================================================ *)

(* 步进换算：2 的幂对指数后继的折乘（nat 加法与幂的定义性换算）。
   后继全资格写 Datatypes.S：S01_BaseRing 之 S 常量遮蔽裸 S，故全资格书写。 *)
Lemma u5c_pow2_shift : forall k c : nat, (2 ^ (Datatypes.S k + c) = 2 * 2 ^ (k + c))%nat.
Proof. intros k c. reflexivity. Qed.

(* 归纳基：2^(k+5) 恒不低于 32（归纳于 k，每步折乘不减） *)
Lemma u5c_pow32 : forall k : nat, (32 <= 2 ^ (k + 5))%nat.
Proof.
  induction k as [| k IH].
  - cbn. lia.
  - rewrite u5c_pow2_shift. lia.
Qed.

(* 12 的二次界：12k² ≤ 2^(k+5)（k ≥ 1）。二次增长被指数翻倍吞没：
   k ≥ 4 时 (k+1)² ≤ 2k² 保步进，k = 1,2,3 逐点计算。 *)
Lemma u5c_pow12 : forall k : nat, (1 <= k)%nat -> (12 * k * k <= 2 ^ (k + 5))%nat.
Proof.
  intro k.
  induction k as [| k IH]; intro Hk.
  - lia.
  - destruct k as [|[|[|k]]].
    + cbn. lia.
    + cbn. lia.
    + cbn. lia.
    + assert (Hk' : (1 <= Datatypes.S (Datatypes.S (Datatypes.S k)))%nat) by lia.
      specialize (IH Hk').
      rewrite !u5c_pow2_shift in IH.
      rewrite !u5c_pow2_shift.
      assert (E1 : (12 * Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k))) * Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))
                    <= 2 * (12 * Datatypes.S (Datatypes.S (Datatypes.S k)) * Datatypes.S (Datatypes.S (Datatypes.S k))))%nat) by nia.
      lia.
Qed.

(* 4 的二次界：4k² ≤ 2^(k+3)（k ≥ 1）。与 12 界同构：(k+1)² ≤ 2k²
   自 k ≥ 4 起保步进（此界 (k+3)² ≤ 2(k+2)² 对 k ≥ 1 恒真）。 *)
Lemma u5c_pow4 : forall k : nat, (1 <= k)%nat -> (4 * k * k <= 2 ^ (k + 3))%nat.
Proof.
  intro k.
  induction k as [| k IH]; intro Hk.
  - lia.
  - destruct k as [|[|[|k]]].
    + cbn. lia.
    + cbn. lia.
    + cbn. lia.
    + assert (Hk' : (1 <= Datatypes.S (Datatypes.S (Datatypes.S k)))%nat) by lia.
      specialize (IH Hk').
      rewrite !u5c_pow2_shift in IH.
      rewrite !u5c_pow2_shift.
      assert (E1 : (4 * Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k))) * Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))
                    <= 2 * (4 * Datatypes.S (Datatypes.S (Datatypes.S k)) * Datatypes.S (Datatypes.S (Datatypes.S k))))%nat) by nia.
      lia.
Qed.

(* 2k 界：2k < 2^(k+5) 对一切 k（归纳基 32 ≥ 2 保证步进严格余量）。 *)
Lemma u5c_pow2b : forall k : nat, (2 * k < 2 ^ (k + 5))%nat.
Proof.
  induction k as [| k IH].
  - cbn. lia.
  - rewrite u5c_pow2_shift.
    pose proof (u5c_pow32 k). lia.
Qed.

(* 64 界：64 ≤ 2^(k+5)（k ≥ 1）。归纳基 32 折乘一次即达；
   任务指令原列无前提形在 k = 0 处为假（2^5 = 32 < 64），已依律五增补前提。 *)
Lemma u5c_pow64 : forall k : nat, (1 <= k)%nat -> (64 <= 2 ^ (k + 5))%nat.
Proof.
  intros k Hk.
  destruct k as [|[|k]].
  - lia.
  - cbn. lia.
  - rewrite !u5c_pow2_shift.
    pose proof (u5c_pow32 k) as Hm. lia.
Qed.

(* ============================================================ *)
(* B 组：Q 微转换（加法右消去 / 减法非负 / Qle ↔ QleT' 双向桥）        *)
(* ============================================================ *)

(* 加法右消去：x + z ≤ y + z 蕴含 x ≤ y。Z 交叉积展开后两约去公因子
   (Qden z)²，由正分母切割保序；Pos2Z.inj_mul 把 Zpos(Pos.mul ·) 归一
   为 Z 乘积后交 nia。 *)
Lemma u5c_qle_add_cancel_r : forall x y z : Q, QleT' (x + z) (y + z) -> QleT' x y.
Proof.
  intros x y z H.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ H) as Hle.
  destruct x as [qx zx]; destruct y as [qy zy]; destruct z as [qz zz].
  unfold Qle in Hle |- *.
  cbn [Qnum Qden Qplus] in Hle |- *.
  rewrite ?Pos2Z.inj_mul in Hle |- *.
  assert (Hz : (0 < Z.pos zz)%Z) by apply Pos2Z.is_pos.
  nia.
Qed.

(* 减法非负：s ≤ t 蕴含 0 ≤ t − s。t − s 的交叉积分子即
   qt·zs − qs·zt，与前提逐项对消，Z 层线性收尾。 *)
Lemma u5c_qle_sub_r : forall s t : Q, QleT' s t -> QleT' 0%Q ((t - s)%Q).
Proof.
  intros s t H.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ H) as Hle.
  destruct s as [qs zs]; destruct t as [qt zt].
  unfold Qle in Hle |- *.
  cbn [Qnum Qden Qminus Qopp Qplus] in Hle |- *.
  rewrite ?Pos2Z.inj_mul in Hle |- *.
  lia.
Qed.

(* 构造向：Qle → QleT'（Z 比较三分 + Qle 排除 Gt 支；不需 Leibniz）。
   Qle_bool 全资格：stdlib QArith_base 同名件（leb 形）遮蔽 S02 判定版
   （与「Qle_bool 头不同」问题同根），须点名 S02 判定定义面。 *)
Lemma u5c_qle_qleT' : forall x y : Q, Qle x y -> QleT' x y.
Proof.
  intros x y H.
  unfold QleT', S02_CauchyComplete.Qle_bool, Qcompare.
  unfold Qle in H.
  destruct (Qnum x * QDen y ?= Qnum y * QDen x)%Z eqn:E; simpl; try reflexivity.
  - exfalso. exact (H E).
Qed.

(* 消解向：QleT' → Qle（Qle 展开 = Z 层交叉积 (· ?= ·) ≠ Gt，
   布尔反映形逐支消解） *)
Lemma u5c_qleT'_qle : forall x y : Q, QleT' x y -> Qle x y.
Proof.
  intros x y H.
  unfold QleT' in H.
  unfold S02_CauchyComplete.Qle_bool, Qcompare in H.
  unfold Qle.
  change ((Qnum x * QDen y ?= Qnum y * QDen x)%Z <> Gt).
  destruct (Qnum x * QDen y ?= Qnum y * QDen x)%Z eqn:E; simpl in H;
    try (inversion H); try (intro Hc; inversion Hc).
Qed.

Print Assumptions u5c_pow12.
Print Assumptions u5c_pow4.
Print Assumptions u5c_pow2b.
Print Assumptions u5c_pow64.
Print Assumptions u5c_qle_add_cancel_r.
Print Assumptions u5c_qle_sub_r.
Print Assumptions u5c_qle_qleT'.
Print Assumptions u5c_qleT'_qle.
