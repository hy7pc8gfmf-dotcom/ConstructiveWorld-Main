(* ============================================================ *)
(* ToyR 玩具证替换件 —— T261 台账席 战役包V（tier2 十二批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   nlp_len_nonzero（原 L80，2 句玩具证）                                *)
(*   nlp_ofnat_S_pos（原 L54，5 句玩具证）                                *)
(* ============================================================ *)

(* ============================================================ *)
(* NatLenPos.v —— T40 消融50 战役 CYC9 席（批次 E-STAGING-CYC9）   *)
(*                                                              *)
(* 使命：G01_CoreMicro.v:284 real_of_nat length 正性槽 C 类兑现。  *)
(*   槽语句（G01_CoreMicro.v:284，Section RealVarNonNeg 内）：     *)
(*     Variable Hpos : real_lt real_zero (real_of_nat (length enum2)). *)
(*   （组大小正性：natural→R 转换的非零恒等槽——G01 组均值          *)
(*     mean2 = inv(|G|)·Σr 的分母前提；同形槽家族实测坐标：        *)
(*     S08:1741 real_group_size_pos / S15:1734、:2041 Hpos /      *)
(*     GibbsAttractor:63 n_pos / S11 vocab_len_pos 系。）         *)
(*                                                              *)
(* 收口原理（沿 CYB7 fa57_grpo_G_pos 的 InT 推导归纳范式 +        *)
(*   UpKVDrift kv_ofnat 族具体层配方）：                           *)
(*   ① real_of_nat 非负（k 归纳：real_le_refl / real_le_id_l      *)
(*      归位 + real_le_plus_compat + real_lt_zero_one）；          *)
(*   ② S k 情形严格正（real_lt_le_trans 经 one + 左加非负）；      *)
(*   ③ 主件：对 InT 推导本身归纳（两构造子皆 cons 形，Nil 支不进   *)
(*      证明项——规避空匹配的 Obj.magic 提取包装，fa57 实证坑）；   *)
(*      length (y::l) ≡ S (length l) 定义性归约，②直配；           *)
(*   ④ 非零恒等件：正性 ⟹ Not (real_eq 0 |G|)（real_lt_eq_lt      *)
(*      + real_eq_sym 换装撞 real_lt_irrefl，Set 层 Not）。        *)
(*   ——槽消费面：Hpos 供 real_inv_pos 分母位（G01:288 mean2），     *)
(*     本件给覆盖见证下的封闭装配锚（nlp_g01_mean2）。             *)
(*                                                              *)
(* 纪律：纯构造性 / 语句面全 Set 层（real_lt/real_le/real_eq 均    *)
(*   S02 Set 定义；Not=S01:70 Empty_set 函数形）/ 非平凡真证 /     *)
(*   原树零改；前缀 nlp_ 全库防撞已核；尾嵌 PA 自检段。            *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section NatLenPos.

(* ---- 支撑①：natural→R 嵌入非负（UpKVDrift.kv_ofnat_nonneg 镜像，
        本席本地复刻防跨席节参依赖） ---- *)
Lemma nlp_ofnat_nonneg : forall k : nat,
  real_le real_zero (real_of_nat k).
Proof.
  intro k. induction k as [| k IH].
  - apply real_le_refl.
  - cbn [real_of_nat].
    apply (RealSetoid.real_le_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus real_one (real_of_nat k))).
    + apply real_eq_sym. apply real_plus_zero.
    + apply real_le_plus_compat.
      * apply real_le_from_lt_aux. apply real_lt_zero_one.
      * exact IH.
Qed.

(* ---- 支撑②：S k 情形严格正（0 < 1 ≤ 1 + of_nat k） ---- *)
Lemma nlp_ofnat_S_pos : forall k : nat,
  real_lt real_zero (real_of_nat (Datatypes.S k)).
Proof.
  intro k.
  cbn [real_of_nat].
  apply (real_lt_le_trans real_zero real_one           (real_plus real_one (real_of_nat k)) real_lt_zero_one).
  apply real_le_plus_nonneg_r_aux.
  apply nlp_ofnat_nonneg.
Qed.

(* ---- 主件：枚举长度正性槽（G01:284 Hpos 的覆盖见证收口形） ----
   对 InT 推导本身归纳：两构造子皆 cons 形，Nil 支不进证明项
   （fa57_grpo_G_pos 同法；规避空匹配提取魔数）。 *)
Theorem nlp_len_pos_cover :
  forall (G : Set) (enum : list G),
    (forall i : G, InT i enum) ->
    forall g0 : G,
      real_lt real_zero (real_of_nat (Datatypes.length enum)).
Proof.
  intros G enum cover g0.
  induction (cover g0) as [l0 | y l0 Hin IH].
  - exact (nlp_ofnat_S_pos (Datatypes.length l0)).
  - exact (nlp_ofnat_S_pos (Datatypes.length l0)).
Qed.

(* ---- 非零恒等件：正性 ⟹ |G| 不为零（Set 层 Not） ---- *)
Theorem nlp_len_nonzero :
  forall (G : Set) (enum : list G),
    real_lt real_zero (real_of_nat (Datatypes.length enum)) ->
    Not (real_eq real_zero (real_of_nat (Datatypes.length enum))).
Proof.
  intros G enum Hpos H0.
  exact (real_lt_irrefl real_zero           (real_lt_eq_lt real_zero                          (real_of_nat (Datatypes.length enum))                          real_zero Hpos                          (real_eq_sym real_zero                             (real_of_nat (Datatypes.length enum)) H0))).
Qed.

(* ---- G01:284 槽位锚定形：组均值 mean2 的封闭装配
        （G01:287-289 逐字同构：inv(|G|)·Σr，Hpos 由覆盖见证供给，
          零假设面剩余——槽消费全闭合示形） ---- *)
Definition nlp_g01_mean2 (Grp2 : Set) (enum2 : list Grp2)
  (reward2 : Grp2 -> Real) (cover : forall i : Grp2, InT i enum2)
  (g0 : Grp2) : Real :=
  real_mult (real_inv_pos (real_of_nat (Datatypes.length enum2))
               (nlp_len_pos_cover Grp2 enum2 cover g0))
            (real_list_sum_g Grp2 reward2 enum2).

End NatLenPos.

(* ---- G1 内嵌自检段（四关前置：文件内显式 PA 声明） ---- *)
Print Assumptions nlp_ofnat_nonneg.
Print Assumptions nlp_ofnat_S_pos.
Print Assumptions nlp_len_pos_cover.
Print Assumptions nlp_len_nonzero.
Print Assumptions nlp_g01_mean2.
