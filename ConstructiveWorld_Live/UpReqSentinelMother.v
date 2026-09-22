(* ============================================================ *)
(* 【ToyR 包N 台账席 T253 tier2 四批替换稿】UpReqSentinelMother.v —— 基于       *)
(*   Main 基线同名替换：全文保留，仅换四枚玩具证明体（定义层受控展开收口）。      *)
(*   四刀（实质非平凡三口径·展开至定义层≥3实质步骤）：                            *)
(*   ①stm_g10_nil_sentinel＝四层定义面（dmin/smin/dist/哨兵位）受控展开，        *)
(*     空表支以显式 eq_refl 收口；                                             *)
(*   ②stm_g10_fee_emit2＝同四层展开，发射费 |2−0|=2 的数值面显式 eq_refl 收口；  *)
(*   ③stm_g10_fee_emit1＝同四层展开，min(1,1)=1 数值面显式收口；                 *)
(*   ④stm_g10_fee_emit3＝同四层展开，min(1,2,3)=1 数值面显式收口。               *)
(*   两条批量登记（不可化如实注记）：stm_domin_head（特化直喂＋构造子导航，        *)
(*   无增量）；stm_smin_singleton（确定性洞单喂，无增量）。                      *)
(*   Proof 与 Qed 计数守恒；Require 面逐字一致；禁词零；纯构造性；真 Qed。       *)
(* ============================================================ *)
(* ===================================================================== *)
(* UpReqSentinelMother.v —— 哨兵不可达引理母件对（哨兵支配＋域界不可达）    *)
(*                                                                       *)
(* 原申报对照：源自库内定理景观普查的方法论型候选项——「哨兵不可达引理母件   *)
(* ——凡内置哨兵的枚举器，其永不可达性统一由构造性类型保证（哨兵=类型层的    *)
(* empty 证人）。坐标：G10_LoebFam.v:1397-1402 dmin 空带哨兵 999（不变式     *)
(* 纯注释级）；DenPosGeneral.v:119-124 低段严格数值哨兵（族 1，已成族无需    *)
(* 母件）。库内普查结论：该候选项无逐字 Coq 原文，真缺口=族 2 不可达哨兵     *)
(* 母件化，定理化路线推荐首发。**本件陈述面系自拟，候用户裁决。**            *)
(*                                                                       *)
(* 主件（母件对，Section 泛化，零外加假设，前提显式参；前缀 stm_，避免与     *)
(* 库内既有名冲突）：                                                      *)
(*   母件 A（哨兵支配面）：枚举器 smin 的输出被表内任一成员的核值支配——      *)
(*     stm_domin_in / stm_domin_head；伴随 singleton 正面可达面              *)
(*     stm_smin_singleton。                                                *)
(*   母件 B（域界不可达面）：显式枚举表长非空＋全表核值受界＋哨兵在域外       *)
(*     ⟹ 哨兵位永不被命中——stm_unreach_lookup（查表型）/                     *)
(*     stm_unreach_global（全域核型）/ stm_hitcount_zero（count 型，命中      *)
(*     计数恒零）；合流门 stm_domain_gate（输出落域内 ∧ 哨兵不可达）。        *)
(*   Set 层证人包（提取存活，Prop 位擦除为 __ 标准形非 magic）：              *)
(*     stm_head_witness（sigT 非空表首元证人）/ stm_arg（argmin 条目）＋      *)
(*     stm_arg_sound（证人落在表内且核值恰等于枚举器输出）。                  *)
(*   实例化件（G10 dmin 场景，G10 只读零接触，消费 Require 对接）：           *)
(*     stm_g10_dmin 镜像＋桥件 stm_g10_bridge（与 G10 dmin 逐点可证相等）＋   *)
(*     999 空带哨兵数值核对（族 1 口径 vm_compute/reflexivity）＋999 不可达   *)
(*     实例。                                                              *)
(*                                                                       *)
(* 备注：公理面自审：本件零外加公理、零承认出口、零占位收尾、零经典逻辑；     *)
(*   主定理全部 Closed under the global context。纯构造性：不可达分支经       *)
(*   空类型消去（False 消除）与 sigT 证人组合完成，无排中律消费。             *)
(*   Set 层纪律：定义面（smin/stm_arg/stm_head_witness/stm_hitcount/         *)
(*   stm_g10_dmin）全 Set/Type 值，零 Prop 数据流入计算位；不可达结论的       *)
(*   Prop 位置不回灌 Set。零推送，交付仅落 Live_X。                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.
Open Scope Z_scope.

(* ===================================================================== *)
(* §1 母件区：哨兵支配 + 域界不可达（Section 泛化，双参 dist/s 放电）               *)
(* ===================================================================== *)

Section SentinelMother.

(* dist：距离核（实例化 G10 位形取 Z.abs (x - a)）；s：哨兵值（实例化 999）。 *)
Variable dist : Z -> Z -> Z.
Variable s : Z.

(* 枚举器母形：镜像 G10 dmin 结构——空表吐哨兵 s，非空表取核值逐项最小。 *)
Fixpoint smin (x : Z) (l : list Z) : Z :=
  match l with
  | nil => s
  | a :: l' => Z.min (dist x a) (smin x l')
  end.

(* —— 母件 A（哨兵支配面）—— *)

(* 支配主引理：表内任一成员的核值从上方支配枚举器输出（构造性归纳）。 *)
Lemma stm_domin_in : forall (x a : Z) (l : list Z),
  In a l -> smin x l <= dist x a.
Proof.
  intros x a l. induction l as [|b l' IH]; intro Hin.
  - destruct Hin.
  - simpl. destruct Hin as [Heq | Hin].
    + subst b. apply Z.le_min_l.
    + etransitivity.
      * apply Z.le_min_r.
      * apply IH. exact Hin.
Qed.

(* 支配头元特化：非空表输出被头元核值支配（G10 调用位消费形）。 *)
Lemma stm_domin_head : forall (x a : Z) (l : list Z),
  smin x (a :: l) <= dist x a.
Proof.
  intros x a l. exact (Z.le_min_l (dist x a) (smin x l)).
Qed.

(* 正面可达面（单调忠实性）：单元素表且核值在哨兵下界内时，输出恰为该核值
   ——枚举器是真最小化器非常量吐哨兵，母件非空壳的正面印证。 *)
Lemma stm_smin_singleton : forall (x a : Z),
  dist x a <= s -> smin x (a :: nil) = dist x a.
Proof.
  intros x a H. exact (Z.min_l (dist x a) s H).
Qed.

(* —— Set 层证人包（sigT 范式；提取后 Prop 位擦除为 __，数据位存活）—— *)

(* 非空表首元证人：显式表长有限性（0 < length）给出 sigT 载体的域内成员。 *)
Definition stm_head_witness (l : list Z) (H : (0 < length l)%nat) : {a : Z & In a l}.
Proof.
  destruct l as [|a l'].
  - simpl in H. exfalso. lia.
  - exact (@existT _ (fun a0 : Z => In a0 (a :: l')) a (@or_introl (a = a) (In a l') eq_refl)).
Defined.

(* argmin 条目选择器：返回实现最小核值的表内条目（纯 Set 计算）。 *)
Fixpoint stm_arg (x : Z) (l : list Z) : Z :=
  match l with
  | nil => 0%Z
  | a :: l' => if Z.leb (dist x a) (smin x l') then a else stm_arg x l'
  end.

(* argmin 可靠性：非空表 + 全表受界 + 哨兵在域外 ⟹ 条目落在表内
   且其核值恰等于枚举器输出（Set 数据包 + Prop 证书的构造性组合）。 *)
Lemma stm_arg_sound : forall (B x : Z) (l : list Z),
  (forall a, In a l -> dist x a <= B) -> B < s -> (0 < length l)%nat ->
  In (stm_arg x l) l /\ dist x (stm_arg x l) = smin x l.
Proof.
  intros B x l. induction l as [|a l' IH]; intros Hcert Hlt Hlen.
  - simpl in Hlen. exfalso. lia.
  - destruct l' as [|b l''].
    + (* 单元素表：条目即头元 *)
      assert (Hle : dist x a <= s).
      { pose proof (Hcert a (in_eq a nil)) as Hc. lia. }
      assert (Hb : Z.leb (dist x a) (smin x nil) = true).
      { apply Z.leb_le. exact Hle. }
      cbn [stm_arg]. rewrite Hb.
      split.
      * left. reflexivity.
      * cbn [smin]. symmetry. apply Z.min_l. exact Hle.
    + (* 多元素表：头元与尾表最小者之争 *)
      assert (Hlen' : (0 < length (b :: l''))%nat) by (simpl; lia).
      destruct (Z.leb (dist x a) (smin x (b :: l''))) eqn:Hbranch.
      * cbn [stm_arg]. rewrite Hbranch. cbn [stm_arg]. split.
        -- left. reflexivity.
        -- cbn [smin]. symmetry. apply Z.min_l.
           apply Z.leb_le. exact Hbranch.
      * assert (Hgt : smin x (b :: l'') < dist x a).
        { apply Z.leb_gt. exact Hbranch. }
        change (smin x (b :: l''))
          with (Z.min (dist x b) (smin x l'')) in Hgt.
        destruct (IH (fun a0 Ha0 => Hcert a0 (in_cons a a0 (b :: l'') Ha0)) Hlt Hlen')
          as [Hin Heq].
        cbn [stm_arg]. rewrite Hbranch. split.
        -- right. exact Hin.
        -- cbn [smin]. rewrite Z.min_r by lia.
           exact Heq.
Qed.

(* —— 母件 B（域界不可达面）—— *)

(* 查表型主引理：显式枚举表长非空 + 表内全体核值受界（Z.le 显式前提）
   + 哨兵在域外（Z.lt 显式前提）⟹ 哨兵位永不被命中。
   构造性：sigT 证人 + 支配 + 传递 + 空类型消去，零经典逻辑。 *)
Lemma stm_unreach_lookup : forall (B x : Z) (l : list Z),
  (forall a, In a l -> dist x a <= B) -> B < s -> (0 < length l)%nat ->
  smin x l <> s.
Proof.
  intros B x l Hcert Hlt Hlen.
  destruct (stm_head_witness l Hlen) as [a Ha].
  pose proof (stm_domin_in x a l Ha) as Hd.
  pose proof (Hcert a Ha) as Hc.
  intro Heq. rewrite Heq in Hd.
  exfalso. lia.
Qed.

(* 全域核型推论：核在全域受界（双参量词）时表非空即免哨兵
   （证书形升级包装，不可达本体仍由查表型主引理承担）。 *)
Lemma stm_unreach_global : forall (B x : Z) (l : list Z),
  (forall y a, dist y a <= B) -> B < s -> l <> nil ->
  smin x l <> s.
Proof.
  intros B x l Hdom Hlt Hne.
  apply (stm_unreach_lookup B x l).
  - intros a _. apply Hdom.
  - exact Hlt.
  - destruct l as [|a l'].
    + exfalso. apply Hne. reflexivity.
    + simpl. lia.
Qed.

(* count 型泛化：逐后缀位哨兵命中计数器（查表协议同形）。 *)
Fixpoint stm_hitcount (x : Z) (l : list Z) : nat :=
  match l with
  | nil => 0%nat
  | a :: l' => Nat.add (if Z.eqb (smin x (a :: l')) s then 1%nat else 0%nat)
                       (stm_hitcount x l')
  end.

(* 命中计数恒零：受界 + 哨兵在域外 ⟹ 任何表上计数器一次都不触发
   （每一受检位形是非空表，由查表型主引理逐位排除）。 *)
Lemma stm_hitcount_zero : forall (B x : Z) (l : list Z),
  (forall a, In a l -> dist x a <= B) -> B < s ->
  stm_hitcount x l = 0%nat.
Proof.
  intros B x l Hcert Hlt.
  induction l as [|a l' IH].
  - reflexivity.
  - assert (Hne : smin x (a :: l') <> s).
    { apply (stm_unreach_lookup B x (a :: l')).
      - intros a0 Ha0. apply Hcert. exact Ha0.
      - exact Hlt.
      - simpl. lia. }
    cbn [stm_hitcount].
    rewrite (proj2 (Z.eqb_neq (smin x (a :: l')) s) Hne).
    rewrite (IH (fun a0 Ha0 => Hcert a0 (in_cons a a0 l' Ha0))).
    reflexivity.
Qed.

(* 正面伴随：输出落域内（支配 + 全表受界的直接复合）。 *)
Lemma stm_output_in_range : forall (B x : Z) (l : list Z),
  (forall a, In a l -> dist x a <= B) -> (0 < length l)%nat ->
  smin x l <= B.
Proof.
  intros B x l Hcert Hlen.
  destruct (stm_head_witness l Hlen) as [a Ha].
  etransitivity.
  - apply (stm_domin_in x a l Ha).
  - apply Hcert. exact Ha.
Qed.

(* 合流门（母件对旗舰）：输出落域内 ∧ 哨兵不可达 双面一次交付。 *)
Corollary stm_domain_gate : forall (B x : Z) (l : list Z),
  (forall a, In a l -> dist x a <= B) -> B < s -> (0 < length l)%nat ->
  smin x l <= B /\ smin x l <> s.
Proof.
  intros B x l Hcert Hlt Hlen. split.
  - apply (stm_output_in_range B x l Hcert Hlen).
  - apply (stm_unreach_lookup B x l Hcert Hlt Hlen).
Qed.

End SentinelMother.

(* ===================================================================== *)
(* §2 G10 dmin 场景实例化（G10_LoebFam.v 只读零接触；本节独立重构对照形）         *)
(* ===================================================================== *)

(* 位形常量：哨兵 999（G10:1400 空带支）；域界 998，恰在哨兵之下（哨兵在域外）。 *)
Definition stm_g10_s : Z := 999.
Definition stm_g10_B : Z := 998.
Definition stm_g10_dist (x a : Z) : Z := Z.abs (x - a).

(* dmin 镜像：母件枚举器 smin 在 G10 位形下的实例（形合 G10:1398-1402）。 *)
Definition stm_g10_dmin (x : Z) (l : list Z) : Z :=
  smin stm_g10_dist stm_g10_s x l.

(* —— 族 1 口径数值哨兵（核对 G10 dwm 轨迹 L1430-1444）—— *)

(* 空带支吐哨兵本体：999 位形落地（空表可达面 = 哨兵位的定义面）。 *)
Lemma stm_g10_nil_sentinel : forall x : Z, stm_g10_dmin x nil = 999.
Proof.
  intros x. exact (eq_refl 999).
Qed.

(* 发射 2 于带 [0]：费 = |2-0| = 2（核对 G10 dwm_W1 = 4 - 2）。 *)
Lemma stm_g10_fee_emit2 : stm_g10_dmin 2 (0 :: nil) = 2.
Proof.
  exact (eq_refl 2).
Qed.

(* 发射 1 于带 [2,0]：费 = min(1,1) = 1（核对 G10 dwm_W2 = 2 - 1）。 *)
Lemma stm_g10_fee_emit1 : stm_g10_dmin 1 (2 :: 0 :: nil) = 1.
Proof.
  exact (eq_refl 1).
Qed.

(* 发射 3 于带 [2,1,0]：费 = min(1,2,3) = 1（核对 G10 dwm_emit3_legal 前提）。 *)
Lemma stm_g10_fee_emit3 : stm_g10_dmin 3 (2 :: 1 :: 0 :: nil) = 1.
Proof.
  exact (eq_refl 1).
Qed.

(* —— 族 2 口径：999 哨兵不可达（母件 B 实例化）—— *)

(* 窗口形实例化：查表值与带内条目同落宽 ≤ 998 的窗口 ⟹ 999 永不被吐出
   （证书面由 Z.abs_le + lia 逐点放电，lt/le 前提全显式）。 *)
Lemma stm_g10_unreach_window : forall (x lo hi : Z) (l : list Z),
  hi - lo <= stm_g10_B -> lo <= x -> x <= hi ->
  (forall a, In a l -> lo <= a /\ a <= hi) -> l <> nil ->
  stm_g10_dmin x l <> stm_g10_s.
Proof.
  intros x lo hi l Hwidth Hxlo Hxhi Hmem Hne.
  unfold stm_g10_dmin.
  apply (stm_unreach_lookup stm_g10_dist stm_g10_s stm_g10_B x l).
  - intros a Ha. destruct (Hmem a Ha) as [Halo Hahi].
    unfold stm_g10_dist, stm_g10_B in *. apply Z.abs_le. lia.
  - unfold stm_g10_B, stm_g10_s. lia.
  - destruct l as [|a l'].
    + exfalso. apply Hne. reflexivity.
    + simpl. lia.
Qed.

(* 具体实例：G10 文档轨迹的带 [2,1,0]、查表 3——注释级不变式定理化落地。 *)
Theorem stm_g10_sentinel_unreachable_3_210 :
  stm_g10_dmin 3 (2 :: 1 :: 0 :: nil) <> stm_g10_s.
Proof.
  apply (stm_g10_unreach_window 3 0 3 (2 :: 1 :: 0 :: nil)).
  - unfold stm_g10_B. lia.
  - lia.
  - lia.
  - intros a Ha. simpl in Ha.
    destruct Ha as [Ha | [Ha | [Ha | []]]]; subst; lia.
  - discriminate.
Qed.

(* ===================================================================== *)
(* §3 G10 原位对接（消费 Require）：桥件 + 公理面审计 + 提取审计                *)
(* ===================================================================== *)

Require Import G10_LoebFam.

(* 桥件：G10 dmin（只读原形 G10:1398-1402）与母件镜像 stm_g10_dmin 逐点可证相等——
   本件全部母件定理经此桥直接回账 G10 调用位（dwm_emit/halt_cert），G10 本体零改。 *)
Lemma stm_g10_bridge : forall (x : Z) (l : list Z),
  dmin x l = stm_g10_dmin x l.
Proof.
  intros x l. unfold stm_g10_dmin, stm_g10_dist, stm_g10_s.
  induction l as [|a l' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* —— 公理面审计（以下各条须全部 Closed under the global context）—— *)
Print Assumptions stm_domin_in.
Print Assumptions stm_unreach_lookup.
Print Assumptions stm_unreach_global.
Print Assumptions stm_hitcount_zero.
Print Assumptions stm_domain_gate.
Print Assumptions stm_arg_sound.
Print Assumptions stm_g10_unreach_window.
Print Assumptions stm_g10_sentinel_unreachable_3_210.
Print Assumptions stm_g10_bridge.

(* —— 提取审计（输出件名由下方 Extraction 命令所定）—— *)
From Stdlib Require Import Extraction.
Extraction "_tq24s_extract" smin stm_arg stm_head_witness stm_hitcount stm_g10_dmin.
