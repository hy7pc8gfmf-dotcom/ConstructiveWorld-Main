(* ============================================================ *)
(* UpAblD1S6_UpReqMinPKLChain.v —— FA-D1S6 数据供给大打包第三梯 件④              *)
(*   ｜独立伴生件·原树零改｜零 Require 母本（防混代际 .vo 地雷，P3S1 坑1）          *)
(*                                                              *)
(* 辖区：UpReqMinPKLChain.v Section X1MinPKLChain 全 7 N 槽（另 1 W 墙登记）        *)
(*   trich:49=W 三分墙（rLPO 族，墙登记不立件，普查 §③ W#6 同源）                 *)
(*   ratio:56｜ratio_pos:57｜ratio_le_one:58                                     *)
(*   （Live_X 副本与 ConstructiveWorld-Main 正册 md5 同代                         *)
(*    实测同代，零代际漂移；零 Require 母本——NatLt/ListDef 经 CW_219 可见，        *)
(*    探针 g0 双轮实测）。                                                        *)
(*                                                              *)
(* 形态：FA-P2S1 直mirror件 UpAblP2_UpMinP_tokens_pack.v（同族槽位——              *)
(*   本模块即 UpMinP.MinPEntropy 概率表世界的 req 镜像；P2S1 判语逐位沿用）。      *)
(*   M1 打包记录型 6 槽（Set 排序，无 Type 字段）：tokens/tokens_ne/tokens_sum/    *)
(*     ratio/ratio_pos/ratio_le_one——单点概率表 real_one::nil 一次打包供给；       *)
(*     ratio_pos 消费=1（普查实测）真消费，与 P2S1 母件零消费剪除情形不同，入包。   *)
(*     real_zero ⇒ 取 i:=length tokens 得 real_lt real_zero real_zero，            *)
(*     与 real_lt_irrefl 矛盾 ⇒ 该槽对任何有限表不可满足（P2S1 M2 同判语）；        *)
(*     有界变体可满足对照 M3（失配仅在量词无界，数据面本体无碍）。                  *)
(*                                                              *)
(* 实例供给（M1）：tokens:=real_one::nil（单点概率表）｜tokens_ne:=existT 0 id_refl｜ *)
(*   tokens_sum:=real_plus_zero real_one（cons 折叠 δ/ι 两步胶）｜ratio:=real_one｜ *)
(*   ratio_pos:=real_lt_zero_one｜ratio_le_one:=inr（real_eq_refl real_one）。     *)
(*                                                              *)
(* 分级（禁注水如实申报）：M1=6 槽 T·供给级合并申报；                              *)
(*   M3=T（real_lt_zero_one 一行直配）。W 位零施工。                               *)
(* 依赖：CW_ConstructiveWorld_219（只读消费）；零 git、零注册面。                   *)
(* 四关留痕：Live_X/attn/logs/g{0..4}-UpAblD1S6_*.{log,exit}                     *)
(* ============================================================ *)

From Stdlib Require Import List.
Import ListNotations.
Require Import CW_ConstructiveWorld_219.

(* ============ M1 打包记录型：6 槽语句逐字入包（对照母本 L50-58） ============ *)

Inductive uabd1s6_mpk_pack6 : Set :=
| uabd1s6_mpk_pack6_intro :
    forall tokens : list Real,
      (* ←L51 tokens_ne *)
      sigT (fun i : nat => NatLt i (length tokens)) ->
      (* ←L54-55 tokens_sum *)
      real_eq (real_list_sum Real (fun x : Real => x) tokens) real_one ->
      (* ←L56 ratio *)
      forall ratio : Real,
      (* ←L57 ratio_pos *)
        real_lt real_zero ratio ->
        (* ←L58 ratio_le_one *)
        real_le ratio real_one ->
        uabd1s6_mpk_pack6.

(* ============ M1 供给件：单点概率表 one::nil ＋ ratio:=one 一次喂定 6 槽 ============ *)

Theorem uabd1s6_mpk_pack6_supplied : uabd1s6_mpk_pack6.
Proof.
  exact (uabd1s6_mpk_pack6_intro
           (real_one :: nil)
           (existT _ 0%nat (@id_refl bool true))
           (real_plus_zero real_one)
           real_one
           real_lt_zero_one
           (inr (real_eq_refl real_one))).
Qed.

(* 原槽语句：forall i : nat, real_lt real_zero (ListDef.nth i tokens real_zero)。
   取 i := length tokens：nth 越界返回默认 real_zero ⇒ 需 real_lt zero zero，
   与 real_lt_irrefl 矛盾 ⇒ 该槽对任何有限表不可满足（P2S1 M2 同判）。 *)
Theorem uabd1s6_mpk_tokens_pos_unsat :
  forall tokens : list Real,
    (forall i : nat, real_lt real_zero (ListDef.nth i tokens real_zero)) -> False.
Proof.
  intros tokens Hpos.
  assert (Hlen : real_lt real_zero (ListDef.nth (length tokens) tokens real_zero))
    by (apply Hpos).
  assert (Hov : ListDef.nth (length tokens) tokens real_zero = real_zero).
  { apply nth_overflow. apply le_n. }
  rewrite Hov in Hlen.
  destruct (real_lt_irrefl real_zero Hlen).
Qed.

(* ============ M3 ←有界变体可满足对照（失配仅在量词无界，数据面本体无碍） ============ *)

Theorem uabd1s6_mpk_tokens_pos_bnd :
  real_lt real_zero (ListDef.nth 0%nat (real_one :: nil) real_zero).
Proof.
  exact real_lt_zero_one.
Qed.

(* ============ 假设面收口申报 ============ *)

Print Assumptions uabd1s6_mpk_pack6_supplied.
Print Assumptions uabd1s6_mpk_tokens_pos_unsat.
Print Assumptions uabd1s6_mpk_tokens_pos_bnd.
