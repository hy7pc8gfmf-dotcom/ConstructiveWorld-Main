(* ============================================================ *)
(* UpAblD1S12_UpReqAttnQ18Tail.v —— AqtTail 8 参数位供给件           *)
(*   ｜独立伴生件·原树零改｜零 Require 上游源件（防混代际 .vo 冲突）        *)
(*                                                              *)
(* 辖区：UpReqAttnQ18Tail.v Section AqtTail 全 9 位（本模块整体认领）。             *)
(*   供给 8 参数位：Token:393｜vocab:394｜vocab_nonempty:395｜z:397｜m:398｜          *)
(*     m_in_vocab:399｜gamma:400｜gap_le:401-402                                 *)
(*   阻隔清单 1 位（可判等墙·不入包·接口内不导出）：                    *)
(*     token_eq_dec:396 —— 本件供给腿以 Token:=bool 具体有限集实例绕行，          *)
(*     直接取其分讨效果（if x then/else 直取），该阻隔前提本体不导入。          *)
(*                                                              *)
(* 形态：供给记录型（参数位语句逐字对照源文件）；Set 排序（Real:Set@S02:394，bool:Set，     *)
(*   全字段 Set 层）。与同族件同实例族（bool 两点/单元素表）。                    *)
(* 实例供给：Token:=bool｜vocab:=cons true nil｜vocab_nonempty:=cons/nil 构造子头 *)
(*   不相交（inversion 一行）｜z:=fun x => if x then real_one else real_zero｜   *)
(*   m:=true｜gamma:=real_one；gap_le 供给腿＝bool 分讨：真支 Set 层 Not（A->Empty_set）以 id_refl 爆 Empty_set 零构造          *)
(*   False_rect，假支 0+1≤1＝comm+zero 两段 trans 链。                           *)
(* Fixpoint 折叠发散坑兑现：供给腿全钉具体实例常量级，无符号表归纳面。            *)
(* 供给级：入包 8 参数位均为机械供给级                    *)
(*   （aqt_pack8_supplied 一件统一供给）。                              *)
(* 依赖：CW_ConstructiveWorld_219（S01 Id:61/InT:97｜S02 环律｜S07 序桥，         *)
(*   只读使用）；零注册面变动。                                *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.

(* ============ 供给腿底座（机械直配，与源文件零耦合） ============ *)

(* 表非空：cons/nil 构造子头不相交 *)
Lemma uabd1s12_aqt_vocabne : Not (Id (cons true (@nil bool)) (@nil bool)).
Proof. intro H. inversion H. Qed.

(* 假支核：0+1 ≤ 1 *)
Lemma uabd1s12_aqt_gap_zero_one : real_le (real_plus real_zero real_one) real_one.
Proof.
  apply RealSetoid.real_eq_le.
  apply (real_eq_trans _ (real_plus real_one real_zero) _).
  - apply real_plus_comm.
  - apply real_plus_zero.
Qed.

(* m_in_vocab 底座：InT_here（tactic 形对参数显隐免疫） *)
Lemma uabd1s12_aqt_mvin : InT true (cons true (@nil bool)).
Proof. apply InT_here. Qed.

(* ============ 供给记录型：8 参数位语句逐字对照源文件 L393-402 ============ *)

(* 构造注记：Set 级 Inductive 构造子内不可量化 Token : Set（Set+1≤Set 拒绝）， *)
(* Token 升为 Inductive 参数（参数在 Set 层合法），排序与 G3 magic=0 通道双保。 *)
Inductive uabd1s12_aqt_pack8 (Token : Set) : Set :=
| uabd1s12_aqt_pack8_intro :
    forall vocab : list Token,                             (* 源文件 L394 *)
      (Not (Id vocab nil)) ->                              (* 源文件 L395 *)
      forall z : Token -> Real,                            (* 源文件 L397 *)
        forall m : Token,                                  (* 源文件 L398 *)
          forall m_in_vocab : InT m vocab,                 (* 源文件 L399 *)
            forall gamma : Real,                           (* 源文件 L400 *)
              (forall x : Token, Not (Id x m) ->           (* 源文件 L401-402 *)
                 real_le (real_plus (z x) gamma) (z m)) ->
              uabd1s12_aqt_pack8 Token.
(* Token 参数位语句＝参数形（源文件 L393，词面入参注记） *)

(* ============ 供给件：bool 两点实例一次喂定 8 槽 ============ *)

Theorem uabd1s12_aqt_pack8_supplied : uabd1s12_aqt_pack8 bool.
Proof.
  apply (uabd1s12_aqt_pack8_intro bool (cons true (@nil bool))
           uabd1s12_aqt_vocabne
           (fun x : bool => if x then real_one else real_zero)
           true uabd1s12_aqt_mvin real_one).
  intros x Hx. destruct x.
  - (* x = true：前提 Not(Id true true) 自爆 *)
    destruct (Hx id_refl).
  - (* x = false：0+1 ≤ 1 *)
    exact uabd1s12_aqt_gap_zero_one.
Qed.

(* ============ 假设面收口申报 ============ *)

Print Assumptions uabd1s12_aqt_pack8_supplied.
