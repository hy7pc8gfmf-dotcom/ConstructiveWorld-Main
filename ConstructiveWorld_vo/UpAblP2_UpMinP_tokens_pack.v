(* ============================================================ *)
(* UpAblP2_UpMinP_tokens_pack.v —— 假设消融战役 FA-P2 批3施工席 S1               *)
(* 辖区：UpMinP.v MinPEntropy 节 7 个 T 槽（现档坐标 L631-641）＋1 W 墙登记        *)
(*   L631 tokens / L632 tokens_ne / L633-634 tokens_pos / L635-636 tokens_sum    *)
(*   L639 ratio / L640 ratio_pos / L641 ratio_le_one                            *)
(*   W 位：L492 um_trich_probe（UpMinPWorld 节）——不发件，落墙登记（见报告）      *)
(*                                                              *)
(* 目的：T 件合并申报（防注水口径，1 件替代 5 槽逐条计数）：                      *)
(*   5 个可满足且真消费的槽（tokens/tokens_ne/tokens_sum/ratio/ratio_le_one）     *)
(*   以单点概率表实例 one::nil 一次打包供给；                                    *)
(*   ratio_pos（L640）=零消费位（全文件唯一出现处即声明行，grep -c=1 实证）       *)
(*   → 剪除即消融，打包件不含该槽；                                             *)
(*   tokens_pos（L633-634）=fail-loud 新发现：语句为无界 forall i＋nth 越界默认    *)
(*   real_zero ⇒ 蕴含 real_lt real_zero real_zero ⇒ 空型（不可满足）——          *)
(*   出空型见证证书一件＋有界变体可满足对照一件；勘误录报告（普查误记 T 级）。    *)
(*                                                              *)
(* 主件清单（前缀 uabp2_）：                                                     *)
(*   M1 uabp2_um_pack5           ←5 槽合并申报（打包记录型，单点表实例直配）      *)
(*   M2 uabp2_um_tokens_pos_unsat←tokens_pos 空型见证证书（N：新发现）           *)
(*   M3 uabp2_um_tokens_pos_bnd  ←有界变体可满足对照（数据面本体无碍，失配仅量词）*)
(*                                                              *)
(* 分级（如实申报）：M1=T 合并申报（供给件 reflexivity/一行直配级，不计非平凡战果）；*)
(*   M2=N（空型见证=真内容：nth_overflow＋real_lt_irrefl 两步，勘误证书）；        *)
(*   M3=T（real_lt_zero_one 一行直配）。                                         *)
(*                                                              *)
(* 依赖（全部只读消费，原树零改）：CW_ConstructiveWorld_219。                     *)
(*   语句面逐字抽取自现档 UpMinP.v L631-641（与正册 md5 同代 fbd63550）。         *)
(*                                                              *)
(* 备注：语句面全集合层（real_lt 为 Q-隙分离型、real_le 为 Or 和型、Id 同一型）；  *)
(*   公理面零新增；文尾逐件 Print Assumptions 收尾。                              *)
(*   四关留痕：Live_X/attn/logs/g{1..4}-UpAblP2S1_umppack.log。                   *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
From Stdlib Require Import List.
Import ListNotations.

(* ============ 打包记录型（5 槽语句逐字对照母本 L631-641，tokens_pos/ratio_pos 不入包） ============ *)
Inductive uabp2_um_pack5 : Set :=
| uabp2_um_pack5_intro :
    forall tokens : list Real,
      (* ←L632 tokens_ne *)
      sigT (fun i : nat => NatLt i (length tokens)) ->
      (* ←L635-636 tokens_sum *)
      real_eq (real_list_sum Real (fun x : Real => x) tokens) real_one ->
      (* ←L639 ratio *)
      forall ratio : Real,
      (* ←L640 剪除：ratio_pos（零消费位，此处不留槽） *)
      (* ←L641 ratio_le_one *)
      real_le ratio real_one ->
      uabp2_um_pack5.

(* M1：单点概率表 one::nil ＋ ratio:=one 一次供给 5 槽 *)
Theorem uabp2_um_pack5_supplied : uabp2_um_pack5.
Proof.
  exact (uabp2_um_pack5_intro
           (real_one :: nil)
           (existT _ 0%nat (@id_refl bool true))
           (real_plus_zero real_one)
           real_one
           (inr (real_eq_refl real_one))).
Qed.

(* ============ M2 ←L633-634 tokens_pos 空型见证证书（fail-loud 勘误件） ============ *)
(* 原槽语句：forall i : nat, real_lt real_zero (nth i tokens real_zero)。
   取 i := length tokens：nth 越界返回默认 real_zero ⇒ 需 real_lt zero zero，
   与 real_lt_irrefl 矛盾 ⇒ 该槽对任何有限表不可满足。 *)
Theorem uabp2_um_tokens_pos_unsat :
  forall tokens : list Real,
    (forall i : nat, real_lt real_zero (nth i tokens real_zero)) -> False.
Proof.
  intros tokens Hpos.
  assert (Hlen : real_lt real_zero (nth (length tokens) tokens real_zero))
    by (apply Hpos).
  rewrite (nth_overflow tokens real_zero (le_n (length tokens)))
    in Hlen.
  destruct (real_lt_irrefl real_zero Hlen).
Qed.

(* ============ M3 ←有界变体可满足对照（失配仅在量词无界，数据面本体无碍） ============ *)
Theorem uabp2_um_tokens_pos_bnd :
  real_lt real_zero (nth 0%nat (real_one :: nil) real_zero).
Proof.
  exact real_lt_zero_one.
Qed.

(* ============ PA 收尾段（逐件 Closed 判读） ============ *)
Print Assumptions uabp2_um_pack5_supplied.
Print Assumptions uabp2_um_tokens_pos_unsat.
Print Assumptions uabp2_um_tokens_pos_bnd.
