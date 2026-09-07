(* ============================================================ *)
(* UpDebtSqrtAbs.v —— 债务清理打包席（件 3，方案三 b+）          *)
(*   抽象 Id 系增强接口下任意非负 d 的构造性平方根见证：          *)
(*   把 Real 层 real_sqrt_exists（根 L96475）的 Or 分支证书      *)
(*   结构逐字镜像回 RealInterfaceEnhanced 接口泛型。             *)
(*                                                              *)
(*   语句（任务书模板）：                                        *)
(*     forall d, Or (lt zero d) (Id zero d) ->                  *)
(*       sigT (fun r => And (le zero r) (Id (mult r r) d))      *)
(*   证明核：                                                    *)
(*     左支 d>0：r := exp_neg(half·log_inv d)（half :=           *)
(*       inv_pos two，two := 1+1 正性经 plus_positive 组装），    *)
(*       r·r == d 链 = exp_neg_plus 反向 + distrib/mult 代数     *)
(*       （half+half == one）+ exp_neg_log_inv 右逆；            *)
(*     右支 d≡0：r := zero（mult_zero）。                        *)
(*                                                              *)
(*   诚实接口说明：接口的 le 是不透明字段，库内仅有 Or→le 单向   *)
(*   （lt_le_iff），故前件取 Or 形态——这正是 real_le 的定义体    *)
(*   （real_le x y := Or (real_lt x y) (real_eq x y)），与 Real  *)
(*   层 real_sqrt_exists 的可消费前提逐字同构；le 形态前提在接口 *)
(*   内无法分解（无 le→Or 字段），不硬凑。                       *)
(*                                                              *)
(*   纪律：纯构造性、零承认；语句全 Set 层（lt/le/Id/sigT/And）；*)
(*   全部 Qed 收口。                                             *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

Section SqrtAbstract.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* 平方维数见证（镜像根内 sqrt_witness）：r·r == d *)
Definition sqrt_witness (d r : R) : Set := Id (mult r r) d.

(* two := 1+1（字面 2）；two > 0（plus_positive × one_pos 组装） *)
Definition two_abs : R := plus one one.
Lemma two_abs_pos : lt zero two_abs.
Proof.
  exact (plus_positive one one one_pos one_pos).
Qed.

(* half := inv(two)；half + half == one
   链：half·two == one（inv_pos_correct，经 mult_comm），
       half·two == half·(1+1) == half·1 + half·1 == half + half
       （distrib + mult_one × 2）。 *)
Definition half_abs : R := inv_pos two_abs two_abs_pos.
Lemma half_plus_half : Id (plus half_abs half_abs) one.
Proof.
  assert (Hd : Id (mult half_abs two_abs) one)
    by exact (id_trans (mult_comm half_abs two_abs)
                       (inv_pos_correct two_abs two_abs_pos)).
  assert (Hsplit : Id (mult half_abs two_abs) (plus half_abs half_abs))
    by exact (id_trans (distrib half_abs one one)
                       (id_cong2 (fun a b => plus a b)
                                 (mult_one half_abs) (mult_one half_abs))).
  exact (id_trans (id_sym Hsplit) Hd).
Qed.

(* Or 前件即 le 的构造性内容（接口单向 lt_le_iff 的记录） *)
Lemma sqrt_premise_le_intro : forall d : R, Or (lt zero d) (Id zero d) -> le zero d.
Proof.
  intros d H. apply lt_le_iff. exact H.
Qed.

(* ---- 旗舰（件 3）：抽象 Id 层任意非负 d 的平方根见证 ----
   左支（d > 0，正间隙证书）：r := exp_neg(half·log_inv d)。
     r·r == d：exp(h)·exp(h) == exp(h+h)（exp_neg_plus 反向）
       == exp(log_inv d)（h+h == half·L+half·L == half·(L+L)
       == one·L == L，其中 half+half == one）
       == d（exp_neg_log_inv 右逆）。
     r > 0：exp_neg_pos + lt_le_iff。
   右支（d ≡ 0，Id 证书）：r := zero；0 ≤ 0（le_refl）；
     0·0 == 0（mult_zero）== d（Hdeq）。 *)
Theorem sqrt_witness_exists_abstract :
  forall d : R, Or (lt zero d) (Id zero d) ->
  sigT (fun r : R => And (le zero r) (Id (mult r r) d)).
Proof.
  intros d Hd.
  destruct Hd as [Hdlt | Hdeq].
  - (* 情形①：d > 0。r := exp(half·log d)。 *)
    exists (exp_neg (mult half_abs (log_inv d))).
    split.
    + (* r > 0：exp 恒正（le 左支 = lt 经 lt_le_iff） *)
      exact (lt_le_iff zero (exp_neg (mult half_abs (log_inv d)))
                        (inl (exp_neg_pos (mult half_abs (log_inv d))))).
    + (* r·r == d：三分链 exp(h)·exp(h) == exp(h+h) == exp(log d) == d *)
      assert (Hinner : Id (plus (mult half_abs (log_inv d))
                                (mult half_abs (log_inv d)))
                          (log_inv d)).
      { exact (id_trans
                (id_trans
                  (id_cong2 (fun a b => plus a b)
                            (mult_comm half_abs (log_inv d))
                            (mult_comm half_abs (log_inv d)))
                  (id_trans (id_sym (distrib (log_inv d) half_abs half_abs))
                            (mult_comm (log_inv d) (plus half_abs half_abs))))
                (id_trans
                  (id_cong (fun x => mult x (log_inv d)) half_plus_half)
                  (id_trans (mult_comm one (log_inv d))
                            (mult_one (log_inv d))))). }
      exact (id_trans
              (id_sym (exp_neg_plus (mult half_abs (log_inv d))
                                    (mult half_abs (log_inv d))))
              (id_trans (id_cong (fun x => exp_neg x) Hinner)
                        (exp_neg_log_inv d))).
  - (* 情形②：d ≡ 0。r := zero。 *)
    exists zero.
    split.
    + (* 0 ≤ 0：自反 *)
      apply le_refl.
    + (* 0·0 == 0 == d *)
      exact (id_trans (mult_zero zero) Hdeq).
Qed.

(* 见证形态重述（sqrt_witness 命名式） *)
Lemma sqrt_witness_exists_abstract_witness :
  forall d : R, Or (lt zero d) (Id zero d) ->
  sigT (fun r : R => And (le zero r) (sqrt_witness d r)).
Proof.
  intros d H.
  exact (sqrt_witness_exists_abstract d H).
Qed.

(* 实例（机器可检查的健全性检查）：1 的抽象平方根可构造——
   r := exp(half·log_inv 1)，r ≥ 0 且 r·r == 1（镜像 real_sqrt_one）。 *)
Lemma sqrt_one_abstract :
  sigT (fun r : R => And (le zero r) (Id (mult r r) one)).
Proof.
  exact (sqrt_witness_exists_abstract one (inl one_pos)).
Qed.

End SqrtAbstract.
