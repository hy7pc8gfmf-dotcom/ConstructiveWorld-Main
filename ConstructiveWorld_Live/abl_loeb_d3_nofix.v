(* ============================================================ *)
(* abl_loeb_d3_nofix.v — Löb D3 装配·不动点不存在性定理（使命: 可证性代数中盒谓词不动点的不存在性）*)
(*   （lbh_ 前缀；沿用池内 abl_loeb_d3 / _ext / _prf2 / _prf2b 四件先行的上游件，    *)
(*   把 DD 的 F2 具体盒盲墙升格为「可证性代数的抽象不可能性定理」）                    *)
(*                                                                *)
(* 【主定理（中英双语，施工前定稿自审）】                                          *)
(*                                                                *)
(* 中文：在 pairp 2-adic 分离编码的账本可证性代数中：                                *)
(*   (T1)【标签=赋值】pairp 码的语法层标签恰为其 2-adic 赋值：                          *)
(*         ν₂(pairp a b) = a——哥德尔码自身携带其所在层的可计算读出。                   *)
(*   (T2)【抽象分离判据】对任意验证机制（解码器 dec：nat→option X、编码器                *)
(*         enc：X→nat）及可计算分离子 σ：nat→bool：若 σ 在 enc 的像上恒定               *)
(*         （∃tv, ∀x, σ(enc x) = tv）且在目标码上分离（σ c = negb tv），               *)
(*         则验证器与有界盒对目标码恒盲：∀w, ver w c = false；∀B, box B c = false。      *)
(*         ——「分离同余类不相交 ⟹ 盒谓词不动点不存在」的判据形态。                      *)
(*   (T3)【反射半边】盒真给出显式旧世界见证：□_B c = true ⟹ ∃g:Formula, ⌜g⌝ = c          *)
(*         ⟹ ν₂ c ∈ {4,5} ⟹ σ₈(c) = true。盒的肯定域被 2-adic 赋值完全确定。            *)
(*   (T4)【不动点不存在性】对任意界 B、任意 F2 句 g：□_B⌜g⌝₂ = false（肯定恒不存在）；        *)
(*         而含盒的 Löb 固定式 fsig(B,⌜g⌝₂)→q 在一切赋值下恒真——固定关系只能              *)
(*         空洞成立；对角句 diagF2 th 之盒在一切界下恒假。两者合取即「空洞化定理」。        *)
(*   (T5)【有效化】σ₈(c) := (ν₂ c ≤? 8) 是盒可能性的可计算必要条件                        *)
(*         （□真 ⟹ σ₈真）且其假侧无条件盲（σ₈假 ⟹ □_B c = false 对一切 B）——              *)
(*         分离见证总造、可提取、O(ν₂ c) 步可判。                                      *)
(*   (T6)【两盒视界】旧盒（verPf/dP2 驱动）与新盒（lbg_verPf2/dPrf2 驱动）的               *)
(*         可见码集互斥且由 ν₂ 阈值逐码可判：旧盒真⟹新盒假；新盒真⟹旧盒假。                *)
(*                                                                *)
(* English: In the ledger provability algebra with pairp 2-adic separation               *)
(*   encoding: (T1) the syntactic tag of a pairp code equals its 2-adic                  *)
(*   valuation, nu2(pairp a b) = a. (T2) [Abstract criterion] For ANY                    *)
(*   verification regime (dec, enc) and computable separator sigma constant              *)
(*   on the enc-image and separated at the target code, the verifier and the            *)
(*   bounded box are totally blind at the target. (T3) [Reflection] box-truth           *)
(*   yields an explicit old-world witness: box B c = true implies exists g,             *)
(*   code g = c, hence nu2 c in {4,5}. (T4) [Non-existence of the fixed point]          *)
(*   For every bound B and every F2 sentence g the box never affirms its code,          *)
(*   while the Loebian fixed form with the sentence's own code in the slot              *)
(*   always evaluates true — the fixed relation holds only vacuously, and the           *)
(*   vacuity is decidable per code. (T5) [Effectivization] sigma_8 is a                 *)
(*   computable necessary condition for box-truth, and its false side is                *)
(*   unconditionally blind at every bound. (T6) [Two-box horizon] the old and           *)
(*   new boxes have disjoint visible code sets, decided by the nu2 threshold.           *)
(*                                                                *)
(* 【自审（忠实性）】经典 Löb 的不动点由对角引理保证存在；本件证明的「不存在」               *)
(*   的精确含义是：盒的「肯定」域（使 □_B⌜·⌝ 为真的码集）被证明与 F2 句码空间                 *)
(*   （及一切 ν₂ ≥ 9 的码）不相交——故「□ 肯定对角句」这一事件不存在，Löb 固定式             *)
(*   只能以恒假左件空洞成立。语义上的「空洞不动点」存在（T4 第二联），本件一并               *)
(*   证明之，从而把不可能性精确定位在「肯定」上，不虚报强度。                               *)
(*                                                                *)
(* 构造性: 纯构造性零承认——抽象判据 (T2) 的 Section 变量（X/dec/enc/sg/tv）全部在节闭时       *)
(*   卸载；每一实例的同伦/分离前提当场消解；文末主定理无一悬置假设——                       *)
(*   不可能性定理的每一肢都是无条件全称语句。                                             *)
(*                                                                *)
(* 依赖: Require Import G10_LoebFam + abl_loeb_d3（lbd_Box）+                      *)
(*   abl_loeb_d3_ext（lbe_gnF2/lbe_diagF2）+ abl_loeb_d3_prf2（gnPrf2）+                  *)
(*   abl_loeb_d3_prf2b（lbg_verPf2/lbg_Box2/dPrf2）。                                     *)
(*   编译配方: rocq c -native-compiler no -q -Q <池> "" -Q <vo_local 树> "" <件>.v（按链序） *)
(*   （Rocq 9.1.0，工具链 Live/toolchain/opam/live；G10 从缓存 .vo 解析。）                *)
(*                                                                *)
(* 【诚实边界（fail-loud）】                                                            *)
(*   1. 本件的不可能性作用于旧账本盒 lbd_Box（对象语言 Σ-原子 fsig 的语义所指）——           *)
(*      新凭证层盒 lbg_Box2 对 F2 码可点火（lbg_Box2_HBL1），其不动点问题不在本件；          *)
(*      本件交付的是两盒可见域互斥（T6），非「新盒也无不动点」。                            *)
(*   2. 无界搜索墙（rLPO 谱系）原样保留（CZ 登记，本件未触碰）：本件全在有界侧。             *)
(*   3. 「分离子恒定+分离」判据的适用域是编码器像可 σ-均色的机制；pairp 族五层              *)
(*      全部满足（ν₂ 读层），非 pairp 形编码不在本件断言域内（诚实外推禁令）。               *)
(*   推导完整性自查：零占位、零伪盒、零悬置假设；唯一语义「恒真」语句（lbh_nofixpoint       *)
(*   第二联）与其否定面（第一联）成对交付，空洞性被定理化而非被掩饰。                        *)
(* ============================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Wf_nat.

Require Import G10_LoebFam.
Require Import abl_loeb_d3.
Require Import abl_loeb_d3_ext.
Require Import abl_loeb_d3_prf2.
Require Import abl_loeb_d3_prf2b.

(* ===================================================================== *)
(* §A  ν₂ 机器：可计算的 2-adic 赋值（燃料递归 + 燃料不变性，照 CZ §A 配方）           *)
(*     ν₂ c = c 的 2-adic 赋值（c 的因子 2 的精确指数；约定 ν₂ 0 = 0）。               *)
(* ===================================================================== *)

(* 燃料递归定义：燃料只是递归护栏（与 dT2/dF2/dP2/dF2b 同构的工艺） *)
Fixpoint lbh_nu2f (f c : nat) {struct f} : nat :=
  match f with
  | O => O
  | Datatypes.S f' =>
      match c with
      | O => O
      | Datatypes.S c' =>
          match Nat.even (Datatypes.S c') with
          | true => Datatypes.S (lbh_nu2f f' (Nat.div2 (Datatypes.S c')))
          | false => O
          end
      end
  end.

(* 解码器燃料不变性的 ν₂ 同型件：赋值的是码而非燃料 *)
Lemma lbh_nu2f_fuel_inv : forall c k1 k2 : nat,
  (c <= k1)%nat -> (c <= k2)%nat -> lbh_nu2f k1 c = lbh_nu2f k2 c.
Proof.
  intros c. induction c as [c IH] using lt_wf_ind. intros k1 k2 H1 H2.
  destruct c as [|c'].
  - destruct k1 as [|k1']; destruct k2 as [|k2']; reflexivity.
  - destruct k1 as [|k1']; [lia|]. destruct k2 as [|k2']; [lia|].
    cbn [lbh_nu2f].
    destruct (Nat.even (Datatypes.S c')) eqn:Ev; cbv iota.
    + (* 偶数：每层折半，div2 (S c') ≤ c' < S c' —— 强归纳供 IH *)
      pose proof (Nat.le_div2 c') as Hd.
      assert (Hlt : (Nat.div2 (Datatypes.S c') < Datatypes.S c')%nat) by lia.
      assert (Ha1 : (Nat.div2 (Datatypes.S c') <= k1')%nat) by lia.
      assert (Ha2 : (Nat.div2 (Datatypes.S c') <= k2')%nat) by lia.
      rewrite (IH (Nat.div2 (Datatypes.S c')) Hlt k1' k2' Ha1 Ha2). reflexivity.
    + (* 奇数：0，无递归 *)
      reflexivity.
Qed.

Definition lbh_nu2 (c : nat) : nat := lbh_nu2f c c.

Corollary lbh_nu2_fuel : forall c k : nat,
  (c <= k)%nat -> lbh_nu2f k c = lbh_nu2 c.
Proof.
  intros c k H. exact (lbh_nu2f_fuel_inv c k c H (Nat.le_refl c)).
Qed.

(* 单步方程：ν₂ 的递归读出（证明内受控展开的唯一通道） *)
Lemma lbh_nu2_step : forall c : nat,
  lbh_nu2 c =
  match c with
  | O => O
  | Datatypes.S c' =>
      match Nat.even (Datatypes.S c') with
      | true => Datatypes.S (lbh_nu2 (Nat.div2 (Datatypes.S c')))
      | false => O
      end
  end.
Proof.
  intros c. destruct c as [|c'].
  - reflexivity.
  - unfold lbh_nu2 at 1. cbn [lbh_nu2f].
    rewrite (lbh_nu2_fuel (Nat.div2 (Datatypes.S c')) c')
      by (apply Nat.le_div2).
    reflexivity.
Qed.

(* 奇半线：ν₂(2b+1) = 0 *)
Lemma lbh_nu2_odd : forall b : nat, lbh_nu2 (Datatypes.S (b + b)) = O.
Proof.
  intros b. rewrite lbh_nu2_step. cbv iota.
  rewrite even_succ_double. reflexivity.
Qed.

(* 倍半线：c ≥ 1 时 ν₂(2c) = S(ν₂ c) *)
Lemma lbh_nu2_double : forall c : nat, (1 <= c)%nat ->
  lbh_nu2 (c + c) = Datatypes.S (lbh_nu2 c).
Proof.
  intros c Hc. rewrite lbh_nu2_step. destruct (c + c) as [|p'] eqn:Ep.
  - exfalso. lia.
  - rewrite <- Ep. rewrite even_double. cbv iota. rewrite div2_add.
    reflexivity.
Qed.

(* ★ T1 标签=赋值定理：pairp 码的 2-adic 赋值恰为其标签。
   这是全件的承重恒等式：五层码空间的标签分区（0–3/4–5/6–8/9–11/12–15）
   由 ν₂ 一步读出——「编码即赋值」。 *)
Lemma lbh_nu2_pairp : forall a b : nat, lbh_nu2 (pairp a b) = a.
Proof.
  induction a as [|a IHa]; intros b.
  - cbn [pairp]. apply lbh_nu2_odd.
  - cbn [pairp]. pose proof (pairp_pos a b) as Hp.
    rewrite (lbh_nu2_double (pairp a b) Hp). rewrite IHa. reflexivity.
Qed.

(* ===================================================================== *)
(* §B  分离子与抽象分离判据（T2 的判据形态）                                            *)
(* ===================================================================== *)

(* 阈值分离子 σ₈：ν₂ c ≤ 8 ⟺ c 在旧世界（项 0–3 / 公式 4–5 / D1 证明 6–8）。
   2-adic 同余读法：ν₂ c ≥ 9 ⟺ c ≡ 0 (mod 2⁹) 且 c ≠ 0——半线同余类；
   DD 盒盲定理的 mod 2⁹ 判别式是本分离子在粗模读法下的特例。 *)
Definition lbh_sep (c : nat) : bool := Nat.leb (lbh_nu2 c) 8.

(* ── 抽象验证机制（Section 变量全部节闭卸载——零悬置假设）── *)
Section Regime.

Variable X : Set.                    (* 句法范畴 *)
Variable dec : nat -> option X.      (* 自燃料解码器 *)
Variable enc : X -> nat.             (* 编码器 *)

(* 验证器：重演比对（verPf/lbg_verPf2 的公共抽象形） *)
Definition lbh_ver (w c : nat) : bool :=
  match dec w with
  | Some x => Nat.eqb (enc x) c
  | None => false
  end.

(* 有界盒：界内存在验证通过的凭证码（lbd_Box/lbg_Box2 的公共抽象形） *)
Definition lbh_box (B c : nat) : bool := bsearch B (fun w : nat => lbh_ver w c).

Variable sg : nat -> bool.            (* 可计算分离子 *)
Variable tv : bool.                   (* 分离子的像常值 *)

(* ★ T2 判据·验证器肢：σ 在 enc 像上恒定 + 目标码分离 ⟹ 验证器恒盲。
   证明结构：eqb 命中 ⟹ 目标码=enc x ⟹ σ 目标码 = σ(enc x) = tv = negb tv，
   矛盾——分离子把「命中」在布尔层直接封死，解码器全然不必展开。 *)
Lemma lbh_ver_blind : forall c : nat,
  (forall x : X, sg (enc x) = tv) -> sg c = negb tv ->
  forall w : nat, lbh_ver w c = false.
Proof.
  intros c Hhom Hsep w. unfold lbh_ver.
  destruct (dec w) as [x|]; cbv iota; [|reflexivity].
  destruct (Nat.eqb (enc x) c) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E.
  pose proof (Hhom x) as Hh. rewrite E in Hh. rewrite Hsep in Hh.
  destruct tv; discriminate Hh.
Qed.

(* ★ T2 判据·盒肢：沿 bsearch 结构归纳，逐界把盲性抬升到一切界 *)
Theorem lbh_box_blind : forall c : nat,
  (forall x : X, sg (enc x) = tv) -> sg c = negb tv ->
  forall B : nat, lbh_box B c = false.
Proof.
  intros c Hhom Hsep B. unfold lbh_box. induction B as [|B IH]; cbn [bsearch].
  - reflexivity.
  - rewrite (lbh_ver_blind c Hhom Hsep B). cbn [orb]. exact IH.
Qed.

(* 反射半边（抽象形）：验证器真 ⟹ 显式原像见证——盒可能的活口全在 enc 像内 *)
Lemma lbh_ver_reflect : forall w c : nat, lbh_ver w c = true ->
  sigT (fun x : X => loeb_tid nat (enc x) c).
Proof.
  intros w c H. unfold lbh_ver in H.
  destruct (dec w) as [x|]; cbv iota in H; [|discriminate H].
  destruct (Nat.eqb (enc x) c) eqn:E; [|discriminate H].
  apply Nat.eqb_eq in E. exists x. apply loeb_tid_eq. exact E.
Qed.

End Regime.

(* ===================================================================== *)
(* §C  五层码空间的 ν₂ 读层（分离子的实例事实）                                          *)
(*     旧世界：gnF 像 ⊆ σ₈ 真侧（ν₂ ∈ {4,5}）；                                          *)
(*     新世界：lbe_gnF2 像 ⊆ σ₈ 假侧（ν₂ ∈ {9,10,11}）；gnPrf2 像 ⊆ σ₈ 假侧                *)
(*     （ν₂ ∈ {12,13,14,15}）。每件都是「rewrite lbh_nu2_pairp + 字面计算」                 *)
(*     ——DD 的 lia 同余分析被标签恒等式一步替代。                                        *)
(* ===================================================================== *)

(* 旧盒机制实例：解码器 = dP2 自燃料，编码器 = gnF *)
Definition lbh_old_dec (w : nat) : option Formula := dP2 w w.
(* 新盒机制实例：解码器 = dPrf2 自燃料，编码器 = lbe_gnF2 *)
Definition lbh_new_dec (w : nat) : option Formula2 := dPrf2 w w.
(* 新世界侧分离子：ν₂ c ≥ 9 *)
Definition lbh_sep_ge9 (c : nat) : bool := Nat.leb 9 (lbh_nu2 c).

Lemma lbh_gnF_sep : forall g : Formula, lbh_sep (gnF g) = true.
Proof.
  intros g. destruct g as [u1 u2|a b]; unfold lbh_sep; cbn [gnF];
    rewrite lbh_nu2_pairp; reflexivity.
Qed.

Lemma lbh_gnF_lt9 : forall g : Formula, Nat.leb 9 (lbh_nu2 (gnF g)) = false.
Proof.
  intros g. destruct g as [u1 u2|a b]; cbn [gnF];
    rewrite lbh_nu2_pairp; reflexivity.
Qed.

Lemma lbh_gnF2_sep : forall f2 : Formula2, lbh_sep (lbe_gnF2 f2) = false.
Proof.
  intros f2. destruct f2 as [g|B c|a b]; unfold lbh_sep; cbn [lbe_gnF2];
    rewrite lbh_nu2_pairp; reflexivity.
Qed.

Lemma lbh_gnF2_ge9 : forall f2 : Formula2,
  Nat.leb 9 (lbh_nu2 (lbe_gnF2 f2)) = true.
Proof.
  intros f2. apply Nat.leb_le.
  pose proof (proj1 (Nat.leb_gt (lbh_nu2 (lbe_gnF2 f2)) 8) (lbh_gnF2_sep f2))
    as H. lia.
Qed.

(* 凭证层（Prf2 码，标签 12–15）同在 σ₈ 假侧——DS 分区定理的 ν₂ 统一表述 *)
Lemma lbh_gnPrf2_sep : forall (f2 : Formula2) (pf : Prf2 f2),
  lbh_sep (gnPrf2 f2 pf) = false.
Proof.
  intros f2 pf. destruct pf as
    [g pf0 | a b pf1 pf2 | th t1 t2 Hv | B c g pf0 Hb Hc];
    unfold lbh_sep; cbn [gnPrf2]; rewrite lbh_nu2_pairp; reflexivity.
Qed.

(* ===================================================================== *)
(* §D  旧盒对一切高位码恒盲（判据实例化）+ 反射半边（T3）                                  *)
(* ===================================================================== *)

(* DD 盒盲定理族的判据重推：verPf 对一切 F2 码恒假
   （lbe_verPf_f2_false 的抽象化重推导；DD 原句零改动，本件由 T2 判据导出） *)
Corollary lbh_verPf_f2_false : forall (w : nat) (f2 : Formula2),
  verPf w (lbe_gnF2 f2) = false.
Proof.
  intros w f2.
  exact (lbh_ver_blind Formula lbh_old_dec gnF lbh_sep true (lbe_gnF2 f2)
          lbh_gnF_sep (lbh_gnF2_sep f2) w).
Qed.

Corollary lbh_box_f2_false : forall (B : nat) (f2 : Formula2),
  lbd_Box B (lbe_gnF2 f2) = false.
Proof.
  intros B f2.
  exact (lbh_box_blind Formula lbh_old_dec gnF lbh_sep true (lbe_gnF2 f2)
          lbh_gnF_sep (lbh_gnF2_sep f2) B).
Qed.

(* 旧盒对凭证码同样恒盲（verPf 的像域是 Formula 码，Prf2 码 ν₂ ∈ 12–15）
   ——DS 分区定理（dP2 拒绝 Prf2 码）的验证器侧推论 *)
Corollary lbh_verPf_gnPrf2_false : forall (w : nat) (f2 : Formula2) (pf : Prf2 f2),
  verPf w (gnPrf2 f2 pf) = false.
Proof.
  intros w f2 pf.
  exact (lbh_ver_blind Formula lbh_old_dec gnF lbh_sep true (gnPrf2 f2 pf)
          lbh_gnF_sep (lbh_gnPrf2_sep f2 pf) w).
Qed.

Corollary lbh_box_gnPrf2_false : forall (B : nat) (f2 : Formula2) (pf : Prf2 f2),
  lbd_Box B (gnPrf2 f2 pf) = false.
Proof.
  intros B f2 pf.
  exact (lbh_box_blind Formula lbh_old_dec gnF lbh_sep true (gnPrf2 f2 pf)
          lbh_gnF_sep (lbh_gnPrf2_sep f2 pf) B).
Qed.

(* ★ T3 反射半边：盒真 ⟹ 显式旧世界见证（⌜g⌝ = c 的 Formula g）。
   盒的「活口域」被完全刻画于 gnF 像内——这是盲性定理的逆否承重件。 *)
Theorem lbh_box_reflect : forall (B c : nat), lbd_Box B c = true ->
  sigT (fun g : Formula => loeb_tid nat (gnF g) c).
Proof.
  intros B c H. unfold lbd_Box in H.
  destruct (bsearch_character B (fun w : nat => verPf w c)
              (loeb_tid_eq _ _ _ H)) as [w [Hlt Hv]].
  tidQ Hv Ev. cbv beta in Ev.
  exact (lbh_ver_reflect Formula lbh_old_dec gnF w c Ev).
Qed.

(* 盒真的 ν₂ 必要条件：□_B c = true ⟹ σ₈ c = true ⟺ ν₂ c ≤ 8（实则 ∈{4,5}） *)
Theorem lbh_box_tag_low : forall (B c : nat), lbd_Box B c = true ->
  lbh_sep c = true.
Proof.
  intros B c H. destruct (lbh_box_reflect B c H) as [g Hgc].
  tidQ Hgc Eg. rewrite <- Eg. exact (lbh_gnF_sep g).
Qed.

Theorem lbh_sep_sound : forall (B c : nat), lbd_Box B c = true ->
  lbh_sep c = true.
Proof. exact lbh_box_tag_low. Qed.

(* ★ 不可能性的最一般形：一切 ν₂ ≥ 9 的码（F2 句码、Prf2 凭证码、乃至
   非任何句之码的 2^k，k ≥ 9）在一切界下恒盲——真包含 DD 的 F2 盒盲墙
   （其只对 lbe_gnF2 像断言；本件对整个高位半线断言，且覆盖无原像码）。 *)
Theorem lbh_box_high_blind : forall (B c : nat),
  Nat.leb 9 (lbh_nu2 c) = true -> lbd_Box B c = false.
Proof.
  intros B c H9. destruct (lbd_Box B c) eqn:E.
  - exfalso.
    pose proof (proj1 (Nat.leb_le 9 (lbh_nu2 c)) H9) as Hge.
    pose proof (proj1 (Nat.leb_le (lbh_nu2 c) 8) (lbh_box_tag_low B c E))
      as Hle. lia.
  - reflexivity.
Qed.

(* 分离见证的盲侧无条件完全性：σ₈ c = false ⟹ 一切界恒盲 *)
Theorem lbh_sep_blind : forall (c : nat) (B : nat),
  lbh_sep c = false -> lbd_Box B c = false.
Proof.
  intros c B Hs. apply lbh_box_high_blind. apply Nat.leb_le.
  pose proof (proj1 (Nat.leb_gt (lbh_nu2 c) 8) Hs) as H. lia.
Qed.

(* ===================================================================== *)
(* §E  新盒的对称盲性 + 两盒视界互斥（T6）                                              *)
(*     新盒（lbg_verPf2/dPrf2）的像域是 lbe_gnF2 像（ν₂ ∈ 9–11），                        *)
(*     故它对一切旧世界码（gnF 像，ν₂ ∈ {4,5}）恒盲——同一判据的对称实例。                   *)
(* ===================================================================== *)

Corollary lbh_verPf2_gnF_false : forall (w : nat) (g : Formula),
  lbg_verPf2 w (gnF g) = false.
Proof.
  intros w g.
  exact (lbh_ver_blind Formula2 lbh_new_dec lbe_gnF2 lbh_sep_ge9 true (gnF g)
          lbh_gnF2_ge9 (lbh_gnF_lt9 g) w).
Qed.

Corollary lbh_box2_gnF_false : forall (B : nat) (g : Formula),
  lbg_Box2 B (gnF g) = false.
Proof.
  intros B g.
  exact (lbh_box_blind Formula2 lbh_new_dec lbe_gnF2 lbh_sep_ge9 true (gnF g)
          lbh_gnF2_ge9 (lbh_gnF_lt9 g) B).
Qed.

(* 新盒的反射半边：Box2 真 ⟹ 显式 F2 见证 *)
Lemma lbh_box2_reflect : forall (B c : nat), lbg_Box2 B c = true ->
  sigT (fun x : Formula2 => loeb_tid nat (lbe_gnF2 x) c).
Proof.
  intros B c H. unfold lbg_Box2 in H.
  destruct (bsearch_character B (fun w : nat => lbg_verPf2 w c)
              (loeb_tid_eq _ _ _ H)) as [w [Hlt Hv]].
  tidQ Hv Ev. cbv beta in Ev. unfold lbg_verPf2 in Ev.
  destruct (dPrf2 w w) as [x|] eqn:Ed; cbv iota in Ev; [|discriminate Ev].
  destruct (Nat.eqb (lbe_gnF2 x) c) eqn:Eq; [|discriminate Ev].
  apply Nat.eqb_eq in Eq. exists x. apply loeb_tid_eq. exact Eq.
Qed.

(* ★ T6 两盒视界互斥：任何码至多被一盒肯定，且由 ν₂ 阈值逐码可判。
   推论形：两盒不可能对同一码同时为真——「肯定」关系上的不相交性定理。 *)
Theorem lbh_horizon_new_old : forall (B1 B2 c : nat),
  lbg_Box2 B2 c = true -> lbd_Box B1 c = false.
Proof.
  intros B1 B2 c H2. destruct (lbh_box2_reflect B2 c H2) as [x Hxc].
  tidQ Hxc Ex. rewrite <- Ex. apply lbh_box_high_blind. apply lbh_gnF2_ge9.
Qed.

Theorem lbh_horizon_old_new : forall (B1 B2 c : nat),
  lbd_Box B1 c = true -> lbg_Box2 B2 c = false.
Proof.
  intros B1 B2 c H1. destruct (lbg_Box2 B2 c) eqn:E2.
  - exfalso. destruct (lbh_box2_reflect B2 c E2) as [x Hxc].
    tidQ Hxc Ex. rewrite <- Ex in H1.
    rewrite (lbh_box_f2_false B1 x) in H1. discriminate H1.
  - reflexivity.
Qed.

(* ===================================================================== *)
(* §F  不动点不存在性主定理（T4）+ 对角句展品                                           *)
(* ===================================================================== *)

(* ★ 主定理：Löb 固定关系的空洞化定理（双联，Set 载体积）。
   第一联（否定面）：对任意界 B、任意 F2 句 g，盒永不肯定其码——
     「□_B(g) 与 g 的固定关系」中的肯定事件不存在；
   第二联（肯定面）：把 g 自身码放进 Σ-槽的 Löb 固定式
     fsig(B,⌜g⌝₂) → q 在一切赋值下恒真——但由第一联其左件恒假，
     恒真必然空洞。两联合取 = 固定关系「只能空洞成立」的精确定位，
     且空洞性由 §G 分离子逐码可判（lbh_sep）。 *)
Theorem lbh_nofixpoint : forall (B : nat) (g q : Formula2) (s : nat -> nat),
  ((lbd_Box B (lbe_gnF2 g) = false) *
   (evalF2 (fimp2 (fsig (numT B) (numT (lbe_gnF2 g))) q) s = true))%type.
Proof.
  intros B g q s. split.
  - apply lbh_box_f2_false.
  - cbn [evalF2]. rewrite valt_numT. rewrite valt_numT.
    assert (Hb : lbd_Box B (lbe_gnF2 g) = false) by apply lbh_box_f2_false.
    unfold lbd_Box in Hb. rewrite Hb. cbn [negb orb]. reflexivity.
Qed.

(* 对角句展品：任意 Löb 算子 th 的对角句 diagF2 th，其码在一切界下不被肯定，
   且其分离见证恒在盲侧——「□(对角句) 恒假」的一般化+可判定化。 *)
Corollary lbh_diag_never_affirmed : forall (th : Formula2) (B : nat),
  lbd_Box B (lbe_gnF2 (lbe_diagF2 th)) = false.
Proof. intros th B. apply lbh_box_f2_false. Qed.

Corollary lbh_sep_diag : forall th : Formula2,
  lbh_sep (lbe_gnF2 (lbe_diagF2 th)) = false.
Proof. intros th. apply lbh_gnF2_sep. Qed.

(* ===================================================================== *)
(* §G  数值验证件（分离见证的 vm_compute 可判性）                                         *)
(* ===================================================================== *)

(* ν₂ 读层验证件：⌜0=0⌝ = 656（公式层 ν₂=4）、D1 证明码 2624（ν₂=6）、
   F2 原子码 672256 = pairp 9 656（ν₂=9）、边界点 512 = 2⁹（ν₂=9） *)
Theorem lbh_demo_nu2_656 : lbh_nu2 656 = 4.
Proof. vm_compute. reflexivity. Qed.

Theorem lbh_demo_nu2_2624 : lbh_nu2 2624 = 6.
Proof. vm_compute. reflexivity. Qed.

Theorem lbh_demo_nu2_672256 : lbh_nu2 672256 = 9.
Proof. vm_compute. reflexivity. Qed.

Theorem lbh_demo_nu2_512 : lbh_nu2 512 = 9.
Proof. vm_compute. reflexivity. Qed.

(* 判别式对偶验证件（DD 1/2≠1/6 形态的一般化）：同一分离子对旧世界码亮、
   新世界码盲——一步计算定两侧 *)
Theorem lbh_demo_sep_pair : ((lbh_sep 656 = true) * (lbh_sep 672256 = false))%type.
Proof. split; vm_compute; reflexivity. Qed.

(* 非码高赋值点的一般盲性：512 = 2⁹ 不是任何句的码（无 gnF/gnF2 原像），
   盲性定理照样覆盖（vm_compute 独立验证件，不经定理通道）——超出编码像的一般性实证 *)
Theorem lbh_demo_blind_512 : lbd_Box 3000 512 = false.
Proof. vm_compute. reflexivity. Qed.

(* DD 展品句 lbe_demo_th 的对角句：定理通道的一切界盲性 + 分离见证 *)
Theorem lbh_demo_diag_blind : forall B : nat,
  lbd_Box B (lbe_gnF2 (lbe_diagF2 lbe_demo_th)) = false.
Proof. intros B. apply lbh_diag_never_affirmed. Qed.

Theorem lbh_demo_diag_sep : lbh_sep (lbe_gnF2 (lbe_diagF2 lbe_demo_th)) = false.
Proof. apply lbh_sep_diag. Qed.

(* ===================================================================== *)
(* 诚实边界（显式声明，不特设构造）：                                                            *)
(*   1. 本件不可能性作用于旧账本盒 lbd_Box（Σ-原子 fsig 的语义所指）。新盒              *)
(*      lbg_Box2 对 F2 码可点火（lbg_Box2_HBL1 在案）；本件交付两盒可见域               *)
(*      互斥（T6），不虚称「新盒也无不动点」。                                            *)
(*   2. 无界搜索墙（rLPO 谱系）原样保留：本件全在有界侧，未触碰无界化。                    *)
(*   3. 判据 (T2) 的断言域 = 编码器像可被某可计算分离子均色的机制；pairp 族               *)
(*      五层全满足，非 pairp 形编码不在断言域内。                                          *)
(*   4. lbh_nofixpoint 第二联的「恒真」是空洞恒真（第一联确定左件恒假），                  *)
(*      与 DD lbe_loeb_diag_vacuous 的伪全形警报同一纪律：边界见证，非 Löb 进展。          *)
(* ===================================================================== *)

(* —— 假设面自审（全部应 Closed under the global context） —— *)
Print Assumptions lbh_nu2_pairp.
Print Assumptions lbh_ver_blind.
Print Assumptions lbh_box_blind.
Print Assumptions lbh_ver_reflect.
Print Assumptions lbh_gnF_sep.
Print Assumptions lbh_gnF2_sep.
Print Assumptions lbh_gnPrf2_sep.
Print Assumptions lbh_box_reflect.
Print Assumptions lbh_box_tag_low.
Print Assumptions lbh_box_high_blind.
Print Assumptions lbh_sep_blind.
Print Assumptions lbh_nofixpoint.
Print Assumptions lbh_diag_never_affirmed.
Print Assumptions lbh_horizon_old_new.
Print Assumptions lbh_horizon_new_old.
Print Assumptions lbh_demo_nu2_672256.
Print Assumptions lbh_demo_blind_512.
