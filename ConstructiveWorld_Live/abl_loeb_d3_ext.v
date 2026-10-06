(* ============================================================ *)
(* abl_loeb_d3_ext.v — Löb D3 层 2 续件 使命: Formula2 编码往返 + 对角组装          *)
(*   +盒盲边界定理（lbe_ 前缀，G10_LoebFam :3633 自指路的落地件）                     *)
(*                                                                *)
(* 【使命】接续首切片（abl_loeb_d3.v，层 1 已闭合+guarded 展品）：               *)
(*   (1) Formula2 的 gnF2/dF2b 编码往返——G10_LoebFam.v :3633 接口建议原文             *)
(*       「下一棒：Formula2 的 gnF2/dF2b 编解码往返（标签 9/10/11）」的实建；            *)
(*   (2) guarded Löb 向全形的剩余障碍消除：把 CZ 登记的障碍 (i)（编码缺件）              *)
(*       消除并实证，同时把障碍升格为两条**已证**的精确边界定理。                       *)
(*                                                                *)
(* 依赖: Require Import G10_LoebFam（vo 走 vo_local_world_unified_0930      *)
(*   新鲜树）+ abl_loeb_d3（同池 CZ 遗产，lbd_ 前缀零改动，使用其燃料不变性三件/           *)
(*   码序三件/HBL 件）。编译配方: rocq c -native-compiler no -q -Q <池> "" -Q <vo_local 树> ""       *)
(*   abl_loeb_d3.v && … abl_loeb_d3_ext.v（Rocq 9.1.0，live switch；9.0.1 报             *)
(*   bad version number——CZ 坑卡沿用）。                                           *)
(*                                                                *)
(* 【本件陈述（两段 17 件 + 展品 3 件）】                                            *)
(*   §E Formula2 编码往返（标签 9/10/11，D1 gnT/gnF 术的整套照抄+使用）：               *)
(*     lbe_gnF2（编码：f2b↦9 槽 gnF、fsig↦10 槽 gnT 对、fimp2↦11 槽 gnF2 对）；          *)
(*     lbe_dF2b（全函数燃料解码器，燃料=递归护栏）；                                  *)
(*     lbe_dF2b_fuel_inv（解码器燃料不变性——lbd_unp2_self_bounds/lbd_dT2_fuel_inv/       *)
(*       lbd_dF2_fuel_inv 三件的直接使用，同型推广）；                                 *)
(*     lbe_dF2b_norm（自燃料规范化）；                                               *)
(*     lbe_gnF2_fuel（**编码往返主定理**：(gnF2 f2 ≤ k) → dF2b k (gnF2 f2) = Some f2——       *)
(*       f2b 肢使用 D1 gnF_fuel，是 D3 对 D1 往返的第一次真实嵌套使用）；                  *)
(*     lbe_dec_gnF2 / lbe_gnF2_inj（真解码 + 编码单射）；                              *)
(*     lbe_dF2_S_gnF2_none / lbe_dF_gnF2_none / lbe_dF2b_S_gnF_none                     *)
(*       （**交叉解码盲区**：F2 码经 Formula 解码器得 None，Formula 码经 F2 解码器         *)
(*        得 None——两类码空间 2-adic 分离的解码器侧表述）。                              *)
(*   §F Formula2 对角组装 + 盒盲边界定理（层 2 障碍消除的实证）：                         *)
(*     lbe_gsubF2 / lbe_wrap2 / lbe_diagF2（对角组合子，照 G10 :3641 接口建议组装）；      *)
(*     lbe_diagF2_code_eq（码恒等：⌜diagF2 th⌝₂ = lbe_gsubF2 ⌜wrap2 th⌝₂ ⌜wrap2 th⌝₂——        *)
(*       D1 diagonal_code_fixed 的 Formula2 对应件，使用 lbe_dec_gnF2）；                *)
(*     lbe_valt_ext / lbe_evalF_ext / lbe_bsearch_ext / lbe_evalF2_ext                  *)
(*       （赋值点态延拓四件——evalF2 只透过 valt 看赋值，无函数外延性公理）；               *)
(*     lbe_diagF2_eval（求值对角恒等：evalF2 (diagF2 th) s = evalF2 th (upd s ⌜wrap2 th⌝₂)   *)
(*       ——对角项 tsub 的值经 gsubF 走 Formula 解码器，F2 码处 gsubF=n 恒等，               *)
(*       故对角正确「退一格」到 wrap2 的码——这正是本件实证出的精确间隙）；                 *)
(*     lbe_verPf_f2_false / lbe_box_f2_false（**盒盲定理**：有界账本盒对一切                  *)
(*       Formula2 码恒假——verPf 的码比对在 F2 码空间恒不命中，□_B⌜f2⌝₂ = false）；           *)
(*     lbe_loeb_diag_vacuous（Löb 句 d2 := □_B(x)→p 的对角组装之求值恒真——                 *)
(*       但其真是**退化的**：□_B⌜d2⌝₂ 盒盲恒假，蕴含式被空真左件托起。                     *)
(*       【伪全形警报】此定理是全形 Löb 的**边界见证**而非 Löb 进展：                      *)
(*       它证明「天真全形提升在该语义下空洞」，与「□(□f→f)→f 可证」无关。）                  *)
(*                                                                *)
(* 【Set 载体纪律】语句面零 Prop 载体：等式以 bool/nat/option 方程，齐性以 loeb_tid，        *)
(*   界前提 (… ≤ …)%nat（Proof 层算术接口，与 D1/D2/D3 同型）。零公理、零承认、              *)
(*   构造性: 零占位、零经典逻辑；全链信息性，可提取（检验件 lbe_d3_probe.v）。                     *)
(*                                                                *)
(* 【fail-loud 记录（层 2/层 3 状态，同步登记于施工报告】）                              *)
(*   层 2 的「编码往返」障碍（CZ 登记 (i) 的缺件半边）本件**消除**：gnF2/dF2b 往返           *)
(*   已闭合，diagF2 组装可施、其码可计算可回读。                                           *)
(*   全形 Löb 仍不闭合，且本件把边界**升格为两条已证定理**：                              *)
(*   (i') 盒盲墙（新，已证）：账本凭证空间（dP2 像）只产出 Formula 码，lbe_verPf_f2_false      *)
(*        + lbe_box_f2_false 钉死 □ 对 F2 码恒假——全形 Löb 需要全新凭证层                   *)
(*        （Prf2/gnPrf2 于 Formula2 上的归纳+重演+MP 封闭），编码往返只是必要件；            *)
(*   (ii') 无界搜索墙（rLPO 谱系，沿 CZ 登记，本件未触碰）：无守卫 □ 的判定需               *)
(*        unbounded bsearch。                                                          *)
(*   另证：F2 对角句的槽值恒为 ⌜wrap2 th⌝₂ 而非 ⌜diagF2 th⌝₂（项通道 tsub↦gsubF 是               *)
(*   Formula 解码器驱动的）——「码级自代入对应 gsubF2 进项值通道」是下一真实山峰。            *)
(*   禁虚报自查：本件零伪 Löb——lbe_loeb_diag_vacuous 以名字与警报注释标定其退化本性。         *)
(* ============================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Wf_nat.

Require Import G10_LoebFam.
Require Import abl_loeb_d3.

(* ===================================================================== *)
(* §E  Formula2 编码往返（标签 9/10/11）                                          *)
(*     D1 参数位占用：项 0–3 / 公式 4–5 / 证明 6–8；本件按 G10 :3633 接口建议                *)
(*     取 9（f2b）/ 10（fsig）/ 11（fimp2），与既有码空间标签互异。                       *)
(* ===================================================================== *)

Fixpoint lbe_gnF2 (f : Formula2) : nat :=
  match f with
  | f2b g => pairp 9 (gnF g)
  | fsig B c => pairp 10 (pairp (gnT B) (gnT c))
  | fimp2 a b => pairp 11 (pairp (lbe_gnF2 a) (lbe_gnF2 b))
  end.

(* 全函数解码器（燃料 = 递归护栏；照 dT2/dF2/dP2 同构，标签 9/10/11 三肢） *)
Fixpoint lbe_dF2b (f c : nat) {struct f} : option Formula2 :=
  match f with
  | O => None
  | Datatypes.S f' =>
      match unp2 c c with
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
           (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
           (Datatypes.S O)))))))), q) =>
          (match dF2 f' q with
           | Some g => Some (f2b g)
           | None => None
           end)
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
           (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
           (Datatypes.S (Datatypes.S O))))))))), q) =>
          (match unp2 q q with
           | Some (a, b) =>
               (match dT2 f' a with
                | Some x =>
                    (match dT2 f' b with
                     | Some y => Some (fsig x y)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
           (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
           (Datatypes.S (Datatypes.S (Datatypes.S O)))))))))), q) =>
          (match unp2 q q with
           | Some (a, b) =>
               (match lbe_dF2b f' a with
                | Some x =>
                    (match lbe_dF2b f' b with
                     | Some y => Some (fimp2 x y)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | _ => None
      end
  end.

(* 解码器燃料不变性：解码的是码而非燃料（lbd_dF2_fuel_inv 的 Formula2 同型推广；
   使用 lbd_unp2_self_bounds + lbd_dT2_fuel_inv + lbd_dF2_fuel_inv） *)
Lemma lbe_dF2b_fuel_inv : forall c k1 k2 : nat,
  (c <= k1)%nat -> (c <= k2)%nat -> lbe_dF2b k1 c = lbe_dF2b k2 c.
Proof.
  intros c. induction c as [c IH] using lt_wf_ind. intros k1 k2 H1 H2.
  destruct c as [|c'].
  - destruct k1 as [|k1']; destruct k2 as [|k2']; reflexivity.
  - destruct k1 as [|k1']; [lia|]. destruct k2 as [|k2']; [lia|].
    cbn [lbe_dF2b].
    destruct (unp2 (Datatypes.S c') (Datatypes.S c')) as [[l q]|] eqn:Epc.
    + cbv iota.
      destruct l as
        [|[|[|[|[|[|[|[|[|[|[|[|[|l3]]]]]]]]]]]]]; cbv iota; try reflexivity.
      * (* 标签 9：f2b，dF2 一路（使用 CZ 的 lbd_dF2_fuel_inv） *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c') _ q Epc) as Hb.
        destruct Hb as [_ [Hq Hqlt]].
        assert (Ha1 : (q <= k1')%nat) by lia.
        assert (Ha2 : (q <= k2')%nat) by lia.
        assert (Hf2 : dF2 k1' q = dF2 k2' q)
          by (apply lbd_dF2_fuel_inv; lia).
        rewrite Hf2. reflexivity.
      * (* 标签 10：fsig，dT2 两路 *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c') _ q Epc) as Hb.
        destruct Hb as [_ [Hq Hqlt]].
        destruct (unp2 q q) as [[a b]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q a b Epq) as Hb2.
        destruct Hb2 as [Hqa [Hqb _]].
        assert (Hta : dT2 k1' a = dT2 k2' a) by (apply lbd_dT2_fuel_inv; lia).
        assert (Htb : dT2 k1' b = dT2 k2' b) by (apply lbd_dT2_fuel_inv; lia).
        rewrite Hta, Htb. reflexivity.
      * (* 标签 11：fimp2，自身 IH 两路 *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c') _ q Epc) as Hb.
        destruct Hb as [_ [Hq Hqlt]].
        destruct (unp2 q q) as [[a b]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q a b Epq) as Hb2.
        destruct Hb2 as [Hqa [Hqb _]].
        assert (Hla : (a < Datatypes.S c')%nat) by lia.
        assert (Hlb : (b < Datatypes.S c')%nat) by lia.
        assert (Ha1 : (a <= k1')%nat) by lia.
        assert (Ha2 : (a <= k2')%nat) by lia.
        assert (Hb1 : (b <= k1')%nat) by lia.
        assert (Hb2 : (b <= k2')%nat) by lia.
        rewrite (IH a Hla k1' k2' Ha1 Ha2). rewrite (IH b Hlb k1' k2' Hb1 Hb2).
        reflexivity.
    + reflexivity.
Qed.

(* 自燃料规范化推论（lbd_dP2_norm 同型） *)
Corollary lbe_dF2b_norm : forall c k : nat,
  (c <= k)%nat -> lbe_dF2b k c = lbe_dF2b c c.
Proof.
  intros c k H. apply (lbe_dF2b_fuel_inv c k c); [exact H | apply Nat.le_refl].
Qed.

(* ── 编码往返主定理：充料燃料下真解码 ──
   f2b 肢使用 D1 的 gnF_fuel（D3 对 D1 往返的第一次嵌套使用）；
   fsig 肢使用 gnT_fuel×2；fimp2 肢走自身归纳。 *)
Theorem lbe_gnF2_fuel : forall (f2 : Formula2) (k : nat),
  (lbe_gnF2 f2 <= k)%nat -> lbe_dF2b k (lbe_gnF2 f2) = Some f2.
Proof.
  intros f2. induction f2 as [g|B c|a IHa b IHb]; intros k Hk.
  - (* f2b g：码 = pairp 9 (gnF g)，内槽走 gnF_fuel *)
    destruct k as [|k'].
    + cbn [lbe_gnF2 pairp] in Hk. lia.
    + pose proof (lbd_pairp_gt_snd 9 (gnF g)) as Hgt.
      cbn [lbe_gnF2 pairp] in Hk. cbn [pairp] in Hgt.
      assert (Hla : (gnF g <= k')%nat) by lia.
      cbn [lbe_gnF2 lbe_dF2b]. rewrite unp2_pair. cbv iota.
      rewrite (gnF_fuel g k' Hla). reflexivity.
  - (* fsig B c：码 = pairp 10 (pairp (gnT B) (gnT c))，双项槽走 gnT_fuel *)
    destruct k as [|k'].
    + cbn [lbe_gnF2 pairp] in Hk. lia.
    + pose proof (pairp_ge1 (gnT B) (gnT c)) as Hq1.
      pose proof (pairp_ge (gnT B) (gnT c)) as Hq2.
      assert (Hq3 : (pairp (gnT B) (gnT c) + 1
                     <= pairp 10 (pairp (gnT B) (gnT c)))%nat)
        by (cbn [pairp]; lia).
      cbn [lbe_gnF2 pairp] in Hk.
      assert (Hq4 : (pairp (gnT B) (gnT c) <= k')%nat) by lia.
      assert (H1a : (gnT B <= k')%nat) by lia.
      assert (H1c : (gnT c <= k')%nat) by lia.
      cbn [lbe_gnF2 lbe_dF2b]. rewrite unp2_pair. cbv iota.
      rewrite unp2_pair. cbv iota.
      rewrite (gnT_fuel B k' H1a). rewrite (gnT_fuel c k' H1c).
      reflexivity.
  - (* fimp2 a b：码 = pairp 11 (pairp (gnF2 a) (gnF2 b))，双公式槽走自身归纳 *)
    destruct k as [|k'].
    + cbn [lbe_gnF2 pairp] in Hk. lia.
    + pose proof (pairp_ge1 (lbe_gnF2 a) (lbe_gnF2 b)) as Hq1.
      pose proof (pairp_ge (lbe_gnF2 a) (lbe_gnF2 b)) as Hq2.
      assert (Hq3 : (pairp (lbe_gnF2 a) (lbe_gnF2 b) + 1
                     <= pairp 11 (pairp (lbe_gnF2 a) (lbe_gnF2 b)))%nat)
        by (cbn [pairp]; lia).
      cbn [lbe_gnF2 pairp] in Hk.
      assert (Hq4 : (pairp (lbe_gnF2 a) (lbe_gnF2 b) <= k')%nat) by lia.
      assert (H1a : (lbe_gnF2 a <= k')%nat) by lia.
      assert (H1b : (lbe_gnF2 b <= k')%nat) by lia.
      cbn [lbe_gnF2 lbe_dF2b]. rewrite unp2_pair. cbv iota.
      rewrite unp2_pair. cbv iota.
      rewrite (IHa k' H1a). rewrite (IHb k' H1b).
      reflexivity.
Qed.

(* 真解码（自燃料规范形） *)
Corollary lbe_dec_gnF2 : forall f2 : Formula2,
  lbe_dF2b (lbe_gnF2 f2) (lbe_gnF2 f2) = Some f2.
Proof.
  intros f2.
  exact (lbe_gnF2_fuel f2 (lbe_gnF2 f2) (Nat.le_refl (lbe_gnF2 f2))).
Qed.

(* 编码单射 *)
Lemma lbe_gnF2_inj : forall f1 f2 : Formula2,
  lbe_gnF2 f1 = lbe_gnF2 f2 -> f1 = f2.
Proof.
  intros f1 f2 H.
  pose proof (lbe_dec_gnF2 f1) as E1. pose proof (lbe_dec_gnF2 f2) as E2.
  rewrite H in E1. rewrite E1 in E2. inversion E2. reflexivity.
Qed.

(* ── 交叉解码盲区三件 ──
   Formula 码（标签 4/5）不在 F2 解码器值域，F2 码（标签 9/10/11）不在
   Formula 解码器值域。技术要点：自燃料形 dX2 (pairp …) (pairp …) 的燃料
   非 constructor 头不可 iota 展开，须先经燃料不变性抬到 S-燃料形再算。 *)

Lemma lbe_dF2_S_gnF2_none : forall f2 : Formula2,
  dF2 (Datatypes.S (lbe_gnF2 f2)) (lbe_gnF2 f2) = None.
Proof.
  intros f2. destruct f2 as [g|B c|a b]; cbn [lbe_gnF2 dF2].
  - rewrite unp2_pair. cbv iota. reflexivity.
  - rewrite unp2_pair. cbv iota. reflexivity.
  - rewrite unp2_pair. cbv iota. reflexivity.
Qed.

Lemma lbe_dF2_norm_aux : forall c k : nat, (c <= k)%nat -> dF2 k c = dF2 c c.
Proof.
  intros c k H. apply (lbd_dF2_fuel_inv c k c); [exact H | apply Nat.le_refl].
Qed.

Lemma lbe_dF_gnF2_none : forall f2 : Formula2, dF (lbe_gnF2 f2) = None.
Proof.
  intros f2. unfold dF.
  rewrite <- (lbe_dF2_norm_aux (lbe_gnF2 f2) (Datatypes.S (lbe_gnF2 f2))
               (Nat.le_succ_diag_r _)).
  apply lbe_dF2_S_gnF2_none.
Qed.

Lemma lbe_dF2b_S_gnF_none : forall g : Formula,
  lbe_dF2b (Datatypes.S (gnF g)) (gnF g) = None.
Proof.
  intros g. destruct g as [u1 u2|a b]; cbn [gnF lbe_dF2b].
  - rewrite unp2_pair. cbv iota. reflexivity.
  - rewrite unp2_pair. cbv iota. reflexivity.
Qed.

(* ===================================================================== *)
(* §F  Formula2 对角组装 + 盒盲边界定理                                            *)
(* ===================================================================== *)

(* 码层自代入（gsubF 的 Formula2 对应件；使用 lbe_dec_gnF2） *)
Definition lbe_gsubF2 (c m : nat) : nat :=
  match lbe_dF2b c c with
  | Some f2 => lbe_gnF2 (substF2 f2 (numT m))
  | None => c
  end.

(* 包装体与对角组合子（照 G10 :3641 接口建议组装） *)
Definition lbe_wrap2 (th : Formula2) : Formula2 := substF2 th selfT.
Definition lbe_diagF2 (th : Formula2) : Formula2 :=
  substF2 (lbe_wrap2 th) (numT (lbe_gnF2 (lbe_wrap2 th))).

(* 码恒等式：对角句的码 = 码层自代入值（D1 diagonal_code_fixed 的 Formula2 对应件） *)
Theorem lbe_diagF2_code_eq : forall th : Formula2,
  loeb_tid nat (lbe_gnF2 (lbe_diagF2 th))
    (lbe_gsubF2 (lbe_gnF2 (lbe_wrap2 th)) (lbe_gnF2 (lbe_wrap2 th))).
Proof.
  intros th. apply loeb_tid_eq. unfold lbe_gsubF2, lbe_diagF2.
  rewrite lbe_dec_gnF2. reflexivity.
Qed.

(* 赋值点态延拓四件：evalF2 只透过 valt 看赋值（零函数外延性公理） *)
Lemma lbe_valt_ext : forall (t : Term) (s1 s2 : nat -> nat),
  (forall k : nat, s1 k = s2 k) -> valt t s1 = valt t s2.
Proof.
  intros t. induction t as [k0| |t IHt|a IHa b IHb]; intros s1 s2 H; cbn [valt].
  - apply H.
  - reflexivity.
  - rewrite (IHt s1 s2 H). reflexivity.
  - rewrite (IHa s1 s2 H). rewrite (IHb s1 s2 H). reflexivity.
Qed.

Lemma lbe_evalF_ext : forall (f : Formula) (s1 s2 : nat -> nat),
  (forall k : nat, s1 k = s2 k) -> evalF f s1 = evalF f s2.
Proof.
  intros f. induction f as [u1 u2|a IHa b IHb]; intros s1 s2 H; cbn [evalF].
  - rewrite (lbe_valt_ext u1 s1 s2 H). rewrite (lbe_valt_ext u2 s1 s2 H).
    reflexivity.
  - rewrite (IHa s1 s2 H). rewrite (IHb s1 s2 H). reflexivity.
Qed.

Lemma lbe_bsearch_ext : forall (bd : nat) (p1 p2 : nat -> bool),
  (forall w : nat, p1 w = p2 w) -> bsearch bd p1 = bsearch bd p2.
Proof.
  intros bd. induction bd as [|bd' IH]; intros p1 p2 H; cbn [bsearch].
  - reflexivity.
  - rewrite (H bd'). rewrite (IH p1 p2 H). reflexivity.
Qed.

Lemma lbe_evalF2_ext : forall (f2 : Formula2) (s1 s2 : nat -> nat),
  (forall k : nat, s1 k = s2 k) -> evalF2 f2 s1 = evalF2 f2 s2.
Proof.
  intros f2. induction f2 as [g|B c|a IHa b IHb]; intros s1 s2 H; cbn [evalF2].
  - apply lbe_evalF_ext. exact H.
  - rewrite (lbe_valt_ext B s1 s2 H). apply lbe_bsearch_ext.
    intros w. rewrite (lbe_valt_ext c s1 s2 H). reflexivity.
  - rewrite (IHa s1 s2 H). rewrite (IHb s1 s2 H). reflexivity.
Qed.

(* ── 求值对角恒等式 ──
   evalF2 (diagF2 th) s = evalF2 th (upd s ⌜wrap2 th⌝₂)。
   对角项 tsub (numT n) (numT n) 的值经 gsubF（Formula 解码器驱动）：n 为 F2 码时
   dF n = None（lbe_dF_gnF2_none），故槽值恒为 n = ⌜wrap2 th⌝₂——
   对角「退一格」到包装体的码，本件实证出的精确间隙。 *)
Theorem lbe_diagF2_eval : forall (th : Formula2) (s : nat -> nat),
  evalF2 (lbe_diagF2 th) s
  = evalF2 th (upd s (lbe_gnF2 (lbe_wrap2 th))).
Proof.
  intros th s. unfold lbe_diagF2.
  rewrite evalF2_subst. rewrite valt_numT.
  unfold lbe_wrap2. rewrite evalF2_subst.
  assert (Hv : valt selfT (upd s (lbe_gnF2 (substF2 th selfT)))
               = lbe_gnF2 (substF2 th selfT)).
  { unfold selfT. cbn [valt upd]. unfold gsubF.
    rewrite lbe_dF_gnF2_none. reflexivity. }
  rewrite Hv.
  apply lbe_evalF2_ext. intros k0. destruct k0; reflexivity.
Qed.

(* ── 盒盲定理 ──
   verPf 的码比对（gnF g =? c）在 F2 码空间恒不命中：Formula 码带标签 4/5
   （pairp 4/5 形 = 16·(·+1) / 32·(·+1)），F2 码带标签 9/10/11
   （512·(·+1) / 1024·(·+1) / 2048·(·+1)），模 2 的幂严格分离。 *)
Theorem lbe_verPf_f2_false : forall (w : nat) (f2 : Formula2),
  verPf w (lbe_gnF2 f2) = false.
Proof.
  intros w f2. unfold verPf.
  destruct (dP2 w w) as [g|].
  - destruct g as [u1 u2|a b]; destruct f2 as [g2|B c|a2 b2];
      cbn [gnF lbe_gnF2]; cbn [pairp];
      apply (proj2 (Nat.eqb_neq _ _)); lia.
  - reflexivity.
Qed.

Theorem lbe_box_f2_false : forall (B : nat) (f2 : Formula2),
  lbd_Box B (lbe_gnF2 f2) = false.
Proof.
  intros B f2. revert f2. induction B as [|B' IH]; intros f2;
    cbn [lbd_Box bsearch].
  - reflexivity.
  - rewrite (lbe_verPf_f2_false B' f2). cbn [orb]. apply IH.
Qed.

(* ── Löb 句的对角组装与其退化真（边界见证，非 Löb 进展）──
   d2 := diagF2 (fimp2 (fsig (numT B) (tvar 0)) p) 即「□_B(x) → p」的对角形：
   其 fsig 槽值恒为 ⌜d2⌝₂-族码 n = ⌜wrap2 th⌝₂，而 n 是 F2 码 → □_B n 盲区恒假
   → 蕴含式被空真左件托起，求值恒真。
   【伪全形警报】这是全形 Löb 在本语义下的**空洞化证明**：天真提升给不出 Löb
   内容，只给出一枚恒真但空的蕴含式。全形 Löb 须另建 Prf2/gnPrf2 凭证层。 *)
Theorem lbe_loeb_diag_vacuous : forall (B : nat) (p : Formula2) (s : nat -> nat),
  evalF2 (lbe_diagF2 (fimp2 (fsig (numT B) (tvar 0)) p)) s = true.
Proof.
  intros B p s. rewrite lbe_diagF2_eval. cbn [evalF2].
  rewrite valt_numT. cbn [valt upd].
  pose proof (lbe_box_f2_false B
               (lbe_wrap2 (fimp2 (fsig (numT B) (tvar 0)) p))) as Hb.
  unfold lbd_Box in Hb. rewrite Hb. reflexivity.
Qed.

(* ── 展品：对角句可编码、可回读、盒盲可计算烟测 ──
   码规模警示：本配对编码下 compound 句的码按 2^(左子码) 增长
   （pairp 的首分量即左子式码），故 Löb 句（fimp2 复合形）的码是一元
   天文数，vm_compute 不可达——复合烟测一律走定理通道；可计算烟测
   缩至闭原子尺度（码 = pairp 9 656 = 672256）。 *)
Definition lbe_demo_th : Formula2 :=
  fimp2 (fsig (numT 3000) (tvar 0)) (f2b (teq tzero tzero)).
Definition lbe_demo_d : Formula2 := lbe_diagF2 lbe_demo_th.
Definition lbe_demo_code : nat := lbe_gnF2 lbe_demo_d.

(* Löb 句的码级回读（定理通道）：⌜d2⌝₂ 解码恰为 d2——F2 句可寻址 *)
Theorem lbe_demo_roundtrip :
  lbe_dF2b lbe_demo_code lbe_demo_code = Some lbe_demo_d.
Proof. apply lbe_dec_gnF2. Qed.

(* 盒盲烟测（定理通道）：界 3000 的账本盒对 ⌜d2⌝₂ 恒假 *)
Theorem lbe_demo_box_blind : lbd_Box 3000 lbe_demo_code = false.
Proof. apply lbe_box_f2_false. Qed.

(* 退化真（定理通道）：Löb 句在一切赋值下求值为真——空真左件托起 *)
Theorem lbe_demo_vacuous : evalF2 lbe_demo_d (fun _ : nat => 0) = true.
Proof. apply lbe_loeb_diag_vacuous. Qed.

(* —— 闭原子尺度的独立 vm_compute 烟测（不依赖上述定理）——
   闭原子码 = pairp 9 (gnF (teq tzero tzero)) = 512·(2·656+1) = 672256。
   【栈边界实录】烟测必须以字面码 672256 入语句：lbe_demo_atom_code 的定义体
   携带 diagF2 的 numT 槽，CBV 求值按码值深度递归构造 numT（67 万层栈）
   即栈溢出——vm_compute 可安全触碰的是解码器（燃料只是护栏，深度随码结构
   而非燃料值）与字面码。此为配对编码 + CBV 的栈复杂度边界，登记于报告。 *)
Theorem lbe_demo_atom_rt_compute :
  lbe_dF2b 672256 672256 = Some (f2b (teq tzero tzero)).
Proof. vm_compute. reflexivity. Qed.

Theorem lbe_demo_atom_blind_compute : lbd_Box 3000 672256 = false.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(* 诚实边界（显式声明，不特设构造）：                                              *)
(*   1. 层 2 编码往返障碍（CZ 登记 (i) 缺件半边）已消除：lbe_gnF2_fuel 已闭合，            *)
(*      对角组装 diagF2 可施、码恒等/求值恒等两件已证。                                  *)
(*   2. 全形 Löb 不在本件。剩余两墙均已**定理化**：                                     *)
(*      (i') 盒盲墙（本件新证）：lbe_verPf_f2_false + lbe_box_f2_false——                 *)
(*           账本凭证空间对 F2 码空转，全形提升需 Prf2/gnPrf2 新凭证层；                   *)
(*      (ii') 无界搜索墙（rLPO 谱系，沿 CZ 登记原样保留）。                              *)
(*   3. F2 对角的「差一格」：槽值 = ⌜wrap2 th⌝₂ ≠ ⌜diagF2 th⌝₂（一般）——                     *)
(*      根因是项值通道 tsub ↦ gsubF 只认 Formula 解码器；把 gsubF2 对应进                *)
(*      项值通道（新项构造子）或求 F2 保码不动点，是下一真实山峰。                          *)
(*   4. lbe_loeb_diag_vacuous 为边界见证：其「恒真」由盒盲托起，与 Löb 内容无关，           *)
(*      名字与警报注释双重钉死，禁作全形 Löb 引用。                                      *)
(* ===================================================================== *)

(* —— 假设面自审（全部应 Closed under the global context） —— *)
Print Assumptions lbe_dF2b_fuel_inv.
Print Assumptions lbe_gnF2_fuel.
Print Assumptions lbe_gnF2_inj.
Print Assumptions lbe_diagF2_code_eq.
Print Assumptions lbe_diagF2_eval.
Print Assumptions lbe_box_f2_false.
Print Assumptions lbe_loeb_diag_vacuous.
Print Assumptions lbe_demo_roundtrip.
